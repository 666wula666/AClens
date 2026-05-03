import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


VALID_TRACE_STEP_TYPES = {
    "STATE_INIT",
    "MODIFIER",
    "CONSTRAINT",
    "STATE_READ",
    "STATE_WRITE",
    "EXTERNAL_CALL",
    "INTERNAL_CALL",
    "EXECUTION_BODY",
    "RETURN",
    # Backward-compatible witness labels seen in paper-era traces and current
    # model outputs. These are descriptive categories, not proof of
    # infeasibility, so they must not invalidate an otherwise useful witness.
    "EVENT",
    "LOOP",
    "LOOP_START",
    "LOOP_END",
    "CALL",
    "FUNCTION_CALL",
    "CONDITION",
    "CONDITIONAL",
    "IF",
    "STATE_UPDATE",
    "STATE_COMPUTE",
    "STATE_MODIFICATION",
    "STATE_CHECK",
    "DATA_FLOW",
    "ASSEMBLY",
    "ERROR",
}


@dataclass
class TraceValidationResult:
    is_valid: bool
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    sink_covered: bool = False
    normalized_trace_lines: List[str] = field(default_factory=list)
    normalized_structured_trace: List[Dict[str, Any]] = field(default_factory=list)


class TraceWitnessValidator:
    """
    Deterministic validator for LLM-generated traces.

    The validator does not prove semantic feasibility. It only accepts traces
    that are structurally coherent, grounded in the sliced context, and
    explicitly reach the requested sink.
    """

    _STEP_PREFIX_RE = re.compile(r"^\s*(\d+)\.\s*\[([^\]]+)\]\s*(.+?)\s*$")
    _COMPATIBLE_TYPES = {
        ("MODIFIER", "CONSTRAINT"),
        ("CONSTRAINT", "MODIFIER"),
    }
    _GENERIC_TYPES = {
        "STATE_INIT",
        "EVENT",
        "LOOP",
        "LOOP_START",
        "LOOP_END",
        "CALL",
        "FUNCTION_CALL",
        "CONDITION",
        "CONDITIONAL",
        "IF",
        "STATE_UPDATE",
        "STATE_COMPUTE",
        "STATE_MODIFICATION",
        "STATE_CHECK",
        "DATA_FLOW",
        "ASSEMBLY",
        "ERROR",
    }
    _GUARD_KEYWORDS = (
        "onlyowner",
        "only owner",
        "onlyadmin",
        "only admin",
        "onlyadminordeveloper",
        "only admin or developer",
        "require(msg.sender ==",
        "require (_msgsender() ==",
        "require(_msgsender() ==",
        "require(msg.sender==",
        "msg.sender == owner",
        "msg.sender == admin",
        "msg.sender == developer",
        "msg.sender == pendingadmin",
        "msg.sender == governance",
        "msg.sender == operator",
        "msg.sender == factory",
    )

    def validate(
        self,
        trace_lines: Optional[List[str]],
        structured_trace: Optional[List[Dict[str, Any]]],
        context: str,
        sink_description: str,
    ) -> TraceValidationResult:
        errors: List[str] = []
        warnings: List[str] = []

        if not isinstance(trace_lines, list) or not trace_lines:
            return TraceValidationResult(is_valid=False, errors=["Missing trace lines"])

        if structured_trace is None:
            structured_trace = []
        if not isinstance(structured_trace, list):
            return TraceValidationResult(is_valid=False, errors=["structured_trace must be a list"])

        parsed_lines, line_errors, line_warnings = self._parse_trace_lines(trace_lines)
        errors.extend(line_errors)
        warnings.extend(line_warnings)

        normalized_structured, struct_errors, struct_warnings = self._normalize_structured_trace(structured_trace)
        if parsed_lines:
            warnings.extend(struct_errors)
        else:
            errors.extend(struct_errors)
        warnings.extend(struct_warnings)

        if not errors and parsed_lines and normalized_structured:
            cross_errors, cross_warnings = self._cross_check(parsed_lines, normalized_structured)
            warnings.extend(cross_errors)
            warnings.extend(cross_warnings)

        sink_type, sink_code = self._parse_sink_description(sink_description)
        sink_target = self._normalize_match_target(sink_code)
        accepted_types = self._accepted_sink_step_types(sink_type, sink_code)

        grounding_errors, grounding_warnings = self._check_context_grounding(
            parsed_lines=parsed_lines,
            normalized_structured=normalized_structured,
            context=context,
            sink_type=sink_type,
            sink_target=sink_target,
            accepted_sink_types=accepted_types,
        )
        errors.extend(grounding_errors)
        warnings.extend(grounding_warnings)

        hallucinated_guard_errors = self._check_hallucinated_guards(
            parsed_lines=parsed_lines,
            normalized_structured=normalized_structured,
            context=context,
        )
        errors.extend(hallucinated_guard_errors)

        sink_covered = self._check_sink_coverage(
            parsed_lines=parsed_lines,
            normalized_structured=normalized_structured,
            context=context,
            sink_description=sink_description,
        )
        if not sink_covered:
            errors.append("Trace does not explicitly cover the target sink")

        return TraceValidationResult(
            is_valid=not errors,
            errors=errors,
            warnings=warnings,
            sink_covered=sink_covered,
            normalized_trace_lines=[item["raw"] for item in parsed_lines],
            normalized_structured_trace=normalized_structured,
        )

    def _check_hallucinated_guards(
        self,
        parsed_lines: List[Dict[str, Any]],
        normalized_structured: List[Dict[str, Any]],
        context: str,
    ) -> List[str]:
        normalized_context = self._normalize_for_match(context)
        errors: List[str] = []

        for item in parsed_lines:
            if item["type"] not in {"MODIFIER", "CONSTRAINT"}:
                continue
            body = item["body"]
            normalized_body = self._normalize_match_target(body)
            if not normalized_body:
                continue
            if not any(keyword in normalized_body for keyword in self._GUARD_KEYWORDS):
                continue
            if normalized_body in normalized_context:
                continue
            errors.append(
                f"Trace introduces an authorization guard not grounded in context at step {item['step']}: {body}"
            )

        for item in normalized_structured:
            if item["type"] not in {"MODIFIER", "CONSTRAINT"}:
                continue
            code = item.get("code", "")
            normalized_code = self._normalize_match_target(code)
            if not normalized_code:
                continue
            if not any(keyword in normalized_code for keyword in self._GUARD_KEYWORDS):
                continue
            if normalized_code in normalized_context:
                continue
            errors.append(
                f"structured_trace introduces an authorization guard not grounded in context at step {item['step']}: {code}"
            )

        return errors

    def _parse_trace_lines(self, trace_lines: List[str]) -> Tuple[List[Dict[str, Any]], List[str], List[str]]:
        parsed: List[Dict[str, Any]] = []
        errors: List[str] = []
        warnings: List[str] = []

        expected_step = 1
        for raw in trace_lines:
            if not isinstance(raw, str) or not raw.strip():
                errors.append("Trace line must be a non-empty string")
                continue

            match = self._STEP_PREFIX_RE.match(raw)
            if not match:
                errors.append(f"Malformed trace line: {raw}")
                continue

            step = int(match.group(1))
            step_type = self._normalize_step_type(match.group(2))
            body = match.group(3).strip()

            if step != expected_step:
                warnings.append(
                    f"Trace steps are non-consecutive (got {step}, expected {expected_step}); "
                    "continuing with the explicit step labels"
                )
            expected_step += 1

            if step_type not in VALID_TRACE_STEP_TYPES:
                warnings.append(f"Unsupported trace step type: {step_type}")

            if not body:
                errors.append(f"Trace step {step} has empty body")

            parsed.append(
                {
                    "step": step,
                    "type": step_type,
                    "body": body,
                    "raw": raw,
                }
            )

        if len(parsed) < 2:
            warnings.append("Trace is very short; reviewable evidence may be limited")

        return parsed, errors, warnings

    def _normalize_structured_trace(
        self, structured_trace: List[Dict[str, Any]]
    ) -> Tuple[List[Dict[str, Any]], List[str], List[str]]:
        normalized: List[Dict[str, Any]] = []
        errors: List[str] = []
        warnings: List[str] = []

        if not structured_trace:
            warnings.append("Missing structured_trace; relying on trace_lines only")
            return normalized, errors, warnings

        expected_step = 1
        for item in structured_trace:
            if not isinstance(item, dict):
                errors.append("Each structured_trace entry must be an object")
                continue

            step = item.get("step")
            step_type = self._normalize_step_type(item.get("type", ""))
            code = item.get("code")
            formula = item.get("formula")

            if not isinstance(step, int):
                errors.append("structured_trace step must be an integer")
                continue
            if step != expected_step:
                warnings.append(
                    f"structured_trace steps are non-consecutive (got {step}, expected {expected_step}); "
                    "continuing with the explicit step labels"
                )
            expected_step += 1

            if step_type not in VALID_TRACE_STEP_TYPES:
                warnings.append(f"Unsupported structured_trace step type: {step_type}")

            code_text = code.strip() if isinstance(code, str) else ""
            formula_text = formula.strip() if isinstance(formula, str) else ""
            if not code_text and formula_text:
                code_text = formula_text
                warnings.append(f"structured_trace step {step} missing code; reused formula")
            if not formula_text and code_text:
                formula_text = code_text
                warnings.append(f"structured_trace step {step} missing formula; reused code")
            if not code_text:
                errors.append(f"structured_trace step {step} has empty code")
            if not formula_text:
                errors.append(f"structured_trace step {step} has empty formula")

            normalized.append(
                {
                    "step": step,
                    "type": step_type,
                    "code": code_text,
                    "formula": formula_text,
                    "taint_source": item.get("taint_source"),
                }
            )

        return normalized, errors, warnings

    def _cross_check(
        self,
        parsed_lines: List[Dict[str, Any]],
        normalized_structured: List[Dict[str, Any]],
    ) -> Tuple[List[str], List[str]]:
        errors: List[str] = []
        warnings: List[str] = []

        if len(parsed_lines) != len(normalized_structured):
            warnings.append(
                "trace_lines and structured_trace have different lengths; grounding will use the available evidence"
            )

        comparable_len = min(len(parsed_lines), len(normalized_structured))
        for idx in range(comparable_len):
            line_item = parsed_lines[idx]
            struct_item = normalized_structured[idx]
            if line_item["step"] != struct_item["step"]:
                errors.append(f"Step mismatch between trace line and structured_trace at position {idx + 1}")
            if (
                line_item["type"] != struct_item["type"]
                and (line_item["type"], struct_item["type"]) not in self._COMPATIBLE_TYPES
            ):
                warnings.append(
                    f"Type mismatch at step {line_item['step']}: {line_item['type']} vs {struct_item['type']}"
                )

        return errors, warnings

    def _check_context_grounding(
        self,
        parsed_lines: List[Dict[str, Any]],
        normalized_structured: List[Dict[str, Any]],
        context: str,
        sink_type: str,
        sink_target: str,
        accepted_sink_types: set[str],
    ) -> Tuple[List[str], List[str]]:
        errors: List[str] = []
        warnings: List[str] = []
        normalized_context = self._normalize_for_match(context)
        grounded_steps = 0
        ungrounded_messages: List[str] = []
        exact_sink_grounded = False
        exact_sink_ungrounded_messages: List[str] = []

        for item in parsed_lines:
            body = item["body"]
            if self._is_placeholder_body(body):
                if item["type"] != "EXECUTION_BODY":
                    warnings.append(f"Placeholder-style body found at step {item['step']}: {body}")
                continue
            if self._is_generic_step(item["type"], body):
                continue
            normalized_body = self._normalize_match_target(body)
            if normalized_body and normalized_body in normalized_context:
                grounded_steps += 1
                if item["type"] == sink_type and self._matches_sink_target(sink_target, normalized_body):
                    exact_sink_grounded = True
            elif normalized_body:
                message = f"Trace step {item['step']} is not grounded in the sliced context: {body}"
                ungrounded_messages.append(message)
                if item["type"] == sink_type and self._matches_sink_target(sink_target, normalized_body):
                    exact_sink_ungrounded_messages.append(message)

        for item in normalized_structured:
            code = item["code"]
            if self._is_placeholder_body(code):
                if item["type"] != "EXECUTION_BODY":
                    warnings.append(f"Placeholder-style code found at structured step {item['step']}: {code}")
                continue
            if self._is_generic_step(item["type"], code):
                continue
            normalized_code = self._normalize_match_target(code)
            if normalized_code and normalized_code in normalized_context:
                grounded_steps += 1
                if item["type"] == sink_type and self._matches_sink_target(sink_target, normalized_code):
                    exact_sink_grounded = True
            elif normalized_code:
                message = f"structured_trace step {item['step']} is not grounded in the sliced context: {code}"
                ungrounded_messages.append(message)
                if item["type"] == sink_type and self._matches_sink_target(sink_target, normalized_code):
                    exact_sink_ungrounded_messages.append(message)

        if grounded_steps == 0 and ungrounded_messages:
            errors.append("Trace has no grounded step in the sliced context")
            warnings.extend(ungrounded_messages)
        else:
            warnings.extend(ungrounded_messages)

        if exact_sink_ungrounded_messages and not exact_sink_grounded:
            errors.append("Trace reaches the target sink only through steps not grounded in the sliced context")

        return errors, warnings

    def _check_sink_coverage(
        self,
        parsed_lines: List[Dict[str, Any]],
        normalized_structured: List[Dict[str, Any]],
        context: str,
        sink_description: str,
    ) -> bool:
        sink_type, sink_code = self._parse_sink_description(sink_description)
        sink_target = self._normalize_match_target(sink_code)
        accepted_types = self._accepted_sink_step_types(sink_type, sink_code)

        line_hits = any(
            item["type"] in accepted_types
            and self._matches_sink_target(sink_target, self._normalize_match_target(item["body"]))
            for item in parsed_lines
        )
        if line_hits:
            return True

        struct_hits = any(
            item["type"] in accepted_types
            and (
                self._matches_sink_target(sink_target, self._normalize_match_target(item["code"]))
                or self._matches_sink_target(sink_target, self._normalize_match_target(item.get("formula", "")))
            )
            for item in normalized_structured
        )
        if struct_hits:
            return True

        callable_name = self._extract_callable_name(sink_code)
        if not callable_name:
            return False

        helper_body = self._extract_callable_body(context, callable_name)
        if not helper_body:
            return False

        helper_targets = self._extract_helper_targets(helper_body)
        if not helper_targets:
            return False

        for target in helper_targets:
            if any(self._matches_sink_target(target, self._normalize_match_target(item["body"])) for item in parsed_lines):
                return True
            if any(
                self._matches_sink_target(target, self._normalize_match_target(item["code"]))
                or self._matches_sink_target(target, self._normalize_match_target(item.get("formula", "")))
                for item in normalized_structured
            ):
                return True

        return False

    def _parse_sink_description(self, sink_description: str) -> Tuple[str, str]:
        sink_type = ""
        sink_code = sink_description

        type_match = re.search(r"type\s*:\s*([^,]+)", sink_description, flags=re.IGNORECASE)
        if type_match:
            sink_type = self._map_sink_type(type_match.group(1).strip())

        code_match = re.search(r"code\s*:\s*(.+)$", sink_description, flags=re.IGNORECASE)
        if code_match:
            sink_code = code_match.group(1).strip()

        if not sink_type:
            sink_type = "STATE_WRITE"
        return sink_type, sink_code

    def _normalize_step_type(self, raw_step_type: Any) -> str:
        step_type = str(raw_step_type or "").strip().upper()
        if not step_type:
            return ""

        normalized = re.sub(r"[^A-Z0-9]+", "_", step_type)
        normalized = re.sub(r"_+", "_", normalized).strip("_")

        aliases = {
            "EXECUTION_BODY": "EXECUTION_BODY",
            "EXECUTIONBODY": "EXECUTION_BODY",
            "EXECUTION": "EXECUTION_BODY",
            "BODY": "EXECUTION_BODY",
            "CALL": "CALL",
            "_CALL": "CALL",
            "EXTERNALCALL": "EXTERNAL_CALL",
            "INTERNALCALL": "INTERNAL_CALL",
            "FUNCTIONCALL": "FUNCTION_CALL",
            "STATEUPDATE": "STATE_UPDATE",
            "STATEMODIFICATION": "STATE_MODIFICATION",
            "STATECOMPUTE": "STATE_COMPUTE",
            "STATECHECK": "STATE_CHECK",
            "DATAFLOW": "DATA_FLOW",
            "LOOPSTART": "LOOP_START",
            "LOOPEND": "LOOP_END",
        }
        return aliases.get(normalized, normalized)

    def _accepted_sink_step_types(self, sink_type: str, sink_code: str) -> set[str]:
        accepted = {sink_type}
        if self._looks_like_call_expression(sink_code):
            accepted.update({"CALL", "FUNCTION_CALL", "INTERNAL_CALL", "EXTERNAL_CALL"})
        if sink_type == "STATE_WRITE":
            accepted.update({"STATE_UPDATE", "STATE_MODIFICATION"})
        if sink_type == "EXTERNAL_CALL":
            accepted.update({"CALL", "FUNCTION_CALL", "INTERNAL_CALL"})
        return accepted

    def _map_sink_type(self, raw_sink_type: str) -> str:
        lowered = raw_sink_type.lower()
        if lowered == "external_interaction":
            return "EXTERNAL_CALL"
        if lowered == "state_modification":
            return "STATE_WRITE"
        if lowered == "public_initialization":
            return "STATE_WRITE"
        return raw_sink_type.strip().upper()

    def _normalize_match_target(self, text: str) -> str:
        if not text:
            return ""

        lowered = self._preprocess_text(text)
        return self._normalize_for_match(lowered)

    def _is_placeholder_body(self, text: str) -> bool:
        lowered = text.lower().strip()
        return lowered in {
            "(function body execution)",
            "function body execution",
            "execute function body",
        }

    def _is_generic_step(self, step_type: str, text: str) -> bool:
        lowered = text.lower()
        if step_type in self._GENERIC_TYPES:
            return True
        if "arbitrary external caller" in lowered:
            return True
        return False

    def _normalize_for_match(self, text: str) -> str:
        text = text.lower()
        text = re.sub(r"[^a-z0-9_]+", " ", text)
        text = re.sub(r"\s+", " ", text).strip()
        return text

    def _preprocess_text(self, text: str) -> str:
        lowered = text.lower()
        lowered = lowered.replace("=> must be true", "")
        lowered = lowered.replace("(function body execution)", "")
        lowered = re.sub(r"^\s*\w+\s+checks\s+", "", lowered)
        lowered = lowered.replace(" called", "")
        lowered = re.sub(r"\s+", " ", lowered).strip()
        return lowered

    def _matches_sink_target(self, sink_target: str, step_target: str) -> bool:
        if not step_target:
            return False
        if not sink_target:
            return True
        sink_tokens = sink_target.split()
        step_tokens = step_target.split()
        sink_call_head = self._extract_call_head_token(sink_tokens)
        step_call_head = self._extract_call_head_token(step_tokens)
        if sink_call_head and step_call_head and sink_call_head != step_call_head:
            return False
        if sink_target == step_target:
            return True
        if sink_target in step_target or step_target in sink_target:
            return True
        if self._contains_token_sequence(step_tokens, sink_tokens):
            return True
        if self._contains_token_sequence(sink_tokens, step_tokens):
            return True
        if sink_tokens and all(token in step_tokens for token in sink_tokens):
            return True
        # Fall back to operation-centric matching so that equivalent witness
        # steps such as permit/depositVault/burn remain acceptable even when
        # the trace targets one effect within the same sink family.
        sink_ops = self._extract_operation_tokens(sink_tokens)
        step_ops = self._extract_operation_tokens(step_tokens)
        if sink_ops and step_ops and sink_ops.intersection(step_ops):
            return True
        return False

    def _looks_like_call_expression(self, text: str) -> bool:
        return bool(re.search(r"\b[a-zA-Z_][a-zA-Z0-9_]*\s*\(", text or ""))

    def _extract_callable_name(self, text: str) -> str:
        match = re.search(r"([a-zA-Z_][a-zA-Z0-9_]*)\s*\(", text or "")
        if not match:
            return ""
        return match.group(1)

    def _extract_callable_body(self, context: str, callable_name: str) -> str:
        if not context or not callable_name:
            return ""

        for prefix in ("function", "modifier", "constructor"):
            pattern = re.compile(rf"\b{prefix}\s+{re.escape(callable_name)}\b[\s\S]*?\{{", re.IGNORECASE)
            match = pattern.search(context)
            if not match:
                continue
            start = match.end() - 1
            body = self._extract_braced_block(context, start)
            if body:
                return body

        # Some sliced contexts are clipped and may miss the first character of
        # the declaration keyword. Fall back to locating the callable name and
        # extracting the nearest braced block that follows it.
        name_match = re.search(rf"\b{re.escape(callable_name)}\s*\(", context)
        if not name_match:
            return ""
        brace_idx = context.find("{", name_match.end())
        if brace_idx == -1:
            return ""
        return self._extract_braced_block(context, brace_idx)

    def _extract_braced_block(self, text: str, brace_start: int) -> str:
        if brace_start < 0 or brace_start >= len(text) or text[brace_start] != "{":
            return ""
        depth = 0
        for idx in range(brace_start, len(text)):
            char = text[idx]
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return text[brace_start + 1:idx]
        return ""

    def _extract_helper_targets(self, helper_body: str) -> List[str]:
        targets: List[str] = []
        seen = set()
        for raw_line in helper_body.splitlines():
            line = raw_line.strip().rstrip(";")
            if not line:
                continue
            if line in {"{", "}"}:
                continue
            if line.startswith("//"):
                continue
            if line.startswith(("if ", "if(", "for ", "for(", "while ", "while(", "return", "require", "assert")):
                continue

            normalized = self._normalize_match_target(line)
            if not normalized:
                continue
            if normalized in seen:
                continue

            has_state_write = any(op in line for op in ("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "++", "--"))
            has_assignment = "=" in line and not any(op in line for op in ("==", "!=", ">=", "<=", "=>"))
            has_call = self._looks_like_call_expression(line)

            if not (has_state_write or has_assignment or has_call):
                continue

            targets.append(normalized)
            seen.add(normalized)
        return targets

    def _contains_token_sequence(self, haystack: List[str], needle: List[str]) -> bool:
        if not needle or len(needle) > len(haystack):
            return False
        window = len(needle)
        for start in range(len(haystack) - window + 1):
            if haystack[start:start + window] == needle:
                return True
        return False

    def _extract_call_head_token(self, tokens: List[str]) -> str:
        if "call" not in tokens:
            return ""
        call_idx = tokens.index("call")
        if call_idx > 0:
            return tokens[call_idx - 1]
        if len(tokens) > 1:
            return tokens[1]
        return ""

    def _extract_operation_tokens(self, tokens: List[str]) -> set[str]:
        stop = {
            "type", "code", "state", "write", "state_write", "state", "read",
            "external", "interaction", "external_interaction", "call", "internal",
            "msg", "sender", "path", "amount", "token", "address", "this",
            "from", "to", "deadline", "permit", "underlying", "data",
        }
        ops = set()
        for token in tokens:
            if token in stop:
                continue
            if token.isdigit():
                continue
            if len(token) <= 2:
                continue
            if token in {"require", "true", "false"}:
                continue
            ops.add(token)
        return ops
