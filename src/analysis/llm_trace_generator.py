import logging
import json
import os
from typing import List, Dict, Any, Optional
from pydantic import BaseModel
from src.llm.service import LLMService

logger = logging.getLogger(__name__)

class TraceGenerationResult(BaseModel):
    trace_lines: List[str]
    structured_trace: Optional[List[Dict[str, Any]]] = None
    success: bool
    error: Optional[str] = None

class LLMTraceGenerator:
    """
    使用 LLM 从源代码中重构执行轨迹。
    """
    def __init__(self, api_key: Optional[str] = None):
        self.model = "gpt-4o-mini" # 使用推理能力较强的模型
        self.llm_service = LLMService(api_key=api_key, model=self.model)

from src.analysis.relevance_agent import RelevanceAgent

class TraceSimulatorAgent(LLMTraceGenerator):
    """
    轨迹模拟智能体：在 ContextBuilder 提供的裁剪上下文中，利用 LLM 模拟执行路径。
    """
    def __init__(self, api_key: Optional[str] = None):
        super().__init__(api_key)
        self.relevance_agent = RelevanceAgent(api_key=api_key)

    def simulate_trace(self, context: str, sink_description: str) -> TraceGenerationResult:
        # Legacy method wrapper
        result = self.simulate_batch(context, [{"id": "single", "description": sink_description}])
        return result.get("single", TraceGenerationResult(trace_lines=[], success=False, error="Simulation failed"))

    def simulate_batch(self, context: str, sinks: List[Dict[str, str]], context_builder: Any = None) -> Dict[str, TraceGenerationResult]:
        """
        Batch process multiple sinks with hybrid gap detection (Graph + LLM Feedback Loop).

        Gap detection strategy:
        1. Graph-based (fast, precise): detect unresolved CALL edges in the backward slice
        2. LLM-based (slower, semantic): RelevanceAgent identifies missing context from trace failures
        Results are merged to maximize coverage.
        """
        current_context = context
        last_results = {}

        # Max retries for dynamic context retrieval
        max_retries = 2

        for attempt in range(max_retries):
            logger.info(f"Trace Simulation Attempt {attempt + 1}/{max_retries}")
            last_results = self._simulate_batch_internal(current_context, sinks)

            # Identify failures that might be fixed by context
            failed_sinks = [sid for sid, res in last_results.items() if not res.success]

            if not failed_sinks or not context_builder:
                return last_results

            # --- Hybrid Gap Detection ---
            new_code_blocks = []
            fetched_names = set()

            # Layer 1: Graph-based gap detection (fast, no LLM call)
            if hasattr(context_builder, 'get_graph_detected_gaps'):
                graph_gaps = context_builder.get_graph_detected_gaps()
                for func_name in graph_gaps:
                    if f"function {func_name}" in current_context:
                        continue
                    code = context_builder.get_function_code_by_name(func_name)
                    if code:
                        new_code_blocks.append(f"// Graph-Detected Dependency: {func_name}\n{code}")
                        fetched_names.add(func_name)
                        logger.info(f"[GraphGap] Retrieved: {func_name}")

            # Layer 2: LLM-based gap detection (semantic, for gaps graph analysis misses)
            logger.info("Analyzing missing context for failed traces...")
            missing = self.relevance_agent.analyze_missing_context(current_context, "Target Function in Context")

            if missing.missing_functions:
                for func_name in missing.missing_functions:
                    if func_name in fetched_names:
                        continue
                    if f"function {func_name}" in current_context:
                        continue
                    code = context_builder.get_function_code_by_name(func_name)
                    if code:
                        new_code_blocks.append(f"// LLM-Detected Dependency: {func_name}\n{code}")
                        fetched_names.add(func_name)

            if not new_code_blocks:
                logger.info("No missing context identified by either graph analysis or RelevanceAgent.")
                return last_results

            # Update context and retry
            current_context += "\n\n### DYNAMICALLY RETRIEVED CONTEXT:\n" + "\n".join(new_code_blocks)
            logger.info(f"Hybrid Gap Detection: Added {len(new_code_blocks)} missing functions "
                        f"({len([b for b in new_code_blocks if 'Graph-Detected' in b])} graph, "
                        f"{len([b for b in new_code_blocks if 'LLM-Detected' in b])} LLM). Retrying...")

        return last_results

    def _simulate_batch_internal(self, context: str, sinks: List[Dict[str, str]]) -> Dict[str, TraceGenerationResult]:
        """
        单轮批量模拟，对每个 sink 生成结构化执行轨迹。
        """
        if not sinks:
            return {}
            
        system_prompt = (
            "You are a 'Structured Trace Analysis Engine' for smart contracts. Your task is to perform rigorous execution path modeling within graph-extracted context.\n"
            "Instead of simple text generation, you must perform **structured trace analysis** to track constraints and state changes.\n\n"
            "### INPUT:\n"
            "1. **Execution Context**: Contract source code (pruned via graph-guided context slicing).\n"
            "2. **Target Sinks**: List of vulnerable operations to reach.\n\n"
            "### METHODOLOGY (Structured Trace Analysis):\n"
            "For EACH sink, perform the following steps:\n"
            "1. **State Initialization ($\\sigma_0$)**: Define the initial state (e.g., `msg.sender` is an arbitrary external caller $\\alpha$, `balances` is a parameterized map).\n"
            "2. **Forward Execution ($\\sigma_t \\rightarrow \\sigma_{t+1}$)**: Simulate execution from function entry to the sink. **MANDATORY**: You MUST inline all Modifiers AND Internal Function Calls (e.g., `_burn`, `_transfer`) encountered in the path. Do not treat them as black boxes.\n"
            "3. **Constraint Accumulation ($\\pi$)**: For every `require`, `if`, or `assert`, record the path condition $\\pi$ required to proceed.\n"
            "4. **Taint Propagation (Data Flow)**: Track data flow from untrusted sources (`msg.data`, `msg.value`, parameters) to the sink.\n"
            "5. **Feasibility Check**: Ensure the accumulated path constraints are logically consistent (satisfiable).\n\n"
            "### OUTPUT FORMAT (JSON):\n"
            "**IMPORTANT**: You MUST generate a result for EVERY `sink_id` in the input list. If a sink is unreachable, set `success: false` and explain why in `error`. Do NOT omit any sink from the output JSON.\n"
            "{\n"
            "  \"results\": {\n"
            "    \"sink_id\": {\n"
            "      \"success\": true,\n"
            "      \"trace_lines\": [\n"
            "         \"1. [MODIFIER] onlyowner checks (msg.sender == owner)\",\n"
            "         \"2. [CONSTRAINT] require(amount > 0) => Must be True\",\n"
            "         \"3. [STATE_WRITE] balances[msg.sender] -= amount\",\n"
            "         \"4. [EXTERNAL_CALL] target.call(data)\"\n"
            "      ],\n"
            "      \"structured_trace\": [\n"
            "        {\"step\": 1, \"type\": \"CONSTRAINT\", \"code\": \"require(msg.sender == owner)\", \"formula\": \"msg.sender == owner\", \"taint_source\": null},\n"
            "        {\"step\": 2, \"type\": \"STATE_WRITE\", \"code\": \"balances[msg.sender] -= amount\", \"formula\": \"balances[msg.sender] := balances[msg.sender] - amount\", \"taint_source\": \"amount\"}\n"
            "      ]\n"
            "    }\n"
            "  }\n"
            "}"
        )
        
        sinks_desc = json.dumps(sinks, indent=2)
        user_prompt = f"### EXECUTION CONTEXT:\n{context}\n\n### TARGET SINKS:\n{sinks_desc}\n\nGenerate structured traces:"
        
        try:
            data = self.llm_service.call_completion(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                model=self.model,
                temperature=0.2,
                response_format={"type": "json_object"}
            )
            
            if not data or not isinstance(data, dict):
                raise ValueError("Invalid response from LLM")

            results_data = data.get("results", {})
            
            final_results = {}
            for sink in sinks:
                s_id = str(sink["id"])
                if s_id in results_data:
                    res = results_data[s_id]
                    final_results[s_id] = TraceGenerationResult(
                        trace_lines=res.get("trace_lines", []),
                        structured_trace=res.get("structured_trace", []),
                        success=res.get("success", False),
                        error=res.get("error")
                    )
                else:
                    final_results[s_id] = TraceGenerationResult(trace_lines=[], success=False, error="LLM skipped this sink")
            return final_results
            
        except Exception as e:
            logger.error(f"Batch Trace Simulation failed: {e}")
            return {str(s["id"]): TraceGenerationResult(trace_lines=[], success=False, error=str(e)) for s in sinks}
