import logging
import json
import time
import os
from datetime import datetime
from threading import Lock
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Optional, Set, Tuple
from contextlib import contextmanager

from pydantic import BaseModel

from src.core.graph_builder import CPGBuilder
from src.analysis.llm_trace_generator import TraceSimulatorAgent
from src.core.context_builder import ContextBuilder
# from src.core.mythril_runner import MythrilRunner # Mythril Removed
from src.analysis.static_analyzer import AccessControlAnalyzer
from src.llm.agent import MultiAgentSystem
from src.analysis.llm_verifier import LLMVerifier
from slither.core.declarations import Function

# Setup Logger
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

@contextmanager
def timer(name: str):
    start = time.time()
    yield
    end = time.time()
    logger.info(f"[{name}] took {end - start:.2f}s")

class VulnerabilityReport(BaseModel):
    contract_name: str
    function_name: str
    vulnerability_type: str
    root_cause: str
    severity: str
    remediation: str
    function_code: str = ""
    evidence: List[str] = []
    status: str = "OPEN"
    analysis_context: str = "" # Added to debug context issues

class Pipeline:
    def __init__(self, openai_api_key: Optional[str] = None):
        self.agents = MultiAgentSystem(api_key=openai_api_key)
        self.verifier = LLMVerifier(api_key=openai_api_key)
        self.trace_generator = TraceSimulatorAgent(api_key=openai_api_key)
        # self.mythril_runner = MythrilRunner(timeout=120) # Mythril Removed
        self.analysis_trace = []
        # self._mythril_cache = {} # Mythril Removed
        # self._mythril_lock = Lock() # Mythril Removed

    def save_analysis_trace(self, identifier: str):
        """
        Save analysis trace to a timestamped log file in 'logs/' directory.
        Args:
            identifier: Contract name or File path to use as filename prefix.
        """
        try:
            # Ensure logs directory exists
            log_dir = "logs"
            if not os.path.exists(log_dir):
                os.makedirs(log_dir)

            # Determine base name
            if identifier.endswith(".sol"):
                base_name = os.path.splitext(os.path.basename(identifier))[0]
            else:
                base_name = identifier
                
            # Sanitize filename (remove potentially illegal characters)
            base_name = "".join([c for c in base_name if c.isalnum() or c in ('_', '-')])

            # Generate timestamped filename
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"{base_name}_{timestamp}.json"
            output_path = os.path.join(log_dir, filename)

            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(self.analysis_trace, f, indent=2, ensure_ascii=False)
            logger.info(f"Detailed analysis trace saved to {output_path}")
            
            # Optional: Update 'latest.json' symlink or copy for convenience? 
            # For now, just strictly follow user request.
            
        except Exception as e:
            logger.error(f"Failed to save analysis trace: {e}")

    def analyze_contract(self, file_path: str, contract_name: Optional[str] = None,
                         solc_remaps=None) -> List[VulnerabilityReport]:
        reports = []
        start_time = time.time()
        self.analysis_trace = []
        # self._mythril_cache = {}  # Clear cache for new file analysis # Mythril Removed

        try:
            logger.info(f"Starting analysis for {file_path}")
            with timer("CPG Construction"):
                builder = CPGBuilder(file_path, solc_remaps=solc_remaps)
                cpg = builder.build()
            
            if not hasattr(builder, 'slither'):
                logger.error("Builder does not expose 'slither' object.")
                return []
            
            slither = builder.slither
            contracts = slither.contracts
            if contract_name:
                contracts = [c for c in contracts if c.name == contract_name]

            valid_contracts = []
            for contract in contracts:
                if contract.is_interface or contract.is_library:
                    continue

                has_implementation = any(f.is_implemented for f in contract.functions)
                if not has_implementation and not contract.state_variables:
                    continue
                valid_contracts.append(contract)

            # Filter to leaf contracts only: skip contracts that are inherited
            # by other contracts in the same file. In flattened DeFi projects,
            # base contracts (Ownable, ERC20, etc.) produce FPs when analyzed
            # independently; their functions are already analyzed via the
            # leaf (most-derived) contract that inherits them.
            inherited_names = set()
            for c in valid_contracts:
                for parent in c.inheritance:
                    if parent.name != c.name:
                        inherited_names.add(parent.name)
            leaf_contracts = [c for c in valid_contracts if c.name not in inherited_names]

            # Among leaf contracts, keep all that have at least a few
            # implemented functions.  Small auxiliary contracts (oracle
            # setters, reward configs, parameter stores) often contain
            # security-critical functions.  The threshold ≥3 implemented
            # functions retains these while skipping empty stubs and
            # pure-abstract leaves.
            if len(leaf_contracts) > 1:
                leaf_contracts = [c for c in leaf_contracts
                                  if sum(1 for f in c.functions if f.is_implemented) >= 3]

            if leaf_contracts:
                logger.info(f"Filtered to {len(leaf_contracts)} leaf contracts "
                           f"(from {len(valid_contracts)} total): "
                           f"{[c.name for c in leaf_contracts]}")
                valid_contracts = leaf_contracts
            
            logger.info(f"Analyzing {len(valid_contracts)} contracts in parallel...")
            
            with ThreadPoolExecutor(max_workers=5) as executor:
                future_to_contract = {
                    executor.submit(self._analyze_single_contract, contract, cpg, slither): contract
                    for contract in valid_contracts
                }
                
                for future in as_completed(future_to_contract):
                    contract = future_to_contract[future]
                    try:
                        contract_reports, contract_traces = future.result()
                        reports.extend(contract_reports)
                        self.analysis_trace.extend(contract_traces)
                        if time.time() - start_time > 300:
                            logger.warning(f"Global timeout reached for {file_path}. Stopping further contracts.")
                            executor.shutdown(wait=False)
                            break
                    except Exception as e:
                        logger.error(f"Error analyzing contract {contract.name}: {e}", exc_info=True)
            
            total_time = time.time() - start_time
            logger.info(f"Total analysis time: {total_time:.2f}s")
            
            # Use contract_name if provided, otherwise file_path base name
            log_identifier = contract_name if contract_name else file_path
            self.save_analysis_trace(log_identifier)
                
        except Exception as e:
            logger.error(f"Pipeline crashed for {file_path}: {e}", exc_info=True)
            
        return reports

    def _analyze_single_contract(self, contract, cpg, slither) -> Tuple[List[VulnerabilityReport], List[Dict]]:
        logger.info(f"Analyzing contract: {contract.name}")
        contract_traces = []
        
        # 1. Static Analysis (Pruning + Graph-Guided Sink Detection)
        # 传入 CPG 图和 node_mapping，启用图引导的 Sink 验证
        from src.core.graph_builder import CPGBuilder
        node_mapping = None
        if hasattr(cpg, 'graph'):
            # cpg is the graph itself (nx.MultiDiGraph)
            node_mapping = None
        # 从 builder 获取 node_mapping（需要在 analyze_contract 中传递）
        # 这里通过遍历图节点来重建 node_mapping
        _node_mapping = {}
        for gid, data in cpg.nodes(data=True):
            contract_name = data.get("contract_name", "GLOBAL")
            func_name = data.get("function_name", "GLOBAL")
            slither_node = data.get("slither_node")
            if slither_node:
                key = (contract_name, func_name, slither_node.node_id)
                _node_mapping[key] = gid
        
        ac_analyzer = AccessControlAnalyzer(contract, cpg=cpg, node_mapping=_node_mapping)
        with timer("Static Analysis"):
            # Returns Dict[Function, List[Sink]] directly (Sink 现在是 6 元素元组)
            relevant_map = ac_analyzer._identify_relevant_functions()
            relevant_functions = list(relevant_map.keys())
            
        if not relevant_functions:
            logger.info(f"No relevant functions found in {contract.name}. Skipping.")
            return [], []

        logger.info(f"Relevant Functions for {contract.name}: {[f.name for f in relevant_functions]}")
        
        # Flatten sinks for mapping logic (although relevant_map already has them)
        # We can simplify _map_reachable_sinks to just use relevant_map if we trust it covers everything.
        # But _map_reachable_sinks also handles Reachability from entry points to internal sinks.
        # Since _identify_relevant_functions now returns sinks directly found in those functions,
        # relevant_map[func] ARE the sinks reachable in func (trivially).
        
        reachable_sinks_map = relevant_map

        # 3. Context & Reachability (Context Builder is still needed for LLM)
        with timer("Context & Reachability"):
            context_builder = ContextBuilder(cpg, slither)
            contract_context = self._get_contract_context(contract)

        # 3.5. Precompute Peer Map (deterministic, no LLM)
        # For each relevant function, select structurally similar peers from
        # the same contract to support intra-contract comparative inference.
        peer_map = {}
        for func in relevant_functions:
            peer_map[func.name] = ac_analyzer.select_peers(func, relevant_map, k=3)

        # 4. Analysis Loop
        reports = []
        reported_funcs = set()
        
        # Prioritize Initialization Functions
        # Use sink type "public_initialization" from static analyzer (graph-derived S5)
        # rather than string matching on function names
        init_functions = [f for f in relevant_functions
                         if any(s[1] == "public_initialization" for s in reachable_sinks_map.get(f, []))]
        other_functions = [f for f in relevant_functions
                         if not any(s[1] == "public_initialization" for s in reachable_sinks_map.get(f, []))]
        
        # Global Vulnerability State (Shared across threads)
        global_state = {"owner_compromised": False}
        
        # --- Helper for Analysis Loop ---
        def run_analysis_loop(functions, label):
            with timer(f"Parallel Analysis Loop ({label})"):
                with ThreadPoolExecutor(max_workers=20) as executor:
                    future_to_func = {
                        executor.submit(
                            self._analyze_function_worker,
                            func,
                            reachable_sinks_map.get(func, []),
                            context_builder,
                            contract_context,
                            ac_analyzer,
                            global_state,
                            self._format_peer_evidence(peer_map.get(func.name, []))
                        ): func
                        for func in functions
                    }
                    
                    for future in as_completed(future_to_func):
                        func = future_to_func[future]
                        try:
                            func_reports, func_trace = future.result()
                            if func_trace:
                                contract_traces.append(func_trace)
                            if func_reports:
                                reports.extend(func_reports)
                                reported_funcs.add(func.name)
                                # Track if any initialization function is found vulnerable
                                # (use sink-type check instead of name matching)
                                if func in init_functions:
                                    global_state["owner_compromised"] = True
                        except Exception as e:
                            logger.error(f"Error analyzing function {func.name}: {e}", exc_info=True)

        run_analysis_loop(init_functions, "Init")
        run_analysis_loop(other_functions, "Others")
        
        return reports, contract_traces

    # Removed: _prune_functions, _detect_sinks, _map_reachable_sinks (now obsolete)
    
    def _analyze_function_worker(self, func, func_sinks, context_builder, contract_context, ac_analyzer, global_state=None, peer_evidence="") -> Tuple[List[VulnerabilityReport], Dict]:
        if not func_sinks: return [], {}
        
        contract = func.contract
        function_code = self._get_function_code_safe(func)
        
        # Inject Global State into Context
        injected_context = contract_context
        # User requested to NOT propagate cascading vulnerabilities to keep report clean.
        # We only track global_state for internal logic if needed, but do not inject it into LLM context.
        # if global_state and global_state.get("owner_compromised"):
        #      injected_context += "\n[CRITICAL WARNING - GLOBAL COMPROMISE DETECTED]:\n"
        #      injected_context += "The contract's initialization logic ('initWallet' or similar) allows ANYONE to become 'owner'.\n"
        #      injected_context += "THEREFORE, assume that 'msg.sender' IS THE OWNER (`isOwner(msg.sender) == true`).\n"
        #      injected_context += "ALSO assume 'msg.sender' can manipulate 'm_required' (e.g. set it to 1).\n"
        #      injected_context += "Any function relying on 'onlyowner' or 'onlymanyowners' is effectively UNPROTECTED."
        
        context_info = self._get_context_info(func) + "\n" + injected_context
        
        func_trace = {
            "contract_name": contract.name,
            "function_name": func.name,
            "status": "ANALYZING",
            "phases": {}
        }
        
        logger.info(f"Analyzing {func.name} with {len(func_sinks)} sinks...")

        # 1. Trace Simulation
        with timer(f"Trace Simulation ({func.name})"):
            collected_traces = self._run_trace_simulation(func, func_sinks, context_builder)
        if not collected_traces:
            func_trace["status"] = "SAFE_NO_TRACES"
            return [], func_trace

        # 2. Policy Inference
        # Generate Static Warnings based on sinks
        # Sink 元组格式: (node_id, sink_type, ir, invariants, gid, is_guarded)
        static_warnings = []
        has_state_mod = False

        # Standard DeFi operations where [UNGUARDED] is expected by design.
        # Suppress misleading warnings for these to prevent Policy Agent from
        # hallucinating permission requirements.
        _DEFI_SELF_SERVICE_NAMES = {
            "deposit", "withdraw", "transfer", "transferfrom", "approve", "burn",
            "mint", "swap", "borrow", "repay", "liquidate", "claim", "stake",
            "unstake", "delegate", "redeem", "supply", "exit", "enter",
            "safetransferfrom", "increaseallowance", "decreaseallowance",
            "increaseapproval", "decreaseapproval", "setapprovalforall",
            "permit", "delegatebysig",
        }
        is_standard_defi_op = func.name.lower() in _DEFI_SELF_SERVICE_NAMES

        for sink in func_sinks:
            node_id, sink_type, ir, invariants = sink[0], sink[1], sink[2], sink[3]
            gid = sink[4] if len(sink) > 4 else None
            is_guarded = sink[5] if len(sink) > 5 else False

            if sink_type == "state_modification":
                has_state_mod = True

            # [Graph-Guided] 如果 Sink 未被守卫保护，生成更强的警告
            # Suppress [UNGUARDED] for standard DeFi self-service operations to avoid
            # biasing the Policy Agent toward false "Restricted" classifications.
            if not is_guarded and sink_type in ("external_interaction", "state_modification"):
                if not is_standard_defi_op:
                    static_warnings.append(f"[UNGUARDED] {sink_type} at node {node_id} has NO role-gated guard in CPG.")

            # [Graph-Guided] 检测未检查返回值的低级调用（基于 IR 类型而非字符串匹配）
            if sink_type == "external_interaction" and ir is not None:
                from slither.slithir.operations import LowLevelCall as _LLC
                if isinstance(ir, _LLC):
                    static_warnings.append(f"Low-level call detected at node {node_id}. Potential for arbitrary execution.")

        # [Graph-Guided] 使用图派生的守卫状态和控制变量替代字符串匹配
        # 检查是否有未守卫的 Sink 修改了控制变量（由 ROLE_GATED 边拓扑派生）
        has_unguarded_sink = any(not (sink[5] if len(sink) > 5 else False) for sink in func_sinks)
        if has_state_mod and has_unguarded_sink:
            # 使用图派生的控制变量集合（来自 AC-CPG 的 ROLE_GATED 边），而非关键字匹配
            control_var_names = {v.name for v in ac_analyzer.critical_state_vars} if ac_analyzer else set()
            for var in func.state_variables_written:
                if var.name in control_var_names:
                    static_warnings.append(f"CRITICAL: Unguarded function modifies control variable '{var.name}' (derived from ROLE_GATED guard topology). Potential access control violation.")

        # [Cross-User Mutation] 检测参数控制的跨用户状态修改
        if ac_analyzer and hasattr(ac_analyzer, '_has_cross_user_mutation'):
            try:
                if ac_analyzer._has_cross_user_mutation(func):
                    static_warnings.append(
                        "[CROSS-USER MUTATION] Function can modify state of arbitrary users "
                        "via parameter-controlled mapping index (not msg.sender). "
                        "An attacker may manipulate another user's balance, allowance, or permissions."
                    )
            except Exception:
                pass

        # [Self-Service Context] 检测调用者自服务语义模式
        if ac_analyzer:
            try:
                ss_indicators = ac_analyzer._detect_self_service_indicators(func)
                if ss_indicators:
                    static_warnings.append(
                        "[SELF-SERVICE CONTEXT] Structural patterns confirm caller-only state modification:\n  - "
                        + "\n  - ".join(ss_indicators)
                    )
            except Exception:
                pass

        with timer(f"Policy Inference ({func.name})"):
            prediction = self._run_policy_inference(func, function_code, context_info, ac_analyzer, static_warnings, peer_evidence=peer_evidence)
        func_trace["phases"]["policy_inference"] = prediction.model_dump()

        invariants_str = prediction.security_invariants
        if isinstance(invariants_str, list):
            invariants_str = "; ".join(invariants_str)

        intended_policy_nl = f"Access Level: {prediction.access_level}\nSecurity Invariants: {invariants_str}\nSummary: {prediction.intended_policy_nl}"

        # Collect self-service indicators from static analysis for Verifier
        ss_indicators = []
        if ac_analyzer:
            try:
                ss_indicators = ac_analyzer._detect_self_service_indicators(func)
            except Exception:
                pass

        # Self-service short-circuit: if Policy Agent classified as Self-Service with
        # high confidence AND static analysis confirms sender-indexed writes AND
        # the static analyzer's _is_purely_self_service also agrees (which includes
        # the address parameter guard against cross-user writes), skip the LLM
        # Verifier entirely and mark as SAFE. This eliminates ~115 FP where the
        # Verifier overrides correct Self-Service classifications.
        #
        # Guard conditions prevent TP loss:
        # - _is_purely_self_service checks that no address parameters flow into
        #   mapping write indices (catches vulnerable transferFrom/approve)
        # - _has_cross_user_mutation checks for non-sender indexed state writes
        access_level = prediction.access_level
        is_self_service = "self-service" in access_level.lower() or "self service" in access_level.lower()
        if is_self_service and prediction.confidence >= 0.8 and ss_indicators:
            has_sender_indexed = any("SENDER_INDEXED_WRITE" in ind for ind in ss_indicators)
            # Additional guards: static analyzer must confirm the function is purely self-service
            # (no address params flowing into mapping write indices) and no cross-user mutation
            static_confirms_safe = False
            if has_sender_indexed and ac_analyzer:
                try:
                    is_pure_ss = ac_analyzer._is_purely_self_service(func, func_sinks)
                    has_cross_user = ac_analyzer._has_cross_user_mutation(func)
                    static_confirms_safe = is_pure_ss and not has_cross_user
                except Exception:
                    pass
            if has_sender_indexed and static_confirms_safe:
                logger.info(f"[SelfServiceShortCircuit] {func.name}: Policy=Self-Service (conf={prediction.confidence:.2f}), "
                           f"static confirms sender-indexed writes. Skipping Verifier → SAFE.")
                func_trace["phases"]["verification_shortcircuit"] = {
                    "reason": "Self-service short-circuit: Policy + static analysis agree on caller-only state modification",
                    "access_level": access_level,
                    "confidence": prediction.confidence,
                    "indicators": ss_indicators,
                    "status": "SAFE"
                }
                func_trace["status"] = "SAFE"
                return [], func_trace

        # 3. Verification & Reporting
        with timer(f"Verification ({func.name})"):
            function_reports, func_trace_status = self._run_verification(
                contract, func, collected_traces, intended_policy_nl, injected_context,
                function_code, func_trace, access_level=access_level,
                self_service_indicators=ss_indicators
            )
        
        found_vulnerability = len(function_reports) > 0

        if not found_vulnerability:
            # Be conservative: lack of a violating trace is not proof of safety.
            # If static semantics do NOT clearly confirm a purely caller-local pattern,
            # preserve the finding as unresolved rather than SAFE. This avoids
            # over-suppressing graph-selected candidate functions.
            preserve_unknown = False
            if ac_analyzer:
                try:
                    preserve_unknown = not ac_analyzer._is_purely_self_service(func, func_sinks)
                except Exception:
                    preserve_unknown = True
            else:
                preserve_unknown = True

            if preserve_unknown:
                func_trace["status"] = "UNKNOWN_NO_VIOLATING_TRACE"
            else:
                func_trace["status"] = "SAFE"
        
        return function_reports, func_trace

    def _run_trace_simulation(self, func, func_sinks, context_builder) -> List[Tuple]:
        collected_traces = []

        # [Graph-Guided] 从 Sink 中提取 GID，使用反向切片构建上下文
        # Sink 元组格式: (node_id, sink_type, ir, invariants, gid, is_guarded)
        sink_gids = []
        for sink in func_sinks:
            gid = sink[4] if len(sink) > 4 else None
            if gid is not None:
                sink_gids.append(gid)

        # 如果有 GID，使用反向切片构建上下文；否则回退到前向调用链
        if sink_gids:
            pruned_context = context_builder.build_sink_context(func, sink_gids)
        else:
            pruned_context = context_builder.build_function_context(func)

        # Prepare sinks for batch processing
        sinks_to_process = []
        for sink in func_sinks:
            node_id, sink_type, ir = sink[0], sink[1], sink[2]
            sink_expr = str(ir.expression) if hasattr(ir, 'expression') else str(ir)
            sink_desc = f"Type: {sink_type}, Code: {sink_expr}"
            sinks_to_process.append({"id": str(node_id), "description": sink_desc})
            
        logger.info(f"Batch simulating traces for {len(sinks_to_process)} sinks in {func.name}...")
        
        try:
            batch_results = self.trace_generator.simulate_batch(
                context=pruned_context, 
                sinks=sinks_to_process, 
                context_builder=context_builder
            )
            
            for sink in func_sinks:
                node_id, sink_type, ir = sink[0], sink[1], sink[2]
                s_id = str(node_id)
                if s_id in batch_results:
                    res = batch_results[s_id]
                    if res.success and res.trace_lines:
                         collected_traces.append((node_id, res.trace_lines, res.structured_trace))
                    else:
                         logger.warning(f"Trace simulation failed/skipped for {node_id}: {res.error}")
        except Exception as e:
             logger.error(f"Batch simulation error: {e}")

        return collected_traces

    def _run_policy_inference(self, func, function_code, context_info, ac_analyzer, static_warnings=None, peer_evidence=""):
        all_symbols = self._collect_symbols(func, ac_analyzer)
        # Pass function metadata to avoid string matching in agent
        func_metadata = {
            "is_constructor": func.is_constructor,
            "is_view": getattr(func, 'view', False) or getattr(func, 'is_view', False),
            "is_pure": getattr(func, 'pure', False) or getattr(func, 'is_pure', False),
        }
        return self.agents.auditor_agent.infer_policy(
            code=function_code,
            context=context_info,
            symbols=all_symbols,
            static_warnings=static_warnings,
            func_metadata=func_metadata,
            peer_evidence=peer_evidence
        )

    def _run_verification(self, contract, func, collected_traces, intended_policy_nl, contract_context, function_code, func_trace,
                          access_level: str = "", self_service_indicators: list = None) -> Tuple[List[VulnerabilityReport], str]:
        function_reports = []
        status = "ANALYZING"
        
        # Deduplication Map: key = (vulnerability_type, root_cause)
        unique_reports = {}

        for node_id, trace_lines, structured_trace in collected_traces:
            verification_result = self.verifier.verify_trace(
                trace_lines=trace_lines,
                intended_policy=intended_policy_nl,
                contract_context=contract_context,
                access_level=access_level,
                self_service_indicators=self_service_indicators
            )
            
            func_trace["phases"][f"verification_{node_id}"] = {
                "trace": trace_lines,
                "structured_trace": structured_trace, # Saved for Academic/Audit purposes
                "status": verification_result.status,
                "reasoning": verification_result.reasoning
            }

            if verification_result.status == "VULNERABLE":
                # Dedupe: One report per function is sufficient for Access Control
                key = "VULNERABLE" 
                
                if key not in unique_reports:
                    report = VulnerabilityReport(
                        contract_name=contract.name,
                        function_name=func.name,
                        vulnerability_type="Access Control Violation",
                        root_cause=verification_result.reasoning,
                        severity=verification_result.severity,
                        remediation=f"Ensure the following policy is enforced: {intended_policy_nl}",
                        function_code=function_code,
                        evidence=trace_lines,
                        status="OPEN",
                        analysis_context=contract_context # Include context used for verification
                    )
                    unique_reports[key] = report
                    # Only log ONCE per unique vulnerability found
                    logger.warning(f"!!! VULNERABILITY FOUND: {contract.name}.{func.name} (Severity: {verification_result.severity}) !!!")
                
                func_trace["status"] = "VULNERABLE"
                status = "VULNERABLE"
        
        function_reports = list(unique_reports.values())
        return function_reports, status

    # Mythril methods removed

    def _collect_symbols(self, func, ac_analyzer) -> Dict[str, str]:
        symbols = {}
        # Collect from critical state vars, read/written vars, and parameters
        sources = [
            ac_analyzer.critical_state_vars,
            func.state_variables_read,
            func.state_variables_written,
            func.parameters
        ]
        
        for source_list in sources:
            for var in source_list:
                if var.name and var.name not in symbols:
                    symbols[var.name] = str(var.type)
        return symbols

    def _get_context_info(self, func) -> str:
        context = []
        if func.modifiers:
            context.append(f"Function Modifiers: {[m.name for m in func.modifiers]}")
        state_vars = set(func.state_variables_read + func.state_variables_written)
        if state_vars:
            context.append(f"State Vars Read/Written in this function: {[v.name for v in state_vars]}")
        return "\n".join(context)

    def _get_contract_context(self, contract) -> str:
        context = ["[CONTRACT CONTEXT]"]
        if contract.state_variables:
            vars_info = []
            for var in contract.state_variables:
                vars_info.append(f"{var.type} {var.visibility} {var.name}")
            context.append(f"State Variables Defined:\n" + "\n".join(vars_info))
        if contract.modifiers:
            mods_info = []
            for mod in contract.modifiers:
                code = self._get_function_code_safe(mod)
                mods_info.append(f"modifier {mod.name} {{\n{code}\n}}")
            context.append(f"Modifiers Implementation:\n" + "\n".join(mods_info))
        return "\n\n".join(context)

    def _get_function_code_safe(self, func) -> str:
        try:
            if func.source_mapping and func.source_mapping.filename.absolute:
                with open(func.source_mapping.filename.absolute, 'r', encoding='utf-8') as f:
                    content = f.read()
                    start = func.source_mapping.start
                    length = func.source_mapping.length
                    if start >= 0 and length > 0 and start + length <= len(content):
                        return content[start : start + length]
        except Exception:
            pass
        try:
             if hasattr(func, 'source_code'): return func.source_code
        except:
            pass
        return f"function {func.name}(...) {{ /* Source Code Unavailable */ }}"

    def _format_peer_evidence(self, peers: List[Dict]) -> str:
        """Format peer function data into a text block for the Auditor prompt."""
        if not peers:
            return ""
        lines = ["[PEER FUNCTION EVIDENCE]"]
        for i, peer in enumerate(peers, 1):
            guarded_str = "GUARDED (has access control)" if peer["is_guarded"] else "UNGUARDED (no access control)"
            lines.append(f"\n--- Peer {i}: {peer['func_name']} (similarity={peer['score']:.2f}, {guarded_str}) ---")
            if peer["shared_state_vars"]:
                lines.append(f"Shared state variables: {', '.join(peer['shared_state_vars'])}")
            if peer["sink_types"]:
                lines.append(f"Sink types: {', '.join(peer['sink_types'])}")
            if peer["modifiers"]:
                lines.append(f"Modifiers: {', '.join(peer['modifiers'])}")
            lines.append(f"Code:\n{peer['code']}")
        return "\n".join(lines)
