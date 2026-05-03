import networkx as nx
import heapq
import logging
from typing import List, Dict, Any, Set, Optional, Tuple, Union
from slither.core.declarations import Function, Structure, Enum, Contract
from slither.core.variables.state_variable import StateVariable
from slither.core.solidity_types import UserDefinedType, MappingType, ArrayType
from slither.slithir.operations import (
    HighLevelCall, InternalCall, LibraryCall, 
    LowLevelCall, Send, Transfer, Return
)
from src.core.graph_builder import EdgeRegistry, EdgeSemantic

logger = logging.getLogger(__name__)

class ContextBuilder:
    """
    基于 AC-CPG 的上下文构建器，提取语义完整执行环境（SCEE）。

    从 Sink 出发沿 AC-CPG 语义边反向切片，收集影响 Sink 的节点（含跨函数状态依赖和权限守卫），
    同时提取类型定义（Struct/Enum）、状态变量、外部调用接口桩。
    """
    
    def __init__(self, cpg: nx.MultiDiGraph, contract_slither):
        self.graph = cpg
        self.slither = contract_slither
        self._visited_callees = set()
        self._collected_types = set()
        self._collected_interfaces = set()
        # 缓存最近一次切片的结果，供反馈循环中的图结构化缺口检测使用
        self._last_reachable_gids = set()
        self._last_sliced_functions = []
        
    def build_function_context(self, target_func: Function, max_depth: int = 5) -> str:
        """
        为目标函数构建裁剪后的上下文。
        
        Components:
        1.  Target Function Source
        2.  Transitive Callee Source (Recursively collected)
        3.  Type Definitions (Structs/Enums used in context)
        4.  State Variables (Read/Written in context)
        5.  Interface Stubs (For external calls found in context)
        """
        self._visited_callees.clear()
        self._collected_types.clear()
        self._collected_interfaces.clear()
        
        context_parts = []
        
        # --- 1. Control Flow Slice (Functions) ---
        # Collect target and all recursive callees
        all_functions = [target_func] + self._get_recursive_callees(target_func, depth=0, max_depth=max_depth)
        
        # --- 2. Type Dependency Slice (Structs/Enums) ---
        # Scan all collected functions for type usage
        for func in all_functions:
            self._collect_type_dependencies(func)
            
        # --- 3. External Interface Slice ---
        # Scan for HighLevelCalls to generate stubs
        for func in all_functions:
            self._scan_for_interfaces(func)

        # --- 4. State Variable Slice ---
        relevant_vars = self._get_relevant_state_vars(all_functions)
        
        # [Fix] Scan state variables for types (Structs/Enums)
        for var in relevant_vars:
            self._extract_type_from_var(var.type)
        
        # === ASSEMBLY ===
        
        # A. Type Definitions (Top of file usually)
        if self._collected_types:
            context_parts.append("### TYPE DEFINITIONS (Structs/Enums):")
            for t in sorted(list(self._collected_types), key=lambda x: x.name):
                context_parts.append(self._get_type_definition(t))
            context_parts.append("")

        # B. Interface Stubs
        if self._collected_interfaces:
            context_parts.append("### EXTERNAL INTERFACES (Stubs):")
            for stub in self._collected_interfaces:
                context_parts.append(stub)
            context_parts.append("")

        # C. State Variables
        if relevant_vars:
            context_parts.append("### STATE VARIABLES (Context-Relevant):")
            for var in relevant_vars:
                context_parts.append(self._format_state_var(var))
            context_parts.append("")

        # E. Modifiers (of target only, as callees' modifiers are usually inline or less relevant for trace)
        # Move MODIFIERS before TARGET FUNCTION as requested
        if target_func.modifiers:
            context_parts.append("### MODIFIERS (Inlined Logic):")
            for mod in target_func.modifiers:
                # Include modifier code
                context_parts.append(self._inline_modifier(mod))
                
                # Also include internal calls made by the modifier (e.g. confirmAndCheck)
                for call in mod.internal_calls:
                    if isinstance(call, Function):
                        context_parts.append(f"// Helper used in modifier {mod.name}:")
                        context_parts.append(self._get_function_code(call))
                        
                        # Recurse for helper's callees if not already visited
                        helpers = self._get_recursive_callees(call, 0, 2) # Shallow depth for helpers
                        for h in helpers:
                             if h.canonical_name not in self._visited_callees:
                                 context_parts.append(f"// Helper used in {call.name}:")
                                 context_parts.append(self._get_function_code(h))
                                 self._visited_callees.add(h.canonical_name)
            context_parts.append("")

        # D. Function Implementations
        context_parts.append(f"### TARGET FUNCTION: {target_func.name}")
        context_parts.append(self._get_function_code(target_func))
        context_parts.append("")

        return "\n".join(context_parts)

    def _get_recursive_callees(self, func: Function, depth: int, max_depth: int) -> List[Function]:
        """
        递归收集被调用函数，包括库调用、继承的内部调用和 this 调用。
        """
        if depth >= max_depth:
            return []
            
        callees = []
        
        # Slither's internal_calls includes:
        # 1. Internal function calls
        # 2. Private function calls
        # 3. Library calls (if linked/internal)
        
        potential_calls = []
        
        # Handle internal_calls (might contain InternalCall IR or Function objects)
        for call in func.internal_calls:
            if isinstance(call, Function):
                potential_calls.append(call)
            elif isinstance(call, (InternalCall, LibraryCall)):
                potential_calls.append(call.function)
        
        # Scan for HighLevelCalls to address(this) which might be missed
        for node in func.nodes:
            for ir in node.irs:
                if isinstance(ir, HighLevelCall):
                    # Check if destination is compatible (same contract hierarchy)
                    if ir.function and (ir.function.contract == func.contract or ir.function.contract in func.contract.inheritance):
                         if ir.function not in potential_calls:
                             potential_calls.append(ir.function)

        for call in potential_calls:
            if not isinstance(call, Function): continue
            
            # Unique ID for visited set
            call_id = call.canonical_name
            if call_id in self._visited_callees: continue
            
            # Logic: Include if it's executable code we can analyze
            # 1. Same contract (Private/Internal/Public to self)
            # 2. Inherited contract (Super/Internal)
            # 3. Library (Code is available)
            
            is_same_contract = call.contract == func.contract
            is_inherited = call.contract in func.contract.inheritance
            is_library = call.contract.is_library
            
            if is_same_contract or is_inherited or is_library:
                self._visited_callees.add(call_id)
                callees.append(call)
                # Recurse
                callees.extend(self._get_recursive_callees(call, depth + 1, max_depth))
                
        return callees

    def _collect_type_dependencies(self, func: Function):
        """
        Extracts UserDefinedTypes (Structs, Enums) from function signature and body.
        """
        # 1. Parameters & Returns
        for var in func.parameters + func.returns:
            self._extract_type_from_var(var.type)
            
        # 2. Local Variables
        for var in func.variables:
             self._extract_type_from_var(var.type)

    def _extract_type_from_var(self, type_obj):
        """Helper to unwrap arrays/mappings and find the base UserDefinedType."""
        if isinstance(type_obj, UserDefinedType):
            if isinstance(type_obj.type, (Structure, Enum)):
                self._collected_types.add(type_obj.type)
        elif isinstance(type_obj, (MappingType, ArrayType)):
             # Recurse for Mapping(Key => Value) or Array[]
             if hasattr(type_obj, 'type_from'): self._extract_type_from_var(type_obj.type_from)
             if hasattr(type_obj, 'type_to'): self._extract_type_from_var(type_obj.type_to)
             if hasattr(type_obj, 'type'): self._extract_type_from_var(type_obj.type)

    def get_graph_detected_gaps(self) -> List[str]:
        """
        返回最近一次切片中图结构化检测到的未解析调用目标。

        供反馈循环调用：先通过此方法做快速图分析，
        再用 RelevanceAgent (LLM) 做补充的语义分析。
        """
        if not self._last_reachable_gids or not self._last_sliced_functions:
            return []
        return self._detect_unresolved_calls(self._last_reachable_gids, self._last_sliced_functions)

    def get_function_code_by_name(self, func_name: str) -> Optional[str]:
        """
        Dynamic Context Retrieval:
        Search for a function by name across all contracts in the project (or current contract hierarchy).
        Used by TraceSimulatorAgent to fetch missing context on-demand.
        """
        # 1. Check if self.slither is the global Slither object
        if hasattr(self.slither, 'contracts'):
            for contract in self.slither.contracts:
                for f in contract.functions + contract.modifiers:
                    if f.name == func_name:
                        return self._get_function_code(f)
        
        # 2. Check if self.slither is a Contract object (fallback)
        elif hasattr(self.slither, 'functions'):
             for f in self.slither.functions + self.slither.modifiers:
                 if f.name == func_name:
                     return self._get_function_code(f)
        
        return None

    def _scan_for_interfaces(self, func: Function):
        """
        Scans for HighLevelCalls to EXTERNAL contracts and generates interface stubs.
        This is crucial for LLM to understand `token.transfer(...)` if `token` is an interface.
        """
        for node in func.nodes:
            for ir in node.irs:
                if isinstance(ir, HighLevelCall):
                    target_func = ir.function
                    if not target_func: continue
                    
                    # If target is in the context (e.g. library or local), skip
                    if target_func.canonical_name in self._visited_callees: continue
                    if target_func.contract == func.contract: continue
                    
                    # It's an external call. Generate a stub.
                    stub = self._generate_interface_stub(target_func)
                    if stub:
                        self._collected_interfaces.add(stub)

    def _generate_interface_stub(self, func: Function) -> str:
        """Generates 'function name(params) external returns (ret)'"""
        try:
            params = ", ".join([f"{p.type} {p.name}" for p in func.parameters])
            returns = ""
            if func.returns:
                rets = ", ".join([f"{r.type} {r.name}" for r in func.returns])
                returns = f" returns ({rets})"
            
            # Use contract name as namespace if possible
            contract_name = func.contract.name if func.contract else "External"
            return f"// Interface: {contract_name}\nfunction {func.name}({params}) external{returns};"
        except:
            return f"function {func.name}(...) external;"

    def _get_relevant_state_vars(self, functions: List[Function]) -> Set[StateVariable]:
        """Collects state variables used in the function set, PLUS constants."""
        vars_found = set()
        for func in functions:
            vars_found.update(func.state_variables_read)
            vars_found.update(func.state_variables_written)
        return vars_found

    def _format_state_var(self, var: StateVariable) -> str:
        """Formats state variable with initial value if constant."""
        base = f"{var.type} {var.name}"
        if var.is_constant:
            # Try to get value
            if var.expression:
                return f"{base} = {var.expression}; // constant"
            return f"{base}; // constant"
        if var.is_immutable:
             return f"{base}; // immutable"
        return f"{base};"

    def _get_type_definition(self, type_obj: Union[Structure, Enum]) -> str:
        """Returns the source code definition of a Struct or Enum."""
        if isinstance(type_obj, Structure):
            # Reconstruct struct
            members = [f"    {elem.type} {elem.name};" for elem in type_obj.elems.values()]
            return f"struct {type_obj.name} {{\n" + "\n".join(members) + "\n}"
        elif isinstance(type_obj, Enum):
            vals = ", ".join(type_obj.values)
            return f"enum {type_obj.name} {{ {vals} }}"
        return ""

    def _get_function_code(self, func) -> str:
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
        # Fallback to Slither's source_code attribute if available (v0.10+)
        if hasattr(func, 'source_code'):
            return func.source_code
        return f"function {func.name}(...) {{ /* Source Unavailable */ }}"

    def _inline_modifier(self, mod) -> str:
        """
        Inline modifier logic for trace simulation.
        Replaces the Solidity `_;` placeholder with a comment marker.
        Only replaces the standalone `_;` pattern, not underscores in variable names.
        """
        code = self._get_function_code(mod)
        # Only replace the Solidity placeholder `_;`, not underscores in identifiers
        import re
        return re.sub(r'\b_\s*;', '// [EXECUTION BODY GOES HERE];', code)

    # =========================================================================
    # AC-Aware Relevance-Guided Backward Slicing (论文 Algorithm 1)
    # =========================================================================

    # Decay factor per hop: controls how quickly relevance diminishes with distance
    DECAY_FACTOR = 0.85
    # Minimum relevance threshold: nodes below this are excluded from the slice
    RELEVANCE_THRESHOLD = 0.05

    def _backward_slice_functions(self, sink_gids: List[int], max_hops: int = 15,
                                   decay: float = None, threshold: float = None
                                   ) -> Tuple[List[Function], Set[int]]:
        """
        AC-Aware Relevance-Guided Backward Slicing.

        从 Sink 节点出发，在 AC-CPG 上执行基于相关性传播的反向切片。
        使用最大优先队列（修改版 Dijkstra），沿语义边反向遍历，
        根据边类型的 AC 语义权重和索引敏感置信度传播相关性得分。

        与传统 BFS 的区别：
        1. AC 语义优先级：ROLE_GATED/ROLE_FLOW 等 AC 守卫边权重最高（1.0），
           保证权限相关路径优先探索
        2. 置信度感知：STATE_DEPENDENCY 边根据索引敏感匹配的置信度
           (High/Medium/Low) 动态调整权重
        3. 软边界：相关性自然衰减，替代硬性跳数限制，
           使切片范围自适应图结构
        4. 排序输出：函数按最大相关性得分排序，
           下游 Agent 可据此聚焦最相关的 AC 代码

        算法本质：最大乘积路径问题（Maximum-Product Path），
        通过 max-heap 实现 O((V+E)logV) 复杂度。

        Returns:
            (functions, reachable_gids): 按相关性排序的函数列表和可达节点 GID 集合
        """
        α = decay if decay is not None else self.DECAY_FACTOR
        τ = threshold if threshold is not None else self.RELEVANCE_THRESHOLD

        slice_edge_types = EdgeRegistry.get_slice_edge_types()

        # rel[gid] = maximum relevance score reached so far
        rel: Dict[int, float] = {}
        reachable_gids: Set[int] = set()

        # Max-heap: store (-relevance, gid) since heapq is a min-heap
        heap: List[Tuple[float, int]] = []

        for gid in sink_gids:
            if gid in self.graph:
                rel[gid] = 1.0
                heapq.heappush(heap, (-1.0, gid))

        while heap:
            neg_r, u = heapq.heappop(heap)
            r_u = -neg_r

            # Skip if a better path to u was already processed
            if r_u < rel.get(u, 0.0) - 1e-9:
                continue

            reachable_gids.add(u)

            # Standard backward traversal: follow predecessors along dependency edges
            for predecessor in self.graph.predecessors(u):
                edge_data_dict = self.graph.get_edge_data(predecessor, u)
                if not edge_data_dict:
                    continue

                # Find the best edge weight among all parallel edges
                best_w = 0.0
                for _, edge_data in edge_data_dict.items():
                    etype = edge_data.get("edge_type", "")
                    if etype not in slice_edge_types:
                        continue
                    conf = edge_data.get("confidence", "")
                    w = EdgeRegistry.get_slice_weight(etype, conf)
                    if w > best_w:
                        best_w = w

                if best_w <= 0.0:
                    continue

                # Propagate relevance: r_v = r_u × w × α
                r_v = r_u * best_w * α

                if r_v >= τ and r_v > rel.get(predecessor, 0.0):
                    rel[predecessor] = r_v
                    heapq.heappush(heap, (-r_v, predecessor))

            # Forward traversal along STATE_DEPENDENCY edges only:
            # For AC analysis, a state variable write's significance depends on
            # how that variable is read/used as a guard in other functions.
            # Traversing successors along STATE_DEPENDENCY edges includes these
            # cross-function readers, providing essential context for policy inference.
            for successor in self.graph.successors(u):
                edge_data_dict = self.graph.get_edge_data(u, successor)
                if not edge_data_dict:
                    continue

                best_w = 0.0
                for _, edge_data in edge_data_dict.items():
                    etype = edge_data.get("edge_type", "")
                    if etype != "STATE_DEPENDENCY":
                        continue
                    conf = edge_data.get("confidence", "")
                    w = EdgeRegistry.get_slice_weight(etype, conf)
                    if w > best_w:
                        best_w = w

                if best_w <= 0.0:
                    continue

                r_v = r_u * best_w * α

                if r_v >= τ and r_v > rel.get(successor, 0.0):
                    rel[successor] = r_v
                    heapq.heappush(heap, (-r_v, successor))

        # Extract unique functions with their maximum relevance scores
        func_relevance: Dict[str, Tuple[Function, float]] = {}
        for gid in reachable_gids:
            node_data = self.graph.nodes.get(gid)
            if not node_data:
                continue
            slither_node = node_data.get("slither_node")
            if slither_node and slither_node.function:
                func = slither_node.function
                cname = func.canonical_name
                node_rel = rel.get(gid, 0.0)
                if cname not in func_relevance or node_rel > func_relevance[cname][1]:
                    func_relevance[cname] = (func, node_rel)

        # Sort functions by relevance (descending) for downstream agents
        sorted_funcs = sorted(func_relevance.values(), key=lambda x: x[1], reverse=True)
        functions = [f for f, _ in sorted_funcs]

        return functions, reachable_gids

    def _detect_unresolved_calls(self, reachable_gids: Set[int], sliced_functions: List[Function]) -> List[str]:
        """
        图结构化缺口检测：识别反向切片中未解析的调用目标。

        遍历切片内所有节点的 IR 指令，检查 InternalCall / HighLevelCall / LibraryCall
        的目标函数是否已包含在切片结果中。未包含的函数名被视为潜在的上下文缺口，
        可通过 get_function_code_by_name 动态补全。

        这是一个纯图结构分析方法（无需 LLM 调用），作为 LLM-based RelevanceAgent 的
        快速前置检测层，减少对 LLM 缺口检测的依赖。
        """
        sliced_canonical = {f.canonical_name for f in sliced_functions}
        unresolved = []

        for gid in reachable_gids:
            node_data = self.graph.nodes.get(gid)
            if not node_data:
                continue
            slither_node = node_data.get("slither_node")
            if not slither_node:
                continue

            for ir in slither_node.irs:
                if isinstance(ir, (InternalCall, HighLevelCall, LibraryCall)):
                    target_func = ir.function
                    if not target_func or not hasattr(target_func, 'canonical_name'):
                        continue
                    if target_func.canonical_name not in sliced_canonical:
                        func_name = target_func.name
                        if func_name not in unresolved:
                            unresolved.append(func_name)

        return unresolved

    def build_sink_context(self, target_func: Function, sink_gids: List[int], max_hops: int = 15) -> str:
        """
        基于反向切片为 Sink 构建上下文（替代 build_function_context）。
        
        论文对应：Section 3.3 - Graph-Guided Context Slicing
        
        从 Sink 出发反向遍历 AC-CPG，找到所有相关函数（包括目标函数自身、
        调用链、守卫 Modifier、以及通过状态依赖边发现的跨函数依赖），
        然后按照与 build_function_context() 相同的格式输出纯源代码上下文。
        
        Args:
            target_func: 目标函数（用于确定 Modifier 等）
            sink_gids: 该函数中所有 Sink 的全局节点 ID 列表
            max_hops: 反向切片最大跳数
        """
        self._visited_callees.clear()
        self._collected_types.clear()
        self._collected_interfaces.clear()
        
        # 反向切片：从 Sink 出发找到所有相关函数
        all_functions, reachable_gids = self._backward_slice_functions(sink_gids, max_hops=max_hops)

        # 缓存切片结果供反馈循环使用
        self._last_reachable_gids = reachable_gids
        self._last_sliced_functions = list(all_functions)

        # 确保目标函数在列表中
        target_in_list = any(f.canonical_name == target_func.canonical_name for f in all_functions)
        if not target_in_list:
            all_functions.insert(0, target_func)

        # 图结构化缺口检测：发现切片遗漏的调用目标
        unresolved_calls = self._detect_unresolved_calls(reachable_gids, all_functions)
        gap_functions = []
        for func_name in unresolved_calls:
            code = self.get_function_code_by_name(func_name)
            if code:
                gap_functions.append((func_name, code))
                logger.info(f"[GapDetection] {target_func.name}: graph-detected missing dependency: {func_name}")

        logger.info(f"[BackwardSlice] {target_func.name}: discovered {len(all_functions)} functions "
                     f"(+{len(gap_functions)} graph-detected gaps): "
                     f"{[f.name for f in all_functions]}")
        
        # 记录已访问的函数
        for func in all_functions:
            self._visited_callees.add(func.canonical_name)
        
        # 以下与 build_function_context() 相同的组装逻辑
        context_parts = []
        
        # 类型依赖
        for func in all_functions:
            self._collect_type_dependencies(func)
        
        # 外部接口
        for func in all_functions:
            self._scan_for_interfaces(func)
        
        # 状态变量
        relevant_vars = self._get_relevant_state_vars(all_functions)
        for var in relevant_vars:
            self._extract_type_from_var(var.type)
        
        # === ASSEMBLY（与 build_function_context 格式一致） ===
        
        if self._collected_types:
            context_parts.append("### TYPE DEFINITIONS (Structs/Enums):")
            for t in sorted(list(self._collected_types), key=lambda x: x.name):
                context_parts.append(self._get_type_definition(t))
            context_parts.append("")

        if self._collected_interfaces:
            context_parts.append("### EXTERNAL INTERFACES (Stubs):")
            for stub in self._collected_interfaces:
                context_parts.append(stub)
            context_parts.append("")

        if relevant_vars:
            context_parts.append("### STATE VARIABLES (Context-Relevant):")
            for var in relevant_vars:
                context_parts.append(self._format_state_var(var))
            context_parts.append("")

        if target_func.modifiers:
            context_parts.append("### MODIFIERS (Inlined Logic):")
            for mod in target_func.modifiers:
                context_parts.append(self._inline_modifier(mod))
                for call in mod.internal_calls:
                    if isinstance(call, Function):
                        context_parts.append(self._get_function_code(call))
            context_parts.append("")

        # 目标函数
        context_parts.append(f"### TARGET FUNCTION: {target_func.name}")
        context_parts.append(self._get_function_code(target_func))
        context_parts.append("")
        
        # 反向切片发现的其他相关函数（纯源码）
        for func in all_functions:
            if func.canonical_name == target_func.canonical_name:
                continue
            context_parts.append(self._get_function_code(func))
            context_parts.append("")

        # 图结构化缺口补全：添加切片未覆盖但通过 CALL 边引用的函数
        if gap_functions:
            context_parts.append("### GRAPH-DETECTED DEPENDENCIES (Unresolved Calls):")
            for func_name, code in gap_functions:
                context_parts.append(f"// Dependency: {func_name} (detected via unresolved CALL edge)")
                context_parts.append(code)
                context_parts.append("")

        return "\n".join(context_parts)
