import networkx as nx
from typing import Optional, List, Dict, Set, Tuple, Any, Union
from enum import Enum, auto
from dataclasses import dataclass, field
from slither.slither import Slither
from slither.core.variables.state_variable import StateVariable
from slither.core.variables.local_variable import LocalVariable
from slither.core.solidity_types import MappingType, ArrayType, UserDefinedType
from slither.core.cfg.node import NodeType
from slither.core.declarations.solidity_variables import SolidityVariableComposed
from slither.analyses.data_dependency.data_dependency import is_dependent
from slither.slithir.operations import (
    HighLevelCall, InternalCall, LibraryCall,
    LowLevelCall, Send, Transfer, Return, SolidityCall, Index
)
from slither.slithir.variables.constant import Constant
from slither.slithir.variables.reference import ReferenceVariable

class EdgeSemantic(Enum):
    """Semantic tags for edge types."""
    PROPAGATES_DEPENDENCY = auto()
    REPRESENTS_GUARD = auto()
    REPRESENTS_CONTROL = auto()
    REPRESENTS_STATE_LINK = auto()


@dataclass
class EdgeTypeInfo:
    """Metadata for one edge type."""
    name: str
    semantics: Set[EdgeSemantic] = field(default_factory=set)
    description: str = ""
    slice_weight: float = 0.0


class EdgeRegistry:
    """Central registry for edge types."""
    _registry: Dict[str, EdgeTypeInfo] = {}
    
    @classmethod
    def register(cls, name: str, semantics: Set[EdgeSemantic], description: str = "", slice_weight: float = 0.0):
        cls._registry[name] = EdgeTypeInfo(name=name, semantics=semantics, description=description, slice_weight=slice_weight)
    
    @classmethod
    def get_types_by_semantic(cls, semantic: EdgeSemantic) -> Set[str]:
        """Return all edge types carrying `semantic`."""
        return {info.name for info in cls._registry.values() if semantic in info.semantics}
    
    @classmethod
    def get_slice_edge_types(cls) -> Set[str]:
        """Return edge types used during slicing."""
        return cls.get_types_by_semantic(EdgeSemantic.PROPAGATES_DEPENDENCY)
    
    @classmethod
    def get_guard_edge_types(cls) -> Set[str]:
        """Return edge types that encode guards."""
        return cls.get_types_by_semantic(EdgeSemantic.REPRESENTS_GUARD)
    
    @classmethod
    def all_types(cls) -> Set[str]:
        return set(cls._registry.keys())

    @classmethod
    def get_slice_weight(cls, edge_type: str, confidence: str = "") -> float:
        """Return the slice weight for an edge type."""
        info = cls._registry.get(edge_type)
        if not info:
            return 0.0
        w = info.slice_weight
        # Scale state-dependency edges by key-match confidence.
        if edge_type == "STATE_DEPENDENCY" and confidence:
            conf_map = {"High": 1.0, "Medium": 0.67, "Low": 0.33}
            w *= conf_map.get(confidence, 0.67)
        return w


# Registered edge types.
EdgeRegistry.register("CFG", {EdgeSemantic.REPRESENTS_CONTROL},
                       "Control Flow Graph edge", slice_weight=0.0)

EdgeRegistry.register("DFG", {EdgeSemantic.PROPAGATES_DEPENDENCY},
                       "Data Flow Graph edge (Reaching Definitions)", slice_weight=0.7)

EdgeRegistry.register("ROLE_FLOW", {EdgeSemantic.PROPAGATES_DEPENDENCY, EdgeSemantic.REPRESENTS_GUARD},
                       "Role propagation edge (msg.sender/owner data flow)", slice_weight=1.0)

EdgeRegistry.register("ROLE_GATED", {EdgeSemantic.REPRESENTS_GUARD, EdgeSemantic.PROPAGATES_DEPENDENCY},
                       "Auth guard edge: control node with sender check dominates target", slice_weight=1.0)

EdgeRegistry.register("CONTROL_DEPENDENCY", {EdgeSemantic.PROPAGATES_DEPENDENCY},
                       "Control dependency edge (dominator-based)", slice_weight=0.8)

EdgeRegistry.register("STATE_DEPENDENCY", {EdgeSemantic.PROPAGATES_DEPENDENCY, EdgeSemantic.REPRESENTS_STATE_LINK},
                       "Index-sensitive state dependency (cross-function)", slice_weight=0.9)

EdgeRegistry.register("CALL", {EdgeSemantic.PROPAGATES_DEPENDENCY},
                       "Inter-procedural call edge", slice_weight=0.5)

EdgeRegistry.register("MODIFIER_USE", {EdgeSemantic.PROPAGATES_DEPENDENCY, EdgeSemantic.REPRESENTS_GUARD},
                       "Function uses modifier edge", slice_weight=1.0)

EdgeRegistry.register("POST_DOMINATOR", set(),
                       "Post-dominator tree edge (internal, for ROLE_GATED construction)", slice_weight=0.0)

class CPGBuilder:
    def __init__(self, file_path, solc_remaps=None):
        """Build a whole-program CPG from one Solidity file."""
        self.file_path = file_path
        slither_kwargs = {}
        if solc_remaps:
            slither_kwargs["solc_remaps"] = solc_remaps
        try:
            self.slither = Slither(file_path, **slither_kwargs)
        except Exception as e:
            if "Stack too deep" in str(e):
                print("[CPGBuilder] Compilation failed (Stack too deep). Retrying with --via-ir...")
                self.slither = Slither(file_path, solc_args="--via-ir --optimize", **slither_kwargs)
            else:
                raise e

        self.graph = nx.MultiDiGraph()

        self.function_entry_points = {} 
        self.function_objects = {}
        self.function_call_contexts: Dict[str, List[Dict[str, Any]]] = {}
        self._call_context_signatures: Set[Tuple[str, str, Tuple[Tuple[str, str], ...]]] = set()
        self._symbolic_summary_cache: Dict[Tuple[str, int], str] = {}

        self.node_mapping = {}
        self.global_counter = 0

        self.current_contract = None

    def _get_global_id(self, node):
        """Return a file-wide node id."""
        func_name = node.function.name if node.function else "GLOBAL"
        contract_name = node.function.contract.name if node.function else "GLOBAL"
        
        key = (contract_name, func_name, node.node_id)
        
        if key not in self.node_mapping:
            self.node_mapping[key] = self.global_counter
            self.global_counter += 1
            
        return self.node_mapping[key]

    def build(self):
        """Build the CPG and its derived semantic edges."""
        # Register callable entry nodes first so later passes can link to them.
        for contract in self.slither.contracts:
            all_callables = (
                contract.functions + 
                contract.modifiers + 
                ([contract.constructor] if contract.constructor else [])
            )
            for func in all_callables:
                self.function_objects[func.canonical_name] = func
                # Reserve entry ids before linking cross-function edges.
                if func.nodes:
                    entry_node = func.entry_point
                    if entry_node:
                        gid = self._get_global_id(entry_node)
                        self.function_entry_points[func.canonical_name] = gid

        # Populate intra-procedural structure.
        for contract in self.slither.contracts:
            self.current_contract = contract
            all_callables = (
                contract.functions + 
                contract.modifiers + 
                ([contract.constructor] if contract.constructor else [])
            )
            for func in all_callables:
                self._process_function(func)
        
        # Add inter-procedural and semantic edges.
        self._compute_interprocedural_edges()
        self._compute_state_dependencies()
        self._compute_modifier_flow()

        return self.graph

    def _compute_state_dependencies(self):
        """Build key-aware cross-function state dependencies."""
        access_registry: Dict[str, List[Dict[str, Any]]] = {}
        confidence_rank = {"Low": 0, "Medium": 1, "High": 2}

        for gid, data in self.graph.nodes(data=True):
            slither_node = data.get("slither_node")
            if not slither_node:
                continue

            accesses = data.get("state_accesses") or self._extract_state_accesses(slither_node)
            function = getattr(slither_node, "function", None)

            for access in accesses:
                expanded_variants = self._expand_key_paths(function, access["key_path"])
                expanded_accesses = self.graph.nodes[gid].setdefault("expanded_state_accesses", [])
                for expanded_path, roots in expanded_variants.items():
                    expanded_accesses.append(
                        {
                            "mode": access["mode"],
                            "variable": access["variable"],
                            "expanded_key_path": expanded_path,
                            "principal": self._principal_token(expanded_path),
                            "root_functions": tuple(sorted(roots)),
                        }
                    )
                access_record = {
                    "gid": gid,
                    "mode": access["mode"],
                    "variable": access["variable"],
                    "var_object": access["var_object"],
                    "raw_key_path": access["key_path"],
                    "expanded_variants": expanded_variants,
                }
                access_registry.setdefault(access["variable"], []).append(access_record)

        for v_name, accesses in access_registry.items():
            writes = [access for access in accesses if access["mode"] == "write"]
            reads = [access for access in accesses if access["mode"] == "read"]

            for write_access in writes:
                for read_access in reads:
                    if write_access["gid"] == read_access["gid"]:
                        continue

                    best_confidence = None
                    best_write_path: Tuple[str, ...] = tuple()
                    best_read_path: Tuple[str, ...] = tuple()

                    best_write_roots: Tuple[str, ...] = tuple()
                    best_read_roots: Tuple[str, ...] = tuple()

                    for write_path, write_roots in write_access["expanded_variants"].items():
                        for read_path, read_roots in read_access["expanded_variants"].items():
                            confidence = self._match_key_paths(write_path, read_path)
                            if confidence is None:
                                continue
                            if (
                                best_confidence is None
                                or confidence_rank[confidence] > confidence_rank[best_confidence]
                            ):
                                best_confidence = confidence
                                best_write_path = write_path
                                best_read_path = read_path
                                best_write_roots = tuple(sorted(write_roots))
                                best_read_roots = tuple(sorted(read_roots))

                    if best_confidence is None:
                        continue

                    self.graph.add_edge(
                        write_access["gid"],
                        read_access["gid"],
                        edge_type="STATE_DEPENDENCY",
                        variable=v_name,
                        write_key_path=best_write_path,
                        read_key_path=best_read_path,
                        write_principal=self._principal_token(best_write_path),
                        read_principal=self._principal_token(best_read_path),
                        write_roots=best_write_roots,
                        read_roots=best_read_roots,
                        key_match=(
                            f"{self._path_to_string(best_write_path)}"
                            f"->{self._path_to_string(best_read_path)}"
                        ),
                        confidence=best_confidence,
                        label=f"sdg({v_name})",
                    )

    def _parameter_token(self, param: LocalVariable) -> str:
        return f"param:{self._get_var_name(param)}"

    @staticmethod
    def _token_kind(token: str) -> str:
        if token in ("sender", "tx_origin", "SCALAR"):
            return token
        return token.split(":", 1)[0]

    def _path_to_string(self, key_path: Tuple[str, ...]) -> str:
        if not key_path:
            return "SCALAR"
        return "|".join(key_path)

    def _principal_token(self, key_path: Tuple[str, ...]) -> str:
        if not key_path:
            return "SCALAR"
        return key_path[0]

    def _register_call_context(self, caller_func, callee_func, bindings: Dict[str, str]):
        if not caller_func or not callee_func or not bindings:
            return
        signature = (
            callee_func.canonical_name,
            caller_func.canonical_name,
            tuple(sorted(bindings.items())),
        )
        if signature in self._call_context_signatures:
            return
        self._call_context_signatures.add(signature)
        self.function_call_contexts.setdefault(callee_func.canonical_name, []).append(
            {
                "caller": caller_func.canonical_name,
                "bindings": dict(bindings),
            }
        )

    def _summarize_symbolic_value(self, var, context) -> str:
        func = None
        if context is not None:
            if hasattr(context, "function") and getattr(context, "function", None):
                func = context.function
            elif hasattr(context, "canonical_name"):
                func = context

        cache_key = ((func.canonical_name if func else "GLOBAL"), id(var))
        if cache_key in self._symbolic_summary_cache:
            return self._symbolic_summary_cache[cache_key]

        token = f"unknown:{self._get_var_name(var)}"

        if isinstance(var, SolidityVariableComposed):
            if var.name == "msg.sender":
                token = "sender"
            elif var.name == "tx.origin":
                token = "tx_origin"
            else:
                token = f"unknown:{var.name}"
        elif isinstance(var, Constant):
            token = f"const:{str(var)}"
        elif isinstance(var, StateVariable):
            token = f"state:{self._get_var_name(var)}"
        elif isinstance(var, ReferenceVariable):
            try:
                origin = var.points_to_origin
            except Exception:
                origin = None
            if origin is not None and origin is not var:
                token = self._summarize_symbolic_value(origin, func)
        elif isinstance(var, LocalVariable):
            if func and var in getattr(func, "parameters", []):
                token = self._parameter_token(var)
            elif func:
                try:
                    if is_dependent(var, SolidityVariableComposed("msg.sender"), func):
                        token = "sender"
                    elif is_dependent(var, SolidityVariableComposed("tx.origin"), func):
                        token = "tx_origin"
                    else:
                        param_matches = []
                        for param in getattr(func, "parameters", []):
                            try:
                                if is_dependent(var, param, func):
                                    param_matches.append(param)
                            except Exception:
                                continue
                        if len(param_matches) == 1:
                            token = self._parameter_token(param_matches[0])
                        else:
                            state_matches = []
                            contract = getattr(func, "contract", None)
                            if contract:
                                for state_var in getattr(contract, "state_variables", []):
                                    try:
                                        if is_dependent(var, state_var, func):
                                            state_matches.append(state_var)
                                    except Exception:
                                        continue
                            if len(state_matches) == 1:
                                token = f"state:{self._get_var_name(state_matches[0])}"
                except Exception:
                    token = f"unknown:{self._get_var_name(var)}"

        self._symbolic_summary_cache[cache_key] = token
        return token

    def _build_index_definitions(self, node) -> Dict[ReferenceVariable, Tuple[Any, Any]]:
        index_defs: Dict[ReferenceVariable, Tuple[Any, Any]] = {}
        for ir in node.irs:
            if isinstance(ir, Index) and isinstance(ir.lvalue, ReferenceVariable):
                index_defs[ir.lvalue] = (ir.variable_left, ir.variable_right)
        return index_defs

    def _resolve_reference_access(
        self,
        ref_var: ReferenceVariable,
        index_defs: Dict[ReferenceVariable, Tuple[Any, Any]],
        function,
    ) -> Optional[Dict[str, Any]]:
        key_tokens: List[str] = []
        current = ref_var
        visited: Set[int] = set()

        while isinstance(current, ReferenceVariable) and id(current) not in visited:
            visited.add(id(current))

            if current in index_defs:
                left_var, key_var = index_defs[current]
                key_tokens.append(self._summarize_symbolic_value(key_var, function))
                current = left_var
                continue

            points_to = getattr(current, "points_to", None)
            if points_to is not None and points_to is not current:
                current = points_to
                continue

            try:
                origin = current.points_to_origin
            except Exception:
                origin = None
            if origin is not None and origin is not current:
                current = origin
                continue
            break

        if isinstance(current, StateVariable):
            if isinstance(current.type, MappingType):
                return {
                    "state_var": current,
                    "key_path": tuple(reversed(key_tokens)),
                }
            return {
                "state_var": current,
                "key_path": tuple(),
            }
        return None

    def _extract_state_accesses(self, node) -> List[Dict[str, Any]]:
        function = getattr(node, "function", None)
        index_defs = self._build_index_definitions(node)
        access_map: Dict[Tuple[str, str, Tuple[str, ...]], Dict[str, Any]] = {}

        def add_access(mode: str, state_var: StateVariable, key_path: Tuple[str, ...]):
            access_key = (mode, self._get_var_name(state_var), key_path)
            if access_key in access_map:
                return
            access_map[access_key] = {
                "mode": mode,
                "variable": self._get_var_name(state_var),
                "var_object": state_var,
                "key_path": key_path,
            }

        for ir in node.irs:
            if isinstance(ir, Index):
                continue

            lvalue = getattr(ir, "lvalue", None)
            if isinstance(lvalue, StateVariable) and not isinstance(lvalue.type, MappingType):
                add_access("write", lvalue, tuple())
            elif isinstance(lvalue, ReferenceVariable):
                resolved = self._resolve_reference_access(lvalue, index_defs, function)
                if resolved:
                    add_access("write", resolved["state_var"], resolved["key_path"])

            for read_var in getattr(ir, "read", []) or []:
                if isinstance(read_var, StateVariable) and not isinstance(read_var.type, MappingType):
                    add_access("read", read_var, tuple())
                elif isinstance(read_var, ReferenceVariable):
                    resolved = self._resolve_reference_access(read_var, index_defs, function)
                    if resolved:
                        add_access("read", resolved["state_var"], resolved["key_path"])

        for state_var in node.variables_written:
            if isinstance(state_var, StateVariable) and not isinstance(state_var.type, MappingType):
                add_access("write", state_var, tuple())
        for state_var in node.variables_read:
            if isinstance(state_var, StateVariable) and not isinstance(state_var.type, MappingType):
                add_access("read", state_var, tuple())

        return list(access_map.values())

    def _substitute_key_path(self, key_path: Tuple[str, ...], bindings: Dict[str, str]) -> Tuple[str, ...]:
        return tuple(bindings.get(token, token) for token in key_path)

    def _expand_key_paths(
        self,
        function,
        key_path: Tuple[str, ...],
        visited: Optional[Set[Tuple[str, Tuple[str, ...]]]] = None,
    ) -> Dict[Tuple[str, ...], Set[str]]:
        if function is None:
            return {key_path: set()}

        param_tokens = {token for token in key_path if self._token_kind(token) == "param"}
        if not param_tokens:
            return {key_path: {function.canonical_name}}

        visit_key = (function.canonical_name, key_path)
        if visited is not None and visit_key in visited:
            return {key_path: {function.canonical_name}}

        local_visited = set(visited or set())
        local_visited.add(visit_key)

        contexts = self.function_call_contexts.get(function.canonical_name, [])
        applicable_contexts = [
            ctx for ctx in contexts if param_tokens.intersection(ctx["bindings"].keys())
        ]
        if not applicable_contexts:
            return {key_path: {function.canonical_name}}

        expanded: Dict[Tuple[str, ...], Set[str]] = {}
        for context in applicable_contexts:
            substituted = self._substitute_key_path(key_path, context["bindings"])
            caller_func = self.function_objects.get(context["caller"])
            if caller_func is None:
                expanded.setdefault(substituted, set()).add(context["caller"])
                continue
            caller_expansions = self._expand_key_paths(caller_func, substituted, local_visited)
            for path, roots in caller_expansions.items():
                expanded.setdefault(path, set()).update(roots)

        if getattr(function, "visibility", None) in ("public", "external"):
            expanded.setdefault(key_path, set()).add(function.canonical_name)

        return expanded or {key_path: {function.canonical_name}}

    def _match_key_paths(self, left_path: Tuple[str, ...], right_path: Tuple[str, ...]) -> Optional[str]:
        if left_path == right_path:
            return "High"
        if len(left_path) != len(right_path):
            return None

        levels: List[str] = []
        for left_token, right_token in zip(left_path, right_path):
            if left_token == right_token:
                levels.append("High")
                continue

            left_kind = self._token_kind(left_token)
            right_kind = self._token_kind(right_token)

            if left_kind == "param" and right_kind == "param":
                levels.append("Medium")
            elif left_kind == "unknown" or right_kind == "unknown":
                levels.append("Low")
            else:
                return None

        if "Low" in levels:
            return "Low"
        if "Medium" in levels:
            return "Medium"
        return "High"

    def _process_function(self, function):
        """Add intra-procedural nodes, CFG edges, and DFG edges."""
        if not function.nodes:
            return

        for node in function.nodes:
            self._add_node(node)

        for node in function.nodes:
            u_gid = self._get_global_id(node)
            
            # Preserve explicit true and false branches for `if` nodes.
            if node.type == NodeType.IF:
                if node.son_true:
                    v_gid = self._get_global_id(node.son_true)
                    self.graph.add_edge(u_gid, v_gid, edge_type="CFG", branch=True)
                if node.son_false:
                    v_gid = self._get_global_id(node.son_false)
                    self.graph.add_edge(u_gid, v_gid, edge_type="CFG", branch=False)
            else:
                for son in node.sons:
                    v_gid = self._get_global_id(son)
                    self.graph.add_edge(u_gid, v_gid, edge_type="CFG")

        self._compute_data_dependencies(function)

    def _get_var_name(self, var):
        """Return a stable variable name across Slither object types."""
        if hasattr(var, "canonical_name"):
            return var.canonical_name
        if hasattr(var, "name"):
            return var.name
        return str(var)

    def _add_node(self, node):
        """Attach one Slither node and its derived metadata to the graph."""
        gid = self._get_global_id(node)
        
        ir_strings = [str(ir) for ir in node.irs]
        
        state_vars_read = [self._get_var_name(v) for v in node.variables_read if isinstance(v, StateVariable)]
        local_vars_read = [self._get_var_name(v) for v in node.variables_read if not isinstance(v, StateVariable)]
        state_accesses = self._extract_state_accesses(node)

        # Prefer IR types over string heuristics for low-level calls.
        has_low_level = any(isinstance(ir, (LowLevelCall, Send, Transfer)) for ir in node.irs)

        # Treat IF/require/assert nodes as control nodes for slicing.
        is_control_node = False
        if node.type == NodeType.IF:
            is_control_node = True
        else:
            _GUARD_BUILTINS = ("require(", "assert(")
            for ir in node.irs:
                if isinstance(ir, SolidityCall) and ir.function.name.startswith(_GUARD_BUILTINS):
                    is_control_node = True
                    break

        attributes = {
            "node_type": str(node.type),
            "source_mapping": str(node.source_mapping),
            "ir_objects": node.irs,
            "ir_strings": ir_strings,
            "is_control_node": is_control_node,
            "vars_read": [self._get_var_name(v) for v in node.variables_read],
            "vars_written": [self._get_var_name(v) for v in node.variables_written],
            "state_vars_read": state_vars_read,
            "local_vars_read": local_vars_read,
            "state_accesses": state_accesses,
            "expanded_state_accesses": [],
            "expression": str(node.expression) if node.expression else None,
            "function_name": node.function.name if node.function else "GLOBAL",
            "contract_name": node.function.contract.name if node.function else "GLOBAL",
            "slither_node_object": node,
            "slither_node": node,
            "has_low_level_call": has_low_level,
            "contract_object": self.current_contract,
        }
        self.graph.add_node(gid, **attributes)

    def _compute_data_dependencies(self, function):
        """Build the intra-procedural DFG with reaching definitions."""
        nodes = function.nodes
        if not nodes: return
        entry_node = function.entry_point

        in_sets = {n.node_id: set() for n in nodes}
        out_sets = {n.node_id: set() for n in nodes}
        gen_sets, kill_sets = {}, {}

        for node in nodes:
            nid = node.node_id
            gen, kill = set(), set()
            vars_written = set(node.variables_written)
            if node == entry_node: vars_written.update(function.parameters)
            for v in vars_written:
                v_name = self._get_var_name(v)
                gen.add((v_name, nid))
                kill.add(v_name)
            gen_sets[nid] = gen
            kill_sets[nid] = kill

        changed = True
        while changed:
            changed = False
            for node in nodes:
                nid = node.node_id
                new_in = set()
                for father in node.fathers:
                    if father.node_id in out_sets: new_in.update(out_sets[father.node_id])
                if new_in != in_sets[nid]:
                    in_sets[nid] = new_in
                    changed = True
                
                survivors = {pair for pair in in_sets[nid] if pair[0] not in kill_sets[nid]}
                new_out = gen_sets[nid].union(survivors)
                if new_out != out_sets[nid]:
                    out_sets[nid] = new_out
                    changed = True

        node_lookup = {n.node_id: n for n in nodes}
        contract = function.contract

        for node in nodes:
            nid = node.node_id
            target_gid = self._get_global_id(node)

            for v in node.variables_read:
                v_name = self._get_var_name(v)
                reaching_defs = [def_nid for (var, def_nid) in in_sets[nid] if var == v_name]
                for def_nid in reaching_defs:
                    def_node = node_lookup[def_nid]
                    source_gid = self._get_global_id(def_node)

                    edge_type = "DFG"

                    # Promote sender-derived data flow to a role-flow edge.
                    if self._is_role_dependent(v, contract):
                        edge_type = "ROLE_FLOW"

                    self.graph.add_edge(source_gid, target_gid, edge_type=edge_type, variable=v_name)

    def _compute_interprocedural_edges(self):
        """Add call edges and their argument/return data flow."""
        for gid, data in self.graph.nodes(data=True):
            node = data.get("slither_node")
            if not node: continue

            for ir in node.irs:
                if isinstance(ir, (HighLevelCall, InternalCall, LibraryCall)):
                    target_func = ir.function
                    if not target_func: continue
                    caller_func = getattr(node, "function", None)
                    
                    target_entry_gid = self.function_entry_points.get(target_func.canonical_name)
                    if target_entry_gid is None: continue

                    arg_bindings: Dict[str, str] = {}
                    if ir.arguments and target_func.parameters:
                        for arg, param in zip(ir.arguments, target_func.parameters):
                            arg_bindings[self._parameter_token(param)] = self._summarize_symbolic_value(arg, caller_func)

                    self.graph.add_edge(
                        gid,
                        target_entry_gid,
                        edge_type="CALL",
                        label="calls",
                        argument_bindings=arg_bindings,
                        callee=target_func.canonical_name,
                        caller=(caller_func.canonical_name if caller_func else None),
                    )
                    self._register_call_context(caller_func, target_func, arg_bindings)

                    if ir.arguments and target_func.parameters:
                        for arg, param in zip(ir.arguments, target_func.parameters):
                            arg_name = self._get_var_name(arg)
                            param_name = self._get_var_name(param)
                            
                            self.graph.add_edge(
                                gid, target_entry_gid,
                                edge_type="DFG",
                                label="arg_pass",
                                variable=f"{arg_name}->{param_name}"
                            )

                    if ir.lvalue: 
                        return_nodes = []
                        for n in target_func.nodes:
                            for inner_ir in n.irs:
                                if isinstance(inner_ir, Return): 
                                    return_nodes.append(n)
                                    break
                        
                        for ret_node in return_nodes:
                            ret_gid = self._get_global_id(ret_node)
                            lvalue_name = self._get_var_name(ir.lvalue)
                            self.graph.add_edge(
                                ret_gid, gid,
                                edge_type="DFG",
                                label="return_pass",
                                variable=f"return->{lvalue_name}"
                            )


        self._compute_control_dependencies()

    def _compute_control_dependencies(self):
        """Build control-dependency and role-gated edges."""
        try:
            cfg = nx.DiGraph()
            for u, v, data in self.graph.edges(data=True):
                if data.get("edge_type") == "CFG":
                    cfg.add_edge(u, v)
            if len(cfg) == 0: return

            rev_cfg = cfg.reverse()
            exit_nodes = [n for n in cfg.nodes() if cfg.out_degree(n) == 0]
            virtual_exit = -1
            rev_cfg.add_node(virtual_exit)
            for exit_n in exit_nodes: rev_cfg.add_edge(virtual_exit, exit_n)
                
            try:
                pdom_map = nx.immediate_dominators(rev_cfg, virtual_exit)
            except Exception: return

            for v, u in pdom_map.items():
                if u != v and u != virtual_exit:
                    self.graph.add_edge(u, v, edge_type="POST_DOMINATOR", label="post_dominates")

            entry_nodes = list(self.function_entry_points.values())
            for entry in entry_nodes:
                if entry not in cfg: continue
                try:
                    dom_map = nx.immediate_dominators(cfg, entry)
                    for v, u in dom_map.items():
                        if u == v: continue
                        node_u = self.graph.nodes[u]
                        if node_u.get("is_control_node"):
                            self.graph.add_edge(u, v, edge_type="CONTROL_DEPENDENCY", label="guarded_by")
                            slither_node = node_u.get("slither_node")
                            contract = node_u.get("contract_object")
                            if slither_node and contract:
                                if self._is_guard_sender_dependent(slither_node, contract):
                                    self.graph.add_edge(u, v, edge_type="ROLE_GATED", label="auth_guard")
                except: continue
        except Exception as e:
            print(f"[CPGBuilder] CDG failed: {e}")

    def _is_role_dependent(self, var, contract) -> bool:
        """Check whether a value depends on `msg.sender` or `tx.origin`."""
        try:
            if isinstance(var, SolidityVariableComposed):
                if var.name in ("msg.sender", "tx.origin"):
                    return True
            if is_dependent(var, SolidityVariableComposed("msg.sender"), contract):
                return True
            if is_dependent(var, SolidityVariableComposed("tx.origin"), contract):
                return True
        except Exception:
            pass
        return False

    def _is_guard_sender_dependent(self, slither_node, contract) -> bool:
        """Check whether a guard condition is sender-dependent."""
        for var in slither_node.variables_read:
            if self._is_role_dependent(var, contract):
                return True
        return False

    def _compute_modifier_flow(self):
        """Link functions to the entry of each modifier they use."""
        for contract in self.slither.contracts:
            for func in contract.functions:
                if not func.modifiers: continue
                f_gid = self.function_entry_points.get(func.canonical_name)
                if f_gid is None: continue
                for mod in func.modifiers:
                    m_gid = self.function_entry_points.get(mod.canonical_name)
                    if m_gid:
                        self.graph.add_edge(f_gid, m_gid, edge_type="MODIFIER_USE", label="uses_modifier")

    def export_to_dot(self, output_path: str):
        """Export the graph as a Graphviz DOT file."""
        export = nx.MultiDiGraph()
        for n, data in self.graph.nodes(data=True):
            lbl = f"[{n}] {data.get('node_type','Node')}\\n" + "\\n".join(data.get('ir_strings',[]))[:40]
            col = "lightyellow" if data.get("is_control_node") else "white"
            export.add_node(n, label=lbl, style="filled", fillcolor=col, shape="box")
        for u, v, data in self.graph.edges(data=True):
            t = data.get("edge_type","UNK"); col="black"; sty="solid"
            if t=="DFG": col="blue"; sty="dashed"
            elif t=="STATE_DEPENDENCY": col="red"; sty="dotted"
            elif t=="ROLE_GATED": col="orange"
            export.add_edge(u, v, label=t, color=col, style=sty)
        try:
            nx.drawing.nx_pydot.write_dot(export, output_path)
            print(f"[CPGBuilder] Exported to {output_path}")
        except: print("[CPGBuilder] Export failed")
