
from typing import List, Tuple, Any, Set, Dict, Optional
from enum import Enum
from collections import deque
import logging
import networkx as nx

# Slither Imports
from slither.slithir.operations import (
    LowLevelCall, HighLevelCall, Transfer, Send,
    Binary, Assignment, LibraryCall,
    SolidityCall, InternalCall
)
from slither.core.solidity_types import MappingType
from slither.core.variables.state_variable import StateVariable
from slither.slithir.variables.reference import ReferenceVariable
from slither.core.declarations.solidity_variables import SolidityVariableComposed
from slither.core.cfg.node import NodeType
from slither.core.declarations import Function
from slither.analyses.data_dependency.data_dependency import is_dependent

from src.core.graph_builder import EdgeRegistry

logger = logging.getLogger(__name__)

# --- 1. Semantic Definitions (语义定义) ---

class SecurityInvariant(Enum):
    """
    定义系统必须维护的安全属性 (Security Invariants)。
    违反这些属性的操作将被标记为 Sinks。
    
    [FOCUSED] ACLens 专门针对 Access Control 类漏洞。
    """
    
    # [最高危] 治理安全 (Governance Safety)
    # 修改了控制合约执行流的关键变量 (e.g. changing owner, pausing contract, selfdestruct)
    GOVERNANCE_SAFETY = "Governance Safety"
    
    # [最高危] 资产完整性 (Asset Integrity)
    # 涉及资金流动或代币交互的操作 (e.g. transfer, withdraw, mint)
    ASSET_INTEGRITY = "Asset Conservation"
    
    # [中危] 授权控制 (Authorization)
    # 通用的状态修改，必须经过授权 (Access Control)
    AUTHORIZATION = "Access Control"

# --- 4. Main Detector (Pure Access Control) (主探测器) ---

class AccessControlAnalyzer:
    """
    [Structure-Aware + Graph-Guided] 访问控制相关函数选择器。
    
    核心哲学：
    Access Control Logic = (Identity + State) -> Execution Gating
    (访问控制 = 身份 + 状态 -> 执行门控)
    
    1. 识别 "Control Variables" (控制变量)：那些被用来检查 msg.sender 的状态变量 (e.g. owner)。
    2. 识别 "Relevant Functions" (相关函数)：修改控制变量或使用控制变量进行门控的函数。
    3. [Graph-Guided] 利用 AC-CPG 中的 ROLE_GATED 边验证 Sink 是否受守卫保护，
       为每个 Sink 标注置信度 (confidence)。
    """
    def __init__(self, contract, cpg: Optional[nx.MultiDiGraph] = None, node_mapping: Optional[Dict] = None):
        self.contract = contract
        self.cpg = cpg                    # AC-CPG 图（可选，用于图引导 Sink 验证）
        self.node_mapping = node_mapping  # (contract, func, local_id) -> global_id 映射
        # Step A: 识别控制变量
        self.critical_state_vars = self._identify_control_variables()
        # Step B: 识别相关函数（含图引导 Sink 检测）
        self.relevant_functions = self._identify_relevant_functions()

    def _identify_control_variables(self) -> Set[StateVariable]:
        """
        [Graph-Driven] Stage 1: Control Variable Discovery.

        AC-CPG 的 ROLE_GATED 边编码守卫到资源的关系：
        边 u → v 表示 u 是依赖 msg.sender 的守卫条件且支配 v。
        守卫条件中读取的状态变量即为控制变量。

        Fallback: 无图时回退到 Slither AST 遍历。
        """
        if self.cpg:
            control_vars = set()
            # 从 ROLE_GATED 边源节点提取守卫条件
            guard_gids = set()
            for u, v, data in self.cpg.edges(data=True):
                if data.get("edge_type") == "ROLE_GATED":
                    guard_gids.add(u)

            # 守卫条件中读取的状态变量 = 控制变量
            for gid in guard_gids:
                node_data = self.cpg.nodes.get(gid, {})
                slither_node = node_data.get("slither_node")
                if slither_node:
                    for var in slither_node.state_variables_read:
                        if isinstance(var, StateVariable):
                            control_vars.add(var)

            logger.debug(f"[Graph-Driven] Control variables from {len(guard_gids)} ROLE_GATED guards: "
                         f"{[v.name for v in control_vars]}")
            return control_vars

        # Fallback: AST-based (no graph available)
        control_vars = set()
        for func in self.contract.functions + self.contract.modifiers:
            for node in func.nodes:
                condition_vars_read = set()
                is_control_node = False

                if node.type == NodeType.IF:
                    is_control_node = True
                    condition_vars_read = set(node.state_variables_read)
                    all_vars_in_condition = node.variables_read

                else:
                    _GUARD_BUILTINS = ("require(", "assert(")
                    for ir in node.irs:
                        if isinstance(ir, SolidityCall):
                             if ir.function.name.startswith(_GUARD_BUILTINS):
                                is_control_node = True
                                condition_vars_read = set(node.state_variables_read)
                                all_vars_in_condition = node.variables_read
                                break

                if is_control_node:
                    if self._is_condition_sender_dependent(all_vars_in_condition):
                        control_vars.update(condition_vars_read)

        return control_vars

    def _is_condition_sender_dependent(self, vars_in_condition: List[Any]) -> bool:
        """检查变量集合是否数据依赖于 msg.sender 或 tx.origin。"""
        sources = ["msg.sender", "tx.origin"]
        
        for var in vars_in_condition:
            # 1. 直接使用
            if isinstance(var, SolidityVariableComposed) and var.name in sources:
                return True
            
            # 2. 数据依赖 (Slither API)
            if is_dependent(var, SolidityVariableComposed("msg.sender"), self.contract):
                return True
            if is_dependent(var, SolidityVariableComposed("tx.origin"), self.contract):
                return True
                
        return False

    # Standard ERC20/ERC721 function names that MAY be safe if they follow the standard pattern.
    STANDARD_TOKEN_FUNCTIONS = {
        # ERC20
        "transfer", "transferFrom", "approve",
        "increaseAllowance", "decreaseAllowance",
        "increaseApproval", "decreaseApproval",
        # ERC721
        "safeTransferFrom", "setApprovalForAll",
        # Common patterns
        "approveAndCall",
    }

    # Known standard library contracts whose token functions are safe to skip.
    # Functions declared in custom parent contracts (TaxToken, CustomERC20, etc.)
    # may contain vulnerabilities and should NOT be filtered.
    STANDARD_LIBRARY_CONTRACTS = {
        "ERC20", "ERC20Burnable", "ERC20Capped", "ERC20Pausable", "ERC20Permit",
        "ERC20Votes", "ERC20Wrapper", "ERC4626",
        "ERC721", "ERC721Burnable", "ERC721Enumerable", "ERC721URIStorage",
        "ERC1155", "ERC1155Burnable",
        # Interfaces (pure declarations, not custom overrides)
        "IERC20", "IERC20Metadata", "IERC721", "IERC721Metadata",
        "IERC721Receiver", "IERC1155", "IERC1155Receiver",
        # Upgradeable variants (OpenZeppelin)
        "ERC20Upgradeable", "ERC721Upgradeable", "ERC1155Upgradeable",
        "IERC20Upgradeable", "IERC721Upgradeable",
    }

    # Standard interface signatures (name + parameter types) for ERC20/ERC721/ERC4626.
    # Functions matching these signatures are tagged as standard_interface to reduce
    # FP from Policy Agent hallucinating permission requirements on standard operations.
    STANDARD_INTERFACE_SIGNATURES = {
        # ERC20 (EIP-20)
        ("transfer", ("address", "uint256")),
        ("transferFrom", ("address", "address", "uint256")),
        ("approve", ("address", "uint256")),
        ("increaseAllowance", ("address", "uint256")),
        ("decreaseAllowance", ("address", "uint256")),
        # ERC721 (EIP-721)
        ("safeTransferFrom", ("address", "address", "uint256")),
        ("safeTransferFrom", ("address", "address", "uint256", "bytes")),
        ("setApprovalForAll", ("address", "bool")),
        # ERC1155 (EIP-1155)
        ("safeTransferFrom", ("address", "address", "uint256", "uint256", "bytes")),
        ("safeBatchTransferFrom", ("address", "address", "uint256[]", "uint256[]", "bytes")),
        # ERC4626 (EIP-4626)
        ("deposit", ("uint256", "address")),
        ("withdraw", ("uint256", "address", "address")),
        ("redeem", ("uint256", "address", "address")),
        ("mint", ("uint256", "address")),
        # ERC20Permit (EIP-2612)
        ("permit", ("address", "address", "uint256", "uint256", "uint8", "bytes32", "bytes32")),
    }

    def _function_has_sender_guard(self, func: Function) -> bool:
        """Check if a function has any form of sender-based access guard (modifier or inline)."""
        return (self._is_function_modifier_guarded(func)
                or (self._function_reads_sender_directly(func, depth=1)
                    and self._has_guard_condition(func, depth=1)))

    def _get_function_guard_state_vars(self, func: Function) -> Set[StateVariable]:
        """
        Extract state variables used in inline sender guards (require/if checking msg.sender).
        Only returns non-mapping address-type vars (owner, admin, etc.),
        NOT mapping reads like balances[msg.sender] which are balance checks.

        Checks both the function's own nodes and immediate internal callees (depth=1)
        to handle delegation patterns (e.g., _reduceReserves → reduceReservesFresh
        which has require(msg.sender == admin)).
        """
        guard_vars = set()

        # Collect function + its immediate internal callees
        funcs_to_check = [func]
        for node in func.nodes:
            for ir in node.irs:
                if isinstance(ir, InternalCall) and ir.function and hasattr(ir.function, 'nodes'):
                    if ir.function not in funcs_to_check:
                        funcs_to_check.append(ir.function)

        for f in funcs_to_check:
            for node in f.nodes:
                is_guard_node = False
                if node.type == NodeType.IF:
                    is_guard_node = True
                else:
                    for ir in node.irs:
                        if isinstance(ir, SolidityCall) and ir.function.name.startswith(("require(", "assert(")):
                            is_guard_node = True
                            break

                if not is_guard_node:
                    continue

                # Check if this guard reads msg.sender
                reads_sender = any(
                    isinstance(v, SolidityVariableComposed) and v.name == "msg.sender"
                    for v in node.variables_read
                )
                if not reads_sender:
                    # Also check _msgSender() calls
                    for ir in node.irs:
                        if isinstance(ir, InternalCall) and hasattr(ir, 'function') and ir.function:
                            if getattr(ir.function, 'name', '') in ('_msgSender', 'msgSender'):
                                reads_sender = True
                                break
                if not reads_sender:
                    continue

                # Collect non-mapping state variables read in this guard
                for var in node.state_variables_read:
                    if isinstance(var, StateVariable) and not isinstance(var.type, MappingType):
                        guard_vars.add(var)

        return guard_vars

    def _guard_vars_safely_managed(self, func: Function, guard_vars: Set[StateVariable], depth: int = 2) -> bool:
        """
        Verify that all guard variables are safely managed: every public/external
        function that writes to them is either a constructor or has its own sender guard.
        Also rejects guard vars that look like contract addresses (callback patterns)
        rather than traditional AC roles (owner, admin, etc.).
        """
        if depth <= 0:
            return False  # Conservative: can't verify deeper chains

        # Reject contract address guard vars (used in callback patterns like onERC1155Received).
        # These verify caller identity for protocol callbacks, not traditional AC roles.
        _ADDR_PATTERNS = {'contract', 'token', 'factory', 'router', 'pair',
                          'pool', 'vault', 'bridge', 'lending', 'handler'}
        for var in guard_vars:
            name_lower = var.name.lower()
            if any(p in name_lower for p in _ADDR_PATTERNS):
                return False

        for var in guard_vars:
            for writer in self.contract.functions:
                if writer == func:
                    continue
                if writer.visibility not in ('public', 'external'):
                    continue
                if var not in writer.state_variables_written:
                    continue
                # Constructor writes are safe (deployment-only)
                if writer.is_constructor:
                    continue
                # Writer must have its own sender guard
                if not self._function_has_sender_guard(writer):
                    return False

        return True

    def _is_inherited_standard_function(self, func: Function) -> bool:
        """Check if a function is a standard token function inherited from a
        known standard library (OpenZeppelin ERC20/ERC721/ERC1155).
        Functions declared in the leaf contract (overridden) or in custom
        parent contracts (TaxToken, TokenHandler, etc.) are kept for analysis."""
        if func.name not in self.STANDARD_TOKEN_FUNCTIONS:
            return False
        declarer = getattr(func, 'contract_declarer', None)
        if not declarer:
            return False
        # If declared in the contract being analyzed, it's overridden — keep
        if declarer == self.contract:
            return False
        # Only filter if the declarer is a known standard library contract
        if declarer.name in self.STANDARD_LIBRARY_CONTRACTS:
            return True
        # Custom parent contract — keep for analysis (may be vulnerable)
        return False

    @staticmethod
    def _normalize_param_type(param_type_str: str) -> str:
        """Normalize Solidity type strings for signature matching.
        Maps uint/int variants to canonical forms and strips storage qualifiers."""
        s = str(param_type_str).strip()
        # Remove storage qualifiers
        for qual in ("memory", "calldata", "storage"):
            s = s.replace(f" {qual}", "")
        s = s.strip()
        # Normalize uint/int aliases
        if s == "uint":
            s = "uint256"
        elif s == "int":
            s = "int256"
        return s

    def _is_standard_interface_function(self, func: Function) -> bool:
        """Check if a function matches a standard ERC interface signature (name + parameter types).
        Unlike _is_inherited_standard_function which checks declaration origin, this matches
        the actual signature regardless of where it's declared. Used for tagging, not filtering."""
        param_types = tuple(self._normalize_param_type(p.type) for p in func.parameters)
        return (func.name, param_types) in self.STANDARD_INTERFACE_SIGNATURES

    def _identify_relevant_functions(self) -> Dict[Function, List[Tuple]]:
        """
        [Unified Static Analysis]
        同时进行函数筛选 (Pruning) 和漏洞点检测 (Sink Detection)。

        Returns:
            Dict[Function, List[Sink]]: 包含 Sinks 的相关函数映射表。

        Side effect:
            Populates self._all_function_sinks with sink data for ALL candidate
            functions (including those filtered out by guards/self-service checks),
            used by select_peers() for intra-contract comparative inference.
        """
        relevant_map = {}
        self._all_function_sinks = {}  # func -> (sinks, is_guarded_func, modifiers)

        for func in self.contract.functions:
            # 1. Scope Filter: Public/External or Internal used by Public
            if func.visibility not in ['public', 'external']:
                continue

            # 2. Skip constructors — they run only at deployment, not callable by external users
            if func.is_constructor:
                continue

            # 3. Skip fallback/receive functions — typically not AC-relevant
            if func.is_fallback or func.is_receive:
                continue

            # 4. Skip inherited (not overridden) standard token functions
            #    Custom/overridden implementations are kept for analysis
            if self._is_inherited_standard_function(func):
                continue

            sinks = self._check_for_sinks(func)

            # Store sink data for ALL candidates before filtering (used by select_peers)
            if sinks:
                is_modifier_guarded = self._is_function_modifier_guarded(func)
                all_guarded = all(sink[5] for sink in sinks)
                is_guarded_func = is_modifier_guarded or all_guarded
                self._all_function_sinks[func] = {
                    "sinks": sinks,
                    "sink_types": set(s[1] for s in sinks),
                    "is_guarded": is_guarded_func,
                    "modifiers": [m.name for m in func.modifiers],
                    "state_vars_read": {v.name for v in func.state_variables_read if isinstance(v, StateVariable)},
                    "state_vars_written": {v.name for v in func.state_variables_written if isinstance(v, StateVariable)},
                }

            if sinks:
                # 5. Modifier-based filtering: skip functions with verified AC modifiers
                #    Only uses explicit modifier analysis (Layer 2), NOT graph-based
                #    ROLE_GATED edges, to avoid false positives from Slither's
                #    transitive is_dependent() (e.g., whenNotPaused → _paused → onlyOwner).
                if self._is_function_modifier_guarded(func):
                    logger.debug(f"[SemanticFilter] Skipping {func.name}: AC modifier detected ({[m.name for m in func.modifiers]})")
                    continue

                # 6. All-sinks-guarded filter: if every sink is guarded by CPG
                #    ROLE_GATED edges (Layer 1/3), and the guard variables are
                #    safely managed (can't be set by arbitrary callers), skip.
                #    Catches Compound-style inline require(msg.sender == admin).
                if all(sink[5] for sink in sinks):
                    guard_vars = self._get_function_guard_state_vars(func)
                    if guard_vars and self._guard_vars_safely_managed(func, guard_vars):
                        logger.debug(f"[AllSinksGuarded] Skipping {func.name}: all sinks guarded, guard vars {[v.name for v in guard_vars]} safely managed")
                        continue

                # 7. Pure self-service filter: function has NO external calls,
                #    NO selfdestruct, NO critical var writes, and ALL state writes
                #    are msg.sender-indexed. Only affects caller's own state.
                if self._is_purely_self_service(func, sinks):
                    logger.debug(f"[SelfService] Skipping {func.name}: purely self-service function")
                    continue

                relevant_map[func] = sinks
            else:
                # Fallback: Check for state mutations to critical variables (Authorization Sinks)
                # These might have been missed by _check_for_sinks if not explicitly modeled
                pass 
                
        return relevant_map

    def _check_for_sinks(self, func: Function) -> List[Tuple]:
        """
        [Graph-Driven] 三阶段 Sink 识别。

        阶段 2 (Sink 枚举):
          S1: 外部交互 (ASSET_INTEGRITY) — 图节点属性 + IR
          S2: 控制变量修改 (GOVERNANCE_SAFETY) — 图派生控制变量
          S3: Selfdestruct (GOVERNANCE_SAFETY) — IR 叶操作
          S4: 传递性 Sink — CALL 边图遍历
          S5: 公共初始化 (GOVERNANCE_SAFETY) — 命名启发式

        阶段 3 (守卫验证): ROLE_GATED 边查询

        Sink 元组: (node_id, sink_type, ir, invariants, gid, is_guarded)
        """
        raw_sinks = []
        seen_nodes = set()

        for node in func.nodes:
            if node.node_id in seen_nodes:
                continue

            gid = self._resolve_gid(func, node) if self.node_mapping else None

            # ── S1: External Interactions ──
            # S1a: Low-level calls (Transfer/Send/LowLevelCall)
            # Graph-driven: use has_low_level_call node attribute when available
            is_low_level = False
            if self.cpg and gid is not None and gid in self.cpg:
                is_low_level = self.cpg.nodes[gid].get("has_low_level_call", False)
            else:
                is_low_level = any(isinstance(ir, (LowLevelCall, Send, Transfer)) for ir in node.irs)

            if is_low_level:
                invariants = set()
                ir_obj = None
                for ir in node.irs:
                    if isinstance(ir, (LowLevelCall, Transfer, Send)):
                        ir_obj = ir
                        if isinstance(ir, (Transfer, Send)):
                            invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)
                        if isinstance(ir, LowLevelCall):
                            invariants.add(SecurityInvariant.GOVERNANCE_SAFETY.name)
                            if hasattr(ir, 'call_value') and ir.call_value:
                                invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)
                        break
                if invariants:
                    raw_sinks.append((node, "external_interaction", ir_obj, invariants))
                    seen_nodes.add(node.node_id)
                    continue

            # S1b: High-level external calls
            for ir in node.irs:
                if isinstance(ir, HighLevelCall) and not isinstance(ir, LibraryCall):
                    is_view_pure = False
                    if isinstance(ir.function, Function):
                        if getattr(ir.function, 'view', False) or getattr(ir.function, 'pure', False):
                            is_view_pure = True
                        elif getattr(ir.function, 'is_view', False) or getattr(ir.function, 'is_pure', False):
                            is_view_pure = True

                    if not is_view_pure:
                        invariants = {SecurityInvariant.ASSET_INTEGRITY.name}
                        if hasattr(ir, 'call_value') and ir.call_value:
                            invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)
                        raw_sinks.append((node, "external_interaction", ir, invariants))
                        seen_nodes.add(node.node_id)
                        break

            if node.node_id in seen_nodes:
                continue

            # ── S2: Control Variable Modifications (Graph-Derived) ──
            # 控制变量由 Stage 1 从 ROLE_GATED 边拓扑中派生
            for var in node.variables_written:
                if isinstance(var, StateVariable) and var in self.critical_state_vars:
                    ir_obj = None
                    for ir in node.irs:
                        if isinstance(ir, (Assignment, Binary)):
                            ir_obj = ir
                            break
                    raw_sinks.append((node, "state_modification",
                                     ir_obj or (node.irs[0] if node.irs else None),
                                     {SecurityInvariant.GOVERNANCE_SAFETY.name}))
                    seen_nodes.add(node.node_id)
                    break

            if node.node_id in seen_nodes:
                continue

            # ── S3: Selfdestruct ──
            for ir in node.irs:
                if isinstance(ir, SolidityCall) and ir.function.name in ['selfdestruct(address)', 'suicide(address)']:
                    raw_sinks.append((node, "selfdestruct", ir, {SecurityInvariant.GOVERNANCE_SAFETY.name}))
                    seen_nodes.add(node.node_id)
                    break

            if node.node_id in seen_nodes:
                continue

            # ── S4: Transitive Sinks via CALL Edges ──
            if self.cpg and gid is not None and gid in self.cpg:
                # Graph-driven: follow CALL edges to check callee operations
                for _, target_gid, edge_data in self.cpg.out_edges(gid, data=True):
                    if edge_data.get("edge_type") == "CALL":
                        has_critical, callee_invariants = self._callee_has_critical_op_graph(target_gid)
                        if has_critical:
                            ir_obj = None
                            for ir in node.irs:
                                if isinstance(ir, InternalCall):
                                    ir_obj = ir
                                    break
                            sink_type = "external_interaction" if SecurityInvariant.ASSET_INTEGRITY.name in callee_invariants else "state_modification"
                            raw_sinks.append((node, sink_type, ir_obj, callee_invariants))
                            seen_nodes.add(node.node_id)
                            break
            else:
                # Fallback: IR-based internal call check (no graph)
                for ir in node.irs:
                    if isinstance(ir, InternalCall) and ir.function:
                        callee_invariants = set()
                        if ir.function.state_variables_written:
                            callee_invariants.add(SecurityInvariant.AUTHORIZATION.name)

                        has_risky_external = False
                        for internal_node in ir.function.nodes:
                            for internal_ir in internal_node.irs:
                                if isinstance(internal_ir, (LowLevelCall, Transfer, Send)):
                                    has_risky_external = True
                                    break
                                if isinstance(internal_ir, HighLevelCall) and not isinstance(internal_ir, LibraryCall):
                                    is_view_pure = False
                                    if isinstance(internal_ir.function, Function):
                                        if getattr(internal_ir.function, 'view', False) or getattr(internal_ir.function, 'pure', False):
                                            is_view_pure = True
                                        elif getattr(internal_ir.function, 'is_view', False) or getattr(internal_ir.function, 'is_pure', False):
                                            is_view_pure = True
                                    if not is_view_pure:
                                        has_risky_external = True
                                        break
                            if has_risky_external:
                                break

                        if has_risky_external:
                            callee_invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)

                        if callee_invariants:
                            sink_type = "external_interaction" if has_risky_external else "state_modification"
                            raw_sinks.append((node, sink_type, ir, callee_invariants))
                            seen_nodes.add(node.node_id)
                            break

            if node.node_id in seen_nodes:
                continue

            # NOTE: General State Modification catch-all disabled.
            # It flags ANY state write as a Sink, far exceeding S1-S6 definitions
            # and causing massive FP inflation (540 FP vs 83 with S1-S5 only).
            # The paper's sink taxonomy (S1-S6) covers: external interactions,
            # control variable writes, selfdestruct, transitive sinks,
            # public initialization, and cross-user state annotations.

        # ── S5: Public Initialization ──
        if func.visibility in ['public', 'external'] and not func.is_constructor:
             is_init = False
             if func.name.lower().startswith("init"): is_init = True
             if any('init' in m.name.lower() for m in func.modifiers): is_init = True

             if is_init and func.state_variables_written:
                 if func.entry_point and func.entry_point.irs:
                     raw_sinks.append((func.entry_point, "public_initialization", func.entry_point.irs[0], {SecurityInvariant.GOVERNANCE_SAFETY.name}))

        # ── S7: Unguarded Non-Self-Service State Modification ──
        # Fallback for public/external functions that modify governance or
        # economic parameters but don't trigger S1-S5 (no external calls,
        # no control-variable writes, no init pattern).  Activates when:
        #   1. No existing raw_sinks from S1-S5
        #   2. No AC modifiers
        #   3. No inline sender guards
        #   4. Writes to at least one non-mapping (scalar) state variable
        # Scalar writes typically represent protocol parameters (oracle
        # prices, fee rates, reward configs), whereas mapping writes are
        # user-indexed balances/allowances.  This distinguishes governance
        # operations from user self-service operations.
        if not raw_sinks and func.visibility in ('public', 'external') and not func.is_constructor:
            has_ac_modifier = self._is_function_modifier_guarded(func)
            has_inline_guard = self._function_has_sender_guard(func)
            if not has_ac_modifier and not has_inline_guard:
                scalar_writes = [v for v in func.state_variables_written
                                 if isinstance(v, StateVariable) and not isinstance(v.type, MappingType)]
                if scalar_writes:
                    # Find the first node that writes a scalar state variable
                    for node in func.nodes:
                        node_scalar_writes = [v for v in node.state_variables_written
                                              if isinstance(v, StateVariable) and not isinstance(v.type, MappingType)]
                        if node_scalar_writes and node.irs:
                            raw_sinks.append((node, "state_modification",
                                              node.irs[0], {SecurityInvariant.GOVERNANCE_SAFETY.name}))
                            break  # one sink is enough to enter the LLM pipeline

        # ── Stage 3: Graph-Guided Guard Verification ──
        sinks = []
        guard_edge_types = EdgeRegistry.get_guard_edge_types()

        for node, sink_type, ir, invariants in raw_sinks:
            gid = self._resolve_gid(func, node)
            is_guarded = self._check_node_guarded(gid, guard_edge_types, func=func) if gid is not None else False

            if is_guarded:
                logger.debug(f"[GraphGuided] Sink {func.name}:{node.node_id} ({sink_type}) is GUARDED by ROLE_GATED edge")
            else:
                logger.debug(f"[GraphGuided] Sink {func.name}:{node.node_id} ({sink_type}) is UNGUARDED")

            sinks.append((node.node_id, sink_type, ir, invariants, gid, is_guarded))

        return sinks

    def _resolve_gid(self, func: Function, node) -> Optional[int]:
        """
        将 Slither 节点解析为 CPG 中的全局节点 ID (GID)。
        """
        if not self.node_mapping:
            return None
        
        contract_name = func.contract.name if func.contract else "GLOBAL"
        func_name = func.name
        key = (contract_name, func_name, node.node_id)
        return self.node_mapping.get(key)

    def _check_node_guarded(self, gid: int, guard_edge_types: Set[str], func: Function = None) -> bool:
        """
        [Graph-Guided] 三层守卫检查。

        Layer 1: 直接前驱是否有 ROLE_GATED / MODIFIER_USE 边（原有逻辑）。
        Layer 2: 函数级修饰器守卫检查——如果函数使用了包含 sender 依赖检查的修饰器
                 （onlyOwner、onlyRole 等），则该函数内所有 Sink 视为受保护。
                 这弥补了 MODIFIER_USE 边仅连接函数入口→修饰器入口，而不连接
                 函数体内部 Sink 节点的结构性缺陷。
        Layer 3: 沿 CFG/CONTROL_DEPENDENCY 边向上 BFS（至多 10 跳），
                 寻找间接传递的 ROLE_GATED 守卫。
        """
        if not self.cpg or gid not in self.cpg:
            return False

        # Layer 1: Direct predecessor guard edge
        for predecessor in self.cpg.predecessors(gid):
            edge_data_dict = self.cpg.get_edge_data(predecessor, gid)
            if not edge_data_dict:
                continue
            for _, edge_data in edge_data_dict.items():
                if edge_data.get("edge_type", "") in guard_edge_types:
                    return True

        # Layer 2: Function-level modifier guard (handles OpenZeppelin patterns)
        if func is not None and self._is_function_modifier_guarded(func):
            return True

        # Layer 3: Transitive BFS upward through CFG/CONTROL_DEPENDENCY
        visited = {gid}
        frontier = {gid}
        for _ in range(10):
            next_frontier = set()
            for node in frontier:
                for predecessor in self.cpg.predecessors(node):
                    if predecessor in visited:
                        continue
                    visited.add(predecessor)
                    edge_data_dict = self.cpg.get_edge_data(predecessor, node)
                    if edge_data_dict:
                        for _, edge_data in edge_data_dict.items():
                            if edge_data.get("edge_type", "") in guard_edge_types:
                                return True
                        for _, edge_data in edge_data_dict.items():
                            if edge_data.get("edge_type", "") in ("CFG", "CONTROL_DEPENDENCY"):
                                next_frontier.add(predecessor)
                                break
            if not next_frontier:
                break
            frontier = next_frontier

        return False

    def _is_function_modifier_guarded(self, func: Function) -> bool:
        """
        检查函数是否拥有 AC 守卫修饰器（直接引用 msg.sender 的）。

        只检测修饰器自身代码（及其直接调用的内部函数）中对 msg.sender
        或 _msgSender() 的直接引用，避免 Slither is_dependent() 的
        合约级传递依赖导致的误判（如 whenNotPaused 读取 _paused，
        而 _paused 被 onlyOwner 函数写入，导致 is_dependent 返回 True）。
        """
        if not func.modifiers:
            return False

        for modifier in func.modifiers:
            try:
                # Check 1: AC modifiers that verify msg.sender identity
                # (onlyOwner, onlyRole, etc.)
                if self._function_reads_sender_directly(modifier, depth=1):
                    # Confirm modifier has a guard condition (require/if).
                    # Check both the modifier's direct nodes AND internal
                    # functions it calls (e.g., onlyOwner → _checkOwner,
                    # onlyRole → _checkRole → _checkRole(role, account)).
                    # OZ AccessControl has 3-level call chains, so depth=2.
                    if self._has_guard_condition(modifier, depth=2):
                        return True

                # Check 2: Temporal guard modifiers (initializer/reinitializer)
                # OpenZeppelin Initializable: restricts function to one-time
                # execution via boolean/uint flag, preventing re-initialization.
                mod_name = getattr(modifier, 'name', '')
                if mod_name in ('initializer', 'reinitializer'):
                    if self._has_guard_condition(modifier, depth=2):
                        return True
            except Exception:
                continue

        return False

    def _function_reads_sender_directly(self, func_or_modifier, depth: int = 0) -> bool:
        """
        检查函数/修饰器是否直接引用 msg.sender 或 _msgSender()。
        depth > 0 时递归检查被调用的内部函数（最多 1 层）。
        """
        for node in func_or_modifier.nodes:
            for var in node.variables_read:
                if isinstance(var, SolidityVariableComposed) and var.name == "msg.sender":
                    return True
            for ir in node.irs:
                # _msgSender() call (OpenZeppelin Context.sol)
                if isinstance(ir, InternalCall) and hasattr(ir, 'function') and ir.function:
                    fname = getattr(ir.function, 'name', '')
                    if fname in ('_msgSender', 'msgSender'):
                        return True
                    # Recurse one level into called internal functions
                    if depth > 0 and hasattr(ir.function, 'nodes'):
                        if self._function_reads_sender_directly(ir.function, depth=0):
                            return True
        return False

    def _has_guard_condition(self, func_or_modifier, depth: int = 0) -> bool:
        """
        检查函数/修饰器（及其调用的内部函数）中是否包含守卫条件。

        守卫条件包括: require(), assert(), if 分支。
        depth > 0 时递归检查被调用的内部函数（如 _checkOwner, _checkRole）。
        """
        for node in func_or_modifier.nodes:
            if node.type == NodeType.IF:
                return True
            for ir in node.irs:
                if isinstance(ir, SolidityCall) and ir.function.name.startswith(("require(", "assert(")):
                    return True
                if depth > 0 and isinstance(ir, InternalCall) and hasattr(ir, 'function') and ir.function:
                    if hasattr(ir.function, 'nodes'):
                        if self._has_guard_condition(ir.function, depth=depth - 1):
                            return True
        return False

    def _callee_has_critical_op_graph(self, call_target_gid: int) -> Tuple[bool, Set[str]]:
        """
        [Graph-Driven] S4: 通过 CALL 边图遍历检查被调用函数是否包含关键操作。
        替代原有的递归 IR 扫描方式。

        从 CALL 边目标节点出发，沿 CFG 边遍历被调函数内所有节点，
        检查是否存在外部交互、控制变量写入或 selfdestruct。

        Returns: (has_critical, invariants)
        """
        if not self.cpg or call_target_gid not in self.cpg:
            return False, set()

        target_data = self.cpg.nodes[call_target_gid]
        callee_func = target_data.get("function_name")
        callee_contract = target_data.get("contract_name")
        if not callee_func:
            return False, set()

        invariants = set()
        cv_names = {v.name for v in self.critical_state_vars}

        visited = set()
        queue = deque([call_target_gid])

        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            visited.add(current)

            node_data = self.cpg.nodes.get(current, {})

            # Check for external interactions (from graph node attribute)
            if node_data.get("has_low_level_call"):
                invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)

            # Check for HighLevelCall (from IR objects stored in graph node)
            ir_objects = node_data.get("ir_objects", [])
            for ir in ir_objects:
                if isinstance(ir, HighLevelCall) and not isinstance(ir, LibraryCall):
                    is_vp = False
                    if isinstance(ir.function, Function):
                        is_vp = (getattr(ir.function, 'view', False) or getattr(ir.function, 'pure', False) or
                                 getattr(ir.function, 'is_view', False) or getattr(ir.function, 'is_pure', False))
                    if not is_vp:
                        invariants.add(SecurityInvariant.ASSET_INTEGRITY.name)

                # Check for selfdestruct
                if isinstance(ir, SolidityCall) and ir.function.name in ['selfdestruct(address)', 'suicide(address)']:
                    invariants.add(SecurityInvariant.GOVERNANCE_SAFETY.name)

            # Check for control variable writes
            vars_written = node_data.get("vars_written", [])
            if any(vw in cv_names for vw in vars_written):
                invariants.add(SecurityInvariant.GOVERNANCE_SAFETY.name)

            # Check for general state writes
            slither_node = node_data.get("slither_node")
            if slither_node and slither_node.state_variables_written:
                invariants.add(SecurityInvariant.AUTHORIZATION.name)

            # Follow CFG edges within same function
            for _, successor, edge_data in self.cpg.out_edges(current, data=True):
                if edge_data.get("edge_type") == "CFG":
                    succ_data = self.cpg.nodes.get(successor, {})
                    if succ_data.get("function_name") == callee_func and succ_data.get("contract_name") == callee_contract:
                        queue.append(successor)
                # Transitive: follow CALL edges to further callees
                elif edge_data.get("edge_type") == "CALL":
                    queue.append(successor)

        return bool(invariants), invariants

    def _collect_internal_callees(self, func: Function) -> List[Function]:
        """
        Collect all internal callee functions (including inherited) via IR traversal.
        Uses BFS to handle transitive calls (e.g., approve → _approve → _spendAllowance).
        Slither's all_internal_calls() returns IR objects, not Function objects,
        so we extract the callee via ir.function.
        """
        contract_chain = set([self.contract]) | set(self.contract.inheritance)
        all_funcs = [func]
        seen = {id(func)}
        queue = [func]
        while queue:
            current = queue.pop(0)
            for node in current.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall) and ir.function and isinstance(ir.function, Function):
                        callee = ir.function
                        if id(callee) not in seen and hasattr(callee, 'contract') and callee.contract in contract_chain:
                            all_funcs.append(callee)
                            seen.add(id(callee))
                            queue.append(callee)
        return all_funcs

    def _is_purely_self_service(self, func: Function, sinks: List[Tuple]) -> bool:
        """
        Check if a function is purely self-service: no selfdestruct, no public_initialization,
        no critical state var writes, and ALL state writes are msg.sender-indexed.

        External interaction sinks are allowed IF all call targets are trusted
        (state variables, not dependent on function parameters). This captures
        common DeFi self-service patterns like deposit/withdraw/claim that
        call token.transferFrom(msg.sender, ...) through trusted contract addresses.
        """
        has_external = False
        for sink in sinks:
            if sink[1] in ("selfdestruct", "public_initialization"):
                return False
            if sink[1] == "external_interaction":
                has_external = True

        # If function has external calls, verify all call targets are trusted
        if has_external:
            if not self._all_external_calls_trusted(func):
                return False

        # Reject if function modifies scalar critical state variables (governance vars).
        scalar_cv_names = {v.name for v in self.critical_state_vars
                           if not isinstance(v.type, MappingType)}
        all_funcs = self._collect_internal_callees(func)

        for f in all_funcs:
            for var in f.state_variables_written:
                if isinstance(var, StateVariable):
                    if var.name in scalar_cv_names:
                        return False

        # State write classification:
        # - Scalar critical vars (owner, admin) → REJECT (governance modification)
        # - Mapping writes → must be msg.sender-indexed (to prevent cross-user impact)
        # - Non-critical scalar writes → ALLOW only if function has external calls
        #   (external calls indicate value exchange backing the state change;
        #    without them, scalar writes like _totalSupply indicate value
        #    creation/destruction with cross-user economic impact)
        has_sender_indexed_write = False
        has_scalar_write = False
        for f in all_funcs:
            for node in f.nodes:
                for var in node.state_variables_written:
                    if isinstance(var, StateVariable):
                        if isinstance(var.type, MappingType):
                            # Mapping writes MUST be msg.sender-indexed
                            gid = self._resolve_gid(f, node)
                            if not self._is_self_service_write(node, var, gid):
                                return False
                            has_sender_indexed_write = True
                        else:
                            has_scalar_write = True

        # Must have at least one msg.sender-indexed mapping write
        if not has_sender_indexed_write:
            return False

        # Scalar writes without external calls = potential mint/burn from nothing.
        # Only allow scalar state writes when there are external interaction sinks
        # (indicating value exchange that backs the state change).
        if has_scalar_write and not has_external:
            return False

        # Final guard: if the top-level function takes address parameters,
        # check that none of them flow into first-level mapping WRITE indices in callees.
        # This catches patterns like depositFor(user) and onERC1155Received(from)
        # where is_dependent() context-insensitively reports the callee's parameter
        # as msg.sender-dependent because OTHER call sites pass msg.sender.
        # Only check IndexOps that are part of state WRITES (not reads like
        # require(!_isBlacklisted[addr]) which are read-only guard checks).
        from slither.slithir.operations import Index as IndexOp
        top_addr_params = set()
        for p in func.parameters:
            ptype = str(getattr(p, 'type', ''))
            if 'address' in ptype:
                top_addr_params.add(p)
        if top_addr_params:
            for f in all_funcs:
                for node in f.nodes:
                    # Only check nodes that actually WRITE to state variables
                    written_vars = {v for v in node.state_variables_written
                                    if isinstance(v, StateVariable)}
                    if not written_vars:
                        continue
                    for ir in node.irs:
                        if isinstance(ir, IndexOp) and isinstance(ir.variable_left, StateVariable):
                            # Only flag if this IndexOp is on a variable being written
                            if ir.variable_left not in written_vars:
                                continue
                            idx = ir.variable_right
                            for param in top_addr_params:
                                try:
                                    if idx == param or is_dependent(idx, param, self.contract):
                                        # Address param flows into a mapping write index.
                                        # Reject: the function can modify arbitrary users' state.
                                        return False
                                except Exception:
                                    pass

        return True

    def _all_external_calls_trusted(self, func: Function) -> bool:
        """
        Check if ALL external call destinations in a function (and its internal callees)
        are trusted — i.e., they come from state variables, not from function parameters
        or user-controlled inputs.

        A call like token.transferFrom(msg.sender, address(this), amount) where 'token'
        is a state variable is trusted. A call like target.call(data) where 'target'
        is a function parameter is NOT trusted.

        Also trusts destinations resolved from state variable reads via ReferenceVariable
        (e.g., IERC20(stakingToken).transfer(...) where stakingToken is a state variable
        read through a reference) and destinations that are data-dependent on state variables
        but not on any function parameter.
        """
        all_funcs = self._collect_internal_callees(func)
        # Collect all function parameters across the call chain
        all_params = set()
        for f in all_funcs:
            for p in f.parameters:
                all_params.add(p)

        for f in all_funcs:
            for node in f.nodes:
                for ir in node.irs:
                    if isinstance(ir, (HighLevelCall, LowLevelCall, Transfer, Send)):
                        dest = getattr(ir, 'destination', None)
                        if dest is None:
                            continue
                        # If destination IS a state variable, it's trusted
                        if isinstance(dest, StateVariable):
                            continue
                        # If destination is a ReferenceVariable pointing to a state variable read,
                        # treat it as trusted (handles IERC20(stateVar).call(...) patterns)
                        if isinstance(dest, ReferenceVariable):
                            points_to = getattr(dest, 'points_to_origin', None)
                            if isinstance(points_to, StateVariable):
                                continue
                        # Check if destination is data-dependent on a state variable
                        # (covers patterns where the call target is loaded from storage
                        # through local variable assignments)
                        is_state_derived = False
                        for sv in f.state_variables_read:
                            try:
                                if is_dependent(dest, sv, self.contract):
                                    is_state_derived = True
                                    break
                            except Exception:
                                pass
                        if is_state_derived:
                            # Even though it's state-derived, reject if also param-dependent
                            is_param_dependent = False
                            for param in all_params:
                                try:
                                    if dest == param or is_dependent(dest, param, self.contract):
                                        is_param_dependent = True
                                        break
                                except Exception:
                                    pass
                            if not is_param_dependent:
                                continue
                        # Check if destination depends on any function parameter
                        for param in all_params:
                            try:
                                if is_dependent(dest, param, self.contract):
                                    return False  # User-controlled call target
                            except Exception:
                                pass
                        # Also check if destination IS a parameter directly
                        if dest in all_params:
                            return False
        return True

    def _has_inline_sender_guard(self, func: Function) -> bool:
        """
        Check if a function has an inline early-return sender guard pattern:
        if(msg.sender != X) revert/return; or require(msg.sender == X).
        This catches Compound-style guards that don't use modifiers and don't
        create ROLE_GATED edges (because early-return doesn't create dominance).
        """
        for node in func.nodes:
            # Check require(msg.sender == X) or if(msg.sender != X) patterns
            is_guard = False
            if node.type == NodeType.IF:
                is_guard = True
            else:
                for ir in node.irs:
                    if isinstance(ir, SolidityCall) and ir.function.name.startswith(("require(", "assert(")):
                        is_guard = True
                        break

            if not is_guard:
                continue

            # Check if this guard compares msg.sender against a state variable
            reads_sender = any(
                isinstance(v, SolidityVariableComposed) and v.name == "msg.sender"
                for v in node.variables_read
            )
            if not reads_sender:
                for ir in node.irs:
                    if isinstance(ir, InternalCall) and hasattr(ir, 'function') and ir.function:
                        if getattr(ir.function, 'name', '') in ('_msgSender', 'msgSender'):
                            reads_sender = True
                            break

            if not reads_sender:
                continue

            # Must also read a state variable (the guard target: owner, admin, etc.)
            has_state_read = any(
                isinstance(v, StateVariable) and not isinstance(v.type, MappingType)
                for v in node.state_variables_read
            )
            if has_state_read:
                return True

        return False

    def _is_self_service_write(self, node, state_var: StateVariable, gid: Optional[int]) -> bool:
        """
        [Graph-Driven] 自服务排除：检查状态写入是否为 msg.sender 索引的映射操作。

        Uses STATE_DEPENDENCY edge key_match when graph available.
        Falls through to IR-based check for nested mappings and parameter aliasing
        (e.g., _approve(owner, spender, amount) where owner = msg.sender).
        """
        # Graph-driven: check STATE_DEPENDENCY edge keys
        if self.cpg and gid is not None and gid in self.cpg:
            var_name = state_var.canonical_name if hasattr(state_var, 'canonical_name') else state_var.name
            for _, _, data in self.cpg.out_edges(gid, data=True):
                if data.get("edge_type") == "STATE_DEPENDENCY" and data.get("variable") == var_name:
                    key_match = data.get("key_match", "")
                    write_key = key_match.split("->")[0] if "->" in key_match else ""
                    if write_key == "msg.sender":
                        return True
            # Graph check didn't find sender key — fall through to IR check
            # (handles nested mappings where graph records parameter name instead of msg.sender)

        # IR-based check: direct lvalue index
        for ir in node.irs:
            if isinstance(ir, (Assignment, Binary)):
                lvalue = ir.lvalue
                if isinstance(lvalue, ReferenceVariable):
                    index = getattr(lvalue, 'index', None)
                    if isinstance(index, SolidityVariableComposed) and index.name == "msg.sender":
                        return True
                    if any(isinstance(v, SolidityVariableComposed) and v.name == "msg.sender" for v in ir.read):
                        return True

        # Extended: check Index operations for nested mappings and parameter aliasing
        # Handles patterns like _approve(msg.sender, spender, amount) where the callee
        # indexes _allowances[owner] with owner being a msg.sender-dependent parameter.
        from slither.slithir.operations import Index as IndexOp
        sender = SolidityVariableComposed("msg.sender")
        for ir in node.irs:
            if isinstance(ir, IndexOp):
                right_var = ir.variable_right
                if isinstance(right_var, SolidityVariableComposed) and right_var.name == "msg.sender":
                    return True
                try:
                    if is_dependent(right_var, sender, self.contract):
                        return True
                except Exception:
                    pass

        return False

    def _is_sender_or_dependent(self, var, func: Function) -> bool:
        """
        检查变量是否为 msg.sender 或数据依赖于 msg.sender。
        处理 _msgSender() 包装器（OpenZeppelin Context.sol）和局部变量别名
        （如 address account = msg.sender）。
        """
        if isinstance(var, SolidityVariableComposed) and var.name == "msg.sender":
            return True
        sender = SolidityVariableComposed("msg.sender")
        try:
            if is_dependent(var, sender, self.contract):
                return True
        except Exception:
            pass
        return False

    def _detect_self_service_indicators(self, func: Function) -> List[str]:
        """
        检测函数的自服务语义指标。

        基于 EIP 标准定义的四类结构化模式：
        - SENDER_INDEXED_WRITE: 映射写入以 msg.sender 为索引（EIP-20 balances/allowances）
        - SENDER_FUNDED:       外部调用以 msg.sender 为资金来源（safeTransferFrom(msg.sender,...)）
        - ALLOWANCE_GATED:     函数读取/消耗 allowance 映射（EIP-20 授权机制）
        - SELF_BURN:           _burn(msg.sender, amount) 只销毁调用者自己的代币

        返回结构化注解列表，用于注入 LLM 提示而非过滤函数。
        使用 Slither 的 is_dependent() 确保通过局部变量和 _msgSender() 的追踪。
        """
        indicators = []
        found_types = set()

        # Also check internal calls for deeper patterns (including inherited functions)
        all_funcs = self._collect_internal_callees(func)

        for f in all_funcs:
            for node in f.nodes:
                gid = self._resolve_gid(f, node) if self.node_mapping else None

                # --- SENDER_INDEXED_WRITE ---
                if "SENDER_INDEXED_WRITE" not in found_types:
                    for var in node.variables_written:
                        if isinstance(var, StateVariable):
                            if self._is_self_service_write(node, var, gid):
                                indicators.append(
                                    f"SENDER_INDEXED_WRITE: State variable '{var.name}' "
                                    f"written at mapping index derived from msg.sender"
                                )
                                found_types.add("SENDER_INDEXED_WRITE")
                                break

                # --- SENDER_FUNDED ---
                if "SENDER_FUNDED" not in found_types:
                    for ir in node.irs:
                        if isinstance(ir, HighLevelCall) and not isinstance(ir, LibraryCall):
                            callee_name = ""
                            if hasattr(ir, 'function') and ir.function:
                                callee_name = ir.function.name if hasattr(ir.function, 'name') else ""
                            if callee_name in ('transferFrom', 'safeTransferFrom') and hasattr(ir, 'arguments') and ir.arguments:
                                if self._is_sender_or_dependent(ir.arguments[0], f):
                                    indicators.append(
                                        f"SENDER_FUNDED: '{callee_name}' pulls funds from msg.sender "
                                        f"(caller provides own assets)"
                                    )
                                    found_types.add("SENDER_FUNDED")
                                    break

                # --- ALLOWANCE_GATED ---
                if "ALLOWANCE_GATED" not in found_types:
                    for ir in node.irs:
                        if isinstance(ir, InternalCall) and ir.function:
                            callee_name = ir.function.name if hasattr(ir.function, 'name') else ""
                            if callee_name in ('_spendAllowance', '_approve', '_burnAllowance'):
                                indicators.append(
                                    f"ALLOWANCE_GATED: Uses '{callee_name}' (EIP-20 allowance authorization)"
                                )
                                found_types.add("ALLOWANCE_GATED")
                                break
                    if "ALLOWANCE_GATED" not in found_types:
                        for var in node.state_variables_read:
                            if hasattr(var, 'name') and 'allowance' in var.name.lower():
                                if hasattr(var, 'type') and isinstance(var.type, MappingType):
                                    indicators.append(
                                        f"ALLOWANCE_GATED: Reads allowance mapping '{var.name}' "
                                        f"(EIP-20 delegated authorization)"
                                    )
                                    found_types.add("ALLOWANCE_GATED")
                                    break

                # --- SELF_BURN ---
                if "SELF_BURN" not in found_types:
                    for ir in node.irs:
                        if isinstance(ir, InternalCall) and ir.function:
                            callee_name = ir.function.name if hasattr(ir.function, 'name') else ""
                            if callee_name in ('_burn', '_burnFrom') and hasattr(ir, 'arguments') and ir.arguments:
                                if self._is_sender_or_dependent(ir.arguments[0], f):
                                    indicators.append(
                                        f"SELF_BURN: '{callee_name}(msg.sender, ...)' "
                                        f"only destroys caller's own tokens"
                                    )
                                    found_types.add("SELF_BURN")
                                    break

        return indicators

    def _has_cross_user_mutation(self, func: Function) -> bool:
        """
        [Graph-Driven] S6: 检测跨用户状态变更。
        使用 STATE_DEPENDENCY 边的索引敏感性检测参数控制的映射写入。

        Fallback: IR 级别的 Index 操作检查。
        """
        if self.cpg and self.node_mapping:
            for node in func.nodes:
                gid = self._resolve_gid(func, node)
                if gid is None or gid not in self.cpg:
                    continue

                for _, _, data in self.cpg.out_edges(gid, data=True):
                    if data.get("edge_type") != "STATE_DEPENDENCY":
                        continue

                    key_match = data.get("key_match", "")
                    if not key_match or "SCALAR" in key_match:
                        continue

                    write_key = key_match.split("->")[0] if "->" in key_match else ""
                    # Non-sender, non-scalar indexed write → potential cross-user mutation
                    if write_key and write_key not in ("msg.sender", "SCALAR", "None"):
                        return True

            return False

        # Fallback: IR-based approach
        from slither.slithir.operations import Index
        sender = SolidityVariableComposed("msg.sender")

        all_funcs = [func]
        for call in func.all_internal_calls():
            if isinstance(call, Function):
                all_funcs.append(call)

        has_write = any(f.state_variables_written for f in all_funcs if hasattr(f, 'state_variables_written'))
        if not has_write:
            return False

        for f in all_funcs:
            if f.contract != self.contract:
                continue
            for node in f.nodes:
                for ir in node.irs:
                    if isinstance(ir, Index):
                        index = ir.variable_right
                        if index != sender and not hasattr(index, 'value'):
                            if index in f.parameters or any(is_dependent(index, p, self.contract) for p in f.parameters):
                                return True

        return False

    # ── Peer Function Selection (Intra-Contract Comparative Inference) ──

    def select_peers(self, target_func: Function, relevant_map: Dict[Function, List[Tuple]], k: int = 3) -> List[Dict]:
        """
        Select top-k peer functions from the same contract for comparative inference.

        Candidate pool: all public/external, non-constructor/fallback/receive/view/pure
        functions in the contract (excluding target itself) that have sinks.

        Scoring (4 signals, weighted sum):
          - Sink Type Overlap (0.35): Jaccard similarity of sink types
          - State Variable Overlap (0.30): Jaccard similarity of state vars (read + written)
          - Guard Asymmetry Bonus (0.20): 1.0 if target is unguarded and peer is guarded
          - Modifier Overlap (0.15): Jaccard similarity of modifier names

        Returns:
            List of top-k peers, each a dict with:
                {func_name, score, sink_types, is_guarded, shared_state_vars, modifiers, code}
        """
        if not hasattr(self, '_all_function_sinks') or not self._all_function_sinks:
            return []

        # Target's data: prefer pre-stored data, fall back to computing on the fly
        target_data = self._all_function_sinks.get(target_func)
        if target_data:
            target_sink_types = target_data["sink_types"]
            target_state_vars = target_data["state_vars_read"] | target_data["state_vars_written"]
            target_is_guarded = target_data["is_guarded"]
            target_modifiers = set(target_data["modifiers"])
        else:
            # Target might not be in _all_function_sinks if it has no sinks (edge case)
            target_sink_types = set(s[1] for s in relevant_map.get(target_func, []))
            target_state_vars = (
                {v.name for v in target_func.state_variables_read if isinstance(v, StateVariable)}
                | {v.name for v in target_func.state_variables_written if isinstance(v, StateVariable)}
            )
            target_is_guarded = False
            target_modifiers = {m.name for m in target_func.modifiers}

        candidates = []
        for func, data in self._all_function_sinks.items():
            if func == target_func:
                continue
            # Skip view/pure functions (no state modification)
            if getattr(func, 'view', False) or getattr(func, 'pure', False):
                continue
            if getattr(func, 'is_view', False) or getattr(func, 'is_pure', False):
                continue

            cand_sink_types = data["sink_types"]
            cand_state_vars = data["state_vars_read"] | data["state_vars_written"]
            cand_is_guarded = data["is_guarded"]
            cand_modifiers = set(data["modifiers"])

            # Signal 1: Sink Type Overlap (Jaccard)
            sink_union = target_sink_types | cand_sink_types
            sink_inter = target_sink_types & cand_sink_types
            sink_jaccard = len(sink_inter) / len(sink_union) if sink_union else 0.0

            # Signal 2: State Variable Overlap (Jaccard)
            sv_union = target_state_vars | cand_state_vars
            sv_inter = target_state_vars & cand_state_vars
            sv_jaccard = len(sv_inter) / len(sv_union) if sv_union else 0.0

            # Signal 3: Guard Asymmetry Bonus
            guard_bonus = 1.0 if (not target_is_guarded and cand_is_guarded) else 0.0

            # Signal 4: Modifier Overlap (Jaccard)
            mod_union = target_modifiers | cand_modifiers
            mod_inter = target_modifiers & cand_modifiers
            mod_jaccard = len(mod_inter) / len(mod_union) if mod_union else 0.0

            score = (0.35 * sink_jaccard
                     + 0.30 * sv_jaccard
                     + 0.20 * guard_bonus
                     + 0.15 * mod_jaccard)

            if score < 0.05:
                continue

            shared_sv = sorted(target_state_vars & cand_state_vars)

            candidates.append({
                "func_name": func.name,
                "score": round(score, 3),
                "sink_types": sorted(cand_sink_types),
                "is_guarded": cand_is_guarded,
                "shared_state_vars": shared_sv,
                "modifiers": sorted(cand_modifiers),
                "code": self._get_peer_code(func),
            })

        # Sort by score descending, take top-k
        candidates.sort(key=lambda c: c["score"], reverse=True)
        return candidates[:k]

    def _get_peer_code(self, func: Function) -> str:
        """Extract source code of a peer function via Slither's source_mapping."""
        try:
            sm = func.source_mapping
            if sm and sm.filename and sm.filename.absolute:
                with open(sm.filename.absolute, 'r', encoding='utf-8') as f:
                    content = f.read()
                start = sm.start
                length = sm.length
                if start >= 0 and length > 0 and start + length <= len(content):
                    return content[start:start + length]
        except Exception:
            pass
        return f"function {func.name}(...) {{ /* Source unavailable */ }}"
