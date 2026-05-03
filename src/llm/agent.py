# 核心库导入
import os
import json
import logging
import re
from typing import Dict, Any, List, Optional, Union
from enum import Enum
from pydantic import BaseModel, Field
from pathlib import Path
from src.llm.service import LLMService

# 配置日志
logger = logging.getLogger(__name__)

# --- 1. Structured Output Models (Pydantic) ---

class PolicyPrediction(BaseModel):
    """AuditorAgent 的输出结构 (自然语言版)"""
    reasoning: str = Field(..., description="关于授权逻辑的逐步推理过程")
    intended_policy_nl: str = Field(..., description="自然语言描述的预期策略 (Legacy field)")
    access_level: str = Field(..., description="Who can enter the function? (e.g., Public, Owner, Role)")
    security_invariants: Union[str, List[str]] = Field(..., description="What specific behaviors must be forbidden regardless of the caller? (e.g., 'Must not allow arbitrary external calls')")
    evidence_snippets: List[str] = Field(..., description="支持该策略的代码片段")
    risk_analysis: str = Field(..., description="如果违反策略的后果 (DeFi 专家视角)")
    confidence: float = Field(default=0.0, description="置信度分数")
    compliance_assessment: str = Field(
        default="UNKNOWN",
        description="初步合规性评估: COMPLIANT (看似有防护), VIOLATED (看似无防护), UNKNOWN (需要深入分析)"
    )
    peer_comparison: str = Field(
        default="",
        description="Summary of how this function's protection compares to structurally similar peer functions in the same contract"
    )

# --- 2. Base Infrastructure ---

class BaseAgent:
    """
    基础智能体类，委托 LLMService 处理 API 调用。
    """
    def __init__(self, model_name: str = "gpt-4o-mini", api_key: Optional[str] = None):
        self.model_name = model_name
        self.llm_service = LLMService(api_key=api_key, model=model_name)

    def _call_llm(self, system_prompt: str, user_prompt: str, response_model: Any, retries: int = 2) -> Any:
        return self.llm_service.call_completion(
            system_prompt=system_prompt,
            user_prompt=user_prompt,
            response_model=response_model,
            model=self.model_name,
            retries=retries
        )

# --- 3. Specialized Agents ---

class AuditorAgent(BaseAgent):
    """
    Role: Smart Contract Access Control Auditor
    Task: 推断函数预期的访问控制策略 (Natural Language Policy Generation)。
    """
    def infer_policy(self, code: str, context: str, symbols: Dict[str, str], static_warnings: List[str] = None, func_metadata: Dict = None, peer_evidence: str = "") -> PolicyPrediction:
        # 1. Constructor exemption (using Slither metadata, not string matching)
        if func_metadata and func_metadata.get("is_constructor"):
            return PolicyPrediction(
                reasoning="Constructor executes only once during deployment. Initial setup phase.",
                intended_policy_nl="Safe (Initialization phase)",
                access_level="Restricted (Constructor)",
                security_invariants="None (Deployment)",
                evidence_snippets=[],
                risk_analysis="None. Deployment logic.",
                confidence=1.0
            )

        # 2. View/Pure function handling (using Slither metadata, not string matching)
        if func_metadata and (func_metadata.get("is_view") or func_metadata.get("is_pure")):
            return PolicyPrediction(
                reasoning="Function is marked as view or pure, indicating it does not modify state.",
                intended_policy_nl="Publicly accessible",
                access_level="Public",
                security_invariants="No state modification",
                evidence_snippets=[],
                risk_analysis="Minimal risk as no state modification occurs.",
                confidence=1.0
            )
        
        # 3. Static Warning Context Injection
        warning_context = ""
        if static_warnings:
            warning_context = "\n[CRITICAL STATIC ANALYSIS WARNINGS]:\n" + "\n".join([f"- {w}" for w in static_warnings]) + "\n"

        system_prompt = (
            "TASK: Analyze the provided Solidity function and infer its intended Access Control Policy.\n\n"
            "### OBJECTIVES\n"
            "1. **Privilege Inference**: Determine the required authorization level (e.g., Public, Owner, DAO) based on modifiers, state checks, and function visibility.\n"
            "2. **Invariant Generation**: Formulate security invariants that must hold true for this function to prevent unauthorized state manipulation or asset loss.\n\n"
            "### PERMISSIONLESS-BY-DESIGN PRINCIPLE (CRITICAL)\n"
            "Many DeFi functions are intentionally public without access control. Do NOT infer 'Restricted' "
            "or 'Owner/Admin' access for the following patterns unless the code contains an explicit but "
            "insufficient access check:\n"
            "- **Token standard operations**: transfer, transferFrom, approve, burn, mint (ERC20/ERC721/ERC1155) "
            "that operate on msg.sender's own balance or allowance\n"
            "- **DeFi user operations**: deposit, withdraw, swap, borrow, repay, liquidate, claim, stake, "
            "unstake, delegate, redeem, supply, exit, enter\n"
            "- **Epoch/checkpoint functions**: newEpoch, advanceEpoch, checkpoint, poke, sync, update\n"
            "- **Functions with `initializer` modifier**: Already one-time guarded by OpenZeppelin Initializable\n"
            "For these patterns, assign access level 'Public' or 'Public (Self-Service)' unless the code shows "
            "a SPECIFIC broken access check (e.g., require that exists but is bypassable).\n\n"
            "### IMPORTANT EXCEPTIONS TO SELF-SERVICE / INITIALIZATION LABELS\n"
            "Do NOT classify a function as 'Public (Self-Service)' or 'Public (Initialization Phase)' merely because "
            "it is public or uses an initialization modifier if ANY of the following hold:\n"
            "1. The function changes governance/configuration state (owner sets, allowlists, fee tables, swap pairs, token listers, reward rates, oracle/config values).\n"
            "2. The function settles orders, auctions, marketplace fills, cancellation registries, or cross-user entitlements.\n"
            "3. The function updates multi-party wallet initialization, owner sets, required confirmations, or daily limits.\n"
            "4. The function performs external transfers/calls whose effects are not obviously restricted to msg.sender only.\n"
            "5. Static warnings mention [UNGUARDED], [CROSS-USER MUTATION], control variables, low-level calls, or suspicious initialization.\n"
            "In these cases, prefer a restricted or unknown policy unless the code provides explicit evidence that the operation is safely caller-local.\n\n"
            "### EVIDENCE REQUIREMENT FOR 'RESTRICTED'\n"
            "Only classify a function as 'Restricted' (Owner/Admin/Role) when at least ONE of these conditions holds:\n"
            "1. The code contains an explicit access modifier (onlyOwner, onlyRole, etc.) that appears insufficient\n"
            "2. The code contains an inline require/if checking msg.sender against a state variable, but "
            "the check is bypassable or missing for some paths\n"
            "3. The function modifies governance-critical scalar state (owner, admin, paused, oracle, fee rate) "
            "AND has zero access checks\n"
            "If the function simply writes to msg.sender-indexed mappings or calls external contracts with "
            "msg.sender's funds, classify as 'Public (Self-Service)', NOT 'Restricted'.\n\n"
            "### ANALYSIS FRAMEWORK\n"
            "- **State Operations**: Identify writes to critical state variables (e.g., ownership, balances).\n"
            "- **External Interactions**: Analyze calls to external contracts (e.g., transfer, delegatecall).\n"
            "- **Control Flow**: Examine conditions (require/if) that restrict execution.\n"
            "- **Self-Service**: If [SELF-SERVICE CONTEXT] annotations are present, the function operates on msg.sender's own state. Assign access level 'Public (Self-Service)'.\n\n"
            "### STATIC WARNINGS INTEGRATION\n"
            "If [CRITICAL STATIC ANALYSIS WARNINGS] are present, consider them as supplementary signals but "
            "do NOT let [UNGUARDED] warnings alone override the permissionless-by-design principle. "
            "An [UNGUARDED] state modification is expected for self-service and standard DeFi operations. "
            "Only elevate the warning when the unguarded operation modifies governance state (owner, admin, "
            "paused, oracle) or enables cross-user fund extraction. If the warning involves marketplace settlement, "
            "cancellation, wallet initialization, reward configuration, or swap-pair configuration, do NOT classify "
            "the function as confidently safe.\n\n"
            "### PEER FUNCTION COMPARISON\n"
            "If [PEER FUNCTION EVIDENCE] is provided, it lists structurally similar functions from the SAME "
            "contract that share state variables or sink types with the target function. Use these as comparative "
            "evidence for policy inference:\n"
            "- If a peer performs similar operations (same sink types, shared state variables) but HAS access "
            "control while the target does NOT, this asymmetry is strong evidence that the target is missing "
            "required protection. Mention this in your reasoning and peer_comparison.\n"
            "- If all peers performing similar operations are also unguarded, this may indicate the operations "
            "are permissionless by design.\n"
            "- Do NOT automatically classify a function as vulnerable just because a peer is guarded. Evaluate "
            "whether the shared operations actually require the same protection level.\n"
            "- Summarize the comparison result in the 'peer_comparison' field.\n\n"
            "### OUTPUT FORMAT (JSON)\n"
            "{\n"
            "  \"reasoning\": \"Logical deduction of the policy based on code analysis.\",\n"
            "  \"access_level\": \"Required privilege (e.g., 'Owner', 'Public', 'Public (Self-Service)', 'Whitelisted').\",\n"
            "  \"security_invariants\": \"List of strict conditions that must be enforced.\",\n"
            "  \"intended_policy_nl\": \"Concise summary of the inferred policy.\",\n"
            "  \"evidence_snippets\": [\"Code lines supporting the inference.\"],\n"
            "  \"risk_analysis\": \"Potential security impact if the policy is violated.\",\n"
            "  \"confidence\": 0.0 to 1.0,\n"
            "  \"peer_comparison\": \"How this function's protection compares to similar peers (empty string if no peers provided).\"\n"
            "}"
        )

        # Build user prompt with optional peer evidence
        peer_section = f"\n{peer_evidence}" if peer_evidence else ""
        user_prompt = f"Symbols: {json.dumps(symbols)}\nContext: {context}{warning_context}{peer_section}\nCode:\n{code}"

        return self._call_llm(system_prompt, user_prompt, PolicyPrediction)


# --- 4. Facade: Multi-Agent System ---

class MultiAgentSystem:
    """
    Simplified Agent Facade (Auditor Only).
    """
    def __init__(self, model_name: str = "gpt-4o-mini", api_key: Optional[str] = None):        self.auditor_agent = AuditorAgent(model_name, api_key)

    def analyze_function(self, code: str, context: str, symbols: Dict[str, str], static_warnings: List[str] = None) -> Dict[str, Any]:
        """
        Runs the Policy Inference Agent.
        """
        # Policy Inference (Natural Language)
        policy = self.auditor_agent.infer_policy(code, context, symbols, static_warnings)
        
        return {
            "status": "ANALYZED",
            "policy": policy
        }

# 为向后兼容保留 LLMAgent 类名
class LLMAgent(AuditorAgent):
    """向后兼容的 LLMAgent，现在由 AuditorAgent 实现核心逻辑。"""
    pass
