import os
import json
import logging
from typing import List, Dict, Any, Optional
from pydantic import BaseModel, Field
from src.llm.agent import BaseAgent

# 配置日志
logger = logging.getLogger(__name__)

from typing import List, Union, Optional
from pydantic import BaseModel, Field, field_validator

class VerificationResult(BaseModel):
    """验证结果的数据结构"""
    status: str = Field(..., description="VULNERABLE, SAFE, or UNKNOWN")

    # 1. 兼容 reasoning 可能是字符串或列表的情况
    reasoning: Union[str, List[str]] = Field(..., description="详细的漏洞推理或安全分析过程")

    # 2. 修复本次报错：将 severity 设为可选，并给予默认值 'None'
    # 这样即使 LLM 忘了输出 severity 字段，程序也不会崩
    severity: str = Field(default="None", description="High, Medium, Low, or None")

    # 验证器：自动将列表格式的 reasoning 转换为字符串
    @field_validator('reasoning', mode='before')
    @classmethod
    def convert_list_to_string(cls, v):
        if isinstance(v, list):
            return "\n".join(str(item) for item in v)
        return v
class LLMVerifier(BaseAgent):
    """
    Role: Smart Contract Security Verification Expert
    Task: 通过"虚拟执行"代码轨迹来验证是否违反了自然语言描述的访问控制策略。
    """

    def __init__(self, model_name: str = "gpt-4o-mini", api_key: Optional[str] = None):
        super().__init__(model_name, api_key)

    def verify_trace(self, trace_lines: List[str], intended_policy: str, contract_context: str = "",
                     access_level: str = "", self_service_indicators: List[str] = None) -> VerificationResult:
        """
        验证给定的执行轨迹是否符合预期的安全策略。

        Args:
            access_level: Structured access level from Policy Agent (e.g., "Public (Self-Service)").
            self_service_indicators: Structural self-service evidence from static analysis.
        """
        # Build structured access context for the prompt
        access_context = ""
        if access_level:
            access_context += f"\n### POLICY AGENT CLASSIFICATION\nAccess Level: {access_level}\n"
        if self_service_indicators:
            access_context += "Self-Service Evidence (from static analysis):\n"
            for ind in self_service_indicators:
                access_context += f"  - {ind}\n"

        system_prompt = (
            "TASK: Verify whether the provided Execution Trace violates the intended access-control policy.\n\n"
            "### CORE RULE\n"
            "If the trace reaches a sensitive state write or external interaction without enforcing the intended policy, "
            "classify as VULNERABLE.\n\n"
            "### IMPORTANT BIAS CORRECTION\n"
            "Do NOT over-trust apparent guards if the trace narrative or state transition implies they can be bypassed, "
            "are misapplied, or protect the wrong principal.\n"
            "Do NOT default to SAFE merely because a function looks like a common DeFi or token operation.\n"
            "For transferFrom / approve / operator-approval / receiver-hook style functions, verify that authorization "
            "is actually enforced for the affected user's assets, not just for the caller.\n\n"
            "### SELF-SERVICE EXCEPTION\n"
            "Only classify as SAFE when the trace clearly demonstrates purely caller-local behavior and no cross-user impact.\n"
            "If there is any plausible cross-user balance / approval / operator / shared-state effect in the trace, prefer VULNERABLE.\n\n"
            "### OUTPUT FORMAT (JSON)\n"
            "{\n"
            "  \"status\": \"VULNERABLE | SAFE\",\n"
            "  \"reasoning\": \"Concise explanation of why the trace violates or satisfies the intended policy.\",\n"
            "  \"severity\": \"High, Medium, Low, or None\"\n"
            "}"
        )
        trace_text = "\n".join(trace_lines)
        user_prompt = f"### INTENDED POLICY:\n{intended_policy}\n\n{access_context}### CONTRACT CONTEXT:\n{contract_context}\n\n### EXECUTION TRACE:\n{trace_text}"

        try:
            result = self._call_llm(system_prompt, user_prompt, VerificationResult)
            if result:
                logger.info(f"[LLMVerifier] Verification completed: {result.status}")
                return result
            else:
                raise ValueError("LLM returned empty result")

        except Exception as e:
            logger.error(f"[LLMVerifier] Verification failed: {e}")
            return VerificationResult(
                status="UNKNOWN",
                reasoning=f"Verification failed: {str(e)}",
                severity="None"
            )
