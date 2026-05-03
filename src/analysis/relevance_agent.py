import logging
import json
import os
from typing import List, Dict, Any, Optional
from pydantic import BaseModel
from src.llm.service import LLMService

logger = logging.getLogger(__name__)

class MissingContext(BaseModel):
    missing_functions: List[str]
    missing_variables: List[str]
    reasoning: str

class RelevanceAgent:
    """Finds context that is still missing for trace simulation."""
    def __init__(self, api_key: Optional[str] = None):
        self.model = "gpt-4o-mini"
        self.llm_service = LLMService(api_key=api_key, model=self.model) 

    def analyze_missing_context(self, current_context: str, target_function: str, trace_error: str = "") -> MissingContext:
        """Identify missing functions or variables from the current context."""
        system_prompt = (
            "You are a 'Context Relevance Analyzer' for a Smart Contract Security Tool.\n"
            "Your goal is to analyze a 'Partial Execution Context' and identify MISSING function definitions "
            "or state variables that are required to simulate the 'Target Function'.\n\n"
            "### RULES:\n"
            "1. Look for function calls in the Target Function (or its known dependencies) that have NO definition in the context.\n"
            "2. Look for modifiers that are used but not defined.\n"
            "3. Ignore standard library calls (e.g., require, assert, keccak256, ecrecover) or low-level calls (call, delegatecall) unless they wrap a specific logic function.\n"
            "4. Return a list of strictly missing function names (e.g., ['_internalHelper', 'onlyOwner']).\n"
            "5. Be precise. Do not hallucinate names.\n\n"
            "### OUTPUT FORMAT (JSON):\n"
            "{\n"
            "  \"missing_functions\": [\"funcName1\", \"funcName2\"],\n"
            "  \"missing_variables\": [],\n"
            "  \"reasoning\": \"funcName1 is called at line 10 but not defined.\"\n"
            "}"
        )

        user_prompt = (
            f"### CURRENT CONTEXT:\n{current_context}\n\n"
            f"### TARGET FUNCTION:\n{target_function}\n\n"
            f"### TRACE ERROR (If any):\n{trace_error}\n\n"
            "Identify missing dependencies:"
        )

        try:
            data = self.llm_service.call_completion(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                model=self.model,
                temperature=0.1,
                response_format={"type": "json_object"}
            )
            
            if not data:
                return MissingContext(missing_functions=[], missing_variables=[], reasoning="Empty response")
            
            if isinstance(data, dict):
                return MissingContext(
                    missing_functions=data.get("missing_functions", []),
                    missing_variables=data.get("missing_variables", []),
                    reasoning=data.get("reasoning", "")
                )
            else:
                 return MissingContext(missing_functions=[], missing_variables=[], reasoning="Invalid response format")
                 
        except Exception as e:
            logger.error(f"Relevance Analysis failed: {e}")
            return MissingContext(missing_functions=[], missing_variables=[], reasoning=str(e))
