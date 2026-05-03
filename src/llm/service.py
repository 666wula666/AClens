import os
import logging
import json
from typing import Optional, Dict, Any, Type, TypeVar
from pydantic import BaseModel
from openai import OpenAI

logger = logging.getLogger(__name__)

T = TypeVar("T", bound=BaseModel)

class LLMService:
    """
    Unified LLM Service to handle API calls, client initialization, and error handling.
    """
    _instance = None

    def __new__(cls, *args, **kwargs):
        if not cls._instance:
            cls._instance = super(LLMService, cls).__new__(cls)
        return cls._instance

    def __init__(self, api_key: Optional[str] = None, base_url: Optional[str] = None, model: str = "gpt-4o", timeout: float = 300.0):
        if hasattr(self, "client"):
            return

        self.api_key = api_key or os.getenv("OPENROUTER_API_KEY") or os.getenv("OPENAI_API_KEY") or "sk-IdoYpO2psiTTBzIEwv4Cdj2zmsSrh0Ou7jvPXPSYIeIMyk9P"
        
        # Default to OneRouter if not specified (legacy behavior preservation)
        self.base_url = base_url or os.getenv("OPENAI_BASE_URL") or "https://llm.onerouter.pro/v1"
        self.default_model = os.getenv("LLM_MODEL") or model or "gpt-4o"
        self.timeout = timeout

        if not self.api_key:
            logger.warning("LLM API key missing. Please set OPENROUTER_API_KEY or OPENAI_API_KEY.")
        
        self.client = OpenAI(api_key=self.api_key, base_url=self.base_url, timeout=self.timeout)
        self.total_prompt_tokens = 0
        self.total_completion_tokens = 0
        self.total_calls = 0
        logger.info(f"LLMService initialized with model={self.default_model}, base_url={self.base_url}, timeout={self.timeout}")

    def _clean_json_content(self, content: str) -> str:
        """
        Cleans LLM response content to extract valid JSON.
        Removes Markdown code blocks and finds the first '{' and last '}'.
        """
        content = content.strip()
        
        # Remove Markdown code blocks
        if "```" in content:
            # Pattern to match ```json ... ``` or just ``` ... ```
            # We use dotall to match across newlines
            import re
            match = re.search(r"```(?:\w+)?\s*([\s\S]*?)\s*```", content)
            if match:
                content = match.group(1)
        
        content = content.strip()
        
        # Find the outermost JSON object
        start_idx = content.find("{")
        end_idx = content.rfind("}")
        
        if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
            content = content[start_idx:end_idx+1]
            
        return content

    def call_completion(
        self, 
        system_prompt: str, 
        user_prompt: str, 
        response_model: Optional[Type[T]] = None,
        model: Optional[str] = None,
        temperature: float = 0.0,
        response_format: Optional[Dict[str, Any]] = None,
        seed: int = 42,
        retries: int = 2
    ) -> Optional[T]:
        """
        Unified method to call LLM completion.
        
        :param system_prompt: System instruction.
        :param user_prompt: User input.
        :param response_model: Pydantic model to parse the response into. If None, returns raw content (or dict if json_object).
        :param model: Override default model.
        :param temperature: Sampling temperature.
        :param response_format: e.g. {"type": "json_object"}. Auto-set to json_object if response_model is provided.
        :param seed: Random seed for reproducibility.
        :param retries: Number of retries on failure.
        :return: Parsed Pydantic model, or Dict (if json), or str.
        """
        target_model = model or self.default_model
        
        # Auto-set json_object if response_model is present
        if response_model and not response_format:
            response_format = {"type": "json_object"}
            
        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt}
        ]

        for attempt in range(retries + 1):
            try:
                response = self.client.chat.completions.create(
                    model=target_model,
                    messages=messages,
                    temperature=temperature,
                    response_format=response_format,
                    seed=seed
                )
                
                content = response.choices[0].message.content
                if not content:
                    raise ValueError("Empty response from LLM")

                # Track token usage
                if hasattr(response, 'usage') and response.usage:
                    self.total_prompt_tokens += response.usage.prompt_tokens or 0
                    self.total_completion_tokens += response.usage.completion_tokens or 0
                    self.total_calls += 1
                
                # Pre-clean content if we expect JSON
                if response_model or (response_format and response_format.get("type") == "json_object"):
                    content = self._clean_json_content(content)

                # Case 1: Pydantic Model parsing
                if response_model:
                    try:
                        return response_model.model_validate_json(content)
                    except Exception as ve:
                        # Fallback: try parsing as generic JSON then validating
                        try:
                            data = json.loads(content)
                            # Handle wrapped responses (e.g. {"PolicyPrediction": {...}})
                            model_name = response_model.__name__
                            if model_name in data:
                                return response_model.model_validate(data[model_name])
                            # Case-insensitive check
                            for key in data.keys():
                                if key.lower() == model_name.lower():
                                    return response_model.model_validate(data[key])
                            # Direct validation
                            return response_model.model_validate(data)
                        except Exception as inner_e:
                             logger.error(f"[LLMService] Parsing failed. Content snippet: {content[:200]}...")
                             raise inner_e

                # Case 2: Generic JSON
                if response_format and response_format.get("type") == "json_object":
                    try:
                        return json.loads(content)
                    except Exception as json_e:
                        logger.error(f"[LLMService] JSON decode failed. Content snippet: {content[:200]}...")
                        raise json_e

                # Case 3: Raw String
                return content

            except Exception as e:
                logger.error(f"[LLMService] Call failed (Attempt {attempt+1}/{retries+1}): {e}")
                if attempt == retries:
                    logger.error(f"[LLMService] All retries failed. Last error: {e}")
                    return None
        return None

    def get_usage_stats(self) -> Dict[str, Any]:
        """Return accumulated token usage statistics."""
        return {
            "prompt_tokens": self.total_prompt_tokens,
            "completion_tokens": self.total_completion_tokens,
            "total_tokens": self.total_prompt_tokens + self.total_completion_tokens,
            "total_calls": self.total_calls,
        }

    def reset_usage_stats(self):
        """Reset accumulated token usage statistics."""
        self.total_prompt_tokens = 0
        self.total_completion_tokens = 0
        self.total_calls = 0
