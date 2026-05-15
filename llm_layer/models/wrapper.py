"""Unified wrapper over local HF seq2seq models and HF Inference Endpoints."""
from __future__ import annotations

from typing import Any, Dict, List, Optional

import torch
from huggingface_hub import InferenceClient
from transformers import AutoModelForSeq2SeqLM, AutoTokenizer


class Model:
    """Wrapper that hides the difference between local HF models and Inference Endpoints.

    - If `use_inference_endpoint=True`, calls a private endpoint URL.
    - If model id contains "t5", load locally via transformers (LeanDojo's
      ByT5 retriever-tacgen model is the canonical case).
    - Otherwise, call HF's hosted Inference API for the model id.
    """

    def __init__(
        self,
        model_id: str,
        api_token: str,
        use_inference_endpoint: bool = False,
        endpoint_url: Optional[str] = None,
        generation_config: Optional[Dict[str, Any]] = None,
    ):
        self.model_id = model_id
        self.api_token = api_token
        self.use_inference_endpoint = use_inference_endpoint
        self.endpoint_url = endpoint_url
        self.generation_config: Dict[str, Any] = generation_config or {
            "temperature": 0.2,
            "top_p": 0.9,
            "max_new_tokens": 512,
        }

        self.is_local = "t5" in model_id.lower() and not use_inference_endpoint

        self.client: Optional[InferenceClient] = None
        self.model = None
        self.tokenizer = None
        self.device: Optional[str] = None

        if use_inference_endpoint and endpoint_url:
            self.client = InferenceClient(model=endpoint_url, token=api_token)
            self.is_local = False
        elif self.is_local:
            self.device = "cuda" if torch.cuda.is_available() else "cpu"
            self.tokenizer = AutoTokenizer.from_pretrained(model_id, token=api_token)
            self.model = AutoModelForSeq2SeqLM.from_pretrained(model_id, token=api_token).to(self.device)
        else:
            self.client = InferenceClient(model=model_id, token=api_token)

    def chat_completion(self, messages: List[Dict[str, str]], config: Optional[Dict[str, Any]] = None) -> str:
        if self.is_local:
            prompt = messages[-1]["content"]
            return self.text_generation(prompt, config)

        final_config = {**self.generation_config, **(config or {})}
        max_new = final_config.pop("max_new_tokens", 512)
        final_config["max_tokens"] = max_new

        response = self.client.chat_completion(messages=messages, **final_config)
        return response.choices[0].message.content

    def text_generation(self, prompt: str, config: Optional[Dict[str, Any]] = None, **kwargs) -> str:
        final_config = {**self.generation_config, **(config or {}), **kwargs}

        if self.is_local:
            inputs = self.tokenizer(prompt, return_tensors="pt", truncation=True, max_length=2048).to(self.device)
            final_config.pop("model", None)
            final_config.pop("prompt", None)
            final_config.pop("top_p", None) if final_config.get("do_sample") is False else None

            outputs = self.model.generate(**inputs, **final_config)
            return self.tokenizer.decode(outputs[0], skip_special_tokens=True)

        output = self.client.text_generation(prompt=prompt, **final_config)
        return output.generated_text if hasattr(output, "generated_text") else output

    def sample_local(
        self,
        prompt: str,
        num_return_sequences: int = 1,
        num_beams: Optional[int] = None,
        do_sample: bool = True,
        max_new_tokens: int = 256,
        temperature: float = 0.8,
        top_p: float = 0.95,
    ) -> List[str]:
        """Generate multiple distinct candidates from a local seq2seq model.

        Used to produce a diverse set of candidate tactics from the LeanDojo
        retriever-tacgen ByT5 model.
        """
        if not self.is_local:
            raise RuntimeError("sample_local only supported for local seq2seq models")

        inputs = self.tokenizer(prompt, return_tensors="pt", truncation=True, max_length=2048).to(self.device)
        gen_kwargs: Dict[str, Any] = {
            "max_new_tokens": max_new_tokens,
            "num_return_sequences": num_return_sequences,
        }
        if num_beams:
            gen_kwargs.update({"num_beams": num_beams, "do_sample": False, "early_stopping": True})
        else:
            gen_kwargs.update({"do_sample": do_sample, "temperature": temperature, "top_p": top_p})

        outputs = self.model.generate(**inputs, **gen_kwargs)
        return [self.tokenizer.decode(o, skip_special_tokens=True) for o in outputs]
