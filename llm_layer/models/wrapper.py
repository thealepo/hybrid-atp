import torch
from transformers import AutoTokenizer , AutoModelForSeq2SeqLM
from huggingface_hub import InferenceClient
from typing import Optional , Dict , List

class Model:
    def __init__(self , model_id , api_token , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None , generation_config: Optional[Dict] = None):
        self.model_id = model_id
        self.api_token = api_token
        self.use_inference_endpoint = use_inference_endpoint
        self.endpoint_url = endpoint_url
        self.generation_config = generation_config or {
            'temperature': 0.2,
            'top_p': 0.9,
            'max_new_tokens': 512
        }

        self.is_local = 't5' in model_id.lower()

        self.client = None
        self.model = None
        self.tokenizer = None
        self.device = None

        if use_inference_endpoint and endpoint_url:
            self.client = InferenceClient(model=endpoint_url , token=api_token)
            self.is_local = False

        elif self.is_local:
            self.device = 'cuda' if torch.cuda.is_available() else 'cpu'
            self.tokenizer = AutoTokenizer.from_pretrained(model_id , token=api_token)
            self.model = AutoModelForSeq2SeqLM.from_pretrained(model_id , token=api_token).to(self.device)

        else:
            self.client = InferenceClient(model=model_id , token=api_token)


    def chat_completion(self , messages: List[Dict[str,str]] , config: Optional[Dict] = None) -> str:

        if self.is_local:
            prompt = messages[-1]['content']
            return self.text_generation(prompt , config)


        final_config = {**self.generation_config , **(config or{})}
        final_config.pop('max_new_tokens', None)
        final_config['max_tokens'] = self.generation_config.get('max_new_tokens' , 512)

        response = self.client.chat_completion(model=self.model_id , messages=messages , **final_config)
        return response.choices[0].message.content

    def text_generation(self, prompt: str, config: Optional[Dict] = None, **kwargs) -> str:
            final_config = {**self.generation_config, **(config or {}), **kwargs}
            
            if self.is_local:
                inputs = self.tokenizer(prompt, return_tensors='pt').to(self.device)
                
                final_config.pop('model', None)
                final_config.pop('prompt', None)
                
                outputs = self.model.generate(
                    **inputs,
                    **final_config
                )
                return self.tokenizer.decode(outputs[0], skip_special_tokens=True)
            
            output = self.client.text_generation(prompt=prompt, **final_config)
            return output.generated_text if hasattr(output, "generated_text") else output