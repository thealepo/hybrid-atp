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
        }

        if use_inference_endpoint and endpoint_url:
            self.client = None
        else:
            self.client = InferenceClient(token=api_token)

    def chat_completion(self , messages: List[Dict[str,str]] , config: Optional[Dict] = None) -> str:
        final_config = {**self.generation_config , **(config or{})}
        response = self.client.chat_completion(model=self.model_id , messages=messages , **final_config)
        return response.choices[0].message.content