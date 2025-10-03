from typing import Optional

from google import genai

class GeminiLeanTranslator:

    def __init__(self , api_key: Optional[str] = None , model_name: str = 'gemini-1.5-pro'):
        client = genai.Client(api_key=api_key)
        self.model = client.models.get(model_name)
    
    