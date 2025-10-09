import os
from dotenv import load_dotenv

load_dotenv()
HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

print(HF_TOKEN)