# claude-suggested cleanup
from typing import Optional

def extract_json(raw: str) -> Optional[str]:
    s = raw.strip()

    if "```json" in s:
        s = s.split("```json", 1)[1].rsplit("```", 1)[0].strip()
    elif "```" in s:
        s = s.split("```", 1)[1].rsplit("```", 1)[0].strip()

    first = s.find("{")
    last = s.rfind("}")
    if first != -1 and last != -1 and last > first:
        return s[first:last + 1]

    return None