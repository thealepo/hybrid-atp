from lean_dojo import *
from validator import LeanDojoValidator

repo_url = "https://github.com/leanprover-community/mathlib4"
file_path = "Mathlib/Algebra/Ring/Defs.lean"
theorem_name = "add_comm"

validator = LeanDojoValidator(repo_url, file_path, theorem_name)
print(validator.state_tactic_pairs)