from lean_dojo import *
from validator import LeanDojoValidator

repo_url = "https://github.com/yangky11/lean4-example"
file_path = "Lean4Example.lean"
theorem_name = "add_abc"

validator = LeanDojoValidator(repo_url, file_path, theorem_name)
print(validator.state_tactic_pairs)