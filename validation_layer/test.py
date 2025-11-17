from lean_dojo import *
from validator import LeanDojoValidator
import time

repo_url = "https://github.com/leanprover-community/mathlib4"
file_path = "Mathlib/Data/Nat/Basic.lean"
theorem_name = "Nat.add_comm"

try:
    start_time = time.time()

    validator = LeanDojoValidator(repo_url , file_path , theorem_name)

    state = validator.get_initial_state()
    print(state.pp)

    tactic = "rw [Nat.add_comm]"
    print(tactic)

    response = validator.validate(state , tactic)

    print(response.result_type)

except Exception as e:
    print(e)

print(f"Time taken: {time.time() - start_time} seconds")
