import Mathlib

theorem temp_goal : ∀ (n : ℕ), (∑ i in finset.range n, (i : ℕ)) = n * (n - 1) / 2 := by
  rw mul_comm, rw mul_assoc, rw mul_comm
