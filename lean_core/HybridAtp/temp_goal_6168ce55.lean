import Mathlib

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  rw congrArg (fun n => n + 0) (eq.refl n)
