import Mathlib

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  rw eq.symm (eq.refl _)
