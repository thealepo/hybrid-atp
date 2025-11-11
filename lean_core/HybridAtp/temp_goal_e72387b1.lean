import Mathlib

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  rw [add_zero]; exact rfl
