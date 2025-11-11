import Mathlib

theorem temp_goal : ∀ (n : ℕ), n * 0 = 0 := by
  have h : ∀ (n : ℕ), n * 0 = 0, from mul_zero
