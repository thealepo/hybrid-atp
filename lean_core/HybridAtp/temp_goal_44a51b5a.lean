import Mathlib

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  have h : n + 0 = n, from rfl
