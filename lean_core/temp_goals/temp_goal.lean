import Mathlib
import HybridAtp.Basic

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  simp only [add_zero]
