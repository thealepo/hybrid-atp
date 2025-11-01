
import Mathlib
import HybridAtp.Basic

theorem temp_goal : ∀ (n : ℕ), n + 0 = n := by
  exact congr_arg (λ (n : ℕ), n + 0) (add_zero n)
