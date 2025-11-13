import Mathlib

theorem temp_goal : f g : ℝ → ℝ
hf : (∀ (x y : ℝ), x ≤ y → f y ≤ f x)
hg : (∀ (x y : ℝ), x ≤ y → g y ≤ g x)
 ∀ (x y : ℝ), x ≤ y → (f y + g y) ≤ (f x + g x) := by
  i
