import Mathlib

theorem temp_goal : ∀ (n : ℕ), (∑ i in finset.range n, (i : ℕ)) = n * (n - 1) / 2 := by
  simp only [finset.sum_const, finset.sum_range_one]
