import Mathlib

theorem temp_goal : ∀ (n : ℕ), (∑ i in finset.range n, (i : ℕ)) = n * (n - 1) / 2 := by
  have h : ∀ i j, i ≠ j → i + j = j + i, from dec_trivial
