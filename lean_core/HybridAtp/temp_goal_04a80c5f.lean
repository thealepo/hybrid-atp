import Mathlib

theorem temp_goal : Prove that the sum of any two decreasing functions is decreasing := by
  have h : LinearMap.add f g = LinearMap.add g f, from LinearMap.add_comp_linear_map f g
