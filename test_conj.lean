import Mathlib
example {a b : ℝ} (h : ¬ a < b) : b ≤ a := by
  push_neg at h
  exact h
