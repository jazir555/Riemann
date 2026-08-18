import Mathlib

example (n : ℕ) (σ : ℝ) (y : ℝ) (hσpos : 0 < σ) (hyge : σ / 2 ≤ y) :
    (n + 1 : ℝ) ^ (-(y + 1)) ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) := by
  push_cast
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

example (n : ℕ) : 0 ≤ Real.log (n + 2 : ℝ) := by
  push_cast
  exact Real.log_nonneg (by linarith)
