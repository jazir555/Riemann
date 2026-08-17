import Mathlib

open Complex Real
open scoped Topology

example (x : ℝ) (n : ℕ) : (↑x - (↑↑n : ℂ)) = ↑(x - (n : ℝ)) := by
  norm_cast

example (x : ℝ) (n : ℕ) (s : ℝ) (h : 0 ≤ x) :
    (↑x - (↑↑n : ℂ)) * (↑x : ℂ) ^ (-(s + 1)) = ↑((x - (n : ℝ)) / x ^ (s + 1)) := by
  rw [show -((s : ℂ) + 1) = ((-(s + 1) : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow h (-(s + 1))]
  rw [Real.rpow_neg h]
  norm_cast
