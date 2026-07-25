import Mathlib

example (z : ℂ) (h : ‖(z ^ 2 + (1 / 4 : ℂ))‖ ≤ z.re ^ 2 + (1 / 2 : ℝ)) :
    ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ ≤ (z.re ^ 2 + (1 / 2 : ℝ)) / 2 := by
  rw [Complex.norm_div, Complex.norm_ofNat]
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2)]
  linarith

-- Test hprod
example (z : ℂ) (hre : 10 < z.re) :
    (z.re ^ 2 + (1 / 2 : ℝ)) / 2 * (1 / z.re ^ 3) ≤ 1 / 4 := by
  have this : (z.re ^ 2 + (1 / 2 : ℝ)) / 2 * (1 / z.re ^ 3) = (z.re ^ 2 + 1 / 2) / (2 * z.re ^ 3) := by ring
  rw [this, div_le_iff₀ (by positivity : (0:ℝ) < 2 * z.re ^ 3)]
  nlinarith [mul_nonneg (sq_nonneg z.re) (sub_nonneg.mpr hre.le)]
