import Mathlib

open Complex Real MeasureTheory Filter
open scoped Topology

example (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  exact RCLike.norm_ofReal x

example (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [RCLike.norm_ofReal (𝕜 := ℂ) x]
  exact abs_of_nonneg hx

example (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  calc
    ‖(x : ℂ)‖ = |x| := RCLike.norm_ofReal x
    _ = x := abs_of_nonneg hx

example (a b : ℝ) (hab : 0 ≤ a - b) : ‖((a - b : ℝ) : ℂ)‖ = a - b := by
  calc
    ‖((a - b : ℝ) : ℂ)‖ = |a - b| := RCLike.norm_ofReal (a - b)
    _ = a - b := abs_of_nonneg hab

example (x : ℝ) : ‖((x : ℂ) * (2 : ℂ))‖ = ‖(x : ℂ)‖ * ‖(2 : ℂ)‖ := by
  rw [norm_mul]

example (x : ℝ) (hx : 0 ≤ x) (hlog : 0 ≤ Real.log x) :
    ‖((Real.log x : ℝ) : ℂ)‖ = Real.log x := by
  calc
    ‖((Real.log x : ℝ) : ℂ)‖ = |Real.log x| := RCLike.norm_ofReal (Real.log x)
    _ = Real.log x := abs_of_nonneg hlog
