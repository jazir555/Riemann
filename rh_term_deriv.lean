import Mathlib

open Set MeasureTheory Filter Topology Real
open scoped Interval Topology

noncomputable section

namespace ZetaAsymptotics

/-- `x ^ (-y) = 1 / x ^ y` for `0 ≤ x`. -/
lemma rpow_neg_eq_one_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = 1 / x ^ y := by
  rw [rpow_neg hx, one_div]

/-- Pointwise derivative (w.r.t. the exponent) of `x ^ s` for `0 < x`. -/
lemma hasDerivAt_rpow_exp (x : ℝ) (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fun p : ℝ => x ^ p) (Real.log x * x ^ s) s := by
  have h_inner : HasDerivAt (fun p : ℝ => p * Real.log x) (Real.log x) s := by
    simpa using (hasDerivAt_id s).mul_const (Real.log x)
  have hc : HasDerivAt ((fun p : ℝ => Real.exp p) ∘ fun p : ℝ => p * Real.log x)
      (Real.exp (s * Real.log x) * Real.log x) s :=
    (hasDerivAt_exp (s * Real.log x)).comp s h_inner
  refine (hc.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [rpow_def_of_pos hx]
    rw [mul_comm (Real.exp (s * Real.log x)) (Real.log x)]
    rw [← mul_comm (Real.log x) s]
  · filter_upwards with p
    rw [rpow_def_of_pos hx]
    congr 1
    ring

/-- Derivative (w.r.t. the real parameter `s`) of `x ^ (-(s + 1))`. -/
lemma hasDerivAt_neg_exponent (x : ℝ) (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fun p : ℝ => x ^ (-(p + 1)))
      (-(Real.log x) * x ^ (-(s + 1))) s := by
  have hd1 : HasDerivAt (fun p : ℝ => x ^ p) (Real.log x * x ^ (-(s + 1))) (-(s + 1)) :=
    hasDerivAt_rpow_exp x hx (-(s + 1))
  have hd2 : HasDerivAt (fun p : ℝ => -(p + 1)) (-1) s := by
    have h1 : HasDerivAt (fun p : ℝ => p + 1) 1 s := by
      simpa using (hasDerivAt_id s).add_const 1
    exact h1.neg
  have hc : HasDerivAt (fun p : ℝ => x ^ (-(p + 1)))
      ((Real.log x * x ^ (-(s + 1))) * (-1)) s :=
    hd1.comp s hd2
  refine (hc.congr_deriv ?_).congr_of_eventuallyEq ?_
  · ring
  · filter_upwards with p
    rfl

/-- Pointwise derivative of the `term` integrand w.r.t. `s`. -/
lemma hasDerivAt_term_integrand {n : ℕ} {x : ℝ} (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fun p : ℝ => (x - (n + 1 : ℕ) : ℝ) / x ^ (p + 1))
      (-(x - (n + 1 : ℕ) : ℝ) * Real.log x / x ^ (s + 1)) s := by
  have hdneg : HasDerivAt (fun p : ℝ => x ^ (-(p + 1)))
      (-(Real.log x) * x ^ (-(s + 1))) s :=
    hasDerivAt_neg_exponent x hx s
  have hconst : HasDerivAt (fun p : ℝ => (x - (n + 1 : ℕ) : ℝ)) 0 s :=
    hasDerivAt_const s _
  have hc : HasDerivAt (fun p : ℝ => (x - (n + 1 : ℕ) : ℝ) * x ^ (-(p + 1)))
      (0 * x ^ (-(s + 1)) + (x - (n + 1 : ℕ) : ℝ) * (-(Real.log x) * x ^ (-(s + 1)))) s :=
    hconst.mul hdneg
  refine (hc.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [div_eq_mul_inv, ← rpow_neg (le_of_lt hx)]
    ring
  · filter_upwards with p
    rw [div_eq_mul_inv, ← rpow_neg (le_of_lt hx)]

end ZetaAsymptotics

end
