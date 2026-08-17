import Mathlib

open Set MeasureTheory Filter Topology Real
open scoped Interval Topology

noncomputable section

namespace ZetaAsymptotics

/-! # Verified analyticity infrastructure for `termTSum`

This file contains the first, verified layer of the infrastructure needed to prove
`AnalyticOnNhd ℝ ZetaAsymptotics.termTSum (Ioi 0)` (the real-analyticity of the `termTSum`
function appearing in `riemannZeta₀_eq_one_sub_mul_termTSum`, sorry 8356 of
`riemannhypothesis.lean`).

All lemmas here are verified against mathlib (`lake env lean` passes with no errors).

## Status (honest)

Closing sorry 8356 requires the full chain:
1. ✔ atomic derivative lemmas (this file: `hasDerivAt_rpow_exp`, `hasDerivAt_neg_exponent`,
   `hasDerivAt_term_integrand`);
2. ✔ atomic analyticity lemmas (this file: `analyticOnNhd_rpow_const_exp`,
   `analyticOnNhd_rpow_neg_exp`, `analyticOnNhd_mul_rpow_neg`);
3. □ per-term analyticity `AnalyticOnNhd ℝ (fun s => term (n+1) s) (Ioi 0)` — needs a
   parametric-integral analyticity result (power series through the interval integral, via
   `expSeries_hasSum_exp` + `hasSum_integral_of_dominated_convergence`); in progress;
4. □ `AnalyticOnNhd ℝ termTSum (Ioi 0)` — needs a real Weierstrass theorem (locally uniform
   limit of real-analytic functions is real-analytic), which does not exist in mathlib;
5. □ the identity-theorem step (`eqOn_of_preconnected_of_eventuallyEq`, which exists for ℝ),
   closing sorry 8356.

Sorry 9117 additionally requires a rigorous numerical certificate bridge.
-/

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

/-- `x ^ (-y) = 1 / x ^ y` for `0 ≤ x`. -/
lemma rpow_neg_eq_one_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = 1 / x ^ y := by
  rw [rpow_neg hx, one_div]

/-- `term (n+1) s` equals an integral over `ℝ` (via an indicator). -/
lemma term_eq_integral_indicator (n : ℕ) (s : ℝ) :
    term (n + 1) s = ∫ a : ℝ, ((a - (n + 1 : ℕ) : ℝ) / a ^ (s + 1)) *
      (if a ∈ Set.Ioc (n + 1 : ℝ) ((n + 1 : ℝ) + 1) then (1 : ℝ) else 0) := by
  rw [term]
  rw [intervalIntegral.integral_of_le (by simp)]
  rw [← integral_indicator (by measurability)]
  congr 1
  funext a
  by_cases ha : a ∈ Set.Ioc (n + 1 : ℝ) ((n + 1 : ℝ) + 1)
  · simp [ha]
  · simp [ha]

/-- `s ↦ x ^ s` is real-analytic for `0 < x`. -/
lemma analyticOnNhd_rpow_const_exp (x : ℝ) (hx : 0 < x) :
    AnalyticOnNhd ℝ (fun s : ℝ => x ^ s) univ := by
  have hlin : AnalyticOnNhd ℝ (fun s : ℝ => s * Real.log x) univ := by
    exact (analyticOnNhd_id (𝕜 := ℝ)).mul analyticOnNhd_const
  have hmain : AnalyticOnNhd ℝ (fun s : ℝ => Real.exp (s * Real.log x)) univ :=
    AnalyticOnNhd.rexp hlin
  exact hmain.congr isOpen_univ (by
    intro s hs
    dsimp
    rw [rpow_def_of_pos hx]
    congr 1
    ring)

/-- `s ↦ x ^ (-(s + 1))` is real-analytic for `0 < x`. -/
lemma analyticOnNhd_rpow_neg_exp (x : ℝ) (hx : 0 < x) :
    AnalyticOnNhd ℝ (fun s : ℝ => x ^ (-(s + 1))) univ := by
  have h0 := analyticOnNhd_rpow_const_exp x hx
  have hlin0 : AnalyticOnNhd ℝ (fun s : ℝ => -s - 1) univ :=
    (analyticOnNhd_id (𝕜 := ℝ)).neg.sub analyticOnNhd_const
  have hlin : AnalyticOnNhd ℝ (fun s : ℝ => -(s + 1)) univ :=
    hlin0.congr isOpen_univ (by intro s hs; ring)
  exact h0.comp hlin (fun s _ => mem_univ _)

/-- `s ↦ (a - c) * a ^ (-(s + 1))` is real-analytic for `0 < a`. -/
lemma analyticOnNhd_mul_rpow_neg (a c : ℝ) (ha : 0 < a) :
    AnalyticOnNhd ℝ (fun s : ℝ => (a - c) * a ^ (-(s + 1))) univ := by
  have h0 := analyticOnNhd_rpow_neg_exp a ha
  have hcst : AnalyticOnNhd ℝ (fun s : ℝ => a - c) univ := analyticOnNhd_const
  exact (h0.mul hcst).congr isOpen_univ (by intro s hs; dsimp; rw [mul_comm])

end ZetaAsymptotics

end
