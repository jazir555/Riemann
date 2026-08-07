import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option maxHeartbeats 400000

/-!
# Infrastructure for the Kadiri zero-free region proof

Support file for `ZeroFreeRegionProof.lean`, built up incrementally.  The target is

`ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ 1 - c / log (|Im s| + 10)`, `c = 1/57.54`.

## Roadmap

The classical (de la Vallée Poussin / Kadiri) route needs the following blocks.

* **[done]** `ζ ↔ ζ₁` dictionary (`riemannZeta_eq_zero_iff_riemannZeta₁_eq_zero`, ...).
* **[done]** Two-sided real-axis bounds `1/(σ-1) ≤ ζ(σ) ≤ 1 + 1/(σ-1)` for `σ > 1`
  (`norm_riemannZeta_ofReal_le`, `one_div_sub_one_le_riemannZeta_ofReal`), plus
  `‖ζ(1+x)‖ ≤ 2/x` and `ζ₁(σ) = (σ-1)ζ(σ) ≥ 1`.
* **[done]** 3-4-1 in logarithmic-derivative form
  (`three_four_one_neg_logDeriv_riemannZeta`), from `-ζ'/ζ(s) = ∑ Λ(n) n^{-s}`.
* **[done]** Real-axis log-derivative bound `-ζ'/ζ(σ) ≤ 1/θ + 1/((1-θ)(σ-1))` for any
  `0 < θ < 1` (`neg_logDeriv_riemannZeta_ofReal_le`).  The leading coefficient matters:
  the optimisation below produces a positive constant **only when it is `< 4/3`**, so the
  cheap Chebyshev bound `ψ(x) ≤ x log 4` (coefficient `log 4 ≈ 1.386`) would *not* suffice;
  here `θ = 1/8` gives `8 + (8/7)/(σ-1)`.
* **[done]** Complex log-derivative bound on `Re s > 1`: the von Mangoldt Dirichlet series
  gives `Re(-ζ'/ζ(s)) ≤ ‖L(Λ, s)‖ ≤ (L(Λ, Re s)).re = -ζ'/ζ(Re s)`, so the real-axis bound
  transfers directly (`abs_LSeries_vonMangoldt_le`, `re_neg_logDeriv_riemannZeta_le`,
  `re_neg_logDeriv_riemannZeta_ofReal_le'`).  **Consequently the approximate functional equation
  and the `O(log(t))` strip-growth bound are NOT needed** for the 3-4-1 evaluation at the points
  `σ + k iγ` with `σ > 1` — the Dirichlet series already dominates termwise by the real series.
  (For completeness mathlib *does* have the exact functional equation
  `riemannZeta (1 - s) = 2·(2π)^(-s)·Γ(s)·cos(πs/2)·riemannZeta s`
  at `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:179`, but it is not needed here.)
* **[done]** Zero-sum helper lemmas: `Re(1/z) ≥ 0` for `Re z ≥ 0` and
  `Re(1/z) ≤ 1/Re z` for `Re z > 0` (`re_inv_nonneg_of_re_nonneg`, `re_inv_le_inv_of_re_pos`,
  plus the `s-ρ` corollaries `re_inv_sub_nonneg_of_re_ge`, `re_inv_sub_le_of_re_pos`).  These
  bound each term `Re(1/(s-ρ)) ≥ 0` (so all zeros but one can be dropped from the zero-sum) and
  `Re(1/(s-ρ)) ≤ 1/(Re s - Re ρ)`.
* **[done]** The zero-sum edge in *parameterised* form (`ZeroFreeEdge`, `zeroFreeEdge_from_factorization`):
  assuming the product decomposition `-ζ'/ζ(s) = analytic s - Σ_ρ (1/(s-ρ) + 1/ρ)` and an
  explicit `O(log|t|)` bound on the 3-4-1 of the analytic part, the 3-4-1 inequality plus the
  zero-sum bounds above give `σ - Re ρ₀ ≥ 4 / (A₀/(σ-1) + A₁·log(|t|+2) + A₂)` for the borderline
  zero `ρ₀` at ordinate `t`.  This is exactly the shape needed; substituting `σ = 1 + a/log t` and
  optimising `a` yields `1 - Re ρ₀ ≥ c/log t`.
* **[todo]** The product decomposition itself, i.e. `-ζ'/ζ(s) = 1/(s-1) + const + Σ_ρ (1/(s-ρ) + 1/ρ)`.
  This needs the **Hadamard factorisation** of the completed zeta function `completedRiemannZeta₀`;
  mathlib currently has *no* Hadamard factorisation theorem (only the three-line theorem in
  `Complex.Hadamard` and the Weierstrass product machinery in `Complex.Weierstrass`), and *no*
  order-of-entire-function theory or `Γ` asymptotics to bound the order of `ξ`.  This is the keystone
  and is a substantial separate contribution to mathlib.
* **[todo]** The numerical optimisation: with `σ = 1 + a/log t` the edge bound gives
  `1 - Re ρ₀ ≥ c/log t`; then check `c ≥ 1/57.54` (and merge with the real-axis / log-derivative
  bounds already proved).

Note on the current skeleton in `ZeroFreeRegionProof.lean`: bounding `ζ₁` by a *Lipschitz*
estimate (mean value inequality with an abstract `sSup` derivative bound) can only produce a
non-explicit, `t`-dependent gap; even a fully explicit Lipschitz/Schwarz argument yields a
region of shape `1 - c / log² |t|`.  Reaching `1 - c / log |t|` requires the log-derivative
route above.

Everything in this file is `sorry`-free.
-/

open Complex Real Topology Asymptotics
open scoped BigOperators

noncomputable section

@[inherit_doc] local notation "γ" => Real.eulerMascheroniConstant

namespace ZeroFreeRegion

/-!
## Conversion between `ζ` and `ζ₁`
-/

/-- For `s ≠ 1`, `ζ(s) = (s-1)⁻¹ · ζ₁(s)`, so `ζ(s) = 0 ↔ ζ₁(s) = 0`. -/
theorem riemannZeta_eq_zero_iff_riemannZeta₁_eq_zero {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = 0 ↔ riemannZeta₁ s = 0 := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (inv_ne_zero (sub_ne_zero.mpr hs))
    · exact h
  · exact fun h => Or.inr h

/-- `‖ζ(s)‖ = ‖ζ₁(s)‖ / ‖s-1‖` for `s ≠ 1`. -/
theorem norm_riemannZeta_eq_div_norm_riemannZeta₁ {s : ℂ} (hs : s ≠ 1) :
    ‖riemannZeta s‖ = ‖riemannZeta₁ s‖ / ‖s - 1‖ := by
  rw [riemannZeta_eq_inv_sub_mul hs, norm_mul, norm_inv, div_eq_inv_mul]

/-- `‖ζ(s)‖ ≠ 0 ↔ ζ₁(s) ≠ 0` for `s ≠ 1`. -/
theorem norm_riemannZeta_ne_zero_iff {s : ℂ} (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≠ 0 ↔ riemannZeta₁ s ≠ 0 := by
  simp only [ne_eq, norm_eq_zero, riemannZeta_eq_zero_iff_riemannZeta₁_eq_zero hs]

/-!
## `ζ` on the real axis

The 3-4-1 argument is fed with two-sided bounds for `ζ` at the real point `σ`:
the upper bound `ζ(σ) ≤ 1 + 1/(σ-1)` and the lower bound `ζ(σ) ≥ 1/(σ-1)`, both from the
integral test applied to `∑ n^{-σ}`.  The lower bound is what allows dividing by `ζ(σ)` in
the logarithmic derivative estimate; it also gives `ζ₁(σ) = (σ-1)ζ(σ) ≥ 1`.
-/

section RealAxis

open MeasureTheory Set

variable {σ : ℝ}

private theorem antitoneOn_rpow_neg (hσ : 1 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici ((1 : ℕ) : ℝ)) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one (by exact_mod_cast ha)
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  simp only [Real.rpow_neg ha0.le, Real.rpow_neg hb0.le]
  gcongr

private theorem integrableOn_rpow_neg (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi ((1 : ℕ) : ℝ)) := by
  simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (c := 1) zero_lt_one

private theorem nonneg_rpow_neg : ∀ t ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ t ^ (-σ) := fun t ht =>
  (Real.rpow_pos_of_pos (lt_trans (by norm_num) ht) _).le

private theorem integral_Ioi_one_rpow_neg (hσ : 1 < σ) :
    ∫ x in Ioi ((1 : ℕ) : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
  rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one, Real.one_rpow]
  rw [div_eq_div_iff (by linarith) (by linarith)]
  ring

/-- **Integral test for the `p`-series** (upper bound).  For `σ > 1`,
`∑' n : ℕ, n^{-σ} ≤ 1 + 1/(σ-1)`.

The `n = 0` term is `0` by the `rpow` convention, the `n = 1` term is `1`, and the
remaining terms are dominated by `∫_1^∞ x^{-σ} dx = 1/(σ-1)`. -/
theorem tsum_nat_rpow_neg_le (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσne : -σ ≠ 0 := ne_of_lt (by linarith)
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    summable_nat_rpow.mpr (by linarith : -σ < -1)
  have hcomp := AntitoneOn.tsum_comp_add_le_integral 1 (antitoneOn_rpow_neg hσ)
    (integrableOn_rpow_neg hσ) nonneg_rpow_neg
  rw [integral_Ioi_one_rpow_neg hσ] at hcomp
  have hsplit := hsummable.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, ((i : ℕ) : ℝ) ^ (-σ) = 1 := by
    simp [Finset.sum_range_succ, Real.zero_rpow hσne, Real.one_rpow]
  have htail : ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-σ) ≤ 1 / (σ - 1) := by
    simpa [Nat.add_assoc] using hcomp
  rw [← hsplit, hhead]
  linarith

/-- **Integral test for the `p`-series** (lower bound).  For `σ > 1`,
`1/(σ-1) = ∫_1^∞ x^{-σ} dx ≤ ∑' n : ℕ, n^{-σ}`. -/
theorem le_tsum_nat_rpow_neg (hσ : 1 < σ) :
    1 / (σ - 1) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  have hσne : -σ ≠ 0 := ne_of_lt (by linarith)
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    summable_nat_rpow.mpr (by linarith : -σ < -1)
  have hcomp := AntitoneOn.integral_le_tsum_comp_add 1 (antitoneOn_rpow_neg hσ)
    hsummable nonneg_rpow_neg
  rw [integral_Ioi_one_rpow_neg hσ] at hcomp
  have hsplit := hsummable.sum_add_tsum_nat_add 1
  have hhead : ∑ i ∈ Finset.range 1, ((i : ℕ) : ℝ) ^ (-σ) = 0 := by
    simp [Real.zero_rpow hσne]
  rw [← hsplit, hhead, zero_add]
  exact hcomp

/-- For real `σ > 1`, `ζ(σ)` is the real number `∑' n, n^{-σ}`. -/
theorem riemannZeta_ofReal_eq_ofReal_tsum (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = ((∑' n : ℕ, (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hσne : -σ ≠ 0 := ne_of_lt (by linarith)
  rw [← LSeries_one_eq_riemannZeta hre, Complex.ofReal_tsum]
  simp only [LSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hσne]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', Pi.one_apply, Complex.ofReal_cpow hn0.le (-σ),
      Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg, one_div]

/-- `‖ζ(σ)‖ = ∑' n, n^{-σ}` for real `σ > 1`. -/
theorem norm_riemannZeta_ofReal (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  rw [riemannZeta_ofReal_eq_ofReal_tsum hσ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- Upper bound for `ζ` on the real axis: `‖ζ(σ)‖ ≤ 1 + 1/(σ-1)` for real `σ > 1`. -/
theorem norm_riemannZeta_ofReal_le (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  rw [norm_riemannZeta_ofReal hσ]; exact tsum_nat_rpow_neg_le hσ

/-- Lower bound for `ζ` on the real axis: `1/(σ-1) ≤ ζ(σ)` for real `σ > 1`. -/
theorem one_div_sub_one_le_riemannZeta_ofReal (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  rw [riemannZeta_ofReal_eq_ofReal_tsum hσ, Complex.ofReal_re]
  exact le_tsum_nat_rpow_neg hσ

/-- `ζ(σ) > 0` for real `σ > 1`. -/
theorem riemannZeta_ofReal_re_pos (hσ : 1 < σ) : 0 < (riemannZeta (σ : ℂ)).re :=
  lt_of_lt_of_le (div_pos zero_lt_one (by linarith)) (one_div_sub_one_le_riemannZeta_ofReal hσ)

/-- `ζ₁(σ) = (σ-1)·ζ(σ)` for real `σ > 1`. -/
theorem riemannZeta₁_ofReal_eq (hσ : 1 < σ) :
    riemannZeta₁ (σ : ℂ) = ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) := by
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have : σ = 1 := by exact_mod_cast h
    linarith
  rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]

/-- The normalisation `ζ₁(σ) = (σ-1)ζ(σ) ≥ 1` on the real axis, `σ > 1`.
This is the lower bound that keeps `ζ₁` away from `0`, so that `ζ₁'/ζ₁` can be estimated. -/
theorem one_le_riemannZeta₁_ofReal_re (hσ : 1 < σ) : 1 ≤ (riemannZeta₁ (σ : ℂ)).re := by
  have hpos : 0 < σ - 1 := by linarith
  have hcast : ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [riemannZeta₁_ofReal_eq hσ, hcast, Complex.re_ofReal_mul]
  calc (1 : ℝ) = (σ - 1) * (1 / (σ - 1)) := by field_simp
    _ ≤ (σ - 1) * (riemannZeta (σ : ℂ)).re := by
        gcongr
        exact one_div_sub_one_le_riemannZeta_ofReal hσ

/-- Consequently `‖ζ₁(σ)‖ ≥ 1` for real `σ > 1`. -/
theorem one_le_norm_riemannZeta₁_ofReal (hσ : 1 < σ) : 1 ≤ ‖riemannZeta₁ (σ : ℂ)‖ :=
  le_trans (one_le_riemannZeta₁_ofReal_re hσ) (Complex.re_le_norm _)

/-- The form of the real-axis bound used by the 3-4-1 argument:
for `0 < x ≤ 1` we have `‖ζ(1+x)‖ ≤ 2/x`. -/
theorem norm_riemannZeta_one_add_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖riemannZeta ((1 + x : ℝ) : ℂ)‖ ≤ 2 / x := by
  have h := norm_riemannZeta_ofReal_le (σ := 1 + x) (by linarith)
  rw [show (1 : ℝ) + x - 1 = x from by ring] at h
  have hdiff : 2 / x - (1 + 1 / x) = (1 - x) / x := by field_simp; ring
  have hnn : 0 ≤ (1 - x) / x := div_nonneg (by linarith) hx0.le
  linarith

end RealAxis

/-!
## The 3-4-1 inequality for the logarithmic derivative

Mathlib provides the 3-4-1 inequality in *product* form
(`DirichletCharacter.norm_LFunction_product_ge_one`).  The zero-free region argument needs the
*logarithmic derivative* form, which is what makes the constant come out proportional to
`1/log |t|` rather than `1/log² |t|`.  It comes from `-ζ'/ζ(s) = ∑ Λ(n) n^{-s}` together with
`3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`.
-/

section ThreeFourOne

open ArithmeticFunction hiding log
open scoped LSeries.notation

/-- Termwise 3-4-1 positivity for the von Mangoldt series: for `n ≠ 0` the combination
`3·Re term(σ) + 4·Re term(σ + iu) + Re term(σ + 2iu)` equals
`2 Λ(n) n^{-σ} (1 + cos(u log n))² ≥ 0`. -/
theorem re_term_vonMangoldt_comb_nonneg {n : ℕ} (hn : n ≠ 0) (σ u : ℝ) :
    0 ≤ 3 * (LSeries.term ↗Λ (σ : ℂ) n).re
      + 4 * (LSeries.term ↗Λ ((σ : ℂ) + u * I) n).re
      + (LSeries.term ↗Λ ((σ : ℂ) + 2 * u * I) n).re := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set a : ℝ := Λ n / (n : ℝ) ^ σ with ha
  have ha0 : 0 ≤ a := div_nonneg vonMangoldt_nonneg (Real.rpow_pos_of_pos hn0 σ).le
  set z : ℂ := (n : ℂ) ^ (-((u : ℂ) * I)) with hzdef
  have hz1 : ‖z‖ = 1 := by
    rw [hzdef, Complex.norm_natCast_cpow_of_pos hnpos]
    simp
  -- the `n`-th term at the real point `σ`
  have hbase : ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ ((σ : ℝ) : ℂ) = (a : ℂ) := by
    rw [ha, Complex.ofReal_div, Complex.ofReal_cpow hn0.le σ, Complex.ofReal_natCast]
  have e0 : LSeries.term ↗Λ (σ : ℂ) n = (a : ℂ) := by
    rw [LSeries.term_of_ne_zero hn]; exact hbase
  have e1 : LSeries.term ↗Λ ((σ : ℂ) + u * I) n = (a : ℂ) * z := by
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC, div_mul_eq_div_div,
      div_eq_mul_inv, hbase, hzdef, Complex.cpow_neg]
  have e2 : LSeries.term ↗Λ ((σ : ℂ) + 2 * u * I) n = (a : ℂ) * z ^ 2 := by
    have h2 : (2 : ℂ) * u * I = ((2 : ℕ) : ℂ) * ((u : ℂ) * I) := by push_cast; ring
    rw [LSeries.term_of_ne_zero hn, h2, Complex.cpow_add _ _ hnC, Complex.cpow_nat_mul,
      div_mul_eq_div_div, div_eq_mul_inv, hbase, hzdef, Complex.cpow_neg, inv_pow]
  rw [e0, e1, e2, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  -- `3 + 4c + (2c² - 1) = 2(1 + c)²` where `c = Re z` and `|z| = 1`
  have hsq : z.re * z.re + z.im * z.im = 1 := by
    have h := congrArg (· ^ 2) hz1
    simpa [Complex.sq_norm, Complex.normSq_apply] using h
  have hz2 : (z ^ 2).re = z.re * z.re - z.im * z.im := by rw [pow_two, Complex.mul_re]
  rw [hz2]
  nlinarith [sq_nonneg (z.re + 1), ha0, hsq]

/-- **3-4-1 inequality, logarithmic derivative form** (von Mangoldt series version).
For real `σ > 1` and real `u`,
`3 Re L(Λ, σ) + 4 Re L(Λ, σ + iu) + Re L(Λ, σ + 2iu) ≥ 0`. -/
theorem three_four_one_re_LSeries_vonMangoldt {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    0 ≤ 3 * (LSeries ↗Λ (σ : ℂ)).re + 4 * (LSeries ↗Λ ((σ : ℂ) + u * I)).re
        + (LSeries ↗Λ ((σ : ℂ) + 2 * u * I)).re := by
  have h₀ : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h₁ : 1 < ((σ : ℂ) + u * I).re := by simpa using hσ
  have h₂ : 1 < ((σ : ℂ) + 2 * u * I).re := by simpa using hσ
  have H₀ := LSeriesSummable_vonMangoldt h₀
  have H₁ := LSeriesSummable_vonMangoldt h₁
  have H₂ := LSeriesSummable_vonMangoldt h₂
  have hs₀ := (Complex.hasSum_re H₀.hasSum).summable.mul_left 3
  have hs₁ := (Complex.hasSum_re H₁.hasSum).summable.mul_left 4
  have hs₂ := (Complex.hasSum_re H₂.hasSum).summable
  simp only [LSeries]
  rw [Complex.re_tsum H₀, Complex.re_tsum H₁, Complex.re_tsum H₂,
    ← tsum_mul_left, ← tsum_mul_left, ← hs₀.tsum_add hs₁, ← (hs₀.add hs₁).tsum_add hs₂]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact re_term_vonMangoldt_comb_nonneg hn σ u

/-- **3-4-1 inequality, logarithmic derivative form** for `ζ`.
For real `σ > 1` and real `u`,
`3·Re(-ζ'/ζ)(σ) + 4·Re(-ζ'/ζ)(σ + iu) + Re(-ζ'/ζ)(σ + 2iu) ≥ 0`. -/
theorem three_four_one_neg_logDeriv_riemannZeta {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + u * I) / riemannZeta ((σ : ℂ) + u * I)).re
      + (-deriv riemannZeta ((σ : ℂ) + 2 * u * I) / riemannZeta ((σ : ℂ) + 2 * u * I)).re := by
  have h₀ : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h₁ : 1 < ((σ : ℂ) + u * I).re := by simpa using hσ
  have h₂ : 1 < ((σ : ℂ) + 2 * u * I).re := by simpa using hσ
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h₀,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h₁,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h₂]
  exact three_four_one_re_LSeries_vonMangoldt hσ u

end ThreeFourOne

/-!
## The real-axis bound for `-ζ'/ζ`

For `σ > 1` and `0 < θ < 1` we prove `-ζ'/ζ(σ) ≤ 1/θ + 1/((1-θ)(σ-1))`.

The leading coefficient `1/(1-θ)` can be made as close to `1` as desired, which is essential:
the final optimisation only yields a positive constant when that coefficient is `< 4/3`.

The proof is elementary.  Termwise, `h · log n ≤ n^h - 1` (i.e. `1 + u ≤ e^u`), so
`∑ log n · n^{-σ} ≤ (ζ(σ-h) - ζ(σ))/h`; then divide by `ζ(σ) ≥ 1/(σ-1)` and take `h = θ(σ-1)`.
-/

section LogDerivRealAxis

open ArithmeticFunction hiding log
open scoped LSeries.notation

variable {σ : ℝ}

/-- `-ζ'(σ) = ∑' n, log n · n^{-σ}` for real `σ > 1`. -/
theorem neg_deriv_riemannZeta_ofReal (hσ : 1 < σ) :
    -deriv riemannZeta (σ : ℂ) = ((∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hσne : -σ ≠ 0 := ne_of_lt (by linarith)
  have habs : LSeries.abscissaOfAbsConv 1 < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hre
  have hderiv : deriv (LSeries 1) (σ : ℂ) = deriv riemannZeta (σ : ℂ) :=
    Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hre,
        fun _ hz => LSeries_one_eq_riemannZeta hz⟩
  rw [← hderiv, LSeries_deriv habs, neg_neg, Complex.ofReal_tsum]
  simp only [LSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hσne]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.logMul, Pi.one_apply, mul_one,
      ← Complex.natCast_log, Complex.ofReal_mul, Complex.ofReal_cpow hn0.le (-σ),
      Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]

/-- Chord bound coming from `1 + u ≤ e^u`: for `0 < h` with `σ - h > 1`,
`∑' n, log n · n^{-σ} ≤ (∑' n, n^{-(σ-h)} - ∑' n, n^{-σ}) / h`. -/
theorem tsum_log_mul_rpow_neg_le {h : ℝ} (hh : 0 < h) (hσh : 1 < σ - h) :
    ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ)
      ≤ (∑' n : ℕ, (n : ℝ) ^ (-(σ - h)) - ∑' n : ℕ, (n : ℝ) ^ (-σ)) / h := by
  have hσne : -σ ≠ 0 := ne_of_lt (by linarith)
  have hσhne : -(σ - h) ≠ 0 := ne_of_lt (by linarith)
  have hsum₁ : Summable (fun n : ℕ => (n : ℝ) ^ (-(σ - h))) :=
    summable_nat_rpow.mpr (by linarith)
  have hsum₂ : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := summable_nat_rpow.mpr (by linarith)
  -- termwise bound
  have hterm : ∀ n : ℕ, Real.log n * (n : ℝ) ^ (-σ)
      ≤ ((n : ℝ) ^ (-(σ - h)) - (n : ℝ) ^ (-σ)) / h := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow hσne
      have h2 : (0 : ℝ) ^ (h - σ) = 0 := Real.zero_rpow (ne_of_lt (by linarith : h - σ < 0))
      simp [h1, h2]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hsplit : (n : ℝ) ^ (-(σ - h)) = (n : ℝ) ^ (-σ) * (n : ℝ) ^ h := by
        rw [← Real.rpow_add hn0]; ring_nf
      have hexp : h * Real.log n + 1 ≤ (n : ℝ) ^ h := by
        rw [Real.rpow_def_of_pos hn0]
        have := Real.add_one_le_exp (h * Real.log n)
        rwa [mul_comm (Real.log n) h]
      have hpow : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
      rw [hsplit, le_div_iff₀ hh]
      nlinarith [hpow, hexp]
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.log n * (n : ℝ) ^ (-σ) := fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsumRHS : Summable (fun n : ℕ => ((n : ℝ) ^ (-(σ - h)) - (n : ℝ) ^ (-σ)) / h) :=
    ((hsum₁.sub hsum₂).div_const h)
  have hsumLHS : Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-σ)) :=
    hsumRHS.of_nonneg_of_le hnonneg hterm
  calc ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ)
      ≤ ∑' n : ℕ, ((n : ℝ) ^ (-(σ - h)) - (n : ℝ) ^ (-σ)) / h :=
        hsumLHS.tsum_le_tsum hterm hsumRHS
    _ = (∑' n : ℕ, (n : ℝ) ^ (-(σ - h)) - ∑' n : ℕ, (n : ℝ) ^ (-σ)) / h := by
        rw [tsum_div_const, hsum₁.tsum_sub hsum₂]

/-- The elementary algebra behind the real-axis logarithmic derivative bound:
if `N ≤ (Z₁ - Z)/(θ d)` with `Z ≥ 1/d` and `Z₁ ≤ 1 + 1/((1-θ)d)`, then
`N / Z ≤ 1/θ + 1/((1-θ)d)`. -/
private theorem logDeriv_algebra {N Z Z₁ d θ : ℝ}
    (hd0 : 0 < d) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hN0 : 0 ≤ N) (hZlow : 1 / d ≤ Z)
    (hZ₁up : Z₁ ≤ 1 + 1 / ((1 - θ) * d))
    (hNup : N ≤ (Z₁ - Z) / (θ * d)) :
    N / Z ≤ 1 / θ + 1 / ((1 - θ) * d) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hθd : 0 < θ * d := mul_pos hθ0 hd0
  have hZpos : 0 < Z := lt_of_lt_of_le (div_pos zero_lt_one hd0) hZlow
  have hNc : N * (θ * d) ≤ Z₁ - Z := (le_div_iff₀ hθd).mp hNup
  have key : 1 + 1 / ((1 - θ) * d) - 1 / d = 1 + θ / ((1 - θ) * d) := by
    field_simp
    ring
  have hNc2 : N * (θ * d) ≤ 1 + θ / ((1 - θ) * d) := by linarith
  have hNd : N * d ≤ 1 / θ + 1 / ((1 - θ) * d) := by
    rw [show (1 : ℝ) / θ + 1 / ((1 - θ) * d) = (1 + θ / ((1 - θ) * d)) / θ from by
      field_simp]
    rw [le_div_iff₀ hθ0]
    calc N * d * θ = N * (θ * d) := by ring
      _ ≤ 1 + θ / ((1 - θ) * d) := hNc2
  have hZinv : 1 / Z ≤ d := by
    rw [div_le_iff₀ hZpos]
    have h2 := mul_le_mul_of_nonneg_left hZlow hd0.le
    have h1 : d * (1 / d) = 1 := by field_simp
    linarith
  calc N / Z = N * (1 / Z) := by rw [div_eq_mul_one_div]
    _ ≤ N * d := mul_le_mul_of_nonneg_left hZinv hN0
    _ ≤ 1 / θ + 1 / ((1 - θ) * d) := hNd

/-- **Real-axis bound for the logarithmic derivative of `ζ`.**
For `σ > 1` and `0 < θ < 1`,
`-ζ'/ζ(σ) ≤ 1/θ + 1/((1-θ)(σ-1))`.

Taking `θ` small makes the coefficient of `1/(σ-1)` as close to `1` as needed; the final
optimisation requires that coefficient to be `< 4/3`, e.g. `θ = 1/8` gives `8 + (8/7)/(σ-1)`. -/
theorem neg_logDeriv_riemannZeta_ofReal_le (hσ : 1 < σ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (LSeries ↗Λ (σ : ℂ)).re ≤ 1 / θ + 1 / ((1 - θ) * (σ - 1)) := by
  have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hd0 : 0 < σ - 1 := by linarith
  have hθd : 0 < θ * (σ - 1) := mul_pos hθ0 hd0
  have hσc : 1 < σ - θ * (σ - 1) := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 - θ by linarith) hd0]
  have hN0 : 0 ≤ ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ) := tsum_nonneg fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hZlow : 1 / (σ - 1) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := le_tsum_nat_rpow_neg hσ
  have hZ₁up : ∑' n : ℕ, (n : ℝ) ^ (-(σ - θ * (σ - 1))) ≤ 1 + 1 / ((1 - θ) * (σ - 1)) := by
    have h := tsum_nat_rpow_neg_le hσc
    rwa [show σ - θ * (σ - 1) - 1 = (1 - θ) * (σ - 1) from by ring] at h
  have hNup := tsum_log_mul_rpow_neg_le hθd hσc
  have hLS : (LSeries ↗Λ (σ : ℂ)).re
      = (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ)) / (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, neg_deriv_riemannZeta_ofReal hσ,
      riemannZeta_ofReal_eq_ofReal_tsum hσ, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hLS]
  exact logDeriv_algebra hd0 hθ0 hθ1 hN0 hZlow hZ₁up hNup

end LogDerivRealAxis

/-!
## The log-derivative bound on the half-plane `Re s > 1`

For `Re s > 1` the von Mangoldt series `-ζ'/ζ(s) = L(Λ, s) = ∑ Λ(n) n^{-s}` converges
(absolutely), so its modulus is dominated termwise by the *real* series `L(Λ, Re s)`:
`|L(Λ, s)| ≤ L(Λ, Re s)`.  Hence `Re(-ζ'/ζ(s)) ≤ |−ζ'/ζ(s)| ≤ -ζ'/ζ(Re s)`, and the
real-axis bound from the previous section applies.  This gives the complex log-derivative
bound needed to evaluate the 3-4-1 inequality at the points `σ + k iγ` with `σ > 1`, *without*
any approximate functional equation or strip-growth estimate.
-/

section LogDerivComplex

open ArithmeticFunction hiding log
open scoped LSeries.notation
open scoped ComplexOrder

/-- For `1 < Re s`, the modulus of the von Mangoldt series at `s` is bounded by its value at
the real point `Re s`: `‖L(Λ, s)‖ ≤ (L(Λ, Re s)).re`.  The latter is a positive real number. -/
theorem abs_LSeries_vonMangoldt_le {s : ℂ} (h : 1 < s.re) :
    ‖LSeries ↗Λ s‖ ≤ (LSeries ↗Λ (s.re : ℂ)).re := by
  have hσ : 1 < ((s.re : ℂ)).re := by simpa using h
  have Hs := LSeriesSummable_vonMangoldt h
  have Hσ := LSeriesSummable_vonMangoldt hσ
  have hterm_nonneg : ∀ n, 0 ≤ LSeries.term ↗Λ (s.re : ℂ) n :=
    fun n => LSeries.term_nonneg (zero_le_real.mpr vonMangoldt_nonneg) (s.re : ℝ)
  have hterm_norm_re : ∀ n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ = (LSeries.term ↗Λ (s.re : ℂ) n).re := by
    intro n
    rw [eq_coe_norm_of_nonneg (hterm_nonneg n)]
    simp
  have hL_re : (LSeries ↗Λ (s.re : ℂ)).re = ∑' n, (LSeries.term ↗Λ (s.re : ℂ) n).re :=
    (congrArg Complex.re Hσ.hasSum.tsum_eq).trans (Complex.re_tsum Hσ)
  calc ‖LSeries ↗Λ s‖ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm Hs.norm
    _ = ∑' n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ := tsum_congr fun n => by simp [LSeries.norm_term_eq]
    _ = ∑' n, (LSeries.term ↗Λ (s.re : ℂ) n).re := tsum_congr hterm_norm_re
    _ = (LSeries ↗Λ (s.re : ℂ)).re := hL_re.symm

/-- For `1 < Re s`, `Re(-ζ'/ζ(s)) ≤ -ζ'/ζ(Re s)`, i.e. the real-part of the complex
log-derivative is bounded by the real-axis log-derivative. -/
theorem re_neg_logDeriv_riemannZeta_le {s : ℂ} (h : 1 < s.re) :
    (LSeries ↗Λ s).re ≤ (LSeries ↗Λ (s.re : ℂ)).re := by
  calc (LSeries ↗Λ s).re ≤ ‖LSeries ↗Λ s‖ := Complex.re_le_norm _
    _ ≤ (LSeries ↗Λ (s.re : ℂ)).re := abs_LSeries_vonMangoldt_le h

/-- **Complex log-derivative bound on `Re s > 1`.** For `1 < Re s` and `0 < θ < 1`,
`Re(-ζ'/ζ(s)) ≤ 1/θ + 1/((1-θ)(Re s - 1))`.

This is the estimate that feeds the 3-4-1 inequality at the points `s, s + 2iγ, s + 4iγ`
(with `Re s = σ > 1`); it is exactly the real-axis bound `neg_logDeriv_riemannZeta_ofReal_le`
transferred to the complex half-plane. -/
theorem re_neg_logDeriv_riemannZeta_ofReal_le' {s : ℂ} (h : 1 < s.re)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (LSeries ↗Λ s).re ≤ 1 / θ + 1 / ((1 - θ) * (s.re - 1)) := by
  calc (LSeries ↗Λ s).re ≤ (LSeries ↗Λ (s.re : ℂ)).re := re_neg_logDeriv_riemannZeta_le h
    _ ≤ 1 / θ + 1 / ((1 - θ) * (s.re - 1)) := neg_logDeriv_riemannZeta_ofReal_le
      (by simpa using h) hθ0 hθ1

end LogDerivComplex

/-!
## Zero-sum helper lemmas

These elementary complex-analysis estimates are what lets the zero-sum in the product form of
`-ζ'/ζ(s)` be controlled.  Once the Hadamard factorisation of the completed zeta function
`completedRiemannZeta₀` is available (it is **not** yet in mathlib), the logarithmic derivative
decomposes as `-ζ'/ζ(s) = analytic part + Σ_ρ (1/(s-ρ) + 1/ρ)`; the estimates below then bound
each `Re(1/(s-ρ))` term by `0` (when `Re s ≥ Re ρ`) and by `1/(Re s - Re ρ)` (when `Re s > Re ρ`).
-/

section ZeroSumHelpers

/-- For `0 ≤ Re z`, `Re(1/z) ≥ 0`.  Hence every term `Re((s-ρ)⁻¹)` is non-negative whenever
`Re s ≥ Re ρ`, which bounds the zero-sum below by the contribution of a single zero. -/
theorem re_inv_nonneg_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (1 / z).re := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [div_re, one_re, one_im]
    simp only [zero_mul, zero_div, add_zero, one_mul]
    exact div_nonneg hz (normSq_nonneg z)

/-- For `0 < Re z`, `Re(1/z) = Re z / |z|² ≤ 1 / Re z`.  So for a zero `ρ`,
`Re((s-ρ)⁻¹) ≤ 1/(Re s - Re ρ)` when `Re s > Re ρ`. -/
theorem re_inv_le_inv_of_re_pos {z : ℂ} (hz : 0 < z.re) : (1 / z).re ≤ 1 / z.re := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [div_re, one_re, one_im]
    simp only [zero_mul, zero_div, add_zero, one_mul]
    rw [le_div_iff₀ hz, div_mul_eq_mul_div, div_le_iff₀ (normSq_pos.mpr hz0)]
    rw [Complex.normSq_apply]
    nlinarith

/-- If `Re s ≥ Re ρ` then `Re((s - ρ)⁻¹) ≥ 0`. -/
theorem re_inv_sub_nonneg_of_re_ge {s ρ : ℂ} (h : s.re ≥ ρ.re) :
    0 ≤ (1 / (s - ρ)).re := re_inv_nonneg_of_re_nonneg (z := s - ρ) (by rw [sub_re]; linarith)

/-- If `Re s > Re ρ` then `Re((s - ρ)⁻¹) ≤ 1 / (Re s - Re ρ)`. -/
theorem re_inv_sub_le_of_re_pos {s ρ : ℂ} (h : ρ.re < s.re) :
    (1 / (s - ρ)).re ≤ 1 / (s.re - ρ.re) := re_inv_le_inv_of_re_pos (z := s - ρ) (by rw [sub_re]; linarith)

end ZeroSumHelpers

/-!
## The zero-free edge from the Hadamard factorisation (Route A)

This section isolates the gap left by the missing Hadamard factorisation of
`completedRiemannZeta₀` to a single, clearly-scoped hypothesis and carries the classical 3-4-1
zero-sum argument to its conclusion.  Assuming the product decomposition of `-ζ'/ζ(s)`
(equivalently `LSeries ↗Λ s`) into an *analytic part* and a finite sum over non-trivial zeros `ρ`,
the already-proved 3-4-1 inequality plus the zero-sum bounds above yield a lower bound on
`σ - Re ρ` for the borderline zero `ρ₀` at ordinate `γ`.  Everything here is elementary complex
analysis; the only unproved inputs are `h_decomp` (the product form) together with
`h_analytic` (the `O(log|γ|)` growth of the analytic part, i.e. the digamma estimate that mathlib
does not yet have).

Concretely we prove
`σ - Re ρ₀ ≥ 4 / (A₀/(σ-1) + A₁·log(|γ|+2) + A₂)`,
which is exactly the shape needed; substituting `σ = 1 + a/log(|γ|+10)` and optimising `a` gives
the final `1 - Re ρ₀ ≥ c/log|γ|` and hence the `1/57.54` constant.
-/

section ZeroFreeEdge

open ArithmeticFunction hiding log
open scoped LSeries.notation
open scoped ComplexOrder

/-! ### The borderline and the generic zero-term -/

/-- Borderline contribution of a single zero.  For `0 < d` and any `g`,
`3·Re(1/(d - g i)) + 4·Re(1/d) + Re(1/(d + g i)) ≥ 4/d`.
This is the 3-4-1 combination at a zero whose ordinate matches `g`, where the middle point makes
the imaginary part cancel. -/
theorem re_three_four_one_one_over_sub_borderline (d g : ℝ) (hd : 0 < d) :
    4 / d ≤ 3 * ((↑d - ↑g * I : ℂ)⁻¹).re + 4 * ((↑d : ℂ)⁻¹).re
      + ((↑d + ↑g * I : ℂ)⁻¹).re := by
  have h_mid : ((↑d : ℂ)⁻¹).re = 1 / d := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]
  have h_lo : ((↑d - ↑g * I : ℂ)⁻¹).re = d / (d ^ 2 + g ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  have h_hi : ((↑d + ↑g * I : ℂ)⁻¹).re = d / (d ^ 2 + g ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  rw [h_mid, h_lo, h_hi]
  have hpos : 0 ≤ d / (d ^ 2 + g ^ 2) := by positivity
  have h4 : 4 * (1 / d) = 4 / d := by ring
  linarith [hpos]

/-- Generic contribution of a non-borderline zero.  If `Re s > Re ρ` at the three points
`σ, σ+it, σ+2it` (i.e. `0 < σ - Re ρ`), then
`3·Re(1/(σ-ρ)) + 4·Re(1/(σ+it-ρ)) + Re(1/(σ+2it-ρ)) ≥ 0`. -/
theorem re_three_four_one_one_over_sub_nonneg {σ t : ℝ} (ρ : ℂ) (hd : 0 < σ - ρ.re) :
    0 ≤ 3 * ((1 : ℂ) / (σ - ρ)).re
      + 4 * ((1 : ℂ) / (σ + ↑t * I - ρ)).re
      + ((1 : ℂ) / (σ + 2 * ↑t * I - ρ)).re := by
  have h1 : 0 ≤ (↑σ - ρ).re := by simp; linarith
  have h2 : 0 ≤ (↑σ + ↑t * I - ρ).re := by simp; linarith
  have h3 : 0 ≤ (↑σ + 2 * ↑t * I - ρ).re := by simp; linarith
  exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (re_inv_nonneg_of_re_nonneg h1))
    (mul_nonneg (by norm_num) (re_inv_nonneg_of_re_nonneg h2)))
    (re_inv_nonneg_of_re_nonneg h3)

/-! ### The edge bound -/

/-- **Zero-free edge from the factorisation (Route A).**
Assuming
* the product decomposition `LSeries ↗Λ s = analytic s - ∑_{ρ ∈ Z} (1/(s-ρ) + 1/ρ)` for the three
  evaluation points `σ, σ+it, σ+2it` (with `Re s = σ > 1`),
* an explicit `O(log|t|)` bound on the 3-4-1 combination of the analytic part,
* `ρ₀ ∈ Z` a borderline zero with `Im ρ₀ = t` and `0 < Re ρ₀ < 1`,
this yields `σ - Re ρ₀ ≥ 4 / (A₀/(σ-1) + A₁·log(|t|+2) + A₂)`. -/
theorem zeroFreeEdge_from_factorization
    (σ t : ℝ) (hσ : 1 < σ)
    (Z : Finset ℂ) (ρ₀ : ℂ) (hρ₀mem : ρ₀ ∈ Z) (hρ₀im : ρ₀.im = t)
    (hρ₀re_pos : 0 < ρ₀.re) (hρ₀re_lt : ρ₀.re < 1)
    (hZre : ∀ ρ ∈ Z, 0 < ρ.re) (hZre_lt : ∀ ρ ∈ Z, ρ.re < 1)
    (analytic : ℂ → ℂ)
    (h_decomp : ∀ (s : ℂ) (hs : 1 < s.re),
      LSeries ↗Λ s = analytic s - ∑ ρ' ∈ Z, (1 / (s - ρ') + 1 / ρ'))
    (A₀ A₁ A₂ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (h_analytic : 3 * (analytic (↑σ : ℂ)).re + 4 * (analytic (↑σ + ↑t * I)).re
        + (analytic (↑σ + 2 * ↑t * I)).re ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂)
    (hRHS_pos : 0 < A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) :
    σ - ρ₀.re ≥ 4 / (A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) := by
  have hd : 0 < σ - ρ₀.re := by linarith
  set d : ℝ := σ - ρ₀.re with hd_def
  have h3f1 := three_four_one_re_LSeries_vonMangoldt hσ t
  have hLS_eq : (3 * (LSeries ↗Λ (↑σ : ℂ)).re + 4 * (LSeries ↗Λ (↑σ + ↑t * I)).re
        + (LSeries ↗Λ (↑σ + 2 * ↑t * I)).re)
      = (3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re + (analytic (↑σ + 2 * ↑t * I)).re)
      - (3 * (∑ ρ' ∈ Z, (1 / (↑σ - ρ') + 1 / ρ')).re
        + 4 * (∑ ρ' ∈ Z, (1 / (↑σ + ↑t * I - ρ') + 1 / ρ')).re
        + (∑ ρ' ∈ Z, (1 / (↑σ + 2 * ↑t * I - ρ') + 1 / ρ')).re) := by
    rw [h_decomp (↑σ) (by simpa using hσ),
      h_decomp (↑σ + ↑t * I) (by simpa using hσ),
      h_decomp (↑σ + 2 * ↑t * I) (by simpa using hσ)]
    simp only [sub_re, re_sum, Finset.sum_add_distrib, add_re]
    ring
  rw [hLS_eq, sub_nonneg] at h3f1
  -- `h3f1` is now `(3-4-1 ΣT) ≤ (3-4-1 analytic)`
  have hρ₀eq : ρ₀ = (↑(ρ₀.re) : ℂ) + ↑t * I := by
    apply Complex.ext <;> simp [hρ₀im]
  have hdC : (↑d : ℂ) = ↑σ - ↑(ρ₀.re) := by rw [hd_def]; push_cast; ring
  have hρ₀_1 : ↑σ - ρ₀ = ↑d - ↑t * I := by rw [hρ₀eq, hdC]; ring
  have hρ₀_2 : ↑σ + ↑t * I - ρ₀ = ↑d := by rw [hρ₀eq, hdC]; ring
  have hρ₀_3 : ↑σ + 2 * ↑t * I - ρ₀ = ↑d + ↑t * I := by rw [hρ₀eq, hdC]; ring
  have hsum : 4 / d ≤ 3 * (∑ ρ' ∈ Z, (1 / (↑σ - ρ') + 1 / ρ')).re
      + 4 * (∑ ρ' ∈ Z, (1 / (↑σ + ↑t * I - ρ') + 1 / ρ')).re
      + (∑ ρ' ∈ Z, (1 / (↑σ + 2 * ↑t * I - ρ') + 1 / ρ')).re := by
    have hcomb : ∀ w : ℂ, (3 * (∑ ρ' ∈ Z, (1 / (↑σ - ρ') + 1 / ρ')).re
        + 4 * (∑ ρ' ∈ Z, (1 / (↑σ + ↑t * I - ρ') + 1 / ρ')).re
        + (∑ ρ' ∈ Z, (1 / (↑σ + 2 * ↑t * I - ρ') + 1 / ρ')).re)
        = ∑ ρ' ∈ Z, (3 * ((1 / (↑σ - ρ') + 1 / ρ')).re
            + 4 * ((1 / (↑σ + ↑t * I - ρ') + 1 / ρ')).re
            + ((1 / (↑σ + 2 * ↑t * I - ρ') + 1 / ρ')).re) := by
      intro w
      rw [re_sum, re_sum, re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
    rw [hcomb 0, ← Finset.add_sum_erase Z _ hρ₀mem]
    have hc0 : 4 / d ≤ 3 * ((1 / (↑σ - ρ₀) + 1 / ρ₀)).re
        + 4 * ((1 / (↑σ + ↑t * I - ρ₀) + 1 / ρ₀)).re
        + ((1 / (↑σ + 2 * ↑t * I - ρ₀) + 1 / ρ₀)).re := by
      rw [hρ₀_1, hρ₀_2, hρ₀_3]
      simp only [add_re]
      have hb := re_three_four_one_one_over_sub_borderline d t hd
      simp only [one_div] at hb ⊢
      have hz : 0 ≤ (ρ₀⁻¹).re := by
        simpa [one_div] using re_inv_nonneg_of_re_nonneg hρ₀re_pos.le
      linarith
    have hrest : 0 ≤ ∑ x ∈ Finset.erase Z ρ₀,
        (3 * ((1 / (↑σ - x) + 1 / x)).re
        + 4 * ((1 / (↑σ + ↑t * I - x) + 1 / x)).re
        + ((1 / (↑σ + 2 * ↑t * I - x) + 1 / x)).re) := by
      apply Finset.sum_nonneg
      intro x hmem
      have hmemZ : x ∈ Z := Finset.mem_of_mem_erase hmem
      have hgen := re_three_four_one_one_over_sub_nonneg (σ := σ) (t := t) x
        (by linarith [hσ, hZre_lt x hmemZ])
      have hz : 0 ≤ ((1 : ℂ) / x).re := re_inv_nonneg_of_re_nonneg (hZre x hmemZ).le
      simp only [add_re]
      linarith
    exact le_trans hc0 (le_add_of_nonneg_right hrest)
  have h4 : 4 / d ≤ 3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re
      + (analytic (↑σ + 2 * ↑t * I)).re := le_trans hsum h3f1
  have h4le : 4 / d ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := le_trans h4 h_analytic
  rw [ge_iff_le, div_le_iff₀ hRHS_pos]
  rw [div_le_iff₀ hd] at h4le
  linarith

end ZeroFreeEdge

end ZeroFreeRegion
