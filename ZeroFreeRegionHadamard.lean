import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Route B infrastructure: Hadamard factorization for the zero-free region

This file builds the missing machinery needed to close the `sorry` in
`ZeroFreeRegionProof.lean` by proving the Hadamard factorization of the
completed Riemann zeta function and deriving the sum over non-trivial zeros
that the 3-4-1 log-derivative argument requires.

## Status (2026-08-06)

Foundational definitions below (`primaryFactor`, `orderSet`, `orderOfEntire`,
`canonicalProduct`) now exist and compile. A thorough survey of `mathlib` shows
that the following are **absent** and must still be built:

1. **Order of an entire function** — `orderOfEntire` (defined below, but its
   basic API and the order-1 bound for the completed zeta still need work).
2. **Weierstrass primary factors** `E_p(z)` — defined below with algebraic
   properties; the convergence estimate
   `‖log E_p(z)‖ ≤ C ‖z‖^{p+1}` for `‖z‖ ≤ 1/2` is still missing (it needs a
   complex `log(1 - z)` Taylor-series `HasSum` lemma, also absent).
3. **Canonical product** over a zero set — defined below (finite version);
   the infinite-product convergence for the non-trivial zeros (genus 1) is
   missing.
4. **Hadamard factorization theorem** itself — entirely absent.
5. **Application to the completed zeta**: identifying the zeros of
   `s ↦ s(s-1)·completedRiemannZeta s` with the non-trivial zeros `ρ` of `ζ`
   (with multiplicities), proving it is entire of order 1, and taking the
   logarithmic derivative to obtain
   `-ζ'/ζ(s) = analytic s - Σ_ρ (1/(s-ρ) + 1/ρ)`.

What `mathlib` *does* already provide and that Route B can lean on:
- `completedRiemannZeta₀_one_sub` (functional equation),
- `Mathlib.Analysis.SpecialFunctions.Stirling` and `Digamma` (for the
  `O(log |t|)` bound on the analytic part),
- `Mathlib.Analysis.Complex.JensenFormula` and the value-distribution theory
  (Jensen/Poisson-Jensen, counting functions),
- `Mathlib.Analysis.SpecialFunctions.Log.Summable` (`HasProd` / `Summable (log f)`)
  for building infinite products once the convergence estimate is available.

## Remaining theorems (the actual Route B program)

- `primaryFactor_log_bound` :
    `‖z‖ ≤ 1/2 → ‖log (primaryFactor p z)‖ ≤ C(p) · ‖z‖^{p+1}`
- `canonicalProduct_converges` (genus 1) for the non-trivial zeros `ρ`,
- `hadamardFactorization` : for `f` entire of finite order `ρ` with zeros
  `a_n`, `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/a_n)` with `deg g ≤ ρ`,
- `completedZeta_order_one` : `orderOfEntire (s ↦ s(s-1)·completedRiemannZeta s) = 1`,
- `completedZeta_zeros_eq_nontrivialZeros` : the zero set (with multiplicity) is
  exactly `{ρ : non-trivial zero of ζ}`,
- `logDeriv_completedZeta` : the logarithmic derivative identity above,
  which instantiates the `h_decomp` / `h_analytic` hypotheses of
  `riemannZeta_ne_zero_of_zeroFreeEdge`.
-/

namespace ZeroFreeRegionHadamard

open Complex Finset

/-! ## Weierstrass primary factors -/

/-- The Weierstrass elementary factor of degree `p`:
`E_p(z) = (1 - z) · exp(z + z²/2 + ⋯ + z^p/p)`. -/
noncomputable def primaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ range p, z ^ (k + 1) / (k + 1))

@[simp]
lemma primaryFactor_zero (p : ℕ) : primaryFactor p 0 = 1 := by
  simp [primaryFactor]

@[simp]
lemma primaryFactor_one (p : ℕ) : primaryFactor p 1 = 0 := by
  simp [primaryFactor]

lemma primaryFactor_of_neg (p : ℕ) (z : ℂ) :
    primaryFactor p (-z) = (1 + z) * exp (∑ k ∈ range p, (-z) ^ (k + 1) / (k + 1)) := by
  simp [primaryFactor]

/-! ## Order of an entire function -/

/-- The set of real exponents `ρ` such that `‖f z‖ ≤ C·exp(‖z‖^ρ)` outside a
disk. The order of `f` is the infimum of this set (or `⊤` if it is empty). -/
def orderSet (f : ℂ → ℂ) : Set ℝ :=
  { ρ : ℝ | ∃ (C : ℝ) (r₀ : ℝ), 0 < r₀ ∧
      ∀ z, r₀ ≤ ‖z‖ → ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ) }

/-- The (extended-real) order of an entire function, defined as the infimum of
`orderSet f` (or `⊤` when that set is empty). -/
noncomputable def orderOfEntire (f : ℂ → ℂ) : WithTop ℝ :=
  ⨅ (ρ : ℝ) (h : ρ ∈ orderSet f), ↑ρ

/-! ## Canonical product (finite version) -/

/-- The finite canonical product over a `Finset` of (nonzero) zeros. The infinite
version over the non-trivial zeros of `ζ` requires the convergence estimate
`primaryFactor_log_bound` and `HasProd` from
`Mathlib.Analysis.SpecialFunctions.Log.Summable`. -/
noncomputable def canonicalProduct (p : ℕ) (Z : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ z ∈ Z, primaryFactor p (s / z)

lemma canonicalProduct_empty (p : ℕ) (s : ℂ) : canonicalProduct p ∅ s = 1 := by
  simp [canonicalProduct]

lemma canonicalProduct_insert {p : ℕ} {Z : Finset ℂ} {z : ℂ} (hz : z ∉ Z) (s : ℂ) :
    canonicalProduct p (insert z Z) s = primaryFactor p (s / z) * canonicalProduct p Z s := by
  simp [canonicalProduct, prod_insert hz]

/-! ## Convergence estimate for the primary factor -/

open FormalMultilinearSeries Real

/-- Coefficients of the Taylor series of `log(1 + x)` at `0`:
`-(-1)^n / n = (-1)^{n+1}/n` (and `0` for `n = 0`). -/
noncomputable private def logCoeff (n : ℕ) : ℂ := -(((-1 : ℂ) ^ n) / n)

/-- The formal power series `∑ (-1)^{n+1} xⁿ / n` has radius of convergence `1`. -/
private lemma logSeries_radius : (FormalMultilinearSeries.ofScalars ℂ logCoeff).radius = 1 := by
  refine ofScalars_radius_eq_inv_of_tendsto (by norm_num) ?_
  have hratio : ∀ n ≥ 1, ‖logCoeff n.succ‖ / ‖logCoeff n‖ = (n : ℝ) / (n + 1) := by
    intro n hn
    rw [logCoeff, logCoeff]
    simp only [neg_div, norm_div, norm_inv, norm_neg, Complex.norm_neg_one, one_pow,
      RCLike.norm_ofReal, ofReal_nat, one_div, div_div]
    field_simp
    norm_cast
  refine Tendsto.congr' (eventually_of_forall fun n hn => ?_) ?_
  · exact hratio n (Nat.succ_pos n)
  · have : (fun n => (n : ℝ) / (n + 1)) = fun n => 1 - ((n : ℝ) + 1)⁻¹ := by
      ext n; field_simp; ring
    simpa [this] using Tendsto.sub tendsto_const_nhds
      (tendsto_inv_atTop_nhds_0_nhds.comp (Filter.Tendsto.add_const 1 tendsto_coe_nat_atTop))

/-- For `‖z‖ < 1`, `log(1 - z) = -∑_{n≥1} zⁿ/n`. -/
private lemma logSeries_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => z ^ n / n) (-log (1 - z)) := by
  let ser := FormalMultilinearSeries.ofScalars ℂ logCoeff
  have hrad : ser.radius = 1 := logSeries_radius
  have hball : HasFPowerSeriesOnBall ser.sum ser 0 1 :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall ser (by simpa using hrad)
  rcases hasFPowerSeriesAt_clog_one_add with ⟨r', hr'⟩
  have hlog_ball : HasFPowerSeriesOnBall (fun x => log (1 + x)) ser 0 1 :=
    hr'.exchange_radius hball
  have hfun : ∀ n, ser n (fun _ => -z) = -z ^ n / n := by
    intro n
    rw [ser, ofScalars_apply_eq, logCoeff, neg_div]
    simp only [neg_div, mul_div_assoc, neg_one_pow_eq_pow, pow_succ, neg_mul, mul_neg,
      neg_neg, one_div, mul_one]
    ring
  have h : HasSum (fun n => ser n (fun _ => -z)) (log (1 - z)) :=
    hlog_ball.hasSum_sub (by simpa using hz)
  exact HasSum.neg (h.congr (by simpa [hfun]))

/-- **Key estimate.** For `‖z‖ ≤ 1/2`, the (principal) logarithm of the Weierstrass primary
factor satisfies `‖log E_p(z)‖ ≤ 2/(p+1) · ‖z‖^{p+1}`. This is the estimate that makes the
canonical product over the non-trivial zeros converge (genus `1`). -/
theorem primaryFactor_log_bound (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (primaryFactor p z)‖ ≤ 2 / (p + 1 : ℝ) * ‖z‖ ^ (p + 1) := by
  have hz1 : ‖z‖ < 1 := by linarith [hz]
  have hnz : 1 - z ≠ 0 := by
    intro h
    have := congrArg norm h
    simpa [norm_sub_eq_zero_iff, hz] using this
  let S (z : ℂ) := ∑ k ∈ range p, z ^ (k + 1) / (k + 1)
  have hS : HasSum (fun n => z ^ n / n) (S z) := by
    convert hasSum_sum_range (fun n => z ^ n / n) (p + 1) using 1
    simp only [S, Finset.sum_range_succ, Nat.succ_ne_zero, zero_div, sum_range_zero, add_zero]
    ext n
    norm_num
  have hlog : HasSum (fun n => z ^ n / n) (-log (1 - z)) := logSeries_hasSum hz1
  -- The tail R(z) := -log(1-z) - S(z) = ∑_{n≥p+1} zⁿ/n.
  let R (z : ℂ) := -log (1 - z) - S z
  have htail : HasSum (fun m => z ^ (m + p + 1) / (m + p + 1)) (R z) := by
    convert (hasSum_nat_add_iff' (p + 1)).mp hlog using 1
    simp only [R, Finset.sum_range_succ, Nat.succ_ne_zero, zero_div, sum_range_zero, add_zero]
    ext i
    norm_num
  -- E_p(z) = (1-z)·exp(S(z)) = exp(log(1-z) + S(z)) = exp(-R(z)).
  have hE : primaryFactor p z = exp (-R z) := by
    rw [primaryFactor, S, ← exp_add]
    rw [← mul_div_assoc, ← exp_log hnz]
    congr 1
    ring
  have hbound : ‖R z‖ ≤ 2 / (p + 1 : ℝ) * ‖z‖ ^ (p + 1) := by
    let g (m : ℕ) := ‖z‖ ^ (m + p + 1) / (p + 1 : ℝ)
    have hg : HasSum g (‖z‖ ^ (p + 1) / (p + 1 : ℝ) * (1 / (1 - ‖z‖))) := by
      refine HasSum.mul_left (hasSum_geometric_of_norm_lt_one hz1)
    have hle : ∀ m, ‖z ^ (m + p + 1) / (m + p + 1)‖ ≤ g m := by
      intro m
      simp only [norm_div, Complex.norm_pow, RCLike.norm_ofReal]
      exact div_le_div_of_le_left (by positivity) (by norm_cast) (by norm_cast)
    refine le_trans (HasSum.norm_le_of_bounded htail hle hg) ?_
    rw [div_le_div_right (by norm_cast; positivity)]
    linarith [hz]
  have him : abs (R z).im < π := by
    refine lt_of_le_of_lt (Complex.abs_im_le_norm (R z)) ?_
    refine lt_of_le_of_lt hbound ?_
    have hc : 2 / (p + 1 : ℝ) * (1 / 2) ^ (p + 1) < π := by
      refine lt_of_le_of_lt ?_ (by norm_num)
      rw [← div_eq_mul_inv, div_le_one (by norm_cast; positivity)]
      have : 1 ≤ 2 ^ p * (p + 1) := by
        induction p <;> simp_all [pow_succ, mul_add, mul_comm, mul_assoc]
      linarith [this]
    linarith [hz, hc, pow_le_one _ (by linarith [hz]) (by norm_cast; positivity)]
  have hlogE : Complex.log (primaryFactor p z) = -R z := by
    rw [hE, Complex.log_exp (-R z) (by linarith [him]) (by linarith [him])]
  rw [hlogE, norm_neg]
  exact hbound

end ZeroFreeRegionHadamard
