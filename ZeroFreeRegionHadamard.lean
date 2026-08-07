import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Route B infrastructure: Hadamard factorization for the zero-free region

This file builds the missing machinery needed to close the `sorry` in
`ZeroFreeRegionProof.lean` by proving the Hadamard factorization of the
completed Riemann zeta function and deriving the sum over non-trivial zeros
that the 3-4-1 log-derivative argument requires.

## Status (2026-08-07)

Foundational definitions below (`primaryFactor`, `orderSet`, `orderOfEntire`,
`canonicalProduct`) exist and compile, and the keystone convergence estimate
`primaryFactor_log_bound` is now **proven**. A thorough survey of `mathlib` shows
that the following are **absent** and must still be built:

1. **Order of an entire function** — `orderOfEntire` (defined below, but its
   basic API and the order-1 bound for the completed zeta still need work).
2. **Hadamard factorization theorem** itself — entirely absent.
3. **Application to the completed zeta**: identifying the zeros of
   `s ↦ s(s-1)·completedRiemannZeta s` with the non-trivial zeros `ρ` of `ζ`
   (with multiplicities), proving it is entire of order 1, and taking the
   logarithmic derivative to obtain
   `-ζ'/ζ(s) = analytic s - Σ_ρ (1/(s-ρ) + 1/ρ)`.

What `mathlib` *does* already provide and that Route B can lean on:
- `Complex.norm_log_sub_logTaylor_le` and the `Complex.logTaylor` API in
  `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` — this is what makes
  `primaryFactor_log_bound` a short proof (no power-series radius work needed),
- `completedRiemannZeta₀_one_sub` (functional equation),
- `Mathlib.Analysis.SpecialFunctions.Stirling` and `Digamma` (for the
  `O(log |t|)` bound on the analytic part),
- `Mathlib.Analysis.Complex.JensenFormula` and the value-distribution theory
  (Jensen/Poisson-Jensen, counting functions),
- `Mathlib.Analysis.SpecialFunctions.Log.Summable` (`HasProd` / `Summable (log f)`)
  for building infinite products now that the convergence estimate is available.

## Remaining theorems (the actual Route B program)

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
  ⨅ (ρ : ℝ) (_ : ρ ∈ orderSet f), ↑ρ

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

/-- The `(p+1)`-st Taylor polynomial of `log` at `1`, evaluated at `-z`, is exactly the
negative of the exponent appearing in `primaryFactor p z`. This is the bridge between the
Weierstrass factor and `mathlib`'s `Complex.logTaylor` API. -/
lemma logTaylor_neg (p : ℕ) (z : ℂ) :
    Complex.logTaylor (p + 1) (-z) = -∑ k ∈ range p, z ^ (k + 1) / (k + 1) := by
  induction p with
  | zero => simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
  | succ n ih =>
    rw [Complex.logTaylor_succ]
    simp only [Pi.add_apply, ih, Finset.sum_range_succ]
    have h : ((-1 : ℂ)) ^ (n + 1 + 1) * (-z) ^ (n + 1) = -(z ^ (n + 1)) := by
      rw [show (-z) ^ (n + 1) = (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) by
        rw [← neg_one_mul z, mul_pow]]
      rw [← mul_assoc, ← pow_add]
      rw [show n + 1 + 1 + (n + 1) = 2 * (n + 1) + 1 by ring]
      rw [pow_succ, pow_mul]
      norm_num
    push_cast
    rw [h]
    ring

/-- **Key estimate.** For `‖z‖ ≤ 1/2`, the (principal) logarithm of the Weierstrass primary
factor satisfies `‖log E_p(z)‖ ≤ 2/(p+1) · ‖z‖^{p+1}`. This is the estimate that makes the
canonical product over the non-trivial zeros converge (genus `1`).

The proof observes that `log E_p(z) = log(1 + (-z)) - logTaylor (p+1) (-z)`, which is exactly
the quantity bounded by `mathlib`'s `Complex.norm_log_sub_logTaylor_le`. -/
theorem primaryFactor_log_bound (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (primaryFactor p z)‖ ≤ 2 / (p + 1 : ℝ) * ‖z‖ ^ (p + 1) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : ‖(-z)‖ < 1 := by simpa using hz1
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz1
    simp at hz1
  set D : ℂ := Complex.log (1 + -z) - Complex.logTaylor (p + 1) (-z) with hD
  have hbnd : ‖D‖ ≤ ‖(-z)‖ ^ (p + 1) * (1 - ‖(-z)‖)⁻¹ / (p + 1) :=
    Complex.norm_log_sub_logTaylor_le p hnz
  have hb2 : ‖D‖ ≤ 2 / (p + 1 : ℝ) * ‖z‖ ^ (p + 1) := by
    refine hbnd.trans ?_
    rw [norm_neg] at *
    have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hp : (0:ℝ) < (p:ℝ) + 1 := by positivity
    rw [div_le_iff₀ hp]
    have h1 : ‖z‖ ^ (p+1) * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ (p+1) * 2 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    calc ‖z‖ ^ (p+1) * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ (p+1) * 2 := h1
      _ = 2 / ((p:ℝ)+1) * ‖z‖^(p+1) * ((p:ℝ)+1) := by field_simp
  -- `E_p(z) = (1-z)·exp(S_p(z)) = exp D`.
  have hE : primaryFactor p z = Complex.exp D := by
    rw [hD, logTaylor_neg, sub_neg_eq_add, ← sub_eq_add_neg, primaryFactor,
      Complex.exp_add, Complex.exp_log hne]
  -- `|Im D| ≤ ‖D‖ ≤ 1 < π`, so `log (exp D) = D`.
  have hsmall : ‖D‖ ≤ 1 := by
    refine hb2.trans ?_
    have h1 : ‖z‖ ^ (p+1) ≤ (1/2 : ℝ) ^ (p+1) := by gcongr
    have h2 : (1/2 : ℝ) ^ (p+1) ≤ 1/2 := by
      rw [pow_succ]
      nlinarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1) (n := p),
        pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) p]
    have h3 : 2 / ((p:ℝ)+1) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (0:ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    have hpos : (0:ℝ) ≤ 2 / ((p:ℝ)+1) := by positivity
    calc 2 / ((p:ℝ)+1) * ‖z‖^(p+1) ≤ 2 / ((p:ℝ)+1) * (1/2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hpos
      _ ≤ 2 * (1/2) := by nlinarith
      _ = 1 := by norm_num
  have him : |D.im| ≤ 1 := le_trans (Complex.abs_im_le_norm D) hsmall
  have hpi : (1:ℝ) < Real.pi := by
    have := Real.pi_gt_three
    linarith
  rw [hE, Complex.log_exp (by cases abs_le.mp him; linarith) (by cases abs_le.mp him; linarith)]
  exact hb2

/-! ## Infinite canonical product convergence -/

/-- **Genus-`(p+1)` convergence of the canonical product over zeros `aᵢ`.**
If `Σ 1/‖aᵢ‖^{p+1}` converges and `z` stays away from the zeros so that
`‖z/aᵢ‖ ≤ 1/2` (e.g. for all but finitely many `i`), then the infinite product
`∏ᵢ E_p(z/aᵢ)` is multipliable. The proof bounds
`Σ ‖log E_p(z/aᵢ)‖` by a constant multiple of `Σ 1/‖aᵢ‖^{p+1}` using
`primaryFactor_log_bound`, then applies `Complex.multipliable_of_summable_log`. -/
theorem multipliable_primaryFactor_of_summable {ι : Type*} (p : ℕ) {a : ι → ℂ} {z : ℂ}
    (haz : ∀ i, ‖z / a i‖ ≤ 1 / 2)
    (hs : Summable fun i => 1 / ‖a i‖ ^ (p + 1)) :
    Multipliable fun i => primaryFactor p (z / a i) := by
  have hlog : Summable fun i => ‖Complex.log (primaryFactor p (z / a i))‖ := by
    refine Summable.of_nonneg_of_le
      (f := fun i => (2 / ((p : ℝ) + 1)) * ‖z‖ ^ (p + 1) * (1 / ‖a i‖ ^ (p + 1))) ?_ ?_ ?_
    · intro _; positivity
    · intro i
      have hb := primaryFactor_log_bound p (haz i : ‖z / a i‖ ≤ 1/2)
      rw [div_eq_mul_inv, norm_mul, norm_inv] at hb
      rw [mul_pow, inv_pow, ← div_eq_mul_inv, inv_eq_one_div (‖a i‖ ^ (p + 1))] at hb
      exact hb.trans (le_of_eq (by ring))
    · exact hs.mul_left ((2 / ((p : ℝ) + 1)) * ‖z‖ ^ (p + 1))
  exact Complex.multipliable_of_summable_log hlog.of_norm

end ZeroFreeRegionHadamard
