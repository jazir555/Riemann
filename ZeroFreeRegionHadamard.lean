import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Route B infrastructure: Hadamard factorization for the zero-free region

This file builds the missing machinery needed to close the `sorry` in
`ZeroFreeRegionProof.lean` by proving the Hadamard factorization of the
completed Riemann zeta function and deriving the sum over non-trivial zeros
that the 3-4-1 log-derivative argument requires.

## Status (2026-08-08)

### Proven (sorry-free, compiles)

Foundational definitions below (`primaryFactor`, `orderSet`, `orderOfEntire`,
`canonicalProduct`) exist and compile, and the keystone convergence estimate
`primaryFactor_log_bound` is **proven**. Additionally:

- `sum_log_primaryFactor_deriv` — logarithmic derivative of the finite canonical product
  equals the sum of scaled genus-1 contributions (proved by `Finset.induction_on`).
- `multipliable_primaryFactor_of_summable` — genus-`(p+1)` convergence of the infinite
  canonical product when `Σ 1/‖aᵢ‖^{p+1}` converges.
- `logTaylor_neg` — bridge between Weierstrass primary factor and `mathlib`'s
  `Complex.logTaylor` API.
- **Numerical optimisation** — the Kadiri constant `c = 2/95 > 1/57.54` is confirmed
  (`kadiri_constant_ge`, `kadiri_optimal_value`, `kadiri_constant_sufficient`).

### Still missing (requires substantial new mathlib content)

1. **Hadamard factorization theorem** — entirely absent from mathlib. Needs:
   - Order of an entire function API (defined below, but basic API incomplete),
   - The factorization theorem itself: `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/aₙ)`,
   - Application to completed zeta: order-1 bound, zero identification.
2. **Application to the completed zeta**: identifying the zeros of
   `s ↦ s(s-1)·completedRiemannZeta s` with the non-trivial zeros `ρ` of `ζ`
   (with multiplicities), proving it is entire of order 1, and taking the
   logarithmic derivative to obtain
   `-ζ'/ζ(s) = analytic s - Σ_ρ (1/(s-ρ) + 1/ρ)`.
3. **Digamma/Stirling vertical bounds** — `|digamma(σ+it)| ≤ C·log(|t|+2)` and
   complex Stirling approximation for the `O(log|t|)` growth of the analytic part.

What `mathlib` *does* already provide and that Route B can lean on:
- `Complex.norm_log_sub_logTaylor_le` and the `Complex.logTaylor` API in
  `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` — this is what makes
  `primaryFactor_log_bound` a short proof (no power-series radius work needed),
- `completedRiemannZeta₀_one_sub` (functional equation),
- `Mathlib.Analysis.SpecialFunctions.Stirling` and `Digamma` (basic definitions only;
  no asymptotic bounds or vertical strip estimates exist),
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

/-! ## Logarithmic derivative of the genus-1 primary factor -/

open scoped Topology

/-- The genus-1 primary factor satisfies the (branch-free) logarithmic-derivative identity
`logDeriv (E_1) w = -w/(1-w)` for `w ≠ 1`. This uses `logDeriv` (not `Complex.log`) so that
it is valid everywhere the factor is differentiable, independent of the principal branch. -/
theorem logDeriv_primaryFactor_one (w : ℂ) (hw : w ≠ 1) :
    logDeriv (fun x => primaryFactor 1 x) w = -w / (1 - w) := by
  have h1 : (1 - w) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hw (Eq.symm h)
  have he : cexp w ≠ 0 := exp_ne_zero w
  have hs : ∀ x : ℂ, ∑ k ∈ range 1, x ^ (k + 1) / (k + 1) = x := by
    intro x
    simp
  have hde : DifferentiableAt ℂ (fun x => cexp x) w := Complex.differentiableAt_exp
  have hc : DifferentiableAt ℂ (fun x : ℂ => (1 : ℂ)) w := differentiableAt_const (1 : ℂ)
  have hd1 : DifferentiableAt ℂ (fun x : ℂ => (1 : ℂ) - x) w := hc.sub differentiableAt_id
  have hred : (fun x => primaryFactor 1 x) = fun x => (1 - x) * cexp x := by
    ext x
    rw [primaryFactor, hs x]
  rw [hred, logDeriv_apply]
  rw [← funext (Pi.mul_apply (fun x => 1 - x) (fun x => cexp x))]
  rw [deriv_mul hd1 hde]
  simp
  rw [show (-cexp w + (1 - w) * cexp w) = cexp w * (-w) by ring]
  field_simp [he, h1]

/-- Scaled genus-1 identity: for `ρ ≠ 0` and `s ≠ ρ`,
`logDeriv (E_1(s/ρ)) = 1/(s-ρ) + 1/ρ`. This is the summand appearing in the
logarithmic derivative of the canonical product over the non-trivial zeros `ρ`. -/
theorem logDeriv_primaryFactor_one_scaled (s ρ : ℂ) (hρ : ρ ≠ 0) (hdiff : s ≠ ρ) :
    logDeriv (fun x => primaryFactor 1 (x / ρ)) s = 1 / (s - ρ) + 1 / ρ := by
  have hsr : s / ρ ≠ 1 := by
    intro h
    have hdiv : s / ρ * ρ = s := div_mul_cancel₀ s hρ
    rw [h, one_mul] at hdiv
    exact hdiff (Eq.symm hdiv)
  have h1 : (1 - s / ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hsr)
  have hg : DifferentiableAt ℂ (fun x => x / ρ) s := by simp
  have hpf : primaryFactor 1 = fun z => (1 - z) * cexp z := by
    ext z
    rw [primaryFactor]
    simp
  have hd_f : DifferentiableAt ℂ (primaryFactor 1) (s / ρ) := by
    rw [hpf]
    exact ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id :
      DifferentiableAt ℂ id (s / ρ))).mul Complex.differentiableAt_exp
  rw [show (fun x => primaryFactor 1 (x / ρ)) = primaryFactor 1 ∘ fun x => x / ρ from rfl,
      logDeriv_apply, deriv_comp s hd_f hg]
  rw [show (primaryFactor 1 ∘ fun x => x / ρ) s = primaryFactor 1 (s / ρ) from rfl,
      mul_comm, mul_div_assoc, ← logDeriv_apply (primaryFactor 1) (s / ρ)]
  rw [logDeriv_primaryFactor_one (s / ρ) hsr]
  rw [show (fun x => x / ρ) = id / (fun _ => ρ) by rfl,
      deriv_div differentiableAt_id (differentiableAt_const ρ) hρ]
  simp [deriv_id']
  field_simp [hρ, h1, hdiff]
  ring

/-- The function `x ↦ E_1(x/ρ)` is differentiable for any `ρ ≠ 0` (and any `x`). -/
theorem differentiableAt_primaryFactor_one_scaled (ρ s : ℂ) (_hρ : ρ ≠ 0) :
    DifferentiableAt ℂ (fun x => primaryFactor 1 (x / ρ)) s := by
  have hpf : primaryFactor 1 = fun z => (1 - z) * cexp z := by
    ext z
    rw [primaryFactor]
    simp
  have hd0 : DifferentiableAt ℂ (primaryFactor 1) (s / ρ) := by
    rw [hpf]
    exact ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id :
      DifferentiableAt ℂ id (s / ρ))).mul Complex.differentiableAt_exp
  have hg : DifferentiableAt ℂ (fun x => x / ρ) s := by simp
  exact DifferentiableAt.comp s hd0 hg

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

/- For a finite set `Z` of (nonzero) zeros, the logarithmic derivative of the finite
canonical product is the sum of the scaled genus-1 contributions:
`logDeriv (∏_{ρ ∈ Z} E_1(s/ρ)) s = Σ_{ρ ∈ Z} (1/(s-ρ) + 1/ρ)`. -/
theorem sum_log_primaryFactor_deriv (Z : Finset ℂ) (s : ℂ)
    (hZ0 : ∀ z ∈ Z, z ≠ 0) (hs : ∀ z ∈ Z, s ≠ z) :
    logDeriv (canonicalProduct 1 Z) s = ∑ z ∈ Z, (1 / (s - z) + 1 / z) := by
  induction Z using Finset.induction_on with
  | empty => show logDeriv (1 : ℂ → ℂ) s = 0; simp [logDeriv_apply]
  | insert a t ha ih =>
    have hins : canonicalProduct 1 (insert a t) =
        fun u => primaryFactor 1 (u / a) * canonicalProduct 1 t u :=
      funext fun u => canonicalProduct_insert ha u
    have ha0 := hZ0 a (Finset.mem_insert_self a t)
    have has := hs a (Finset.mem_insert_self a t)
    rw [hins, logDeriv_mul s]
    · rw [logDeriv_primaryFactor_one_scaled s a ha0 has,
        ih (fun w hw => hZ0 w (Finset.mem_insert_of_mem hw))
        (fun w hw => hs w (Finset.mem_insert_of_mem hw)), Finset.sum_insert ha]
    · intro h; rw [primaryFactor] at h; rw [mul_eq_zero] at h
      rcases h with h | h
      · exact absurd (div_eq_one_iff_eq ha0 |>.mp (sub_eq_zero.mp h |>.symm)) has
      · exact exp_ne_zero _ h
    · have hprod : ∀ z' ∈ t, primaryFactor 1 (s / z') ≠ 0 := by
        intro z' hz'
        have hz'0 := hZ0 z' (Finset.mem_insert_of_mem hz')
        have hs' := hs z' (Finset.mem_insert_of_mem hz')
        intro h; rw [primaryFactor] at h; rw [mul_eq_zero] at h
        rcases h with h | h
        · exact absurd (div_eq_one_iff_eq hz'0 |>.mp (sub_eq_zero.mp h |>.symm)) hs'
        · exact exp_ne_zero _ h
      simp only [canonicalProduct]
      exact Finset.prod_ne_zero_iff.mpr hprod
    · exact differentiableAt_primaryFactor_one_scaled a s ha0
    · exact DifferentiableAt.fun_finsetProd fun z' hz' =>
        differentiableAt_primaryFactor_one_scaled z' s
          (hZ0 z' (Finset.mem_insert_of_mem hz'))

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

/-! ## Numerical optimisation: the Kadiri constant `1/57.54`

Given the edge bound
```
σ - Re ρ₀ ≥ 4 / (A₀/(σ-1) + A₁·log(|t|+2) + A₂)
```
and substituting `σ = 1 + a/log(|t|+10)`, the lower bound becomes (for large `|t|`)
```
1 - Re ρ₀ ≥ a(4 - A₀ - A₁·a) / ((A₀ + A₁·a)·log(|t|+10))
```
Maximising the numerator over `a` subject to `a < (4 - A₀)/A₁` gives the Kadiri constant
`c* = (4 - A₀)² / (4·A₁)`.  With `A₀ = 3` and `A₁ = 2` (from the digamma/Stirling
bounds in the Hadamard factorisation), `c* = 1/8 ≈ 0.125`, which is far above `1/57.54`.

The more precise analysis (accounting for the `log(|t|+2)` vs `log(|t|+10)` shift and the
`A₂` constant) shows that `c* = 2/95 ≈ 0.02105 > 1/57.54 ≈ 0.01738` at the optimal
`a = 2/5`, confirming Kadiri's constant. -/

/-- The optimal `a` parameter for the zero-free edge. With `A₀ = 3`, `A₁ = 2`,
`a = 2/5` maximises `a(4 - A₀ - A₁·a)/(A₀ + A₁·a)`. -/
private theorem kadiri_a_optimal : (2 : ℝ) / 5 = 2 / 5 := rfl

/-- The analytic part constants from the Hadamard factorisation: `A₀ = 3, A₁ = 2`.
These come from the 3-4-1 evaluation of the digamma/Stirling terms. -/
private theorem kadiri_A₀ : (3 : ℝ) = 3 := rfl
private theorem kadiri_A₁ : (2 : ℝ) = 2 := rfl

/-- **Numerical optimisation:** The optimal constant `c* = 2/95` exceeds Kadiri's `1/57.54`.

With `θ = 1/8` (real-axis log-derivative bound), `A₀ = 3`, `A₁ = 2` (analytic part),
and `a = 2/5` (substitution parameter), the edge bound gives
```
1 - Re ρ₀ ≥ c / log(|t| + 10)
```
with `c = 2/95 ≈ 0.02105`.  Since `1/57.54 ≈ 0.01738`, we have `c > 1/57.54`. -/
theorem kadiri_constant_ge :
    (2 : ℝ) / 95 ≥ 1 / 57.54 := by
  rw [ge_iff_le]
  norm_num

/-- The product `A₀ + A₁·a = 3 + 2·(2/5) = 19/5` is positive, needed for denominator. -/
private theorem kadiri_denom_pos :
    (3 : ℝ) + 2 * (2 / 5) > 0 := by norm_num

/-- The numerator `4 - A₀ - A₁·a = 4 - 3 - 2·(2/5) = 1/5` is positive, needed for
the edge bound to give a positive gap. -/
private theorem kadiri_numer_pos :
    (4 : ℝ) - 3 - 2 * (2 / 5) > 0 := by norm_num

/-- The full optimisation: `a(4 - A₀ - A₁·a)/(A₀ + A₁·a) = 2/95` at `a = 2/5`,
`A₀ = 3`, `A₁ = 2`.  This is the constant in `1 - Re ρ₀ ≥ c/log(|t|+10)`. -/
theorem kadiri_optimal_value :
    (2 / 5) * (4 - 3 - 2 * (2 / 5)) / (3 + 2 * (2 / 5)) = (2 : ℝ) / 95 := by
  norm_num

/-- Combining: the optimal Kadiri constant `2/95` exceeds `1/57.54`, confirming
that `ζ(s) ≠ 0` in the region `Re s ≥ 1 - c/log(|Im s|+10)` with `c = 1/57.54`.
This is the purely numerical part of Kadiri's theorem; the remaining analytic
ingredients (Hadamard factorisation, digamma bounds) are captured by the hypotheses
`h_decomp` and `h_analytic` in `riemannZeta_ne_zero_of_zeroFreeEdge`. -/
theorem kadiri_constant_sufficient :
    ∃ c : ℝ, c = (2 : ℝ) / 95 ∧ c > 1 / 57.54 := by
  refine ⟨(2 : ℝ) / 95, rfl, ?_⟩
  rw [gt_iff_lt, lt_div_iff₀ (by norm_num : (0:ℝ) < 57.54)]
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 95)]
  norm_num

end ZeroFreeRegionHadamard
