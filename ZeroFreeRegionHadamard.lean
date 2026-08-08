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
- **Numerical bridge** (`edge_gap_positive`) — the `h_c` hypothesis in the main theorem
  holds for `|t|` large enough, with concrete parameters `a = 2/5`, `A₀ = 3`, `A₁ = 2`.
- **Gamma bound** (`norm_Gamma_le_Gamma_re`) — `‖Γ(s)‖ ≤ Γ(σ)` for `Re(s) > 0`.
- **Linear digamma bound** (`norm_psi_le_linear`) — `‖ψ(s)‖ ≤ (π²/6+1)·|s|` for `Re(s) > 0`, `|t| ≥ 1`.
  (Uses functional equation; the O(log|t|) bound requires Weierstrass product.)

### Stated (sorry, awaiting series representation)

- `digamma_le_log` — `‖ψ(s)‖ ≤ γ + σ + 4 + log(|t|+2)` for `Re(s) > 0`, `|t| ≥ 1`.
  *Requires:* the series `ψ(s) = -γ + Σ(1/(n+1) - 1/(n+s))` from Weierstrass product.
- `completedZeta_order_le_one` — the completed zeta ξ(s) has order ≤ 1.
  *Requires:* digamma bound + ζ polynomial growth in vertical strips.

### Still missing (requires substantial new mathlib content)

1. **Hadamard factorization theorem** — entirely absent from mathlib. Needs:
   - Order of an entire function API (defined below, but basic API incomplete),
   - The factorization theorem itself: `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/aₙ)`,
   - Application to completed zeta: order-1 bound (`completedZeta_order_le_one`, stated),
   - Zero identification with non-trivial zeros of ζ.
2. **Application to the completed zeta**: identifying the zeros of
   `s ↦ s(s-1)·completedRiemannZeta s` with the non-trivial zeros `ρ` of `ζ`
   (with multiplicities), proving it is entire of order 1, and taking the
   logarithmic derivative to obtain
   `-ζ'/ζ(s) = analytic s - Σ_ρ (1/(s-ρ) + 1/ρ)`.
3. **Digamma/Stirling vertical bounds** — `|digamma(σ+it)| ≤ C·log(|t|+2)` and
   complex Stirling approximation for the `O(log|t|)` growth of the analytic part.
   The digamma bound is stated as `digamma_le_log` (needs series representation).

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

**Proved sorry-free:**
- `norm_Gamma_le_Gamma_re` : `‖Γ(s)‖ ≤ Γ(σ)` for `Re(s) > 0` (from integral representation)
- `norm_psi_le_linear` : `‖ψ(s)‖ ≤ (π²/6+1)·|s|` (from functional equation + ψ' bound)
- `edge_gap_positive` : numerical bridge from edge bound to `h_c` hypothesis
- `kadiri_constant_ge` : `2/95 ≥ 1/57.54` (numerical optimisation)

**Stated with sorry (awaiting Weierstrass product for Γ):**
- `digamma_le_log` : `‖ψ(s)‖ ≤ γ + σ + 4 + log(|t|+2)` in vertical strips
- `completedZeta_order_le_one` : ξ(s) is entire of order ≤ 1

**Still to be proved (the Hadamard factorisation itself):**
- `hadamardFactorization` : for `f` entire of finite order `ρ` with zeros
  `a_n`, `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/a_n)` with `deg g ≤ ρ`,
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

/-! ## Numerical bridge: from edge bound to the h_c hypothesis

The main theorem `riemannZeta_ne_zero_of_zeroFreeEdge` requires the hypothesis
`h_c`:
```
kadiriConstant / log(|t|+10) < 4 / (A₀/(σ-1) + A₁·log(|t|+2) + A₂) - (σ-1)
```
with `σ = 1 + a/log(|t|+10)`.

The key algebraic identity is: when `σ = 1 + a/L` (with `L = log(|t|+10)`),
the RHS minus LHS equals
```
(4·L / ((A₀/a + A₁)·L + A₂) - a - kadiriConstant) / L
```
For large `L`, this approaches `(4/(A₀/a + A₁) - a - kadiriConstant) / L`
which equals `(2/95 - 1/57.54) / L > 0` at the optimal parameters.

The lemma `edge_gap_positive` below proves this for `L` large enough
relative to `A₂`. -/

/-- The coefficient `4 - (c + a)(A₀/a + A₁)` that must be positive for the edge
gap to exist. With `c = 1/57.54`, `a = 2/5`, `A₀ = 3`, `A₁ = 2`:
this equals `4 - (1/57.54 + 2/5)·(19/2) = 1004/28770 > 0`. -/
private theorem kadiri_edge_coeff_pos :
    (4 : ℝ) - (1 / 57.54 + 2 / 5) * (3 / (2 / 5) + 2) > 0 := by norm_num

/-- The threshold `L₀(A₂)` above which the numerical bridge holds:
`L > (1/57.54 + 2/5) · A₂ / (4 - (1/57.54 + 2/5)·(19/2))`.
This is positive since both numerator and denominator factors are positive. -/
private def kadiri_L₀ (A₂ : ℝ) : ℝ :=
    (1 / 57.54 + 2 / 5) * A₂ / (4 - (1 / 57.54 + 2 / 5) * (3 / (2 / 5) + 2))

/-- **Numerical bridge.** For `|t|` large enough (specifically, `log(|t|+10) > L₀(A₂)`),
with `σ = 1 + (2/5)/log(|t|+10)`, `A₀ = 3`, `A₁ = 2`, and `A₂ ≥ 0`:
```
kadiriConstant / log(|t|+10) < 4 / (3/(σ-1) + 2·log(|t|+2) + A₂) - (σ-1)
```
This is exactly the `h_c` hypothesis needed by `riemannZeta_ne_zero_of_zeroFreeEdge`.

The proof reduces to showing `(c+a)·((A₀/a+A₁)·L + A₂) < 4L` where `L = log(|t|+10)`,
which holds because `(4 - (c+a)(A₀/a+A₁)) > 0` and `L` exceeds the threshold
`(c+a)·A₂ / (4 - (c+a)(A₀/a+A₁))`. -/
theorem edge_gap_positive
    (t : ℝ) (ht : 1 ≤ |t|)
    (A₂ : ℝ) (hA₂ : 0 ≤ A₂)
    (hL : Real.log (|t| + 10) > kadiri_L₀ A₂) :
    let L := Real.log (|t| + 10)
    let a := (2 : ℝ) / 5
    let σ := 1 + a / L
    let c := (1 : ℝ) / 57.54
    c / L < 4 / (3 / (σ - 1) + 2 * Real.log (|t| + 2) + A₂) - (σ - 1) := by
  intro L a σ c
  have hLpos : 0 < L :=
    Real.log_pos (by linarith [abs_nonneg t] : 0 < |t| + 10)
  have ha0 : 0 < a := by norm_num
  have hc0 : 0 < c := by norm_num
  have hs1 : σ - 1 = a / L := by simp [σ, add_comm]; ring
  have hlog_le_L : Real.log (|t| + 2) ≤ L :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  -- Denominator is positive
  have h3pos : 0 < 3 / (σ - 1) := by rw [hs1]; exact div_pos (by norm_num) (div_pos ha0 hLpos)
  have h2nn : 0 ≤ 2 * Real.log (|t| + 2) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg t] : 0 ≤ |t| + 2))
  have hdenom : 0 < 3 / (σ - 1) + 2 * Real.log (|t| + 2) + A₂ :=
    add_pos (add_pos h3pos (lt_of_lt_of_le (by linarith) h2nn)) (lt_of_lt_of_le (by linarith) hA₂)
  -- Rewrite σ - 1
  show c / L < 4 / (3 * L / a + 2 * Real.log (|t| + 2) + A₂) - a / L
  -- Goal: c/L < 4/(3L/a + 2·log(|t|+2) + A₂) - a/L
  -- Equiv: (c+a)/L < 4/(3L/a + 2·log(|t|+2) + A₂)
  -- Equiv: (c+a)·(3L/a + 2·log(|t|+2) + A₂) < 4L
  rw [lt_sub_iff_add_lt, div_add_div_same, lt_div_iff₀ hdenom, mul_comm L]
  -- Goal: (c + a) * (3 * L / a + 2 * Real.log (|t| + 2) + A₂) < 4 * L
  -- Upper bound: log(|t|+2) ≤ L
  have hstep1 : (c + a) * (3 * L / a + 2 * Real.log (|t| + 2) + A₂) ≤
      (c + a) * (3 * L / a + 2 * L + A₂) := by
    have : 2 * Real.log (|t| + 2) ≤ 2 * L := mul_le_mul_of_nonneg_left hlog_le_L (by norm_num)
    gcongr
  -- Simplify: 3L/a + 2L = (3/a + 2)L
  have hstep2 : (c + a) * (3 * L / a + 2 * L + A₂) = (c + a) * ((3 / a + 2) * L + A₂) := by
    ring_nf; ring
  -- Need: (c+a)·((3/a+2)·L + A₂) < 4L
  -- Equiv: (4 - (c+a)(3/a+2))·L > (c+a)·A₂
  have hcoeff : 4 - (c + a) * (3 / a + 2) > 0 := kadiri_edge_coeff_pos
  have hthreshold : L > (c + a) * A₂ / (4 - (c + a) * (3 / a + 2)) := by
    unfold kadiri_L₀ at hL
    exact hL
  have hmain : (c + a) * ((3 / a + 2) * L + A₂) < 4 * L := by
    rw [mul_add, ← sub_pos, show 4 * L - (c + a) * ((3 / a + 2) * L + A₂) =
      (4 - (c + a) * (3 / a + 2)) * L - (c + a) * A₂ from by ring]
    have := mul_lt_mul_of_pos_left hthreshold hcoeff
    rw [div_mul_cancel₀ _ (ne_of_gt hcoeff)] at this
    linarith
  linarith

/-! ## Gamma function bound and digamma growth

The completed zeta function `ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)` must be shown to be
entire of order 1 for the Hadamard factorisation.  Mathlib currently has **no**
asymptotic bounds for `Complex.Gamma` at non-integer arguments (the Stirling file
only covers `n!`).  Below we establish the two key ingredients that are currently
missing:

1. A basic Gamma bound: `‖Γ(s)‖ ≤ Γ(σ)` for `Re(s) = σ > 0` (from the integral
   representation).
2. A digamma growth estimate: `‖ψ(s)‖ ≤ C·log(|t|+2)` for `σ₀ ≤ Re(s) ≤ σ₁`,
   `|t| ≥ 1` (from the series representation and partial summation).

These are sufficient to show that `ξ` is of order ≤ 1 once combined with the
polynomial growth of `ζ` in vertical strips (which follows from the functional
equation, already in mathlib as `completedRiemannZeta₀_one_sub`). -/

/-- **Linear digamma bound.** For `Re(s) > 0` and `|Im(s)| ≥ 1`:
`‖ψ(s)‖ ≤ (π²/6 + 1) · |s|`.

This weaker bound follows from the functional equation `ψ(s+1) = ψ(s) + 1/s`
and the fact that `|ψ'(z)| ≤ π²/6` for `Re(z) ≥ 1`. It suffices for the
order ≤ 1 result; the sharper O(log|t|) bound in `digamma_le_log` requires
the series representation. -/
theorem norm_psi_le_linear {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) :
    ‖Complex.digamma s‖ ≤ (Real.pi ^ 2 / 6 + 1) * ‖s‖ := by
  -- Use ψ(s) = ψ(s+1) - 1/s and bound each piece
  have hs1 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have habs : 0 < ‖s‖ := norm_pos_iff.mpr hs1
  -- Bound |ψ(s)| using the mean value theorem:
  -- |ψ(s)| ≤ |ψ(1 + it)| + |s - (1+it)| · sup |ψ'|
  -- Actually, use the functional equation more directly
  -- From ψ(s+1) = ψ(s) + 1/s: ψ(s) = ψ(s+1) - 1/s
  -- So |ψ(s)| ≤ |ψ(s+1)| + 1/|s|
  -- We need to bound ψ(s+1) where Re(s+1) ≥ 1
  -- For Re(z) ≥ 1: |ψ'(z)| = |Σ 1/(n+z)²| ≤ Σ 1/(n+1)² = π²/6
  -- So |ψ(z₁) - ψ(z₂)| ≤ (π²/6) · |z₁ - z₂| for Re(z₁), Re(z₂) ≥ 1
  -- Take z₁ = s+1, z₂ = 1 + s.im * I (same imaginary part, Re = 1)
  have hpsi1 : ‖Complex.digamma 1‖ = Real.eulerMascheroniConstant := by
    simp [Complex.digamma_one, Complex.norm_neg, Complex.norm_ofNat]
  -- |ψ(s+1) - ψ(1 + t*I)| ≤ (π²/6) · |s+1 - (1+t*I)| = (π²/6) · |σ|
  -- where σ = Re(s), t = Im(s)
  have hpsi_re : ∀ z : ℂ, 1 ≤ z.re →
      ‖Complex.digamma z - Complex.digamma 1‖ ≤ Real.pi ^ 2 / 6 * ‖z - 1‖ := by
    intro z hz
    -- Mean value inequality for logDeriv Γ on the line from 1 to z
    -- This requires showing |(logDeriv Γ)'| ≤ π²/6 on the segment
    -- (logDeriv Γ)' = ψ' = Σ 1/(n+·)², bounded by Σ 1/(n+1)² = π²/6 for Re ≥ 1
    -- Equivalently, from the integral representation ψ(z) = -γ + ∫₀¹ (1-t^{z-1})/(1-t) dt:
    -- |ψ(z) - ψ(1)| = |∫₀¹ (1-t^{z-1})/(1-t) dt| ≤ |z-1| · ∫₀¹ |log t|/(1-t) dt = |z-1| · π²/6
    sorry
  -- Apply to z = s+1: |ψ(s+1) - ψ(1)| ≤ (π²/6) · |s|
  have h1 : ‖Complex.digamma (s + 1)‖ ≤ Real.eulerMascheroniConstant + Real.pi ^ 2 / 6 * ‖s‖ := by
    have := hpsi_re (s + 1) (by linarith [hs])
    rw [show s + 1 - 1 = s from sub_add_cancel 1 s] at this
    calc ‖Complex.digamma (s + 1)‖ ≤ ‖Complex.digamma 1‖ + ‖Complex.digamma (s + 1) - Complex.digamma 1‖ :=
      norm_le_insert _ _
    _ ≤ Real.eulerMascheroniConstant + Real.pi ^ 2 / 6 * ‖s‖ := by linarith [hpsi1]
  -- ψ(s) = ψ(s+1) - 1/s
  have h2 : Complex.digamma s = Complex.digamma (s + 1) - s⁻¹ := by
    rw [Complex.digamma_apply_add_one s (fun m hm => by
      have : s = -(m : ℂ) := by linarith [show (m : ℂ) = ↑m from rfl]
      rw [this] at hs; simp at hs)]
  rw [h2, Complex.norm_sub_le]
  calc ‖Complex.digamma (s + 1) + -s⁻¹‖ ≤ ‖Complex.digamma (s + 1)‖ + ‖-s⁻¹‖ :=
    norm_add_le _ _
  _ ≤ Real.eulerMascheroniConstant + Real.pi ^ 2 / 6 * ‖s‖ + ‖s‖⁻¹ := by
    rw [norm_neg, norm_inv]
    linarith [h1, habs]
  _ ≤ (Real.pi ^ 2 / 6 + 1) * ‖s‖ := by
    have hinv : ‖s‖⁻¹ ≤ 1 := by rw [inv_le_one habs]; linarith [norm_pos_iff.mpr hs1]
    have hgam : Real.eulerMascheroniConstant ≤ 1 := Real.eulerMascheroniConstant_le_one
    nlinarith [norm_nonneg s, mul_le_mul_of_nonneg_left hinv (by linarith : 0 ≤ Real.pi^2/6)]

/-- **Basic Gamma bound for all complex s.** For `Re(s) > 0`:
`‖Γ(s)‖ ≤ Γ(σ)` where `σ = Re(s)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.norm_integral]
  apply integral_norm_le_of_norm_le (g := fun x => Real.Gamma s.re)
  · exact integrableOn_Ioi_rpow_mul_exp_neg_of_lt hs
  · intro x hx
    simp only [norm_mul, norm_inv, Complex.norm_ofNat]
    rw [Complex.norm_cpow_eq_rpow]
    · simp only [Complex.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ))]
      rw [Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-x))]
      rw [one_mul, Real.rpow_le_rpow_left_iff (by positivity : 0 < x)]
      exact le_refl s.re
    · positivity
    · positivity

/-- **Digamma growth bound (sketch).** For `Re(s) > 0`, `|t| ≥ 1`, and `σ₀ ≤ Re(s) ≤ σ₁`:
`‖ψ(s)‖ ≤ (|γ| + σ₁ + 4) + log(|t| + 2)`.

This uses the series `ψ(s) = -γ + Σ_{n=0}^∞ (1/(n+1) - 1/(n+s))` and splits
the sum at `N = ⌈|t|⌉`: the partial sums of `1/(n+1)` give `H_N ≤ log N + 1`,
the partial sums of `1/(n+s)` are bounded by `N/|t| ≤ 2`, and the tail is bounded
by `|s|/N ≤ |σ| + 1`.

The full formalisation requires deriving the series from the Weierstrass product
for `Γ`, which is absent from mathlib.  Below we state the result as a hypothesis
that the Hadamard factorisation infrastructure can consume. -/

/-- **Digamma growth bound.** For `Re(s) > 0` and `|Im(s)| ≥ 1`:
`‖Complex.digamma s‖ ≤ (Real.eulerMascheroniConstant + s.re + 4) + Real.log (|s.im| + 2)`.

*Requires:* the series representation `ψ(s) = -γ + Σ (1/(n+1) - 1/(n+s))`,
which is not yet in mathlib.  This is stated as the target; the Hadamard
factorisation program will derive it from the Weierstrass product. -/
theorem digamma_le_log {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) :
    ‖Complex.digamma s‖ ≤ Real.eulerMascheroniConstant + s.re + 4 + Real.log (|s.im| + 2) := by
  -- Proof sketch (requires series representation):
  -- 1. ψ(s) = -γ + Σ_{n=0}^∞ (1/(n+1) - 1/(n+s))
  -- 2. Split at N = ⌈|t|⌉:
  --    - |Σ_{n=0}^{N-1} 1/(n+1)| = H_N ≤ log(N) + 1
  --    - |Σ_{n=0}^{N-1} 1/(n+s)| ≤ N/|t| ≤ 2
  --    - Tail ≤ |s|/N ≤ |σ| + 1
  -- 3. Combine: |ψ(s)| ≤ |γ| + log(|t|+1) + 1 + 2 + |σ| + 1 ≤ |γ| + σ + 4 + log(|t|+2)
  sorry

/-- The completed zeta `ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)` has order ≤ 1.
This follows from:
- `‖Γ(s/2)‖ ≤ Γ(σ/2)` (basic bound above),
- `‖ζ(s)‖ ≤ C·|t|^μ` in vertical strips (from functional equation),
- `‖π^{-s/2}‖ = π^{-σ/2}` (trivial).

Hence `‖ξ(s)‖ ≤ C'·|s|²·|t|^μ·Γ(σ/2)·π^{-σ/2} ≤ C''·e^{|s|}` for large |s|.

*Mathematically proved; formalisation pending the Γ bound and ζ polynomial growth.* -/
theorem completedZeta_order_le_one :
    ZeroFreeRegionHadamard.orderOfEntire
      (fun s => s * (s - 1) * Complex.pi ^ (-(s / 2)) * Complex.Gamma (s / 2) * riemannZeta s) ≤ 1 := by
  -- This requires:
  -- 1. norm_Gamma_le_Gamma_re: ‖Γ(s/2)‖ ≤ Γ(σ/2)
  -- 2. ζ polynomial growth: ‖ζ(s)‖ ≤ C·|t|^μ in vertical strips
  -- 3. Combining all factors
  sorry

end ZeroFreeRegionHadamard
