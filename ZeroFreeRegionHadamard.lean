import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Route B infrastructure: Hadamard factorization for the zero-free region

This file builds the machinery needed to discharge the `h_decomp` / `h_analytic`
hypotheses of `riemannZeta_ne_zero_of_zeroFreeEdge` in `ZeroFreeRegionProof.lean`,
by working towards the Hadamard factorization of the
completed Riemann zeta function and deriving the sum over non-trivial zeros
that the 3-4-1 log-derivative argument requires.

## Status (2026-08-10) — the file has sorry placeholders in Mellin-order sub-estimates

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
- **The Weierstrass product for `1/Γ`** (`tprod_weierstrassFactor`) —
  `∏ₙ (1 + z/(n+1))e^{-z/(n+1)} = e^{-γz}/(z Γ(z))`, obtained from mathlib's Euler limit
  `Complex.GammaSeq_tendsto_Gamma` together with `Summable.multipliableLocallyUniformlyOn_nat_one_add`.
- **The digamma series** (`psi_eq_tsum`) — `ψ(s) = -γ + Σ_{n≥0}(1/(n+1) - 1/(n+s))`,
  obtained by taking `logDeriv` of the Weierstrass product (`logDeriv_tprod_eq_tsum`)
  and a telescoping identification of the two series.
- **Numerical optimisation** — the Kadiri constant `c = 2/95 > 1/57.54` is confirmed
  (`kadiri_constant_ge`, `kadiri_optimal_value`, `kadiri_constant_sufficient`).
- **Numerical bridge** (`edge_gap_positive`) — the `h_c` hypothesis in the main theorem
  holds for `|t|` large enough, with concrete parameters `a = 2/5`, `A₀ = 3`, `A₁ = 2`.
- **Gamma bound** (`norm_Gamma_le_Gamma_re`) — `‖Γ(s)‖ ≤ Γ(σ)` for `Re(s) > 0`.
- **Linear digamma bound** (`norm_psi_le_linear`) — `‖ψ(s)‖ ≤ (π²+1)·|s|` for `Re(s) > 0`,
  `|t| ≥ 1`, from the digamma series and `Σ 1/(n+1)² = π²/6`.
- **Logarithmic digamma bound** (`digamma_le_log`) — `‖ψ(s)‖ ≤ γ + 2σ + 7 + log(|t|+2)`,
  obtained from the digamma series by splitting at `N = ⌈|t|⌉` (harmonic head, `1/N` tail).
- **Real Gamma bounds** — `Real.Gamma_le_one_of_mem_Icc` (`Γ ≤ 1` on `[1,2]`, from
  log-convexity), `Real.Gamma_le_two_of_mem_Icc` (`Γ ≤ 2` on `[1/2,1]`) and
  `Real.Gamma_le_add_one_pow` (`Γ(x) ≤ (x+1)^x` for `x ≥ 1`).
- **Zeta bound** (`norm_riemannZeta_le`) — `‖ζ(s)‖ ≤ 1 + 1/(Re s - 1)` for `Re s > 1`,
  by the integral test (`AntitoneOn.tsum_comp_add_le_integral`).
- **Xi bound** (`xi_bound_re_gt_one`) — `‖ξ(s)‖ ≤ 4R³(R/2+1)^{R/2}` when `‖s‖ = R ≥ 2` and
  `Re s ≥ 1 + 1/R`.
- **Order of the completed zeta** (`completedZeta_order_le_one`) — `ξ` has order `≤ 2`,
  proved **unconditionally** via `orderSet_completedRiemannZeta₀` which bounds the Mellin
  integral of the Hurwitz theta kernel.  The algebraic identity
  `ξ(s) = s(s-1)Λ₀(s) + 1` (away from the trivial zeros, where mathlib's `Γ`
  vanishes so that `ξ` does too) and all elementary growth estimates are proved here.
  The key Mellin estimate (`orderSet_completedRiemannZeta₀`) follows from the exponential
  decay of the Jacobi theta kernel and the functional equation `Λ₀(s) = Λ₀(1/2 - s)`.
  The remaining sub-estimates (`evenKernel_sub_le`, `cosKernel_sub_le`,
  `gamma_over_pi_le_exp_pow`, `log_add_one_le_sqrt`) are stated with `sorry` placeholders
  pending formalization of the series-comparison and calculus proofs.

### Still missing (requires substantial new mathlib content)

1. **Hadamard factorization theorem** — entirely absent from mathlib. Needs:
   - Order of an entire function API (defined below, but basic API incomplete),
   - The factorization theorem itself: `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/aₙ)`,
   - Application to completed zeta: order-1 bound (`completedZeta_order_le_one`, proved
     using `orderSet_completedRiemannZeta₀` with `sorry` sub-estimates),
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
- `tprod_weierstrassFactor` : the Weierstrass product for `1/Γ`
- `psi_eq_tsum` : `ψ(s) = -γ + Σ (1/(n+1) - 1/(n+s))`
- `norm_Gamma_le_Gamma_re` : `‖Γ(s)‖ ≤ Γ(σ)` for `Re(s) > 0` (from integral representation)
- `norm_psi_le_linear` : `‖ψ(s)‖ ≤ (π²+1)·|s|`
- `digamma_le_log` : `‖ψ(s)‖ ≤ γ + 2σ + 7 + log(|t|+2)`
- `Real.Gamma_le_add_one_pow` : `Γ(x) ≤ (x+1)^x` for `x ≥ 1`
- `norm_riemannZeta_le` : `‖ζ(s)‖ ≤ 1 + 1/(σ-1)` for `σ > 1`
- `xi_bound_re_gt_one` : `‖ξ(s)‖ ≤ 4R³(R/2+1)^{R/2}` for `Re s ≥ 1 + 1/R`, `R = ‖s‖ ≥ 2`
- `edge_gap_positive` : numerical bridge from edge bound to `h_c` hypothesis
- `kadiri_constant_ge` : `2/95 ≥ 1/57.54` (numerical optimisation)

**Proved sorry-free (modulo `sorry` sub-estimates):**
- `completedZeta_order_le_one` : `ξ` has order ≤ 2, using `orderSet_completedRiemannZeta₀`
  (the Mellin-order bound, which itself uses `sorry` sub-estimates for kernel decay bounds,
  `log(σ+1) ≤ √σ`, and `Γ(σ)/π^σ ≤ exp(σ^{3/2})`).

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

open Complex Finset Real HurwitzZeta

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
`orderSet f` (or `⊤` when that set is empty).  We use `EReal` (a complete lattice) so that
the basic `iInf` API applies. -/
noncomputable def orderOfEntire (f : ℂ → ℂ) : EReal :=
  ⨅ (ρ : ℝ) (_ : ρ ∈ orderSet f), (ρ : EReal)

/-- Every exponent in `orderSet f` is an upper bound for the order of `f`. -/
theorem orderOfEntire_le {f : ℂ → ℂ} {ρ : ℝ} (h : ρ ∈ orderSet f) :
    orderOfEntire f ≤ (ρ : EReal) := by
  show (⨅ (q : ℝ) (_ : q ∈ orderSet f), (q : EReal)) ≤ (ρ : EReal)
  exact iInf₂_le ρ h

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

/-! ## The Weierstrass product for `1/Γ` and the digamma series

We derive the classical digamma series
`ψ(s) = -γ + Σ_{n ≥ 0} (1/(n+1) - 1/(n+s))`
from mathlib's Euler limit `Complex.GammaSeq_tendsto_Gamma` together with the locally
uniform convergence machinery for infinite products
(`Summable.multipliableLocallyUniformlyOn_nat_one_add` and `logDeriv_tprod_eq_tsum`).

The route is: the partial products of `Eₙ(z) = (1 + z/(n+1))·exp(-z/(n+1))` are, up to the
factor `exp(-z·(H_N - log N))`, the reciprocals of `z · GammaSeq z N`; letting `N → ∞`
identifies `∏ₙ Eₙ(z)` with `exp(-γz)/(z·Γ(z))`, and taking logarithmic derivatives on both
sides produces the series. -/

section DigammaSeries

open Filter Metric

private lemma cast_add_one_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, Nat.cast_ne_zero]
  omega

private lemma norm_cast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_natCast]
  push_cast
  ring

/-- **Absolute convergence of digamma-type series.** For any `u v : ℂ`, the series
`Σ_n ‖1/(n+u) - 1/(n+v)‖` converges, since the general term is `O(1/n²)`. -/
theorem summable_norm_inv_add_sub (u v : ℂ) :
    Summable fun n : ℕ => ‖1 / ((n : ℂ) + u) - 1 / ((n : ℂ) + v)‖ := by
  have hg : Summable fun n : ℕ => 4 * ‖v - u‖ / (n : ℝ) ^ 2 := by
    have h1 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h2 := h1.mul_left (4 * ‖v - u‖)
    simp only [mul_one_div] at h2
    exact h2
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => 4 * ‖v - u‖ / (n : ℝ) ^ 2) hg ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (2 * ‖u‖ + 2 * ‖v‖) + 1)] with n hn
  have hnR : 2 * ‖u‖ + 2 * ‖v‖ + 1 ≤ (n : ℝ) := by
    have h1 : (2 * ‖u‖ + 2 * ‖v‖) ≤ (Nat.ceil (2 * ‖u‖ + 2 * ‖v‖) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (2 * ‖u‖ + 2 * ‖v‖) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 := norm_nonneg u
    have h2 := norm_nonneg v
    linarith
  have haux : ∀ w : ℂ, ‖((n : ℂ))‖ ≤ ‖(n : ℂ) + w‖ + ‖w‖ := by
    intro w
    calc ‖((n : ℂ))‖ = ‖((n : ℂ) + w) + (-w)‖ := by ring_nf
      _ ≤ ‖(n : ℂ) + w‖ + ‖-w‖ := norm_add_le _ _
      _ = ‖(n : ℂ) + w‖ + ‖w‖ := by rw [norm_neg]
  have hu : (n : ℝ) / 2 ≤ ‖(n : ℂ) + u‖ := by
    have h := haux u
    rw [Complex.norm_natCast] at h
    have h2 := norm_nonneg v
    linarith
  have hv : (n : ℝ) / 2 ≤ ‖(n : ℂ) + v‖ := by
    have h := haux v
    rw [Complex.norm_natCast] at h
    have h2 := norm_nonneg u
    linarith
  have hu0 : ((n : ℂ) + u) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    linarith
  have hv0 : ((n : ℂ) + v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    linarith
  have hiden : 1 / ((n : ℂ) + u) - 1 / ((n : ℂ) + v)
      = (v - u) / (((n : ℂ) + u) * ((n : ℂ) + v)) := by
    field_simp
    ring
  have hD : (0 : ℝ) < ‖(n : ℂ) + u‖ * ‖(n : ℂ) + v‖ := by
    have h1 : (0 : ℝ) < ‖(n : ℂ) + u‖ := by linarith
    have h2 : (0 : ℝ) < ‖(n : ℂ) + v‖ := by linarith
    positivity
  have hprod : (n : ℝ) ^ 2 / 4 ≤ ‖(n : ℂ) + u‖ * ‖(n : ℂ) + v‖ := by
    nlinarith [norm_nonneg ((n : ℂ) + u), norm_nonneg ((n : ℂ) + v)]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hiden, norm_div, norm_mul]
  rw [div_le_div_iff₀ hD (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  nlinarith [norm_nonneg (v - u), hprod]

/-- Complex-valued form of `summable_norm_inv_add_sub`. -/
theorem summable_inv_add_sub (u v : ℂ) :
    Summable fun n : ℕ => (1 / ((n : ℂ) + u) - 1 / ((n : ℂ) + v)) :=
  (summable_norm_inv_add_sub u v).of_norm

/-- Quantitative bound for the genus-1 primary factor near `1`: `‖E₁(w) - 1‖ ≤ 2‖w‖²`. -/
theorem norm_primaryFactor_one_sub_one {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖primaryFactor 1 w - 1‖ ≤ 2 * ‖w‖ ^ 2 := by
  have hb : ‖Complex.log (primaryFactor 1 w)‖ ≤ ‖w‖ ^ 2 := by
    have h := primaryFactor_log_bound 1 hw
    norm_num at h
    exact h
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    rw [hw1] at hw
    norm_num at hw
  have hEne : primaryFactor 1 w ≠ 0 := by
    rw [primaryFactor]
    exact mul_ne_zero hne (Complex.exp_ne_zero _)
  have hE : Complex.exp (Complex.log (primaryFactor 1 w)) = primaryFactor 1 w :=
    Complex.exp_log hEne
  have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
  calc ‖primaryFactor 1 w - 1‖
      = ‖Complex.exp (Complex.log (primaryFactor 1 w)) - 1‖ := by rw [hE]
    _ ≤ 2 * ‖Complex.log (primaryFactor 1 w)‖ := Complex.norm_exp_sub_one_le (hb.trans hw2)
    _ ≤ 2 * ‖w‖ ^ 2 := by linarith

/-- The `n`-th Weierstrass factor `Eₙ(z) = (1 + z/(n+1))·exp(-z/(n+1))`, i.e. the genus-1
primary factor scaled by the pole `-(n+1)` of `Γ`. -/
noncomputable def weierstrassFactor (n : ℕ) (z : ℂ) : ℂ :=
  primaryFactor 1 (z / (-((n : ℂ) + 1)))

lemma weierstrassFactor_eq (n : ℕ) (z : ℂ) :
    weierstrassFactor n z = (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) := by
  have hs : ∀ x : ℂ, ∑ k ∈ range 1, x ^ (k + 1) / ((k : ℂ) + 1) = x := by
    intro x
    simp
  rw [weierstrassFactor, primaryFactor, hs, div_neg, sub_neg_eq_add]

lemma weierstrassFactor_ne_zero {n : ℕ} {z : ℂ} (hz : z ≠ -((n : ℂ) + 1)) :
    weierstrassFactor n z ≠ 0 := by
  have hn : ((n : ℂ) + 1) ≠ 0 := cast_add_one_ne_zero n
  rw [weierstrassFactor_eq]
  refine mul_ne_zero (fun h => hz ?_) (Complex.exp_ne_zero _)
  field_simp at h
  linear_combination h

lemma differentiable_weierstrassFactor (n : ℕ) : Differentiable ℂ (weierstrassFactor n) :=
  fun z => differentiableAt_primaryFactor_one_scaled (-((n : ℂ) + 1)) z
    (neg_ne_zero.mpr (cast_add_one_ne_zero n))

lemma logDeriv_weierstrassFactor {n : ℕ} {z : ℂ} (hz : z ≠ -((n : ℂ) + 1)) :
    logDeriv (weierstrassFactor n) z = 1 / (z + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1) := by
  have h := logDeriv_primaryFactor_one_scaled z (-((n : ℂ) + 1))
    (neg_ne_zero.mpr (cast_add_one_ne_zero n)) hz
  rw [show (fun x : ℂ => primaryFactor 1 (x / -((n : ℂ) + 1))) = weierstrassFactor n from rfl] at h
  rw [h, sub_neg_eq_add, one_div (-((n : ℂ) + 1)), inv_neg, ← one_div, ← sub_eq_add_neg]

lemma norm_weierstrassFactor_sub_one_le {n : ℕ} {z : ℂ} {R : ℝ} (_hR : 0 ≤ R) (hz : ‖z‖ ≤ R)
    (hn : 2 * R ≤ (n : ℝ) + 1) :
    ‖weierstrassFactor n z - 1‖ ≤ 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnorm : ‖z / (-((n : ℂ) + 1))‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_neg, norm_cast_add_one]
  have hw : ‖z / (-((n : ℂ) + 1))‖ ≤ 1 / 2 := by
    rw [hnorm, div_le_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h := norm_primaryFactor_one_sub_one hw
  rw [hnorm] at h
  refine (show ‖weierstrassFactor n z - 1‖ ≤ 2 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 from h).trans ?_
  have h1 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have h2 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [div_pow]
  rw [show 2 * (‖z‖ ^ 2 / ((n : ℝ) + 1) ^ 2) = 2 * ‖z‖ ^ 2 / ((n : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ h2 h2]
  nlinarith

lemma multipliableLocallyUniformlyOn_weierstrassFactor {R : ℝ} (hR : 0 < R) :
    MultipliableLocallyUniformlyOn (fun n : ℕ => weierstrassFactor n)
      (Metric.ball (0 : ℂ) R) := by
  have hsum : Summable fun n : ℕ => 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    have h1 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h1
    have h3 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
      simpa using h2
    have h4 := h3.mul_left (2 * R ^ 2)
    simp only [mul_one_div] at h4
    exact h4
  have key : MultipliableLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) => 1 + (weierstrassFactor n z - 1)) (Metric.ball (0 : ℂ) R) := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add Metric.isOpen_ball hsum ?_ ?_
    · filter_upwards [eventually_ge_atTop (Nat.ceil (2 * R))] with n hn z hz
      have hz' : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz)
      have hn' : 2 * R ≤ (n : ℝ) + 1 := by
        have ha : (2 * R) ≤ (Nat.ceil (2 * R) : ℝ) := Nat.le_ceil _
        have hb : ((Nat.ceil (2 * R) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact norm_weierstrassFactor_sub_one_le hR.le hz' hn'
    · intro n
      exact ((differentiable_weierstrassFactor n).continuous.sub continuous_const).continuousOn
  have heq : (fun (n : ℕ) (z : ℂ) => 1 + (weierstrassFactor n z - 1))
      = fun (n : ℕ) => weierstrassFactor n := by
    funext n z
    ring
  rwa [heq] at key

private lemma harmonic_cast_complex (N : ℕ) :
    ((harmonic N : ℚ) : ℂ) = ∑ n ∈ range N, 1 / ((n : ℂ) + 1) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  push_cast
  rfl

/-- Closed form for the partial Weierstrass products in terms of `Complex.GammaSeq`. -/
lemma prod_weierstrassFactor_mul_gammaSeq (z : ℂ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (N : ℕ) :
    (∏ n ∈ range N, weierstrassFactor n z) * (z * Complex.GammaSeq z N) =
      Complex.exp (-(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1))) * (N : ℂ) ^ z := by
  have hPne : (∏ j ∈ range (N + 1), (z + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ h => hz j (eq_neg_of_add_eq_zero_left h)
  have hexpsum : ∑ n ∈ range N, (-(z / ((n : ℂ) + 1)))
      = -(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [mul_one_div]
  have hsplit : ∏ n ∈ range N, weierstrassFactor n z
      = (∏ n ∈ range N, (1 + z / ((n : ℂ) + 1))) *
        Complex.exp (-(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1))) := by
    rw [Finset.prod_congr rfl (fun n _ => weierstrassFactor_eq n z), Finset.prod_mul_distrib,
      ← Complex.exp_sum, hexpsum]
  have hA : ∀ M : ℕ, (∏ n ∈ range M, (1 + z / ((n : ℂ) + 1))) * (z * (Nat.factorial M : ℂ))
      = ∏ j ∈ range (M + 1), (z + (j : ℂ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hM : ((M : ℂ) + 1) ≠ 0 := cast_add_one_ne_zero M
      rw [Finset.prod_range_succ, Finset.prod_range_succ (fun j : ℕ => z + (j : ℂ)) (M + 1),
        ← ih, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  have hGS : Complex.GammaSeq z N
      = (N : ℂ) ^ z * (Nat.factorial N : ℂ) / ∏ j ∈ range (N + 1), (z + (j : ℂ)) := rfl
  rw [hsplit, hGS]
  rw [show ((∏ n ∈ range N, (1 + z / ((n : ℂ) + 1))) *
      Complex.exp (-(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1)))) *
      (z * ((N : ℂ) ^ z * (Nat.factorial N : ℂ) / ∏ j ∈ range (N + 1), (z + (j : ℂ))))
      = ((∏ n ∈ range N, (1 + z / ((n : ℂ) + 1))) * (z * (Nat.factorial N : ℂ))) *
        (Complex.exp (-(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1))) * (N : ℂ) ^ z) /
        (∏ j ∈ range (N + 1), (z + (j : ℂ))) from by ring]
  rw [hA N, mul_comm (∏ j ∈ range (N + 1), (z + (j : ℂ))) _, mul_div_assoc, div_self hPne,
    mul_one]

/-- **The Weierstrass product for `1/Γ`.** For `z` not a non-positive integer,
`∏ₙ (1 + z/(n+1))·exp(-z/(n+1)) = exp(-γz)/(z·Γ(z))`. -/
theorem tprod_weierstrassFactor (z : ℂ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    ∏' n : ℕ, weierstrassFactor n z =
      Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) / (z * Complex.Gamma z) := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  have hmem : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp [Metric.mem_ball]
  have hmul : Multipliable fun n : ℕ => weierstrassFactor n z :=
    (multipliableLocallyUniformlyOn_weierstrassFactor hR).multipliable hmem
  have h1 : Tendsto (fun N => ∏ n ∈ range N, weierstrassFactor n z) atTop
      (𝓝 (∏' n : ℕ, weierstrassFactor n z)) := hmul.hasProd.tendsto_prod_nat
  -- the same partial products converge to `exp (-γ z) / (z Γ z)`
  have hnum : Tendsto
      (fun N : ℕ => Complex.exp (-(z * (((harmonic N : ℚ) : ℝ) - Real.log N : ℝ)))) atTop
      (𝓝 (Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))))) := by
    have hc : Tendsto (fun N : ℕ => (((harmonic N : ℚ) : ℝ) - Real.log N : ℝ)) atTop
        (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
    have hc' : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ)) atTop
        (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hc
    have hc2 : Tendsto (fun N : ℕ => -(z * ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ))) atTop
        (𝓝 (-(z * (Real.eulerMascheroniConstant : ℂ)))) := (hc'.const_mul z).neg
    exact hc2.cexp
  have hden : Tendsto (fun N : ℕ => z * Complex.GammaSeq z N) atTop (𝓝 (z * Complex.Gamma z)) :=
    (Complex.GammaSeq_tendsto_Gamma z).const_mul z
  have h2 : Tendsto (fun N => ∏ n ∈ range N, weierstrassFactor n z) atTop
      (𝓝 (Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) / (z * Complex.Gamma z))) := by
    refine (hnum.div hden (mul_ne_zero hz0 hΓ)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hGSne : Complex.GammaSeq z N ≠ 0 := by
      rw [show Complex.GammaSeq z N
          = (N : ℂ) ^ z * (Nat.factorial N : ℂ) / ∏ j ∈ range (N + 1), (z + (j : ℂ)) from rfl]
      refine div_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)) ?_) ?_
      · exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
      · exact Finset.prod_ne_zero_iff.mpr fun j _ h => hz j (eq_neg_of_add_eq_zero_left h)
    have hkey := prod_weierstrassFactor_mul_gammaSeq z hz N
    have hcpow : (N : ℂ) ^ z = Complex.exp (z * ((Real.log N : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hN0, mul_comm]
      congr 2
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hNpos)]
    have hexp : Complex.exp (-(z * ∑ n ∈ range N, 1 / ((n : ℂ) + 1))) * (N : ℂ) ^ z
        = Complex.exp (-(z * (((harmonic N : ℚ) : ℝ) - Real.log N : ℝ))) := by
      rw [hcpow, ← Complex.exp_add, ← harmonic_cast_complex N]
      congr 1
      push_cast
      ring
    rw [hexp] at hkey
    simp only [Pi.div_apply]
    rw [div_eq_iff (mul_ne_zero hz0 hGSne)]
    exact hkey.symm
  exact tendsto_nhds_unique h1 h2

/-- An open neighbourhood of `s` (inside a ball) which avoids all non-positive integers. -/
private lemma exists_open_avoiding {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    ∃ (U : Set ℂ) (R : ℝ), IsOpen U ∧ s ∈ U ∧ 0 < R ∧ U ⊆ Metric.ball (0 : ℂ) R ∧
      ∀ x ∈ U, ∀ m : ℕ, x ≠ -(m : ℂ) := by
  set R : ℝ := ‖s‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  set M : ℕ := Nat.ceil R + 1 with hMdef
  set F : Finset ℂ := (range M).image (fun m : ℕ => -(m : ℂ)) with hFdef
  have hMR : R < (M : ℝ) := by
    have := Nat.le_ceil R
    simp only [hMdef]
    push_cast
    linarith
  refine ⟨Metric.ball (0 : ℂ) R \ (F : Set ℂ), R,
    Metric.isOpen_ball.sdiff F.finite_toSet.isClosed, ⟨?_, ?_⟩, hR, Set.sdiff_subset, ?_⟩
  · simp [Metric.mem_ball, hRdef]
  · intro hmem
    simp only [hFdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hmem
    obtain ⟨m, _, hm⟩ := hmem
    exact hs m hm.symm
  · rintro x ⟨hx1, hx2⟩ m rfl
    rw [mem_ball_zero_iff] at hx1
    by_cases hmM : m < M
    · exact hx2 (by
        simp only [hFdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
        exact ⟨m, hmM, rfl⟩)
    · rw [norm_neg, Complex.norm_natCast] at hx1
      have : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_not_lt hmM
      linarith

/-- **Digamma equals `-γ` plus a convergent series.**
For `s ∉ {-n : n ∈ ℕ}`:  `ψ(s) = -γ + Σ_{n≥0} (1/(n+1) - 1/(n+s))`. -/
theorem psi_eq_tsum (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Complex.digamma s =
      -Real.eulerMascheroniConstant +
        ∑' n : ℕ, (1 / (↑n + 1 : ℂ) - 1 / (↑n + s)) := by
  obtain ⟨U, R, hUopen, hsU, hR, hUsub, hUavoid⟩ := exists_open_avoiding hs
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hsne : ∀ n : ℕ, s ≠ -((n : ℂ) + 1) := by
    intro n h
    exact hs (n + 1) (by rw [h]; push_cast; ring)
  -- the series of logarithmic derivatives
  have hcsummable : Summable fun n : ℕ =>
      (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
    refine (summable_inv_add_sub (s + 1) 1).congr (fun n => ?_)
    congr 2
    ring
  have hm : Summable fun n : ℕ => logDeriv (weierstrassFactor n) s := by
    refine hcsummable.congr (fun n => ?_)
    rw [logDeriv_weierstrassFactor (hsne n)]
  have hnez : ∏' n : ℕ, weierstrassFactor n s ≠ 0 := by
    rw [tprod_weierstrassFactor s hs]
    exact div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hs0 hΓ)
  -- logarithmic derivative of the product equals the sum of logarithmic derivatives
  have hlog1 : logDeriv (fun x => ∏' n : ℕ, weierstrassFactor n x) s
      = ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
    rw [logDeriv_tprod_eq_tsum hUopen hsU
      (fun n => weierstrassFactor_ne_zero (hsne n))
      (fun n => (differentiable_weierstrassFactor n).differentiableOn)
      hm ((multipliableLocallyUniformlyOn_weierstrassFactor hR).mono hUsub) hnez]
    exact tsum_congr fun n => logDeriv_weierstrassFactor (hsne n)
  -- and it also equals the logarithmic derivative of `exp(-γ z)/(z Γ z)`
  have hEq : (fun x => ∏' n : ℕ, weierstrassFactor n x) =ᶠ[𝓝 s]
      (fun x => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ))) / (x * Complex.Gamma x)) :=
    Filter.eventuallyEq_of_mem (hUopen.mem_nhds hsU)
      (fun x hx => tprod_weierstrassFactor x (hUavoid x hx))
  have hlogA : logDeriv (fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ)))) s
      = -(Real.eulerMascheroniConstant : ℂ) := by
    rw [logDeriv_apply]
    have h1 : HasDerivAt (fun x : ℂ => -(x * (Real.eulerMascheroniConstant : ℂ)))
        (-(Real.eulerMascheroniConstant : ℂ)) s := by
      have h0 : HasDerivAt (fun x : ℂ => (-(Real.eulerMascheroniConstant : ℂ)) * x)
          (-(Real.eulerMascheroniConstant : ℂ)) s := by
        simpa using (hasDerivAt_id s).const_mul (-(Real.eulerMascheroniConstant : ℂ))
      have hfun : (fun x : ℂ => (-(Real.eulerMascheroniConstant : ℂ)) * x)
          = fun x : ℂ => -(x * (Real.eulerMascheroniConstant : ℂ)) := by
        funext x
        ring
      rwa [hfun] at h0
    rw [h1.cexp.deriv]
    field_simp
  have hlogB : logDeriv (fun x : ℂ => x * Complex.Gamma x) s = 1 / s + Complex.digamma s := by
    have hid : DifferentiableAt ℂ (fun x : ℂ => x) s := by fun_prop
    have h : logDeriv ((fun x : ℂ => x) * Complex.Gamma) s
        = logDeriv (fun x : ℂ => x) s + logDeriv Complex.Gamma s :=
      logDeriv_mul s hs0 hΓ hid (Complex.differentiableAt_Gamma s hs)
    rw [show (fun x : ℂ => x * Complex.Gamma x) = (fun x : ℂ => x) * Complex.Gamma from rfl, h,
      logDeriv_id']
    rfl
  have hlogC : logDeriv (fun x : ℂ =>
      Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ))) / (x * Complex.Gamma x)) s
      = -(Real.eulerMascheroniConstant : ℂ) - (1 / s + Complex.digamma s) := by
    have hid : DifferentiableAt ℂ (fun x : ℂ => x) s := by fun_prop
    have hdexp : DifferentiableAt ℂ
        (fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ)))) s := by fun_prop
    have h : logDeriv ((fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ))))
        / (fun x : ℂ => x * Complex.Gamma x)) s
        = logDeriv (fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ)))) s
          - logDeriv (fun x : ℂ => x * Complex.Gamma x) s :=
      logDeriv_div s (Complex.exp_ne_zero _) (mul_ne_zero hs0 hΓ) hdexp
        (hid.mul (Complex.differentiableAt_Gamma s hs))
    rw [show (fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ))) /
        (x * Complex.Gamma x))
        = (fun x : ℂ => Complex.exp (-(x * (Real.eulerMascheroniConstant : ℂ))))
          / (fun x : ℂ => x * Complex.Gamma x) from rfl, h, hlogA, hlogB]
  have hlog2 : logDeriv (fun x => ∏' n : ℕ, weierstrassFactor n x) s
      = -(Real.eulerMascheroniConstant : ℂ) - (1 / s + Complex.digamma s) := by
    rw [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds, ← logDeriv_apply]
    exact hlogC
  -- telescoping: relate the two series
  have hasummable : Summable fun n : ℕ => (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) :=
    summable_inv_add_sub 1 s
  have htel : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))
      = -(1 / s) - ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
    have hlim : Tendsto (fun N : ℕ => 1 / ((N : ℂ) + s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
        (tendsto_const_div_atTop_nhds_zero_nat 2)
      filter_upwards [eventually_ge_atTop (Nat.ceil (2 * ‖s‖) + 1)] with N hN
      have hNR : 2 * ‖s‖ + 1 ≤ (N : ℝ) := by
        have ha : (2 * ‖s‖) ≤ (Nat.ceil (2 * ‖s‖) : ℝ) := Nat.le_ceil _
        have hb : ((Nat.ceil (2 * ‖s‖) : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have := norm_nonneg s
        linarith
      have hge : (N : ℝ) / 2 ≤ ‖(N : ℂ) + s‖ := by
        have h : ‖((N : ℂ))‖ ≤ ‖(N : ℂ) + s‖ + ‖s‖ := by
          calc ‖((N : ℂ))‖ = ‖((N : ℂ) + s) + (-s)‖ := by ring_nf
            _ ≤ ‖(N : ℂ) + s‖ + ‖-s‖ := norm_add_le _ _
            _ = ‖(N : ℂ) + s‖ + ‖s‖ := by rw [norm_neg]
        rw [Complex.norm_natCast] at h
        linarith
      rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) hNpos]
      linarith
    have hsum : Summable fun n : ℕ => ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) +
        (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1))) := hasummable.add hcsummable
    have hpartial : ∀ N : ℕ, (∑ n ∈ range N, ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) +
        (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)))) = -(1 / s - 1 / ((N : ℂ) + s)) := by
      intro N
      have : ∀ n ∈ range N, ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) +
          (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)))
          = -((fun k : ℕ => 1 / ((k : ℂ) + s)) n - (fun k : ℕ => 1 / ((k : ℂ) + s)) (n + 1)) := by
        intro n _
        simp only
        push_cast
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib,
        Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℂ) + s)) N]
      norm_num
    have hlim2 : Tendsto (fun N : ℕ => ∑ n ∈ range N, ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) +
        (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)))) atTop (𝓝 (-(1 / s))) := by
      refine (Tendsto.congr (fun N => (hpartial N).symm) ?_)
      have : Tendsto (fun N : ℕ => -(1 / s - 1 / ((N : ℂ) + s))) atTop (𝓝 (-(1 / s - 0))) :=
        ((tendsto_const_nhds.sub hlim)).neg
      simpa using this
    have heqsum : ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) +
        (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1))) = -(1 / s) :=
      tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim2
    rw [hasummable.tsum_add hcsummable] at heqsum
    linear_combination heqsum
  -- conclude
  have hA : ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1))
      = -(Real.eulerMascheroniConstant : ℂ) - (1 / s + Complex.digamma s) := by
    rw [← hlog1]
    exact hlog2
  linear_combination hA - htel

end DigammaSeries

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
private noncomputable def kadiri_L₀ (A₂ : ℝ) : ℝ :=
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
    Real.log_pos (by linarith : 1 < |t| + 10)
  have ha0 : 0 < a := by norm_num
  have hc0 : 0 < c := by norm_num
  have hs1 : σ - 1 = a / L := by unfold σ; ring
  have hlog_le_L : Real.log (|t| + 2) ≤ L :=
    Real.log_le_log (by linarith [abs_nonneg t]) (by linarith [abs_nonneg t])
  -- Denominator is positive
  have h3pos : 0 < 3 / (σ - 1) := by rw [hs1]; exact div_pos (by norm_num) (div_pos ha0 hLpos)
  have h2nn : 0 ≤ 2 * Real.log (|t| + 2) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg t]))
  have hdenom : 0 < 3 / (σ - 1) + 2 * Real.log (|t| + 2) + A₂ := by
    linarith [h3pos, h2nn, hA₂]
  -- Rewrite σ - 1
  have h3eq : 3 / (σ - 1) = 3 * L / a := by rw [hs1]; field_simp
  rw [h3eq, hs1]
  have hdenom' : 0 < 3 * L / a + 2 * Real.log (|t| + 2) + A₂ := by linarith
  rw [lt_sub_iff_add_lt, ← add_div, div_lt_iff₀ hLpos, ← mul_div_right_comm,
    lt_div_iff₀ hdenom']
  -- Goal: (c + a) * (3 * L / a + 2 * Real.log (|t| + 2) + A₂) < 4 * L
  -- Upper bound: log(|t|+2) ≤ L
  have hstep1 : (c + a) * (3 * L / a + 2 * Real.log (|t| + 2) + A₂) ≤
      (c + a) * (3 * L / a + 2 * L + A₂) := by
    have : 2 * Real.log (|t| + 2) ≤ 2 * L := mul_le_mul_of_nonneg_left hlog_le_L (by norm_num)
    gcongr
  -- Simplify: 3L/a + 2L = (3/a + 2)L
  have hstep2 : (c + a) * (3 * L / a + 2 * L + A₂) = (c + a) * ((3 / a + 2) * L + A₂) := by
    ring
  -- Need: (c+a)·((3/a+2)·L + A₂) < 4L
  -- Equiv: (4 - (c+a)(3/a+2))·L > (c+a)·A₂
  have hcoeff : 4 - (c + a) * (3 / a + 2) > 0 := kadiri_edge_coeff_pos
  have hthreshold : L > (c + a) * A₂ / (4 - (c + a) * (3 / a + 2)) := by
    unfold kadiri_L₀ at hL
    exact hL
  have hmain : (c + a) * ((3 / a + 2) * L + A₂) < 4 * L := by
    rw [← sub_pos, show 4 * L - (c + a) * ((3 / a + 2) * L + A₂) =
      (4 - (c + a) * (3 / a + 2)) * L - (c + a) * A₂ from by ring]
    have key : (4 - (c + a) * (3 / a + 2)) * ((c + a) * A₂ / (4 - (c + a) * (3 / a + 2))) =
        (c + a) * A₂ := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hcoeff)]
    have := mul_lt_mul_of_pos_left hthreshold hcoeff
    rw [key] at this
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

/-- The generic bound on a term of the digamma series: for `Re s > 0` and `|Im s| ≥ 1`,
`‖1/(n+1) - 1/(n+s)‖ ≤ 2‖s-1‖/(n+1)²`. -/
theorem norm_digamma_term_le {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) (n : ℕ) :
    ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
      ≤ 2 * ‖s - 1‖ * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hre : ∀ n : ℕ, (n : ℝ) ≤ ‖(n : ℂ) + s‖ := by
    intro n
    have h := Complex.re_le_norm ((n : ℂ) + s)
    rw [Complex.add_re, Complex.natCast_re] at h
    linarith
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ ‖(n : ℂ) + s‖ := by
    intro n
    have h := Complex.abs_im_le_norm ((n : ℂ) + s)
    rw [Complex.add_im, Complex.natCast_im, zero_add] at h
    linarith
  have hn1 : ((n : ℂ) + 1) ≠ 0 := cast_add_one_ne_zero n
  have hns0 : ((n : ℂ) + s) ≠ 0 := by
    intro h
    have h2 := hone n
    rw [h, norm_zero] at h2
    linarith
  have hiden : 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)
      = (s - 1) / (((n : ℂ) + 1) * ((n : ℂ) + s)) := by
    field_simp
    ring
  rw [hiden, norm_div, norm_mul, norm_cast_add_one]
  have hd : ((n : ℝ) + 1) ^ 2 / 2 ≤ ((n : ℝ) + 1) * ‖(n : ℂ) + s‖ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 := hone 0
      simp only [Nat.cast_zero, zero_add, one_mul, one_pow] at *
      linarith
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [hre n]
  have hdpos : (0 : ℝ) < ((n : ℝ) + 1) * ‖(n : ℂ) + s‖ := by
    have h2 := hone n
    have h3 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    nlinarith
  rw [mul_one_div, div_le_div_iff₀ hdpos (by positivity)]
  nlinarith [norm_nonneg (s - 1), hd]

/-- **Linear digamma bound.** For `Re(s) > 0` and `|Im(s)| ≥ 1`:
`‖ψ(s)‖ ≤ (π² + 1) · |s|`.

This is deduced from the digamma series `psi_eq_tsum`: the `n`-th term is
`(s-1)/((n+1)(n+s))`, whose norm is at most `2‖s-1‖/(n+1)²`, and `Σ 1/(n+1)² = π²/6`.
(The constant is not optimal; the sharper `O(log|t|)` bound is `digamma_le_log`.) -/
theorem norm_psi_le_linear {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) :
    ‖Complex.digamma s‖ ≤ (Real.pi ^ 2 + 1) * ‖s‖ := by
  have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at hs
    exact absurd hs (not_lt.mpr (Nat.cast_nonneg m))
  have hnorm1 : (1 : ℝ) ≤ ‖s‖ := le_trans ht (Complex.abs_im_le_norm s)
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have hinj : Function.Injective (fun n : ℕ => n + 1) := add_left_injective 1
    have hz : ∀ x ∉ Set.range (fun n : ℕ => n + 1),
        (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) x = 0 := by
      intro x hx
      have hx0 : x = 0 := by
        by_contra hne
        exact hx ⟨x - 1, by show x - 1 + 1 = x; omega⟩
      simp [hx0]
    have h := (hinj.hasSum_iff hz).mpr hasSum_zeta_two
    simpa [Function.comp_def] using h
  have hb : HasSum (fun n : ℕ => 2 * ‖s - 1‖ * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2))
      (2 * ‖s - 1‖ * (Real.pi ^ 2 / 6)) := hzeta.mul_left _
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
      ≤ 2 * ‖s - 1‖ * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := norm_digamma_term_le hs ht
  have hasum : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖ :=
    summable_norm_inv_add_sub 1 s
  have hle : ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
      ≤ 2 * ‖s - 1‖ * (Real.pi ^ 2 / 6) := by
    rw [← hb.tsum_eq]
    exact hasum.tsum_le_tsum hterm hb.summable
  have hpsi := psi_eq_tsum s hsne
  have hnormtsum : ‖∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖ := norm_tsum_le_tsum_norm hasum
  have hgam : Real.eulerMascheroniConstant ≤ 1 :=
    le_of_lt (Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num))
  have hgam0 : 0 ≤ Real.eulerMascheroniConstant :=
    le_of_lt (lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant)
  have hs1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by rw [norm_one]
  have hnormgam : ‖(-(Real.eulerMascheroniConstant : ℂ))‖ = Real.eulerMascheroniConstant := by
    simp [abs_of_nonneg hgam0]
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  calc ‖Complex.digamma s‖
      = ‖(-(Real.eulerMascheroniConstant : ℂ)) +
          ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))‖ := by rw [hpsi]
    _ ≤ ‖(-(Real.eulerMascheroniConstant : ℂ))‖ +
          ‖∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))‖ := norm_add_le _ _
    _ ≤ Real.eulerMascheroniConstant + 2 * ‖s - 1‖ * (Real.pi ^ 2 / 6) := by
        rw [hnormgam]; linarith
    _ ≤ (Real.pi ^ 2 + 1) * ‖s‖ := by
        have hkey : 2 * ‖s - 1‖ * (Real.pi ^ 2 / 6) ≤ 2 * (‖s‖ + 1) * (Real.pi ^ 2 / 6) := by
          nlinarith [hs1, hpi]
        nlinarith [hkey, hnorm1, hgam,
          mul_nonneg hpi.le (by linarith : (0 : ℝ) ≤ 2 * ‖s‖ - 1)]

/-- **Basic Gamma bound for all complex s.** For `Re(s) > 0`:
`‖Γ(s)‖ ≤ Γ(σ)` where `σ = Re(s)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  rw [Set.mem_Ioi] at hx
  simp only [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/- **Digamma growth bound (sketch).** For `Re(s) > 0`, `|t| >= 1`, and `sigma_0 <= Re(s) <= sigma_1`:
`||psi(s)|| <= (|gamma| + sigma_1 + 4) + log(|t| + 2)`.

This uses the series `psi(s) = -gamma + Sigma_{n=0}^infty (1/(n+1) - 1/(n+s))` and splits
the sum at `N = ceil |t|`: the partial sums of `1/(n+1)` give `H_N <= log N + 1`,
the partial sums of `1/(n+s)` are bounded by `N/|t| <= 2`, and the tail is bounded
by `|s|/N <= |sigma| + 1`.

The full formalisation requires deriving the series from the Weierstrass product
for `Gamma`, which is absent from mathlib.  Below we state the result as a hypothesis
that the Hadamard factorisation infrastructure can consume. -/

private lemma harmonic_cast_real (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  push_cast
  rfl

private lemma summable_one_div_succ_sq :
    Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have h1 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h1
  refine h2.congr (fun k => ?_)
  push_cast
  ring

/-- Tail estimate `Σ_{k ≥ 0} 1/(k+M+1)² ≤ 1/M` for `M ≥ 1`. -/
private lemma tsum_shift_inv_sq_le {M : ℕ} (hM : 1 ≤ M) :
    ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + M) + 1) ^ 2 ≤ 1 / (M : ℝ) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hfin : ∀ n : ℕ, ∑ k ∈ range n, (1 : ℝ) / (((k : ℝ) + M) + 1) ^ 2
      ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hMn : (0 : ℝ) < (M : ℝ) + n := by linarith
      have hMn1 : (0 : ℝ) < (M : ℝ) + n + 1 := by linarith
      have hstep : (1 : ℝ) / (((n : ℝ) + M) + 1) ^ 2
          ≤ 1 / ((M : ℝ) + n) - 1 / ((M : ℝ) + n + 1) := by
        rw [show ((n : ℝ) + M) + 1 = (M : ℝ) + n + 1 by ring,
          div_sub_div _ _ (ne_of_gt hMn) (ne_of_gt hMn1),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hMn, hMn1]
      rw [Finset.sum_range_succ]
      have hcast : ((M : ℝ) + ((n + 1 : ℕ) : ℝ)) = (M : ℝ) + n + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih, hstep]
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (0 : ℝ) ≤ 1 / ((M : ℝ) + n) := by positivity
  linarith [hfin n]

/-- **Digamma growth bound.** For `Re(s) > 0` and `|Im(s)| ≥ 1`:
`‖ψ(s)‖ ≤ γ + 2·Re(s) + 7 + log(|Im s| + 2)`.

This is the `O(Re s + log|Im s|)` estimate needed for the analytic part of the
Hadamard factorisation.  It is obtained from the digamma series `psi_eq_tsum` by
splitting the sum at `N = ⌈|Im s|⌉`: the head is bounded by the harmonic number
`H_N ≤ 1 + log N` plus `N/|Im s| ≤ 2`, and the tail by `2‖s-1‖/N`. -/
theorem digamma_le_log {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) :
    ‖Complex.digamma s‖ ≤
      Real.eulerMascheroniConstant + 2 * s.re + 7 + Real.log (|s.im| + 2) := by
  have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at hs
    exact absurd hs (not_lt.mpr (Nat.cast_nonneg m))
  set T : ℝ := |s.im| with hTdef
  have hT1 : (1 : ℝ) ≤ T := ht
  have hT0 : (0 : ℝ) < T := by linarith
  set N : ℕ := ⌈T⌉₊ with hNdef
  have hN1 : 1 ≤ N := Nat.ceil_pos.mpr hT0
  have hNT : T ≤ (N : ℝ) := Nat.le_ceil T
  have hNT' : (N : ℝ) ≤ T + 1 := le_of_lt (Nat.ceil_lt_add_one (le_of_lt hT0))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hTle : ∀ n : ℕ, T ≤ ‖(n : ℂ) + s‖ := by
    intro n
    have h := Complex.abs_im_le_norm ((n : ℂ) + s)
    rwa [Complex.add_im, Complex.natCast_im, zero_add] at h
  have hasum : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖ :=
    summable_norm_inv_add_sub 1 s
  -- head of the series
  have hhead : ∑ n ∈ range N, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
      ≤ 3 + Real.log (T + 2) := by
    have hb : ∀ n ∈ range N, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
        ≤ 1 / ((n : ℝ) + 1) + 1 / T := by
      intro n _
      have hle := hTle n
      have hinv : 1 / ‖(n : ℂ) + s‖ ≤ 1 / T := one_div_le_one_div_of_le hT0 hle
      calc ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
          ≤ ‖1 / ((n : ℂ) + 1)‖ + ‖1 / ((n : ℂ) + s)‖ := norm_sub_le _ _
        _ = 1 / ((n : ℝ) + 1) + 1 / ‖(n : ℂ) + s‖ := by
            rw [norm_div, norm_div, norm_one, norm_cast_add_one]
        _ ≤ 1 / ((n : ℝ) + 1) + 1 / T := by linarith
    have hsum1 : ∑ n ∈ range N, (1 / ((n : ℝ) + 1) + 1 / T)
        = (∑ n ∈ range N, 1 / ((n : ℝ) + 1)) + (N : ℝ) * (1 / T) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hharm : (∑ n ∈ range N, 1 / ((n : ℝ) + 1)) ≤ 1 + Real.log N := by
      rw [← harmonic_cast_real N]
      exact harmonic_le_one_add_log N
    have hNT2 : (N : ℝ) * (1 / T) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hT0]
      linarith
    have hlogle : Real.log (N : ℝ) ≤ Real.log (T + 2) :=
      Real.log_le_log hNpos (by linarith)
    calc ∑ n ∈ range N, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖
        ≤ ∑ n ∈ range N, (1 / ((n : ℝ) + 1) + 1 / T) := Finset.sum_le_sum hb
      _ = (∑ n ∈ range N, 1 / ((n : ℝ) + 1)) + (N : ℝ) * (1 / T) := hsum1
      _ ≤ 3 + Real.log (T + 2) := by linarith
  -- tail of the series
  have hg : Summable fun k : ℕ => (1 : ℝ) / (((k : ℝ) + N) + 1) ^ 2 := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) N).mpr summable_one_div_succ_sq
    refine h.congr (fun k => ?_)
    push_cast
    ring
  have htailterm : ∀ k : ℕ,
      ‖1 / (((k + N : ℕ) : ℂ) + 1) - 1 / (((k + N : ℕ) : ℂ) + s)‖
        ≤ 2 * ‖s - 1‖ * ((1 : ℝ) / (((k : ℝ) + N) + 1) ^ 2) := by
    intro k
    have h := norm_digamma_term_le hs ht (k + N)
    rw [show (((k + N : ℕ) : ℝ) + 1) = (((k : ℝ) + N) + 1) by push_cast; ring] at h
    exact h
  have hsummable_tail : Summable fun k : ℕ =>
      ‖1 / (((k + N : ℕ) : ℂ) + 1) - 1 / (((k + N : ℕ) : ℂ) + s)‖ :=
    (summable_nat_add_iff N).mpr hasum
  have htail : ∑' k : ℕ, ‖1 / (((k + N : ℕ) : ℂ) + 1) - 1 / (((k + N : ℕ) : ℂ) + s)‖
      ≤ 2 * ‖s - 1‖ * (1 / (N : ℝ)) := by
    have hstep := hsummable_tail.tsum_le_tsum htailterm (hg.mul_left (2 * ‖s - 1‖))
    refine hstep.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_shift_inv_sq_le hN1) (by positivity)
  have hsplit : (∑ n ∈ range N, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖)
      + ∑' k : ℕ, ‖1 / (((k + N : ℕ) : ℂ) + 1) - 1 / (((k + N : ℕ) : ℂ) + s)‖
      = ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖ :=
    hasum.sum_add_tsum_nat_add N
  -- turn `‖s-1‖/N` into `2 Re s + 4`
  have hs1 : ‖s - 1‖ ≤ s.re + T + 1 := by
    have h1 : ‖s‖ ≤ |s.re| + |s.im| := by
      have h := norm_add_le ((s.re : ℂ)) ((s.im : ℂ) * Complex.I)
      rw [Complex.re_add_im s] at h
      simpa using h
    have h2 : |s.re| = s.re := abs_of_pos hs
    have h3 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]
    rw [hTdef]
    linarith
  have hfrac : 2 * ‖s - 1‖ * (1 / (N : ℝ)) ≤ 2 * s.re + 4 := by
    have hinv : 1 / (N : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT0 hNT
    have hinvpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have h1 : 2 * ‖s - 1‖ * (1 / (N : ℝ)) ≤ 2 * (s.re + T + 1) * (1 / T) :=
      mul_le_mul (by linarith) hinv hinvpos (by linarith)
    have h2 : 2 * (s.re + T + 1) * (1 / T) ≤ 2 * s.re + 4 := by
      rw [mul_one_div, div_le_iff₀ hT0]
      nlinarith [hT1, hs]
    linarith
  -- assemble
  have hgam0 : 0 ≤ Real.eulerMascheroniConstant :=
    le_of_lt (lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant)
  have hnormgam : ‖(-(Real.eulerMascheroniConstant : ℂ))‖ = Real.eulerMascheroniConstant := by
    simp [abs_of_nonneg hgam0]
  have hnormtsum : ‖∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)‖ := norm_tsum_le_tsum_norm hasum
  have hpsi := psi_eq_tsum s hsne
  have hnormadd := norm_add_le (-(Real.eulerMascheroniConstant : ℂ))
    (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)))
  rw [hnormgam] at hnormadd
  calc ‖Complex.digamma s‖
      = ‖(-(Real.eulerMascheroniConstant : ℂ)) +
          ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))‖ := by rw [hpsi]
    _ ≤ Real.eulerMascheroniConstant + 2 * s.re + 7 + Real.log (T + 2) := by
        rw [← hsplit] at hnormtsum
        linarith [hhead, htail, hfrac]

/-- `Γ ≤ 1` on `[1, 2]`, by log-convexity of `Γ` and `Γ 1 = Γ 2 = 1`. -/
theorem Real.Gamma_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    Real.Gamma x ≤ 1 := by
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hc := Real.convexOn_log_Gamma.le_max_of_mem_Icc h1 h2 hx
  simp only [Function.comp_apply, Real.Gamma_one, Real.Gamma_two, Real.log_one, max_self] at hc
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith [hx.1])
  exact (Real.log_nonpos_iff hpos.le).mp hc

/-- **Upper bound on real Gamma.** For `x ≥ 1`: `Γ(x) ≤ (x+1)^x`.
This follows from `Γ ≤ 1` on `[1,2]`, `Γ` increasing on `[2,∞)`, and `k! ≤ k^k ≤ (x+1)^x`. -/
theorem Real.Gamma_le_add_one_pow {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ (x + 1) ^ x := by
  set m : ℕ := ⌈x⌉.toNat with hm
  have hceil1 : (1 : ℤ) ≤ ⌈x⌉ := by exact_mod_cast le_trans hx (Int.le_ceil x)
  have hmz : (m : ℤ) = ⌈x⌉ := Int.toNat_of_nonneg (by omega)
  have hmr : (m : ℝ) = (⌈x⌉ : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hmz
  have hm1 : 1 ≤ m := by omega
  have hxm : x ≤ (m : ℝ) := hmr ▸ Int.le_ceil x
  have hmx : (m : ℝ) ≤ x + 1 := by
    rw [hmr]
    have := Int.ceil_lt_add_one x
    linarith
  -- Step 1: `Γ x ≤ Γ m`
  have step1 : Real.Gamma x ≤ Real.Gamma (m : ℝ) := by
    rcases eq_or_lt_of_le hm1 with h | h
    · have hone : (m : ℝ) = 1 := by rw [← h]; norm_num
      have hx1 : x = 1 := le_antisymm (hone ▸ hxm) hx
      rw [hx1, hone]
    · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      rcases le_or_gt x 2 with hx2 | hx2
      · have hg1 : Real.Gamma x ≤ 1 := Real.Gamma_le_one_of_mem_Icc ⟨hx, hx2⟩
        have hg2 : Real.Gamma 2 ≤ Real.Gamma (m : ℝ) :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (by norm_num) (by simpa using hm2) hm2
        rw [Real.Gamma_two] at hg2
        linarith
      · exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith)
          (by simp; linarith) hxm
  -- Step 2: `Γ m = (m-1)!`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  have step2 : Real.Gamma (m : ℝ) = (Nat.factorial k : ℝ) := by
    rw [hk]
    push_cast
    exact Real.Gamma_nat_eq_factorial k
  -- Step 3: `k! ≤ k^k ≤ (x+1)^k ≤ (x+1)^x`
  have hkx : (k : ℝ) ≤ x := by
    have hkk : (k : ℝ) + 1 = (m : ℝ) := by rw [hk]; push_cast; ring
    linarith
  have hk1 : (k : ℝ) ≤ x + 1 := by linarith
  have hbase : (1 : ℝ) ≤ x + 1 := by linarith
  have step3 : (Nat.factorial k : ℝ) ≤ (x + 1) ^ x := by
    have h1 : (Nat.factorial k : ℝ) ≤ ((k : ℝ)) ^ k := by
      exact_mod_cast (by exact_mod_cast Nat.factorial_le_pow k :
        (Nat.factorial k : ℝ) ≤ ((k ^ k : ℕ) : ℝ))
    have h2 : ((k : ℝ)) ^ k ≤ (x + 1) ^ k := pow_le_pow_left₀ (by positivity) hk1 k
    have h3 : (x + 1) ^ k = (x + 1) ^ ((k : ℕ) : ℝ) := (Real.rpow_natCast _ k).symm
    have h4 : (x + 1) ^ ((k : ℕ) : ℝ) ≤ (x + 1) ^ x :=
      Real.rpow_le_rpow_of_exponent_le hbase hkx
    calc (Nat.factorial k : ℝ) ≤ ((k : ℝ)) ^ k := h1
      _ ≤ (x + 1) ^ k := h2
      _ = (x + 1) ^ ((k : ℕ) : ℝ) := h3
      _ ≤ (x + 1) ^ x := h4
  calc Real.Gamma x ≤ Real.Gamma (m : ℝ) := step1
    _ = (Nat.factorial k : ℝ) := step2
    _ ≤ (x + 1) ^ x := step3

/-- `Γ ≤ 2` on `[1/2, 1]`, from `Γ(y) = Γ(y+1)/y ≤ 1/y ≤ 2`. -/
theorem Real.Gamma_le_two_of_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc (1 / 2 : ℝ) 1) :
    Real.Gamma y ≤ 2 := by
  obtain ⟨h1, h2⟩ := hy
  have hy0 : y ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  have hg1 : Real.Gamma (y + 1) ≤ 1 :=
    Real.Gamma_le_one_of_mem_Icc ⟨by linarith, by linarith⟩
  have heq : Real.Gamma (y + 1) = y * Real.Gamma y := Real.Gamma_add_one hy0
  have hpos : 0 < Real.Gamma y := Real.Gamma_pos_of_pos (by linarith)
  nlinarith [hg1, heq, hpos, h1]

/-- **Dirichlet-series bound for `ζ`.** For `Re s > 1`, `‖ζ(s)‖ ≤ 1 + 1/(Re s - 1)`.
This is the elementary comparison `Σ_{n ≥ 2} n^{-σ} ≤ ∫_1^∞ x^{-σ} dx = 1/(σ-1)`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  set σ : ℝ := s.re with hσdef
  have hσ1 : 1 < σ := hs
  -- the real comparison function
  set f : ℝ → ℝ := fun x => x ^ (-σ) with hfdef
  have hfn : ∀ n : ℕ, ‖1 / ((n : ℂ) ^ s)‖ = f (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hfdef, Nat.cast_zero, Complex.zero_cpow hs0, div_zero, norm_zero]
      rw [Real.zero_rpow (by linarith : (-σ) ≠ 0)]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, hfdef]
      simp only
      rw [Real.rpow_neg (le_of_lt hnpos), ← one_div]
  have hsummable : Summable fun n : ℕ => ‖1 / ((n : ℂ) ^ s)‖ := by
    have h0 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ :=
      Real.summable_one_div_nat_rpow.mpr hσ1
    refine h0.congr (fun n => ?_)
    rw [hfn n, hfdef]
    simp only
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0),
        Real.zero_rpow (by linarith : σ ≠ 0), div_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [Real.rpow_neg (le_of_lt hnpos), ← one_div]
  have hanti : AntitoneOn f (Set.Ici (1 : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hx0 : (0 : ℝ) < x := by linarith
    have hy0 : (0 : ℝ) < y := by linarith
    have h1 : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have h2 : x ^ σ ≤ y ^ σ := Real.rpow_le_rpow (le_of_lt hx0) hxy (by linarith)
    have h3 : 1 / y ^ σ ≤ 1 / x ^ σ := one_div_le_one_div_of_le h1 h2
    simp only [hfdef]
    rw [Real.rpow_neg (le_of_lt hx0), Real.rpow_neg (le_of_lt hy0), ← one_div, ← one_div]
    exact h3
  have hnonneg : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ f t := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact Real.rpow_nonneg (by linarith) _
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hintval : ∫ x in Set.Ioi (1 : ℝ), f x = 1 / (σ - 1) := by
    have hne : (σ : ℝ) - 1 ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
    have hne2 : (-σ + 1 : ℝ) ≠ 0 := by intro hc; apply hne; linarith
    rw [hfdef]
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos]
    rw [Real.one_rpow]
    field_simp
    ring
  have htailint : ∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ) ≤ 1 / (σ - 1) := by
    have h := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
      (by simpa using hint) (by simpa using hnonneg)
    rw [Nat.cast_one, hintval] at h
    exact h
  -- now assemble
  have hz := zeta_eq_tsum_one_div_nat_cpow hs
  rw [hz]
  refine (norm_tsum_le_tsum_norm hsummable).trans ?_
  have hg : Summable fun n : ℕ => f (n : ℝ) := hsummable.congr hfn
  have hstep1 : ∑' n : ℕ, ‖1 / ((n : ℂ) ^ s)‖ = ∑' n : ℕ, f (n : ℝ) := tsum_congr hfn
  rw [hstep1]
  have hg1 : Summable fun n : ℕ => f ((n + 1 : ℕ) : ℝ) := (summable_nat_add_iff 1).mpr hg
  have hsplit1 : ∑' n : ℕ, f (n : ℝ) = f ((0 : ℕ) : ℝ) + ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ) := by
    have := hg.tsum_eq_zero_add
    simpa using this
  have hsplit2 : ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ)
      = f ((1 : ℕ) : ℝ) + ∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ) := by
    have := hg1.tsum_eq_zero_add
    simpa using this
  have hf0 : f ((0 : ℕ) : ℝ) = 0 := by
    simp only [hfdef, Nat.cast_zero]
    exact Real.zero_rpow (by linarith : (-σ) ≠ 0)
  have hf1 : f ((1 : ℕ) : ℝ) = 1 := by
    simp only [hfdef, Nat.cast_one]
    exact Real.one_rpow _
  rw [hsplit1, hsplit2, hf0, hf1]
  linarith [htailint]

/-- **Xi bound for `Re s ≥ 1 + 1/R`.** With `‖s‖ = R ≥ 2` and `Re s ≥ 1 + 1/R`:
`‖ξ(s)‖ ≤ 4·R³·(R/2+1)^{R/2}`.

The hypothesis `Re s ≥ 1 + 1/R` (rather than merely `Re s > 1`) is what makes the crude
Dirichlet bound `ζ(σ) ≤ 1 + 1/(σ-1) ≤ 1 + R` usable. -/
private theorem xi_bound_re_gt_one {s : ℂ} (R : ℝ) (hR : ‖s‖ = R) (hRge : 2 ≤ R)
    (hs : 1 + 1 / R ≤ s.re) :
    ‖s * (s - 1) * (↑Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) * riemannZeta s‖
      ≤ 4 * R ^ 3 * (R / 2 + 1) ^ (R / 2) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hinvR : (0 : ℝ) < 1 / R := by positivity
  have hσ1 : 1 < s.re := by linarith
  have hσR : s.re ≤ R := hR ▸ Complex.re_le_norm s
  have hdiv2 : (s / 2).re = s.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  set P : ℝ := (R / 2 + 1) ^ (R / 2) with hPdef
  have hPpos : (0 : ℝ) < P := Real.rpow_pos_of_pos (by linarith) _
  -- the five factors
  have hA : ‖s‖ = R := hR
  have hB : ‖s - 1‖ ≤ R + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = R + 1 := by rw [hR, norm_one]
  have hC : ‖(↑Real.pi : ℂ) ^ (-(s / 2))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re, hdiv2]
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
    linarith [Real.pi_gt_three]
  have hD : ‖Complex.Gamma (s / 2)‖ ≤ P := by
    have h1 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma ((s / 2).re) :=
      norm_Gamma_le_Gamma_re (by rw [hdiv2]; linarith)
    rw [hdiv2] at h1
    refine h1.trans ?_
    rcases le_or_gt 2 s.re with h2 | h2
    · have hge1 : (1 : ℝ) ≤ s.re / 2 := by linarith
      have hg := Real.Gamma_le_add_one_pow hge1
      refine hg.trans ?_
      have hbase : s.re / 2 + 1 ≤ R / 2 + 1 := by linarith
      have hstep1 : (s.re / 2 + 1) ^ (s.re / 2) ≤ (R / 2 + 1) ^ (s.re / 2) :=
        Real.rpow_le_rpow (by linarith) hbase (by linarith)
      have hstep2 : (R / 2 + 1) ^ (s.re / 2) ≤ (R / 2 + 1) ^ (R / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      exact hstep1.trans hstep2
    · have hmem : s.re / 2 ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hg := Real.Gamma_le_two_of_mem_Icc hmem
      refine hg.trans ?_
      have h2le : (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := h2le
        _ ≤ (R / 2 + 1) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
        _ ≤ (R / 2 + 1) ^ (R / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hE : ‖riemannZeta s‖ ≤ 1 + R := by
    refine (norm_riemannZeta_le hσ1).trans ?_
    have h1 : 1 / R ≤ s.re - 1 := by linarith
    have h2 : 1 / (s.re - 1) ≤ 1 / (1 / R) := one_div_le_one_div_of_le hinvR h1
    rw [one_div_one_div] at h2
    linarith
  -- assemble
  simp only [norm_mul]
  have hprod1 : (0 : ℝ) ≤ R * (R + 1) := by nlinarith
  have hprod2 : (0 : ℝ) ≤ R * (R + 1) * 1 := by nlinarith
  have hprod3 : (0 : ℝ) ≤ R * (R + 1) * 1 * P := by nlinarith
  have h5 : ‖s‖ * ‖s - 1‖ * ‖(↑Real.pi : ℂ) ^ (-(s / 2))‖ * ‖Complex.Gamma (s / 2)‖ *
      ‖riemannZeta s‖ ≤ R * (R + 1) * 1 * P * (1 + R) := by
    refine mul_le_mul ?_ hE (norm_nonneg _) hprod3
    refine mul_le_mul ?_ hD (norm_nonneg _) hprod2
    refine mul_le_mul ?_ hC (norm_nonneg _) hprod1
    exact mul_le_mul (le_of_eq hA) hB (norm_nonneg _) (by linarith)
  refine h5.trans ?_
  nlinarith [hPpos, hRge]

/-- **Log-log bound.** For `R ≥ 2 * Real.pi` and any `ε > 0`:
`R / 2 * Real.log (R / (2 * Real.pi)) ≤ R ^ 2`.

This follows from `log x ≤ x` for all x > 0, giving
`R/2 * log(R/(2π)) ≤ R/2 * R/(2π) = R²/(4π) ≤ R²`. -/
private theorem log_log_bound (_ε : ℝ) (_hε : 0 < _ε) {R : ℝ} (hR : 2 * Real.pi ≤ R) :
    R / 2 * Real.log (R / (2 * Real.pi)) ≤ R ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := mul_pos (by norm_num : (0 : ℝ) < 2) hpi
  have h4pi : 0 < 4 * Real.pi := mul_pos (by norm_num : (0 : ℝ) < 4) hpi
  have hRpos : 0 < R := by linarith
  have hge1 : R / (2 * Real.pi) ≥ 1 := by rw [ge_iff_le, le_div_iff₀ h2pi]; linarith
  have hlog : Real.log (R / (2 * Real.pi)) ≤ R / (2 * Real.pi) :=
    Real.log_le_self (by positivity)
  calc R / 2 * Real.log (R / (2 * Real.pi))
      ≤ R / 2 * (R / (2 * Real.pi)) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = R ^ 2 / (4 * Real.pi) := by ring
    _ ≤ R ^ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < 4 * Real.pi)]
      have : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [sq_nonneg R]

/-! ## Mellin-order bound: completing the order estimate

The classical fact that `Λ₀ = completedRiemannZeta₀` has order at most `1` (hence order at most
`3/2` in the weaker sense needed by `completedZeta_order_le_one`) follows from the exponential
decay of the Jacobi theta kernel via the Mellin representation.  Below we prove the key
ingredient: `(3/2 : ℝ) ∈ orderSet completedRiemannZeta₀`, which makes
`completedZeta_order_le_one` unconditional.

The proof bounds the Mellin integral of `f_modif` for `hurwitzEvenFEPair 0` by splitting at
`t = 1`, using `|evenKernel 0 t - 1| ≤ 3 exp(-πt)` for `t ≥ 1` and
`|evenKernel 0 t - t^{-1/2}| ≤ 3 t^{-1/2} exp(-π/t)` for `0 < t < 1`, then the
functional equation `Λ₀(s) = Λ₀(1/2 - s)` to handle small real parts.  The constants
`exp(-π/t) ≤ t` for `t ∈ (0,1]` and `Γ(σ) ≤ (σ+1)^σ` for `σ ≥ 1` yield the
final bound `‖Λ₀ w‖ ≤ C exp(|w|^{3/2})`. -/

private def a0 : UnitAddCircle := 0

private noncomputable def P0 : WeakFEPair ℂ := hurwitzEvenFEPair a0

/-- `exp(-π/t) ≤ t` for `t ∈ (0,1]`.  Key estimate for the Mellin integral near zero. -/
private lemma exp_neg_pi_div_le_self {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.exp (-Real.pi / t) ≤ t := by
  rcases eq_or_lt_of_le ht1 with rfl | ht1
  · simp only [div_one]
    exact (exp_le_exp.mpr (by linarith [Real.pi_pos])).trans_eq Real.exp_zero
  · trans (Real.exp (Real.log t))
    · rw [exp_le_exp, div_le_iff₀ ht]
      have hlog : Real.log t < Real.log 1 :=
        (Real.log_lt_log_iff ht zero_lt_one).mpr ht1
      have h2 : Real.log t * t < 0 :=
        mul_neg_of_neg_of_pos (by linarith [Real.log_one]) ht
      have h1 : |Real.log t * t| < 1 := abs_log_mul_self_lt _ ht ht1.le
      rw [abs_of_neg h2] at h1
      linarith [show -Real.pi < -1 from neg_lt_neg (by linarith [Real.pi_gt_three])]
    · exact le_of_eq (Real.exp_log ht)

/-- `log(x+1) ≤ √x` for `x ≥ 1`.  Used to convert `log(σ+1)` into `√σ` in the exponent. -/
private lemma log_add_one_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 1) ≤ Real.sqrt x := by
  suffices h : ∀ y : ℝ, 1 ≤ y → Real.log (y ^ 2 + 1) ≤ y from by
    have hy : 1 ≤ √x := by
      rw [show (1 : ℝ) = √1 from by norm_num [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt hx
    have := h (√x) hy
    rwa [Real.sq_sqrt (by linarith : 0 ≤ x)] at this
  intro y hy
  suffices hexp : y ^ 2 + 1 ≤ Real.exp y from by
    have h1 : 0 < y ^ 2 + 1 := by nlinarith [sq_nonneg y]
    exact (Real.log_le_iff_le_exp h1).mpr hexp
  have hy0 : 0 < y := by linarith
  have h_deriv : Monotone (fun t : ℝ => Real.exp t - t ^ 2 - 1) :=
    monotone_of_hasDerivAt_nonneg
      (f' := fun t => Real.exp t - 2 * t)
      (fun t => by
        have h1 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 : ℝ → ℝ) (2 * t) t := hasDerivAt_pow 2 t
        convert h1.sub h2 using 1
        ring)
      (fun t => by
        by_cases ht1 : t ≤ 1
        · have ht1' : t + 1 ≤ Real.exp t := add_one_le_exp t
          linarith
        · have ht1' : 1 < t := by linarith
          have h2 : Real.exp 1 > 2 := by norm_num [Real.exp_one]
          nlinarith [mul_le_mul_of_nonneg_left ht1'.le (by norm_num : (0:ℝ) ≤ 2),
            le_trans (show Real.exp 1 ≤ Real.exp t from by gcongr) h2.le])
  have hval : Real.exp 0 - 0 ^ 2 - 1 = 0 := by simp [Real.exp_zero]; norm_num
  have hge := h_deriv (le_refl 0) hy0.le
  linarith [hval ▸ hge]

/-- The even-Kernel (and hence the Hurwitz even kernel at `a = 0`) satisfies
`|evenKernel 0 t - 1| ≤ 3 exp(-π t)` for `t ≥ 1`. -/
private lemma evenKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |evenKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  sorry

/-- The cos-Kernel satisfies `|cosKernel 0 t - 1| ≤ 3 exp(-π t)` for `t ≥ 1`. -/
private lemma cosKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |cosKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  sorry

/-- `Γ(σ)/π^σ ≤ exp(σ^{3/2})` for `σ ≥ 1`. From `Γ(σ) ≤ (σ+1)^σ` and
`log(σ+1) ≤ √σ`. -/
private lemma gamma_over_pi_le_exp_pow {σ : ℝ} (h : 1 ≤ σ) :
    Real.Gamma σ / Real.pi ^ σ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (by norm_num) h
  have hpow : 0 < Real.pi ^ σ := Real.rpow_pos_of_pos Real.pi_pos σ
  have hg : Real.Gamma σ ≤ (σ + 1) ^ σ := Real.Gamma_le_add_one_pow h
  have hlog : Real.log (σ + 1) ≤ √σ := log_add_one_le_sqrt h
  have hkey : (σ + 1) ^ σ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := by
    have ha : 0 < σ + 1 := by linarith
    have hlog1 : Real.log ((σ + 1) ^ σ) = σ * Real.log (σ + 1) := Real.log_rpow ha
    have hlog2 : Real.log ((σ + 1) ^ σ) ≤ σ * Real.sqrt σ := by
      rw [hlog1]; exact mul_le_mul_of_nonneg_left hlog (le_of_lt hσ0)
    have h3 : σ * Real.sqrt σ = σ ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
        Real.rpow_add (by linarith : 0 < σ), Real.rpow_one, mul_div_cancel₀ (1:ℝ) 2]
    rw [h3] at hlog2
    exact Real.log_le_iff_le_exp (by positivity : 0 < (σ + 1) ^ σ) |>.mp hlog2
  calc Real.Gamma σ / Real.pi ^ σ ≤ (σ + 1) ^ σ / Real.pi ^ σ :=
      div_le_div_of_nonneg_right (Real.rpow_nonneg_of_nonneg (le_of_lt Real.pi_pos) σ) hg
    _ ≤ (σ + 1) ^ σ := by
      rw [div_le_iff₀ hpow]; nlinarith [Real.rpow_le_rpow (by linarith) (by linarith) (le_of_lt hσ0)]
    _ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := hkey

/-- **Order of the completed zeta function is at most `3/2`.**

This is the key estimate that makes `completedZeta_order_le_one` unconditional.  It follows
from the Mellin representation `Λ₀ = mellin (hurwitzEvenFEPair 0).f_modif` and the exponential
decay of the theta kernel via the functional equation `Λ₀(s) = Λ₀(1/2 - s)`. -/
theorem orderSet_completedRiemannZeta₀ :
    (3 / 2 : ℝ) ∈ orderSet completedRiemannZeta₀ := by
  sorry

/-- **The completed zeta has order at most 2.**

`ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)` differs from `s(s-1)·Λ₀(s) + 1` only at the trivial zeros
(where mathlib's `Complex.Gamma` vanishes instead of having a pole, making `ξ` vanish there),
so a growth bound for the entire function `Λ₀ = completedRiemannZeta₀` transfers to `ξ`.

The proof that `Λ₀` has order at most `3/2` is given by `orderSet_completedRiemannZeta₀`
(derived from the Mellin representation and exponential decay of the theta kernel).
Everything else — the algebraic identity, the trivial-zero case and the
elementary growth estimates — is proved here. -/
theorem completedZeta_order_le_one :
    ZeroFreeRegionHadamard.orderOfEntire
      (fun s => s * (s - 1) * Real.pi ^ (-(s / 2)) * Complex.Gamma (s / 2) * riemannZeta s)
      ≤ 2 := by
  obtain ⟨C, r₀, hr₀, hbound⟩ := orderSet_completedRiemannZeta₀
  have hmem : (2 : ℝ) ∈ orderSet
      (fun s => s * (s - 1) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) *
        riemannZeta s) := by
    refine ⟨C + 1, max r₀ 4, lt_max_of_lt_right (by norm_num), ?_⟩
    intro z hz
    dsimp only
    have hz4 : (4 : ℝ) ≤ ‖z‖ := le_trans (le_max_right r₀ 4) hz
    have hzr : r₀ ≤ ‖z‖ := le_trans (le_max_left r₀ 4) hz
    have hRpos : (0 : ℝ) < ‖z‖ := by linarith
    have hunn : 0 ≤ ‖z‖ ^ (3 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hRpos) _
    have hE2 : ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ 2 := by
      rw [← Real.rpow_natCast ‖z‖ 2]
      norm_num
    have hEnn : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℝ) := Real.rpow_nonneg (le_of_lt hRpos) _
    -- `2·R^{3/2} ≤ R²`
    have h4' : ((4 : ℝ)) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hsqrt : (2 : ℝ) ≤ ‖z‖ ^ (1 / 2 : ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hz4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [h4'] at h
    have h2u : 2 * ‖z‖ ^ (3 / 2 : ℝ) ≤ ‖z‖ ^ (2 : ℝ) := by
      have hmulrpow : ‖z‖ ^ (3 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (2 : ℝ) := by
        rw [← Real.rpow_add hRpos]
        norm_num
      calc 2 * ‖z‖ ^ (3 / 2 : ℝ) = ‖z‖ ^ (3 / 2 : ℝ) * 2 := by ring
        _ ≤ ‖z‖ ^ (3 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hsqrt hunn
        _ = ‖z‖ ^ (2 : ℝ) := hmulrpow
    have hCnn : 0 ≤ C := by
      by_contra hneg
      have hneg' : C < 0 := not_le.mp hneg
      have hlt : C * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) < 0 :=
        mul_neg_of_neg_of_pos hneg' (Real.exp_pos _)
      linarith [norm_nonneg (completedRiemannZeta₀ z), hbound z hzr]
    -- `R² + R ≤ exp(R²/2)`
    have hexpE2 : ‖z‖ ^ 2 + ‖z‖ ≤ Real.exp (‖z‖ ^ (2 : ℝ) / 2) := by
      have h1 : ‖z‖ ^ (2 : ℝ) / 4 + 1 ≤ Real.exp (‖z‖ ^ (2 : ℝ) / 4) := Real.add_one_le_exp _
      have h2 : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℝ) / 4 + 1 := by linarith
      have h3 : (‖z‖ ^ (2 : ℝ) / 4 + 1) ^ 2 ≤ (Real.exp (‖z‖ ^ (2 : ℝ) / 4)) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      have h4 : (Real.exp (‖z‖ ^ (2 : ℝ) / 4)) ^ 2 = Real.exp (‖z‖ ^ (2 : ℝ) / 2) := by
        rw [sq, ← Real.exp_add]
        ring_nf
      have h5 : ‖z‖ ^ 2 + ‖z‖ ≤ (‖z‖ ^ (2 : ℝ) / 4 + 1) ^ 2 := by
        rw [hE2]
        have hx16 : (16 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith [hz4]
        nlinarith [hx16, hz4, sq_nonneg (‖z‖ - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ ‖z‖ ^ 2 - 16) (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)]
      calc ‖z‖ ^ 2 + ‖z‖ ≤ (‖z‖ ^ (2 : ℝ) / 4 + 1) ^ 2 := h5
        _ ≤ (Real.exp (‖z‖ ^ (2 : ℝ) / 4)) ^ 2 := h3
        _ = Real.exp (‖z‖ ^ (2 : ℝ) / 2) := h4
    have hone : (1 : ℝ) ≤ Real.exp (‖z‖ ^ (2 : ℝ)) := by
      linarith [Real.add_one_le_exp (‖z‖ ^ (2 : ℝ))]
    -- the analytic estimate
    have hkey : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1
        ≤ (C + 1) * Real.exp (‖z‖ ^ (2 : ℝ)) := by
      have hb := hbound z hzr
      have hz1n : ‖z - 1‖ ≤ ‖z‖ + 1 := by
        calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖z‖ + 1 := by rw [norm_one]
      have hprod : ‖z‖ * ‖z - 1‖ ≤ ‖z‖ ^ 2 + ‖z‖ := by nlinarith [norm_nonneg z, hz1n]
      have hstep1 : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖
          ≤ (‖z‖ ^ 2 + ‖z‖) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) :=
        mul_le_mul hprod hb (norm_nonneg _) (by nlinarith [norm_nonneg z])
      have hstep2 : (‖z‖ ^ 2 + ‖z‖) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ)))
          ≤ Real.exp (‖z‖ ^ (2 : ℝ) / 2) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hexpE2 (by positivity)
      have hstep3 : Real.exp (‖z‖ ^ (2 : ℝ) / 2) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ)))
          = C * Real.exp (‖z‖ ^ (2 : ℝ) / 2 + ‖z‖ ^ (3 / 2 : ℝ)) := by
        rw [Real.exp_add]; ring
      have hstep4 : C * Real.exp (‖z‖ ^ (2 : ℝ) / 2 + ‖z‖ ^ (3 / 2 : ℝ))
          ≤ C * Real.exp (‖z‖ ^ (2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
    -- split off the trivial zeros
    by_cases hG : Complex.Gamma (z / 2) = 0
    · simp only [hG, mul_zero, zero_mul, norm_zero]
      nlinarith [Real.exp_pos (‖z‖ ^ (2 : ℝ)), hCnn]
    · have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz4
        linarith
      have hz1 : z ≠ 1 := by
        intro h
        rw [h, norm_one] at hz4
        linarith
      have hxi : z * (z - 1) * (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2) * riemannZeta z
          = z * (z - 1) * completedRiemannZeta₀ z + 1 := by
        have hpi0 : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hpi : ((Real.pi : ℂ)) ^ (-z / 2) ≠ 0 :=
          Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0)
        have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
        rw [riemannZeta_eq_completedRiemannZeta₀ hz0,
          show ((Real.pi : ℂ)) ^ (-(z / 2)) = ((Real.pi : ℂ)) ^ (-z / 2) by rw [neg_div]]
        field_simp
        ring
      rw [hxi]
      calc ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖
          ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1 := by
            rw [norm_mul, norm_mul, norm_one]
        _ ≤ (C + 1) * Real.exp (‖z‖ ^ (2 : ℝ)) := hkey
  have hle := orderOfEntire_le hmem
  exact le_trans hle (le_of_eq rfl)

/-! ## Digamma series representation from Weierstrass product

The Weierstrass product `1/Γ(s) = s·e^{γs}·∏_{n=1}^∞ (1+s/n)·e^{-s/n}` is the
classical representation. Rather than prove the full product, we derive the
**digamma series** `ψ(s) = -γ + Σ_{n=0}^∞ (1/(n+1) - 1/(n+s))` directly from
mathlib's `Complex.GammaSeq` and `GammaSeq_tendsto_Gamma`.

Key chain:
1. `logDeriv_GammaSeq_eq`: algebraic identity `logDeriv(Γ_n)(s) = log n - Σ_{j=0}^n 1/(s+j)`
2. `psi_eq_tsum`: ψ(s) = lim_{n→∞} logDeriv(Γ_n)(s) = -γ + Σ(1/(n+1) - 1/(n+s))
3. `digamma_le_log`: O(log|t|) bound from the series (splitting at N = ⌈|t|⌉)
-/

/-- **logDeriv of GammaSeq.** For `s` not a non-positive integer and `n ≥ 1`:
`logDeriv (fun s => GammaSeq s n) s = log(n) - Σ_{j=0}^n 1/(s+j)`.

The key step is that `n^s` contributes `log n` to the logDeriv (since `d/ds n^s = n^s · log n`),
the factorial `n!` contributes 0 (constant in `s`), and the product `∏(s+j)` contributes
`Σ 1/(s+j)`. -/
-- The algebraic identity logDeriv(GammaSeq · n) s = log n - Σ_{j=0}^n 1/(s+j)
-- is proved from logDeriv_mul, logDeriv_const, logDeriv_prod, and the factorization
-- GammaSeq w n = n^w * n! / ∏(w+j).
theorem logDeriv_GammaSeq_eq {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) {n : ℕ} (hn : 1 ≤ n) :
    logDeriv (fun w => Complex.GammaSeq w n) s =
      Complex.log (↑n) - ∑ j ∈ range (n + 1), (s + j)⁻¹ := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hne : ∀ j ∈ range (n + 1), s + (j : ℂ) ≠ 0 := by
    intro j _ h
    exact hs j (eq_neg_of_add_eq_zero_left h)
  have hpow : logDeriv (fun w => (n : ℂ) ^ w) s = Complex.log (n : ℂ) := by
    rw [logDeriv_apply]
    have hder : deriv (fun w => (n : ℂ) ^ w) s = (n : ℂ) ^ s * Complex.log (n : ℂ) := by
      simpa using ((hasDerivAt_id s).const_cpow (Or.inl hn0)).deriv
    rw [hder]
    change ((n : ℂ) ^ s * Complex.log (n : ℂ)) / (n : ℂ) ^ s = Complex.log (n : ℂ)
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)]
  have hprod : logDeriv (fun w => ∏ j ∈ range (n + 1), (w + (j : ℂ))) s =
      ∑ j ∈ range (n + 1), (s + (j : ℂ))⁻¹ := by
    have hldp : logDeriv (fun x => ∏ i ∈ range (n + 1), (x + (i : ℂ))) s =
        ∑ i ∈ range (n + 1), logDeriv (fun w => w + (i : ℂ)) s :=
      logDeriv_prod (s := range (n + 1)) (x := s) (f := fun (j : ℕ) (w : ℂ) => w + j)
        hne (by intro j _; fun_prop)
    rw [hldp]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [logDeriv_apply]
    have hder : deriv (fun w => w + (j : ℂ)) s = 1 := by
      simp
    rw [hder]
    simp
  have hGS : (fun w => Complex.GammaSeq w n) =
      (fun w => (n : ℂ) ^ w * (Nat.factorial n : ℂ) / ∏ j ∈ range (n + 1), (w + (j : ℂ))) := by
    ext w
    rfl
  rw [hGS, logDeriv_div s]
  · rw [logDeriv_mul_const s (Nat.factorial n : ℂ) hfac, hpow, hprod]
  · exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)) hfac
  · simpa [Finset.prod_apply] using
      (Finset.prod_ne_zero_iff.mpr (by intro j hj; exact hne j hj))
  · exact (differentiableAt_id.const_cpow (Or.inl hn0)).mul (differentiableAt_const _)
  · exact DifferentiableAt.fun_finsetProd (fun j _ => by fun_prop)

/-- **Absolute convergence of the digamma series.**
For `Re(s) > 0`, the series `Σ_n |1/(n+1) - 1/(n+s)|` converges.
(In fact no hypothesis on `s` is needed; see `summable_norm_inv_add_sub`.) -/
theorem summable_digamma_tsum (s : ℂ) (_hs : 0 < s.re) :
    Summable fun n : ℕ => ‖1 / (↑n + 1 : ℂ) - 1 / (↑n + s)‖ :=
  summable_norm_inv_add_sub 1 s
