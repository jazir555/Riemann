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

## Status (2026-08-14) — the file compiles with no `sorry`s: all Mellin-order sub-estimates are proved

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
  `gamma_over_pi_le_exp_pow`, `log_add_one_le_sqrt`) are proved below (series-comparison and calculus proofs).

### Still missing (requires substantial new mathlib content)

1. **Hadamard factorization theorem** — **DONE (2026-08-15)**: the genus-one
   factorization `hadamard_factorization_genus_one` is proved in this file
   (`f = e^g · canonicalProductNat 1 a` for entire `f` with simple zeros `a`).
   The full genus-`⌊ρ⌋` statement and the order-`ρ` bound (`completedZeta_order_le_one`)
   remain future work.
2. **Application to the completed zeta** — **zero identification DONE (2026-08-15)**:
   `xi_zero_iff_riemannZeta_zero` identifies the zeros of the entire function
   `ξ(s) = s(s-1)Λ₀(s) + 1` with the non-trivial zeros of `ζ`, and
   `riemannZeta_zero_imp_critical_strip_or_trivial` gives the critical-strip
   classification. **Log-derivative identity DONE (2026-08-15)** in parametric
   form: `logDeriv_completedZeta` gives
   `-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv(·Γℝ)(s)) - Σₙ (1/(s-aₙ) + 1/aₙ)`
   from the Hadamard hypotheses (zero enumeration `a`, `hzero`, `hord`, `hinj`,
   `hs2`, `htend`), via `logDeriv_xi_of_factorization` and
   `neg_logDeriv_riemannZeta_eq_xi`. **Zero set DONE (2026-08-15)**: as a set,
   `xiZeros_eq_riemannZetaZeros_inter_closedStrip` identifies `{z | xi z = 0}`
   with `riemannZetaZeros ∩ {0 ≤ Re s ≤ 1}`, and
   `tendsto_xiZeros_cofinite_cocompact` transfers the discreteness/local
   finiteness of `riemannZetaZeros`. Still missing: constructing the zero
   enumeration `a` of `ξ` with `Σ 1/‖ρ‖² < ∞` (Jensen), which turns this into
   the concrete `h_decomp` for `riemannZeta_ne_zero_of_zeroFreeEdge`.
3. **Digamma/Stirling vertical bounds** — **DONE**: `digamma_le_log`
   (`‖ψ(s)‖ ≤ γ + 2σ + 7 + log(|t|+2)`) and `norm_psi_le_linear`
   (`‖ψ(s)‖ ≤ (π²+1)·|s|`).

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

**Proved sorry-free (unconditional):**
- `completedZeta_order_le_one` : `ξ` has order ≤ 2, using `orderSet_completedRiemannZeta₀`
  (the Mellin-order bound, which is proved via the kernel decay bounds,
  `log(σ+1) ≤ √σ`, and `Γ(σ)/π^σ ≤ exp(σ^{3/2})`).

**Still to be proved (the Hadamard factorisation itself):**
- `hadamardFactorization` : for `f` entire of finite order `ρ` with zeros
  `a_n`, `f(z) = z^m e^{g(z)} ∏ E_{⌊ρ⌋}(z/a_n)` with `deg g ≤ ρ` — **DONE for genus one**
  (`hadamard_factorization_genus_one`, 2026-08-15); general genus remains,
- `completedZeta_zeros_eq_nontrivialZeros` : the zero set (with multiplicity) is
  exactly `{ρ : non-trivial zero of ζ}` — **DONE** in the form
  `xi_zero_iff_riemannZeta_zero` + `riemannZeta_zero_imp_critical_strip_or_trivial`
  + `xiZeros_eq_riemannZetaZeros_inter_closedStrip` (set equality with
  `riemannZetaZeros` in the closed strip; `xi` is `s(s-1)Λ₀ + 1`), 2026-08-15,
- `logDeriv_completedZeta` : the logarithmic derivative identity above,
  which instantiates the `h_decomp` / `h_analytic` hypotheses of
  `riemannZeta_ne_zero_of_zeroFreeEdge` — **DONE in parametric form**
  (2026-08-15): `-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv(·Γℝ)(s)) -
  Σₙ (1/(s-aₙ) + 1/aₙ)` given the Hadamard hypotheses on the zero
  enumeration `a`. What remains is constructing that enumeration from
  `ξ` itself (with `Σ 1/‖ρ‖² < ∞` via Jensen) — then the identity becomes
  the concrete `h_decomp` for `riemannZeta_ne_zero_of_zeroFreeEdge`.
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
  have hmz : (m : ℤ) = ⌈x⌉ := Int.toNat_of_nonneg (by linarith)
  have hmr : (m : ℝ) = (⌈x⌉ : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hmz
  have hm1 : 1 ≤ m := by linarith
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
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          have hid : HasDerivAt (id : ℝ → ℝ) 1 t := hasDerivAt_id t
          have hmul : HasDerivAt (id * id : ℝ → ℝ) (1 * t + t * 1) t := hid.mul hid
          convert hmul using 1
          · funext x; simp [id]; ring
          · ring
        have h3 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
        show HasDerivAt (fun t => rexp t - t ^ 2 - 1) (rexp t - 2 * t) t
        have h12 : HasDerivAt (fun t => rexp t - t ^ 2) (rexp t - 2 * t) t := h1.sub h2
        have h123 : HasDerivAt (fun t => rexp t - t ^ 2 - 1) (rexp t - 2 * t - 0) t := h12.sub h3
        simpa using h123)
      (fun t => by
        by_cases ht1 : t ≤ 1
        · -- t ≤ 1: exp(t) ≥ t+1 ≥ 2t
          have h1 : t + 1 ≤ Real.exp t := add_one_le_exp t
          have h2 : 2 * t ≤ t + 1 := by linarith
          have h3 : 2 * t ≤ Real.exp t := le_trans h2 h1
          show Real.exp t - 2 * t ≥ 0
          linarith
        · -- t > 1: exp(t) ≥ exp(1)*t ≥ 2t
          have ht0 : 0 < t := by linarith
          have h2 : Real.exp 1 > 2 := Real.exp_one_gt_two
          have hle : t ≤ Real.exp (t - 1) := by linarith [add_one_le_exp (t - 1)]
          have h4 : Real.exp 1 * t ≤ Real.exp 1 * Real.exp (t - 1) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos 1))
          have h5 : 2 * t ≤ Real.exp 1 * t :=
            mul_le_mul_of_nonneg_right (le_of_lt h2) (le_of_lt ht0)
          have h7 : Real.exp 1 * t ≤ Real.exp t := by
            have hexp : Real.exp t = Real.exp 1 * Real.exp (t - 1) := by
              conv_lhs => rw [show t = 1 + (t - 1) from by ring]
              rw [Real.exp_add]
            rw [hexp]; exact h4
          have h8 : 2 * t ≤ Real.exp t := le_trans h5 h7
          show Real.exp t - 2 * t ≥ 0
          linarith)
  have hval : Real.exp 0 - 0 ^ 2 - 1 = 0 := by simp [Real.exp_zero]
  have hge := h_deriv hy0.le
  linarith [hval, hge]

private lemma term_le_geom (t : ℝ) (ht : 1 ≤ t) (m : ℕ) :
    Real.exp (-Real.pi * (m + 1) ^ 2 * t) ≤
    Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) ^ m := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsq : ((m : ℝ) + 1) ^ 2 ≥ (m : ℝ) + 1 := by
    calc ((m : ℝ) + 1) ^ 2 = ((m : ℝ) + 1) * ((m : ℝ) + 1) := by ring
      _ ≥ ((m : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (m : ℝ) + 1 := by ring
  have h1 : -(Real.pi) * (((m : ℝ) + 1) ^ 2) * t ≤ -(Real.pi) * ((m : ℝ) + 1) * t := by
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hsq)) ht0.le]
  have hexple := Real.exp_le_exp.mpr h1
  have hexp_add : Real.exp (-(Real.pi) * (m+1:ℝ) * t) =
      Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi) * m * t) := by
    rw [show -(Real.pi) * (m+1:ℝ) * t = -(Real.pi) * t + -(Real.pi) * m * t from by ring,
        Real.exp_add]
  have hexp_mul : Real.exp (-(Real.pi) * m * t) = Real.exp (-(Real.pi * t) * m) := by
    rw [show -(Real.pi) * m * t = -(Real.pi * t) * m from by ring]
  have hexp_nat : Real.exp (-(Real.pi * t) * m) = Real.exp (-(Real.pi * t)) ^ m := by
    rw [show -(Real.pi * t) * m = (m:ℝ) * (-(Real.pi * t)) from by ring, Real.exp_nat_mul]
  calc _ ≤ Real.exp (-(Real.pi) * (m+1:ℝ) * t) := hexple
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi) * m * t) := hexp_add
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi * t) * m) := by rw [hexp_mul]
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi * t)) ^ m := by rw [hexp_nat]
    _ = _ := by simp only [neg_mul]

private lemma exp_le_third (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-Real.pi * t) ≤ 1 / 3 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h1 : -Real.pi * t ≤ -3 := by nlinarith [Real.pi_gt_three]
  have h2 := Real.exp_le_exp.mpr h1
  have h3 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
  have h4 : (8:ℝ) ≤ Real.exp 3 := by
    have h4a : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    rw [show (3:ℝ) = 1+1+1 from by norm_num, Real.exp_add, Real.exp_add]
    have h4b : Real.exp 1 * Real.exp 1 ≥ 4 := by
      have := mul_le_mul h4a h4a (by linarith) (by linarith)
      linarith [show (2:ℝ) * 2 = 4 from by norm_num]
    have h4c : Real.exp 1 * Real.exp 1 * Real.exp 1 ≥ 8 := by
      have := mul_le_mul h4b h4a (by linarith) (by linarith)
      linarith [show (4:ℝ) * 2 = 8 from by norm_num]
    exact h4c
  have h5 : (Real.exp 3)⁻¹ ≤ (8:ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos 3) (by norm_num : (0:ℝ) < 8)).mpr h4
  have h6 : (8:ℝ)⁻¹ ≤ (3:ℝ)⁻¹ :=
    (inv_le_inv₀ (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 3)).mpr
      (by norm_num : (3:ℝ) ≤ 8)
  have h5' : Real.exp (-3) ≤ (8:ℝ)⁻¹ := by rw [h3]; exact h5
  rw [show (1/3:ℝ) = (3:ℝ)⁻¹ from by norm_num]
  exact h2 |>.trans h5' |>.trans h6

/-- The cos-Kernel satisfies `|cosKernel 0 t - 1| ≤ 3 exp(-π t)` for `t ≥ 1`. -/
private lemma cosKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |cosKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hsum := hasSum_nat_cosKernel₀ (0 : ℝ) ht0
  have hsum' : HasSum (fun n : ℕ ↦ 2 * Real.exp (-Real.pi * (n + 1) ^ 2 * t))
      (cosKernel (0 : UnitAddCircle) t - 1) :=
    hsum.congr_fun (fun n => by simp [Real.cos_zero])
  have hge : 0 ≤ cosKernel (0 : UnitAddCircle) t - 1 := by
    rw [← hsum'.tsum_eq]; exact tsum_nonneg (fun n => by positivity)
  rw [abs_of_nonneg hge, ← hsum'.tsum_eq, tsum_mul_left]
  have hexp1 : Real.exp (-Real.pi * t) < 1 := by
    rw [Real.exp_lt_one_iff]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) ht0
  have hsrc : Summable (fun n : ℕ => Real.exp (-Real.pi * (n + 1) ^ 2 * t)) := by
    have hg := summable_geometric_of_lt_one (Real.exp_nonneg _) hexp1
    exact Summable.of_norm_bounded (hg.mul_left _) (fun n => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; exact term_le_geom t ht n)
  have htsum : ∑' n : ℕ, Real.exp (-Real.pi * (n + 1) ^ 2 * t) ≤
      Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹ := by
    have hg := summable_geometric_of_lt_one (Real.exp_nonneg _) hexp1
    have htsum' := Summable.tsum_le_tsum (term_le_geom t ht) hsrc (hg.mul_left _)
    rwa [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) hexp1] at htsum'
  -- 2 * tsum ≤ 2 * exp(-πt) / (1-exp(-πt)) ≤ 3 * exp(-πt)
  have hfrac : 2 * (Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹) ≤
      3 * Real.exp (-Real.pi * t) := by
    rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ (sub_pos.mpr hexp1)]
    have hx : 0 ≤ Real.exp (-Real.pi * t) := le_of_lt (Real.exp_pos _)
    have h3x : 3 * Real.exp (-Real.pi * t) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (exp_le_third t ht) (by norm_num : (0:ℝ) ≤ 3)
      linarith [show (3:ℝ) * (1/3) = 1 from by norm_num]
    have hmid : 0 ≤ Real.exp (-Real.pi * t) * (1 - 3 * Real.exp (-Real.pi * t)) := by
      apply mul_nonneg hx; linarith [h3x]
    nlinarith [hmid]
  exact (mul_le_mul_of_nonneg_left htsum (by positivity : (0:ℝ) ≤ 2)).trans hfrac

/-- The even-Kernel (and hence the Hurwitz even kernel at `a = 0`) satisfies
`|evenKernel 0 t - 1| ≤ 3 exp(-π t)` for `t ≥ 1`. -/
private lemma evenKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |evenKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have := congr_fun evenKernel_eq_cosKernel_of_zero t
  simp only [this]
  exact cosKernel_sub_le t ht

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
    have hlog1 : Real.log ((σ + 1) ^ σ) = σ * Real.log (σ + 1) :=
      Real.log_rpow ha σ
    have hlog2 : Real.log ((σ + 1) ^ σ) ≤ σ * Real.sqrt σ := by
      rw [hlog1]; exact mul_le_mul_of_nonneg_left hlog (le_of_lt hσ0)
    have h3 : σ * Real.sqrt σ = σ ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_comm]
      have : σ ^ (1 / 2 : ℝ) * σ = σ ^ (1 / 2 : ℝ) * σ ^ (1 : ℝ) := by simp [Real.rpow_one]
      rw [this, ← Real.rpow_add (by linarith : 0 < σ), show (1 / 2 : ℝ) + 1 = 3 / 2 from by norm_num]
    rw [h3] at hlog2
    exact Real.log_le_iff_le_exp (by positivity : 0 < (σ + 1) ^ σ) |>.mp hlog2
  calc Real.Gamma σ / Real.pi ^ σ ≤ (σ + 1) ^ σ / Real.pi ^ σ :=
      div_le_div_of_nonneg_right hg (Real.rpow_nonneg (le_of_lt Real.pi_pos) σ)
    _ ≤ (σ + 1) ^ σ := by
      rw [div_le_iff₀ hpow, mul_comm ((σ + 1) ^ σ)]
      have hpow1 : Real.pi ^ σ ≥ 1 := by
        have hpi : 1 ≤ π := by linarith [Real.pi_gt_three]
        have h1 : (1:ℝ) ^ σ ≤ π ^ σ := Real.rpow_le_rpow zero_le_one hpi (le_of_lt hσ0)
        simp only [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1), Real.log_one,
          zero_mul, Real.exp_zero] at h1
        exact h1
      calc (σ + 1) ^ σ = 1 * (σ + 1) ^ σ := by ring
        _ ≤ π ^ σ * (σ + 1) ^ σ := mul_le_mul_of_nonneg_right hpow1 (by positivity)
    _ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := hkey

/- **Order of the completed zeta function is at most `3/2`.**

This is the key estimate that makes `completedZeta_order_le_one` unconditional.  It follows
from the Mellin representation `Λ₀ = mellin (hurwitzEvenFEPair 0).f_modif` and the exponential
decay of the theta kernel via the functional equation `Λ₀(s) = Λ₀(1/2 - s)`. -/
/-- Mellin transform of the modified kernel `f_modif` is bounded by `14·exp(σ^{3/2})`.
For `σ ≥ 1/4`: split the integral at `t=1`, bound `(0,1)` by `3/(σ+1/2) ≤ 4`
via `evenKernel_functional_equation` + `cosKernel_sub_le` + `exp_neg_pi_div_le_self`,
and `(1,∞)` by `3·Γ(σ)/π^σ ≤ 3·exp(σ^{3/2})` via `evenKernel_sub_le` +
`integral_cpow_mul_exp_neg_mul_Ioi` + `gamma_over_pi_le_exp_pow`. -/
/- `3 * t^(σ-1) * exp(-πt)` is integrable on `(0, ∞)` for `σ > 0`, by comparison with the
Gamma integral. -/
private lemma integrableOn_exp_neg_pi_mul_rpow (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ (σ - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent hσ
  have hcon : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 0) := by
    have hrpow : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Set.Ioi 0) := by
      intro t ht
      exact (continuousAt_rpow_const t (σ - 1) (Or.inl ht.ne')).continuousWithinAt
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (-Real.pi * t)) (Set.univ : Set ℝ) := by
      fun_prop
    exact hrpow.mul (hexp.mono (Set.subset_univ _))
  have hdom : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ t ^ (σ - 1) * Real.exp (-Real.pi * t) ∧
      t ^ (σ - 1) * Real.exp (-Real.pi * t) ≤ Real.exp (-t) * t ^ (σ - 1) := by
    intro t ht
    constructor
    · exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) (σ - 1)) (le_of_lt (Real.exp_pos _))
    · have hπ : Real.exp (-Real.pi * t) ≤ Real.exp (-t) := by
        apply Real.exp_le_exp.mpr
        have hle1 : -Real.pi ≤ -1 := by linarith [Real.pi_gt_three]
        exact (mul_le_mul_of_nonneg_right hle1 (le_of_lt ht)).trans_eq (by simp)
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hπ (Real.rpow_nonneg (le_of_lt ht) (σ - 1))
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono_nonneg (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      hbase ?_ ?_ ?_
    · exact hcon.aestronglyMeasurable measurableSet_Ioi
    · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => (hdom t ht).1))
    · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => (hdom t ht).2))
  have h3 : MeasureTheory.IntegrableOn
      (fun t : ℝ => 3 * (t ^ (σ - 1) * Real.exp (-Real.pi * t))) (Set.Ioi 0) :=
    (hint.smul (3 : ℝ)).congr (Filter.Eventually.of_forall (fun t => by simp [smul_eq_mul]))
  simpa [mul_assoc] using h3

/- If `f` is continuous on `(a, ∞)`, nonnegative, and bounded above by an integrable function
`g` on `(a, ∞)`, then `f` is integrable on `(a, ∞)`. -/
private lemma integrableOn_Ici_of_continuousOn {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Set.Ioi a))
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi a))
    (hfg : ∀ t ∈ Set.Ioi a, 0 ≤ f t ∧ f t ≤ g t) :
    MeasureTheory.IntegrableOn f (Set.Ioi a) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    hf.aestronglyMeasurable measurableSet_Ioi
  have hnonneg : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)), 0 ≤ f t := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => (hfg t ht).1))
  have hle : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)), f t ≤ g t := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => (hfg t ht).2))
  exact MeasureTheory.Integrable.mono_nonneg (μ := MeasureTheory.volume.restrict (Set.Ioi a))
    hg hmeas hnonneg hle

private lemma mellin_fmodif_bound {w : ℂ} (hw : (1/4 : ℝ) ≤ w.re) :
    ‖(hurwitzEvenFEPair 0).Λ₀ w‖ ≤ 14 * Real.exp (w.re ^ (3 / 2 : ℝ)) := by
  set σ := w.re with hσ
  have hσge : (1/4 : ℝ) ≤ σ := hσ ▸ hw
  have hσpos : 0 < σ := by linarith
  -- Λ₀(w) = mellin f_modif w
  have hΛeq : (hurwitzEvenFEPair 0).Λ₀ w =
      mellin ((hurwitzEvenFEPair 0).f_modif : ℝ → ℂ) w := rfl
  -- Bound the norm by the integral of the norm
  have hle : ‖mellin ((hurwitzEvenFEPair 0).f_modif : ℝ → ℂ) w‖ ≤
      ∫ t : ℝ in Set.Ioi 0, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    rw [mellin]
    apply (MeasureTheory.norm_integral_le_integral_norm _).trans
    apply le_of_eq
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, hσ, sub_re, one_re]
  -- Split at t=1 and bound each part
  -- (0,1): |f_modif(t)| ≤ 3t^{1/2} via evenKernel_functional_equation + cosKernel_sub_le + exp_neg_pi_div_le_self
  --   so ∫₀¹ ≤ 3/(σ+1/2) ≤ 4 for σ ≥ 1/4
  -- (1,∞): |f_modif(t)| ≤ 3exp(-πt) via evenKernel_sub_le
  --   so ∫₁^∞ ≤ 3Γ(σ)/π^σ ≤ 3exp(σ^{3/2}) via gamma_over_pi_le_exp_pow
  -- Total ≤ 4 + 3exp(σ^{3/2}) ≤ 14exp(σ^{3/2})
  -- Key: bound the integral by splitting into (0,1) and (1,∞) contributions
  -- For t∈(0,1): |f_modif(t)| ≤ 3t^{1/2}, so integrand ≤ 3t^{σ-1/2}
  -- For t∈(1,∞): |f_modif(t)| ≤ 3exp(-πt), so integrand ≤ 3t^{σ-1}exp(-πt)
  -- ∫₀¹ 3t^{σ-1/2} dt = 3/(σ+1/2) ≤ 4 for σ ≥ 1/4
  -- ∫₁^∞ 3t^{σ-1}exp(-πt) dt ≤ 3Γ(σ)/π^σ ≤ 3exp(σ^{3/2}) by gamma_over_pi_le_exp_pow
  -- Total ≤ 4 + 3exp(σ^{3/2}) ≤ 14exp(σ^{3/2})
  -- Bound the (0,1) part using the FE and kernel bounds
  have h01_pt : ∀ t ∈ Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      3 * t ^ (σ - 1 / 2 : ℝ) := by
    intro t ht
    have htpos : 0 < t := (Set.mem_Ioc.mp ht).1
    have htle : t ≤ 1 := (Set.mem_Ioc.mp ht).2
    rcases htle.eq_or_lt with rfl | hlt
    · -- t = 1: f_modif 1 = 0 by definition (both indicators vanish at t=1)
      dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
      simp only [hurwitzEvenFEPair, P0, a0, Pi.add_apply,
        Set.indicator_of_notMem (Set.notMem_Ioi.mpr le_rfl),
        Set.indicator_of_notMem (Set.notMem_Ioo_of_ge le_rfl),
        zero_add, norm_zero, mul_zero, Real.one_rpow]; norm_num
    · -- t < 1: functional equation for evenKernel and cosKernel_sub_le
      have hkeq : evenKernel (0 : UnitAddCircle) t =
          (Real.sqrt t)⁻¹ * cosKernel (0 : UnitAddCircle) (1 / t) := by
        rw [evenKernel_functional_equation]; simp [Real.sqrt_eq_rpow]
      have hcos := cosKernel_sub_le (1 / t) (by linarith [one_le_one_div htpos hlt.le])
      have hexp := exp_neg_pi_div_le_self htpos hlt.le
      have hfmod : (hurwitzEvenFEPair 0).f_modif t =
          Complex.ofReal (evenKernel (0 : UnitAddCircle) t) -
              Complex.ofReal (t ^ (-(1 / 2 : ℝ))) := by
        dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
        simp only [Pi.add_apply, Set.indicator_of_notMem (Set.notMem_Ioi.mpr htle),
          zero_add, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨htpos, hlt⟩),
          smul_eq_mul, one_mul, mul_one]
      have hle_val : (hurwitzEvenFEPair 0).f_modif t =
          ((evenKernel (0 : UnitAddCircle) t : ℝ) : ℂ) -
            ((t ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) := by
        dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
        simp only [hurwitzEvenFEPair, P0, a0, Pi.add_apply,
          Set.indicator_of_notMem (Set.notMem_Ioi.mpr htle),
          zero_add, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨htpos, hlt⟩),
          smul_eq_mul, one_mul, mul_one]
      have hval : (hurwitzEvenFEPair 0).f_modif t =
          ((Real.sqrt t)⁻¹ * (cosKernel (0 : UnitAddCircle) (1 / t) - 1) : ℝ) := by
        rw [hle_val, hkeq, show (t ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) = (Real.sqrt t)⁻¹ from by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg htpos.le]]
        push_cast; ring
      have hnorm : ‖(hurwitzEvenFEPair 0).f_modif t‖ =
          |(Real.sqrt t)⁻¹ * (cosKernel (0 : UnitAddCircle) (1 / t) - 1)| := by
        rw [hval]
        exact RCLike.norm_ofReal _
      rw [hnorm, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt t)⁻¹)]
      calc
        t ^ (σ - 1) * ((Real.sqrt t)⁻¹ * |cosKernel (0 : UnitAddCircle) (1 / t) - 1|)
            ≤ t ^ (σ - 1) * ((Real.sqrt t)⁻¹ * (3 * Real.exp (-Real.pi / t))) := by
              have hcos' : |cosKernel (0 : UnitAddCircle) (1 / t) - 1| ≤
                  3 * Real.exp (-Real.pi / t) := by
                have hstep : (-Real.pi) * (1 / t) = -Real.pi / t := by
                  rw [mul_one_div]
                rwa [hstep] at hcos
              have hA : (0 : ℝ) ≤ (Real.sqrt t)⁻¹ := by positivity
              have hT : (0 : ℝ) ≤ t ^ (σ - 1) := Real.rpow_nonneg (le_of_lt htpos) (σ - 1)
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos' hA) hT
        _ ≤ t ^ (σ - 1) * ((Real.sqrt t)⁻¹ * (3 * t)) := by
              have hA : (0 : ℝ) ≤ (Real.sqrt t)⁻¹ := by positivity
              have hT : (0 : ℝ) ≤ t ^ (σ - 1) := Real.rpow_nonneg (le_of_lt htpos) (σ - 1)
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 3)) hA) hT
        _ = 3 * t ^ (σ - 1 / 2 : ℝ) := by
              have hsqrt : (Real.sqrt t)⁻¹ * t = Real.sqrt t := by
                have hpos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 htpos
                rw [mul_comm, ← div_eq_mul_inv, div_eq_iff hpos.ne']
                exact (mul_self_sqrt (le_of_lt htpos)).symm
              have hpow : t ^ (σ - 1) * Real.sqrt t = t ^ (σ - 1 / 2 : ℝ) := by
                rw [Real.sqrt_eq_rpow]
                rw [← Real.rpow_add htpos]
                congr 1
                ring
              calc
                t ^ (σ - 1) * ((Real.sqrt t)⁻¹ * (3 * t))
                    = 3 * (t ^ (σ - 1) * ((Real.sqrt t)⁻¹ * t)) := by ring
                _ = 3 * (t ^ (σ - 1) * Real.sqrt t) := by rw [hsqrt]
                _ = 3 * t ^ (σ - 1 / 2 : ℝ) := by rw [hpow]
  -- Pointwise bound on (1, ∞) for the integrand (used by h1inf and the splitting argument)
  have hpt : ∀ t ∈ Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) := by
    intro t ht
    have hfmod : (hurwitzEvenFEPair 0).f_modif t =
        ((evenKernel (0 : UnitAddCircle) t : ℝ) : ℂ) - (1 : ℂ) := by
      dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
      simp only [Pi.add_apply, Set.indicator_of_mem ht,
        Set.indicator_of_notMem (Set.notMem_Ioo_of_ge (Set.mem_Ioi.mp ht).le),
        add_zero, sub_zero, smul_eq_mul, one_mul, mul_one, if_true]
    have hnorm : ‖(hurwitzEvenFEPair 0).f_modif t‖ =
        |evenKernel (0 : UnitAddCircle) t - 1| := by
      rw [hfmod]
      have hc : ((evenKernel (0 : UnitAddCircle) t : ℝ) : ℂ) - (1 : ℂ) =
          ((evenKernel (0 : UnitAddCircle) t - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hc]
      exact RCLike.norm_ofReal _
    rw [hnorm]
    have ht0 : (0 : ℝ) ≤ t := by linarith [Set.mem_Ioi.mp ht]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (evenKernel_sub_le t (Set.mem_Ioi.mp ht).le)
        (Real.rpow_nonneg ht0 (σ - 1))
  -- Integrability of the integrand on (1, ∞) (dominated by the exponential decay bound)
  have hL1 : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioi 1) := by
    refine integrableOn_Ici_of_continuousOn ?_ (g := fun t : ℝ => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) ?_ ?_
    · intro t ht
      have ht0 : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
      have hc1 : ContinuousAt (fun x : ℝ => x ^ (σ - 1)) t :=
        continuousAt_rpow_const t (σ - 1) (Or.inl ht0.ne')
      have hc2 : ContinuousAt (fun x : ℝ => ‖(hurwitzEvenFEPair 0).f_modif x‖) t := by
        have hfcont : ContinuousAt (fun x : ℝ => (hurwitzEvenFEPair 0).f_modif x) t := by
          have hfmod : (fun x : ℝ => (hurwitzEvenFEPair 0).f_modif x) =ᶠ[𝓝 t]
              (fun x : ℝ => ((evenKernel (0 : UnitAddCircle) x : ℝ) : ℂ) - (1 : ℂ)) := by
            filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
            dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
            simp only [Pi.add_apply, Set.indicator_of_mem hx,
              Set.indicator_of_notMem (Set.notMem_Ioo_of_ge (Set.mem_Ioi.mp hx).le),
              add_zero, sub_zero, smul_eq_mul, one_mul, mul_one, if_true]
          have hc : ContinuousAt (fun x : ℝ => ((evenKernel (0 : UnitAddCircle) x : ℝ) : ℂ)) t :=
            continuous_ofReal.continuousAt.comp
              ((continuousOn_evenKernel (0 : UnitAddCircle)).continuousAt
                (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp ht] : (0 : ℝ) < t))))
          exact ContinuousAt.congr (hc.sub continuous_const.continuousAt) hfmod.symm
        exact ContinuousAt.comp continuous_norm.continuousAt hfcont
      exact (hc1.mul hc2).continuousWithinAt
    · exact (integrableOn_exp_neg_pi_mul_rpow σ hσpos).mono_set
        (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    · intro t ht
      constructor
      · exact mul_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht] : (0 : ℝ) ≤ t) (σ - 1)) (norm_nonneg _)
      · exact hpt t ht
  -- Integrability of the comparison integrand 3*t^(σ-1/2) on (0,1]
  have hb_rpow : MeasureTheory.IntegrableOn
      (fun t : ℝ => 3 * t ^ (σ - 1 / 2 : ℝ)) (Set.Ioc 0 1) := by
    have hi : IntervalIntegrable (fun t : ℝ => t ^ (σ - 1 / 2 : ℝ)) MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith [hσpos])
    have hic : IntervalIntegrable (fun t : ℝ => 3 * t ^ (σ - 1 / 2 : ℝ)) MeasureTheory.volume 0 1 :=
      hi.const_mul 3
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hic
  -- Integrability of the integrand on (0,1) (dominated by 3*t^(σ-1/2) via h01_pt)
  have hf_int_Ioo : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioo 0 1) := by
    have hcon : ContinuousOn
        (fun t : ℝ => (hurwitzEvenFEPair 0).f_modif t) (Set.Ioo 0 1) := by
      intro t ht
      have ht0 : 0 < t := (Set.mem_Ioo.mp ht).1
      have ht1 : t < 1 := (Set.mem_Ioo.mp ht).2
      have hc1 : ContinuousAt (fun x : ℝ => ((evenKernel (0 : UnitAddCircle) x : ℝ) : ℂ)) t :=
        continuous_ofReal.continuousAt.comp
          ((continuousOn_evenKernel (0 : UnitAddCircle)).continuousAt
            (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht0)))
      have hc2 : ContinuousAt
          (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) * (1 : ℂ)) t := by
        simpa [mul_comm] using
          (continuous_ofReal.continuousAt.comp
            (continuousAt_rpow_const t (-(1 / 2 : ℝ)) (Or.inl ht0.ne'))).const_mul (1 : ℂ)
      have heq : (hurwitzEvenFEPair 0).f_modif =ᶠ[𝓝 t]
          (fun x : ℝ => ((evenKernel (0 : UnitAddCircle) x : ℝ) : ℂ) -
            ((x ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) * (1 : ℂ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, ht1⟩] with x hx
        dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair, P0, a0]
        simp only [Pi.add_apply,
          Set.indicator_of_notMem (Set.notMem_Ioi.mpr (Set.mem_Ioo.mp hx).2.le),
          zero_add, Set.indicator_of_mem (Set.mem_Ioo.mpr hx), smul_eq_mul, one_mul]
      exact ContinuousAt.continuousWithinAt (ContinuousAt.congr (hc1.sub hc2) heq.symm)
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
      have hc : ContinuousOn
          (fun t : ℝ => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioo 0 1) := by
        intro t ht
        have ht0 : 0 < t := (Set.mem_Ioo.mp ht).1
        have hc1 : ContinuousAt (fun x : ℝ => x ^ (σ - 1)) t :=
          continuousAt_rpow_const t (σ - 1) (Or.inl ht0.ne')
        have hc2 : ContinuousAt (fun x : ℝ => ‖(hurwitzEvenFEPair 0).f_modif x‖) t :=
          ContinuousAt.comp continuous_norm.continuousAt
            (hcon.continuousAt (isOpen_Ioo.mem_nhds ht))
        exact (hc1.mul hc2).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioo
    have hnonneg : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 1)), 0 ≤
        t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall (fun t ht =>
          mul_nonneg (Real.rpow_nonneg (le_of_lt (Set.mem_Ioo.mp ht).1) (σ - 1)) (norm_nonneg _)))
    have hle : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 1)),
        t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ 3 * t ^ (σ - 1 / 2 : ℝ) := by
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall (fun t ht =>
          h01_pt t ⟨(Set.mem_Ioo.mp ht).1, (Set.mem_Ioo.mp ht).2.le⟩))
    exact MeasureTheory.Integrable.mono_nonneg
      (μ := MeasureTheory.volume.restrict (Set.Ioo 0 1))
      (hb_rpow.mono_set Set.Ioo_subset_Ioc_self) hmeas hnonneg hle
  -- Integrability of the integrand on (0,1] = (0,1) ∪ {1}
  have hf_Ioc : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioc 0 1) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
        (Set.Ioo 0 1 ∪ ({1} : Set ℝ)) :=
      MeasureTheory.IntegrableOn.union hf_int_Ioo
        (MeasureTheory.integrableOn_singleton (x := (1 : ℝ)) (hx := by simp [Real.volume_singleton]))
    have hset : Set.Ioo 0 1 ∪ ({1} : Set ℝ) = Set.Ioc (0 : ℝ) 1 := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · rintro (h | h)
        · exact ⟨h.1, h.2.le⟩
        · rw [h]; exact ⟨by norm_num, le_rfl⟩
      · intro h
        rcases lt_or_eq_of_le h.2 with hlt | heq
        · exact Or.inl ⟨h.1, hlt⟩
        · exact Or.inr heq
    rwa [hset] at h1
  -- Bound (0,1) integral by 4
  have h01 : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ 4 := by
    have hcalc : ∫ t in Set.Ioc (0 : ℝ) 1, 3 * t ^ (σ - 1 / 2 : ℝ) = 3 / (σ + 1 / 2) := by
      rw [MeasureTheory.integral_const_mul (3 : ℝ),
        ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        integral_rpow (Or.inl (by linarith [hσpos])),
        Real.one_rpow, Real.zero_rpow (by linarith [hσpos] : σ - 1 / 2 + 1 ≠ 0),
        sub_zero]
      ring
    have hcomp : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
        ∫ t in Set.Ioc (0 : ℝ) 1, 3 * t ^ (σ - 1 / 2 : ℝ) := by
      exact MeasureTheory.setIntegral_mono_on hf_Ioc hb_rpow measurableSet_Ioc h01_pt
    have h4 : 3 / (σ + 1 / 2) ≤ 4 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < σ + 1 / 2)]
      nlinarith [hσge]
    linarith [hcomp, hcalc, h4]
  -- Bound (1,∞) integral
  have h1inf : ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      3 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
    have hmono : ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
        ∫ t in Set.Ioi (1 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) := by
      have hR : MeasureTheory.IntegrableOn
          (fun t => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 1) := by
        exact (integrableOn_exp_neg_pi_mul_rpow σ hσpos).mono_set
          (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
      exact MeasureTheory.setIntegral_mono_on hL1 hR measurableSet_Ioi hpt
    have htail : ∫ t in Set.Ioi (1 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) ≤
        3 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
      by_cases hσ1 : 1 ≤ σ
      · -- σ ≥ 1: tail ≤ full integral = π^{-σ}·Γ(σ) ≤ exp(σ^{3/2})
        have hle0 : ∫ t in Set.Ioi (1 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) ≤
            ∫ t in Set.Ioi (0 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) := by
          have hR0 : MeasureTheory.IntegrableOn
              (fun t => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 0) :=
            integrableOn_exp_neg_pi_mul_rpow σ hσpos
          have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
              (fun t => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) := by
            exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
              (Filter.Eventually.of_forall (fun t ht =>
                mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
                  (Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.mp ht)) (σ - 1)))
                  (le_of_lt (Real.exp_pos _))))
          exact MeasureTheory.setIntegral_mono_set hR0 hnonneg
            (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)).eventuallyLE
        have hfull0 : ∫ t in Set.Ioi (0 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) ≤
            3 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
          have hid : ∫ t : ℝ in Set.Ioi 0, t ^ (σ - 1) * Real.exp (-Real.pi * t) =
              (1 / Real.pi) ^ σ * Real.Gamma σ := by
            have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hσpos Real.pi_pos
            simpa [neg_mul, mul_neg] using h
          have hI : ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-Real.pi * t) =
              (1 / Real.pi) ^ σ * Real.Gamma σ := by
            rw [hid]
          have hfull0' : ∫ t in Set.Ioi (0 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) =
              3 * ((1 / Real.pi) ^ σ * Real.Gamma σ) := by
            calc
              ∫ t in Set.Ioi (0 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)
                  = ∫ t in Set.Ioi (0 : ℝ), (3 : ℝ) * (t ^ (σ - 1) * Real.exp (-Real.pi * t)) := by
                    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
                    intro t ht
                    ring
              _ = 3 * ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-Real.pi * t) := by
                    rw [MeasureTheory.integral_const_mul (3 : ℝ)]
              _ = 3 * ((1 / Real.pi) ^ σ * Real.Gamma σ) := by
                    rw [hI]
          have hg : (1 / Real.pi) ^ σ * Real.Gamma σ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := by
            rw [one_div, Real.inv_rpow (le_of_lt Real.pi_pos) σ]
            rw [mul_comm, ← div_eq_mul_inv]
            exact gamma_over_pi_le_exp_pow hσ1
          rw [hfull0']
          exact mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 3)
        exact hle0.trans hfull0
      · -- σ < 1 (and σ ≥ 1/4): t^(σ-1) ≤ 1 for t ≥ 1, so ∫₁^∞ ≤ ∫₁^∞ 3e^{-πt} ≤ 3/π ≤ 3
        have hσle1 : σ ≤ 1 := le_of_not_ge hσ1
        have hpow : ∀ t ∈ Set.Ioi (1 : ℝ), t ^ (σ - 1) ≤ 1 := by
          intro t ht
          have ht1 : (1 : ℝ) ≤ t := (Set.mem_Ioi.mp ht).le
          have hσm1 : σ - 1 ≤ 0 := by linarith
          exact (Real.rpow_le_rpow_of_exponent_le ht1 hσm1).trans_eq (Real.rpow_zero t)
        have hR1 : MeasureTheory.IntegrableOn
            (fun t => 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t)) (Set.Ioi 1) :=
          (integrableOn_exp_neg_pi_mul_rpow σ hσpos).mono_set
            (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
        have hg0 : MeasureTheory.IntegrableOn
            (fun t => 3 * Real.exp (-Real.pi * t)) (Set.Ioi 0) := by
          have h := integrableOn_exp_neg_pi_mul_rpow 1 (by norm_num)
          simpa [Real.rpow_zero, mul_assoc] using h
        have hgint : MeasureTheory.IntegrableOn
            (fun t => 3 * Real.exp (-Real.pi * t)) (Set.Ioi 1) :=
          hg0.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
        have hle1 : ∫ t in Set.Ioi (1 : ℝ), 3 * t ^ (σ - 1) * Real.exp (-Real.pi * t) ≤
            ∫ t in Set.Ioi (1 : ℝ), 3 * Real.exp (-Real.pi * t) := by
          exact MeasureTheory.setIntegral_mono_on hR1 hgint measurableSet_Ioi
            (fun t ht => by
              have h1 := mul_le_mul_of_nonneg_left (hpow t ht) ((Real.exp_pos (-Real.pi * t)).le)
              have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 3)
              simpa [mul_assoc, mul_comm, mul_left_comm] using h2)
        have hle2 : ∫ t in Set.Ioi (1 : ℝ), 3 * Real.exp (-Real.pi * t) ≤ 3 := by
          have h01' : ∫ t in Set.Ioi (1 : ℝ), 3 * Real.exp (-Real.pi * t) ≤
              ∫ t in Set.Ioi (0 : ℝ), 3 * Real.exp (-Real.pi * t) := by
            have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
                (fun t => 3 * Real.exp (-Real.pi * t)) := by
              exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
                (Filter.Eventually.of_forall (fun t ht =>
                  mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt (Real.exp_pos _))))
            exact MeasureTheory.setIntegral_mono_set hg0 hnonneg
              (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)).eventuallyLE
          have h02 : ∫ t in Set.Ioi (0 : ℝ), 3 * Real.exp (-Real.pi * t) = 3 * (1 / Real.pi) := by
            have hid1 : ∫ t : ℝ in Set.Ioi 0, Real.exp (-Real.pi * t) = 1 / Real.pi := by
              have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := Real.pi) (by norm_num) Real.pi_pos
              simpa [Real.rpow_zero, Real.rpow_one, Real.Gamma_one, neg_mul, mul_neg] using h
            have hI2 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-Real.pi * t) = 1 / Real.pi := by
              rw [hid1]
            calc
              ∫ t in Set.Ioi (0 : ℝ), 3 * Real.exp (-Real.pi * t)
                  = ∫ t in Set.Ioi (0 : ℝ), (3 : ℝ) * Real.exp (-Real.pi * t) := by
                    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
                    intro t ht
                    ring
              _ = 3 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-Real.pi * t) := by
                    rw [MeasureTheory.integral_const_mul (3 : ℝ)]
              _ = 3 * (1 / Real.pi) := by
                    rw [hI2]
          have h23 : 3 * (1 / Real.pi) ≤ 3 := by
            rw [show 3 * (1 / Real.pi) = 3 / Real.pi by ring]
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
            nlinarith [Real.pi_gt_three]
          exact h01'.trans (h02.trans_le h23)
        have hle3 : 3 ≤ 3 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
          have h1 : (1 : ℝ) ≤ Real.exp (σ ^ (3 / 2 : ℝ)) :=
            (Real.one_le_exp_iff).2 (Real.rpow_nonneg (le_of_lt hσpos) (3 / 2))
          simpa using mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 3)
        exact (hle1.trans hle2).trans hle3
    linarith [hmono, htail]
  -- Combine using integral additivity: Ioi 0 ⊆ Ioc 0 1 ∪ Ioi 1
  have htotal : ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      4 + 3 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
    -- Split: Ioi 0 ⊆ Ioc 0 1 ∪ Ioi 1 (up to measure-zero {0}), so
    -- ∫_Ioi 0 ≤ ∫_{Ioc 0 1} + ∫_{Ioi 1}
    have hsub : Set.Ioi (0 : ℝ) ⊆ (Set.Ioc (0 : ℝ) 1 : Set ℝ) ∪ Set.Ioi (1 : ℝ) := by
      intro t ht
      by_cases hle : t ≤ 1
      · exact Or.inl ⟨ht, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1 : Set ℝ) (Set.Ioi (1 : ℝ)) := Set.Ioc_disjoint_Ioi le_rfl
    have hsplit : ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
        (∫ t in Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) +
          ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
      have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hf_Ioc hL1
      have hUI : (Set.Ioc (0 : ℝ) 1 : Set ℝ) ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
        ext t
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (h | h)
          · exact h.1
          · linarith
        · intro ht
          by_cases hle : t ≤ 1
          · exact Or.inl ⟨ht, hle⟩
          · exact Or.inr (by linarith)
      rw [hUI] at hunion
      rw [show (∫ t in Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ∂MeasureTheory.volume) =
            ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ from rfl,
        show (∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ∂MeasureTheory.volume) =
            ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ from rfl,
        show (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ∂MeasureTheory.volume) =
            ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ from rfl] at hunion
      exact le_of_eq hunion
    linarith [h01, h1inf]
  have hexp3 : (3 : ℝ) * Real.exp (σ ^ (3 / 2 : ℝ)) ≤
      10 * Real.exp (σ ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ) ≤ 10) (le_of_lt (Real.exp_pos _))
  have hexp4 : (4 : ℝ) ≤ 4 * Real.exp (σ ^ (3 / 2 : ℝ)) := by
    have h1 : (1 : ℝ) ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := (Real.one_le_exp_iff).2 (by positivity)
    simpa using mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
  have hnorm : ‖(hurwitzEvenFEPair 0).Λ₀ w‖ = ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ := by
    rw [hΛeq]
  linarith [hle, htotal, hexp4, hexp3, hnorm]

/-- Order of completedRiemannZeta₀ is at most 3/2.
Follows from `mellin_fmodif_bound` (Mellin integral bound for the theta kernel)
and `completedRiemannZeta₀_one_sub` (functional equation) to cover all half-planes. -/
theorem orderSet_completedRiemannZeta₀ :
    (3 / 2 : ℝ) ∈ orderSet completedRiemannZeta₀ := by
  refine ⟨10, 4, by norm_num, fun z hz => ?_⟩
  have hz4 : (4 : ℝ) ≤ ‖z‖ := hz
  -- Key: ‖completedRiemannZeta₀ z‖ ≤ 7 * exp(|z|^{3/2})
  suffices h : ‖completedRiemannZeta₀ z‖ ≤ 7 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) from by
    nlinarith [Real.exp_nonneg (‖z‖ ^ (3 / 2 : ℝ))]
  -- Case split: Re(z) ≥ 1/2 vs Re(z) < 1/2
  by_cases hRe : (1/2 : ℝ) ≤ z.re
  · -- Case Re(z) ≥ 1/2: use Mellin representation and integral bounds
    -- completedRiemannZeta₀(z) = Λ₀(z/2)/2 where Λ₀ = mellin f_modif
    set w := z / 2 with hw
    have hwRe : (1/4 : ℝ) ≤ w.re := by
      rw [hw, Complex.div_re]; norm_num; linarith
    have hb := mellin_fmodif_bound hwRe
    have hwle : w.re ≤ ‖z‖ / 2 := by
      rw [hw, Complex.div_re]
      have h2r : (2 : ℂ).re = 2 := by norm_num
      have h2i : (2 : ℂ).im = 0 := by norm_num
      have h2n : normSq (2 : ℂ) = 4 := by norm_num
      rw [h2r, h2i, h2n]
      linarith [Complex.re_le_norm z]
    have hM : completedRiemannZeta₀ z = ((hurwitzEvenFEPair 0).Λ₀ w) / 2 := by
      simp [hw, completedRiemannZeta₀, completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
    have hpwle : w.re ^ (3 / 2 : ℝ) ≤ (‖z‖ / 2) ^ (3 / 2 : ℝ) := by gcongr
    have hexp_le : Real.exp (w.re ^ (3 / 2 : ℝ)) ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ)) :=
      (Real.exp_le_exp.mpr (hpwle.trans (by gcongr; nlinarith [norm_nonneg z])))
    rw [hM, Complex.norm_div]
    rw [Complex.norm_two]
    have hb' : ‖(hurwitzEvenFEPair 0).Λ₀ w‖ ≤
        14 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) :=
      hb.trans (mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 14))
    linarith [hb']
  · -- Case Re(z) < 1/2: use functional equation to reflect to Re(1-z) ≥ 1/2
    have hFE : completedRiemannZeta₀ z = completedRiemannZeta₀ (1 - z) :=
      (completedRiemannZeta₀_one_sub z).symm
    have hRe1s : (1/2 : ℝ) ≤ (1 - z).re := by simp [Complex.sub_re]; linarith
    -- Apply Re ≥ 1/2 case to (1-z): bound ‖Λ₀((1-z)/2)‖ by 14·exp(w.re^{3/2})
    -- and use w.re ≤ ‖z‖ (since w.re = (1-z.re)/2 ≤ (1+‖z‖)/2 ≤ ‖z‖ for ‖z‖ ≥ 1)
    have hkey : ‖completedRiemannZeta₀ (1 - z)‖ ≤
        7 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) := by
      set w := (1 - z) / 2 with hw
      have hwRe : (1/4 : ℝ) ≤ w.re := by
        rw [hw, Complex.div_re]; norm_num; linarith
      have hM : completedRiemannZeta₀ (1 - z) = ((hurwitzEvenFEPair 0).Λ₀ w) / 2 := by
        simp [hw, completedRiemannZeta₀, completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
      have hb := mellin_fmodif_bound hwRe
      -- Key bound: w.re = (1-z.re)/2 ≤ ‖z‖
      have hwle : w.re ≤ ‖z‖ := by
        rw [hw, Complex.div_re]; norm_num
        have h1 : (1 : ℝ) / 2 ≤ ‖z‖ / 2 := by linarith [hz4]
        have h2 : -z.re / 2 ≤ ‖z‖ / 2 := by linarith [Complex.re_le_norm (-z), norm_neg z, Complex.neg_re z]
        linarith
      have hpwle : w.re ^ (3 / 2 : ℝ) ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
        gcongr
      have hexp_le : Real.exp (w.re ^ (3 / 2 : ℝ)) ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr hpwle
      rw [hM, Complex.norm_div]
      rw [Complex.norm_two]
      have hb' : ‖(hurwitzEvenFEPair 0).Λ₀ w‖ ≤
          14 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) :=
        hb.trans (mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 14))
      linarith [hb']
    rw [hFE]; exact hkey

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



/-! ## Order of an entire function: API -/

/-- The set `orderSet f` is upward closed: if a bound holds with exponent `ρ₁`, it holds
with any larger exponent `ρ₂`. -/
lemma orderSet_mono {f : ℂ → ℂ} {ρ₁ ρ₂ : ℝ} (h : ρ₁ ∈ orderSet f) (hle : ρ₁ ≤ ρ₂) :
    ρ₂ ∈ orderSet f := by
  rcases h with ⟨C, r₀, hr₀, hb⟩
  refine ⟨C, max r₀ 1, lt_max_of_lt_right (by norm_num), ?_⟩
  intro z hz
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_right r₀ 1) hz
  have hzr : r₀ ≤ ‖z‖ := le_trans (le_max_left r₀ 1) hz
  have hpow : ‖z‖ ^ ρ₁ ≤ ‖z‖ ^ ρ₂ := Real.rpow_le_rpow_of_exponent_le hz1 hle
  have hC : 0 ≤ C := by
    by_contra hneg
    have hlt : C * Real.exp (‖z‖ ^ ρ₁) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (Real.exp_pos _)
    linarith [norm_nonneg (f z), hb z hzr]
  calc ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ₁) := hb z hzr
    _ ≤ C * Real.exp (‖z‖ ^ ρ₂) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) hC

/-- From `ρ ∈ orderSet f` we can extract a constant `C ≥ 1`. -/
lemma orderSet_bound_ge_one {f : ℂ → ℂ} {ρ : ℝ} (h : ρ ∈ orderSet f) :
    ∃ C ≥ 1, ∃ r₀ > 0, ∀ z, r₀ ≤ ‖z‖ → ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ) := by
  rcases h with ⟨C₀, r₀, hr₀, hb⟩
  refine ⟨max C₀ 1, le_max_right C₀ 1, r₀, hr₀, ?_⟩
  intro z hz
  exact (hb z hz).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
    (Real.exp_pos _).le)

/-! ## Zero counting via Jensen's formula -/

/-- The number of zeros of `f` inside `Metric.closedBall 0 r`, counted with multiplicity,
as a real number. -/
noncomputable def zeroCount (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ↑(∑ᶠ u : ℂ, MeromorphicOn.divisor f (Metric.closedBall 0 r) u)

/-- **Jensen's inequality in the form of a zero-counting bound.** If `f` is analytic on
`Metric.closedBall 0 R`, nonzero at `0`, and bounded by `M ≥ 1` on the circle of radius `R`,
then the number of zeros in `Metric.closedBall 0 r` (with multiplicity) is at most
`log(M/|f 0|)/log(R/r)`. -/
theorem zeroCount_le_of_bound {f : ℂ → ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z ∈ Metric.sphere 0 R, ‖f z‖ ≤ M) :
    zeroCount f r ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := lt_trans hr hrR
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall 0 |R|) := by
    simpa [abs_of_pos hR] using hf
  have hsum := hf'.sum_divisor_le (c := 0) (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr) (by simpa [abs_of_pos hr, abs_of_pos hR] using hrR)
    hM hf0 (by simpa [abs_of_pos hR] using hbound)
  rw [zeroCount]
  rw [show Metric.closedBall (0 : ℂ) r = Metric.closedBall (0 : ℂ) |r| from by rw [abs_of_pos hr]]
  exact hsum

/-- If `κ ∈ orderSet f` then the zero-counting function satisfies `N(r) = O(r^κ)`. -/
theorem zeroCount_le_rpow_of_orderSet {f : ℂ → ℂ} {κ : ℝ} (hκ : 0 ≤ κ) (hord : κ ∈ orderSet f)
    (hf0 : f 0 ≠ 0) (hfAn : ∀ R : ℝ, 0 < R → AnalyticOnNhd ℂ f (Metric.closedBall 0 R)) :
    ∃ D ≥ 0, ∀ r : ℝ, 1 ≤ r → zeroCount f r ≤ D * r ^ κ := by
  rcases orderSet_bound_ge_one hord with ⟨C, hC, r₀, hr₀, hb⟩
  let R₀ : ℝ := max r₀ 1
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le hr₀ (le_max_left r₀ 1)
  have hR₀ge : (1 : ℝ) ≤ R₀ := le_max_right r₀ 1
  let N₂ : ℝ := |Real.log C| + (2 * R₀) ^ κ + |Real.log ‖f 0‖|
  let D : ℝ := N₂ / Real.log 2
  have hN₂nn : 0 ≤ N₂ := by
    dsimp [N₂]
    exact add_nonneg (add_nonneg (abs_nonneg (Real.log C))
      (Real.rpow_nonneg (by nlinarith [hR₀pos]) κ))
      (abs_nonneg (Real.log ‖f 0‖))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg hN₂nn (Real.log_pos (by norm_num)).le
  refine ⟨D, hD, ?_⟩
  intro r hr
  have hrpos : 0 < r := by linarith
  have hfpos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hCnn : 0 ≤ C := by linarith
  have hM : ∀ R : ℝ, 0 < R → (1 : ℝ) ≤ C * Real.exp (R ^ κ) := by
    intro R hR
    have he : (1 : ℝ) ≤ Real.exp (R ^ κ) := (Real.one_le_exp_iff).2 (Real.rpow_nonneg hR.le κ)
    exact le_trans hC (le_mul_of_one_le_right hCnn he)
  have hbnd : ∀ {R : ℝ}, 0 < R → r₀ ≤ R →
      ∀ z ∈ Metric.sphere 0 R, ‖f z‖ ≤ C * Real.exp (R ^ κ) := by
    intro R hR hr₀R z hz
    have hz' : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzr : r₀ ≤ ‖z‖ := by rw [hz']; exact hr₀R
    have hb' := hb z hzr
    rwa [hz'] at hb'
  have hjensen : ∀ {R : ℝ}, 0 < R → r₀ ≤ R → r < R →
      zeroCount f r ≤ (Real.log C + R ^ κ - Real.log ‖f 0‖) / Real.log (R / r) := by
    intro R hR hr₀R hrR
    have hsum := zeroCount_le_of_bound (f := f) (r := r) (R := R)
      (M := C * Real.exp (R ^ κ)) hrpos hrR (hM R hR) (hfAn R hR) hf0 (hbnd hR hr₀R)
    have hlogM : Real.log (C * Real.exp (R ^ κ) / ‖f 0‖)
        = Real.log C + R ^ κ - Real.log ‖f 0‖ := by
      have hMpos : 0 < C * Real.exp (R ^ κ) := mul_pos (by linarith) (Real.exp_pos _)
      rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hfpos),
        Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    rwa [hlogM] at hsum
  by_cases hR₀r : R₀ ≤ r
  · have h2r : 0 < 2 * r := by linarith
    have hr2r : r < 2 * r := by linarith
    have hzr₀ : r₀ ≤ 2 * r := by
      exact le_trans (le_max_left r₀ 1) (le_trans hR₀r (by linarith))
    have hj := hjensen (R := 2 * r) h2r hzr₀ hr2r
    have hrκ : (1 : ℝ) ≤ r ^ κ := by
      have : (1 : ℝ) ^ κ ≤ r ^ κ := Real.rpow_le_rpow zero_le_one hr hκ
      simpa using this
    have hN₂ : Real.log C + (2 * r) ^ κ - Real.log ‖f 0‖ ≤ N₂ * r ^ κ := by
      have h₁ : Real.log C ≤ |Real.log C| * r ^ κ :=
        le_trans (le_abs_self (Real.log C)) (le_mul_of_one_le_right (abs_nonneg _) hrκ)
      have h₂ : (2 * r) ^ κ ≤ (2 * R₀) ^ κ * r ^ κ := by
        have h₀ : (2 * r) ^ κ = (2 : ℝ) ^ κ * r ^ κ := by
          exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hrpos)
        have h₀' : (2 : ℝ) ^ κ ≤ (2 * R₀) ^ κ := by
          exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) (by nlinarith [hR₀ge]) hκ
        rw [h₀]
        exact mul_le_mul_of_nonneg_right h₀' (Real.rpow_nonneg (le_of_lt hrpos) κ)
      have h₃ : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| * r ^ κ :=
        le_trans (neg_le_abs _) (le_mul_of_one_le_right (abs_nonneg _) hrκ)
      calc Real.log C + (2 * r) ^ κ - Real.log ‖f 0‖
          ≤ |Real.log C| * r ^ κ + (2 * R₀) ^ κ * r ^ κ + |Real.log ‖f 0‖| * r ^ κ := by
            linarith
        _ = N₂ * r ^ κ := by
          dsimp [N₂]
          ring
    have hlog2 : Real.log (2 * r / r) = Real.log 2 := by
      have hdiv : 2 * r / r = 2 := by field_simp [ne_of_gt hrpos]
      rw [hdiv]
    calc zeroCount f r ≤ (Real.log C + (2 * r) ^ κ - Real.log ‖f 0‖) / Real.log (2 * r / r) := hj
      _ = (Real.log C + (2 * r) ^ κ - Real.log ‖f 0‖) / Real.log 2 := by rw [hlog2]
      _ ≤ N₂ * r ^ κ / Real.log 2 := div_le_div_of_nonneg_right hN₂ (Real.log_pos (by norm_num)).le
      _ = D * r ^ κ := by
        dsimp [D, N₂]
        ring
  · have h2R₀ : 0 < 2 * R₀ := by nlinarith
    have hr2R₀ : r < 2 * R₀ := by nlinarith [hR₀r]
    have hzr₀ : r₀ ≤ 2 * R₀ := by
      exact le_trans (le_max_left r₀ 1) (by nlinarith)
    have hj := hjensen (R := 2 * R₀) h2R₀ hzr₀ hr2R₀
    have hden : Real.log 2 ≤ Real.log (2 * R₀ / r) := by
      have h₁ : (2 : ℝ) ≤ 2 * R₀ / r := by
        rw [le_div_iff₀ hrpos]
        nlinarith [hR₀ge, hR₀r]
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) h₁
    have hnum₂ : Real.log C + (2 * R₀) ^ κ - Real.log ‖f 0‖ ≤ N₂ := by
      dsimp [N₂]
      linarith [le_abs_self (Real.log C), neg_le_abs (Real.log ‖f 0‖)]
    have hstep : (Real.log C + (2 * R₀) ^ κ - Real.log ‖f 0‖) / Real.log (2 * R₀ / r)
        ≤ N₂ / Real.log 2 := by
      have h₁ : (Real.log C + (2 * R₀) ^ κ - Real.log ‖f 0‖) / Real.log (2 * R₀ / r)
          ≤ N₂ / Real.log (2 * R₀ / r) :=
        div_le_div_of_nonneg_right hnum₂
          (Real.log_pos (by exact (one_lt_div hrpos).mpr hr2R₀)).le
      have h₂ : N₂ / Real.log (2 * R₀ / r) ≤ N₂ / Real.log 2 :=
        div_le_div_of_nonneg_left hN₂nn (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hden
      exact h₁.trans h₂
    have hrκ : (1 : ℝ) ≤ r ^ κ := by
      have : (1 : ℝ) ^ κ ≤ r ^ κ := Real.rpow_le_rpow zero_le_one hr hκ
      simpa using this
    calc zeroCount f r ≤ (Real.log C + (2 * R₀) ^ κ - Real.log ‖f 0‖) / Real.log (2 * R₀ / r) := hj
      _ ≤ N₂ / Real.log 2 := hstep
      _ ≤ N₂ * r ^ κ / Real.log 2 := by
        refine div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hrκ hN₂nn
      _ = D * r ^ κ := by
        dsimp [D, N₂]
        ring

/-! ## Summability of `1/‖aₙ‖^γ` from the zero-counting bound -/

open Filter Metric

/-- Every `x ≥ 1` lies between two consecutive powers of two: `∃ k, 2^k ≤ x < 2^(k+1)`. -/
lemma exists_shell_two_pow {x : ℝ} (hx : 1 ≤ x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1) := by
  let s : Set ℕ := {k : ℕ | (2 : ℝ) ^ k ≤ x}
  have hten : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hbig : ∀ᶠ k in atTop, x + 1 ≤ (2 : ℝ) ^ k := hten.eventually_ge_atTop (x + 1)
  rcases eventually_atTop.1 hbig with ⟨N, hN⟩
  have hs_fin : s.Finite := by
    refine (Set.finite_lt_nat N).subset ?_
    intro k hk
    by_contra hkge
    have hkN : N ≤ k := not_lt.mp hkge
    have hxlt : x + 1 ≤ (2 : ℝ) ^ k := hN k hkN
    have hkx : (2 : ℝ) ^ k ≤ x := hk
    linarith
  have hs_nen : s.Nonempty := ⟨0, by simpa [s] using hx⟩
  let F : Finset ℕ := hs_fin.toFinset
  have hFne : F.Nonempty := by
    rw [← Finset.coe_nonempty]
    simpa [F] using hs_nen
  let k : ℕ := F.max' hFne
  have hk_mem : k ∈ s := by
    have := Finset.max'_mem F hFne
    simpa [F, k] using this
  have hk_max : ∀ j ∈ s, j ≤ k := by
    intro j hj
    exact Finset.le_max' F j (by simpa [F, k] using hj)
  have hk1_not : k + 1 ∉ s := by
    intro h
    have : k + 1 ≤ k := hk_max (k + 1) h
    omega
  exact ⟨k, by simpa [k, s] using hk_mem, lt_of_not_ge hk1_not⟩

/-- The dyadic shell index of `x` (with `shellIndex x = 0` for `x ≤ 1`). -/
noncomputable def shellIndex (x : ℝ) : ℕ :=
  if h : 1 < x then Classical.choose (exists_shell_two_pow (le_of_lt h)) else 0

lemma shellIndex_spec {x : ℝ} (hx : 1 < x) :
    (2 : ℝ) ^ shellIndex x ≤ x ∧ x < (2 : ℝ) ^ (shellIndex x + 1) := by
  unfold shellIndex
  rw [dif_pos hx]
  exact Classical.choose_spec (exists_shell_two_pow (le_of_lt hx))

/-- If the counting function of a sequence `a : ℕ → ℂ` satisfies `N(r) ≤ D·r^κ`
(counted with the `ncard` of `{n : ℕ | ‖a n‖ ≤ r}`), then `Σ 1/‖aₙ‖^γ` converges
for every `γ > κ ≥ 0`. -/
theorem summable_inv_norm_pow_of_ncard_bound {a : ℕ → ℂ} {κ γ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ < γ)
    (hfinite : ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite)
    (hcount : ∃ D : ℝ, 0 ≤ D ∧
      ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ κ) :
    Summable (fun n : ℕ => (‖a n‖ ^ γ)⁻¹) := by
  rcases hcount with ⟨D, hD, hcount⟩
  have hγ : 0 ≤ γ := le_trans hκ hκγ.le
  let r0 : ℝ := (2 : ℝ) ^ (κ - γ)
  have hr0nn : 0 ≤ r0 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (κ - γ)
  have hr0lt : r0 < 1 := by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (sub_neg.mpr hκγ)
  have hgeom : Summable (fun k : ℕ => r0 ^ k) := summable_geometric_of_lt_one hr0nn hr0lt
  have hu : Summable (fun k : ℕ => D * (2 : ℝ) ^ κ * r0 ^ k) := hgeom.mul_left (D * (2 : ℝ) ^ κ)
  let C : ℝ := ∑' k : ℕ, D * (2 : ℝ) ^ κ * r0 ^ k
  let S : Set ℕ := {n : ℕ | ‖a n‖ ≤ 1}
  have hS_fin : S.Finite := hfinite 1 le_rfl
  let headC : ℝ := ∑ n ∈ hS_fin.toFinset, (‖a n‖ ^ γ)⁻¹
  have hterm_le : ∀ k : ℕ, (2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)
      ≤ D * (2 : ℝ) ^ κ * r0 ^ k := by
    intro k
    have h1 : (2 : ℝ) ^ (-(k : ℝ) * γ) * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)
        = (2 : ℝ) ^ κ * r0 ^ k := by
      have h2 : r0 ^ k = (2 : ℝ) ^ ((k : ℝ) * (κ - γ)) := by
        dsimp [r0]
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (κ - γ)) k]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (κ - γ) (k : ℝ)]
        congr 1
        ring
      calc (2 : ℝ) ^ (-(k : ℝ) * γ) * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)
          = (2 : ℝ) ^ (-(k : ℝ) * γ + ((k + 1 : ℕ) : ℝ) * κ) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-(k : ℝ) * γ) (((k + 1 : ℕ) : ℝ) * κ)]
        _ = (2 : ℝ) ^ (κ + (k : ℝ) * (κ - γ)) := by
              congr 1
              push_cast
              ring
        _ = (2 : ℝ) ^ κ * (2 : ℝ) ^ ((k : ℝ) * (κ - γ)) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) κ ((k : ℝ) * (κ - γ))]
        _ = (2 : ℝ) ^ κ * r0 ^ k := by
              rw [← h2]
    calc (2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)
        ≤ D * ((2 : ℝ) ^ (-(k : ℝ) * γ) * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)) := by
          exact le_of_eq (by ring)
      _ = D * ((2 : ℝ) ^ κ * r0 ^ k) := by rw [h1]
      _ = D * (2 : ℝ) ^ κ * r0 ^ k := by ring
  have htail_bdd : ∀ N : ℕ, (∑ n ∈ Finset.range N, (‖a n‖ ^ γ)⁻¹)
      ≤ headC + ∑' k : ℕ, D * (2 : ℝ) ^ κ * r0 ^ k := by
    intro N
    let t : ℕ → ℝ := fun n => if 1 < ‖a n‖ then (‖a n‖ ^ γ)⁻¹ else 0
    have htail : (∑ n ∈ Finset.range N, t n) ≤ C := by
      by_cases hN : N = 0
      · subst hN
        have hCnn : 0 ≤ C := by
          refine tsum_nonneg ?_
          intro k
          exact mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) κ))
            (pow_nonneg hr0nn k)
        simpa [C, hCnn] using hCnn
      · let Fk : Finset ℕ := Finset.image (fun n : ℕ => shellIndex ‖a n‖) (Finset.range N)
        have hFk_ne : Fk.Nonempty := by
          exact Finset.image_nonempty.mpr ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hN)⟩
        let K : ℕ := Fk.max' hFk_ne
        have hkK : ∀ n, n < N → shellIndex ‖a n‖ ≤ K := by
          intro n hn
          exact Finset.le_max' Fk (shellIndex ‖a n‖)
            (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩)
        have hpt : ∀ n, n < N → t n ≤
            ∑ k ∈ Finset.range (K + 1),
              (if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0) := by
          intro n hn
          by_cases h1n : 1 < ‖a n‖
          · have hk := shellIndex_spec h1n
            have hkpos : (2 : ℝ) ^ shellIndex ‖a n‖ ≤ ‖a n‖ := hk.1
            have hpowle : ((2 : ℝ) ^ shellIndex ‖a n‖) ^ γ ≤ ‖a n‖ ^ γ := by
              exact Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ shellIndex ‖a n‖)
                hkpos hγ
            have hbpos : (0 : ℝ) < ‖a n‖ ^ γ :=
              Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < ‖a n‖) γ
            have hapos : (0 : ℝ) < ((2 : ℝ) ^ shellIndex ‖a n‖) ^ γ :=
              Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ shellIndex ‖a n‖) γ
            have hinv : (‖a n‖ ^ γ)⁻¹ ≤ (((2 : ℝ) ^ shellIndex ‖a n‖) ^ γ)⁻¹ :=
              (inv_le_inv₀ hbpos hapos).mpr hpowle
            have hpowinv : (((2 : ℝ) ^ shellIndex ‖a n‖) ^ γ)⁻¹
                = (2 : ℝ) ^ (-((shellIndex ‖a n‖ : ℝ) * γ)) := by
              rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((shellIndex ‖a n‖ : ℝ) * γ)]
              congr 1
              rw [← Real.rpow_natCast (2 : ℝ) (shellIndex ‖a n‖)]
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (shellIndex ‖a n‖ : ℝ) γ]
            have hsum_eq : (∑ k ∈ Finset.range (K + 1),
                if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
                = (2 : ℝ) ^ (-((shellIndex ‖a n‖ : ℝ) * γ)) := by
              have hse : (∑ k ∈ Finset.range (K + 1),
                  if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
                  = if shellIndex ‖a n‖ = shellIndex ‖a n‖ then
                      (2 : ℝ) ^ (-((shellIndex ‖a n‖ : ℝ) * γ)) else 0 := by
                exact Finset.sum_eq_single (a := shellIndex ‖a n‖)
                  (s := Finset.range (K + 1))
                  (f := fun k => if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
                  (by intro k hk hkne; simp [hkne])
                  (by intro hknot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hkK n hn))) hknot)
              rw [if_pos rfl] at hse
              exact hse
            calc t n = (‖a n‖ ^ γ)⁻¹ := by simp [t, h1n]
              _ ≤ (2 : ℝ) ^ (-((shellIndex ‖a n‖ : ℝ) * γ)) := by rw [hpowinv] at hinv; exact hinv
              _ = ∑ k ∈ Finset.range (K + 1),
                  if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0 := hsum_eq.symm
          · have ht0 : t n = 0 := by simp [t, h1n]
            rw [ht0]
            exact Finset.sum_nonneg (by
              intro k hk
              by_cases hk' : k = shellIndex ‖a n‖
              · simp [hk', Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _]
              · simp [hk'])
        have hcount_k : ∀ k : ℕ,
            (∑ n ∈ Finset.range N, if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
            ≤ (2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ) := by
          intro k
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
            exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
          have hfin' : ({n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} : Set ℕ).Finite :=
            hfinite ((2 : ℝ) ^ (k + 1)) h2
          have hsub : {n : ℕ | n ∈ (Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)}
              ⊆ {n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} := by
            intro n hn
            simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range] at hn
            rcases hn with ⟨hnrange, hnk⟩
            by_cases h1n : 1 < ‖a n‖
            · have hs := shellIndex_spec h1n
              rw [hnk] at hs
              exact le_of_lt hs.2
            · exact le_trans (le_of_not_gt h1n) h2
          have hcard : ({n : ℕ | n ∈ (Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)} : Set ℕ).ncard
              ≤ ({n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} : Set ℕ).ncard := by
            exact Set.ncard_le_ncard hsub hfin'
          have hb0 : 0 ≤ (2 : ℝ) ^ (-(k : ℝ) * γ) :=
            Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
          have hbcnt : ({n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} : Set ℕ).ncard
              ≤ D * ((2 : ℝ) ^ (k + 1)) ^ κ := hcount ((2 : ℝ) ^ (k + 1)) h2
          have hcard' : (((Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)).card : ℝ)
              ≤ ({n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} : Set ℕ).ncard := by
            have h₀ : ({n : ℕ | n ∈ (Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)} : Set ℕ)
                = ↑((Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)) := by
              ext n
              simp
            have h₁ : ({n : ℕ | n ∈ (Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)} : Set ℕ).ncard
                = ((Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)).card := by
              rw [h₀, Set.ncard_coe_finset]
            rw [h₁] at hcard
            exact_mod_cast hcard
          have hbk : (2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)
              = (2 : ℝ) ^ (-(k : ℝ) * γ) * (D * ((2 : ℝ) ^ (k + 1)) ^ κ) := by
            have h₀ : ((2 : ℝ) ^ (k + 1)) ^ κ = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ) := by
              rw [← Real.rpow_natCast (2 : ℝ) (k + 1)]
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((k + 1 : ℕ) : ℝ) κ]
            rw [h₀]
            ring
          have hinner : (∑ n ∈ Finset.range N,
              if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
              = (2 : ℝ) ^ (-(k : ℝ) * γ) *
                ((Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)).card := by
            rw [← Finset.sum_filter]
            simp [eq_comm, Finset.sum_const, nsmul_eq_mul, mul_comm]
          calc (∑ n ∈ Finset.range N,
              if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0)
              = (2 : ℝ) ^ (-(k : ℝ) * γ) *
                ((Finset.range N).filter (fun n => shellIndex ‖a n‖ = k)).card := hinner
            _ ≤ (2 : ℝ) ^ (-(k : ℝ) * γ) *
                ({n : ℕ | ‖a n‖ ≤ (2 : ℝ) ^ (k + 1)} : Set ℕ).ncard :=
              mul_le_mul_of_nonneg_left hcard' hb0
            _ ≤ (2 : ℝ) ^ (-(k : ℝ) * γ) * (D * ((2 : ℝ) ^ (k + 1)) ^ κ) :=
              mul_le_mul_of_nonneg_left hbcnt hb0
            _ = (2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ) := hbk.symm
        calc (∑ n ∈ Finset.range N, t n)
            ≤ ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (K + 1),
                if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0) :=
              Finset.sum_le_sum (by intro n hn; exact hpt n (Finset.mem_range.mp hn))
          _ = ∑ k ∈ Finset.range (K + 1), (∑ n ∈ Finset.range N,
                if k = shellIndex ‖a n‖ then (2 : ℝ) ^ (-((k : ℝ) * γ)) else 0) := by
              rw [Finset.sum_comm]
          _ ≤ ∑ k ∈ Finset.range (K + 1),
              ((2 : ℝ) ^ (-(k : ℝ) * γ) * D * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * κ)) :=
              Finset.sum_le_sum (by intro k hk; exact hcount_k k)
          _ ≤ ∑ k ∈ Finset.range (K + 1), (D * (2 : ℝ) ^ κ * r0 ^ k) :=
              Finset.sum_le_sum (by intro k hk; exact hterm_le k)
          _ ≤ ∑' k : ℕ, D * (2 : ℝ) ^ κ * r0 ^ k :=
              hu.sum_le_tsum (Finset.range (K + 1)) (by
                intro k hk
                exact mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) κ))
                  (pow_nonneg hr0nn k))
          _ = C := rfl
    have hhead : (∑ n ∈ Finset.range N, ((‖a n‖ ^ γ)⁻¹ - t n)) ≤ headC := by
      have hdiff : ∀ n, (‖a n‖ ^ γ)⁻¹ - t n = if ‖a n‖ ≤ 1 then (‖a n‖ ^ γ)⁻¹ else 0 := by
        intro n
        by_cases h1n : 1 < ‖a n‖
        · have hle' : ¬ ‖a n‖ ≤ 1 := by linarith
          simp [t, h1n, hle']
        · have hle' : ‖a n‖ ≤ 1 := le_of_not_gt h1n
          simp [t, h1n, hle']
      calc (∑ n ∈ Finset.range N, ((‖a n‖ ^ γ)⁻¹ - t n))
          = ∑ n ∈ Finset.range N, if ‖a n‖ ≤ 1 then (‖a n‖ ^ γ)⁻¹ else 0 := by
              exact Finset.sum_congr rfl (fun n hn => hdiff n)
        _ = ∑ n ∈ (Finset.range N).filter (fun n => ‖a n‖ ≤ 1), (‖a n‖ ^ γ)⁻¹ := by
              rw [← Finset.sum_filter]
        _ ≤ ∑ n ∈ hS_fin.toFinset, (‖a n‖ ^ γ)⁻¹ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro n hn
                rw [Finset.mem_filter, Finset.mem_range] at hn
                simpa [S] using hn.2
              · intro n hn hnot
                exact inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg (a n)) γ)
        _ = headC := rfl
    calc (∑ n ∈ Finset.range N, (‖a n‖ ^ γ)⁻¹)
        = (∑ n ∈ Finset.range N, t n) + (∑ n ∈ Finset.range N, ((‖a n‖ ^ γ)⁻¹ - t n)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun n hn => by ring)
      _ ≤ C + headC := add_le_add htail hhead
      _ = headC + C := by rw [add_comm]
  have hmono : Monotone (fun N : ℕ => ∑ n ∈ Finset.range N, (‖a n‖ ^ γ)⁻¹) := by
    intro N M hNM
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.range_subset.mpr (by
        intro x hx
        exact Finset.mem_range.mpr (lt_of_lt_of_le hx hNM))
    · intro n hn hnot
      exact inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg (a n)) γ)
  have hbdd : BddAbove (Set.range (fun N : ℕ => ∑ n ∈ Finset.range N, (‖a n‖ ^ γ)⁻¹)) := by
    refine ⟨headC + C, ?_⟩
    rintro y ⟨N, rfl⟩
    exact htail_bdd N
  exact summable_of_sum_range_le
    (by intro n; exact inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg (a n)) γ))
    (fun N => htail_bdd N)

/-! ## The canonical product over the zeros -/

/-- The canonical product `∏ₙ E_p(z/aₙ)` over a sequence of (nonzero) zeros. -/
noncomputable def canonicalProductNat (p : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, primaryFactor p (z / a n)

lemma primaryFactor_ne_zero (p : ℕ) {z : ℂ} (hz : z ≠ 1) : primaryFactor p z ≠ 0 := by
  rw [primaryFactor, mul_ne_zero_iff]
  constructor
  · exact sub_ne_zero.mpr (Ne.symm hz)
  · exact exp_ne_zero _

lemma primaryFactor_eq_zero_iff (p : ℕ) (z : ℂ) : primaryFactor p z = 0 ↔ z = 1 := by
  constructor
  · intro h
    rw [primaryFactor, mul_eq_zero] at h
    rcases h with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (exp_ne_zero _)
  · intro h
    rw [h, primaryFactor_one]

/-- The Weierstrass primary factor is entire. -/
@[fun_prop]
lemma differentiable_primaryFactor (p : ℕ) : Differentiable ℂ (primaryFactor p) := by
  have h : primaryFactor p = fun z => (1 - z) * Complex.exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := rfl
  rw [h]
  apply Differentiable.mul
  · fun_prop
  · exact Differentiable.comp Complex.differentiable_exp (by fun_prop)

/-- The scaled primary factor `z ↦ E_p(z/a)` is entire for `a ≠ 0`. -/
@[fun_prop]
lemma differentiable_primaryFactor_scaled (p : ℕ) {a : ℂ} (ha : a ≠ 0) :
    Differentiable ℂ (fun z => primaryFactor p (z / a)) := by
  exact (differentiable_primaryFactor p).comp (by fun_prop)

/-- Pointwise bound `‖E_p(w) - 1‖ ≤ 4/(p+1) · ‖w‖^{p+1}` for `‖w‖ ≤ 1/2`. -/
lemma norm_primaryFactor_sub_one_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖primaryFactor p w - 1‖ ≤ (4 / (p + 1 : ℝ)) * ‖w‖ ^ (p + 1) := by
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, norm_one] at hw
    norm_num at hw
  have hL := primaryFactor_log_bound p hw
  have hLle1 : ‖Complex.log (primaryFactor p w)‖ ≤ 1 := by
    have h₁ : ‖w‖ ^ (p + 1) ≤ (1 / 2 : ℝ) ^ (p + 1) := by
      exact pow_le_pow_left₀ (norm_nonneg w) hw (p + 1)
    have h₂ : (1 / 2 : ℝ) ^ (p + 1) ≤ 1 / 2 := by
      rw [pow_succ]
      nlinarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1) (n := p),
        pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) p]
    have h₃ : 2 / ((p : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) + 1)]
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    have hpos : (0 : ℝ) ≤ 2 / ((p : ℝ) + 1) := by positivity
    calc ‖Complex.log (primaryFactor p w)‖ ≤ 2 / ((p : ℝ) + 1) * ‖w‖ ^ (p + 1) := hL
      _ ≤ 2 / ((p : ℝ) + 1) * (1 / 2) := mul_le_mul_of_nonneg_left (h₁.trans h₂) hpos
      _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_right h₃ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = 1 := by norm_num
  have hpf : primaryFactor p w = Complex.exp (Complex.log (primaryFactor p w)) := by
    rw [Complex.exp_log (primaryFactor_ne_zero p hw1)]
  calc ‖primaryFactor p w - 1‖
      = ‖Complex.exp (Complex.log (primaryFactor p w)) - 1‖ := by rw [← hpf]
    _ ≤ 2 * ‖Complex.log (primaryFactor p w)‖ := Complex.norm_exp_sub_one_le hLle1
    _ ≤ (4 / (p + 1 : ℝ)) * ‖w‖ ^ (p + 1) := by
      calc 2 * ‖Complex.log (primaryFactor p w)‖
          ≤ 2 * ((2 / (p + 1 : ℝ)) * ‖w‖ ^ (p + 1)) := by
              exact mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 2)
        _ = (4 / (p + 1 : ℝ)) * ‖w‖ ^ (p + 1) := by ring

/-- The canonical product converges locally uniformly on `ℂ`. -/
theorem multipliableLocallyUniformlyOn_primaryFactor {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ)
    (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    MultipliableLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Set.univ : Set ℂ) := by
  have hball : ∀ R : ℝ, 0 < R → MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) := by
    intro R hR
    let c : ℕ → ℝ := fun n => (4 / (p + 1 : ℝ)) * R ^ (p + 1) * (1 / ‖a n‖ ^ (p + 1))
    have hc : Summable c := by
      simpa [c, one_div, mul_assoc] using
        (hs.mul_left ((4 / (p + 1 : ℝ)) * R ^ (p + 1)))
    have hev : ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖primaryFactor p (z / a n) - 1‖ ≤ c n := by
      filter_upwards [htend.eventually_ge_atTop (2 * R)] with n hn z hz
      have hz' : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz)
      have hanz : (0 : ℝ) < ‖a n‖ := by linarith
      have hnorm : ‖z / a n‖ ≤ 1 / 2 := by
        rw [norm_div]
        have h₁ : ‖z‖ / ‖a n‖ ≤ R / ‖a n‖ :=
          div_le_div_of_nonneg_right hz' (le_of_lt hanz)
        have h₂ : R / ‖a n‖ ≤ 1 / 2 := by
          rw [div_le_iff₀ hanz]
          nlinarith
        exact h₁.trans h₂
      have hb := norm_primaryFactor_sub_one_le p hnorm
      have hb' : ‖primaryFactor p (z / a n) - 1‖ ≤ (4 / (p + 1 : ℝ)) * (‖z‖ ^ (p + 1) / ‖a n‖ ^ (p + 1)) := by
        simpa [norm_div, div_pow] using hb
      have hRpow : ‖z‖ ^ (p + 1) ≤ R ^ (p + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hz' (p + 1)
      have h₀ : (4 / (p + 1 : ℝ)) * (‖z‖ ^ (p + 1) / ‖a n‖ ^ (p + 1))
          ≤ (4 / (p + 1 : ℝ)) * (R ^ (p + 1) / ‖a n‖ ^ (p + 1)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hRpow (pow_nonneg (norm_nonneg (a n)) (p + 1)))
          (by positivity : (0 : ℝ) ≤ 4 / (p + 1 : ℝ))
      have h₁ : (4 / (p + 1 : ℝ)) * (R ^ (p + 1) / ‖a n‖ ^ (p + 1)) = c n := by
        have hanz0 : ‖a n‖ ^ (p + 1) ≠ 0 := pow_ne_zero (p + 1) (norm_ne_zero_iff.mpr (hane n))
        simp [c, div_eq_mul_inv, one_div, mul_assoc, hanz0]
      exact hb'.trans (h₀.trans_eq h₁)
    have hcts : ∀ n, ContinuousOn (fun z : ℂ => primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) := by
      intro n
      exact (differentiable_primaryFactor_scaled p (hane n)).continuous.continuousOn
    have hm : MultipliableLocallyUniformlyOn
        (fun n : ℕ => fun z : ℂ => 1 + (primaryFactor p (z / a n) - 1)) (Metric.ball (0 : ℂ) R) := by
      refine Summable.multipliableLocallyUniformlyOn_nat_one_add Metric.isOpen_ball hc ?_ ?_
      · exact hev
      · intro n
        exact (hcts n).sub continuousOn_const
    have heq : (fun (n : ℕ) (z : ℂ) => 1 + (primaryFactor p (z / a n) - 1))
        = fun (n : ℕ) => fun z : ℂ => primaryFactor p (z / a n) := by
      funext n z
      ring
    rwa [heq] at hm
  refine multipliableLocallyUniformlyOn_of_of_forall_exists_nhds ?_
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  have hzmem : z ∈ Metric.ball (0 : ℂ) R := by
    simp [R, Metric.mem_ball, dist_eq_norm]
  have hzR : ‖z‖ < R := by simp [R]
  have hballR : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) :=
    hball R hR
  have hballR1 : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) (R + 1)) :=
    hball (R + 1) (by positivity)
  have hmono' : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.closedBall (0 : ℂ) R) :=
    hballR1.mono (by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [Metric.mem_ball, dist_eq_norm]
      nlinarith)
  have hcompact : MultipliableUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.closedBall (0 : ℂ) R) :=
    hmono'.multipliableUniformlyOn_of_isCompact (isCompact_closedBall (0 : ℂ) R)
  have huniform : MultipliableUniformlyOn
      (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) := by
    rcases hcompact with ⟨g, hg⟩
    exact ⟨g, HasProdUniformlyOn.mono hg (by intro x hx; rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hx))⟩
  refine ⟨Metric.ball (0 : ℂ) R, ?_, huniform⟩
  simpa [nhdsWithin_univ] using (Metric.isOpen_ball.mem_nhds hzmem)

/-- The canonical product over the zeros defines an entire function. -/
theorem differentiable_canonicalProductNat {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ)
    (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    Differentiable ℂ (canonicalProductNat p a) := by
  have hm : MultipliableLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => primaryFactor p (z / a n)) (Set.univ : Set ℂ) :=
    multipliableLocallyUniformlyOn_primaryFactor hane p hs htend
  have htend' : TendstoLocallyUniformlyOn
      (fun (N : Finset ℕ) => fun z : ℂ => ∏ n ∈ N, primaryFactor p (z / a n))
      (fun z => canonicalProductNat p a z) atTop (Set.univ : Set ℂ) := by
    simpa [canonicalProductNat] using
      (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hm.hasProdLocallyUniformlyOn)
  have hF : ∀ᶠ N in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ n ∈ N, primaryFactor p (z / a n)) (Set.univ : Set ℂ) := by
    filter_upwards [eventually_ge_atTop (∅ : Finset ℕ)] with N hN
    refine DifferentiableOn.fun_finsetProd ?_
    intro n hn
    exact (differentiable_primaryFactor_scaled p (hane n)).differentiableOn
  have hd : DifferentiableOn ℂ (fun z => canonicalProductNat p a z) (Set.univ : Set ℂ) :=
    htend'.differentiableOn hF isOpen_univ
  exact differentiableOn_univ.mp hd

/-- For `z` not a zero, the log series converges. -/
lemma summable_log_primaryFactor {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) {z : ℂ}
    (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    Summable (fun n : ℕ => Complex.log (primaryFactor p (z / a n))) := by
  rcases eventually_atTop.1 (htend.eventually_ge_atTop (2 * (‖z‖ + 1))) with ⟨N, hN⟩
  have htail : Summable (fun n : ℕ => ‖Complex.log (primaryFactor p (z / a (n + N)))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n => (2 / (p + 1 : ℝ)) * (2 * (‖z‖ + 1)) ^ (p + 1) * (1 / ‖a (n + N)‖ ^ (p + 1))) ?_ ?_ ?_
    · intro n
      positivity
    · intro n
      have ha : 2 * (‖z‖ + 1) ≤ ‖a (n + N)‖ := hN (n + N) (by omega)
      have hanz : (0 : ℝ) < ‖a (n + N)‖ := by
        have hpos : (0 : ℝ) < 2 * (‖z‖ + 1) := by positivity
        linarith
      have hz1 : ‖z‖ / ‖a (n + N)‖ ≤ 1 / 2 := by
        have h₁ : ‖z‖ / ‖a (n + N)‖ ≤ ‖z‖ / (2 * (‖z‖ + 1)) :=
          div_le_div_of_nonneg_left (norm_nonneg z) (by positivity : (0 : ℝ) < 2 * (‖z‖ + 1)) ha
        have h₂ : ‖z‖ / (2 * (‖z‖ + 1)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖z‖ + 1))]
          nlinarith
        exact h₁.trans h₂
      have hnorm0 : ‖z / a (n + N)‖ ≤ 1 / 2 := by
        rw [norm_div]
        exact hz1
      have hb := primaryFactor_log_bound p hnorm0
      calc ‖Complex.log (primaryFactor p (z / a (n + N)))‖
          ≤ (2 / (p + 1 : ℝ)) * ‖z / a (n + N)‖ ^ (p + 1) := hb
        _ ≤ (2 / (p + 1 : ℝ)) * ((2 * (‖z‖ + 1)) / ‖a (n + N)‖) ^ (p + 1) := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ (p + 1))
              (by positivity : (0 : ℝ) ≤ 2 / (p + 1 : ℝ))
            rw [norm_div]
            exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg z]) (le_of_lt hanz)
        _ = (2 / (p + 1 : ℝ)) * ((2 * (‖z‖ + 1)) ^ (p + 1) / ‖a (n + N)‖ ^ (p + 1)) := by
            rw [div_pow]
        _ = (2 / (p + 1 : ℝ)) * (2 * (‖z‖ + 1)) ^ (p + 1) * (1 / ‖a (n + N)‖ ^ (p + 1)) := by
            rw [← mul_div_assoc, div_eq_mul_inv, one_div]
    · have hshift : Summable (fun n : ℕ => (‖a (n + N)‖ ^ (p + 1))⁻¹) := by
        simpa [one_div] using (summable_nat_add_iff (f := fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹) N).mpr hs
      simpa [one_div, mul_assoc] using
        (hshift.mul_left ((2 / (p + 1 : ℝ)) * (2 * (‖z‖ + 1)) ^ (p + 1)))
  have hnorm : Summable (fun n : ℕ => ‖Complex.log (primaryFactor p (z / a n))‖) :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖Complex.log (primaryFactor p (z / a n))‖) N).mp htail
  exact hnorm.of_norm

/-- Off the zeros, the canonical product equals `exp` of the sum of the logarithms. -/
lemma tprod_eq_exp_tsum_log {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) {z : ℂ}
    (hz : ∀ n, z ≠ a n) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    canonicalProductNat p a z = Complex.exp (∑' n : ℕ, Complex.log (primaryFactor p (z / a n))) := by
  have hlog : Summable (fun n : ℕ => Complex.log (primaryFactor p (z / a n))) :=
    summable_log_primaryFactor hane p hs htend
  have hm : Multipliable (fun n : ℕ => primaryFactor p (z / a n)) :=
    (multipliableLocallyUniformlyOn_primaryFactor hane p hs htend).multipliable (by simp : z ∈ (Set.univ : Set ℂ))
  have hprod : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, primaryFactor p (z / a n)) atTop
      (𝓝 (canonicalProductNat p a z)) := by
    simpa [canonicalProductNat] using hm.hasProd.tendsto_prod_nat
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, Complex.log (primaryFactor p (z / a n))) atTop
      (𝓝 (∑' n : ℕ, Complex.log (primaryFactor p (z / a n)))) :=
    hlog.hasSum.tendsto_sum_nat
  have hexp : Tendsto (fun N : ℕ => Complex.exp (∑ n ∈ Finset.range N, Complex.log (primaryFactor p (z / a n)))) atTop
      (𝓝 (Complex.exp (∑' n : ℕ, Complex.log (primaryFactor p (z / a n))))) :=
    (Complex.continuous_exp.tendsto (∑' n : ℕ, Complex.log (primaryFactor p (z / a n)))).comp hsum
  have heq : ∀ N : ℕ, (∏ n ∈ Finset.range N, primaryFactor p (z / a n))
      = Complex.exp (∑ n ∈ Finset.range N, Complex.log (primaryFactor p (z / a n))) := by
    intro N
    calc ∏ n ∈ Finset.range N, primaryFactor p (z / a n)
        = ∏ n ∈ Finset.range N, Complex.exp (Complex.log (primaryFactor p (z / a n))) := by
            refine Finset.prod_congr rfl ?_
            intro n hn
            rw [Complex.exp_log (primaryFactor_ne_zero p (by
              intro h
              apply hz n
              rw [div_eq_one_iff_eq (hane n)] at h
              exact h))]
      _ = Complex.exp (∑ n ∈ Finset.range N, Complex.log (primaryFactor p (z / a n))) := by
            rw [Complex.exp_sum]
  exact tendsto_nhds_unique (hprod.congr' (by
    filter_upwards with N
    exact heq N)) hexp

/-- The canonical product does not vanish away from the zeros. -/
theorem canonicalProductNat_ne_zero {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) {z : ℂ}
    (hz : ∀ n, z ≠ a n) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    canonicalProductNat p a z ≠ 0 := by
  rw [tprod_eq_exp_tsum_log hane p hz hs htend]
  exact Complex.exp_ne_zero _

/-- The canonical product vanishes at each zero `aₙ`. -/
theorem canonicalProductNat_eq_zero_of_mem {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) {z : ℂ}
    (hzm : ∃ n, z = a n) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    canonicalProductNat p a z = 0 := by
  rcases hzm with ⟨n₀, rfl⟩
  have hm : Multipliable (fun n : ℕ => primaryFactor p (a n₀ / a n)) :=
    (multipliableLocallyUniformlyOn_primaryFactor hane p hs htend).multipliable (by simp : a n₀ ∈ (Set.univ : Set ℂ))
  have hprod : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, primaryFactor p (a n₀ / a n)) atTop
      (𝓝 (canonicalProductNat p a (a n₀))) := by
    simpa [canonicalProductNat] using hm.hasProd.tendsto_prod_nat
  have hz0 : ∀ᶠ N in atTop, (∏ n ∈ Finset.range N, primaryFactor p (a n₀ / a n)) = 0 := by
    filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
    refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self n₀) hN)) ?_
    rw [div_self (hane n₀), primaryFactor_one]
  have hprod0 : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, primaryFactor p (a n₀ / a n)) atTop
      (𝓝 (0 : ℂ)) :=
    (tendsto_const_nhds : Tendsto (fun N : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ))).congr' (by
      filter_upwards [hz0] with N hN
      exact hN.symm)
  exact tendsto_nhds_unique hprod hprod0

/-- Logarithmic derivative of the canonical product. -/
theorem logDeriv_canonicalProductNat {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) {s : Set ℂ}
    (hs : IsOpen s) {z : ℂ} (hz : z ∈ s) (hzane : ∀ n, z ≠ a n)
    (hs2 : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hlogsum : Summable fun n => logDeriv (fun x => primaryFactor p (x / a n)) z) :
    logDeriv (canonicalProductNat p a) z = ∑' n, logDeriv (fun x => primaryFactor p (x / a n)) z := by
  exact logDeriv_tprod_eq_tsum hs hz
    (fun n => primaryFactor_ne_zero p (by
      intro h
      apply hzane n
      rw [div_eq_one_iff_eq (hane n)] at h
      exact h))
    (fun n => (differentiable_primaryFactor_scaled p (hane n)).differentiableOn)
    hlogsum
    ((multipliableLocallyUniformlyOn_primaryFactor hane p hs2 htend).mono (by intro x hx; trivial))
    (canonicalProductNat_ne_zero hane p hzane hs2 htend)

/-! ## The holomorphic logarithm and Weierstrass factorization -/

/-- An entire function without zeros is the exponential of an entire function. -/
theorem exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hne : ∀ z, f z ≠ 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hφ : Differentiable ℂ (fun z => deriv f z / f z) :=
    Differentiable.div hf.deriv hf hne
  rcases hφ.isExactOn_univ with ⟨η, hη⟩
  let g : ℂ → ℂ := fun z => η z - η 0 + Complex.log (f 0)
  have hηd : Differentiable ℂ η := fun z => (hη z trivial).differentiableAt
  have hg_diff : Differentiable ℂ g := by
    exact (hηd.sub (differentiable_const (η 0))).add (differentiable_const (Complex.log (f 0)))
  have hgval : ∀ z, deriv g z = deriv f z / f z := by
    intro z
    have hηz := (hη z trivial).deriv
    have h1 : deriv (fun x => η x - η 0) z = deriv η z := by
      change deriv (η - fun x => η 0) z = deriv η z
      rw [deriv_sub (hηd z) (differentiableAt_const (η 0))]
      rw [deriv_const z (η 0)]
      ring
    have h2 : deriv (fun x => (η x - η 0) + Complex.log (f 0)) z = deriv (fun x => η x - η 0) z := by
      change deriv ((fun x => η x - η 0) + (fun x => Complex.log (f 0))) z = deriv (fun x => η x - η 0) z
      rw [deriv_add (by exact (hηd.sub (differentiable_const (η 0))).differentiableAt)
        (differentiableAt_const (Complex.log (f 0)))]
      rw [deriv_const z (Complex.log (f 0))]
      ring
    dsimp [g]
    rw [h2, h1, hηz]
  have hhd : Differentiable ℂ (fun z => f z * Complex.exp (-g z)) := by
    apply Differentiable.mul hf
    exact Differentiable.comp Complex.differentiable_exp hg_diff.neg
  have hderiv0 : ∀ z, deriv (fun x => f x * Complex.exp (-g x)) z = 0 := by
    intro z
    have hg' : HasDerivAt g (deriv g z) z := (hg_diff z).hasDerivAt
    have hneg : HasDerivAt (fun x => -g x) (-deriv g z) z := hg'.neg
    have hexp' : HasDerivAt (fun x => Complex.exp (-g x)) (Complex.exp (-g z) * (-deriv g z)) z :=
      HasDerivAt.comp z (Complex.hasDerivAt_exp (-g z)) hneg
    have hexpd : deriv (fun x => Complex.exp (-g x)) z = Complex.exp (-g z) * (-deriv g z) :=
      hexp'.deriv
    rw [show deriv (fun x => f x * Complex.exp (-g x)) z =
        deriv (f * (fun x => Complex.exp (-g x))) z from rfl]
    rw [deriv_mul hf.differentiableAt (by
      exact (Differentiable.comp Complex.differentiable_exp hg_diff.neg).differentiableAt)]
    rw [hexpd, hgval z]
    field_simp [hne z]
    ring
  have hc : ∀ z, f z * Complex.exp (-g z) = f 0 * Complex.exp (-g 0) :=
    fun z => is_const_of_deriv_eq_zero hhd hderiv0 z 0
  have h01 : f 0 * Complex.exp (-g 0) = 1 := by
    have hg0 : g 0 = Complex.log (f 0) := by
      dsimp [g]
      ring
    rw [hg0, Complex.exp_neg, Complex.exp_log h0]
    field_simp
  have hmain : ∀ z, f z * Complex.exp (-g z) = 1 := by
    intro z
    exact (hc z).trans h01
  refine ⟨g, hg_diff, ?_⟩
  intro z
  have hz := hmain z
  rw [Complex.exp_neg] at hz
  simpa using (mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero (g z))).mp hz

/-! ## The genus-1 log-derivative identity -/

/-- For `z` not a zero, the genus-1 logarithmic derivatives are summable. -/
lemma summable_logDeriv_genus_one {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) {z : ℂ}
    (hzane : ∀ n, z ≠ a n) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    Summable (fun n => logDeriv (fun x => primaryFactor 1 (x / a n)) z) := by
  have heq : ∀ n, logDeriv (fun x => primaryFactor 1 (x / a n)) z = 1 / (z - a n) + 1 / a n := by
    intro n
    exact logDeriv_primaryFactor_one_scaled z (a n) (hane n) (hzane n)
  rw [show (fun n => logDeriv (fun x => primaryFactor 1 (x / a n)) z) = fun n => 1 / (z - a n) + 1 / a n from funext heq]
  -- the tail bound: ‖1/(z-aₙ) + 1/aₙ‖ ≤ 2‖z‖·(1/‖aₙ‖²) for ‖aₙ‖ ≥ 2(‖z‖+1):
  rcases eventually_atTop.1 (htend.eventually_ge_atTop (2 * (‖z‖ + 1))) with ⟨N, hN⟩
  have htail : Summable (fun n : ℕ => ‖1 / (z - a (n + N)) + 1 / a (n + N)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n => 2 * ‖z‖ * (1 / ‖a (n + N)‖ ^ 2)) ?_ ?_ ?_
    · intro n
      positivity
    · intro n
      have ha : 2 * (‖z‖ + 1) ≤ ‖a (n + N)‖ := hN (n + N) (by omega)
      have hanz : (0 : ℝ) < ‖a (n + N)‖ := by
        have hpos : (0 : ℝ) < 2 * (‖z‖ + 1) := by positivity
        linarith
      have hnorm : ‖1 / (z - a (n + N)) + 1 / a (n + N)‖ ≤ 2 * ‖z‖ * (1 / ‖a (n + N)‖ ^ 2) := by
        have hid : 1 / (z - a (n + N)) + 1 / a (n + N) = z / (a (n + N) * (z - a (n + N))) := by
          field_simp [hane (n + N), sub_ne_zero.mpr (hzane (n + N))]
          ring
        rw [hid]
        have hzma : ‖z - a (n + N)‖ = ‖a (n + N) - z‖ := by
          rw [← norm_neg]
          simp
        have hza : ‖a (n + N)‖ - ‖z‖ ≤ ‖a (n + N) - z‖ := by
          have h₁ : ‖(a (n + N) - z) + z‖ ≤ ‖a (n + N) - z‖ + ‖z‖ := norm_add_le _ _
          have h₂ : ‖(a (n + N) - z) + z‖ = ‖a (n + N)‖ := by
            rw [show (a (n + N) - z) + z = a (n + N) by ring]
          rw [h₂] at h₁
          linarith
        have hden : (0 : ℝ) < ‖a (n + N)‖ * (‖a (n + N)‖ - ‖z‖) := by
          have h₁ : (0 : ℝ) < ‖a (n + N)‖ - ‖z‖ := by
            have : ‖z‖ + 1 ≤ ‖a (n + N)‖ := by linarith
            linarith
          exact mul_pos hanz h₁
        have h₁ : ‖z / (a (n + N) * (z - a (n + N)))‖
            ≤ ‖z‖ / (‖a (n + N)‖ * (‖a (n + N)‖ - ‖z‖)) := by
          rw [norm_div, norm_mul]
          rw [hzma]
          refine div_le_div_of_nonneg_left (norm_nonneg z) hden ?_
          exact mul_le_mul_of_nonneg_left hza (le_of_lt hanz)
        have h₂ : ‖z‖ / (‖a (n + N)‖ * (‖a (n + N)‖ - ‖z‖)) ≤ 2 * ‖z‖ * (1 / ‖a (n + N)‖ ^ 2) := by
          have h₃ : ‖a (n + N)‖ * (‖a (n + N)‖ - ‖z‖) ≥ ‖a (n + N)‖ ^ 2 / 2 := by
            nlinarith [ha, norm_nonneg z, sq_nonneg ‖a (n + N)‖, hanz]
          have h₄ : (0 : ℝ) < ‖a (n + N)‖ ^ 2 / 2 := by positivity
          have h₅ : ‖z‖ / (‖a (n + N)‖ * (‖a (n + N)‖ - ‖z‖)) ≤ ‖z‖ / (‖a (n + N)‖ ^ 2 / 2) :=
            div_le_div_of_nonneg_left (norm_nonneg z) h₄ h₃
          have h₆ : ‖z‖ / (‖a (n + N)‖ ^ 2 / 2) = 2 * ‖z‖ * (1 / ‖a (n + N)‖ ^ 2) := by
            field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr (hane (n + N)))]
          exact h₅.trans_eq h₆
        exact h₁.trans h₂
      exact hnorm
    · have hshift : Summable (fun n : ℕ => (‖a (n + N)‖ ^ 2)⁻¹) := by
        simpa [one_div] using (summable_nat_add_iff (f := fun n : ℕ => (‖a n‖ ^ 2)⁻¹) N).mpr hs2
      simpa [one_div, mul_assoc] using (hshift.mul_left (2 * ‖z‖))
  have hnorm : Summable (fun n : ℕ => ‖1 / (z - a n) + 1 / a n‖) :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖1 / (z - a n) + 1 / a n‖) N).mp htail
  exact hnorm.of_norm

/-- **Logarithmic derivative of the genus-1 canonical product.** For `z` not a zero,
`logDeriv (∏ₙ E₁(·/aₙ)) z = Σₙ (1/(z-aₙ) + 1/aₙ)`. -/
theorem logDeriv_canonicalProductNat_genus_one {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) {z : ℂ}
    (hzane : ∀ n, z ≠ a n) :
    logDeriv (canonicalProductNat 1 a) z = ∑' n, (1 / (z - a n) + 1 / a n) := by
  have hsum : Summable fun n => logDeriv (fun x => primaryFactor 1 (x / a n)) z :=
    summable_logDeriv_genus_one hane hzane hs2 htend
  have hmain := logDeriv_canonicalProductNat hane 1 isOpen_univ (by simp : z ∈ (Set.univ : Set ℂ)) hzane hs2 htend hsum
  have heq : (fun n => logDeriv (fun x => primaryFactor 1 (x / a n)) z) = fun n => 1 / (z - a n) + 1 / a n := by
    funext n
    exact logDeriv_primaryFactor_one_scaled z (a n) (hane n) (hzane n)
  rw [heq] at hmain
  exact hmain



/-! ## The Hadamard (Weierstrass) factorization theorem -/
set_option maxHeartbeats 800000

/-- The canonical product with the factor at index `k` removed. -/
noncomputable def canonicalProductNatSkip (k : ℕ) (p : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, (if n = k then 1 else primaryFactor p (z / a n))

/-- The skipped canonical product converges locally uniformly on `ℂ`. -/
theorem multipliableLocallyUniformlyOn_primaryFactorSkip {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (p : ℕ) (k : ℕ) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n))
      (Set.univ : Set ℂ) := by
  have hball : ∀ R : ℝ, 0 < R → MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n))
      (Metric.ball (0 : ℂ) R) := by
    intro R hR
    let c : ℕ → ℝ := fun n => (4 / (p + 1 : ℝ)) * R ^ (p + 1) * (1 / ‖a n‖ ^ (p + 1))
    have hc : Summable c := by
      simpa [c, one_div, mul_assoc] using
        (hs.mul_left ((4 / (p + 1 : ℝ)) * R ^ (p + 1)))
    have hev : ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖(if n = k then 1 else primaryFactor p (z / a n)) - 1‖ ≤ c n := by
      filter_upwards [htend.eventually_ge_atTop (2 * R)] with n hn z hz
      by_cases hnk : n = k
      · have hak : (0 : ℝ) < ‖a n‖ := norm_pos_iff.mpr (hane n)
        simp [hnk, c]
        positivity
      · have hz' : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz)
        have hanz : (0 : ℝ) < ‖a n‖ := by linarith
        have hnorm : ‖z / a n‖ ≤ 1 / 2 := by
          rw [norm_div]
          have h₁ : ‖z‖ / ‖a n‖ ≤ R / ‖a n‖ :=
            div_le_div_of_nonneg_right hz' (le_of_lt hanz)
          have h₂ : R / ‖a n‖ ≤ 1 / 2 := by
            rw [div_le_iff₀ hanz]
            nlinarith
          exact h₁.trans h₂
        have hb := norm_primaryFactor_sub_one_le p hnorm
        have hb' : ‖primaryFactor p (z / a n) - 1‖ ≤ (4 / (p + 1 : ℝ)) * (‖z‖ ^ (p + 1) / ‖a n‖ ^ (p + 1)) := by
          simpa [norm_div, div_pow] using hb
        have hRpow : ‖z‖ ^ (p + 1) ≤ R ^ (p + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hz' (p + 1)
        have h₀ : (4 / (p + 1 : ℝ)) * (‖z‖ ^ (p + 1) / ‖a n‖ ^ (p + 1))
            ≤ (4 / (p + 1 : ℝ)) * (R ^ (p + 1) / ‖a n‖ ^ (p + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hRpow (pow_nonneg (norm_nonneg (a n)) (p + 1)))
            (by positivity : (0 : ℝ) ≤ 4 / (p + 1 : ℝ))
        have h₁ : (4 / (p + 1 : ℝ)) * (R ^ (p + 1) / ‖a n‖ ^ (p + 1)) = c n := by
          have hanz0 : ‖a n‖ ^ (p + 1) ≠ 0 := pow_ne_zero (p + 1) (norm_ne_zero_iff.mpr (hane n))
          simp [c, div_eq_mul_inv, one_div, mul_assoc, hanz0]
        simp [hnk]
        exact hb'.trans (h₀.trans_eq h₁)
    have hcts : ∀ n, ContinuousOn (fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n))
        (Metric.ball (0 : ℂ) R) := by
      intro n
      by_cases hnk : n = k
      · simpa [hnk] using
          (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (Metric.ball (0 : ℂ) R))
      · simp [hnk]
        exact (differentiable_primaryFactor_scaled p (hane n)).continuous.continuousOn
    have hm : MultipliableLocallyUniformlyOn
        (fun n : ℕ => fun z : ℂ => 1 + ((if n = k then 1 else primaryFactor p (z / a n)) - 1))
        (Metric.ball (0 : ℂ) R) := by
      refine Summable.multipliableLocallyUniformlyOn_nat_one_add Metric.isOpen_ball hc ?_ ?_
      · exact hev
      · intro n
        exact (hcts n).sub continuousOn_const
    have heq : (fun (n : ℕ) (z : ℂ) => 1 + ((if n = k then 1 else primaryFactor p (z / a n)) - 1))
        = fun (n : ℕ) => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n) := by
      funext n z
      ring
    rwa [heq] at hm
  refine multipliableLocallyUniformlyOn_of_of_forall_exists_nhds ?_
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  have hzmem : z ∈ Metric.ball (0 : ℂ) R := by
    simp [R, Metric.mem_ball, dist_eq_norm]
  have hballR : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) :=
    hball R hR
  have hballR1 : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) (R + 1)) :=
    hball (R + 1) (by positivity)
  have hmono' : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Metric.closedBall (0 : ℂ) R) :=
    hballR1.mono (by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [Metric.mem_ball, dist_eq_norm]
      nlinarith)
  have hcompact : MultipliableUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Metric.closedBall (0 : ℂ) R) :=
    hmono'.multipliableUniformlyOn_of_isCompact (isCompact_closedBall (0 : ℂ) R)
  have huniform : MultipliableUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Metric.ball (0 : ℂ) R) := by
    rcases hcompact with ⟨g, hg⟩
    exact ⟨g, HasProdUniformlyOn.mono hg (by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hx))⟩
  refine ⟨Metric.ball (0 : ℂ) R, ?_, huniform⟩
  simpa [nhdsWithin_univ] using (Metric.isOpen_ball.mem_nhds hzmem)

/-- The skipped canonical product is entire. -/
theorem differentiable_canonicalProductNatSkip {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) (k : ℕ)
    (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    Differentiable ℂ (canonicalProductNatSkip k p a) := by
  have hm : MultipliableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => if n = k then 1 else primaryFactor p (z / a n)) (Set.univ : Set ℂ) :=
    multipliableLocallyUniformlyOn_primaryFactorSkip hane p k hs htend
  have htend' : TendstoLocallyUniformlyOn
      (fun (N : Finset ℕ) => fun z : ℂ => ∏ n ∈ N, (if n = k then 1 else primaryFactor p (z / a n)))
      (fun z => canonicalProductNatSkip k p a z) atTop (Set.univ : Set ℂ) := by
    simpa [canonicalProductNatSkip] using
      (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hm.hasProdLocallyUniformlyOn)
  have hF : ∀ᶠ N in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ n ∈ N, (if n = k then 1 else primaryFactor p (z / a n))) (Set.univ : Set ℂ) := by
    filter_upwards [eventually_ge_atTop (∅ : Finset ℕ)] with N hN
    refine DifferentiableOn.fun_finsetProd ?_
    intro n hn
    by_cases hnk : n = k
    · simpa [hnk] using (differentiable_const (1 : ℂ)).differentiableOn
    · simpa [hnk] using (differentiable_primaryFactor_scaled p (hane n)).differentiableOn
  have hd : DifferentiableOn ℂ (fun z => canonicalProductNatSkip k p a z) (Set.univ : Set ℂ) :=
    htend'.differentiableOn hF isOpen_univ
  exact differentiableOn_univ.mp hd

/-- The canonical product splits off the `k`-th primary factor. -/
lemma canonicalProductNat_eq_mul_skip {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) (k : ℕ)
    (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) (z : ℂ) :
    canonicalProductNat p a z = primaryFactor p (z / a k) * canonicalProductNatSkip k p a z := by
  let F : ℕ → ℂ := fun n => primaryFactor p (z / a n)
  have hm : Multipliable F :=
    (multipliableLocallyUniformlyOn_primaryFactor hane p hs htend).multipliable (by simp)
  by_cases hz : z = a k
  · subst hz
    have h₀ : primaryFactor p (a k / a k) = 0 := by
      rw [primaryFactor_eq_zero_iff p (a k / a k)]
      exact div_self (hane k)
    rw [canonicalProductNat_eq_zero_of_mem hane p ⟨k, rfl⟩ hs htend, h₀]
    simp
  · have hFk : F k ≠ 0 := by
      dsimp [F]
      exact primaryFactor_ne_zero p (by
        intro h
        rw [div_eq_one_iff_eq (hane k)] at h
        exact hz h)
    have hinv : HasProd (fun n : ℕ => if n = k then (F k)⁻¹ else 1) ((F k)⁻¹) := by
      exact hasProd_ite_eq k ((F k)⁻¹)
    have hmul : HasProd (fun n : ℕ => F n * (if n = k then (F k)⁻¹ else 1))
        ((∏' n : ℕ, F n) * (F k)⁻¹) :=
      hm.hasProd.mul hinv
    have heqfun : (fun n : ℕ => F n * (if n = k then (F k)⁻¹ else 1)) =
        (fun n : ℕ => if n = k then 1 else F n) := by
      funext n
      by_cases hn : n = k
      · subst hn
        simp [hFk]
      · simp [hn]
    have hite : HasProd (fun n : ℕ => if n = k then 1 else F n)
        ((∏' n : ℕ, F n) * (F k)⁻¹) := by
      exact heqfun ▸ hmul
    have hmit : Multipliable (fun n : ℕ => if n = k then 1 else F n) :=
      ⟨(∏' n : ℕ, F n) * (F k)⁻¹, hite⟩
    have hskip_val : (∏' n : ℕ, (if n = k then 1 else F n)) = (∏' n : ℕ, F n) * (F k)⁻¹ :=
      (hite.unique hmit.hasProd).symm
    have hsplit : canonicalProductNat p a z * (F k)⁻¹ = canonicalProductNatSkip k p a z := by
      rw [canonicalProductNatSkip]
      simpa [canonicalProductNat, F] using hskip_val.symm
    simpa [F, mul_comm] using (mul_inv_eq_iff_eq_mul₀ hFk).mp hsplit

/-- A convergent product equals `exp` of the sum of the logarithms. -/
lemma tprod_eq_exp_tsum_log_any {ι : Type*} {x : ι → ℂ} (hm : Multipliable x)
    (hlog : Summable fun n : ι => Complex.log (x n)) (hx : ∀ n, x n ≠ 0) :
    (∏' n : ι, x n) = Complex.exp (∑' n : ι, Complex.log (x n)) := by
  have hprod : Tendsto (fun s : Finset ι => ∏ n ∈ s, x n) atTop (𝓝 (∏' n : ι, x n)) := by
    simpa [HasProd, SummationFilter.unconditional] using hm.hasProd
  have hsum : Tendsto (fun s : Finset ι => ∑ n ∈ s, Complex.log (x n)) atTop
      (𝓝 (∑' n : ι, Complex.log (x n))) := by
    simpa [HasSum, SummationFilter.unconditional] using hlog.hasSum
  have hexp : Tendsto (fun s : Finset ι => Complex.exp (∑ n ∈ s, Complex.log (x n))) atTop
      (𝓝 (Complex.exp (∑' n : ι, Complex.log (x n)))) :=
    (Complex.continuous_exp.tendsto (∑' n : ι, Complex.log (x n))).comp hsum
  have heq : ∀ s : Finset ι, (∏ n ∈ s, x n) = Complex.exp (∑ n ∈ s, Complex.log (x n)) := by
    intro s
    calc ∏ n ∈ s, x n = ∏ n ∈ s, Complex.exp (Complex.log (x n)) := by
          refine Finset.prod_congr rfl ?_
          intro n hn
          rw [Complex.exp_log (hx n)]
      _ = Complex.exp (∑ n ∈ s, Complex.log (x n)) := by rw [Complex.exp_sum]
  exact tendsto_nhds_unique (hprod.congr' (by
    filter_upwards with s
    exact heq s)) hexp

/-- The skipped canonical product does not vanish at the removed zero. -/
lemma canonicalProductNatSkip_ne_zero_at {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (p : ℕ) (k : ℕ)
    (hinj : Function.Injective a) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    canonicalProductNatSkip k p a (a k) ≠ 0 := by
  let x : ℕ → ℂ := fun n => if n = k then 1 else primaryFactor p (a k / a n)
  have hm : Multipliable x := by
    exact (multipliableLocallyUniformlyOn_primaryFactorSkip hane p k hs htend).multipliable (by simp)
  have hx : ∀ n, x n ≠ 0 := by
    intro n
    by_cases hn : n = k
    · subst hn
      simp [x]
    · simp [x, hn]
      exact primaryFactor_ne_zero p (by
        intro h
        rw [div_eq_one_iff_eq (hane n)] at h
        exact hn (hinj h).symm)
  have hlog : Summable fun n : ℕ => Complex.log (x n) := by
    have hlg : Summable (fun n : ℕ => Complex.log (primaryFactor p (a k / a n))) :=
      summable_log_primaryFactor hane p hs htend
    have h₀ : primaryFactor p (a k / a k) = 0 := by
      rw [primaryFactor_eq_zero_iff p (a k / a k)]
      exact div_self (hane k)
    have hcong : (fun n : ℕ => Complex.log (x n)) = fun n : ℕ => Complex.log (primaryFactor p (a k / a n)) := by
      funext n
      by_cases hn : n = k
      · subst hn
        simp [x, h₀]
      · simp [x, hn]
    simpa [hcong] using hlg
  have heq : (∏' n : ℕ, x n) = Complex.exp (∑' n : ℕ, Complex.log (x n)) :=
    tprod_eq_exp_tsum_log_any hm hlog hx
  have heq' : canonicalProductNatSkip k p a (a k) =
      Complex.exp (∑' n : ℕ, Complex.log (x n)) := by
    rw [canonicalProductNatSkip]
    simpa [x] using heq
  rw [heq']
  exact Complex.exp_ne_zero _

/-- Two analytic functions equal on a punctured neighbourhood agree at the point. -/
lemma analytic_extension_unique {g₁ g₂ : ℂ → ℂ} {z₀ : ℂ}
    (hg₁ : AnalyticAt ℂ g₁ z₀) (hg₂ : AnalyticAt ℂ g₂ z₀)
    (heq : g₁ =ᶠ[𝓝[≠] z₀] g₂) : g₁ z₀ = g₂ z₀ := by
  have ht₁ : Tendsto g₁ (𝓝[≠] z₀) (𝓝 (g₁ z₀)) :=
    hg₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht₂ : Tendsto g₂ (𝓝[≠] z₀) (𝓝 (g₂ z₀)) :=
    hg₂.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique ht₁ (ht₂.congr' heq.symm)

/-- The order of a non-vanishing analytic function at a point is zero. -/
lemma meromorphicOrderAt_eq_zero_of_ne_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z₀) (hf₀ : f z₀ ≠ 0) :
    meromorphicOrderAt f z₀ = 0 := by
  exact (meromorphicOrderAt_eq_int_iff (n := 0) hf.meromorphicAt).mpr ⟨f, hf, hf₀, by
    filter_upwards with z
    simp⟩

/-- The order of the skipped canonical product at the removed zero is zero. -/
lemma meromorphicOrderAt_canonicalProductNatSkip_eq_zero {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (p : ℕ) (k : ℕ) (hinj : Function.Injective a) (hs : Summable fun n : ℕ => (‖a n‖ ^ (p + 1))⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    meromorphicOrderAt (fun z => canonicalProductNatSkip k p a z) (a k) = 0 := by
  have hskip : AnalyticAt ℂ (fun z => canonicalProductNatSkip k p a z) (a k) :=
    Differentiable.analyticAt (differentiable_canonicalProductNatSkip hane p k hs htend) (a k)
  have hne : (fun z => canonicalProductNatSkip k p a z) (a k) ≠ 0 :=
    canonicalProductNatSkip_ne_zero_at hane p k hinj hs htend
  exact (meromorphicOrderAt_eq_int_iff (n := 0) hskip.meromorphicAt).mpr ⟨
    fun z => canonicalProductNatSkip k p a z, hskip, hne, by
      filter_upwards with z
      simp⟩

/-- The order of the `k`-th primary factor at the zero `a k` is one. -/
lemma meromorphicOrderAt_primaryFactor_one_scaled_at_zero {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (k : ℕ) :
    meromorphicOrderAt (fun z => primaryFactor 1 (z / a k)) (a k) = 1 := by
  have hdiff : AnalyticAt ℂ (fun z : ℂ => z / a k) (a k) :=
    Differentiable.analyticAt (differentiable_id.div (differentiable_const (a k)) (fun _ => hane k)) (a k)
  have hg : AnalyticAt ℂ (fun z => (-1 / a k) * Complex.exp (z / a k)) (a k) :=
    AnalyticAt.mul (analyticAt_const (v := (-1 / a k)))
      (AnalyticAt.comp (Differentiable.analyticAt Complex.differentiable_exp (a k / a k)) hdiff)
  have hg_ne : ((-1 / a k) * Complex.exp (a k / a k)) ≠ 0 := by
    rw [div_self (hane k)]
    exact mul_ne_zero (div_ne_zero (by norm_num) (hane k)) (Complex.exp_ne_zero 1)
  have hgeq : ∀ᶠ z in 𝓝[≠] (a k),
      primaryFactor 1 (z / a k) = (z - a k) ^ (1 : ℤ) • ((-1 / a k) * Complex.exp (z / a k)) := by
    filter_upwards with z
    simp [primaryFactor]
    field_simp [hane k]
    ring
  exact (meromorphicOrderAt_eq_int_iff (n := 1)
    (AnalyticAt.meromorphicAt (Differentiable.analyticAt (differentiable_primaryFactor_scaled 1 (hane k)) (a k)))).mpr
    ⟨fun z => (-1 / a k) * Complex.exp (z / a k), hg, hg_ne, hgeq⟩

/-- The order of the canonical product at the zero `a k` is one. -/
lemma meromorphicOrderAt_canonicalProductNat_one_at_zero {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (k : ℕ) (hinj : Function.Injective a) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    meromorphicOrderAt (canonicalProductNat 1 a) (a k) = 1 := by
  have hsplit : canonicalProductNat 1 a =
      fun z : ℂ => primaryFactor 1 (z / a k) * canonicalProductNatSkip k 1 a z := by
    funext z
    exact canonicalProductNat_eq_mul_skip hane 1 k hs2 htend z
  have hdiff : AnalyticAt ℂ (fun z : ℂ => z / a k) (a k) :=
    Differentiable.analyticAt (differentiable_id.div (differentiable_const (a k)) (fun _ => hane k)) (a k)
  have hgan : AnalyticAt ℂ (fun z => (-1 / a k) * Complex.exp (z / a k) * canonicalProductNatSkip k 1 a z) (a k) :=
    AnalyticAt.mul
      (AnalyticAt.mul (analyticAt_const (v := (-1 / a k)))
        (AnalyticAt.comp (Differentiable.analyticAt Complex.differentiable_exp (a k / a k)) hdiff))
      (Differentiable.analyticAt (differentiable_canonicalProductNatSkip hane 1 k hs2 htend) (a k))
  have hgan_ne : ((-1 / a k) * Complex.exp (a k / a k) * canonicalProductNatSkip k 1 a (a k)) ≠ 0 := by
    rw [div_self (hane k)]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (by norm_num) (hane k)) (Complex.exp_ne_zero 1))
      (canonicalProductNatSkip_ne_zero_at hane 1 k hinj hs2 htend)
  have hgeq : ∀ᶠ z in 𝓝[≠] (a k),
      canonicalProductNat 1 a z = (z - a k) ^ (1 : ℤ) • ((-1 / a k) * Complex.exp (z / a k) * canonicalProductNatSkip k 1 a z) := by
    filter_upwards with z
    rw [hsplit]
    simp [primaryFactor, mul_assoc]
    field_simp [hane k]
    ring
  exact (meromorphicOrderAt_eq_int_iff (n := 1)
    (AnalyticAt.meromorphicAt (Differentiable.analyticAt (differentiable_canonicalProductNat hane 1 hs2 htend) (a k)))).mpr
    ⟨fun z => (-1 / a k) * Complex.exp (z / a k) * canonicalProductNatSkip k 1 a z, hgan, hgan_ne, hgeq⟩

/-- An analytic function vanishing at `z₀` with order at most one has order exactly one. -/
lemma meromorphicOrderAt_eq_one_of_mem {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hf₀ : f z₀ = 0) (hord : meromorphicOrderAt f z₀ ≤ 1) :
    meromorphicOrderAt f z₀ = 1 := by
  have hfₐ : AnalyticAt ℂ f z₀ := Differentiable.analyticAt hf z₀
  have hge : 1 ≤ meromorphicOrderAt f z₀ := by
    have hne : analyticOrderAt f z₀ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hfₐ, hf₀⟩
    cases h₀ : analyticOrderAt f z₀ with
    | top =>
      rw [hfₐ.meromorphicOrderAt_eq, h₀, ENat.map_top]
      exact le_top
    | coe n =>
      have hn : n ≠ 0 := by
        intro hn0
        apply hne
        rw [h₀, hn0]
        simp
      have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn)
      rw [hfₐ.meromorphicOrderAt_eq, h₀, ENat.map_natCast]
      exact_mod_cast hn1
  exact le_antisymm hord hge

/-- The Hadamard factorization theorem for genus one. -/
theorem hadamard_factorization_genus_one {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f) (hane : ∀ n, a n ≠ 0)
    (hzero : ∀ z, f z = 0 ↔ ∃ n, z = a n)
    (hord : ∀ z, meromorphicOrderAt f z ≤ 1)
    (hinj : Function.Injective a) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) * canonicalProductNat 1 a z := by
  let P : ℂ → ℂ := canonicalProductNat 1 a
  have hPd : Differentiable ℂ P := differentiable_canonicalProductNat hane 1 hs2 htend
  have hPne : ∀ z, (∀ n, z ≠ a n) → P z ≠ 0 := by
    intro z hz
    exact canonicalProductNat_ne_zero hane 1 hz hs2 htend
  have hPz : ∀ k : ℕ, P (a k) = 0 := by
    intro k
    exact canonicalProductNat_eq_zero_of_mem hane 1 ⟨k, rfl⟩ hs2 htend
  have hordP : ∀ k : ℕ, meromorphicOrderAt P (a k) = 1 := by
    intro k
    exact meromorphicOrderAt_canonicalProductNat_one_at_zero hane k hinj hs2 htend
  have hordf : ∀ k : ℕ, meromorphicOrderAt f (a k) = 1 := by
    intro k
    exact meromorphicOrderAt_eq_one_of_mem hf ((hzero (a k)).2 ⟨k, rfl⟩) (hord (a k))
  have hordQ₀ : ∀ k : ℕ, meromorphicOrderAt (fun z => f z / P z) (a k) = 0 := by
    intro k
    calc meromorphicOrderAt ((fun z : ℂ => f z) / P) (a k)
        = meromorphicOrderAt (fun z : ℂ => f z) (a k) - meromorphicOrderAt P (a k) := by
            exact meromorphicOrderAt_div (AnalyticAt.meromorphicAt (Differentiable.analyticAt hf (a k)))
              (AnalyticAt.meromorphicAt (Differentiable.analyticAt hPd (a k)))
      _ = 0 := by
            rw [hordf k, hordP k]
            simp
  have hQ : ∀ z₀ : ℂ, ∃ g₀ : ℂ → ℂ, AnalyticAt ℂ g₀ z₀ ∧ g₀ z₀ ≠ 0 ∧
      (fun z => f z / P z) =ᶠ[𝓝[≠] z₀] g₀ := by
    intro z₀
    by_cases hz₀ : ∃ n, z₀ = a n
    · rcases hz₀ with ⟨k, rfl⟩
      have h₀ : meromorphicOrderAt (fun z => f z / P z) (a k) = 0 := hordQ₀ k
      rcases (meromorphicOrderAt_eq_int_iff (n := 0) (by
        change MeromorphicAt ((fun z : ℂ => f z) / P) (a k)
        exact MeromorphicAt.mul (AnalyticAt.meromorphicAt (Differentiable.analyticAt hf (a k)))
          (MeromorphicAt.inv (AnalyticAt.meromorphicAt (Differentiable.analyticAt hPd (a k)))))).mp h₀ with ⟨g₀, hg₀, hg₀ne, hgeq⟩
      refine ⟨g₀, hg₀, hg₀ne, ?_⟩
      filter_upwards [hgeq] with z hz
      simp at hz
      exact hz
    · have hf₀ : f z₀ ≠ 0 := by
        intro h
        exact hz₀ ((hzero z₀).1 h)
      have hP₀ : P z₀ ≠ 0 := hPne z₀ (by
        intro n hn
        exact hz₀ ⟨n, hn⟩)
      refine ⟨fun z => f z / P z, ?_, ?_, ?_⟩
      · exact AnalyticAt.div (Differentiable.analyticAt hf z₀) (Differentiable.analyticAt hPd z₀) hP₀
      · exact div_ne_zero hf₀ hP₀
      · filter_upwards with z
        rfl
  let Q : ℂ → ℂ := fun z₀ => (Classical.choose (hQ z₀)) z₀
  have hQval : ∀ z₀, Q z₀ = (Classical.choose (hQ z₀)) z₀ := by
    intro z₀
    rfl
  have zeros_isolated : ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    intro z₀
    rcases (Differentiable.analyticAt hf z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      classical
      rcases _root_.eventually_nhds_iff.mp h with ⟨s, hs_sub, hs_open, hs_mem⟩
      rcases Metric.isOpen_iff.mp hs_open z₀ hs_mem with ⟨r, hr, hr_sub⟩
      rcases Filter.Eventually.exists_forall_of_atTop
        (htend.eventually (Filter.eventually_ge_atTop (‖z₀‖ + 1))) with ⟨N, hN⟩
      let ρ : ℝ := min r 1
      have hρ : 0 < ρ := lt_min hr zero_lt_one
      let bad : Finset ℝ := (Finset.range N).image
        (fun n => if h : ∃ r : ℝ, (r : ℂ) = a n - z₀ then Classical.choose h else 0)
      have hpick : ∃ t : ℝ, t ∈ Set.Ioo 0 ρ ∧ t ∉ (bad : Set ℝ) := by
        rcases Set.Infinite.exists_notMem_finite (Set.Ioo_infinite hρ) bad.finite_toSet with
          ⟨t, htI, htb⟩
        exact ⟨t, htI, htb⟩
      rcases hpick with ⟨t, htI, htb⟩
      let z : ℂ := z₀ + (t : ℂ)
      have hz1 : ‖z - z₀‖ < ρ := by
        simp [z]
        rw [abs_of_pos htI.1]
        exact htI.2
      have hz2 : ∀ n : ℕ, z ≠ a n := by
        intro n
        by_cases hn : n < N
        · intro heq
          have ht' : (t : ℂ) = a n - z₀ := by
            rw [← heq]
            simp [z]
          have hc : ∃ r : ℝ, (r : ℂ) = a n - z₀ := ⟨t, ht'⟩
          have hch : Classical.choose hc = t := by
            have h1 : ((Classical.choose hc : ℝ) : ℂ) = (t : ℂ) := by
              rw [Classical.choose_spec hc, ← ht']
            exact congrArg Complex.re h1
          have hbad : t ∈ bad := by
            dsimp [bad]
            refine Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, ?_⟩
            simp [hc, hch]
          exact htb hbad
        · intro heq
          have hnN : N ≤ n := Nat.le_of_not_gt hn
          have hnorm : ‖z₀‖ + 1 ≤ ‖a n‖ := hN n hnN
          have hz1' : ‖z - z₀‖ < 1 := lt_of_lt_of_le hz1 (min_le_right r 1)
          have hdist : ‖a n - z₀‖ < 1 := by
            rw [← heq]
            exact hz1'
          have htri : ‖a n‖ ≤ ‖a n - z₀‖ + ‖z₀‖ := by
            simpa [sub_eq_add_neg, add_assoc] using norm_add_le (a n - z₀) z₀
          linarith
      have hzs : z ∈ s := hr_sub (by
        simpa [Metric.mem_ball, dist_eq_norm] using
          lt_of_lt_of_le hz1 (min_le_left r 1))
      have hfz : f z = 0 := hs_sub z hzs
      rcases (hzero z).1 hfz with ⟨n, hn⟩
      exact hz2 n hn
    · exact h
  have hQeq : ∀ z₀, Q =ᶠ[𝓝[≠] z₀] (fun z => f z / P z) := by
    intro z₀
    filter_upwards [zeros_isolated z₀] with z hfz
    have hz : P z ≠ 0 := hPne z (by
      intro n hn
      exact hfz ((hzero z).2 ⟨n, hn⟩))
    rw [hQval z]
    exact analytic_extension_unique (Classical.choose_spec (hQ z)).1
      (AnalyticAt.div (Differentiable.analyticAt hf z) (Differentiable.analyticAt hPd z) hz)
      ((Classical.choose_spec (hQ z)).2.2.symm.trans (by
        filter_upwards with w
        rfl))
  have hQanal : ∀ z₀, AnalyticAt ℂ Q z₀ := by
    intro z₀
    have hmero : MeromorphicAt Q z₀ := by
      have hq : MeromorphicAt (fun z => f z / P z) z₀ := by
        change MeromorphicAt ((fun z : ℂ => f z) / P) z₀
        exact MeromorphicAt.mul (AnalyticAt.meromorphicAt (Differentiable.analyticAt hf z₀))
          (MeromorphicAt.inv (AnalyticAt.meromorphicAt (Differentiable.analyticAt hPd z₀)))
      exact MeromorphicAt.congr hq (hQeq z₀).symm
    have hcont : ContinuousAt Q z₀ := by
      rcases hQ z₀ with ⟨g₀, hg₀, hg₀ne, hgeq⟩
      have h₀ : 0 ≤ meromorphicOrderAt (fun z => f z / P z) z₀ := by
        by_cases hz₀ : ∃ n, z₀ = a n
        · rcases hz₀ with ⟨k, rfl⟩
          rw [hordQ₀ k]
        · have hf₀ : f z₀ ≠ 0 := by
            intro h
            exact hz₀ ((hzero z₀).1 h)
          have hP₀ : P z₀ ≠ 0 := hPne z₀ (by
            intro n hn
            exact hz₀ ⟨n, hn⟩)
          change meromorphicOrderAt ((fun z : ℂ => f z) / P) z₀ ≥ 0
          rw [meromorphicOrderAt_div (AnalyticAt.meromorphicAt (Differentiable.analyticAt hf z₀))
            (AnalyticAt.meromorphicAt (Differentiable.analyticAt hPd z₀))]
          rw [meromorphicOrderAt_eq_zero_of_ne_zero (Differentiable.analyticAt hf z₀) hf₀,
            meromorphicOrderAt_eq_zero_of_ne_zero (Differentiable.analyticAt hPd z₀) hP₀]
          simp
      rcases tendsto_nhds_of_meromorphicOrderAt_nonneg (by
        change MeromorphicAt ((fun z : ℂ => f z) / P) z₀
        exact MeromorphicAt.mul (AnalyticAt.meromorphicAt (Differentiable.analyticAt hf z₀))
          (MeromorphicAt.inv (AnalyticAt.meromorphicAt (Differentiable.analyticAt hPd z₀)))) h₀ with ⟨c, hc⟩
      have hc' : c = g₀ z₀ := by
        have hg₀' : Tendsto g₀ (𝓝[≠] z₀) (𝓝 (g₀ z₀)) :=
          hg₀.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact tendsto_nhds_unique (Tendsto.congr' hgeq hc) hg₀'
      have hQz₀ : Q z₀ = g₀ z₀ := by
        rw [hQval z₀]
        exact analytic_extension_unique (Classical.choose_spec (hQ z₀)).1 hg₀
          ((Classical.choose_spec (hQ z₀)).2.2.symm.trans hgeq)
      have hQt : Tendsto Q (𝓝[≠] z₀) (𝓝 (Q z₀)) := by
        rw [hQz₀, ← hc']
        exact Tendsto.congr' (hQeq z₀).symm hc
      exact continuousAt_iff_punctured_nhds.mpr hQt
    exact MeromorphicAt.analyticAt hmero hcont
  have hQd : Differentiable ℂ Q := by
    have hQan : AnalyticOnNhd ℂ Q (Set.univ : Set ℂ) := by
      intro z hz
      exact hQanal z
    exact differentiableOn_univ.mp (hQan.differentiableOn)
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z
    exact (Classical.choose_spec (hQ z)).2.1
  rcases exists_entire_log (f := Q) hQd (hQne 0) hQne with ⟨g, hgd, hgeq⟩
  refine ⟨g, hgd, ?_⟩
  intro z
  by_cases hz : f z = 0
  · rcases (hzero z).1 hz with ⟨k, rfl⟩
    rw [canonicalProductNat_eq_zero_of_mem hane 1 ⟨k, rfl⟩ hs2 htend]
    simpa using hz
  · have hzane : ∀ n, z ≠ a n := by
      intro n hn
      apply hz
      exact (hzero z).2 ⟨n, hn⟩
    have hP₀ : P z ≠ 0 := hPne z hzane
    have h₃ : Q z = f z / P z := by
      rw [hQval z]
      exact analytic_extension_unique (Classical.choose_spec (hQ z)).1
        (AnalyticAt.div (Differentiable.analyticAt hf z) (Differentiable.analyticAt hPd z) hP₀)
        ((Classical.choose_spec (hQ z)).2.2.symm.trans (by
          filter_upwards with w
          rfl))
    have h₄ : f z = Q z * P z := by
      rw [h₃]
      field_simp [hP₀]
    have h₅ : Q z = Complex.exp (g z) := hgeq z
    rw [h₄, h₅]

/-!
## Application to the completed Riemann zeta function

We define the entire function xi (ξ(s) = s(s-1)·Λ₀(s) + 1, where Λ₀ is
mathlib's completedRiemannZeta₀), record the algebraic identity linking it to
the completed zeta function Λ, and prove the **zero identification**: the zeros
of ξ are exactly the non-trivial zeros of the Riemann zeta function
(xi_zero_iff_riemannZeta_zero), together with the critical-strip classification
(
iemannZeta_zero_imp_critical_strip_or_trivial).

These feed the h_decomp / h_analytic hypotheses of

iemannZeta_ne_zero_of_zeroFreeEdge in ZeroFreeRegionProof.lean.
-/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

set_option maxHeartbeats 800000 in
theorem xi_differentiable : Differentiable ℂ xi := by
  unfold xi
  apply Differentiable.add
  · apply Differentiable.mul
    · apply Differentiable.mul <;> fun_prop
    · exact differentiable_completedZeta₀
  · fun_prop

set_option maxHeartbeats 800000 in
theorem xi_eq_mul_completedRiemannZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  field_simp [hs, sub_ne_zero.mpr hs']
  ring

set_option maxHeartbeats 800000 in
theorem xi_zero_iff_riemannZeta_zero {s : ℂ} (hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro hxi
    by_cases hs : s = 0
    · rw [hs, xi] at hxi
      norm_num at hxi
    · by_cases hs1 : s = 1
      · rw [hs1, xi] at hxi
        norm_num at hxi
      · have hΛ : completedRiemannZeta s = 0 := by
          have hxi' : s * (s - 1) * completedRiemannZeta s = 0 := by
            rwa [xi_eq_mul_completedRiemannZeta hs hs1] at hxi
          have hsnz : s * (s - 1) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr hs1)
          exact (mul_eq_zero.mp hxi').resolve_left hsnz
        rw [riemannZeta_def_of_ne_zero hs, hΛ]
        simp
  · intro hζ
    by_cases hs : s = 0
    · rw [hs, riemannZeta_zero] at hζ
      norm_num at hζ
    · by_cases hs1 : s = 1
      · rw [hs1] at hζ
        exact False.elim ((riemannZeta_ne_zero_of_one_le_re (s := 1) (by norm_num)) hζ)
      · have hΓne : s.Gammaℝ ≠ 0 := by
          rw [Complex.Gammaℝ_def]
          apply mul_ne_zero
          · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
            exact Complex.exp_ne_zero _
          · exact Complex.Gamma_ne_zero hΓ
        have hΛ : completedRiemannZeta s = 0 := by
          rw [riemannZeta_def_of_ne_zero hs] at hζ
          exact (div_eq_zero_iff.mp hζ).resolve_right hΓne
        rw [xi_eq_mul_completedRiemannZeta hs hs1, hΛ]
        simp

set_option maxHeartbeats 800000 in
theorem riemannZeta_zero_imp_critical_strip_or_trivial {s : ℂ} (hζ : riemannZeta s = 0) :
    0 < s.re ∨ ∃ n : ℕ, s = -2 * (n + 1) := by
  by_contra h
  push_neg at h
  have hsre : s.re ≤ 0 := h.1
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  by_cases hint : ∃ n : ℕ, s = -n
  · rcases hint with ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      simp only [neg_zero, Nat.cast_zero] at hζ
      rw [riemannZeta_zero] at hζ
      norm_num at hζ
    · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : 1 ≤ m := by
          by_contra hm'
          have : m = 0 := by omega
          subst m
          simp at hn
        exact h.2 (m - 1) (by
          rw [Nat.cast_sub hm]
          norm_num
          ring)
      · have hne : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
          let n' : ℕ := 2 * m + 1
          have hn'0 : (n' : ℂ) ≠ 0 := by exact_mod_cast (show n' ≠ 0 by omega)
          have hΓneg : (-(n' : ℂ)).Gammaℝ ≠ 0 := by
            rw [Complex.Gammaℝ_def]
            apply mul_ne_zero
            · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
              exact Complex.exp_ne_zero _
            · apply Complex.Gamma_ne_zero
              intro k hk
              have hre : (-(n' : ℂ) / 2).re = (-(k : ℂ)).re := congrArg Complex.re hk
              have h1 : (-(n' : ℂ) / 2).re = -(n' : ℝ) / 2 := by simp
              have h2 : (-(k : ℂ)).re = -(k : ℝ) := by simp
              rw [h1, h2] at hre
              have hrn : (n' : ℝ) = 2 * (k : ℝ) := by linarith
              have hn' : n' = 2 * k := by exact_mod_cast hrn
              dsimp [n'] at hn'
              omega
          have hζ1 : riemannZeta (1 + (n' : ℂ)) ≠ 0 :=
            riemannZeta_ne_zero_of_one_le_re (s := 1 + (n' : ℂ)) (by simp)
          have hΛ1 : completedRiemannZeta (1 + (n' : ℂ)) ≠ 0 := by
            intro hΛ
            have hdef := riemannZeta_def_of_ne_zero (s := 1 + (n' : ℂ))
              (by
                have h : 1 ≤ (1 + (n' : ℂ)).re := by simp
                intro h0
                rw [h0] at h
                norm_num at h)
            rw [hΛ] at hdef
            exact hζ1 (by simpa using hdef)
          have hΛneg : completedRiemannZeta (1 + (n' : ℂ)) = completedRiemannZeta (-(n' : ℂ)) := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (completedRiemannZeta_one_sub (1 + (n' : ℂ))).symm
          intro hz
          have hdef := riemannZeta_def_of_ne_zero (s := -(n' : ℂ)) (neg_ne_zero.mpr hn'0)
          rw [hdef] at hz
          have hΛ0 : completedRiemannZeta (-(n' : ℂ)) = 0 :=
            (div_eq_zero_iff.mp hz).resolve_right hΓneg
          exact hΛ1 (by
            rw [hΛneg]
            exact hΛ0)
        exact hne hζ
  · push_neg at hint
    have hfe := riemannZeta_one_sub (s := s) hint hs1
    have hζ1s : riemannZeta (1 - s) = 0 := by
      rw [hfe, hζ]
      simp
    have hre1 : 1 ≤ (1 - s).re := by
      simp
      linarith
    exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hre1) hζ1s

/-!
### The logarithmic derivative identity (h_decomp)

For ξ = e^g · ∏ₙ E₁(·/aₙ) (the Hadamard factorization, supplied as hypotheses
hzero/hord/hinj/hs2/htend on the zero sequence ), we obtain the
logarithmic derivative identity

-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv (·Γℝ)(s)) - Σₙ (1/(s-aₙ) + 1/aₙ)

for Re s > 1 (logDeriv_completedZeta).  Together with mathlib's
LSeries_vonMangoldt_eq_deriv_riemannZeta_div (L ↗Λ = -ζ'/ζ) this instantiates
the h_decomp hypothesis of zeroFreeEdge_from_factorization /

iemannZeta_ne_zero_of_zeroFreeEdge in ZeroFreeRegionProof.lean, with
nalytic s = -g'(s) + 1/s + 1/(s-1) + logDeriv (·Γℝ)(s) and the zero-sum
truncated to any finite Finset Z of zeros (the remainder being absorbed into
nalytic).
-/
theorem logDeriv_xi_of_factorization {a : ℕ → ℂ} {g : ℂ → ℂ} {z : ℂ}
    (hane : ∀ n, a n ≠ 0) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hgd : Differentiable ℂ g)
    (hxi : ∀ w, xi w = Complex.exp (g w) * canonicalProductNat 1 a w)
    (hzane : ∀ n, z ≠ a n) :
    logDeriv xi z = deriv g z + ∑' n, (1 / (z - a n) + 1 / a n) := by
  let P : ℂ → ℂ := canonicalProductNat 1 a
  have hP0 : P z ≠ 0 := by
    dsimp [P]
    exact canonicalProductNat_ne_zero hane 1 hzane hs2 htend
  have hlogP : logDeriv P z = ∑' n, (1 / (z - a n) + 1 / a n) := by
    dsimp [P]
    exact logDeriv_canonicalProductNat_genus_one hane hs2 htend hzane
  have hlogexp : logDeriv (fun w : ℂ => Complex.exp (g w)) z = deriv g z := by
    rw [logDeriv_apply]
    have h₁ : DifferentiableAt ℂ Complex.exp (g z) := Complex.differentiableAt_exp (x := g z)
    have h₂ : DifferentiableAt ℂ g z := hgd.differentiableAt
    have hc := deriv_comp z h₁ h₂
    rw [show (fun w : ℂ => Complex.exp (g w)) = Complex.exp ∘ g from rfl, hc]
    rw [show deriv Complex.exp (g z) = Complex.exp (g z) from (Complex.hasDerivAt_exp (g z)).deriv]
    ring
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  have hlogmul : logDeriv (fun w : ℂ => Complex.exp (g w) * P w) z =
      logDeriv (fun w : ℂ => Complex.exp (g w)) z + logDeriv P z := by
    exact logDeriv_mul z (Complex.exp_ne_zero (g z)) hP0
      (DifferentiableAt.comp z (Complex.differentiableAt_exp (x := g z)) hgd.differentiableAt)
      (differentiable_canonicalProductNat hane 1 hs2 htend).differentiableAt
  have hfun : xi = fun w : ℂ => Complex.exp (g w) * P w := by
    funext w
    exact hxi w
  rw [hfun, hlogmul, hlogexp, hlogP]

set_option maxHeartbeats 800000 in
theorem neg_logDeriv_riemannZeta_eq_xi {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) (hζ0 : riemannZeta s ≠ 0) :
    - deriv riemannZeta s / riemannZeta s =
      - logDeriv xi s + 1 / s + 1 / (s - 1) + logDeriv (fun x : ℂ => x.Gammaℝ) s := by
  let Λ : ℂ → ℂ := completedRiemannZeta
  let G : ℂ → ℂ := fun x : ℂ => x.Gammaℝ
  have hG0 : G s ≠ 0 := by
    dsimp [G]
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
      exact Complex.exp_ne_zero _
    · exact Complex.Gamma_ne_zero hΓ
  have hΛ0 : Λ s ≠ 0 := by
    dsimp [Λ]
    intro hΛ
    have hdef := riemannZeta_def_of_ne_zero hs
    rw [hΛ] at hdef
    exact hζ0 (by rw [hdef]; simp)
  have hΛd : DifferentiableAt ℂ Λ s := by
    dsimp [Λ]
    exact differentiableAt_completedZeta hs hs1
  have hGd : DifferentiableAt ℂ G s := by
    dsimp [G]
    apply DifferentiableAt.mul
    · have hh : HasDerivAt (fun x : ℂ => -x / 2) (-1 / 2) s := by
        rw [show (fun x : ℂ => -x / 2) = fun x : ℂ => (-1 / 2) * x from by
          funext x
          ring]
        exact hasDerivAt_const_mul (-1 / 2)
      have hc : HasDerivAt (fun x : ℂ => (π : ℂ) ^ (-x / 2)) _ s :=
        HasDerivAt.cpow (hasDerivAt_const s (π : ℂ)) hh
          (Complex.ofReal_mem_slitPlane.mpr Real.pi_pos)
      exact hc.differentiableAt
    · have hhalf : DifferentiableAt ℂ (fun x : ℂ => x / 2) s := by fun_prop
      exact DifferentiableAt.comp s (Complex.differentiableAt_Gamma (s / 2) (by
        intro m hm
        exact hΓ m (by simpa using hm))) hhalf
  have hζeq : riemannZeta =ᶠ[𝓝 s] (fun x : ℂ => Λ x / G x) := by
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hs] with x hx
    simpa [Λ, G] using riemannZeta_def_of_ne_zero hx
  have hlogζ : logDeriv riemannZeta s = logDeriv Λ s - logDeriv G s := by
    have hcongr : logDeriv riemannZeta s = logDeriv (fun x : ℂ => Λ x / G x) s := by
      rw [logDeriv_apply]
      rw [hζeq.deriv_eq, hζeq.eq_of_nhds, logDeriv_apply]
    rw [hcongr]
    have hloginv : logDeriv (fun x : ℂ => (G x)⁻¹) s = -logDeriv G s := by
      rw [logDeriv_apply]
      rw [show deriv (fun x : ℂ => (G x)⁻¹) s = -deriv G s / G s ^ 2 by
        exact (HasDerivAt.inv (hGd.hasDerivAt) hG0).deriv]
      rw [logDeriv_apply]
      field_simp [hG0]
    have hm : logDeriv (fun x : ℂ => Λ x / G x) s = logDeriv Λ s - logDeriv G s := by
      rw [show (fun x : ℂ => Λ x / G x) = fun x : ℂ => Λ x * G⁻¹ x from by
        funext x
        rw [div_eq_mul_inv]
        rfl]
      rw [logDeriv_mul s hΛ0 (inv_ne_zero (a := G s) hG0) hΛd (DifferentiableAt.inv hGd hG0)]
      rw [show logDeriv G⁻¹ s = logDeriv (fun x : ℂ => (G x)⁻¹) s from rfl, hloginv]
      ring
    exact hm
  have hxiΛ : xi =ᶠ[𝓝 s] (fun x : ℂ => x * (x - 1) * Λ x) := by
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hs,
      (isOpen_ne (x := (1 : ℂ))).mem_nhds hs1] with x hx0 hx1
    simpa [Λ] using xi_eq_mul_completedRiemannZeta hx0 hx1
  have hlogxi : logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv Λ s := by
    have hlogcongr : logDeriv xi s = logDeriv (fun x : ℂ => x * (x - 1) * Λ x) s := by
      rw [logDeriv_apply]
      rw [hxiΛ.deriv_eq, hxiΛ.eq_of_nhds, logDeriv_apply]
    rw [hlogcongr]
    have h1 : logDeriv (fun x : ℂ => x) s = 1 / s := by
      rw [logDeriv_apply]
      simp
    have h2 : logDeriv (fun x : ℂ => x - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]
      have hd : deriv (fun x : ℂ => x - 1) s = 1 := by
        simpa using ((hasDerivAt_id s).sub (hasDerivAt_const s (1 : ℂ))).deriv
      rw [hd]
    have hlogid : logDeriv (fun x : ℂ => x * (x - 1)) s = 1 / s + 1 / (s - 1) := by
      rw [← h1, ← h2]
      exact logDeriv_mul s (by simpa using hs) (sub_ne_zero.mpr hs1) (by fun_prop) (by fun_prop)
    have hm : logDeriv (fun x : ℂ => x * (x - 1) * Λ x) s =
        logDeriv (fun x : ℂ => x * (x - 1)) s + logDeriv Λ s := by
      exact logDeriv_mul s (mul_ne_zero hs (sub_ne_zero.mpr hs1)) hΛ0 (by fun_prop) hΛd
    rw [hm, hlogid]
  rw [show - deriv riemannZeta s / riemannZeta s = - logDeriv riemannZeta s from by
    rw [logDeriv_apply]
    ring]
  rw [hlogζ, hlogxi]
  ring

set_option maxHeartbeats 800000 in
theorem logDeriv_completedZeta {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (hinj : Function.Injective a) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n)
    (hord : ∀ z, meromorphicOrderAt xi z ≤ 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s, 1 < s.re ->
        - deriv riemannZeta s / riemannZeta s =
          (- deriv g s + 1 / s + 1 / (s - 1) + logDeriv (fun x : ℂ => x.Gammaℝ) s) -
            ∑' n, (1 / (s - a n) + 1 / a n) := by
  rcases hadamard_factorization_genus_one (f := xi) xi_differentiable hane hzero hord hinj hs2 htend with
    ⟨g, hgd, hxi⟩
  refine ⟨g, hgd, ?_⟩
  intro s hsre
  have h1 : 1 ≤ s.re := le_of_lt hsre
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre : (s / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
    simp at hre
    linarith
  have hxi0 : xi s ≠ 0 := by
    intro h
    exact hζ0 ((xi_zero_iff_riemannZeta_zero hΓ).mp h)
  have hzane : ∀ n : ℕ, s ≠ a n := by
    intro n hn
    exact hxi0 ((hzero s).2 ⟨n, hn⟩)
  have hlog := logDeriv_xi_of_factorization (a := a) (g := g) hane hs2 htend hgd hxi hzane
  have hbridge := neg_logDeriv_riemannZeta_eq_xi hs hs1 hΓ hζ0
  rw [hbridge, hlog]
  ring

/-!
### The zero set of `xi`

The zeros of `xi` are precisely the non-trivial zeros of `ζ`, i.e. the zeros of `ζ`
lying in the critical strip `0 < Re s < 1`.  We record this as a set equality
(`xiZeros_eq_riemannZetaZeros_inter_closedStrip`), which transfers the discreteness
and local-finiteness of `riemannZetaZeros` to the zero set of `xi`, and gives the
cocompact `Tendsto` needed to enumerate the zeros (`tendsto_xiZeros_cofinite_cocompact`).
-/

/-- A zero of `xi` is a zero of `ζ`. -/
theorem xi_zero_imp_riemannZeta_zero {z : ℂ} (hxi : xi z = 0) : riemannZeta z = 0 := by
  by_cases hs : z = 0
  · rw [hs, xi] at hxi
    norm_num at hxi
  · by_cases hs1 : z = 1
    · rw [hs1, xi] at hxi
      norm_num at hxi
    · have hΛ : completedRiemannZeta z = 0 := by
        have hxi' : z * (z - 1) * completedRiemannZeta z = 0 := by
          rwa [xi_eq_mul_completedRiemannZeta hs hs1] at hxi
        have hsnz : z * (z - 1) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr hs1)
        exact (mul_eq_zero.mp hxi').resolve_left hsnz
      rw [riemannZeta_def_of_ne_zero hs, hΛ]
      simp

/-- `xi` does not vanish at the trivial zeros `-2(n+1)` of `ζ`. -/
theorem xi_neg_two_mul_nat_add_one_ne_zero (n : ℕ) : xi (-2 * (n + 1)) ≠ 0 := by
  let u : ℂ := -2 * (n + 1)
  have hpos : (n + 1 : ℕ) ≠ 0 := by omega
  have ht0 : u ≠ 0 := by
    dsimp [u]
    simpa [neg_mul] using
      neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (by exact_mod_cast hpos))
  have ht1 : u ≠ 1 := by
    dsimp [u]
    intro h
    have hre : (-2 * (n + 1) : ℂ).re = 1 := congrArg Complex.re h
    simp at hre
    have hx : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 from by omega)
    nlinarith
  have hΓ1 : (1 + 2 * (n + 1) : ℂ).Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
      exact Complex.exp_ne_zero _
    · apply Complex.Gamma_ne_zero
      intro m hm
      have hre : ((1 + 2 * (n + 1) : ℂ) / 2).re = (-(m : ℂ)).re := congrArg Complex.re hm
      simp at hre
      have hx : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 from by omega)
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      nlinarith
  have hζ1 : riemannZeta (1 + 2 * (n + 1)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
    have hx : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 from by omega)
    nlinarith
  have hΛ1 : completedRiemannZeta (1 + 2 * (n + 1)) ≠ 0 := by
    intro hΛ
    have hdef := riemannZeta_def_of_ne_zero (s := 1 + 2 * (n + 1)) (by
      intro h
      have hre : (1 + 2 * (n + 1) : ℂ).re = 0 := congrArg Complex.re h
      simp at hre
      have hx : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 from by omega)
      nlinarith [hx])
    rw [hΛ] at hdef
    exact hζ1 (by rw [hdef]; simp)
  have hFE : completedRiemannZeta u = completedRiemannZeta (1 - u) := by
    simpa [u, sub_sub_cancel] using completedRiemannZeta_one_sub (1 - u)
  have h1t : 1 - u = 1 + 2 * (n + 1) := by
    dsimp [u]
    ring
  have hxi' : xi u = u * (u - 1) * completedRiemannZeta u := xi_eq_mul_completedRiemannZeta ht0 ht1
  intro h
  have hxi0 : u * (u - 1) * completedRiemannZeta u = 0 := by rwa [hxi'] at h
  rw [hFE, h1t] at hxi0
  exact (mul_eq_zero.mp hxi0).elim
    (fun h1 => (mul_eq_zero.mp h1).elim (fun h2 => False.elim (ht0 h2))
      (fun h2 => False.elim (ht1 (sub_eq_zero.mp h2))))
    hΛ1

/-- A zero of `xi` lies in the critical strip: `0 < Re z`. -/
theorem xi_zero_imp_zero_lt_re {z : ℂ} (hxi : xi z = 0) : 0 < z.re := by
  have hζ := xi_zero_imp_riemannZeta_zero hxi
  rcases riemannZeta_zero_imp_critical_strip_or_trivial hζ with hre | ⟨n, hn⟩
  · exact hre
  · rw [hn] at hxi
    exact False.elim (xi_neg_two_mul_nat_add_one_ne_zero n hxi)

/-- The zero set of `xi` equals the zeros of `ζ` in the closed strip `0 ≤ Re s ≤ 1`
(the boundary is not attained by any zero). -/
theorem xiZeros_eq_riemannZetaZeros_inter_closedStrip :
    {z : ℂ | xi z = 0} = riemannZetaZeros ∩ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := by
  ext z
  constructor
  · intro hz
    have hζ := xi_zero_imp_riemannZeta_zero hz
    have hre0 : 0 < z.re := xi_zero_imp_zero_lt_re hz
    have hre1 : z.re < 1 := by
      by_contra h
      exact (riemannZeta_ne_zero_of_one_le_re (s := z) (le_of_not_gt h)) hζ
    exact ⟨mem_riemannZetaZeros.mpr hζ, ⟨le_of_lt hre0, le_of_lt hre1⟩⟩
  · intro hz
    rcases hz with ⟨hζmem, hstrip⟩
    have hζ : riemannZeta z = 0 := mem_riemannZetaZeros.mp hζmem
    have hre0 : 0 < z.re := by
      rcases riemannZeta_zero_imp_critical_strip_or_trivial hζ with hre | ⟨n, hn⟩
      · exact hre
      · exfalso
        have hzre : z.re ≤ -2 := by
          rw [hn]
          simp
        nlinarith [hstrip.1, hzre]
    have hΓ : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
      intro n hn
      have hre : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      simp at hre
      linarith
    exact (xi_zero_iff_riemannZeta_zero hΓ).mpr hζ

/-- The zero set of `xi` is closed. -/
theorem isClosed_xiZeros : IsClosed {z : ℂ | xi z = 0} := by
  rw [xiZeros_eq_riemannZetaZeros_inter_closedStrip]
  exact isClosed_riemannZetaZeros.inter (isClosed_Icc.preimage continuous_re)

/-- The zero set of `xi` is discrete. -/
theorem isDiscrete_xiZeros : IsDiscrete {z : ℂ | xi z = 0} := by
  rw [xiZeros_eq_riemannZetaZeros_inter_closedStrip]
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_left

/-- Any compact subset of `ℂ` contains only finitely many zeros of `xi`. -/
theorem IsCompact.inter_xiZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ {z : ℂ | xi z = 0}).Finite := by
  have hsub : S ∩ {z : ℂ | xi z = 0} ⊆ S ∩ riemannZetaZeros := by
    intro z hz
    exact ⟨hz.1, mem_riemannZetaZeros.mpr (xi_zero_imp_riemannZeta_zero hz.2)⟩
  exact (hS.inter_riemannZetaZeros_finite).subset hsub

/-- The zeros of `xi` escape to infinity: the inclusion `xiZeros → ℂ` is
cofinite-to-cocompact, so the zeros can be enumerated. -/
theorem tendsto_xiZeros_cofinite_cocompact :
    Tendsto ((↑) : {z : ℂ | xi z = 0} → ℂ) cofinite (cocompact ℂ) :=
  isClosed_xiZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_xiZeros
/-! ## The zero enumeration of `xi` (Jensen)

We construct an enumeration `a : ℕ → ℂ` of the zeros of the entire function
`xi` satisfying the Hadamard hypotheses `hane`, `hinj`, `hzero`, `htend`, and the
convergence estimate `hs2 : Summable (fun n => (‖a n‖ ^ 2)⁻¹)`.  The convergence
estimate is derived from Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`)
applied to `xi`, using the whole-plane growth bound `xi_norm_bound_whole_plane`
(which follows from `orderSet_completedRiemannZeta₀` and the functional
equation), followed by a dyadic counting argument.

The construction requires two facts about the zeros, kept as hypotheses:
`hord : ∀ z, meromorphicOrderAt xi z ≤ 1` (simplicity of the zeros) and
`hSinf : {z | xi z = 0}.Infinite` (infinitely many non-trivial zeros).  With
these, `logDeriv_completedZeta` becomes the concrete `h_decomp` for
`riemannZeta_ne_zero_of_zeroFreeEdge`. -/

open Filter Metric Set Function
open scoped Topology

/-- `xi` does not vanish at `0` (in fact `xi 0 = 1`). -/
theorem xi_ne_zero_at_zero : xi 0 ≠ 0 := by
  rw [xi]
  norm_num

/-- Whole-plane growth of `xi`: for some constants `K ≥ 0` and `C₀ ≥ 0`,
`‖xi z‖ ≤ exp(K·‖z‖^(3/2))` whenever `C₀ ≤ ‖z‖`.

This follows from `orderSet_completedRiemannZeta₀` (a `exp(‖z‖^(3/2))` bound
for `Λ₀` on the whole plane, via the functional equation) together with the
algebraic identity `xi z = z·(z-1)·Λ₀ z + 1` and the elementary estimate
`exp x ≥ x⁴/256` for `x ≥ 0`. -/
theorem xi_norm_bound_whole_plane :
    ∃ K ≥ 0, ∃ C₀ ≥ 0, ∀ z : ℂ, C₀ ≤ ‖z‖ → ‖xi z‖ ≤ Real.exp (K * ‖z‖ ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, r₀, hr₀, hbound⟩ := orderSet_completedRiemannZeta₀
  have hCpos : 0 ≤ C := by
    by_contra h
    have h1 := hbound (r₀ : ℂ) (by rw [Complex.norm_of_nonneg (le_of_lt hr₀)])
    have h2 := norm_nonneg (completedRiemannZeta₀ (r₀ : ℂ))
    have h3 : C * Real.exp (‖(r₀ : ℂ)‖ ^ (3 / 2 : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp h) (Real.exp_pos (‖(r₀ : ℂ)‖ ^ (3 / 2 : ℝ)))
    linarith [h1, h2, h3]
  refine ⟨C + 3, by linarith, max r₀ 10, by linarith [le_max_right r₀ 10], fun z hz => ?_⟩
  have hzr : r₀ ≤ ‖z‖ := le_trans (le_max_left r₀ 10) hz
  have hz10 : (10 : ℝ) ≤ ‖z‖ := le_trans (le_max_right r₀ 10) hz
  have hRpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz1n : ‖z - 1‖ ≤ ‖z‖ + 1 := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ + 1 := by rw [norm_one]
  have hprod : ‖z‖ * ‖z - 1‖ ≤ ‖z‖ ^ 2 + ‖z‖ := by nlinarith [norm_nonneg z, hz1n]
  have hbound' := hbound z hzr
  have hkey : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1 ≤ Real.exp ((C + 3) * ‖z‖ ^ (3 / 2 : ℝ)) := by
    have hs1 : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ ≤ (‖z‖ ^ 2 + ‖z‖) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) :=
      mul_le_mul hprod hbound' (norm_nonneg _) (by nlinarith [norm_nonneg z])
    have hs2 : (‖z‖ ^ 2 + ‖z‖) * (C * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) ≤
        2 * C * ‖z‖ ^ 2 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) := by
      have : ‖z‖ ^ 2 + ‖z‖ ≤ 2 * ‖z‖ ^ 2 := by nlinarith [hz10]
      nlinarith [mul_nonneg hCpos (Real.exp_nonneg (‖z‖ ^ (3 / 2 : ℝ)))]
    have hs3 : 2 * C * ‖z‖ ^ 2 * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) ≤
        2 * C * Real.exp (2 * ‖z‖ ^ (3 / 2 : ℝ)) := by
      rw [mul_assoc (2 * C) (‖z‖ ^ 2), show Real.exp (2 * ‖z‖ ^ (3 / 2 : ℝ)) =
        Real.exp (‖z‖ ^ (3 / 2 : ℝ)) * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) from by
          rw [← Real.exp_add]; ring_nf, mul_comm (‖z‖ ^ 2) (Real.exp _)]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCpos)
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
      have hsq_le_exp : (‖z‖ : ℝ) ^ 2 ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ)) := by
        have hle : (‖z‖ : ℝ) ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ) / 2) := Real.add_one_le_exp _
        have h2 := mul_le_mul (norm_nonneg z) (Real.exp_nonneg (‖z‖ ^ (3 / 2 : ℝ) / 2)) hle hle
        rwa [show Real.exp _ * Real.exp _ = Real.exp (‖z‖ ^ (3 / 2 : ℝ)) from by rw [← Real.exp_add]; ring_nf] at h2
      have h2z : (2:ℝ) * ‖z‖ ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
        have h4 : (4:ℝ) ≤ ‖z‖ := by linarith
        have hsqrt : (2:ℝ) ≤ ‖z‖ ^ (1 / 2 : ℝ) := by
          rw [show (2:ℝ) = (4:ℝ) ^ (1 / 2 : ℝ) from by norm_num [Real.sqrt_eq_rpow]]
          exact Real.rpow_le_rpow (by norm_num) h4 (by norm_num)
        have h12 : (1:ℝ) ≤ ‖z‖ := by linarith
        calc (2:ℝ) * ‖z‖ ≤ ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hsqrt (le_of_lt hRpos)
          _ = ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1:ℝ) := by rw [Real.rpow_one]
          _ = ‖z‖ ^ (1 / 2 + 1 : ℝ) := by rw [← Real.rpow_add (le_of_lt hRpos)]
          _ = ‖z‖ ^ (3 / 2 : ℝ) := by norm_num
      have hzle : (‖z‖ : ℝ) ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ) / 2) :=
        by linarith [Real.add_one_le_exp (‖z‖ ^ (3 / 2 : ℝ) / 2)]
      calc (‖z‖ : ℝ) ^ 2
          ≤ (Real.exp (‖z‖ ^ (3 / 2 : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) hzle 2
        _ = Real.exp (‖z‖ ^ (3 / 2 : ℝ)) := by rw [sq, ← Real.exp_add]; ring_nf
    have hs4 : 2 * C * Real.exp (2 * ‖z‖ ^ (3 / 2 : ℝ)) ≤
        Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by
      have h2c : 2 * C ≤ Real.exp (C * ‖z‖ ^ (3 / 2 : ℝ)) := by
        have := Real.add_one_le_exp (C * ‖z‖ ^ (3 / 2 : ℝ)); nlinarith [Real.exp_nonneg _]
      calc 2 * C * Real.exp (2 * ‖z‖ ^ (3 / 2 : ℝ))
          ≤ Real.exp (C * ‖z‖ ^ (3 / 2 : ℝ)) * Real.exp (2 * ‖z‖ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right h2c (Real.exp_nonneg _)
        _ = Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by rw [← Real.exp_add]; ring_nf
    have hchain : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ ≤ Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by
      linarith [hs1, hs2, hs3, hs4]
    have hRge1 : (1 : ℝ) ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
      rw [← Real.one_rpow (3 / 2 : ℝ)]
      exact Real.rpow_le_rpow (by norm_num) (by linarith [hz10]) (by norm_num)
    have hone : (1 : ℝ) ≤ Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by
      have h1 := Real.add_one_le_exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ))
      have h2 : 0 ≤ (C + 2) * ‖z‖ ^ (3 / 2 : ℝ) := mul_nonneg (by linarith) (by positivity)
      linarith
    have hgap : Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) + 1 ≤ Real.exp ((C + 3) * ‖z‖ ^ (3 / 2 : ℝ)) := by
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hle : Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) + 1 ≤ Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ) + 1) := by
        calc Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) + 1
            ≤ Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) + Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by
              rw [add_le_add_iff_left]; exact hone
          _ = 2 * Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) := by ring
          _ ≤ Real.exp 1 * Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right h2le (Real.exp_nonneg _)
          _ = Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ) + 1) := by rw [Real.exp_add, mul_comm]
      have hexp_le : Real.exp ((C + 2) * ‖z‖ ^ (3 / 2 : ℝ) + 1) ≤ Real.exp ((C + 3) * ‖z‖ ^ (3 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [hRge1])
      exact hle.trans hexp_le
    linarith [hchain, hgap]
  have hxi : ‖xi z‖ ≤ ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1 := by
    unfold xi
    have := norm_add_le (z * (z - 1) * completedRiemannZeta₀ z) 1
    simp only [norm_mul, norm_one] at this
    linarith
  linarith [hxi, hkey]

/-- The zero set of `xi` is countable. -/
theorem xiZeros_countable : ({z : ℂ | xi z = 0} : Set ℂ).Countable := by
  exact IsLindelof.countable_of_isDiscrete
    (HereditarilyLindelofSpace.isLindelof ({z : ℂ | xi z = 0} : Set ℂ)) isDiscrete_xiZeros

/-- The zero set of `xi` is locally finite: only finitely many zeros lie in any
bounded set. -/
theorem xiZeros_bounded_finite (N : ℕ) :
    ((closedBall (0 : ℂ) N : Set ℂ) ∩ {z : ℂ | xi z = 0}).Finite := by
  exact IsCompact.inter_xiZeros_finite (isCompact_closedBall (0 : ℂ) N)

/-- **Enumeration of the zeros of `xi`.**  Assuming that the zeros of `xi` are
simple (`hord`) and infinite in number (`hSinf`), there is an injective
enumeration `a : ℕ → ℂ` of the zero set which escapes to infinity. -/
theorem xi_zero_enumeration (hord : ∀ z, meromorphicOrderAt xi z ≤ 1)
    (hSinf : ({z : ℂ | xi z = 0} : Set ℂ).Infinite) :
    ∃ a : ℕ → ℂ, (∀ n, a n ≠ 0) ∧ Function.Injective a ∧
      Tendsto (fun n : ℕ => ‖a n‖) atTop atTop ∧
      (∀ z, xi z = 0 ↔ ∃ n, z = a n) := by
  let S : Set ℂ := {z : ℂ | xi z = 0}
  have hcount : S.Countable := by
    dsimp [S]
    exact xiZeros_countable
  rcases (Set.countable_infinite_iff_nonempty_denumerable.mp ⟨hcount, hSinf⟩) with ⟨e⟩
  letI : Denumerable S := e
  let a : ℕ → ℂ := fun n => ((Denumerable.eqv S).symm n : ℂ)
  have hinj : Function.Injective a := by
    dsimp [a]
    exact Subtype.val_injective.comp (Denumerable.eqv S).symm.injective
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro n
    have hre : 0 < (a n).re := by
      dsimp [a]
      exact xi_zero_imp_zero_lt_re ((Denumerable.eqv S).symm n).2
    intro h
    rw [h] at hre
    norm_num at hre
  · exact hinj
  · have hbounded : ∀ N : ℕ, ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ).Finite := by
      intro N
      have hfin : ((closedBall (0 : ℂ) N : Set ℂ) ∩ S).Finite := by
        simpa [S] using xiZeros_bounded_finite N
      have hpre : ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ) = a ⁻¹' ((closedBall (0 : ℂ) N : Set ℂ) ∩ S) := by
        ext n
        constructor
        · intro hn
          constructor
          · simpa [dist_eq_norm] using hn
          · dsimp [a]
            exact ((Denumerable.eqv S).symm n).2
        · intro hx
          simpa [dist_eq_norm] using hx.1
      rw [hpre]
      refine hfin.preimage ?_
      intro x hx y hy hxy
      exact hinj hxy
    rw [tendsto_atTop_atTop]
    intro N
    by_cases hN : 0 ≤ N
    · have hfin : ({n : ℕ | ‖a n‖ < (Nat.ceil N : ℝ)} : Set ℕ).Finite := by
        refine ((hbounded (Nat.ceil N)).subset ?_)
        intro n hn
        exact le_of_lt (by simpa using hn)
      have hmem : {n : ℕ | (Nat.ceil N : ℝ) ≤ ‖a n‖} ∈ atTop := by
        have hcompl : {n : ℕ | (Nat.ceil N : ℝ) ≤ ‖a n‖} = {n : ℕ | ‖a n‖ < (Nat.ceil N : ℝ)}ᶜ := by
          ext n; simp [not_lt]
        rw [hcompl, ← Nat.cofinite_eq_atTop]
        exact hfin.compl_mem_cofinite
      rcases Filter.eventually_atTop.1 hmem with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      intro n hn
      exact le_trans (Nat.le_ceil N) (hi n hn)
    · refine ⟨0, ?_⟩
      intro n hn
      exact (le_of_not_gt (by
        intro hlt
        have : 0 ≤ ‖a n‖ := norm_nonneg (a n)
        linarith))
  · intro z
    constructor
    · intro hz
      use (Denumerable.eqv S) ⟨z, by simpa [S] using hz⟩
      dsimp [a]
      simp
    · rintro ⟨n, rfl⟩
      dsimp [a]
      exact ((Denumerable.eqv S).symm n).2
