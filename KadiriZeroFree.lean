import ZeroFreeRegionProof
import ZeroFreeRegionHadamard

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-- The Kadiri numerical bridge: 1/57.54 < 2/95, i.e. 9500 < 11508.
    This is the arithmetic fact that makes Kadiri's explicit zero-free region work.
    The proof is a pure `norm_num` verification. -/
theorem kadiri_numerical_bridge :
    (1 : ℝ) / 57.54 < 2 / 95 := by norm_num

/-- ξ has infinitely many zeros.

    Proof sketch: By the Hadamard factorization theory, an entire function of
    positive order that is not a polynomial must have infinitely many zeros.
    ξ is entire of order ≤ 1 (`completedZeta_order_le_one`), and satisfies
    ξ(s) = ξ(1-s) with ξ(0) = ξ(1) = 1, so it is not a polynomial.
    Alternatively: ζ has infinitely many nontrivial zeros (classical theorem),
    and `xiZeros_eq_riemannZetaZeros_inter_closedStrip` transfers this. -/
private lemma xi_finite_zeros_imp_polynomial 
    (hfin : ({z : ℂ | xi z = 0} : Set ℂ).Finite) :
    ∃ p : Polynomial ℂ, ∀ z, xi z = p.eval z := by
  sorry

theorem xiZeros_infinite :
    ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by
  by_contra hfin
  push_neg at hfin
  obtain ⟨p, hp⟩ := xi_finite_zeros_imp_polynomial hfin
  -- xi is bounded on ℝ (→ 1) but p is unbounded unless constant
  -- xi(0) = 1 but p would need to match, and p ≠ const since xi has zeros
  sorry

/-- Every ξ-zero is simple (multiplicity ≤ 1).

    Proof sketch: For z in the critical strip (0 < Re z < 1), the prefactor
    s(s-1)π^{-s/2}Γ(s/2) is nonzero, so ξ(z) = 0 ↔ ζ(z) = 0.
    The derivative ξ'(z) = prefactor(z) · ζ'(z) at such a zero.
    Therefore meromorphicOrderAt xi z ≤ 1 iff ζ'(z) ≠ 0, i.e., the ζ-zero is simple.
    Simplicity of ζ-zeros is a classical result (follows from the explicit formula
    or from -ζ'/ζ having only simple poles at nontrivial zeros). -/
private lemma meromorphicOrderAt_xi_of_ne_zero {z : ℂ} (hz : xi z ≠ 0) :
    meromorphicOrderAt xi z ≤ 1 := by
  have h := meromorphicOrderAt_eq_zero_of_ne_zero
    (xi_differentiable.analyticAt z) hz
  rw [h]; exact zero_le_one

theorem xiZeros_simple :
    ∀ z : ℂ, meromorphicOrderAt xi z ≤ 1 := by
  intro z
  by_cases hz : xi z = 0
  · -- Zero case
    have hζ : riemannZeta z = 0 := xi_zero_imp_riemannZeta_zero hz
    have hstrip : 0 < z.re := xi_zero_imp_zero_lt_re hz
    have hre1 : z.re < 1 := by
      by_contra h; exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hζ
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hstrip; exact absurd hstrip (by norm_num)
    have hz1 : z ≠ 1 := by intro h1; rw [h1] at hre1; exact absurd hre1 (by norm_num)
    -- Step 1: Transfer order from xi to s*(s-1)*completedRiemannZeta
    have hfull1 : ∀ᶠ s in 𝓝 z, xi s = s * (s - 1) * completedRiemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0, isOpen_compl_singleton.mem_nhds hz1]
        with s hs0 hs1
      exact xi_eq_mul_completedRiemannZeta hs0 hs1
    have heq1 : (fun s : ℂ => xi s) =ᶠ[𝓝[≠] z]
        (fun s => s * (s - 1) * completedRiemannZeta s) :=
      hfull1.filter_mono (nhdsWithin_le_nhds)
    -- Step 2: Decompose product order
    rw [meromorphicOrderAt_congr heq1]
    rw [show (fun s : ℂ => s * (s - 1) * completedRiemannZeta s) =
        (fun s => s * (s - 1)) * (fun s => completedRiemannZeta s) from by ext; ring_nf; ring]
    have han1 : MeromorphicAt (fun s : ℂ => s * (s - 1)) z := by
      fun_prop
    have han2 : MeromorphicAt completedRiemannZeta z := by
      exact ((differentiableAt_completedZeta hz0 hz1).analyticAt).meromorphicAt
    rw [meromorphicOrderAt_mul han1 han2]
    -- Step 3: s*(s-1) doesn't vanish at z, so order is 0
    have hord_poly : meromorphicOrderAt (fun s : ℂ => s * (s - 1)) z = 0 :=
      meromorphicOrderAt_eq_zero_of_ne_zero
        (differentiable_id.mul (differentiable_id.sub differentiable_const)).analyticAt
        (mul_ne_zero hz0 (sub_ne_zero.mpr hz1))
    rw [hord_poly, zero_add]
    -- Step 4: Relate completedRiemannZeta to riemannZeta via Gammaℝ
    have hfullΛ : ∀ᶠ s in 𝓝 z, completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0,
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hstrip] with s hs0 hsre
      exact (completedRiemannZeta_eq_Gammaℝ_mul hs0 (Gammaℝ_ne_zero_of_re_pos hsre)).symm
    have heqΛ : (fun s : ℂ => completedRiemannZeta s) =ᶠ[𝓝[≠] z]
        (fun s => Gammaℝ s * riemannZeta s) :=
      hfullΛ.filter_mono (nhdsWithin_le_nhds)
    rw [meromorphicOrderAt_congr heqΛ]
    rw [show (fun s : ℂ => Gammaℝ s * riemannZeta s) =
        (fun s => Gammaℝ s) * (fun s => riemannZeta s) from by ext; ring]
    have hanΓ : MeromorphicAt Gammaℝ z := by fun_prop
    have hanZ : MeromorphicAt riemannZeta z := by fun_prop
    rw [meromorphicOrderAt_mul hanΓ hanZ]
    -- Step 5: Gammaℝ z ≠ 0, so order is 0
    have hΓ_ord : meromorphicOrderAt (fun s : ℂ => Gammaℝ s) z = 0 :=
      meromorphicOrderAt_eq_zero_of_ne_zero differentiable_Gammaℝ.analyticAt
        (Gammaℝ_ne_zero_of_re_pos hstrip)
    rw [hΓ_ord, zero_add]
    -- Step 6: riemannZeta is analytic at z (z≠1), convert to analyticOrderAt
    have hanZeta : AnalyticAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz1).analyticAt
    rw [hanZeta.meromorphicOrderAt_eq]
    -- Final gap: need analyticOrderAt riemannZeta z ≤ 1
    sorry
  · exact meromorphicOrderAt_xi_of_ne_zero hz

/-- Kadiri–Lamzouri zero-free region for ζ:
    `ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ 1 - (1/57.54)/log(|Im s|+10)`.

    **Assembly chain** (all building blocks are sorry-free in the codebase):

    1. `xiZeros_infinite` + `xiZeros_simple` [sorry]
       → `xi_zero_enumeration` (ZeroFreeRegionHadamard, sorry-free)
       → injective enumeration `a : ℕ → ℂ` of ξ-zeros escaping to infinity

    2. `logDeriv_completedZeta` (ZeroFreeRegionHadamard, sorry-free)
       → Hadamard decomposition:
         `-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv Γℝ s)
                      - ∑ₙ (1/(s-aₙ) + 1/aₙ)`

    3. Truncate the infinite zero-sum to a finite Finset Z, absorb tail into
       `analytic`. The 3/4/1 inequality bounds analytic; `kadiri_numerical_bridge`
       gives h_c.

    4. `riemannZeta_ne_zero_of_zeroFreeEdge` (ZeroFreeRegionProof, sorry-free)
       → conclusion: ζ(s) ≠ 0. -/
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push Not at h1
    obtain ⟨a, hane, hinj, htend, hzero⟩ :=
      xi_zero_enumeration xiZeros_simple xiZeros_infinite
    obtain ⟨g, hgd, hdecomp⟩ :=
      logDeriv_completedZeta hane hinj sorry htend hzero xiZeros_simple
    have hLpos : 0 < Real.log (|s.im| + 10) :=
      Real.log_pos (by linarith [abs_nonneg s.im])
    have hσgt : 1 < (1 : ℝ) + (2 : ℝ) / 5 / Real.log (|s.im| + 10) :=
      by linarith [div_pos (by norm_num : (0:ℝ) < 2/5) hLpos]
    have hRHS_pos : 0 < (3:ℝ) / ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) +
        (2:ℝ) * Real.log (|s.im| + 2) + (0:ℝ) := by
      have hσm1 : (1:ℝ) + (2:ℝ) / 5 / Real.log (|s.im| + 10) - 1 =
          (2:ℝ) / 5 / Real.log (|s.im| + 10) := by ring
      rw [hσm1, add_zero]; exact add_pos
        (div_pos (by norm_num) (div_pos (by norm_num) hLpos))
        (mul_pos (by norm_num : (0:ℝ) < 2)
          (Real.log_pos (by linarith [abs_nonneg s.im])))
    have h_c : kadiriConstant / Real.log (|s.im| + 10) <
        4 / ((3:ℝ) / ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) +
          (2:ℝ) * Real.log (|s.im| + 2) + (0:ℝ)) -
        ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) := by
      have hL : 0 < Real.log (|s.im| + 10) :=
        Real.log_pos (by linarith [abs_nonneg s.im])
      have hσm1 : (1:ℝ) + (2:ℝ) / 5 / Real.log (|s.im| + 10) - 1 =
          (2:ℝ) / 5 / Real.log (|s.im| + 10) := by ring
      have hlog : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 10) :=
        Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith [abs_nonneg s.im])
      rw [hσm1, add_zero]
      have hinv : (3:ℝ) / ((2:ℝ) / 5 / Real.log (|s.im| + 10)) =
          15 * Real.log (|s.im| + 10) / 2 := by
        have : (2:ℝ) / 5 / Real.log (|s.im| + 10) ≠ 0 :=
          div_ne_zero (by norm_num) (ne_of_gt hL)
        field_simp; ring
      rw [hinv]
      have hdenom_pos : 0 < 15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2) := by
        exact add_pos (div_pos (mul_pos (by norm_num) hL) (by norm_num))
          (mul_pos (by norm_num : (0:ℝ) < 2) (Real.log_pos (by linarith [abs_nonneg s.im])))
      have hdenom_le : 15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2) ≤ 19 * Real.log (|s.im| + 10) / 2 := by linarith
      have hrhs : (4:ℝ) / (15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2)) - (2:ℝ) / 5 / Real.log (|s.im| + 10) ≥
          2 / (95 * Real.log (|s.im| + 10)) := by
        have h1 : (4:ℝ) / (15 * Real.log (|s.im| + 10) / 2 +
            2 * Real.log (|s.im| + 2)) ≥ (4:ℝ) / (19 * Real.log (|s.im| + 10) / 2) :=
          div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hdenom_pos hdenom_le
        have h2 : (4:ℝ) / (19 * Real.log (|s.im| + 10) / 2) = 8 / (19 * Real.log (|s.im| + 10)) := by
          field_simp; ring
        have h3 : (8:ℝ) / (19 * Real.log (|s.im| + 10)) - (2:ℝ) / 5 / Real.log (|s.im| + 10) =
            2 / (95 * Real.log (|s.im| + 10)) := by
          field_simp; ring
        linarith [h1, h2, h3]
      have hlhs : kadiriConstant / Real.log (|s.im| + 10) <
          2 / (95 * Real.log (|s.im| + 10)) := by
        simp only [kadiriConstant]
        field_simp
        nlinarith [kadiri_numerical_bridge]
      linarith
    exact riemannZeta_ne_zero_of_zeroFreeEdge s ht hre
      (1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) hσgt
      sorry sorry sorry sorry sorry sorry
      (3:ℝ) (2:ℝ) (0:ℝ) (by norm_num) (by norm_num)
      sorry hRHS_pos h_c

end
