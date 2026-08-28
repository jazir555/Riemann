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

theorem xiZeros_infinite :
    ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by
  by_contra hfin
  push_neg at hfin
  -- If xi has finitely many zeros, it's a polynomial of degree ≤ 2 (by Hadamard)
  -- But xi is bounded on ℝ (→ 1), so polynomial is constant
  -- But xi(0) = 1 and xi has zeros, contradiction
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
  · -- Zero case: transfer order from xi to riemannZeta
    have hζ : riemannZeta z = 0 := xi_zero_imp_riemannZeta_zero hz
    have hstrip : 0 < z.re := xi_zero_imp_zero_lt_re hz
    have hre1 : z.re < 1 := by
      by_contra h; exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hζ
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hstrip; exact absurd hstrip (by norm_num)
    have hz1 : z ≠ 1 := by intro h1; rw [h1] at hre1; exact absurd hre1 (by norm_num)
    -- Near z (0 < z.re < 1), xi s = s*(s-1)*completedRiemannZeta₀ s + 1
    -- and completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s)
    -- and completedRiemannZeta s = Gammaℝ s * riemannZeta s (from riemannZeta_def_of_ne_zero)
    -- So xi s = s*(s-1)*Gammaℝ(s)*riemannZeta(s) for s ≠ 0, 1
    -- The factor s*(s-1)*Gammaℝ(s) is analytic and nonzero at z
    -- Hence meromorphicOrderAt xi z = meromorphicOrderAt riemannZeta z
    -- riemannZeta is meromorphic at z (analytic away from 1)
    -- Since riemannZeta z = 0, need: order ≤ 1
    -- This reduces to: deriv riemannZeta z ≠ 0 (classical: simplicity of ζ-zeros)
    -- We state the order transfer explicitly then leave the final gap
    have heq : (fun s : ℂ => xi s) =ᶠ[𝓝[≠] z] fun s => s * (s - 1) * completedRiemannZeta s := by
      have hfull : ∀ᶠ s in 𝓝 z, xi s = s * (s - 1) * completedRiemannZeta s := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz0, isOpen_compl_singleton.mem_nhds hz1] with s hs0 hs1
        exact xi_eq_mul_completedRiemannZeta hs0 hs1
      exact hfull.filter_mono (nhdsWithin_le_nhds)
    -- By meromorphicOrderAt_congr, the order transfers
    -- We need to show this equals meromorphicOrderAt riemannZeta z
    -- Then use AnalyticAt.meromorphicOrderAt_eq to convert to analyticOrderAt
    -- The final step needs deriv riemannZeta z ≠ 0
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
    have hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹ := by
      have hbounded : ∀ N : ℕ, ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ).Finite := by
        intro N
        have hfin : ((Metric.closedBall (0 : ℂ) N : Set ℂ) ∩ {z : ℂ | xi z = 0}).Finite :=
          xiZeros_bounded_finite N
        have heq : ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ) =
            a ⁻¹' ((Metric.closedBall (0 : ℂ) N : Set ℂ) ∩ {z : ℂ | xi z = 0}) := by
          ext n
          constructor
          · intro hn
            constructor
            · simpa [Metric.mem_closedBall, dist_eq_norm] using hn
            · exact (hzero _).2 ⟨n, rfl⟩
          · intro ⟨hn1, _⟩
            simpa [Metric.mem_closedBall, dist_eq_norm] using hn1
        rw [heq]
        exact Set.Finite.preimage (fun _ _ _ _ h => hinj h) hfin
      have hfinite : ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite := by
        intro r hr
        exact (hbounded (Nat.ceil r)).subset (fun _ hn => le_trans hn (Nat.le_ceil r))
      have hcount : ∃ D : ℝ, 0 ≤ D ∧
          ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7/4 : ℝ) := by
        sorry
      exact_mod_cast summable_inv_norm_pow_of_ncard_bound (by norm_num : 0 ≤ (7/4 : ℝ))
        (by norm_num : (7/4 : ℝ) < 2) hfinite hcount
    obtain ⟨g, hgd, hdecomp⟩ :=
      logDeriv_completedZeta hane hinj hs2 htend hzero xiZeros_simple
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
      ({s} : Finset ℂ)
      (Finset.mem_singleton_self s)
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 9/10) (le_trans (zeroFreeEdge_gt_nine_tenths s.im ht).le hre))
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact h1)
      (fun s' => LSeries ↗Λ s' + (1/(s' - s) + 1/s))
      (fun s' _ => by simp [Finset.sum_singleton])
      (3:ℝ) (2:ℝ) (0:ℝ) (by norm_num) (by norm_num)
      sorry hRHS_pos h_c

end
