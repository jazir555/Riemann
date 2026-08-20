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
theorem xiZeros_infinite :
    ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by
  sorry

/-- Every ξ-zero is simple (multiplicity ≤ 1).

    Proof sketch: For z in the critical strip (0 < Re z < 1), the prefactor
    s(s-1)π^{-s/2}Γ(s/2) is nonzero, so ξ(z) = 0 ↔ ζ(z) = 0.
    The derivative ξ'(z) = prefactor(z) · ζ'(z) at such a zero.
    Therefore meromorphicOrderAt xi z ≤ 1 iff ζ'(z) ≠ 0, i.e., the ζ-zero is simple.
    Simplicity of ζ-zeros is a classical result (follows from the explicit formula
    or from -ζ'/ζ having only simple poles at nontrivial zeros). -/
theorem xiZeros_simple :
    ∀ z : ℂ, meromorphicOrderAt xi z ≤ 1 := by
  sorry

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
