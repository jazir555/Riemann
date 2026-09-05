import zeta_rigorous
import central_cover_assembly

/-! # CutR10 zeta lower-bound adapter

This file specializes the already-proved eta-pair continuation and lower-bound
engine to `s = 1/2 + 10 I`. It isolates the remaining numerical task as a
finite partial-sum/tail certificate.
-/

open scoped BigOperators

namespace Door3ZetaCutoff

noncomputable def sCut : ℂ := (1 / 2 : ℂ) + 10 * Complex.I

theorem sCut_re : sCut.re = (1 / 2 : ℝ) := by
  simp [sCut]

theorem sCut_im : sCut.im = (10 : ℝ) := by
  simp [sCut]

theorem sCut_pos : 0 < sCut.re := by rw [sCut_re]; norm_num

theorem sCut_re_ne_one : sCut.re ≠ 1 := by rw [sCut_re]; norm_num

/-- The eta conversion factor at the cutoff has a simple universal upper bound. -/
theorem eta_factor_cutoff_upper :
    ‖1 - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ ≤ (5 / 2 : ℝ) := by
  have hre : ((1 : ℂ) - sCut).re = (1 / 2 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, sCut_re]
    norm_num
  have hp : ‖(2 : ℂ) ^ ((1 : ℂ) - sCut)‖ ≤ (3 / 2 : ℝ) := by
    rw [two_cpow_norm, hre]
    have h2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    convert h2 using 1 <;> rw [← Real.sqrt_eq_rpow]
  calc
    ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ ≤
        ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - sCut)‖ := norm_sub_le _ _
    _ ≤ 5 / 2 := by rw [norm_one]; linarith

theorem zeta_cutoff_lower_of_certificate
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ)
    (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hgap : rtail < slow) :
    (slow - rtail) / (5 / 2 : ℝ) ≤ ‖riemannZeta sCut‖ := by
  have h := zeta_lower_of_Sn_tail_factor sCut_pos sCut_re_ne_one N S hSdef
    slow hSlow rtail hTail (5 / 2) (by norm_num)
      eta_factor_cutoff_upper
  exact h

theorem cutR10_zetaRemainder_of_certificate
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) * (5 / 2 : ℝ) + rtail ≤ slow) :
    Door3CutR10Center.cutR10_zetaRemainder := by
  unfold Door3CutR10Center.cutR10_zetaRemainder
  have h := zeta_cutoff_lower_of_certificate N S hSdef
    slow rtail hSlow hTail (by linarith)
  have hbound : (7 / 5 : ℝ) ≤ (slow - rtail) / (5 / 2 : ℝ) := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hscut : sCut = (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.CutR10.center := by
    rw [Door3CutR10Center.cutR10_s_eq]
    simp [sCut]
  rw [hscut] at h
  exact hbound.trans h

end Door3ZetaCutoff

#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate
