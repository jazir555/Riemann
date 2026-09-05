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

theorem cutoff_phase_cos_lower :
    (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2) := by
  have hloglo := Real.log_two_gt_d9
  have hloghi := Real.log_two_lt_d9
  have hθlo : (6.931471803 : ℝ) < 10 * Real.log 2 := by linarith
  have hθhi : 10 * Real.log 2 < (6.931471808 : ℝ) := by linarith
  have hπlo := Real.pi_gt_d4
  have hπhi := Real.pi_lt_d4
  have hdlo : (0.6482 : ℝ) < 10 * Real.log 2 - 2 * Real.pi := by linarith
  have hdhi : 10 * Real.log 2 - 2 * Real.pi < (0.6486 : ℝ) := by linarith
  have hsq : (10 * Real.log 2 - 2 * Real.pi) ^ 2 ≤ (0.6486 : ℝ) ^ 2 := by
    have hp : 0 ≤ 10 * Real.log 2 - 2 * Real.pi := by linarith
    nlinarith [sq_nonneg (10 * Real.log 2 - 2 * Real.pi)]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 10 * Real.log 2 - 2 * Real.pi)
  have hbase : (3 / 4 : ℝ) ≤ 1 - (0.6486 : ℝ) ^ 2 / 2 := by norm_num
  have hcosd : (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2 - 2 * Real.pi) := by
    nlinarith [hc, hsq]
  rw [Real.cos_sub_two_pi] at hcosd
  exact hcosd

theorem eta_factor_cutoff_upper_one :
    ‖1 - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ ≤ (1 : ℝ) := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by rw [hlog]; rfl
  have hqre : ((2 : ℂ) ^ ((1 : ℂ) - sCut)).re =
      Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [Complex.exp_re]
    have hargre : (Complex.log (2 : ℂ) * (1 - sCut)).re = Real.log 2 / 2 := by
      rw [Complex.mul_re, hlogre, hlogim]
      simp [sCut]
      ring
    have hargim : (Complex.log (2 : ℂ) * (1 - sCut)).im = -(10 * Real.log 2) := by
      rw [Complex.mul_im, hlogre, hlogim]
      simp [sCut]
      ring
    rw [hargre, hargim]
    have hexp : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      calc
        Real.exp (Real.log 2 / 2) = Real.exp (Real.log 2 * (1 / 2 : ℝ)) := by congr 1 <;> ring
        _ = (2 : ℝ) ^ (1 / 2 : ℝ) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
        _ = Real.sqrt 2 := by rw [← Real.sqrt_eq_rpow]
    rw [hexp]
    rw [Real.cos_neg]
  let q : ℂ := (2 : ℂ) ^ ((1 : ℂ) - sCut)
  have hqre : q.re = Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    dsimp [q]
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [Complex.exp_re]
    have hargre : (Complex.log (2 : ℂ) * (1 - sCut)).re = Real.log 2 / 2 := by
      rw [Complex.mul_re, hlogre, hlogim]
      simp [sCut]
      ring
    have hargim : (Complex.log (2 : ℂ) * (1 - sCut)).im = -(10 * Real.log 2) := by
      rw [Complex.mul_im, hlogre, hlogim]
      simp [sCut]
      ring
    rw [hargre, hargim]
    have hexp : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      calc
        Real.exp (Real.log 2 / 2) = Real.exp (Real.log 2 * (1 / 2 : ℝ)) := by congr 1 <;> ring
        _ = (2 : ℝ) ^ (1 / 2 : ℝ) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
        _ = Real.sqrt 2 := by rw [← Real.sqrt_eq_rpow]
    rw [hexp, Real.cos_neg]
  have hqnorm : ‖q‖ = Real.sqrt 2 := by
    dsimp [q]
    rw [two_cpow_norm]
    have hpow : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by rw [← Real.sqrt_eq_rpow]
    convert hpow using 1 <;> norm_num [sCut]
  have hsqid : ‖(1 : ℂ) - q‖ ^ 2 = 1 + ‖q‖ ^ 2 - 2 * q.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hq]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, zero_sub]
    ring
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hcos := cutoff_phase_cos_lower
  have hprod : (1 : ℝ) ≤ Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (by nlinarith [hcos])]
  have hsq : ‖(1 : ℂ) - q‖ ^ 2 ≤ 1 := by
    rw [hsqid, hqnorm, hqre]
    have hsqroot : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      exact Real.sq_sqrt (by norm_num)
    nlinarith
  have hnonneg : 0 ≤ ‖(1 : ℂ) - q‖ := norm_nonneg _
  nlinarith

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

theorem zeta_cutoff_lower_of_certificate_one
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ)
    (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hgap : rtail < slow) :
    slow - rtail ≤ ‖riemannZeta sCut‖ := by
  have h := zeta_lower_of_Sn_tail_factor sCut_pos sCut_re_ne_one N S hSdef
    slow hSlow rtail hTail 1 (by norm_num) eta_factor_cutoff_upper_one
  simpa using h

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

theorem cutR10_zetaRemainder_of_certificate_one
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow) :
    Door3CutR10Center.cutR10_zetaRemainder := by
  unfold Door3CutR10Center.cutR10_zetaRemainder
  have h := zeta_cutoff_lower_of_certificate_one N S hSdef
    slow rtail hSlow hTail (by linarith)
  have hbound : (7 / 5 : ℝ) ≤ slow - rtail := by linarith
  have hscut : sCut = (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.CutR10.center := by
    rw [Door3CutR10Center.cutR10_s_eq]
    simp [sCut]
  rw [hscut] at h
  exact hbound.trans h

end Door3ZetaCutoff

#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate
#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate_one
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_one
