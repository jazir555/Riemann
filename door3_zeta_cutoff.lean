import zeta_rigorous
import central_cover_assembly
import door3_tail_eta_upper

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

/-! The unconditional eta-pair majorant also supplies a finite upper wall at
the cutoff itself.  This is used by derivative-side suppliers; it carries no
numerical or analytic hypothesis beyond the defining cutoff coordinates. -/

theorem zeta_cutoff_upper_125 : ‖riemannZeta sCut‖ ≤ (125 : ℝ) := by
  apply Door3TailEtaUpper.zeta_upper_tail_quarter
  · rw [sCut_re]
    norm_num
  · rw [sCut_re]
  · rw [sCut_im]
    norm_num

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

/-! A sharper cutoff factor is needed for the named `7/5` zeta floor.  The
    preceding proof deliberately stopped at `1`; retaining the exact
    real-part identity and the same quadratic cosine enclosure gives a
    rational bound below `9/10`. -/

theorem eta_factor_cutoff_upper_nine_tenths :
    ‖1 - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ ≤ (9 / 10 : ℝ) := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by rw [hlog]; rfl
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
  have hcos : (789 / 1000 : ℝ) ≤ Real.cos (10 * Real.log 2) := by
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
    have hc := Real.one_sub_sq_div_two_le_cos
      (x := 10 * Real.log 2 - 2 * Real.pi)
    have hcosd : (789 / 1000 : ℝ) ≤
        Real.cos (10 * Real.log 2 - 2 * Real.pi) := by
      nlinarith [hc, hsq]
    rw [Real.cos_sub_two_pi] at hcosd
    exact hcosd
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hprod : (1095 / 1000 : ℝ) ≤
      Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    have hc0 : 0 ≤ Real.cos (10 * Real.log 2) := by linarith
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hmul := mul_le_mul hsqrt hcos (by norm_num) (by linarith)
    nlinarith [hmul]
  have hsq : ‖(1 : ℂ) - q‖ ^ 2 ≤ (81 / 100 : ℝ) := by
    rw [hsqid, hqnorm, hqre]
    have hsqroot : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith [hprod, hsqroot]
  have hnonneg : 0 ≤ ‖(1 : ℂ) - q‖ := norm_nonneg _
  change ‖(1 : ℂ) - q‖ ≤ (9 / 10 : ℝ)
  nlinarith

/-! The same phase enclosure gives a quantitative lower wall for the
conversion factor.  It is useful when a cutoff certificate is phrased as an
absolute eta sum rather than as a zeta lower bound. -/

theorem eta_factor_cutoff_lower_nine_hundredths :
    (9 / 100 : ℝ) ≤ ‖1 - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by rw [hlog]; rfl
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
  have hcos : (789 / 1000 : ℝ) ≤ Real.cos (10 * Real.log 2) := by
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
    have hc := Real.one_sub_sq_div_two_le_cos
      (x := 10 * Real.log 2 - 2 * Real.pi)
    have hcosd : (789 / 1000 : ℝ) ≤
        Real.cos (10 * Real.log 2 - 2 * Real.pi) := by
      nlinarith [hc, hsq]
    rw [Real.cos_sub_two_pi] at hcosd
    exact hcosd
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hqre_lo : (1095 / 1000 : ℝ) ≤ q.re := by
    rw [hqre]
    have hc0 : 0 ≤ Real.cos (10 * Real.log 2) := by linarith
    have hmul := mul_le_mul hsqrt hcos (by norm_num) (by linarith)
    nlinarith [hmul]
  have hreal : (9 / 100 : ℝ) ≤ |(1 - q).re| := by
    have hre : (1 - q).re = 1 - q.re := by simp
    rw [hre, abs_of_nonpos]
    · linarith
    · linarith
  exact le_trans hreal (Complex.abs_re_le_norm (1 - q))

theorem eta_factor_cutoff_ne_zero :
    (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - sCut) ≠ 0 := by
  intro h
  have hz : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - sCut)‖ = 0 := by rw [h]; simp
  have hlow := eta_factor_cutoff_lower_nine_hundredths
  rw [hz] at hlow
  norm_num at hlow

theorem zeta_cutoff_lower_of_certificate_nine_tenths
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ)
    (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hgap : rtail < slow) :
    (slow - rtail) / (9 / 10 : ℝ) ≤ ‖riemannZeta sCut‖ := by
  have h := zeta_lower_of_Sn_tail_factor sCut_pos sCut_re_ne_one N S hSdef
    slow hSlow rtail hTail (9 / 10) (by norm_num)
      eta_factor_cutoff_upper_nine_tenths
  exact h

theorem cutR10_zetaRemainder_of_certificate_nine_tenths
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm sCut k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm sCut m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) * (9 / 10 : ℝ) + rtail ≤ slow) :
    Door3CutR10Center.cutR10_zetaRemainder := by
  unfold Door3CutR10Center.cutR10_zetaRemainder
  have h := zeta_cutoff_lower_of_certificate_nine_tenths N S hSdef
    slow rtail hSlow hTail (by linarith)
  have hbound : (7 / 5 : ℝ) ≤ (slow - rtail) / (9 / 10 : ℝ) := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hscut : sCut = (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.CutR10.center := by
    rw [Door3CutR10Center.cutR10_s_eq]
    simp [sCut]
  rw [hscut] at h
  exact hbound.trans h

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

/- A Cauchy supplier interface for the remaining cutoff derivative leaf.  A
   single entire-function sup enclosure on the center ball of radius
   `CutR10.radius + 1` gives the named `M = 0.04` derivative remainder. -/
theorem cutR10_derivRemainder_of_closedBall_sup
    (hC : ∀ z ∈ Metric.closedBall CentralCoverAssembly.CutR10.center
      (CentralCoverAssembly.CutR10.radius + 1),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    Door3CutR10Center.cutR10_derivRemainder 0.04 := by
  unfold Door3CutR10Center.cutR10_derivRemainder
  have hstrip : ∀ w, CentralCoverAssembly.CutR10.mem w →
      -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
    intro w hw
    have hlo : CentralCoverAssembly.CutR10.y0 ≤ w.im := hw.2.2.1
    have hhi : w.im ≤ CentralCoverAssembly.CutR10.y1 := hw.2.2.2
    rw [CentralCoverAssembly.CutR10_y0] at hlo
    rw [CentralCoverAssembly.CutR10_y1] at hhi
    constructor <;> linarith
  have hD := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.CutR10 1 (0.04 : ℝ) (by norm_num) hstrip hC
  intro w hw
  have hle := hD w hw
  norm_num at hle ⊢
  exact hle

end Door3ZetaCutoff

#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate
#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate_one
#print axioms Door3ZetaCutoff.zeta_cutoff_upper_125
#print axioms Door3ZetaCutoff.eta_factor_cutoff_upper_nine_tenths
#print axioms Door3ZetaCutoff.eta_factor_cutoff_lower_nine_hundredths
#print axioms Door3ZetaCutoff.zeta_cutoff_lower_of_certificate_nine_tenths
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_nine_tenths
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate
#print axioms Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_one
#print axioms Door3ZetaCutoff.cutR10_derivRemainder_of_closedBall_sup

#print axioms Door3ZetaCutoff.eta_factor_cutoff_ne_zero

/-!
## Door-3 remainder 2 final step: real-axis minorant at `0` + `BottomStripObligations` bridge

Unconditional real-axis input (reproved here from the transitively visible
`D3` chain — `riemannZeta_eq_inv_sub_add` (Mathlib), Euler–Maclaurin
`riemannZeta₀_eq_one_sub_mul_termTSum_on` (via `riemann_hypothesis`),
`Real.Gamma_strictAntiOn_Ioc` (Mathlib) — since `door3_real_center_bounds`
is outside this file's import closure): at `s = 1 / 2`,
`1 ≤ ‖ζ(1/2)‖` and `1 / 16 ≤ ‖classicalXiPrefactor(1/2)‖`, hence
`1 / 16 ≤ ‖classicalXi(1/2)‖`. Transferred along
`xiShifted 0 = classicalXi(1/2)` and strip agreement
`xiShifted_eq_entire_on_strip` at `0`, this gives the explicit single-point
minorant `(0.025 : ℝ) ≤ ‖xiShiftedEntire 0‖` (`1 / 16 = 0.0625`).

Conditional bridge (mirrors `door3_deriv_certs.lean` shapes without importing
it): the local Cauchy rule plus the `0.01`-segment estimate turn a uniform
base minorant `hb : (0.025 : ℝ) ≤ ‖xiShiftedEntire (x : ℂ)‖` and a ball sup
`hB` on `closedBall (bsCenter x) 1` with `B / (1 / 2) ≤ 1` into
`CentralCoverAssembly.StripBaseBounds x 0.025 1` for every
`-10 < x < 10`, hence `CentralCoverAssembly.BottomStripObligations`, hence
`bottom_strip_covered`. The local center `bsCenter` is definitionally the
`stripSegCenter` point expression (`(x : ℂ) + I * 0.01`).

Residual (exact): the uniform minorant `hb` for `-10 < x < 10` (critical-line
`ξ` lower bound, absent from Mathlib) and the tube sup `hB`; the point
`x = 0` instance fires unconditionally modulo `hB` at `0`.
-/

namespace Door3ZetaCutoff

/-- Zeta lower bound at `s = 1 / 2`: `1 ≤ ‖ζ(1/2)‖` (mirror of
`D3_real_zeta_norm_lower` at `s = 1 / 2`). -/
theorem zeta_half_norm_lower_one :
    (1 : ℝ) ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ := by
  have h12 : (1 / 2 : ℝ) ≠ 1 := by norm_num
  have hsne : ((((1 / 2 : ℝ))) : ℂ) ≠ 1 := by exact_mod_cast h12
  have hz := riemannZeta_eq_inv_sub_add (s := ((((1 / 2 : ℝ))) : ℂ)) hsne
  have h0 := riemannZeta₀_eq_one_sub_mul_termTSum_on (show (0 : ℝ) < 1 / 2 by norm_num)
  have ht : (0 : ℝ) ≤ ZetaAsymptotics.termTSum (1 / 2 : ℝ) :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) (1 / 2 : ℝ))
  have hz0 : (riemannZeta₀ ((((1 / 2 : ℝ))) : ℂ)).re ≤ 1 := by
    rw [h0]
    have hprod : (0 : ℝ) ≤ (1 / 2 : ℝ) * ZetaAsymptotics.termTSum (1 / 2 : ℝ) :=
      mul_nonneg (by norm_num) ht
    linarith
  have heq : ((((1 / 2 : ℝ))) : ℂ) - 1 = (((-1 / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hinv : ((((((1 / 2 : ℝ))) : ℂ) - 1)⁻¹).re = (-2 : ℝ) := by
    rw [heq, ← Complex.ofReal_inv, Complex.ofReal_re]
    norm_num
  have hre : (riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re ≤ -1 := by
    rw [hz, Complex.add_re, hinv]
    linarith
  have hneg : (riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re < 0 := by linarith
  calc (1 : ℝ) ≤ |(riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re| := by
        rw [abs_of_neg hneg]
        linarith
    _ ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ := Complex.abs_re_le_norm _

/-- Prefactor lower bound at `s = 1 / 2`: `1 / 16 ≤ ‖prefactor‖` (mirror of
`D3_real_prefactor_norm_lower` at `s = 1 / 2`). -/
theorem prefactor_half_norm_lower :
    (1 / 16 : ℝ) ≤ ‖classicalXiPrefactor ((((1 / 2 : ℝ))) : ℂ)‖ := by
  have hcast : (1 / 2 : ℂ) = ((((1 / 2 : ℝ))) : ℂ) := by simp
  have hsabs : ‖((((1 / 2 : ℝ))) : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hsm1 : ‖((((1 / 2 : ℝ))) : ℂ) - 1‖ = (1 / 2 : ℝ) := by
    have heq : ((((1 / 2 : ℝ))) : ℂ) - 1 = (((-1 / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
    norm_num
  have hcpow : (1 / 2 : ℝ) ≤ ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) / 2))‖ := by
    have heq : (-(((1 / 2 : ℝ) : ℂ) / 2)) = (((-1 / 4 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [heq, ← Complex.ofReal_cpow (x := Real.pi) (y := (-1 / 4 : ℝ)) (le_of_lt Real.pi_pos),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _)]
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hexp : (-(1 / 2 : ℝ)) ≤ (-(1 / 4 : ℝ)) := by norm_num
    have hp : Real.pi ^ (-(1 / 2 : ℝ)) ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hpi hexp
    have hsqrt : Real.sqrt Real.pi < 2 := by
      nlinarith [Real.sq_sqrt (le_of_lt Real.pi_pos)]
    have hinv : (1 / 2 : ℝ) < Real.pi ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt Real.pi_pos), ← Real.sqrt_eq_rpow, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 Real.pi_pos) hsqrt
    linarith
  have hgamma : (1 : ℝ) ≤ ‖Complex.Gamma (((((1 / 2 : ℝ))) : ℂ) / 2)‖ := by
    have heq : (((((1 / 2 : ℝ))) : ℂ) / 2) = ((((1 / 4 : ℝ))) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4))]
    have hx : (1 / 4 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by constructor <;> norm_num
    have hy : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
    have h := Real.Gamma_strictAntiOn_Ioc.antitoneOn hx hy (by norm_num : (1 / 4 : ℝ) ≤ 1)
    rw [Real.Gamma_one] at h
    exact h
  unfold classicalXiPrefactor
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcast, hsabs, hsm1]
  have h1 : (1 / 16 : ℝ) ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) *
      ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) / 2))‖ := by
    nlinarith [hcpow]
  have h2 : (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) *
      ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) / 2))‖ ≤
      (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) *
      ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) / 2))‖ *
      ‖Complex.Gamma (((((1 / 2 : ℝ))) : ℂ) / 2)‖ :=
    le_mul_of_one_le_right (by positivity) hgamma
  exact le_trans h1 h2

/-- Classical `ξ` lower bound at `s = 1 / 2`: `1 / 16 ≤ ‖ξ(1/2)‖`. -/
theorem classicalXi_half_norm_lower :
    (1 / 16 : ℝ) ≤ ‖classicalXi ((((1 / 2 : ℝ))) : ℂ)‖ := by
  have hz := zeta_half_norm_lower_one
  have hp := prefactor_half_norm_lower
  have hmul : (1 : ℝ) * (1 / 16 : ℝ) ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ *
      ‖classicalXiPrefactor ((((1 / 2 : ℝ))) : ℂ)‖ :=
    mul_le_mul hz hp (by norm_num) (norm_nonneg _)
  rw [one_mul] at hmul
  have hdecomp : classicalXi ((((1 / 2 : ℝ))) : ℂ) =
      classicalXiPrefactor ((((1 / 2 : ℝ))) : ℂ) * zeta ((((1 / 2 : ℝ))) : ℂ) := rfl
  rw [hdecomp, norm_mul]
  have hzeta : zeta ((((1 / 2 : ℝ))) : ℂ) = riemannZeta ((((1 / 2 : ℝ))) : ℂ) := rfl
  rw [hzeta]
  exact le_trans hmul (le_of_eq (mul_comm _ _))

/-- Single-point real-axis minorant: `(0.025 : ℝ) ≤ ‖xiShiftedEntire 0‖`. -/
theorem xiShiftedEntire_zero_minorant :
    (0.025 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire (0 : ℂ)‖ := by
  have him0 : (0 : ℂ).im = 0 := rfl
  have hshift : (1 / 2 : ℂ) + Complex.I * (0 : ℂ) = ((((1 / 2 : ℝ))) : ℂ) := by
    rw [mul_zero, add_zero]
    simp
  have hxi0 : xiShifted (0 : ℂ) = classicalXi ((((1 / 2 : ℝ))) : ℂ) := by
    unfold xiShifted
    rw [hshift]
  have hagree : xiShifted (0 : ℂ) = CentralCoverAssembly.xiShiftedEntire (0 : ℂ) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip (0 : ℂ)
      (by rw [him0]; norm_num) (by rw [him0]; norm_num)
  have h16 := classicalXi_half_norm_lower
  rw [← hagree, hxi0]
  exact le_trans (by norm_num : (0.025 : ℝ) ≤ 1 / 16) h16

/-- Positivity at the origin. -/
theorem xiShiftedEntire_zero_pos :
    (0 : ℝ) < ‖CentralCoverAssembly.xiShiftedEntire (0 : ℂ)‖ :=
  lt_of_lt_of_le (by norm_num) xiShiftedEntire_zero_minorant

/-- Midpoint center of the `0 ≤ y ≤ 0.02` segment at fixed `x`
(same point expression as `stripSegCenter`). -/
noncomputable def bsCenter (x : ℝ) : ℂ := (x : ℂ) + Complex.I * (((0.01 : ℝ)) : ℂ)

/-- Segment displacement factors through `I`. -/
theorem bsPoint_sub_center_eq (x : ℝ) (y : ℝ) :
    ((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)) - bsCenter x =
      Complex.I * (((((y - 0.01 : ℝ))) : ℂ)) := by
  unfold bsCenter
  have hfold : ((((y : ℝ))) : ℂ) - ((((0.01 : ℝ))) : ℂ) = (((((y - 0.01 : ℝ))) : ℂ)) := by
    push_cast
    ring
  rw [← hfold]
  ring

/-- Every segment point is within `0.01` of the midpoint center. -/
theorem bsPoint_dist_center_le (x : ℝ) (y : ℝ) (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ (0.02 : ℝ)) :
    ‖((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)) - bsCenter x‖ ≤ (0.01 : ℝ) := by
  have heq := bsPoint_sub_center_eq x y
  have hnorm : ‖((((y - 0.01 : ℝ))) : ℂ)‖ = |y - 0.01| := RCLike.norm_ofReal _
  have habs : |y - 0.01| ≤ (0.01 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc ‖((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)) - bsCenter x‖
      = ‖Complex.I * (((((y - 0.01 : ℝ))) : ℂ))‖ := by rw [heq]
    _ = ‖((((y - 0.01 : ℝ))) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ = |y - 0.01| := hnorm
    _ ≤ 0.01 := habs

/-- Local Cauchy rule: sup `B` on `closedBall c R` gives `‖deriv f w‖ ≤ B / r`. -/
theorem bs_deriv_bound_of_ballSup {f : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hd : DiffContOnCl ℂ f (Metric.ball c R))
    (hB : ∀ (z : ℂ), z ∈ Metric.closedBall c R → ‖f z‖ ≤ B)
    {w : ℂ} {r : ℝ} (hr : (0 : ℝ) < r) (hw : ‖w - c‖ + r ≤ R) :
    ‖deriv f w‖ ≤ B / r := by
  have hball : Metric.ball w r ⊆ Metric.ball c R := by
    intro z hz
    have hzw : ‖z - w‖ < r := by rw [← dist_eq_norm]; exact hz
    show dist z c < R
    calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
      _ = ‖z - w‖ + ‖w - c‖ := by rw [dist_eq_norm, dist_eq_norm]
      _ < r + ‖w - c‖ := add_lt_add_of_lt_of_le hzw le_rfl
      _ = ‖w - c‖ + r := add_comm _ _
      _ ≤ R := hw
  have hsph : Metric.sphere w r ⊆ Metric.closedBall c R := by
    intro z hz
    have h1 : ‖z - w‖ = r := by rw [← dist_eq_norm]; exact hz
    show dist z c ≤ R
    calc dist z c = ‖(z - w) + (w - c)‖ := by rw [dist_eq_norm]; congr 1; abel
      _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
      _ = r + ‖w - c‖ := by rw [h1]
      _ = ‖w - c‖ + r := add_comm _ _
      _ ≤ R := hw
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd.mono hball)
    (fun z hz => hB z (hsph hz))

/-- Segment deriv bound from the ball sup (`B / (1 / 2) ≤ M1`, margin `r = 1 / 2`). -/
theorem bs_strip_deriv_of_ballSup (x : ℝ) {B M1 : ℝ}
    (hd : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire (Metric.ball (bsCenter x) 1))
    (hB : ∀ (z : ℂ), z ∈ Metric.closedBall (bsCenter x) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ M1)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))‖ ≤ M1 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hdist : ‖((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)) - bsCenter x‖ ≤ (0.01 : ℝ) :=
    bsPoint_dist_center_le x y hy0 hy1
  have hw : ‖((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)) - bsCenter x‖ + (1 / 2 : ℝ) ≤ 1 := by
    linarith
  have h := bs_deriv_bound_of_ballSup hd hB (show (0 : ℝ) < 1 / 2 by norm_num) hw
  exact le_trans h hM

/-- Per-`x` shape instance at `(0.025, 1)` from the explicit base/deriv inputs. -/
theorem bs_stripBaseBounds_of_explicit (x : ℝ) {B : ℝ}
    (hb : (0.025 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire (x : ℂ)‖)
    (hB : ∀ (z : ℂ), z ∈ Metric.closedBall (bsCenter x) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ)) :
    CentralCoverAssembly.StripBaseBounds x (0.025 : ℝ) (1 : ℝ) := by
  refine ⟨by norm_num, by norm_num, hb, ?_, by norm_num⟩
  intro y hy
  exact bs_strip_deriv_of_ballSup x
    CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl hB hM y hy

/-- The `x = 0` bounds fire from the unconditional minorant modulo the ball sup. -/
theorem bs_stripBaseBounds_at_zero_of_ballSup {B : ℝ}
    (hB0 : ∀ (z : ℂ), z ∈ Metric.closedBall (bsCenter 0) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ)) :
    CentralCoverAssembly.StripBaseBounds 0 (0.025 : ℝ) (1 : ℝ) :=
  bs_stripBaseBounds_of_explicit 0 xiShiftedEntire_zero_minorant hB0 hM

/-- Uniform bridge: base minorant plus tube sup gives `BottomStripObligations`. -/
theorem bottomStrip_obligations_of_uniform_bounds {B : ℝ}
    (hb : ∀ (x : ℝ), -10 < x → x < 10 →
      (0.025 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire (x : ℂ)‖)
    (hB : ∀ (x : ℝ), -10 < x → x < 10 → ∀ (z : ℂ), z ∈ Metric.closedBall (bsCenter x) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ)) :
    CentralCoverAssembly.BottomStripObligations := by
  intro x hx_lo hx_hi
  exact ⟨(0.025 : ℝ), (1 : ℝ), bs_stripBaseBounds_of_explicit x (hb x hx_lo hx_hi)
    (hB x hx_lo hx_hi) hM⟩

/-- Cover corollary: the uniform inputs fence `xiShifted z ≠ 0` on the strip. -/
theorem bottomStrip_covered_of_uniform_bounds {B : ℝ}
    (hb : ∀ (x : ℝ), -10 < x → x < 10 →
      (0.025 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire (x : ℂ)‖)
    (hB : ∀ (x : ℝ), -10 < x → x < 10 → ∀ (z : ℂ), z ∈ Metric.closedBall (bsCenter x) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ))
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.01) :
    xiShifted z ≠ 0 :=
  CentralCoverAssembly.bottom_strip_covered
    (bottomStrip_obligations_of_uniform_bounds hb hB hM) hx_lo hx_hi hy_pos hy_le

end Door3ZetaCutoff

#print axioms Door3ZetaCutoff.zeta_half_norm_lower_one
#print axioms Door3ZetaCutoff.prefactor_half_norm_lower
#print axioms Door3ZetaCutoff.classicalXi_half_norm_lower
#print axioms Door3ZetaCutoff.xiShiftedEntire_zero_minorant
#print axioms Door3ZetaCutoff.xiShiftedEntire_zero_pos
#print axioms Door3ZetaCutoff.bsPoint_sub_center_eq
#print axioms Door3ZetaCutoff.bsPoint_dist_center_le
#print axioms Door3ZetaCutoff.bs_deriv_bound_of_ballSup
#print axioms Door3ZetaCutoff.bs_strip_deriv_of_ballSup
#print axioms Door3ZetaCutoff.bs_stripBaseBounds_of_explicit
#print axioms Door3ZetaCutoff.bs_stripBaseBounds_at_zero_of_ballSup
#print axioms Door3ZetaCutoff.bottomStrip_obligations_of_uniform_bounds
#print axioms Door3ZetaCutoff.bottomStrip_covered_of_uniform_bounds
