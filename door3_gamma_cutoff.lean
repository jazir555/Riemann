import door3_gamma_product

/-! # Gamma lower bound at the Door-3 cutoff center

The reflected Gamma factor is bounded by a 128-factor rational certificate.
Euler reflection then gives the required lower bound at `1/4 + 5i`.
-/

open scoped BigOperators

namespace Door3GammaCutoff

theorem real_gamma_three_quarters_le : Real.Gamma (3 / 4) ≤ 4 / 3 := by
  have h := Real.convexOn_Gamma.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (0 : ℝ) ≤ 3 / 4 by norm_num)
    (show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num)
  norm_num [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have hr := Real.Gamma_add_one (s := (3 / 4 : ℝ)) (by norm_num)
  norm_num at hr
  linarith

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem reflected_gamma_product_certificate :
    (16 / 9 : ℝ) * (∏ k ∈ Finset.range 128,
      (((3 / 4 : ℝ) + k) ^ 2 / (((3 / 4 : ℝ) + k) ^ 2 + 25))) ≤
        (9 / 5000 : ℝ) ^ 2 := by
  norm_num [Finset.prod_range_succ]

/-- Reflected factor for `1/4 + 5i`, using only exact arithmetic. -/
theorem reflected_gamma_upper :
    ‖Complex.Gamma ((3 / 4 : ℂ) - 5 * Complex.I)‖ ≤ (9 / 5000 : ℝ) := by
  have h := Door3GammaProduct.norm_gamma_sq_le_prod
    (z := (3 / 4 : ℂ) - 5 * Complex.I) (by norm_num) 128
  norm_num at h
  have hG := pow_le_pow_left₀
    (Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)).le
    real_gamma_three_quarters_le 2
  have hp : 0 ≤ ∏ k ∈ Finset.range 128,
      (((3 / 4 : ℝ) + k) ^ 2 / (((3 / 4 : ℝ) + k) ^ 2 + 25)) := by
    apply Finset.prod_nonneg
    intro k hk
    positivity
  have hmul := mul_le_mul_of_nonneg_right hG hp
  have hcert := reflected_gamma_product_certificate
  nlinarith [norm_nonneg (Complex.Gamma ((3 / 4 : ℂ) - 5 * Complex.I))]

theorem exp_five_pi_le : Real.exp (5 * Real.pi) ≤ 6800000 := by
  have hsmall := Real.exp_bound' (x := (71 / 100 : ℝ)) (by norm_num)
    (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ] at hsmall
  have hsmall' : Real.exp (71 / 100 : ℝ) ≤ 204 / 100 := by linarith
  have hlarge : Real.exp (15 : ℝ) ≤ (2.7182818286 : ℝ) ^ 15 := by
    have heq : Real.exp (15 : ℝ) = Real.exp 1 ^ (15 : ℕ) := by
      simp [Real.exp_nat_mul]
    rw [heq]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 15
  have hpi : 5 * Real.pi ≤ (15 : ℝ) + 71 / 100 := by
    have := Real.pi_lt_d4
    linarith
  calc
    Real.exp (5 * Real.pi) ≤ Real.exp (15 + 71 / 100 : ℝ) :=
      Real.exp_le_exp.mpr hpi
    _ = Real.exp 15 * Real.exp (71 / 100 : ℝ) := Real.exp_add _ _
    _ ≤ (2.7182818286 : ℝ) ^ 15 * (204 / 100) :=
      mul_le_mul hlarge hsmall' (Real.exp_pos _).le (by positivity)
    _ ≤ 6800000 := by norm_num

theorem cutoff_sine_upper :
    ‖Complex.sin ((Real.pi : ℂ) * ((1 / 4 : ℂ) + 5 * Complex.I))‖ ≤
      (3400001 : ℝ) := by
  let w : ℂ := (Real.pi : ℂ) * ((1 / 4 : ℂ) + 5 * Complex.I)
  have hIm : w.im = 5 * Real.pi := by dsimp [w]; simp; ring
  have heq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  change ‖Complex.sin w‖ ≤ _
  rw [heq]
  simp only [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have h := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
  have hr1 : (-w * Complex.I).re = w.im := by simp
  have hr2 : (w * Complex.I).re = -w.im := by simp
  rw [Complex.norm_exp, Complex.norm_exp, hr1, hr2, hIm] at h
  have hneg : Real.exp (-(5 * Real.pi)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hpos := exp_five_pi_le
  linarith

theorem cutoff_gamma_lower :
    (1 / 2000 : ℝ) ≤ ‖Complex.Gamma ((1 / 4 : ℂ) + 5 * Complex.I)‖ := by
  let z : ℂ := (1 / 4 : ℂ) + 5 * Complex.I
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro hs
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have him := congrArg Complex.im hk
    dsimp [z] at him
    norm_num at him
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hnorm := congrArg norm href
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hnorm
  have hid : (1 - z) = (3 / 4 : ℂ) - 5 * Complex.I := by dsimp [z]; ring
  have hG : ‖Complex.Gamma (1 - z)‖ ≤ (9 / 5000 : ℝ) := by
    rw [hid]
    exact reflected_gamma_upper
  have hS : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ (3400001 : ℝ) := cutoff_sine_upper
  have heq : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.pi := by
    rw [hnorm]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hsin)
  have hb := mul_le_mul hG hS (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 5000)
  have hb' := mul_le_mul_of_nonneg_left hb (norm_nonneg (Complex.Gamma z))
  have hpi := Real.pi_gt_d2
  change (1 / 2000 : ℝ) ≤ ‖Complex.Gamma z‖
  nlinarith [heq]

/-- Discharges the existing named Gamma remainder at the cutoff center. -/
theorem cutR10_gammaRemainder : Door3CutR10Center.cutR10_gammaRemainder := by
  unfold Door3CutR10Center.cutR10_gammaRemainder
  rw [Door3CutR10Center.cutR10_s_eq]
  have heq : (((1 / 2 : ℝ) : ℂ) + ((10 : ℝ) : ℂ) * Complex.I) / 2 =
      (1 / 4 : ℂ) + 5 * Complex.I := by push_cast; ring
  rw [heq]
  exact cutoff_gamma_lower

/-- The cutoff center now needs only its zeta enclosure. -/
theorem cutR10_center_bound_of_zeta
    (hZ : Door3CutR10Center.cutR10_zetaRemainder) :
    (0.001 : ℝ) + 0.04 * CentralCoverAssembly.CutR10.radius ≤
      ‖xiShifted CentralCoverAssembly.CutR10.center‖ :=
  Door3CutR10Center.cutR10_center_bound_of_gamma_zeta cutR10_gammaRemainder hZ

/-- Cutoff fencing with the Gamma supplier discharged. The zeta and
derivative estimates remain explicit proof obligations. -/
theorem cutR10_fencing_of_zeta_deriv
    (hZ : Door3CutR10Center.cutR10_zetaRemainder)
    (hD : Door3CutR10Center.cutR10_derivRemainder 0.04) :
    CentralCoverAssembly.CellFencingHypotheses CentralCoverAssembly.CutR10 0.001 0.04 :=
  Door3CutR10Center.cutR10_fencing_of_remainders cutR10_gammaRemainder hZ hD

end Door3GammaCutoff

#print axioms Door3GammaCutoff.cutR10_gammaRemainder
#print axioms Door3GammaCutoff.cutR10_center_bound_of_zeta
#print axioms Door3GammaCutoff.cutR10_fencing_of_zeta_deriv
