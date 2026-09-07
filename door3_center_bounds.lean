import riemann_hypothesis

open Complex Real

noncomputable section

/-! Unconditional center bounds on the real-symmetric axis.  These are exact
Real inequalities for the actual `xiShifted`, rather than Float data. -/

def D3_imag_axis_center_lower (y : ℝ) : ℝ :=
  ‖xiShifted (Complex.I * (y : ℂ))‖ / 2

theorem D3_imag_axis_center_lower_pos {y : ℝ} (hyne : y ≠ 0)
    (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    0 < D3_imag_axis_center_lower y := by
  unfold D3_imag_axis_center_lower
  have hnz : xiShifted (Complex.I * (y : ℂ)) ≠ 0 :=
    (by
      exact RHProofScaffold.xiShifted_imag_axis_nonvanishing_unconditional y hyne hgt hlt)
  have hnorm : 0 < ‖xiShifted (Complex.I * (y : ℂ))‖ := norm_pos_iff.mpr hnz
  linarith

theorem D3_imag_axis_center_lower_le {y : ℝ} :
    D3_imag_axis_center_lower y ≤ ‖xiShifted (Complex.I * (y : ℂ))‖ := by
  unfold D3_imag_axis_center_lower
  have hnorm : 0 ≤ ‖xiShifted (Complex.I * (y : ℂ))‖ := norm_nonneg _
  linarith

/- Four exact heights used by the standard central y-tiling. -/
theorem D3_center_lower_21_pos :
    0 < D3_imag_axis_center_lower (21 / 200 : ℝ) := by
  apply D3_imag_axis_center_lower_pos
  · norm_num
  · norm_num
  · norm_num

theorem D3_center_lower_1_4_pos :
    0 < D3_imag_axis_center_lower (1 / 4 : ℝ) := by
  apply D3_imag_axis_center_lower_pos
  · norm_num
  · norm_num
  · norm_num

theorem D3_center_lower_7_20_pos :
    0 < D3_imag_axis_center_lower (7 / 20 : ℝ) := by
  apply D3_imag_axis_center_lower_pos
  · norm_num
  · norm_num
  · norm_num

theorem D3_center_lower_89_200_pos :
    0 < D3_imag_axis_center_lower (89 / 200 : ℝ) := by
  apply D3_imag_axis_center_lower_pos
  · norm_num
  · norm_num
  · norm_num

#print axioms D3_imag_axis_center_lower_pos
#print axioms D3_imag_axis_center_lower_le
#print axioms D3_center_lower_21_pos
#print axioms D3_center_lower_1_4_pos
#print axioms D3_center_lower_7_20_pos
#print axioms D3_center_lower_89_200_pos
