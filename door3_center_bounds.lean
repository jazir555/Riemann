import door3_real_center_bounds

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
  have hexp := D3_imag_axis_explicit_center_lower_le hgt hlt
  have hpos : 0 < D3_imag_axis_explicit_center_lower y := by
    unfold D3_imag_axis_explicit_center_lower
    have hs : 0 < (1 / 2 : ℝ) - y := by linarith
    positivity
  nlinarith

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

/-! The four tiling centers also have explicit rational lower bounds for the
actual analytic `xiShifted`, rather than only positivity of an abstract
half-norm certificate. -/

theorem D3_center_lower_21_explicit :
    (6241 / 160000 : ℝ) ≤
      ‖xiShifted (Complex.I * ((21 / 200 : ℝ) : ℂ))‖ :=
  D3_explicit_center_lower_21

theorem D3_center_lower_1_4_explicit :
    (1 / 64 : ℝ) ≤
      ‖xiShifted (Complex.I * ((1 / 4 : ℝ) : ℂ))‖ :=
  D3_explicit_center_lower_1_4

theorem D3_center_lower_7_20_explicit :
    (9 / 1600 : ℝ) ≤
      ‖xiShifted (Complex.I * ((7 / 20 : ℝ) : ℂ))‖ :=
  D3_explicit_center_lower_7_20

theorem D3_center_lower_89_200_explicit :
    (121 / 160000 : ℝ) ≤
      ‖xiShifted (Complex.I * ((89 / 200 : ℝ) : ℂ))‖ :=
  D3_explicit_center_lower_89

theorem D3_center_lower_uniform_explicit {y : ℝ}
    (hy0 : -(49 / 100 : ℝ) ≤ y) (hy1 : y ≤ (49 / 100 : ℝ)) :
    (1 / 40000 : ℝ) ≤ ‖xiShifted (Complex.I * (y : ℂ))‖ :=
  D3_imag_axis_explicit_center_uniform hy0 hy1

#print axioms D3_imag_axis_center_lower_pos
#print axioms D3_imag_axis_center_lower_le
#print axioms D3_center_lower_21_pos
#print axioms D3_center_lower_1_4_pos
#print axioms D3_center_lower_7_20_pos
#print axioms D3_center_lower_89_200_pos
