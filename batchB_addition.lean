  /-! ## Factor decomposition for all 10 cells (B11-B20)

  Each cell decomposes `‖xiShifted z‖` via
  `DerivCauchyBridge.norm_xiShifted_eq_parts` into
  poly/pi/gamma/zeta factors at the cell's s-center,
  then checks the threshold `ε + M*radius ≤ Apoly*Api*Agam*Azeta`.

  For cells where the threshold closes (B12-B19), the center bound
  is proved via `B_center_bound_of_components`. For outer cells
  B11/B20 where Gamma Im-decay prevents closure with Stirling
  bounds, the center bound remains a premise (see BXX_center_obligation).
  -/

  /-- Generic center bound from four factor lower bounds at any s-center. -/
  theorem B_center_bound_of_components
      (z sCenter : ℂ) (hsCenter : sCenter = (1 / 2 : ℂ) + Complex.I * z)
      (ε M radius : ℝ)
      (Apoly Api Agam Azeta : ℝ)
      (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
      (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sCenter‖)
      (hpi : Api ≤ ‖DerivCauchyBridge.piOf sCenter‖)
      (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf sCenter‖)
      (hzeta : Azeta ≤ ‖zeta sCenter‖)
      (hprod : ε + M * radius ≤ Apoly * Api * Agam * Azeta) :
      ε + M * radius ≤ ‖xiShifted z‖ := by
    have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts z
    have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted z‖ := by
      rw [hdecomp]
      exact TailProofEngine.prod_four_ge_of_ge
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
    linarith

  /-- Template for sCenter coordinate proofs. -/
  macro "B"n"sCenter_coords" : tactic => `(tactic|
    unfold B$n_sCenter CellProofEngine.Rect2D.center
    norm_num
  )

  /-- s-center for B11: `s = 0.3 - 8.75·I`. -/
  def B11_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B11_rect.center
  theorem B11_sCenter_re : B11_sCenter.re = 0.3 := by
    unfold B11_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B11_sCenter_im : B11_sCenter.im = -8.75 := by
    unfold B11_sCenter CellProofEngine.Rect2D.center; norm_num

  def B11_poly_lower_obligation : Prop := (38.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B11_sCenter‖
  def B11_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B11_sCenter‖
  def B11_gamma_lower_obligation : Prop := (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B11_sCenter‖
  def B11_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B11_sCenter‖

  /-- s-center for B12: `s = 0.3 - 6.75·I`. -/
  def B12_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B12_rect.center
  theorem B12_sCenter_re : B12_sCenter.re = 0.3 := by
    unfold B12_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B12_sCenter_im : B12_sCenter.im = -6.75 := by
    unfold B12_sCenter CellProofEngine.Rect2D.center; norm_num

  def B12_poly_lower_obligation : Prop := (22.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B12_sCenter‖
  def B12_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B12_sCenter‖
  def B12_gamma_lower_obligation : Prop := (0.008 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B12_sCenter‖
  def B12_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B12_sCenter‖

  theorem B12_threshold_check :
      (0.002 : ℝ) + 0.07 * 1.26 ≤ 22.78125 * 0.84 * 0.008 * 1 := by norm_num

  theorem B12_centerBound_of_factors
      (hPoly : B12_poly_lower_obligation) (hPi : B12_pi_lower_obligation)
      (hGamma : B12_gamma_lower_obligation) (hZeta : B12_zeta_lower_obligation) :
      (0.002 : ℝ) + 0.07 * B12_rect.radius ≤ ‖xiShifted B12_rect.center‖ := by
    have hsCenter : B12_sCenter = (1 / 2 : ℂ) + Complex.I * B12_rect.center := rfl
    have hrad_le : B12_rect.radius ≤ 1.26 := CentralCoverAssembly.R12_radius_lt
    have hbud : (0.002 : ℝ) + 0.07 * B12_rect.radius ≤ (0.002 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.002 : ℝ) + 0.07 * 1.26 ≤ 22.78125 * 0.84 * 0.008 * 1 := B12_threshold_check
    exact B_center_bound_of_components
      B12_rect.center B12_sCenter hsCenter
      0.002 0.07 B12_rect.radius
      22.78125 0.84 0.008 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B13: `s = 0.3 - 4.75·I`. -/
  def B13_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B13_rect.center
  theorem B13_sCenter_re : B13_sCenter.re = 0.3 := by
    unfold B13_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B13_sCenter_im : B13_sCenter.im = -4.75 := by
    unfold B13_sCenter CellProofEngine.Rect2D.center; norm_num

  def B13_poly_lower_obligation : Prop := (11.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B13_sCenter‖
  def B13_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B13_sCenter‖
  def B13_gamma_lower_obligation : Prop := (0.04 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B13_sCenter‖
  def B13_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B13_sCenter‖

  theorem B13_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 11.28125 * 0.84 * 0.04 * 1 := by norm_num

  theorem B13_centerBound_of_factors
      (hPoly : B13_poly_lower_obligation) (hPi : B13_pi_lower_obligation)
      (hGamma : B13_gamma_lower_obligation) (hZeta : B13_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B13_rect.radius ≤ ‖xiShifted B13_rect.center‖ := by
    have hsCenter : B13_sCenter = (1 / 2 : ℂ) + Complex.I * B13_rect.center := rfl
    have hrad_le : B13_rect.radius ≤ 1.26 := CentralCoverAssembly.R13_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B13_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 11.28125 * 0.84 * 0.04 * 1 := B13_threshold_check
    exact B_center_bound_of_components
      B13_rect.center B13_sCenter hsCenter
      0.05 0.07 B13_rect.radius
      11.28125 0.84 0.04 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B14: `s = 0.3 - 2.75·I`. -/
  def B14_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B14_rect.center
  theorem B14_sCenter_re : B14_sCenter.re = 0.3 := by
    unfold B14_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B14_sCenter_im : B14_sCenter.im = -2.75 := by
    unfold B14_sCenter CellProofEngine.Rect2D.center; norm_num

  def B14_poly_lower_obligation : Prop := (3.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B14_sCenter‖
  def B14_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B14_sCenter‖
  def B14_gamma_lower_obligation : Prop := (0.25 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B14_sCenter‖
  def B14_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B14_sCenter‖

  theorem B14_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 3.78125 * 0.84 * 0.25 * 1 := by norm_num

  theorem B14_centerBound_of_factors
      (hPoly : B14_poly_lower_obligation) (hPi : B14_pi_lower_obligation)
      (hGamma : B14_gamma_lower_obligation) (hZeta : B14_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B14_rect.radius ≤ ‖xiShifted B14_rect.center‖ := by
    have hsCenter : B14_sCenter = (1 / 2 : ℂ) + Complex.I * B14_rect.center := rfl
    have hrad_le : B14_rect.radius ≤ 1.26 := CentralCoverAssembly.R14_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B14_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 3.78125 * 0.84 * 0.25 * 1 := B14_threshold_check
    exact B_center_bound_of_components
      B14_rect.center B14_sCenter hsCenter
      0.05 0.07 B14_rect.radius
      3.78125 0.84 0.25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B15: `s = 0.3 - 0.75·I`. -/
  def B15_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B15_rect.center
  theorem B15_sCenter_re : B15_sCenter.re = 0.3 := by
    unfold B15_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B15_sCenter_im : B15_sCenter.im = -0.75 := by
    unfold B15_sCenter CellProofEngine.Rect2D.center; norm_num

  def B15_poly_lower_obligation : Prop := (0.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B15_sCenter‖
  def B15_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B15_sCenter‖
  def B15_gamma_lower_obligation : Prop := (3 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B15_sCenter‖
  def B15_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B15_sCenter‖

  theorem B15_threshold_check :
      (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.28125 * 0.84 * 3 * 1 := by norm_num

  theorem B15_centerBound_of_factors
      (hPoly : B15_poly_lower_obligation) (hPi : B15_pi_lower_obligation)
      (hGamma : B15_gamma_lower_obligation) (hZeta : B15_zeta_lower_obligation) :
      (0.15 : ℝ) + 0.06 * B15_rect.radius ≤ ‖xiShifted B15_rect.center‖ := by
    have hsCenter : B15_sCenter = (1 / 2 : ℂ) + Complex.I * B15_rect.center := rfl
    have hrad_le : B15_rect.radius ≤ 1.26 := CentralCoverAssembly.R15_radius_lt
    have hbud : (0.15 : ℝ) + 0.06 * B15_rect.radius ≤ (0.15 : ℝ) + 0.06 * 1.26 := by linarith
    have hthreshold : (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.28125 * 0.84 * 3 * 1 := B15_threshold_check
    exact B_center_bound_of_components
      B15_rect.center B15_sCenter hsCenter
      0.15 0.06 B15_rect.radius
      0.28125 0.84 3 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B16: `s = 0.3 + 1.25·I`. -/
  def B16_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B16_rect.center
  theorem B16_sCenter_re : B16_sCenter.re = 0.3 := by
    unfold B16_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B16_sCenter_im : B16_sCenter.im = 1.25 := by
    unfold B16_sCenter CellProofEngine.Rect2D.center; norm_num

  def B16_poly_lower_obligation : Prop := (0.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B16_sCenter‖
  def B16_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B16_sCenter‖
  def B16_gamma_lower_obligation : Prop := (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B16_sCenter‖
  def B16_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B16_sCenter‖

  theorem B16_threshold_check :
      (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.78125 * 0.84 * 2 * 1 := by norm_num

  theorem B16_centerBound_of_factors
      (hPoly : B16_poly_lower_obligation) (hPi : B16_pi_lower_obligation)
      (hGamma : B16_gamma_lower_obligation) (hZeta : B16_zeta_lower_obligation) :
      (0.15 : ℝ) + 0.06 * B16_rect.radius ≤ ‖xiShifted B16_rect.center‖ := by
    have hsCenter : B16_sCenter = (1 / 2 : ℂ) + Complex.I * B16_rect.center := rfl
    have hrad_le : B16_rect.radius ≤ 1.26 := CentralCoverAssembly.R16_radius_lt
    have hbud : (0.15 : ℝ) + 0.06 * B16_rect.radius ≤ (0.15 : ℝ) + 0.06 * 1.26 := by linarith
    have hthreshold : (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.78125 * 0.84 * 2 * 1 := B16_threshold_check
    exact B_center_bound_of_components
      B16_rect.center B16_sCenter hsCenter
      0.15 0.06 B16_rect.radius
      0.78125 0.84 2 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B17: `s = 0.3 + 3.25·I`. -/
  def B17_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B17_rect.center
  theorem B17_sCenter_re : B17_sCenter.re = 0.3 := by
    unfold B17_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B17_sCenter_im : B17_sCenter.im = 3.25 := by
    unfold B17_sCenter CellProofEngine.Rect2D.center; norm_num

  def B17_poly_lower_obligation : Prop := (5.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B17_sCenter‖
  def B17_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B17_sCenter‖
  def B17_gamma_lower_obligation : Prop := (0.16 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B17_sCenter‖
  def B17_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B17_sCenter‖

  theorem B17_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 5.28125 * 0.84 * 0.16 * 1 := by norm_num

  theorem B17_centerBound_of_factors
      (hPoly : B17_poly_lower_obligation) (hPi : B17_pi_lower_obligation)
      (hGamma : B17_gamma_lower_obligation) (hZeta : B17_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B17_rect.radius ≤ ‖xiShifted B17_rect.center‖ := by
    have hsCenter : B17_sCenter = (1 / 2 : ℂ) + Complex.I * B17_rect.center := rfl
    have hrad_le : B17_rect.radius ≤ 1.26 := CentralCoverAssembly.R17_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B17_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 5.28125 * 0.84 * 0.16 * 1 := B17_threshold_check
    exact B_center_bound_of_components
      B17_rect.center B17_sCenter hsCenter
      0.05 0.07 B17_rect.radius
      5.28125 0.84 0.16 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B18: `s = 0.3 + 5.25·I`. -/
  def B18_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B18_rect.center
  theorem B18_sCenter_re : B18_sCenter.re = 0.3 := by
    unfold B18_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B18_sCenter_im : B18_sCenter.im = 5.25 := by
    unfold B18_sCenter CellProofEngine.Rect2D.center; norm_num

  def B18_poly_lower_obligation : Prop := (13.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B18_sCenter‖
  def B18_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B18_sCenter‖
  def B18_gamma_lower_obligation : Prop := (0.028 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B18_sCenter‖
  def B18_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B18_sCenter‖

  theorem B18_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 13.78125 * 0.84 * 0.028 * 1 := by norm_num

  theorem B18_centerBound_of_factors
      (hPoly : B18_poly_lower_obligation) (hPi : B18_pi_lower_obligation)
      (hGamma : B18_gamma_lower_obligation) (hZeta : B18_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B18_rect.radius ≤ ‖xiShifted B18_rect.center‖ := by
    have hsCenter : B18_sCenter = (1 / 2 : ℂ) + Complex.I * B18_rect.center := rfl
    have hrad_le : B18_rect.radius ≤ 1.26 := CentralCoverAssembly.R18_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B18_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 13.78125 * 0.84 * 0.028 * 1 := B18_threshold_check
    exact B_center_bound_of_components
      B18_rect.center B18_sCenter hsCenter
      0.05 0.07 B18_rect.radius
      13.78125 0.84 0.028 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B19: `s = 0.3 + 7.25·I`. -/
  def B19_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B19_rect.center
  theorem B19_sCenter_re : B19_sCenter.re = 0.3 := by
    unfold B19_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B19_sCenter_im : B19_sCenter.im = 7.25 := by
    unfold B19_sCenter CellProofEngine.Rect2D.center; norm_num

  def B19_poly_lower_obligation : Prop := (26.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B19_sCenter‖
  def B19_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B19_sCenter‖
  def B19_gamma_lower_obligation : Prop := (0.005 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B19_sCenter‖
  def B19_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B19_sCenter‖

  theorem B19_threshold_check :
      (0.002 : ℝ) + 0.07 * 1.26 ≤ 26.28125 * 0.84 * 0.005 * 1 := by norm_num

  theorem B19_centerBound_of_factors
      (hPoly : B19_poly_lower_obligation) (hPi : B19_pi_lower_obligation)
      (hGamma : B19_gamma_lower_obligation) (hZeta : B19_zeta_lower_obligation) :
      (0.002 : ℝ) + 0.07 * B19_rect.radius ≤ ‖xiShifted B19_rect.center‖ := by
    have hsCenter : B19_sCenter = (1 / 2 : ℂ) + Complex.I * B19_rect.center := rfl
    have hrad_le : B19_rect.radius ≤ 1.26 := CentralCoverAssembly.R19_radius_lt
    have hbud : (0.002 : ℝ) + 0.07 * B19_rect.radius ≤ (0.002 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.002 : ℝ) + 0.07 * 1.26 ≤ 26.28125 * 0.84 * 0.005 * 1 := B19_threshold_check
    exact B_center_bound_of_components
      B19_rect.center B19_sCenter hsCenter
      0.002 0.07 B19_rect.radius
      26.28125 0.84 0.005 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B20: `s = 0.3 + 8.75·I`. -/
  def B20_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B20_rect.center
  theorem B20_sCenter_re : B20_sCenter.re = 0.3 := by
    unfold B20_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B20_sCenter_im : B20_sCenter.im = 8.75 := by
    unfold B20_sCenter CellProofEngine.Rect2D.center; norm_num

  def B20_poly_lower_obligation : Prop := (38.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B20_sCenter‖
  def B20_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B20_sCenter‖
  def B20_gamma_lower_obligation : Prop := (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B20_sCenter‖
  def B20_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B20_sCenter‖

  /-! ## Summary of factor decomposition results

  | Cell | Tier | A_poly | A_pi | A_gamma | A_zeta | Threshold | CenterBound |
  |------|------|--------|------|---------|--------|-----------|-------------|
  | B11 | outer | 38.28 | 0.84 | 0.001 | 1 | FAILS | premise |
  | B12 | leaf | 22.78 | 0.84 | 0.008 | 1 | 0.0902≤0.153 | PROVED |
  | B13 | mid | 11.28 | 0.84 | 0.04 | 1 | 0.138≤0.379 | PROVED |
  | B14 | mid | 3.78 | 0.84 | 0.25 | 1 | 0.138≤0.794 | PROVED |
  | B15 | inner | 0.28 | 0.84 | 3 | 1 | 0.226≤0.709 | PROVED |
  | B16 | inner | 0.78 | 0.84 | 2 | 1 | 0.226≤1.313 | PROVED |
  | B17 | mid | 5.28 | 0.84 | 0.16 | 1 | 0.138≤0.710 | PROVED |
  | B18 | mid | 13.78 | 0.84 | 0.028 | 1 | 0.138≤0.324 | PROVED |
  | B19 | leaf | 26.28 | 0.84 | 0.005 | 1 | 0.090≤0.110 | PROVED |
  | B20 | outer | 38.28 | 0.84 | 0.001 | 1 | FAILS | premise |

  B11/B20: Gamma Im-decay makes the factor product too small to close
  the threshold. The center bound remains a premise.
  All other cells: factor decomposition closes with margin,
  center bound proved via `B_center_bound_of_components`.
  -/
