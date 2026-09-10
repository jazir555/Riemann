import interval_arith
import door3_tail_eta_upper

open Complex Real
noncomputable section

namespace Door3OffAxis

theorem R03_zeta_upper_center :
    ‖zeta R03GammaUpper.sR03‖ ≤ (125 : ℝ) := by
  apply Door3TailEtaUpper.zeta_upper_tail_quarter
  · rw [R03GammaUpper.sR03_re]
    norm_num
  · rw [R03GammaUpper.sR03_re]
    norm_num
  · rw [R03GammaUpper.sR03_im]
    rw [abs_of_neg (by norm_num)]
    norm_num

theorem zeta_upper_shifted_of_bottom_bounds {w : ℂ}
    (hx0 : (-10 : ℝ) ≤ w.re) (hx1 : w.re ≤ (10 : ℝ))
    (hy0 : (0.01 : ℝ) ≤ w.im) (hy1 : w.im ≤ (0.2 : ℝ)) :
    ‖zeta (shiftedS w)‖ ≤ (125 : ℝ) := by
  apply Door3TailEtaUpper.zeta_upper_tail_quarter
  · rw [shiftedS_re]
    linarith
  · rw [shiftedS_re]
    linarith
  · rw [RHProofScaffold.LeafDecomp.shiftedS_im_eq]
    rw [abs_le]
    constructor <;> linarith

theorem R03_zeta_upper_on_rect {w : ℂ}
    (hw : CentralCoverAssembly.R03.mem w) :
    ‖zeta (shiftedS w)‖ ≤ (125 : ℝ) := by
  apply zeta_upper_shifted_of_bottom_bounds
  · have h := hw.1
    rw [CentralCoverAssembly.R03_x0] at h
    linarith
  · have h := hw.2.1
    rw [CentralCoverAssembly.R03_x1] at h
    linarith
  · have h := hw.2.2.1
    rw [CentralCoverAssembly.R03_y0] at h
    exact h
  · have h := hw.2.2.2
    rw [CentralCoverAssembly.R03_y1] at h
    exact h
/-- The two independently generated descriptions of the R02 centre coincide. -/
theorem R02_s_center_eq : R02Uniform.sR02 = R02GammaUpper.sR02 := by
  rfl

/-- A tight fourth-root upper bound for π, proved from the elementary
`π < 3.1416` bound. -/
theorem pi_rpow_quarter_lt_13314 :
    Real.pi ^ ((1 / 4 : ℝ)) < (1.3314 : ℝ) := by
  have h4 : (3.1416 : ℝ) < (1.3314 : ℝ) ^ 4 := by norm_num
  have hpi : Real.pi < (1.3314 : ℝ) ^ 4 := lt_trans Real.pi_lt_d4 h4
  have hlog : Real.log Real.pi < 4 * Real.log (1.3314 : ℝ) := by
    have h := (Real.log_lt_log_iff Real.pi_pos (by positivity)).mpr hpi
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hrw : Real.log (Real.pi ^ ((1 / 4 : ℝ))) =
      (1 / 4) * Real.log Real.pi := Real.log_rpow Real.pi_pos _
  have hfin : Real.log (Real.pi ^ ((1 / 4 : ℝ))) < Real.log (1.3314 : ℝ) := by
    rw [hrw]
    linarith
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos Real.pi_pos _)
    (by norm_num)).mp hfin

/-- The R02 π-power factor has the explicit lower bound `0.751`. -/
theorem R02_pi_lower_tight :
    (0.751 : ℝ) ≤ ‖R00Enclosure.piPart R02Uniform.sR02‖ := by
  have hnorm : ‖R00Enclosure.piPart R02Uniform.sR02‖ =
      Real.pi ^ (-(R02Uniform.sR02.re) / 2) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos
      (-(R02Uniform.sR02 / 2))
    unfold R00Enclosure.piPart
    rw [h]
    congr 1
    rw [Complex.neg_re, Complex.div_ofNat_re]
    ring
  rw [hnorm]
  have h_exp : (-(1 / 4 : ℝ)) ≤ -(R02Uniform.sR02.re) / 2 := by
    rw [R02Uniform.sR02_re]
    norm_num
  have hquarter : (0.751 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt Real.pi_pos), inv_eq_one_div]
    have hp : (0 : ℝ) < Real.pi ^ ((1 / 4 : ℝ)) :=
      Real.rpow_pos_of_pos Real.pi_pos _
    have hi : (1 / 1.3314 : ℝ) ≤ (1 / Real.pi ^ ((1 / 4 : ℝ))) := by
      exact one_div_le_one_div_of_le hp (le_of_lt pi_rpow_quarter_lt_13314)
    exact le_trans (by norm_num : (0.751 : ℝ) ≤ 1 / 1.3314) hi
  calc
    (0.751 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := hquarter
    _ ≤ Real.pi ^ (-(R02Uniform.sR02.re) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) h_exp

/-- R02 centre fencing from the sharp analytic factors and a unit zeta lower
bound.  The theorem is a direct kernel-checked certificate: the only input
left is the actual zeta enclosure at this off-axis point. -/
theorem R02_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R02Uniform.sR02‖) :
    (0.002 : ℝ) + 0.07 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  have harg : R02Uniform.sR02 =
      (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center := rfl
  have hpoly : (22 : ℝ) ≤ ‖R00Enclosure.polyPart
      ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center)‖ := by
    rw [← harg]
    exact R02Uniform.poly_lower_R02
  have hpi : (0.751 : ℝ) ≤ ‖R00Enclosure.piPart
      ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center)‖ := by
    rw [← harg]
    exact R02_pi_lower_tight
  have hgam : (0.006 : ℝ) ≤ ‖R00Enclosure.gammaPart
      ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center)‖ := by
    rw [← harg]
    rw [R02_s_center_eq]
    exact R02SineSharp.gamma_lower_R02_sharp
  have hprod : (0.002 : ℝ) + 0.07 * 1.26 ≤
      22 * 0.751 * 0.006 * 1 := by norm_num
  exact CellUniform.center_bound_of_component_bounds
    CentralCoverAssembly.R02 0.002 0.07 (by norm_num)
    (le_of_lt CentralCoverAssembly.R02_radius_lt)
    22 0.751 0.006 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpoly hpi hgam hzeta hprod

/- The corresponding packaged rectangle is obtained as soon as the derivative
bound on this cell is supplied.  This keeps the analytic centre calculation
and the Cauchy fencing step in one reusable certificate constructor. -/
noncomputable def R02_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R02Uniform.sR02‖)
    (hderiv : ∀ w, CentralCoverAssembly.R02.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) :
    XiLocalZeroFreeRect := by
  have hcenter := R02_center_certificate_of_zeta_ge_one hzeta
  exact CentralCoverAssembly.R02_zeroFree_of_bounds ⟨hcenter, hderiv⟩


/-- Generic off-axis centre certificate. -/
theorem center_certificate_of_components
    (R : CellProofEngine.Rect2D) (s : ℂ) (ε M Apoly Api Agam Azeta : ℝ)
    (harg : s = (1 / 2 : ℂ) + Complex.I * R.center)
    (hM0 : 0 ≤ M) (hrad : R.radius ≤ 1.26)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖R00Enclosure.polyPart s‖)
    (hpi : Api ≤ ‖R00Enclosure.piPart s‖)
    (hgam : Agam ≤ ‖R00Enclosure.gammaPart s‖)
    (hzeta : Azeta ≤ ‖zeta s‖)
    (hprod : ε + M * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  rw [harg] at hpoly hpi hgam hzeta
  exact CellUniform.center_bound_of_component_bounds R ε M hM0 hrad
    Apoly Api Agam Azeta hA0 hB0 hC0 hD0 hpoly hpi hgam hzeta hprod

theorem R03_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖)
    (hgam : (0.025 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR03‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R03.radius ≤
      ‖xiShifted CentralCoverAssembly.R03.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR03‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR03_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R03 R03R10PolyLower.sR03
    0.05 0.07 11.3 (1 / 2 : ℝ) 0.025 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R03_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R03 hpi hgam hzeta
    (by norm_num)


theorem R04_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖)
    (hgam : (0.08 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR04‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R04.radius ≤
      ‖xiShifted CentralCoverAssembly.R04.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR04‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR04_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R04 R03R10PolyLower.sR04
    0.05 0.07 3.85 (1 / 2 : ℝ) 0.08 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R04_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R04 hpi hgam hzeta
    (by norm_num)

theorem R05_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖)
    (hgam : (1.2 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR05‖) :
    (0.15 : ℝ) + 0.06 * CentralCoverAssembly.R05.radius ≤
      ‖xiShifted CentralCoverAssembly.R05.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR05‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR05_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R05 R03R10PolyLower.sR05
    0.15 0.06 0.39 (1 / 2 : ℝ) 1.2 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R05_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R05 hpi hgam hzeta
    (by norm_num)

theorem R06_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖)
    (hgam : (0.52 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR06‖) :
    (0.15 : ℝ) + 0.06 * CentralCoverAssembly.R06.radius ≤
      ‖xiShifted CentralCoverAssembly.R06.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR06‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR06_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R06 R03R10PolyLower.sR06
    0.15 0.06 0.88 (1 / 2 : ℝ) 0.52 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R06_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R06 hpi hgam hzeta
    (by norm_num)

theorem R07_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖)
    (hgam : (0.052 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR07‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R07.radius ≤
      ‖xiShifted CentralCoverAssembly.R07.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR07‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR07_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R07 R03R10PolyLower.sR07
    0.05 0.07 5.35 (1 / 2 : ℝ) 0.052 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R07_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R07 hpi hgam hzeta
    (by norm_num)

theorem R08_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR08‖)
    (hgam : (0.021 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR08‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R08.radius ≤
      ‖xiShifted CentralCoverAssembly.R08.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR08‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR08_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R08 R03R10PolyLower.sR08
    0.05 0.07 13.8 (1 / 2 : ℝ) 0.021 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R08_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R08 hpi hgam hzeta
    (by norm_num)

theorem R09_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR09‖)
    (hgam : (0.007 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR09‖) :
    (0.002 : ℝ) + 0.07 * CentralCoverAssembly.R09.radius ≤
      ‖xiShifted CentralCoverAssembly.R09.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR09‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR09_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R09 R03R10PolyLower.sR09
    0.002 0.07 26.3 (1 / 2 : ℝ) 0.007 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R09_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R09 hpi hgam hzeta
    (by norm_num)

theorem R10_center_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR10‖)
    (hgam : (0.0035 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR10‖) :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R10.radius ≤
      ‖xiShifted CentralCoverAssembly.R10.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR10‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR10_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R10 R03R10PolyLower.sR10
    0.002 0.05 38.3 (1 / 2 : ℝ) 0.0035 1 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R10_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R10 hpi hgam hzeta
    (by norm_num)



noncomputable def R03_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖)
    (hgam : (0.025 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR03‖)
    (hderiv : ∀ w, CentralCoverAssembly.R03.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R03_zeroFree_of_bounds
    ⟨R03_center_certificate hzeta hgam, hderiv⟩


noncomputable def R04_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖)
    (hgam : (0.08 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR04‖)
    (hderiv : ∀ w, CentralCoverAssembly.R04.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R04_zeroFree_of_bounds
    ⟨R04_center_certificate hzeta hgam, hderiv⟩

noncomputable def R05_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖)
    (hgam : (1.2 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR05‖)
    (hderiv : ∀ w, CentralCoverAssembly.R05.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R05_zeroFree_of_bounds
    ⟨R05_center_certificate hzeta hgam, hderiv⟩

noncomputable def R06_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖)
    (hgam : (0.52 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR06‖)
    (hderiv : ∀ w, CentralCoverAssembly.R06.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R06_zeroFree_of_bounds
    ⟨R06_center_certificate hzeta hgam, hderiv⟩

noncomputable def R07_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖)
    (hgam : (0.052 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR07‖)
    (hderiv : ∀ w, CentralCoverAssembly.R07.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R07_zeroFree_of_bounds
    ⟨R07_center_certificate hzeta hgam, hderiv⟩

noncomputable def R08_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR08‖)
    (hgam : (0.021 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR08‖)
    (hderiv : ∀ w, CentralCoverAssembly.R08.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R08_zeroFree_of_bounds
    ⟨R08_center_certificate hzeta hgam, hderiv⟩

noncomputable def R09_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR09‖)
    (hgam : (0.007 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR09‖)
    (hderiv : ∀ w, CentralCoverAssembly.R09.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R09_zeroFree_of_bounds
    ⟨R09_center_certificate hzeta hgam, hderiv⟩

noncomputable def R10_zero_free_certificate
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR10‖)
    (hgam : (0.0035 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR10‖)
    (hderiv : ∀ w, CentralCoverAssembly.R10.mem w →
      ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R10_zeroFree_of_bounds
    ⟨R10_center_certificate hzeta hgam, hderiv⟩



theorem exp_five_lt_149 : Real.exp 5 < (149 : ℝ) := by
  have h1 : Real.exp (5 : ℝ) = (Real.exp 1) ^ (5 : ℕ) := by
    have h := Real.exp_nat_mul (1 : ℝ) (5 : ℕ)
    simpa using h.symm
  have h2 : (Real.exp 1) ^ (5 : ℕ) < (2.7182818286 : ℝ) ^ (5 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (5 : ℕ) < 149 := by norm_num
  rw [h1]
  exact lt_trans h2 h3

theorem sin_upper_of_nonpos_im_five {w : ℂ}
    (habs : |w.im| ≤ (5 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (75 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 5 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 75 := by
    have hexp := exp_five_lt_149
    linarith
  exact le_trans hle hfin

/- A sharp local sine enclosure used for the R05 Gamma reflection.  The
   identity `‖sin(x+iy)‖² = sin(x)² + sinh(y)²` keeps the bound below the
   1.66 threshold needed by the centre product. -/
theorem norm_sin_of_re_im_small {w : ℂ} (hx : |w.re| ≤ (0.63 : ℝ))
    (hy : |w.im| ≤ (1.2 : ℝ)) :
    ‖Complex.sin w‖ ≤ (1.66 : ℝ) := by
  have hsin : |Real.sin w.re| ≤ |w.re| := Real.abs_sin_le_abs
  have hsinh : |Real.sinh w.im| ≤ Real.sinh |w.im| := by
    rw [Real.abs_sinh]
  have hsq_sinh : (Real.sinh |w.im|)^2 ≤ (Real.sinh (1.2:ℝ))^2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr
      (Real.sinh_le_sinh.mpr hy)
  have hexp12 : Real.exp (1.2:ℝ) ≤ (3.35:ℝ) := by
    have he1' := Real.exp_one_lt_d9
    have he1 : Real.exp (1:ℝ) ≤ (2.719:ℝ) := by linarith
    have he02 : Real.exp (0.2:ℝ) ≤ (1.23:ℝ) := by
      have h := Real.exp_bound' (x := (0.2 : ℝ)) (by norm_num) (by norm_num)
        (n := 4) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num at h
      linarith
    calc
      Real.exp (1.2:ℝ) = Real.exp 1 * Real.exp 0.2 := by
        rw [show (1.2:ℝ)=1+0.2 by norm_num, Real.exp_add]
      _ ≤ 2.719 * 1.23 := mul_le_mul he1 he02 (by positivity) (by norm_num)
      _ ≤ 3.35 := by norm_num
  have hexpneg : (1 / (3.35:ℝ)) ≤ Real.exp (-(1.2:ℝ)) := by
    rw [Real.exp_neg]
    simpa [one_div] using (one_div_le_one_div_of_le (by positivity) hexp12)
  have hsinh12 : Real.sinh (1.2:ℝ) ≤ (1.53:ℝ) := by
    rw [Real.sinh_eq]
    have hpos : 0 ≤ Real.exp (-(1.2:ℝ)) := (Real.exp_pos _).le
    nlinarith [hexp12, hexpneg]
  have hsq_sinh' : (Real.sinh w.im)^2 ≤ (1.53:ℝ)^2 := by
    calc
      (Real.sinh w.im)^2 = |Real.sinh w.im|^2 := by rw [sq_abs]
      _ ≤ (Real.sinh |w.im|)^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hsinh
      _ ≤ (Real.sinh (1.2:ℝ))^2 := hsq_sinh
      _ ≤ (1.53:ℝ)^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hsinh12
  have hsq_sin : (Real.sin w.re)^2 ≤ (0.63:ℝ)^2 := by
    calc
      (Real.sin w.re)^2 = |Real.sin w.re|^2 := by rw [sq_abs]
      _ ≤ |w.re|^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hsin
      _ ≤ (0.63:ℝ)^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hx
  have hsq : ‖Complex.sin w‖^2 ≤ (1.66:ℝ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sin_eq]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im]
    norm_num
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq w.re, Real.cosh_sq' w.im,
      hsq_sin, hsq_sinh']
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

/- Generic reflection assembly.  It isolates the only analytic inputs needed
   to turn an upper bound for Γ(1-s/2) and sin(πs/2) into a lower bound for
   Γ(s/2), so later cells can reuse the same kernel-checked bridge. -/
theorem gamma_lower_of_reflection {s : ℂ} {L G S : ℝ}
    (hG0 : 0 ≤ G) (hS0 : 0 ≤ S)
    (hG1_ne : Complex.Gamma (1 - s / 2) ≠ 0)
    (hsin_ne : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0)
    (hG1 : ‖Complex.Gamma (1 - s / 2)‖ ≤ G)
    (hsin : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ S)
    (hbase : L ≤ Real.pi / (S * G)) :
    L ≤ ‖Complex.Gamma (s / 2)‖ := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  have hnorm : ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hp] at h
    exact h
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - s / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ *
      ‖Complex.Gamma (1 - s / 2)‖ := mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ *
      ‖Complex.Gamma (1 - s / 2)‖ ≤ S * G :=
    mul_le_mul hsin hG1 (norm_nonneg _) hS0
  have hfrac_le : Real.pi / (S * G) ≤
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ *
        ‖Complex.Gamma (1 - s / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ *
      ‖Complex.Gamma (1 - s / 2)‖) = ‖Complex.Gamma (s / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - s / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (s / 2)‖ =
        (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖) /
          ‖Complex.Gamma (1 - s / 2)‖ := eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  exact le_trans hbase (hfrac_le.trans_eq hnum)

theorem exp_four_point_four_le_83 : Real.exp (4.4 : ℝ) ≤ (83 : ℝ) := by
  have he4 : Real.exp (4 : ℝ) ≤ (55 : ℝ) := by
    have h1 : Real.exp (4 : ℝ) = (Real.exp 1) ^ (4 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (4 : ℕ)
      simpa using h.symm
    rw [h1]
    have hh := Real.exp_one_lt_d9
    have hpow : (Real.exp 1) ^ (4 : ℕ) < (2.7182818286 : ℝ) ^ (4 : ℕ) := by
      apply pow_lt_pow_left₀ hh (le_of_lt (Real.exp_pos _)) (by norm_num)
    norm_num at hpow ⊢
    linarith
  have he04 : Real.exp (0.4 : ℝ) ≤ (1.5 : ℝ) := by
    have h := Real.exp_bound' (x := (0.4 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (4.4 : ℝ) = Real.exp 4 * Real.exp 0.4 := by
      rw [show (4.4 : ℝ) = 4 + 0.4 by norm_num, Real.exp_add]
    _ ≤ 55 * 1.5 := mul_le_mul he4 he04 (by positivity) (by norm_num)
    _ ≤ 83 := by norm_num

theorem sin_upper_of_nonpos_im_four_four {w : ℂ}
    (habs : |w.im| ≤ (4.4 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (42 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 4.4 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 42 := by
    have hexp := exp_four_point_four_le_83
    linarith
  exact le_trans hle hfin

theorem R04_sine_upper_tight :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2))‖ ≤ (42 : ℝ) := by
  apply sin_upper_of_nonpos_im_four_four
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
        Real.pi * (R03R10PolyLower.sR04.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR04_im, abs_mul]
    have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    calc
      |Real.pi| * |-2.75 / 2| ≤ 3.1416 * 1.375 := by
        apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
      _ ≤ 4.4 := by norm_num
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
        Real.pi * (R03R10PolyLower.sR04.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR04_im]
    nlinarith [Real.pi_pos]

theorem R04_gamma_lower_sharp_014 :
    (0.14 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR04‖ := by
  have hs : R03R10PolyLower.sR04 = R04GammaUpper.sR04 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R04GammaUpper.sR04 / 2).re := by
    rw [R04GammaUpper.zUpR04_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R04GammaUpper.sR04 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R04GammaUpper.sR04_im]
    norm_num
  apply gamma_lower_of_reflection (s := R04GammaUpper.sR04)
    (L := (0.14 : ℝ)) (G := (0.5 : ℝ)) (S := (42 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R04GammaUpper.gamma_one_sub_half_upper_R04
  · exact R04_sine_upper_tight
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

theorem exp_four_point_thirtytwo_le_76 : Real.exp (4.32 : ℝ) ≤ (76 : ℝ) := by
  have he4 : Real.exp (4 : ℝ) ≤ (55 : ℝ) := by
    have h1 : Real.exp (4 : ℝ) = (Real.exp 1) ^ (4 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (4 : ℕ)
      simpa using h.symm
    rw [h1]
    have hh := Real.exp_one_lt_d9
    have hpow : (Real.exp 1) ^ (4 : ℕ) < (2.7182818286 : ℝ) ^ (4 : ℕ) := by
      apply pow_lt_pow_left₀ hh (le_of_lt (Real.exp_pos _)) (by norm_num)
    norm_num at hpow ⊢
    linarith
  have he032 : Real.exp (0.32 : ℝ) ≤ (1.38 : ℝ) := by
    have h := Real.exp_bound' (x := (0.32 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (4.32 : ℝ) = Real.exp 4 * Real.exp 0.32 := by
      rw [show (4.32 : ℝ) = 4 + 0.32 by norm_num, Real.exp_add]
    _ ≤ 55 * 1.38 := mul_le_mul he4 he032 (by positivity) (by norm_num)
    _ ≤ 76 := by norm_num

theorem exp_seven_point_four_seven_le_1767 : Real.exp (7.47 : ℝ) ≤ (1767 : ℝ) := by
  have he7 : Real.exp (7 : ℝ) ≤ (1097 : ℝ) := by
    have h1 : Real.exp (7 : ℝ) = (Real.exp 1) ^ (7 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (7 : ℕ)
      simpa using h.symm
    rw [h1]
    have hpow : (Real.exp 1) ^ (7 : ℕ) < (2.7182818286 : ℝ) ^ (7 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    norm_num at hpow ⊢
    linarith
  have he047 : Real.exp (0.47 : ℝ) ≤ (1.61 : ℝ) := by
    have h := Real.exp_bound' (x := (0.47 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (7.47 : ℝ) = Real.exp 7 * Real.exp 0.47 := by
      rw [show (7.47 : ℝ) = 7 + 0.47 by norm_num, Real.exp_add]
    _ ≤ 1097 * 1.61 := mul_le_mul he7 he047 (by positivity) (by norm_num)
    _ ≤ 1767 := by norm_num

theorem sin_upper_of_nonpos_im_seven_point_four_seven {w : ℂ}
    (habs : |w.im| ≤ (7.47 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (884 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 7.47 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 884 := by
    have hexp := exp_seven_point_four_seven_le_1767
    linarith
  exact le_trans hle hfin

theorem R03_sine_upper_tight :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR03 / 2))‖ ≤ (884 : ℝ) := by
  apply sin_upper_of_nonpos_im_seven_point_four_seven
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR03 / 2)).im =
        Real.pi * (R03R10PolyLower.sR03.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR03_im, abs_mul]
    have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    calc
      |Real.pi| * |-4.75 / 2| ≤ 3.1416 * 2.375 := by
        apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
      _ ≤ 7.47 := by norm_num
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR03 / 2)).im =
        Real.pi * (R03R10PolyLower.sR03.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR03_im]
    nlinarith [Real.pi_pos]

theorem R03_gamma_lower_sharp :
    (0.025 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR03‖ := by
  have hs : R03R10PolyLower.sR03 = R03GammaUpper.sR03 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R03GammaUpper.sR03 / 2).re := by
    rw [R03GammaUpper.zUpR03_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R03GammaUpper.sR03 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R03GammaUpper.sR03 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R03GammaUpper.sR03_im]
    norm_num
  apply gamma_lower_of_reflection (s := R03GammaUpper.sR03)
    (L := (0.025 : ℝ)) (G := (0.14 : ℝ)) (S := (884 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R03GammaUpper.gamma_one_sub_half_upper_R03
  · exact R03_sine_upper_tight
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

theorem R03_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R03.radius ≤
      ‖xiShifted CentralCoverAssembly.R03.center‖ := by
  exact R03_center_certificate hzeta R03_gamma_lower_sharp

noncomputable def R03_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖)
    (hderiv : ∀ w, CentralCoverAssembly.R03.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R03_zeroFree_of_bounds
    ⟨R03_center_certificate_of_zeta_ge_one hzeta, hderiv⟩

theorem sin_upper_of_nonpos_im_four_point_thirtytwo {w : ℂ}
    (habs : |w.im| ≤ (4.32 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (38.5 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 4.32 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 38.5 := by
    have hexp := exp_four_point_thirtytwo_le_76
    linarith
  exact le_trans hle hfin

theorem R04_sine_upper_tighter :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2))‖ ≤ (38.5 : ℝ) := by
  apply sin_upper_of_nonpos_im_four_point_thirtytwo
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
        Real.pi * (R03R10PolyLower.sR04.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR04_im, abs_mul]
    have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    calc
      |Real.pi| * |-2.75 / 2| ≤ 3.1416 * 1.375 := by
        apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
      _ ≤ 4.32 := by norm_num
  · have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
        Real.pi * (R03R10PolyLower.sR04.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR04_im]
    nlinarith [Real.pi_pos]

theorem R04_gamma_lower_sharp_016 :
    (0.16 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR04‖ := by
  have hs : R03R10PolyLower.sR04 = R04GammaUpper.sR04 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R04GammaUpper.sR04 / 2).re := by
    rw [R04GammaUpper.zUpR04_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R04GammaUpper.sR04 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R04GammaUpper.sR04_im]
    norm_num
  apply gamma_lower_of_reflection (s := R04GammaUpper.sR04)
    (L := (0.16 : ℝ)) (G := (0.5 : ℝ)) (S := (38.5 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R04GammaUpper.gamma_one_sub_half_upper_R04
  · exact R04_sine_upper_tighter
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

theorem R04_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R04.radius ≤
      ‖xiShifted CentralCoverAssembly.R04.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤
      ‖R00Enclosure.piPart R03R10PolyLower.sR04‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR04_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R04 R03R10PolyLower.sR04
    0.05 0.07 3.85 (1 / 2 : ℝ) 0.16 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R04_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R04 hpi
    R04_gamma_lower_sharp_016 hzeta (by norm_num)

noncomputable def R04_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖)
    (hderiv : ∀ w, CentralCoverAssembly.R04.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R04_zeroFree_of_bounds
    ⟨R04_center_certificate_of_zeta_ge_half hzeta, hderiv⟩

theorem R05_sine_upper_tight :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR05 / 2))‖ ≤ (1.66 : ℝ) := by
  let w : ℂ := (Real.pi : ℂ) * (R03R10PolyLower.sR05 / 2)
  have hre : w.re = Real.pi * (R03R10PolyLower.sR05.re / 2) := by
    dsimp [w]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re]
  have him : w.im = Real.pi * (R03R10PolyLower.sR05.im / 2) := by
    dsimp [w]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  have hx : |w.re| ≤ (0.63 : ℝ) := by
    rw [hre, R03R10PolyLower.sR05_re, abs_mul]
    calc
      |Real.pi| * |0.395 / 2| ≤ 3.1416 * 0.1975 := by
        apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
      _ ≤ 0.63 := by norm_num
  have hy : |w.im| ≤ (1.2 : ℝ) := by
    rw [him, R03R10PolyLower.sR05_im, abs_mul]
    calc
      |Real.pi| * |-0.75 / 2| ≤ 3.1416 * 0.375 := by
        apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
      _ ≤ 1.2 := by norm_num
  exact norm_sin_of_re_im_small hx hy

theorem R05_gamma_lower_sharp :
    (1.2 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR05‖ := by
  have hs : R03R10PolyLower.sR05 = R05GammaUpper.sR05 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R05GammaUpper.sR05 / 2).re := by
    rw [R05GammaUpper.zUpR05_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R05GammaUpper.sR05 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R05GammaUpper.sR05_im]
    norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (R05GammaUpper.sR05 / 2)
  have hnorm : ‖Complex.Gamma (R05GammaUpper.sR05 / 2)‖
        * ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hp] at h
    exact h
  have hG1_le : ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ ≤ 1.5 :=
    R05GammaUpper.gamma_one_sub_half_upper_R05
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ ≤ 1.66 := by
    exact R05_sine_upper_tight
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) <
      ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ *
        ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ := mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ *
      ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ ≤ 1.66 * 1.5 :=
    mul_le_mul hsin_le hG1_le (norm_nonneg _) (by norm_num)
  have hfrac_le : Real.pi / (1.66 * 1.5) ≤
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ *
        ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖ *
      ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖) =
      ‖Complex.Gamma (R05GammaUpper.sR05 / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (R05GammaUpper.sR05 / 2)‖ =
        (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R05GammaUpper.sR05 / 2))‖) /
          ‖Complex.Gamma (1 - R05GammaUpper.sR05 / 2)‖ :=
      eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  have hbase : (1.2 : ℝ) ≤ Real.pi / (1.66 * 1.5) := by
    rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith
  exact le_trans hbase (hfrac_le.trans_eq hnum)

theorem R04_pi_half_im_abs_le_five :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im| ≤ (5 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
      Real.pi * (R03R10PolyLower.sR04.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR04_im]
  rw [abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |-2.75 / 2| ≤ 3.1416 * 1.375 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 5 := by norm_num

theorem R04_sine_upper :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2))‖ ≤ (75 : ℝ) :=
  sin_upper_of_nonpos_im_five R04_pi_half_im_abs_le_five (by
    have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR04 / 2)).im =
        Real.pi * (R03R10PolyLower.sR04.im / 2) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_im]
    rw [him, R03R10PolyLower.sR04_im]
    nlinarith [Real.pi_pos])

theorem R04_gamma_lower_sharp :
    (0.08 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR04‖ := by
  have hs : R03R10PolyLower.sR04 = R04GammaUpper.sR04 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R04GammaUpper.sR04 / 2).re := by
    rw [R04GammaUpper.zUpR04_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R04GammaUpper.sR04 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R04GammaUpper.sR04_im]
    norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (R04GammaUpper.sR04 / 2)
  have hnorm : ‖Complex.Gamma (R04GammaUpper.sR04 / 2)‖
        * ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hp] at h
    exact h
  have hG1_le : ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ ≤ 0.5 :=
    R04GammaUpper.gamma_one_sub_half_upper_R04
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ ≤ 75 := by
    exact R04_sine_upper
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) <
      ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ *
        ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ := mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ *
      ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ ≤ 75 * 0.5 :=
    mul_le_mul hsin_le hG1_le (norm_nonneg _) (by norm_num)
  have hfrac_le : Real.pi / (75 * 0.5) ≤
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ *
        ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖ *
      ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖) =
      ‖Complex.Gamma (R04GammaUpper.sR04 / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (R04GammaUpper.sR04 / 2)‖ =
        (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R04GammaUpper.sR04 / 2))‖) /
          ‖Complex.Gamma (1 - R04GammaUpper.sR04 / 2)‖ :=
      eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  have hbase : (0.08 : ℝ) ≤ Real.pi / (75 * 0.5) := by
    rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith
  exact le_trans hbase (hfrac_le.trans_eq hnum)



theorem R04_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R04.radius ≤
      ‖xiShifted CentralCoverAssembly.R04.center‖ :=
  R04_center_certificate hzeta R04_gamma_lower_sharp

noncomputable def R04_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR04‖)
    (hderiv : ∀ w, CentralCoverAssembly.R04.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R04_zeroFree_of_bounds
    ⟨R04_center_certificate_of_zeta_ge_one hzeta, hderiv⟩

theorem R05_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖) :
    (0.15 : ℝ) + 0.06 * CentralCoverAssembly.R05.radius ≤
      ‖xiShifted CentralCoverAssembly.R05.center‖ :=
  R05_center_certificate hzeta R05_gamma_lower_sharp

noncomputable def R05_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖)
    (hderiv : ∀ w, CentralCoverAssembly.R05.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R05_zeroFree_of_bounds
    ⟨R05_center_certificate_of_zeta_ge_one hzeta, hderiv⟩



theorem exp_two_tenths_le_123 : Real.exp 0.2 ≤ (1.23 : ℝ) := by
  have h := Real.exp_bound' (x := (0.2 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem exp_five_point_two_le_183 : Real.exp 5.2 ≤ (184 : ℝ) := by
  have hsplit : (5.2 : ℝ) = 5 + 0.2 := by norm_num
  have h5 := exp_five_lt_149.le
  have h2 := exp_two_tenths_le_123
  have hm : Real.exp 5 * Real.exp 0.2 ≤ 149 * 1.23 :=
    mul_le_mul h5 h2 (le_of_lt (Real.exp_pos _)) (by norm_num)
  calc
    Real.exp 5.2 = Real.exp 5 * Real.exp 0.2 := by
      rw [hsplit, Real.exp_add]
    _ ≤ 149 * 1.23 := hm
    _ ≤ 184 := by norm_num

theorem sin_upper_of_nonpos_im_five_point_two {w : ℂ}
    (habs : |w.im| ≤ (5.2 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (93 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 5.2 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 93 := by
    have hexp := exp_five_point_two_le_183
    linarith
  exact le_trans hle hfin

theorem R07_pi_half_im_abs_le_five_point_two :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR07 / 2)).im| ≤ (5.2 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR07 / 2)).im =
      Real.pi * (R03R10PolyLower.sR07.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR07_im]
  rw [abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |3.25 / 2| ≤ 3.1416 * 1.625 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 5.2 := by norm_num

theorem R07_sine_upper :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR07 / 2))‖ ≤ (93 : ℝ) := by
  let w : ℂ := (Real.pi : ℂ) * (R03R10PolyLower.sR07 / 2)
  have habs : |(-w).im| ≤ (5.2 : ℝ) := by
    dsimp [w]
    rw [abs_neg]
    exact R07_pi_half_im_abs_le_five_point_two
  have him : w.im = Real.pi * (R03R10PolyLower.sR07.im / 2) := by
    dsimp [w]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  have hnon : (-w).im ≤ 0 := by
    rw [Complex.neg_im, him, R03R10PolyLower.sR07_im]
    have hp : (0 : ℝ) ≤ Real.pi * (3.25 / 2) :=
      mul_nonneg Real.pi_pos.le (by norm_num)
    linarith
  have h := sin_upper_of_nonpos_im_five_point_two (w := -w) habs hnon
  dsimp [w] at h ⊢
  simpa [Complex.sin_neg, norm_neg] using h

theorem R07_gamma_lower_sharp :
    (0.052 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR07‖ := by
  have hs : R03R10PolyLower.sR07 = R07GammaUpper.sR07 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R07GammaUpper.sR07 / 2).re := by
    rw [R07GammaUpper.zUpR07_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R07GammaUpper.sR07 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R07GammaUpper.sR07_im]
    norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (R07GammaUpper.sR07 / 2)
  have hnorm : ‖Complex.Gamma (R07GammaUpper.sR07 / 2)‖
        * ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hp] at h
    exact h
  have hG1_le : ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ ≤ 0.5 :=
    R07GammaUpper.gamma_one_sub_half_upper_R07
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ ≤ 93 := by
    exact R07_sine_upper
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) <
      ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ *
        ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ := mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ *
      ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ ≤ 93 * 0.5 :=
    mul_le_mul hsin_le hG1_le (norm_nonneg _) (by norm_num)
  have hfrac_le : Real.pi / (93 * 0.5) ≤
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ *
        ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖ *
      ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖) =
      ‖Complex.Gamma (R07GammaUpper.sR07 / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (R07GammaUpper.sR07 / 2)‖ =
        (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R07GammaUpper.sR07 / 2))‖) /
          ‖Complex.Gamma (1 - R07GammaUpper.sR07 / 2)‖ :=
      eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  have hbase : (0.052 : ℝ) ≤ Real.pi / (93 * 0.5) := by
    rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith
  exact le_trans hbase (hfrac_le.trans_eq hnum)



theorem R07_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R07.radius ≤
      ‖xiShifted CentralCoverAssembly.R07.center‖ :=
  R07_center_certificate hzeta R07_gamma_lower_sharp

noncomputable def R07_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖)
    (hderiv : ∀ w, CentralCoverAssembly.R07.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R07_zeroFree_of_bounds
    ⟨R07_center_certificate_of_zeta_ge_one hzeta, hderiv⟩



theorem exp_two_lt_7_4 : Real.exp 2 < (7.4 : ℝ) := by
  have h1 : Real.exp (2 : ℝ) = (Real.exp 1) ^ (2 : ℕ) := by
    have h := Real.exp_nat_mul (1 : ℝ) (2 : ℕ)
    simpa using h.symm
  have h2 : (Real.exp 1) ^ (2 : ℕ) < (2.7182818286 : ℝ) ^ (2 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (2 : ℕ) < 7.4 := by norm_num
  rw [h1]
  exact lt_trans h2 h3

theorem sin_upper_of_nonpos_im_two {w : ℂ}
    (habs : |w.im| ≤ (2 : ℝ)) (hnonpos : w.im ≤ 0) :
    ‖Complex.sin w‖ ≤ (4.2 : ℝ) := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  have hfin : (Real.exp w.im + Real.exp (-w.im)) / 2 ≤ 4.2 := by
    have hexp := exp_two_lt_7_4
    linarith
  exact le_trans hle hfin

theorem R06_pi_half_im_abs_le_two :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR06 / 2)).im| ≤ (2 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR06 / 2)).im =
      Real.pi * (R03R10PolyLower.sR06.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR06_im]
  rw [abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |1.25 / 2| ≤ 3.1416 * 0.625 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 2 := by norm_num

theorem R06_sine_upper :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR06 / 2))‖ ≤ (4.2 : ℝ) := by
  let w : ℂ := (Real.pi : ℂ) * (R03R10PolyLower.sR06 / 2)
  have habs : |(-w).im| ≤ (2 : ℝ) := by
    dsimp [w]
    rw [abs_neg]
    exact R06_pi_half_im_abs_le_two
  have him : w.im = Real.pi * (R03R10PolyLower.sR06.im / 2) := by
    dsimp [w]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  have hnon : (-w).im ≤ 0 := by
    rw [Complex.neg_im, him, R03R10PolyLower.sR06_im]
    have hp : (0 : ℝ) ≤ Real.pi * (1.25 / 2) :=
      mul_nonneg Real.pi_pos.le (by norm_num)
    linarith
  have h := sin_upper_of_nonpos_im_two (w := -w) habs hnon
  dsimp [w] at h ⊢
  simpa [Complex.sin_neg, norm_neg] using h

theorem R06_gamma_lower_sharp :
    (0.52 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR06‖ := by
  have hs : R03R10PolyLower.sR06 = R06GammaUpper.sR06 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R06GammaUpper.sR06 / 2).re := by
    rw [R06GammaUpper.zUpR06_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R06GammaUpper.sR06 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R06GammaUpper.sR06_im]
    norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (R06GammaUpper.sR06 / 2)
  have hnorm : ‖Complex.Gamma (R06GammaUpper.sR06 / 2)‖
        * ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hp] at h
    exact h
  have hG1_le : ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ ≤ 1.2 :=
    R06GammaUpper.gamma_one_sub_half_upper_R06
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ ≤ 4.2 := by
    exact R06_sine_upper
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) <
      ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ *
        ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ := mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ *
      ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ ≤ 4.2 * 1.2 :=
    mul_le_mul hsin_le hG1_le (norm_nonneg _) (by norm_num)
  have hfrac_le : Real.pi / (4.2 * 1.2) ≤
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ *
        ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖ *
      ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖) =
      ‖Complex.Gamma (R06GammaUpper.sR06 / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (R06GammaUpper.sR06 / 2)‖ =
        (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (R06GammaUpper.sR06 / 2))‖) /
          ‖Complex.Gamma (1 - R06GammaUpper.sR06 / 2)‖ :=
      eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  have hbase : (0.52 : ℝ) ≤ Real.pi / (4.2 * 1.2) := by
    rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith
  exact le_trans hbase (hfrac_le.trans_eq hnum)



theorem R06_center_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖) :
    (0.15 : ℝ) + 0.06 * CentralCoverAssembly.R06.radius ≤
      ‖xiShifted CentralCoverAssembly.R06.center‖ :=
  R06_center_certificate hzeta R06_gamma_lower_sharp

noncomputable def R06_zero_free_certificate_of_zeta_ge_one
    (hzeta : (1 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖)
    (hderiv : ∀ w, CentralCoverAssembly.R06.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R06_zeroFree_of_bounds
    ⟨R06_center_certificate_of_zeta_ge_one hzeta, hderiv⟩

/- A reusable elementary sine bound. -/
theorem sin_upper_of_nonpos_im_of_exp_bound {w : ℂ} {K E : ℝ}
    (habs : |w.im| ≤ K) (hnonpos : w.im ≤ 0)
    (hexp : Real.exp K ≤ E) :
    ‖Complex.sin w‖ ≤ (E + 1) / 2 := by
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin
    ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ 1 := by
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
      _ = 1 := Real.exp_zero
  have e2 : Real.exp (-w.im) ≤ Real.exp K := by
    apply Real.exp_le_exp.mpr
    exact le_trans (neg_le_abs _) habs
  linarith

theorem exp_eleven_point_four_le_110000 : Real.exp (11.4 : ℝ) ≤ (110000 : ℝ) := by
  have h11 : Real.exp (11 : ℝ) ≤ (70000 : ℝ) := by
    have hpow : Real.exp (11 : ℝ) = (Real.exp 1) ^ (11 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (11 : ℕ)
      simpa using h.symm
    rw [hpow]
    have hh : (Real.exp 1) ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    exact le_of_lt (calc
      (Real.exp 1) ^ (11 : ℕ) < (2.7182818286 : ℝ) ^ (11 : ℕ) := hh
      _ < 70000 := by norm_num)
  have h04 : Real.exp (0.4 : ℝ) ≤ (1.5 : ℝ) := by
    have h := Real.exp_bound' (x := (0.4 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (11.4 : ℝ) = Real.exp 11 * Real.exp 0.4 := by
      rw [show (11.4 : ℝ) = 11 + 0.4 by norm_num, Real.exp_add]
    _ ≤ 70000 * 1.5 := mul_le_mul h11 h04 (by positivity) (by norm_num)
    _ ≤ 110000 := by norm_num

theorem exp_thirteen_point_sevenfive_le_990000 :
    Real.exp (13.75 : ℝ) ≤ (990000 : ℝ) := by
  have h13 : Real.exp (13 : ℝ) ≤ (450000 : ℝ) := by
    have hpow : Real.exp (13 : ℝ) = (Real.exp 1) ^ (13 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (13 : ℕ)
      simpa using h.symm
    rw [hpow]
    have hh : (Real.exp 1) ^ (13 : ℕ) < (2.7182818286 : ℝ) ^ (13 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    exact le_of_lt (calc
      (Real.exp 1) ^ (13 : ℕ) < (2.7182818286 : ℝ) ^ (13 : ℕ) := hh
      _ < 450000 := by norm_num)
  have h075 : Real.exp (0.75 : ℝ) ≤ (2.2 : ℝ) := by
    have h := Real.exp_bound' (x := (0.75 : ℝ)) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (13.75 : ℝ) = Real.exp 13 * Real.exp 0.75 := by
      rw [show (13.75 : ℝ) = 13 + 0.75 by norm_num, Real.exp_add]
    _ ≤ 450000 * 2.2 := mul_le_mul h13 h075 (by positivity) (by norm_num)
    _ ≤ 990000 := by norm_num

theorem exp_eight_point_three_le_4200 : Real.exp (8.3 : ℝ) ≤ (4200 : ℝ) := by
  have h8 : Real.exp (8 : ℝ) ≤ (3000 : ℝ) := by
    have hpow : Real.exp (8 : ℝ) = (Real.exp 1) ^ (8 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (8 : ℕ)
      simpa using h.symm
    rw [hpow]
    have hh : (Real.exp 1) ^ (8 : ℕ) < (2.7182818286 : ℝ) ^ (8 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    exact le_of_lt (calc
      (Real.exp 1) ^ (8 : ℕ) < (2.7182818286 : ℝ) ^ (8 : ℕ) := hh
      _ < 3000 := by norm_num)
  have h03 : Real.exp (0.3 : ℝ) ≤ (1.37 : ℝ) := by
    have h := Real.exp_bound' (x := (0.3 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    linarith
  calc
    Real.exp (8.3 : ℝ) = Real.exp 8 * Real.exp 0.3 := by
      rw [show (8.3 : ℝ) = 8 + 0.3 by norm_num, Real.exp_add]
    _ ≤ 3000 * 1.37 := mul_le_mul h8 h03 (by positivity) (by norm_num)
    _ ≤ 4200 := by norm_num

theorem R08_pi_half_im_abs_le_eight_point_three :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2)).im| ≤ (8.3 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2)).im =
      Real.pi * (R03R10PolyLower.sR08.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR08_im, abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |5.25 / 2| ≤ 3.1416 * 2.625 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 8.3 := by norm_num

theorem R08_sine_upper_large :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2))‖ ≤ (2101 : ℝ) := by
  have h := sin_upper_of_nonpos_im_of_exp_bound
    (w := -((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2)))
    (K := (8.3 : ℝ)) (E := (4200 : ℝ))
    (by simpa [abs_neg] using R08_pi_half_im_abs_le_eight_point_three)
    (by
      have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2)).im =
          Real.pi * (R03R10PolyLower.sR08.im / 2) := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.div_ofNat_im]
      rw [Complex.neg_im, him, R03R10PolyLower.sR08_im]
      nlinarith [Real.pi_pos])
    exp_eight_point_three_le_4200
  have heq : ‖Complex.sin (-((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2)))‖ =
      ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR08 / 2))‖ := by
    rw [Complex.sin_neg, norm_neg]
  rw [heq] at h
  linarith

theorem R08_gamma_lower_sharp_small :
    (0.005 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR08‖ := by
  have hs : R03R10PolyLower.sR08 = R08GammaUpper.sR08 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R08GammaUpper.sR08 / 2).re := by
    rw [R08GammaUpper.zUpR08_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R08GammaUpper.sR08 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R08GammaUpper.sR08 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R08GammaUpper.sR08_im]
    norm_num
  apply gamma_lower_of_reflection (s := R08GammaUpper.sR08)
    (L := (0.005 : ℝ)) (G := (0.15 : ℝ)) (S := (2101 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R08GammaUpper.gamma_one_sub_half_upper_R08
  · exact R08_sine_upper_large
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

theorem R09_pi_half_im_abs_le_eleven_point_four :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2)).im| ≤ (11.4 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2)).im =
      Real.pi * (R03R10PolyLower.sR09.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR09_im, abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |7.25 / 2| ≤ 3.1416 * 3.625 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 11.4 := by norm_num

theorem R09_sine_upper_large :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2))‖ ≤ (55001 : ℝ) := by
  have h := sin_upper_of_nonpos_im_of_exp_bound
    (w := -((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2)))
    (K := (11.4 : ℝ)) (E := (110000 : ℝ))
    (by simpa [abs_neg] using R09_pi_half_im_abs_le_eleven_point_four)
    (by
      have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2)).im =
          Real.pi * (R03R10PolyLower.sR09.im / 2) := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.div_ofNat_im]
      rw [Complex.neg_im, him, R03R10PolyLower.sR09_im]
      nlinarith [Real.pi_pos])
    exp_eleven_point_four_le_110000
  have heq : ‖Complex.sin (-((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2)))‖ =
      ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR09 / 2))‖ := by
    rw [Complex.sin_neg, norm_neg]
  rw [heq] at h
  linarith

theorem R09_gamma_lower_sharp_small :
    (0.001 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR09‖ := by
  have hs : R03R10PolyLower.sR09 = R09GammaUpper.sR09 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R09GammaUpper.sR09 / 2).re := by
    rw [R09GammaUpper.zUpR09_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R09GammaUpper.sR09 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R09GammaUpper.sR09 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R09GammaUpper.sR09_im]
    norm_num
  apply gamma_lower_of_reflection (s := R09GammaUpper.sR09)
    (L := (0.001 : ℝ)) (G := (0.05 : ℝ)) (S := (55001 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R09GammaUpper.gamma_one_sub_half_upper_R09
  · exact R09_sine_upper_large
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

theorem R10_pi_half_im_abs_le_thirteen_point_sevenfive :
    |((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2)).im| ≤ (13.75 : ℝ) := by
  have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2)).im =
      Real.pi * (R03R10PolyLower.sR10.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im]
  rw [him, R03R10PolyLower.sR10_im, abs_mul]
  have hpi : |Real.pi| ≤ (3.1416 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  calc
    |Real.pi| * |8.75 / 2| ≤ 3.1416 * 4.375 := by
      apply mul_le_mul hpi (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 13.75 := by norm_num

theorem R10_sine_upper_large :
    ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2))‖ ≤ (495001 : ℝ) := by
  have h := sin_upper_of_nonpos_im_of_exp_bound
    (w := -((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2)))
    (K := (13.75 : ℝ)) (E := (990000 : ℝ))
    (by simpa [abs_neg] using R10_pi_half_im_abs_le_thirteen_point_sevenfive)
    (by
      have him : ((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2)).im =
          Real.pi * (R03R10PolyLower.sR10.im / 2) := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.div_ofNat_im]
      rw [Complex.neg_im, him, R03R10PolyLower.sR10_im]
      nlinarith [Real.pi_pos])
    exp_thirteen_point_sevenfive_le_990000
  have heq : ‖Complex.sin (-((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2)))‖ =
      ‖Complex.sin ((Real.pi : ℂ) * (R03R10PolyLower.sR10 / 2))‖ := by
    rw [Complex.sin_neg, norm_neg]
  rw [heq] at h
  linarith

theorem R10_gamma_lower_sharp_small :
    (0.0006 : ℝ) ≤ ‖R00Enclosure.gammaPart R03R10PolyLower.sR10‖ := by
  have hs : R03R10PolyLower.sR10 = R10GammaUpper.sR10 := rfl
  rw [hs]
  have h1w_re : (0 : ℝ) < (1 - R10GammaUpper.sR10 / 2).re := by
    rw [R10GammaUpper.zUpR10_re]
    norm_num
  have hG1_ne : Complex.Gamma (1 - R10GammaUpper.sR10 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (R10GammaUpper.sR10 / 2)) ≠ 0 := by
    apply CellGammaUniform.sin_pi_half_ne_wide
    rw [R10GammaUpper.sR10_im]
    norm_num
  apply gamma_lower_of_reflection (s := R10GammaUpper.sR10)
    (L := (0.0006 : ℝ)) (G := (0.01 : ℝ)) (S := (495001 : ℝ))
  · norm_num
  · norm_num
  · exact hG1_ne
  · exact hsin_ne
  · exact R10GammaUpper.gamma_one_sub_half_upper_R10
  · exact R10_sine_upper_large
  · rw [le_div_iff₀ (by norm_num)]
    have hp : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d4
    nlinarith

/- The revised small-budget centre certificates use the proved Gamma floors.
   They are parameterized only by the still explicit zeta lower input and by
   the derivative bound needed by the rectangle fencing theorem. -/
theorem R09_center_certificate_small_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR09‖) :
    (0.001 : ℝ) + 0.003 * CentralCoverAssembly.R09.radius ≤
      ‖xiShifted CentralCoverAssembly.R09.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤
      ‖R00Enclosure.piPart R03R10PolyLower.sR09‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR09_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R09 R03R10PolyLower.sR09
    0.001 0.003 26.3 (1 / 2 : ℝ) 0.001 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R09_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R09 hpi
    R09_gamma_lower_sharp_small hzeta (by norm_num)

noncomputable def R09_zero_free_certificate_small_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR09‖)
    (hderiv : ∀ w, CentralCoverAssembly.R09.mem w →
      ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)) : XiLocalZeroFreeRect := by
  exact CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R09 0.001
    (by norm_num) 0.003 CentralCoverAssembly.R09_strip_lo
    CentralCoverAssembly.R09_strip_hi hderiv
    (R09_center_certificate_small_of_zeta_ge_half hzeta)

theorem R10_center_certificate_small_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR10‖) :
    (0.001 : ℝ) + 0.003 * CentralCoverAssembly.R10.radius ≤
      ‖xiShifted CentralCoverAssembly.R10.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤
      ‖R00Enclosure.piPart R03R10PolyLower.sR10‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR10_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R10 R03R10PolyLower.sR10
    0.001 0.003 38.3 (1 / 2 : ℝ) 0.0006 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R10_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R10 hpi
    R10_gamma_lower_sharp_small hzeta (by norm_num)

noncomputable def R10_zero_free_certificate_small_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR10‖)
    (hderiv : ∀ w, CentralCoverAssembly.R10.mem w →
      ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)) : XiLocalZeroFreeRect := by
  exact CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R10 0.001
    (by norm_num) 0.003 CentralCoverAssembly.R10_strip_lo
    CentralCoverAssembly.R10_strip_hi hderiv
    (R10_center_certificate_small_of_zeta_ge_half hzeta)


/-! Additional half-zeta off-axis certificates.  These use the unconditional
Gamma lower bounds proved above and expose the remaining analytic inputs as
explicit zeta and derivative bounds. -/

theorem R03_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖) :
    (0.05 : ℝ) + 0.01 * CentralCoverAssembly.R03.radius ≤
      ‖xiShifted CentralCoverAssembly.R03.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR03‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR03_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R03 R03R10PolyLower.sR03
    0.05 0.01 11.3 (1 / 2 : ℝ) 0.025 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R03_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R03 hpi
    R03_gamma_lower_sharp hzeta (by norm_num)

noncomputable def R03_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR03‖)
    (hderiv : ∀ w, CentralCoverAssembly.R03.mem w →
      ‖deriv xiShifted w‖ ≤ (0.01 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R03 0.05
    (by norm_num) 0.01 CentralCoverAssembly.R03_strip_lo
    CentralCoverAssembly.R03_strip_hi hderiv
    (R03_center_certificate_of_zeta_ge_half hzeta)

theorem R05_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖) :
    (0.03 : ℝ) + 0.06 * CentralCoverAssembly.R05.radius ≤
      ‖xiShifted CentralCoverAssembly.R05.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR05‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR05_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R05 R03R10PolyLower.sR05
    0.03 0.06 0.39 (1 / 2 : ℝ) 1.2 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R05_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R05 hpi
    R05_gamma_lower_sharp hzeta (by norm_num)

noncomputable def R05_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR05‖)
    (hderiv : ∀ w, CentralCoverAssembly.R05.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R05 0.03
    (by norm_num) 0.06 CentralCoverAssembly.R05_strip_lo
    CentralCoverAssembly.R05_strip_hi hderiv
    (R05_center_certificate_of_zeta_ge_half hzeta)

theorem R06_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖) :
    (0.03 : ℝ) + 0.06 * CentralCoverAssembly.R06.radius ≤
      ‖xiShifted CentralCoverAssembly.R06.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR06‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR06_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R06 R03R10PolyLower.sR06
    0.03 0.06 0.88 (1 / 2 : ℝ) 0.52 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R06_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R06 hpi
    R06_gamma_lower_sharp hzeta (by norm_num)

noncomputable def R06_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR06‖)
    (hderiv : ∀ w, CentralCoverAssembly.R06.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R06 0.03
    (by norm_num) 0.06 CentralCoverAssembly.R06_strip_lo
    CentralCoverAssembly.R06_strip_hi hderiv
    (R06_center_certificate_of_zeta_ge_half hzeta)

theorem R07_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖) :
    (0.015 : ℝ) + 0.04 * CentralCoverAssembly.R07.radius ≤
      ‖xiShifted CentralCoverAssembly.R07.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR07‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR07_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R07 R03R10PolyLower.sR07
    0.015 0.04 5.35 (1 / 2 : ℝ) 0.052 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R07_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R07 hpi
    R07_gamma_lower_sharp hzeta (by norm_num)

noncomputable def R07_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR07‖)
    (hderiv : ∀ w, CentralCoverAssembly.R07.mem w →
      ‖deriv xiShifted w‖ ≤ (0.04 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R07 0.015
    (by norm_num) 0.04 CentralCoverAssembly.R07_strip_lo
    CentralCoverAssembly.R07_strip_hi hderiv
    (R07_center_certificate_of_zeta_ge_half hzeta)

theorem R08_center_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR08‖) :
    (0.001 : ℝ) + 0.001 * CentralCoverAssembly.R08.radius ≤
      ‖xiShifted CentralCoverAssembly.R08.center‖ := by
  have hpi : ((1 / 2 : ℝ) : ℝ) ≤ ‖R00Enclosure.piPart R03R10PolyLower.sR08‖ := by
    exact CellUniform.pi_lower_of_re (by rw [R03R10PolyLower.sR08_re]; norm_num)
  exact center_certificate_of_components CentralCoverAssembly.R08 R03R10PolyLower.sR08
    0.001 0.001 13.8 (1 / 2 : ℝ) 0.005 0.5 rfl (by norm_num)
    (le_of_lt CentralCoverAssembly.R08_radius_lt) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R03R10PolyLower.poly_lower_R08 hpi
    R08_gamma_lower_sharp_small hzeta (by norm_num)

noncomputable def R08_zero_free_certificate_of_zeta_ge_half
    (hzeta : (0.5 : ℝ) ≤ ‖zeta R03R10PolyLower.sR08‖)
    (hderiv : ∀ w, CentralCoverAssembly.R08.mem w →
      ‖deriv xiShifted w‖ ≤ (0.001 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R08 0.001
    (by norm_num) 0.001 CentralCoverAssembly.R08_strip_lo
    CentralCoverAssembly.R08_strip_hi hderiv
    (R08_center_certificate_of_zeta_ge_half hzeta)

#print axioms R02_pi_lower_tight
#print axioms R02_center_certificate_of_zeta_ge_one
#print axioms R02_zero_free_certificate_of_zeta_ge_one

end Door3OffAxis

open Complex Real
noncomputable section

namespace Door3OffAxis

/- The positive-height R10 center is the conjugate of the R00 center.  This
identity transports any rigorously proved norm enclosure at R00 to R10. -/
theorem R10_zeta_norm_eq_R00 :
    ‖zeta R03R10PolyLower.sR10‖ = ‖zeta zetaCellS0‖ := by
  have hs : star zetaCellS0 = R03R10PolyLower.sR10 := by
    apply Complex.ext
    · change zetaCellS0.re = R03R10PolyLower.sR10.re
      rw [zetaCellS0_re, R03R10PolyLower.sR10_re]
    · change -zetaCellS0.im = R03R10PolyLower.sR10.im
      rw [zetaCellS0_im, R03R10PolyLower.sR10_im]
      norm_num
  rw [← hs]
  change ‖riemannZeta (star zetaCellS0)‖ = ‖riemannZeta zetaCellS0‖
  change ‖riemannZeta ((starRingEnd ℂ) zetaCellS0)‖ = ‖riemannZeta zetaCellS0‖
  rw [riemannZeta_conj]
  simp

/-!
This record is the exact finite-data interface required by the unconditional
eta-pair continuation theorem.  It deliberately stores the finite sum and
the tail/factor bounds as propositions in `ℝ`; no Float value is ever coerced
into a theorem.  Once a generated interval proof supplies these fields, the
resulting lower bound is an ordinary kernel theorem.
-/
structure FiniteZetaLowerCertificate (s : ℂ) where
  N : ℕ
  S : ℂ
  slow : ℝ
  rtail : ℝ
  cF : ℝ
  hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm s k
  hSlow : slow ≤ ‖S‖
  hTail : ‖(∑' m, etaPairTerm s m) - S‖ ≤ rtail
  hcFpos : 0 < cF
  hFac : ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - s))‖ ≤ cF

/- The positivity and `Re s ≠ 1` premises are concrete center facts; this
version leaves them explicit so the record is useful for every off-axis center. -/
theorem FiniteZetaLowerCertificate.lower_of_re
    {s : ℂ} (C : FiniteZetaLowerCertificate s)
    (hs : 0 < s.re) (hre : s.re ≠ 1) :
    (C.slow - C.rtail) / C.cF ≤ ‖zeta s‖ := by
  have h := zeta_lower_of_Sn_tail_factor hs hre C.N C.S C.hSdef C.slow C.hSlow
    C.rtail C.hTail C.cF C.hcFpos C.hFac
  simpa only [zeta] using h

/- The existing unconditional eta-pair tail and factor estimates package the
R00 finite certificate completely; the only supplied field is the genuine
finite-sum lower bound. -/
noncomputable def R00_finite_zeta_certificate
    (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 2097152),
      etaDirichletTerm zetaCellS0 k)
    (hSlow : (1 / 5 : ℝ) ≤ ‖Slarge‖) :
    FiniteZetaLowerCertificate zetaCellS0 :=
  { N := 2 * 2097152
    S := Slarge
    slow := 1 / 5
    rtail := 0.1
    cF := 13 / 5
    hSdef := hSdef
    hSlow := hSlow
    hTail := by
      rw [hSdef]
      exact zetaCellS0_tail_2097152_le
    hcFpos := by norm_num
    hFac := etaFactor_upper_S0 }

theorem R00_finite_zeta_certificate_lower
    (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 2097152),
      etaDirichletTerm zetaCellS0 k)
    (hSlow : (1 / 5 : ℝ) ≤ ‖Slarge‖) :
    (1 / 26 : ℝ) ≤ ‖zeta zetaCellS0‖ := by
  have h := (R00_finite_zeta_certificate Slarge hSdef hSlow).lower_of_re
    zetaCellS0_pos (by rw [zetaCellS0_re]; norm_num)
  have heq : ((R00_finite_zeta_certificate Slarge hSdef hSlow).slow -
      (R00_finite_zeta_certificate Slarge hSdef hSlow).rtail) /
      (R00_finite_zeta_certificate Slarge hSdef hSlow).cF =
      (1 / 26 : ℝ) := by
    simp [R00_finite_zeta_certificate]
    norm_num
  rw [heq] at h
  exact h

noncomputable def R00_reflected_finite_zeta_certificate
    (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 1024),
      etaDirichletTerm (1 - zetaCellS0) k)
    (hSlow : (1 / 3 : ℝ) ≤ ‖Slarge‖) :
    FiniteZetaLowerCertificate (1 - zetaCellS0) :=
  { N := 2 * 1024
    S := Slarge
    slow := 1 / 3
    rtail := 4 / 15
    cF := 13 / 5
    hSdef := hSdef
    hSlow := hSlow
    hTail := by
      rw [hSdef]
      exact zetaRefl_tail_1024_le
    hcFpos := by norm_num
    hFac := etaFactor_upper_S1refl }

theorem R00_reflected_finite_zeta_certificate_lower
    (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 1024),
      etaDirichletTerm (1 - zetaCellS0) k)
    (hSlow : (1 / 3 : ℝ) ≤ ‖Slarge‖) :
    (1 / 39 : ℝ) ≤ ‖zeta (1 - zetaCellS0)‖ := by
  have h := (R00_reflected_finite_zeta_certificate Slarge hSdef hSlow).lower_of_re
    zetaRefl_pos (by rw [zetaRefl_re]; norm_num)
  have heq : ((R00_reflected_finite_zeta_certificate Slarge hSdef hSlow).slow -
      (R00_reflected_finite_zeta_certificate Slarge hSdef hSlow).rtail) /
      (R00_reflected_finite_zeta_certificate Slarge hSdef hSlow).cF =
      (1 / 39 : ℝ) := by
    simp [R00_reflected_finite_zeta_certificate]
    norm_num
  rw [heq] at h
  exact h

theorem R00_zeta_lower_of_reflected_finite_certificate
    (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 1024),
      etaDirichletTerm (1 - zetaCellS0) k)
    (hSlow : (1 / 3 : ℝ) ≤ ‖Slarge‖) :
    (1 / 2340000000 : ℝ) ≤ ‖zeta zetaCellS0‖ := by
  exact zeta_S0_lower_of_S1
    (R00_reflected_finite_zeta_certificate_lower Slarge hSdef hSlow)

theorem R02_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R02Uniform.sR02)
    (hOne : (1 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.002 : ℝ) + 0.07 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  apply R02_center_certificate_of_zeta_ge_one
  exact hOne.trans (C.lower_of_re (by rw [R02Uniform.sR02_re]; norm_num)
    (by rw [R02Uniform.sR02_re]; norm_num))

theorem R03_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR03)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.05 : ℝ) + 0.01 * CentralCoverAssembly.R03.radius ≤
      ‖xiShifted CentralCoverAssembly.R03.center‖ :=
  R03_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR03_re]; norm_num)
      (by rw [R03R10PolyLower.sR03_re]; norm_num)))

theorem R04_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR04)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.05 : ℝ) + 0.07 * CentralCoverAssembly.R04.radius ≤
      ‖xiShifted CentralCoverAssembly.R04.center‖ :=
  R04_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR04_re]; norm_num)
      (by rw [R03R10PolyLower.sR04_re]; norm_num)))

theorem R05_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR05)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.03 : ℝ) + 0.06 * CentralCoverAssembly.R05.radius ≤
      ‖xiShifted CentralCoverAssembly.R05.center‖ :=
  R05_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR05_re]; norm_num)
      (by rw [R03R10PolyLower.sR05_re]; norm_num)))

theorem R06_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR06)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.03 : ℝ) + 0.06 * CentralCoverAssembly.R06.radius ≤
      ‖xiShifted CentralCoverAssembly.R06.center‖ :=
  R06_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR06_re]; norm_num)
      (by rw [R03R10PolyLower.sR06_re]; norm_num)))

theorem R07_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR07)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.015 : ℝ) + 0.04 * CentralCoverAssembly.R07.radius ≤
      ‖xiShifted CentralCoverAssembly.R07.center‖ :=
  R07_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR07_re]; norm_num)
      (by rw [R03R10PolyLower.sR07_re]; norm_num)))

theorem R08_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR08)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.001 : ℝ) + 0.001 * CentralCoverAssembly.R08.radius ≤
      ‖xiShifted CentralCoverAssembly.R08.center‖ :=
  R08_center_certificate_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR08_re]; norm_num)
      (by rw [R03R10PolyLower.sR08_re]; norm_num)))

theorem R09_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR09)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.001 : ℝ) + 0.003 * CentralCoverAssembly.R09.radius ≤
      ‖xiShifted CentralCoverAssembly.R09.center‖ :=
  R09_center_certificate_small_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR09_re]; norm_num)
      (by rw [R03R10PolyLower.sR09_re]; norm_num)))

theorem R10_center_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR10)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.001 : ℝ) + 0.003 * CentralCoverAssembly.R10.radius ≤
      ‖xiShifted CentralCoverAssembly.R10.center‖ :=
  R10_center_certificate_small_of_zeta_ge_half
    (hHalf.trans (C.lower_of_re (by rw [R03R10PolyLower.sR10_re]; norm_num)
      (by rw [R03R10PolyLower.sR10_re]; norm_num)))

/- A finite eta certificate at the reflected R00 point is enough for the R10
center, by the conjugation identity above. -/
theorem R10_center_certificate_of_R00_finite_zeta
    (C : FiniteZetaLowerCertificate zetaCellS0)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF) :
    (0.001 : ℝ) + 0.003 * CentralCoverAssembly.R10.radius ≤
      ‖xiShifted CentralCoverAssembly.R10.center‖ := by
  apply R10_center_certificate_small_of_zeta_ge_half
  have h0 : (0.5 : ℝ) ≤ ‖zeta zetaCellS0‖ :=
    hHalf.trans (C.lower_of_re (by rw [zetaCellS0_re]; norm_num)
      (by rw [zetaCellS0_re]; norm_num))
  rw [R10_zeta_norm_eq_R00]
  exact h0

/- Complete rectangle packages fed by the same finite certificate and the
uniform derivative enclosure on the corresponding cell. -/
noncomputable def R03_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR03)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R03.mem w →
      ‖deriv xiShifted w‖ ≤ (0.01 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R03 0.05
    (by norm_num) 0.01 CentralCoverAssembly.R03_strip_lo
    CentralCoverAssembly.R03_strip_hi hderiv
    (R03_center_certificate_of_finite_zeta C hHalf)

noncomputable def R04_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR04)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R04.mem w →
      ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.R04_zeroFree_of_bounds
    ⟨R04_center_certificate_of_finite_zeta C hHalf, hderiv⟩

noncomputable def R05_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR05)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R05.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R05 0.03
    (by norm_num) 0.06 CentralCoverAssembly.R05_strip_lo
    CentralCoverAssembly.R05_strip_hi hderiv
    (R05_center_certificate_of_finite_zeta C hHalf)

noncomputable def R06_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR06)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R06.mem w →
      ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R06 0.03
    (by norm_num) 0.06 CentralCoverAssembly.R06_strip_lo
    CentralCoverAssembly.R06_strip_hi hderiv
    (R06_center_certificate_of_finite_zeta C hHalf)

noncomputable def R07_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR07)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R07.mem w →
      ‖deriv xiShifted w‖ ≤ (0.04 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R07 0.015
    (by norm_num) 0.04 CentralCoverAssembly.R07_strip_lo
    CentralCoverAssembly.R07_strip_hi hderiv
    (R07_center_certificate_of_finite_zeta C hHalf)

noncomputable def R08_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR08)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R08.mem w →
      ‖deriv xiShifted w‖ ≤ (0.001 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R08 0.001
    (by norm_num) 0.001 CentralCoverAssembly.R08_strip_lo
    CentralCoverAssembly.R08_strip_hi hderiv
    (R08_center_certificate_of_finite_zeta C hHalf)

noncomputable def R09_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR09)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R09.mem w →
      ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R09 0.001
    (by norm_num) 0.003 CentralCoverAssembly.R09_strip_lo
    CentralCoverAssembly.R09_strip_hi hderiv
    (R09_center_certificate_of_finite_zeta C hHalf)

noncomputable def R10_zero_free_certificate_of_finite_zeta
    (C : FiniteZetaLowerCertificate R03R10PolyLower.sR10)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R10.mem w →
      ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R10 0.001
    (by norm_num) 0.003 CentralCoverAssembly.R10_strip_lo
    CentralCoverAssembly.R10_strip_hi hderiv
    (R10_center_certificate_of_finite_zeta C hHalf)

noncomputable def R10_zero_free_certificate_of_R00_finite_zeta
    (C : FiniteZetaLowerCertificate zetaCellS0)
    (hHalf : (0.5 : ℝ) ≤ (C.slow - C.rtail) / C.cF)
    (hderiv : ∀ w, CentralCoverAssembly.R10.mem w →
      ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip CentralCoverAssembly.R10 0.001
    (by norm_num) 0.003 CentralCoverAssembly.R10_strip_lo
    CentralCoverAssembly.R10_strip_hi hderiv
    (R10_center_certificate_of_R00_finite_zeta C hHalf)

/- A single bundle is convenient for generated certificate files: the
finite eta data and the derivative enclosures remain explicit fields, while
this constructor assembles the eight corresponding zero-free rectangles. -/
structure OffAxisFiniteCertificateBundle where
  C03 : FiniteZetaLowerCertificate R03R10PolyLower.sR03
  C04 : FiniteZetaLowerCertificate R03R10PolyLower.sR04
  C05 : FiniteZetaLowerCertificate R03R10PolyLower.sR05
  C06 : FiniteZetaLowerCertificate R03R10PolyLower.sR06
  C07 : FiniteZetaLowerCertificate R03R10PolyLower.sR07
  C08 : FiniteZetaLowerCertificate R03R10PolyLower.sR08
  C09 : FiniteZetaLowerCertificate R03R10PolyLower.sR09
  C10 : FiniteZetaLowerCertificate R03R10PolyLower.sR10
  h03 : (0.5 : ℝ) ≤ (C03.slow - C03.rtail) / C03.cF
  h04 : (0.5 : ℝ) ≤ (C04.slow - C04.rtail) / C04.cF
  h05 : (0.5 : ℝ) ≤ (C05.slow - C05.rtail) / C05.cF
  h06 : (0.5 : ℝ) ≤ (C06.slow - C06.rtail) / C06.cF
  h07 : (0.5 : ℝ) ≤ (C07.slow - C07.rtail) / C07.cF
  h08 : (0.5 : ℝ) ≤ (C08.slow - C08.rtail) / C08.cF
  h09 : (0.5 : ℝ) ≤ (C09.slow - C09.rtail) / C09.cF
  h10 : (0.5 : ℝ) ≤ (C10.slow - C10.rtail) / C10.cF
  d03 : ∀ w, CentralCoverAssembly.R03.mem w → ‖deriv xiShifted w‖ ≤ (0.01 : ℝ)
  d04 : ∀ w, CentralCoverAssembly.R04.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
  d05 : ∀ w, CentralCoverAssembly.R05.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
  d06 : ∀ w, CentralCoverAssembly.R06.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
  d07 : ∀ w, CentralCoverAssembly.R07.mem w → ‖deriv xiShifted w‖ ≤ (0.04 : ℝ)
  d08 : ∀ w, CentralCoverAssembly.R08.mem w → ‖deriv xiShifted w‖ ≤ (0.001 : ℝ)
  d09 : ∀ w, CentralCoverAssembly.R09.mem w → ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)
  d10 : ∀ w, CentralCoverAssembly.R10.mem w → ‖deriv xiShifted w‖ ≤ (0.003 : ℝ)

noncomputable def OffAxisFiniteCertificateBundle.rects
    (B : OffAxisFiniteCertificateBundle) :
    List XiLocalZeroFreeRect :=
  [ R03_zero_free_certificate_of_finite_zeta B.C03 B.h03 B.d03
  , R04_zero_free_certificate_of_finite_zeta B.C04 B.h04 B.d04
  , R05_zero_free_certificate_of_finite_zeta B.C05 B.h05 B.d05
  , R06_zero_free_certificate_of_finite_zeta B.C06 B.h06 B.d06
  , R07_zero_free_certificate_of_finite_zeta B.C07 B.h07 B.d07
  , R08_zero_free_certificate_of_finite_zeta B.C08 B.h08 B.d08
  , R09_zero_free_certificate_of_finite_zeta B.C09 B.h09 B.d09
  , R10_zero_free_certificate_of_finite_zeta B.C10 B.h10 B.d10 ]

theorem OffAxisFiniteCertificateBundle.rects_length
    (B : OffAxisFiniteCertificateBundle) : B.rects.length = 8 := by
  simp [OffAxisFiniteCertificateBundle.rects]

#print axioms FiniteZetaLowerCertificate.lower_of_re
#print axioms R00_finite_zeta_certificate_lower
#print axioms R00_reflected_finite_zeta_certificate_lower
#print axioms R00_zeta_lower_of_reflected_finite_certificate
#print axioms R03_center_certificate_of_finite_zeta
#print axioms R10_zeta_norm_eq_R00
#print axioms OffAxisFiniteCertificateBundle.rects_length

end Door3OffAxis

namespace Door3OffAxis

/-- R03 two-term eta partial sum in closed form (`S₂ = 1 - (2^s)⁻¹`). -/
theorem R03_eta_S2_eq :
    (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR03 k)
      = 1 - ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR03)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR03 k)
      = etaDirichletTerm R03R10PolyLower.sR03 0 + etaDirichletTerm R03R10PolyLower.sR03 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  have h0 : etaDirichletTerm R03R10PolyLower.sR03 0 = 1 := by
    have h01 : (0 + 1 : ℕ) = 1 := rfl
    have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by
      rw [h01, Nat.cast_one]
    simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]
  have h1 : etaDirichletTerm R03R10PolyLower.sR03 1
      = -((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR03)⁻¹) := by
    unfold etaDirichletTerm
    rw [pow_one]
    rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
    rw [neg_div, one_div]
  rw [hsum, h0, h1]
  ring

/-- Modulus of the R03 second eta term (`2^{-0.395} ≤ 4/5`, from `5/4 ≤ 2^0.395`). -/
theorem R03_eta_second_norm_le :
    ‖((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR03)⁻¹)‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, R03R10PolyLower.sR03_re]
  have hge := zetaCellS0_rpow_0395_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.395 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R03 finite-sum lower bound (`1/5 ≤ ‖S₂‖`, reverse triangle). -/
theorem R03_eta_S2_norm_ge :
    (1 / 5 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR03 k‖ := by
  rw [R03_eta_S2_eq]
  have hX := R03_eta_second_norm_le
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR03)⁻¹))
    ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR03)⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Genuine R03 eta-factor upper bound (`‖1 - 2^{1-s}‖ ≤ 13/5`, needs only `Re = 0.395`). -/
theorem R03_etaFactor_upper :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR03))‖ ≤ 13 / 5 := by
  have hre : ((1 : ℂ) - R03R10PolyLower.sR03).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R03R10PolyLower.sR03_re]
    norm_num
  have hY : ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR03)‖ ≤ 8 / 5 := by
    rw [two_cpow_norm, hre]
    exact zetaCellS0_rpow_0605_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR03)‖
        ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR03)‖ :=
          norm_sub_le _ _
    _ ≤ 13 / 5 := by
          rw [norm_one]
          linarith [hY]

/-- R03 center norm upper (`‖sR03‖ ≤ 4.77` from `0.395² + 4.75² ≤ 4.77²`). -/
theorem R03_s_norm_le : ‖R03R10PolyLower.sR03‖ ≤ (4.77 : ℝ) := by
  have hsq : ‖R03R10PolyLower.sR03‖ ^ 2 ≤ (4.77 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, R03R10PolyLower.sR03_re,
      R03R10PolyLower.sR03_im]
    norm_num
  have hnn : (0 : ℝ) ≤ ‖R03R10PolyLower.sR03‖ := norm_nonneg _
  calc ‖R03R10PolyLower.sR03‖ = Real.sqrt (‖R03R10PolyLower.sR03‖ ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((4.77 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (4.77 : ℝ) := Real.sqrt_sq (by norm_num)

/-- Genuine R03 paired tail at `M = 1` (`‖G - S₂‖ ≤ 61/5`, via `zetaCell_even_remainder_le`). -/
theorem R03_eta_tail_1_le :
    ‖(∑' m, etaPairTerm R03R10PolyLower.sR03 m)
      - (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR03 k)‖ ≤
      (61 / 5 : ℝ) := by
  have hs : 0 < R03R10PolyLower.sR03.re := by
    rw [R03R10PolyLower.sR03_re]
    norm_num
  have hC : ‖R03R10PolyLower.sR03‖ ≤ (4.77 : ℝ) := R03_s_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1 (by norm_num)
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at hgen
  have hre : R03R10PolyLower.sR03.re = (0.395 : ℝ) := R03R10PolyLower.sR03_re
  rw [hre] at hgen
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow] at hgen
  have hle : (4.77 : ℝ) * (1 / (0.395 : ℝ)) ≤ (61 / 5 : ℝ) := by norm_num
  linarith

/-- Genuine (fully proved-field) R03 finite zeta lower certificate at `N = 2`.
Its `(slow - rtail) / cF` ratio is negative, so the `0.5` threshold stays open:
the next step is a larger-`N` slow bound plus a small-`M` tail decay bound. -/
noncomputable def R03_genuine_finite_zeta_certificate :
    FiniteZetaLowerCertificate R03R10PolyLower.sR03 :=
  { N := 2
    S := ∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR03 k
    slow := 1 / 5
    rtail := 61 / 5
    cF := 13 / 5
    hSdef := rfl
    hSlow := R03_eta_S2_norm_ge
    hTail := R03_eta_tail_1_le
    hcFpos := by norm_num
    hFac := R03_etaFactor_upper }

#print axioms R03_eta_S2_eq
#print axioms R03_eta_S2_norm_ge
#print axioms R03_etaFactor_upper
#print axioms R03_s_norm_le
#print axioms R03_eta_tail_1_le
#print axioms R03_genuine_finite_zeta_certificate

/-- R05 center norm upper (`‖sR05‖ ≤ 0.85` from `0.395² + 0.75² ≤ 0.85²`). -/
theorem R05_s_norm_le : ‖R03R10PolyLower.sR05‖ ≤ (0.85 : ℝ) := by
  have hsq : ‖R03R10PolyLower.sR05‖ ^ 2 ≤ (0.85 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, R03R10PolyLower.sR05_re,
      R03R10PolyLower.sR05_im]
    norm_num
  have hnn : (0 : ℝ) ≤ ‖R03R10PolyLower.sR05‖ := norm_nonneg _
  calc ‖R03R10PolyLower.sR05‖ = Real.sqrt (‖R03R10PolyLower.sR05‖ ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((0.85 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (0.85 : ℝ) := Real.sqrt_sq (by norm_num)

/-- Cast helper: `((1024 : ℕ) : ℝ) = 2 ^ (10 : ℕ)`. -/
theorem R05_M1024_eq : ((((1024 : ℕ)) : ℝ)) = (2 : ℝ) ^ (10 : ℕ) := by
  norm_num

/-- Cleared integer-pow lemma: `(16/15)^20 ≥ 2` via small-step lower bounds. -/
theorem R05_pow_16_15_20_ge_two : (2 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (20 : ℕ) := by
  have h106 : (1.06 : ℝ) ≤ (16 / 15 : ℝ) := by norm_num
  have h106nn : (0 : ℝ) ≤ (1.06 : ℝ) := by norm_num
  have h112 : (1.12 : ℝ) ≤ ((1.06 : ℝ)) ^ (2 : ℕ) := by norm_num
  have h2le : ((1.06 : ℝ)) ^ (2 : ℕ) ≤ ((16 / 15 : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ h106nn h106 2
  have g2 : (1.12 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (2 : ℕ) := le_trans h112 h2le
  have h125 : (1.25 : ℝ) ≤ ((1.12 : ℝ)) ^ (2 : ℕ) := by norm_num
  have h4le : ((1.12 : ℝ)) ^ (2 : ℕ) ≤ ((((16 / 15 : ℝ)) ^ (2 : ℕ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) g2 2
  have h44 : ((((16 / 15 : ℝ)) ^ (2 : ℕ))) ^ (2 : ℕ) =
      ((16 / 15 : ℝ)) ^ (4 : ℕ) := by
    rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num]
  have g4 : (1.25 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (4 : ℕ) := by
    rw [← h44]
    exact le_trans h125 h4le
  have h4nn : (0 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (4 : ℕ) := pow_nonneg (by norm_num) _
  have h5mul : ((16 / 15 : ℝ)) ^ (4 : ℕ) * (16 / 15 : ℝ) =
      ((16 / 15 : ℝ)) ^ (5 : ℕ) := by
    have hps := pow_succ ((16 / 15 : ℝ)) (4 : ℕ)
    rw [show (4 + 1 : ℕ) = 5 by norm_num] at hps
    exact hps.symm
  have h5le : (1.25 : ℝ) * (1.06 : ℝ) ≤
      ((16 / 15 : ℝ)) ^ (4 : ℕ) * (16 / 15 : ℝ) :=
    mul_le_mul g4 h106 (by norm_num) h4nn
  have h132 : (1.32 : ℝ) ≤ (1.25 : ℝ) * (1.06 : ℝ) := by norm_num
  have g5 : (1.32 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (5 : ℕ) := by
    rw [← h5mul]
    exact le_trans h132 h5le
  have h174 : (1.74 : ℝ) ≤ ((1.32 : ℝ)) ^ (2 : ℕ) := by norm_num
  have h10le : ((1.32 : ℝ)) ^ (2 : ℕ) ≤
      ((((16 / 15 : ℝ)) ^ (5 : ℕ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) g5 2
  have h1010 : ((((16 / 15 : ℝ)) ^ (5 : ℕ))) ^ (2 : ℕ) =
      ((16 / 15 : ℝ)) ^ (10 : ℕ) := by
    rw [← pow_mul, show (5 * 2 : ℕ) = 10 by norm_num]
  have g10 : (1.74 : ℝ) ≤ ((16 / 15 : ℝ)) ^ (10 : ℕ) := by
    rw [← h1010]
    exact le_trans h174 h10le
  have h2low : (2 : ℝ) ≤ ((1.74 : ℝ)) ^ (2 : ℕ) := by norm_num
  have h20le : ((1.74 : ℝ)) ^ (2 : ℕ) ≤
      ((((16 / 15 : ℝ)) ^ (10 : ℕ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) g10 2
  have h2020 : ((((16 / 15 : ℝ)) ^ (10 : ℕ))) ^ (2 : ℕ) =
      ((16 / 15 : ℝ)) ^ (20 : ℕ) := by
    rw [← pow_mul, show (10 * 2 : ℕ) = 20 by norm_num]
  rw [← h2020]
  exact le_trans h2low h20le

/-- Small rpow upper: `2^0.05 ≤ 16/15` (cleared via `(16/15)^20 ≥ 2`). -/
theorem R05_rpow_005_le : (2 : ℝ) ^ (0.05 : ℝ) ≤ (16 / 15 : ℝ) := by
  by_contra hle
  have hlt : (16 / 15 : ℝ) < (2 : ℝ) ^ (0.05 : ℝ) := lt_of_not_ge hle
  have hle_pow : ((16 / 15 : ℝ)) ^ (20 : ℕ) ≤
      ((((2 : ℝ) ^ (0.05 : ℝ))) ^ (20 : ℕ)) :=
    pow_le_pow_left₀ (by norm_num) hlt.le 20
  have h2_eq : ((((2 : ℝ) ^ (0.05 : ℝ))) ^ (20 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : (0.05 : ℝ) * ((((20 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [h2_eq] at hle_pow
  have hge := R05_pow_16_15_20_ge_two
  linarith

/-- Rpow lower: `15 ≤ ((1024 : ℕ) : ℝ)^0.395` via `2^3.95 = 16/2^0.05`. -/
theorem R05_M1024_rpow_ge :
    (15 : ℝ) ≤ ((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)) := by
  rw [R05_M1024_eq]
  have h1 : (((2 : ℝ) ^ (10 : ℕ)) ^ (0.395 : ℝ)) =
      (2 : ℝ) ^ (((((10 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have e_exp : ((((10 : ℕ)) : ℝ)) * (0.395 : ℝ) = 4 - (0.05 : ℝ) := by norm_num
  rw [e_exp]
  have hsub : (2 : ℝ) ^ (4 - (0.05 : ℝ)) =
      (2 : ℝ) ^ (4 : ℝ) / (2 : ℝ) ^ (0.05 : ℝ) := by
    rw [Real.rpow_sub (by norm_num)]
  rw [hsub]
  have e4 : (4 : ℝ) = ((((4 : ℕ)) : ℝ)) := by norm_num
  have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
    rw [e4, Real.rpow_natCast]
    norm_num
  rw [h16]
  have h005 := R05_rpow_005_le
  have h005pos : (0 : ℝ) < (2 : ℝ) ^ (0.05 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h15 : (15 : ℝ) ≤ 16 / ((2 : ℝ) ^ (0.05 : ℝ)) := by
    rw [le_div_iff₀ h005pos]
    have hmul : (15 : ℝ) * ((2 : ℝ) ^ (0.05 : ℝ)) ≤ 15 * (16 / 15) :=
      mul_le_mul_of_nonneg_left h005 (by norm_num)
    have heq : (15 : ℝ) * (16 / 15) = 16 := by norm_num
    linarith
  linarith

/-- R05 `M = 1024` tail-decay bound: `0.85·(1024^-0.395)/0.395 ≤ 3/20`. -/
theorem R05_r_1024_le :
    (0.85 : ℝ) * ((((((1024 : ℕ)) : ℝ) ^ (-0.395 : ℝ))) / (0.395 : ℝ)) ≤
      (3 / 20 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1024 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := R05_M1024_rpow_ge
  have hrw : ((((1024 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) =
      (((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ ≤ (15 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ / (0.395 : ℝ) ≤
      (15 : ℝ)⁻¹ / (0.395 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (0.85 : ℝ) * ((((((1024 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ /
      (0.395 : ℝ)) ≤ (0.85 : ℝ) * ((15 : ℝ)⁻¹ / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (0.85 : ℝ) * ((15 : ℝ)⁻¹ / (0.395 : ℝ)) ≤ (3 / 20 : ℝ) := by
    norm_num
  linarith

/-- Genuine R05 paired tail at `M = 1024` (`‖G - S₂₀₄₈‖ ≤ 3/20`). -/
theorem R05_eta_tail_1024_le :
    ‖(∑' m, etaPairTerm R03R10PolyLower.sR05 m) -
      (∑ k ∈ Finset.range (2 * 1024), etaDirichletTerm R03R10PolyLower.sR05 k)‖ ≤
      (3 / 20 : ℝ) := by
  have hs : 0 < R03R10PolyLower.sR05.re := by
    rw [R03R10PolyLower.sR05_re]
    norm_num
  have hC : ‖R03R10PolyLower.sR05‖ ≤ (0.85 : ℝ) := R05_s_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1024 (by norm_num)
  have hre : R03R10PolyLower.sR05.re = (0.395 : ℝ) := R03R10PolyLower.sR05_re
  rw [hre] at hgen
  have hr := R05_r_1024_le
  linarith

#print axioms R05_s_norm_le
#print axioms R05_M1024_eq
#print axioms R05_pow_16_15_20_ge_two
#print axioms R05_rpow_005_le
#print axioms R05_M1024_rpow_ge
#print axioms R05_r_1024_le
#print axioms R05_eta_tail_1024_le

end Door3OffAxis

namespace Door3OffAxis

/-- R05 two-term eta partial sum in closed form (`S₂ = 1 - (2^s)⁻¹`). -/
theorem R05_eta_S2_eq :
    (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k)
      = 1 - ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR05)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k)
      = etaDirichletTerm R03R10PolyLower.sR05 0 + etaDirichletTerm R03R10PolyLower.sR05 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  have h0 : etaDirichletTerm R03R10PolyLower.sR05 0 = 1 := by
    have h01 : (0 + 1 : ℕ) = 1 := rfl
    have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by
      rw [h01, Nat.cast_one]
    simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]
  have h1 : etaDirichletTerm R03R10PolyLower.sR05 1
      = -((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR05)⁻¹) := by
    unfold etaDirichletTerm
    rw [pow_one]
    rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
    rw [neg_div, one_div]
  rw [hsum, h0, h1]
  ring

/-- Modulus of the R05 second eta term (`2^{-0.395} ≤ 4/5`, from `5/4 ≤ 2^0.395`). -/
theorem R05_eta_second_norm_le :
    ‖((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR05)⁻¹)‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, R03R10PolyLower.sR05_re]
  have hge := zetaCellS0_rpow_0395_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.395 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R05 finite-sum lower bound (`1/5 ≤ ‖S₂‖`, reverse triangle). -/
theorem R05_eta_S2_norm_ge :
    (1 / 5 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  rw [R05_eta_S2_eq]
  have hX := R05_eta_second_norm_le
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR05)⁻¹))
    ((((2 : ℕ) : ℂ) ^ R03R10PolyLower.sR05)⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Genuine R05 eta-factor upper bound (`‖1 - 2^{1-s}‖ ≤ 13/5`, needs only `Re = 0.395`). -/
theorem R05_etaFactor_upper :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05))‖ ≤ 13 / 5 := by
  have hre : ((1 : ℂ) - R03R10PolyLower.sR05).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R03R10PolyLower.sR05_re]
    norm_num
  have hY : ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ≤ 8 / 5 := by
    rw [two_cpow_norm, hre]
    exact zetaCellS0_rpow_0605_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖
        ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ :=
          norm_sub_le _ _
    _ ≤ 13 / 5 := by
          rw [norm_one]
          linarith [hY]

/-- Genuine R05 paired tail at `M = 1` (`‖G - S₂‖ ≤ 11/5`, via `zetaCell_even_remainder_le`). -/
theorem R05_eta_tail_1_le :
    ‖(∑' m, etaPairTerm R03R10PolyLower.sR05 m)
      - (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k)‖ ≤
      (11 / 5 : ℝ) := by
  have hs : 0 < R03R10PolyLower.sR05.re := by
    rw [R03R10PolyLower.sR05_re]
    norm_num
  have hC : ‖R03R10PolyLower.sR05‖ ≤ (0.85 : ℝ) := R05_s_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1 (by norm_num)
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at hgen
  have hre : R03R10PolyLower.sR05.re = (0.395 : ℝ) := R03R10PolyLower.sR05_re
  rw [hre] at hgen
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow] at hgen
  have hle : (0.85 : ℝ) * (1 / (0.395 : ℝ)) ≤ (11 / 5 : ℝ) := by norm_num
  linarith

/-- Genuine (fully proved-field) R05 finite zeta lower certificate at `N = 2`. -/
noncomputable def R05_genuine_finite_zeta_certificate :
    FiniteZetaLowerCertificate R03R10PolyLower.sR05 :=
  { N := 2
    S := ∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k
    slow := 1 / 5
    rtail := 11 / 5
    cF := 13 / 5
    hSdef := rfl
    hSlow := R05_eta_S2_norm_ge
    hTail := R05_eta_tail_1_le
    hcFpos := by norm_num
    hFac := R05_etaFactor_upper }

/-- The genuine R05 certificate wired through the API (negative-valued, honest). -/
theorem R05_genuine_zeta_lower :
    ((R05_genuine_finite_zeta_certificate.slow - R05_genuine_finite_zeta_certificate.rtail) /
      R05_genuine_finite_zeta_certificate.cF) ≤ ‖zeta R03R10PolyLower.sR05‖ :=
  R05_genuine_finite_zeta_certificate.lower_of_re
    (by rw [R03R10PolyLower.sR05_re]; norm_num)
    (by rw [R03R10PolyLower.sR05_re]; norm_num)

/-- Exact ratio of the genuine R05 `N = 2` certificate: `(1/5 - 11/5)/(13/5) = -10/13`. -/
theorem R05_genuine_ratio_eq :
    ((R05_genuine_finite_zeta_certificate.slow - R05_genuine_finite_zeta_certificate.rtail) /
      R05_genuine_finite_zeta_certificate.cF) = (-10 / 13 : ℝ) := by
  have h1 : R05_genuine_finite_zeta_certificate.slow = (1 / 5 : ℝ) := rfl
  have h2 : R05_genuine_finite_zeta_certificate.rtail = (11 / 5 : ℝ) := rfl
  have h3 : R05_genuine_finite_zeta_certificate.cF = (13 / 5 : ℝ) := rfl
  rw [h1, h2, h3]
  norm_num

/-- With the banked `M = 1024` tail value (`3/20`) in place of the `M = 1` tail,
the `N = 2` slow value gives ratio exactly `1/52`: magnitude-only bounds cannot
meet the `1/2` threshold (shortfall `25/52`). -/
theorem R05_banked_tail_ratio_eq :
    (((1 / 5 : ℝ) - (3 / 20 : ℝ)) / (13 / 5 : ℝ)) = (1 / 52 : ℝ) := by
  norm_num

theorem R05_banked_tail_ratio_lt_half : (1 / 52 : ℝ) < (1 / 2 : ℝ) := by
  norm_num

/-- Threshold meeting with banked numbers needs `slow ≥ 1/2 * cF + rtail = 29/20`:
the quantified target for the larger-`N` slow bound plus phase-aware factor bound. -/
theorem R05_slow_needed_eq :
    ((1 / 2 : ℝ) * (13 / 5 : ℝ) + (3 / 20 : ℝ)) = (29 / 20 : ℝ) := by
  norm_num

#print axioms R05_eta_S2_eq
#print axioms R05_eta_second_norm_le
#print axioms R05_eta_S2_norm_ge
#print axioms R05_etaFactor_upper
#print axioms R05_eta_tail_1_le
#print axioms R05_genuine_finite_zeta_certificate
#print axioms R05_genuine_zeta_lower
#print axioms R05_genuine_ratio_eq
#print axioms R05_banked_tail_ratio_eq
#print axioms R05_banked_tail_ratio_lt_half
#print axioms R05_slow_needed_eq

end Door3OffAxis

namespace Door3OffAxis

/-- R05 phase-cosine floor (`cos (0.75 * log 2) ≥ 43/50`): `0.75 * log 2 < 0.5199`
from the banked `log 2` upper bound, then `1 - x ^ 2 / 2 ≤ cos x`. -/
theorem R05_phase_cos_lower :
    (43 / 50 : ℝ) ≤ Real.cos (0.75 * Real.log 2) := by
  have hloghi := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : (0 : ℝ) ≤ 0.75 * Real.log 2 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hhi : 0.75 * Real.log 2 < (0.5199 : ℝ) := by linarith
  have hle : 0.75 * Real.log 2 ≤ (0.5199 : ℝ) := le_of_lt hhi
  have hsq : (0.75 * Real.log 2) ^ 2 ≤ (0.5199 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hnn hle 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := 0.75 * Real.log 2)
  have hbase : (43 / 50 : ℝ) ≤ 1 - (0.5199 : ℝ) ^ 2 / 2 := by norm_num
  linarith [hc, hsq, hbase]

/-- Phase-aware R05 eta-factor upper bound (`‖1 - 2 ^ (1 - sR05)‖ ≤ 1`).
With `q = 2 ^ (1 - sR05)`, `‖q‖ = 2 ^ 0.605 ≤ 8 / 5` and
`Re q = 2 ^ 0.605 * cos (0.75 * log 2)`; the phase floor gives
`‖q‖ ≤ 2 * cos (0.75 * log 2)`, hence
`‖1 - q‖ ^ 2 = 1 + ‖q‖ * (‖q‖ - 2 * cos θ) ≤ 1`.
This drops the factor cap `13 / 5 → 1`. -/
theorem R05_etaFactor_phase_le_one :
    ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ≤ (1 : ℝ) := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by rw [hlog]; rfl
  have hwre : ((1 : ℂ) - R03R10PolyLower.sR05).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R03R10PolyLower.sR05_re]
    norm_num
  have hwim : ((1 : ℂ) - R03R10PolyLower.sR05).im = (0.75 : ℝ) := by
    rw [Complex.sub_im, Complex.one_im, R03R10PolyLower.sR05_im]
    norm_num
  have hargre : (Complex.log (2 : ℂ) * ((1 : ℂ) - R03R10PolyLower.sR05)).re =
      Real.log 2 * 0.605 := by
    rw [Complex.mul_re, hlogre, hlogim, hwre, hwim]
    ring
  have hargim : (Complex.log (2 : ℂ) * ((1 : ℂ) - R03R10PolyLower.sR05)).im =
      Real.log 2 * 0.75 := by
    rw [Complex.mul_im, hlogre, hlogim, hwre, hwim]
    ring
  have hqre : ((2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)).re =
      (2 : ℝ) ^ (0.605 : ℝ) * Real.cos (0.75 * Real.log 2) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [Complex.exp_re, hargre, hargim]
    have hexp : Real.exp (Real.log 2 * 0.605) = (2 : ℝ) ^ (0.605 : ℝ) :=
      (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
    rw [hexp]
    have hcos : Real.cos (Real.log 2 * 0.75) = Real.cos (0.75 * Real.log 2) := by
      congr 1
      ring
    rw [hcos]
  have hqnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ =
      (2 : ℝ) ^ (0.605 : ℝ) := by
    rw [two_cpow_norm, hwre]
  have hsqid : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ^ 2 =
      1 + ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ^ 2
        - 2 * ((2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)).re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hq : ‖(2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ^ 2 =
        ((2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)).re ^ 2
          + ((2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hq]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub]
    ring
  have hRle : (2 : ℝ) ^ (0.605 : ℝ) ≤ (8 / 5 : ℝ) := zetaCellS0_rpow_0605_le
  have hRnn : (0 : ℝ) ≤ (2 : ℝ) ^ (0.605 : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcos := R05_phase_cos_lower
  have hRle2 : (2 : ℝ) ^ (0.605 : ℝ) ≤ 2 * Real.cos (0.75 * Real.log 2) := by
    linarith [hRle, hcos]
  have hprod : (2 : ℝ) ^ (0.605 : ℝ)
      * ((2 : ℝ) ^ (0.605 : ℝ) - 2 * Real.cos (0.75 * Real.log 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hRnn (by linarith [hRle2])
  have hsq : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ ^ 2 ≤ 1 := by
    have heq : (1 : ℝ) + ((2 : ℝ) ^ (0.605 : ℝ)) ^ 2
        - 2 * ((2 : ℝ) ^ (0.605 : ℝ) * Real.cos (0.75 * Real.log 2))
        = 1 + (2 : ℝ) ^ (0.605 : ℝ)
          * ((2 : ℝ) ^ (0.605 : ℝ) - 2 * Real.cos (0.75 * Real.log 2)) := by
      ring
    rw [hsqid, hqnorm, hqre]
    linarith [hprod, heq]
  have hnonneg : (0 : ℝ) ≤
      ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R03R10PolyLower.sR05)‖ := norm_nonneg _
  nlinarith [hsq, hnonneg]

/-- With the phase-aware factor cap `cF = 1` and the banked tail `3 / 20`,
threshold meeting needs `slow ≥ 1 / 2 * 1 + 3 / 20 = 13 / 20`
(down from `29 / 20` with the magnitude-only cap `13 / 5`). -/
theorem R05_slow_needed_phase_eq :
    ((1 / 2 : ℝ) * 1 + (3 / 20 : ℝ)) = (13 / 20 : ℝ) := by
  norm_num

/-- Honest residual: the `N = 2` slow value with banked tail and phase-aware
factor gives only `(1 / 5 - 3 / 20) / 1 = 1 / 20 < 1 / 2`, so the larger-`N`
slow bound (`slow ≥ 13 / 20`) remains the exact next task. -/
theorem R05_phase_ratio_S2_eq :
    (((1 / 5 : ℝ) - (3 / 20 : ℝ)) / (1 : ℝ)) = (1 / 20 : ℝ) := by
  norm_num

theorem R05_phase_ratio_S2_lt_half : (1 / 20 : ℝ) < (1 / 2 : ℝ) := by
  norm_num

#print axioms R05_phase_cos_lower
#print axioms R05_etaFactor_phase_le_one
#print axioms R05_slow_needed_phase_eq
#print axioms R05_phase_ratio_S2_eq
#print axioms R05_phase_ratio_S2_lt_half

end Door3OffAxis

namespace Door3OffAxis

/-- R05 cosine upper (`cos (0.75 * log 2) <= 87/100`) via quartic majorant. -/
theorem R05_cos_075log2_upper :
    Real.cos (0.75 * Real.log 2) <= (87 / 100 : Real) := by
  have hloghi := Real.log_two_lt_d9
  have hloglo := Real.log_two_gt_d9
  have hpos : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hx_nn : (0 : Real) <= 0.75 * Real.log 2 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hx_hi : 0.75 * Real.log 2 <= (0.52 : Real) := by linarith
  have hx_lo : (0.519 : Real) <= 0.75 * Real.log 2 := by linarith
  have hcos := CG_cos_le_quartic hx_nn
  have h2lo : (0.519 : Real) ^ 2 <= (0.75 * Real.log 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo 2
  have h4hi : (0.75 * Real.log 2) ^ 4 <= (0.52 : Real) ^ 4 :=
    pow_le_pow_left₀ hx_nn hx_hi 4
  have hnum : (1 : Real) - (0.519 : Real) ^ 2 / 2 + (0.52 : Real) ^ 4 / 24 <= (87 / 100 : Real) := by
    norm_num
  linarith

/-- Real rpow inverse upper (`2 ^ (-0.395) <= 4/5`) from banked `5/4 <= 2 ^ 0.395`. -/
theorem R05_rpow_neg0395_le : (2 : Real) ^ (-0.395 : Real) <= (4 / 5 : Real) := by
  have hge := zetaCellS0_rpow_0395_ge
  have hpos : (0 : Real) < (2 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (2 : Real) ^ (-0.395 : Real) = (((2 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (4 / 5 : Real) = ((5 / 4 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Real part of the R05 second eta inverse (`Re (2 ^ s)⁻¹ = 2 ^ (-0.395) * cos`). -/
theorem R05_inv_two_cpow_re_eq :
    (((((2 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (2 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 2) := by
  have h2eq : ((((2 : Nat)) : Complex)) = (2 : Complex) := by norm_cast
  rw [h2eq]
  have hlog : Complex.log (2 : Complex) = (((Real.log 2 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) <= 2)).symm
  have hlogre : (Complex.log (2 : Complex)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (2 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 2 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (2 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 2 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (2 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (2 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : Complex) ≠ 0)]
  have hinv : ((2 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (2 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (2 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 2 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (2 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 2 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (2 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 2 * 0.395)) * Real.cos (-(Real.log 2 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 2 * (-0.75))) = Real.cos (0.75 * Real.log 2) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 2 * 0.395)) = (2 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 2 * 0.395) = Real.log 2 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2)]
  rw [hinv, hre, hexp, hcos]

/-- Phase-aware R05 two-term real part (`3/10 <= Re S2`). -/
theorem R05_S2_Re_ge :
    (3 / 10 : Real) <= (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_eta_S2_eq]
  rw [Complex.sub_re, Complex.one_re]
  have hre := R05_inv_two_cpow_re_eq
  rw [hre]
  have hrpow := R05_rpow_neg0395_le
  have hcos_hi := R05_cos_075log2_upper
  have hcos_lo := R05_phase_cos_lower
  have hrpow_nn : (0 : Real) <= (2 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcos_nn : (0 : Real) <= Real.cos (0.75 * Real.log 2) := by linarith
  have hprod : (2 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 2) <=
      (4 / 5 : Real) * (87 / 100 : Real) :=
    mul_le_mul hrpow hcos_hi hcos_nn (by norm_num)
  have hle : (4 / 5 : Real) * (87 / 100 : Real) <= (7 / 10 : Real) := by norm_num
  linarith

/-- Rpow lower (`29/20 <= 3 ^ 0.395`) via cleared `(29/20) ^ 20 <= 3 ^ 7`. -/
theorem R05_three_rpow_ge : (29 / 20 : Real) <= (3 : Real) ^ (0.395 : Real) := by
  have h2up : ((29 / 20 : Real)) ^ (2 : Nat) <= (211 / 100 : Real) := by norm_num
  have h2nn : (0 : Real) <= ((29 / 20 : Real)) ^ (2 : Nat) :=
    pow_nonneg (by norm_num) _
  have h4le : ((((29 / 20 : Real)) ^ (2 : Nat))) ^ (2 : Nat) <=
      ((211 / 100 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h2nn h2up 2
  have h4eq : ((((29 / 20 : Real)) ^ (2 : Nat))) ^ (2 : Nat) =
      ((29 / 20 : Real)) ^ (4 : Nat) := by
    rw [<- pow_mul, show (2 * 2 : Nat) = 4 by norm_num]
  have h4up : ((29 / 20 : Real)) ^ (4 : Nat) <= (446 / 100 : Real) := by
    have hcalc : ((211 / 100 : Real)) ^ (2 : Nat) <= (446 / 100 : Real) := by norm_num
    rw [<- h4eq]
    exact le_trans h4le hcalc
  have h4nn : (0 : Real) <= ((29 / 20 : Real)) ^ (4 : Nat) :=
    pow_nonneg (by norm_num) _
  have h5eq : ((29 / 20 : Real)) ^ (4 : Nat) * (29 / 20 : Real) =
      ((29 / 20 : Real)) ^ (5 : Nat) := by
    have hps := pow_succ ((29 / 20 : Real)) (4 : Nat)
    rw [show (4 + 1 : Nat) = 5 by norm_num] at hps
    exact hps.symm
  have h5le : ((29 / 20 : Real)) ^ (4 : Nat) * (29 / 20 : Real) <=
      (446 / 100 : Real) * (29 / 20 : Real) :=
    mul_le_mul h4up (le_refl _) (by norm_num) (by norm_num)
  have h5up : ((29 / 20 : Real)) ^ (5 : Nat) <= (647 / 100 : Real) := by
    have hcalc : (446 / 100 : Real) * (29 / 20 : Real) <= (647 / 100 : Real) := by norm_num
    rw [<- h5eq]
    exact le_trans h5le hcalc
  have h5nn : (0 : Real) <= ((29 / 20 : Real)) ^ (5 : Nat) :=
    pow_nonneg (by norm_num) _
  have h10le : ((((29 / 20 : Real)) ^ (5 : Nat))) ^ (2 : Nat) <=
      ((647 / 100 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h5nn h5up 2
  have h10eq : ((((29 / 20 : Real)) ^ (5 : Nat))) ^ (2 : Nat) =
      ((29 / 20 : Real)) ^ (10 : Nat) := by
    rw [<- pow_mul, show (5 * 2 : Nat) = 10 by norm_num]
  have h10up : ((29 / 20 : Real)) ^ (10 : Nat) <= (4187 / 100 : Real) := by
    have hcalc : ((647 / 100 : Real)) ^ (2 : Nat) <= (4187 / 100 : Real) := by norm_num
    rw [<- h10eq]
    exact le_trans h10le hcalc
  have h10nn : (0 : Real) <= ((29 / 20 : Real)) ^ (10 : Nat) :=
    pow_nonneg (by norm_num) _
  have h20le : ((((29 / 20 : Real)) ^ (10 : Nat))) ^ (2 : Nat) <=
      ((4187 / 100 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h10nn h10up 2
  have h20eq : ((((29 / 20 : Real)) ^ (10 : Nat))) ^ (2 : Nat) =
      ((29 / 20 : Real)) ^ (20 : Nat) := by
    rw [<- pow_mul, show (10 * 2 : Nat) = 20 by norm_num]
  have h20up : ((29 / 20 : Real)) ^ (20 : Nat) <= (1754 : Real) := by
    have hcalc : ((4187 / 100 : Real)) ^ (2 : Nat) <= (1754 : Real) := by norm_num
    rw [<- h20eq]
    exact le_trans h20le hcalc
  have h37 : ((29 / 20 : Real)) ^ (20 : Nat) <= (3 : Real) ^ (7 : Nat) := by
    have h37num : (1754 : Real) <= (3 : Real) ^ (7 : Nat) := by norm_num
    exact le_trans h20up h37num
  have e : ((((3 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) = (3 : Real) ^ (7 : Nat) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 3)]
    rw [show (7 / 20 : Real) * ((((20 : Nat)) : Real)) = (7 : Real) by norm_num]
    rw [show (7 : Real) = ((((7 : Nat)) : Real)) by norm_num]
    exact Real.rpow_natCast 3 7
  have hpow : ((29 / 20 : Real)) ^ (20 : Nat) <=
      ((((3 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) := by
    rw [e]
    exact h37
  have hstep : (29 / 20 : Real) <= (3 : Real) ^ ((7 / 20 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (29 / 20 : Real) <= (3 : Real) ^ ((7 / 20 : Real)) := hstep
    _ <= (3 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- First-pair magnitude cap (`‖pair 1‖ <= 1/5`) from `‖s‖ <= 0.85` and `3 ^ 0.395 >= 29/20`. -/
theorem R05_pair1_norm_le :
    ‖etaPairTerm R03R10PolyLower.sR05 1‖ <= (1 / 5 : Real) := by
  have hs : 0 < R03R10PolyLower.sR05.re := by
    rw [R03R10PolyLower.sR05_re]
    norm_num
  have hgen := norm_etaPairTerm_le R03R10PolyLower.sR05 hs 1
  have hC : ‖R03R10PolyLower.sR05‖ <= (0.85 : Real) := R05_s_norm_le
  have hre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  rw [hre] at hgen
  have hcast : ((((2 * 1 + 1 : Nat)) : Real)) = (3 : Real) := by norm_num
  rw [hcast] at hgen
  have h3ge := R05_three_rpow_ge
  have h3pos : (0 : Real) < (3 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h3inv : (((3 : Real) ^ (0.395 : Real)))⁻¹ <= ((29 / 20 : Real))⁻¹ :=
    (inv_le_inv₀ h3pos (by norm_num)).mpr h3ge
  have hrw1 : (3 : Real) ^ (-0.395 - 1 : Real) =
      ((3 : Real) ^ (0.395 : Real))⁻¹ * ((3 : Real) ^ (-1 : Real)) := by
    rw [show (-0.395 - 1 : Real) = (-0.395 : Real) + (-1 : Real) by ring]
    rw [Real.rpow_add (by norm_num)]
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 3)]
  have hrw2 : (3 : Real) ^ (-1 : Real) = (1 / 3 : Real) := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 3), Real.rpow_one]
    norm_num
  have hbase : (3 : Real) ^ (-0.395 - 1 : Real) <= (20 / 29 : Real) * (1 / 3 : Real) := by
    rw [hrw1, hrw2]
    have heq : ((29 / 20 : Real))⁻¹ = (20 / 29 : Real) := by norm_num
    rw [heq] at h3inv
    exact mul_le_mul h3inv (le_refl _) (by norm_num) (by norm_num)
  have hmul : ‖R03R10PolyLower.sR05‖ * ((3 : Real) ^ (-0.395 - 1 : Real)) <=
      (0.85 : Real) * ((20 / 29 : Real) * (1 / 3 : Real)) :=
    mul_le_mul hC hbase (by positivity) (by norm_num)
  have hnum : (0.85 : Real) * ((20 / 29 : Real) * (1 / 3 : Real)) <= (1 / 5 : Real) := by
    norm_num
  linarith

/-- Four-term split (`S4 = S2 + pair 1`). -/
theorem R05_S4_eq :
    (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaPairTerm R03R10PolyLower.sR05 1 := by
  have hp : etaPairTerm R03R10PolyLower.sR05 1 =
      etaDirichletTerm R03R10PolyLower.sR05 2 +
        etaDirichletTerm R03R10PolyLower.sR05 3 := by
    unfold etaPairTerm
    have e0 : 2 * 1 = 2 := by norm_num
    have e1 : 2 * 1 + 1 = 3 := by norm_num
    rw [e0, e1]
  have h : (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k) +
        (etaDirichletTerm R03R10PolyLower.sR05 2 +
          etaDirichletTerm R03R10PolyLower.sR05 3) := by
    rw [show (4 : Nat) = 3 + 1 by norm_num, Finset.sum_range_succ,
      show (3 : Nat) = 2 + 1 by norm_num, Finset.sum_range_succ]
    ring
  rw [h, hp]

/-- Larger-N slow bound (`1/10 <= ‖S4‖`, `N = 4 > 2`, phase-aware Re route). -/
theorem R05_S4_norm_ge :
    (1 / 10 : Real) <= ‖∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  have hS2 := R05_S2_Re_ge
  have hp := R05_pair1_norm_le
  have hdecomp := R05_S4_eq
  have hRe4 : (1 / 10 : Real) <=
      (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
    rw [hdecomp, Complex.add_re]
    have habs : |(etaPairTerm R03R10PolyLower.sR05 1).re| <=
        ‖etaPairTerm R03R10PolyLower.sR05 1‖ :=
      Complex.abs_re_le_norm _
    have hneg : -(etaPairTerm R03R10PolyLower.sR05 1).re <=
        |(etaPairTerm R03R10PolyLower.sR05 1).re| :=
      neg_le_abs _
    linarith
  have hle : (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k).re <=
      ‖∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k‖ :=
    Complex.re_le_norm _
  linarith

/-- Honest residual: `S4 = 1/10` with banked tail `3/20` and `cF = 1` gives
`(1/10 - 3/20) / 1 = -1/20 < 1/2`; the `13/20` slow target stays open. -/
theorem R05_S4_phase_ratio_eq :
    (((1 / 10 : Real) - (3 / 20 : Real)) / (1 : Real)) = (-1 / 20 : Real) := by
  norm_num

theorem R05_S4_phase_ratio_lt_half : (-1 / 20 : Real) < (1 / 2 : Real) := by
  norm_num

#print axioms R05_cos_075log2_upper
#print axioms R05_rpow_neg0395_le
#print axioms R05_inv_two_cpow_re_eq
#print axioms R05_S2_Re_ge
#print axioms R05_three_rpow_ge
#print axioms R05_pair1_norm_le
#print axioms R05_S4_eq
#print axioms R05_S4_norm_ge
#print axioms R05_S4_phase_ratio_eq
#print axioms R05_S4_phase_ratio_lt_half

end Door3OffAxis

namespace Door3OffAxis

/-- Rpow upper (`3 ^ 0.395 <= 8/5`) via cleared `(3 ^ (2/5)) ^ 5 = 9 <= (8/5) ^ 5`. -/
theorem R05_three_rpow_le : (3 : Real) ^ (0.395 : Real) ≤ (8 / 5 : Real) := by
  have hpow : ((((3 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((8 / 5 : Real)) ^ (5 : Nat) := by
    have e : ((((3 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (3 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 3)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 3 2
    rw [e]
    norm_num
  have hstep : (3 : Real) ^ ((2 / 5 : Real)) ≤ (8 / 5 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (3 : Real) ^ (0.395 : Real) ≤ (3 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (8 / 5 : Real) := hstep

/-- Phase of the R05 third eta term (`0.75 * log 3` in `[4/5, 5/6]`)
from the banked `log 3` d9 bounds. -/
theorem R05_theta3_mem :
    (4 / 5 : Real) ≤ 0.75 * Real.log 3 ∧ 0.75 * Real.log 3 ≤ (5 / 6 : Real) := by
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  constructor <;> linarith

/-- Cosine floor at the third-term phase (`cos (0.75 * log 3) >= 14/25`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log3_lower :
    (14 / 25 : Real) ≤ Real.cos (0.75 * Real.log 3) := by
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hpos : (0 : Real) < Real.log 3 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 3 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (4 / 5 : Real) ≤ 0.75 * Real.log 3 := by linarith
  have hhi : 0.75 * Real.log 3 ≤ (5 / 6 : Real) := by linarith
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 3) ^ 2 ≤ (5 / 6 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (4 / 5 : Real) ^ 4 ≤ (0.75 * Real.log 3) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 3) ^ 6 ≤ (5 / 6 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (14 / 25 : Real) ≤
      1 - (5 / 6 : Real) ^ 2 / 2 + (4 / 5 : Real) ^ 4 / 24 -
        (5 / 6 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real part of the R05 third eta inverse
(`Re (3 ^ s)⁻¹ = 3 ^ (-0.395) * cos (0.75 * log 3)`). -/
theorem R05_inv_three_cpow_re_eq :
    (((((3 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (3 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 3) := by
  have h3eq : ((((3 : Nat)) : Complex)) = (3 : Complex) := by norm_cast
  rw [h3eq]
  have hlog : Complex.log (3 : Complex) = (((Real.log 3 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 3)).symm
  have hlogre : (Complex.log (3 : Complex)).re = Real.log 3 := by rw [hlog]; rfl
  have hlogim : (Complex.log (3 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (3 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 3 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (3 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 3 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (3 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (3 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (3 : Complex) ≠ 0)]
  have hinv : ((3 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (3 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (3 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 3 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (3 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 3 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (3 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 3 * 0.395)) * Real.cos (-(Real.log 3 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 3 * (-0.75))) = Real.cos (0.75 * Real.log 3) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 3 * 0.395)) = (3 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 3 * 0.395) = Real.log 3 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [hinv, hre, hexp, hcos]

/-- Real rpow inverse lower (`5/8 <= 3 ^ (-0.395)`) from `3 ^ 0.395 <= 8/5`. -/
theorem R05_rpow_three_neg0395_ge :
    (5 / 8 : Real) ≤ (3 : Real) ^ (-0.395 : Real) := by
  have hle := R05_three_rpow_le
  have hpos : (0 : Real) < (3 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (3 : Real) ^ (-0.395 : Real) = (((3 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (5 / 8 : Real) = ((8 / 5 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- R05 third eta term in closed form (`term 2 = (3^s)⁻¹`, since `(-1)^2 = 1`). -/
theorem R05_eta_third_eq :
    etaDirichletTerm R03R10PolyLower.sR05 2 =
      ((((3 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (2 + 1 : Nat) = 3 := rfl
  have hcast : ((((2 + 1 : Nat)) : Complex)) = ((((3 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (2 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- Real part of the R05 third eta term (`7/20 <= Re term3`,
from `5/8 * 14/25 = 7/20`). -/
theorem R05_eta_third_Re_ge :
    (7 / 20 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 2).re := by
  rw [R05_eta_third_eq, R05_inv_three_cpow_re_eq]
  have hamp := R05_rpow_three_neg0395_ge
  have hcos := R05_cos_075log3_lower
  have hamp_nn : (0 : Real) ≤ (3 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hprod : (5 / 8 : Real) * (14 / 25 : Real) ≤
      (3 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 3) :=
    mul_le_mul hamp hcos (by norm_num) hamp_nn
  have heq : (5 / 8 : Real) * (14 / 25 : Real) = (7 / 20 : Real) := by norm_num
  linarith

/-- Three-term split (`S3 = S2 + term 2`). -/
theorem R05_S3_eq :
    (∑ k ∈ Finset.range 3, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 2, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 2 := by
  rw [show (3 : Nat) = 2 + 1 by norm_num, Finset.sum_range_succ]

/-- Phase-aware R05 three-term real part (`13/20 <= Re S3`). -/
theorem R05_S3_Re_ge :
    (13 / 20 : Real) ≤
      (∑ k ∈ Finset.range 3, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S3_eq, Complex.add_re]
  have hS2 := R05_S2_Re_ge
  have ht := R05_eta_third_Re_ge
  linarith

/-- Bridge: three-term slow bound (`13/20 <= ‖S3‖`, `Re`-route). -/
theorem R05_S3_norm_ge :
    (13 / 20 : Real) ≤
      ‖∑ k ∈ Finset.range 3, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  have hRe := R05_S3_Re_ge
  have hle : (∑ k ∈ Finset.range 3, etaDirichletTerm R03R10PolyLower.sR05 k).re ≤
      ‖∑ k ∈ Finset.range 3, etaDirichletTerm R03R10PolyLower.sR05 k‖ :=
    Complex.re_le_norm _
  linarith

/-- Banked-ratio arithmetic: with `slow = 13/20`, banked tail `3/20` and
phase-aware factor `cF = 1`, `(slow - rtail) / cF = 1/2` exactly. -/
theorem R05_S3_banked_ratio_eq :
    (((13 / 20 : Real) - (3 / 20 : Real)) / (1 : Real)) = (1 / 2 : Real) := by
  norm_num

#print axioms R05_three_rpow_le
#print axioms R05_theta3_mem
#print axioms R05_cos_075log3_lower
#print axioms R05_inv_three_cpow_re_eq
#print axioms R05_rpow_three_neg0395_ge
#print axioms R05_eta_third_eq
#print axioms R05_eta_third_Re_ge
#print axioms R05_S3_eq
#print axioms R05_S3_Re_ge
#print axioms R05_S3_norm_ge
#print axioms R05_S3_banked_ratio_eq

/-- Log-4 double (`log 4 = 2 * log 2`) via `log (2 * 2)`. -/
theorem R05_log_four_eq :
    Real.log 4 = 2 * Real.log 2 := by
  have h4 : (4 : Real) = 2 * 2 := by norm_num
  rw [h4, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- Phase of the R05 fourth eta term (`0.75 * log 4` in `[1.039, 1.04]`)
from the banked `log 2` d9 bounds. -/
theorem R05_theta4_mem :
    (1.039 : Real) ≤ 0.75 * Real.log 4 ∧ 0.75 * Real.log 4 ≤ (1.04 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hx : 0.75 * Real.log 4 = 1.5 * Real.log 2 := by
    rw [R05_log_four_eq]
    ring
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the fourth-term phase (`cos (0.75 * log 4) ≤ 13/25`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log4_upper :
    Real.cos (0.75 * Real.log 4) ≤ (13 / 25 : Real) := by
  have hmem := R05_theta4_mem
  have hpos : (0 : Real) < Real.log 4 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 4 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.039 : Real) ≤ 0.75 * Real.log 4 := hmem.1
  have hhi : 0.75 * Real.log 4 ≤ (1.04 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.039 : Real) ^ 2 ≤ (0.75 * Real.log 4) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 4) ^ 4 ≤ (1.04 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.039 : Real) ^ 2 / 2 + (1.04 : Real) ^ 4 / 24 ≤
      (13 / 25 : Real) := by
    norm_num
  linarith

/-- Cosine floor at the fourth-term phase (`1/2 ≤ cos (0.75 * log 4)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log4_lower :
    (1 / 2 : Real) ≤ Real.cos (0.75 * Real.log 4) := by
  have hmem := R05_theta4_mem
  have hpos : (0 : Real) < Real.log 4 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 4 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.039 : Real) ≤ 0.75 * Real.log 4 := hmem.1
  have hhi : 0.75 * Real.log 4 ≤ (1.04 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 4) ^ 2 ≤ (1.04 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.039 : Real) ^ 4 ≤ (0.75 * Real.log 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 4) ^ 6 ≤ (1.04 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (1 / 2 : Real) ≤
      1 - (1.04 : Real) ^ 2 / 2 + (1.039 : Real) ^ 4 / 24 -
        (1.04 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real rpow fourth inverse upper (`4 ^ (-0.395) ≤ 16/25`) from
banked `2 ^ (-0.395) ≤ 4/5`, squared via `Real.mul_rpow`. -/
theorem R05_rpow_four_neg0395_le :
    (4 : Real) ^ (-0.395 : Real) ≤ (16 / 25 : Real) := by
  have h2 := R05_rpow_neg0395_le
  have hnn : (0 : Real) ≤ (2 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have h42 : (4 : Real) = 2 * 2 := by norm_num
  have heq : (4 : Real) ^ (-0.395 : Real) =
      (2 : Real) ^ (-0.395 : Real) * (2 : Real) ^ (-0.395 : Real) := by
    rw [h42, Real.mul_rpow (by norm_num) (by norm_num)]
  have hsq : (2 : Real) ^ (-0.395 : Real) * (2 : Real) ^ (-0.395 : Real) ≤
      (4 / 5 : Real) * (4 / 5 : Real) :=
    mul_le_mul h2 h2 hnn (by norm_num)
  have hnum : (4 / 5 : Real) * (4 / 5 : Real) = (16 / 25 : Real) := by
    norm_num
  rw [heq]
  rw [hnum] at hsq
  exact hsq

/-- Real part of the R05 fourth eta inverse
(`Re (4 ^ s)⁻¹ = 4 ^ (-0.395) * cos (0.75 * log 4)`). -/
theorem R05_inv_four_cpow_re_eq :
    (((((4 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (4 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 4) := by
  have h4eq : ((((4 : Nat)) : Complex)) = (4 : Complex) := by norm_cast
  rw [h4eq]
  have hlog : Complex.log (4 : Complex) = (((Real.log 4 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 4)).symm
  have hlogre : (Complex.log (4 : Complex)).re = Real.log 4 := by rw [hlog]; rfl
  have hlogim : (Complex.log (4 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (4 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 4 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (4 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 4 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (4 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (4 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (4 : Complex) ≠ 0)]
  have hinv : ((4 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (4 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (4 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 4 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (4 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 4 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (4 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 4 * 0.395)) * Real.cos (-(Real.log 4 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 4 * (-0.75))) = Real.cos (0.75 * Real.log 4) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 4 * 0.395)) = (4 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 4 * 0.395) = Real.log 4 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 4)]
  rw [hinv, hre, hexp, hcos]

/-- R05 fourth eta term in closed form (`term 3 = -((4 ^ s)⁻¹)`, since `(-1)^3 = -1`). -/
theorem R05_eta_fourth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 3 =
      -((((4 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (3 + 1 : Nat) = 4 := rfl
  have hcast : ((((3 + 1 : Nat)) : Complex)) = ((((4 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (3 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- Real part of the R05 fourth eta term (`-(208/625) ≤ Re term4`,
from `-(16/25 * 13/25)`). -/
theorem R05_eta_fourth_Re_ge :
    (-(208 / 625) : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 3).re := by
  rw [R05_eta_fourth_eq, Complex.neg_re, R05_inv_four_cpow_re_eq]
  have hamp := R05_rpow_four_neg0395_le
  have hcos := R05_cos_075log4_upper
  have hamp_nn : (0 : Real) ≤ (4 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcos_nn : (0 : Real) ≤ Real.cos (0.75 * Real.log 4) := by
    have h := R05_cos_075log4_lower
    linarith
  have hprod : (4 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 4) ≤
      (16 / 25 : Real) * (13 / 25 : Real) :=
    mul_le_mul hamp hcos hcos_nn (by norm_num)
  have heq : (16 / 25 : Real) * (13 / 25 : Real) = (208 / 625 : Real) := by
    norm_num
  linarith

/-- Phase-aware first-pair real part (`43/2500 ≤ Re pair 1`,
from `7/20 - 208/625`). -/
theorem R05_pair1_Re_ge :
    (43 / 2500 : Real) ≤ (etaPairTerm R03R10PolyLower.sR05 1).re := by
  have hp : etaPairTerm R03R10PolyLower.sR05 1 =
      etaDirichletTerm R03R10PolyLower.sR05 2 +
        etaDirichletTerm R03R10PolyLower.sR05 3 := by
    unfold etaPairTerm
    have e0 : 2 * 1 = 2 := by norm_num
    have e1 : 2 * 1 + 1 = 3 := by norm_num
    rw [e0, e1]
  rw [hp, Complex.add_re]
  have ht2 := R05_eta_third_Re_ge
  have ht3 := R05_eta_fourth_Re_ge
  linarith

/-- Phase-aware R05 four-term real part (`793/2500 ≤ Re S4`). -/
theorem R05_S4_Re_phase_ge :
    (793 / 2500 : Real) ≤
      (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S4_eq, Complex.add_re]
  have hS2 := R05_S2_Re_ge
  have hp := R05_pair1_Re_ge
  linarith

/-- Improved larger-N slow bound (`793/2500 ≤ ‖S4‖`, `Re`-route;
replaces the `1/10` magnitude-route cap). -/
theorem R05_S4_norm_phase_ge :
    (793 / 2500 : Real) ≤
      ‖∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  have hRe := R05_S4_Re_phase_ge
  have hle : (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k).re ≤
      ‖∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k‖ :=
    Complex.re_le_norm _
  linarith

/-- Honest residual: `S4 = 793/2500` with banked tail `3/20` and `cF = 1` gives
`(793/2500 - 3/20) / 1 = 209/1250 < 1/2`; the `13/20` slow target for `N = 2048`
stays open (shortfall `416/1250`). -/
theorem R05_S4_Re_phase_ratio_eq :
    ((((793 / 2500 : Real)) - (3 / 20 : Real)) / (1 : Real)) = (209 / 1250 : Real) := by
  norm_num

theorem R05_S4_Re_phase_ratio_lt_half : (209 / 1250 : Real) < (1 / 2 : Real) := by
  norm_num

/-- Genuine R05 paired tail at `M = 2` (`‖G - S₄‖ ≤ 7/4`,
via `zetaCell_even_remainder_le`). -/
theorem R05_eta_tail_2_le :
    ‖(∑' m, etaPairTerm R03R10PolyLower.sR05 m) -
      (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k)‖ ≤
      (7 / 4 : Real) := by
  have hs : 0 < R03R10PolyLower.sR05.re := by
    rw [R03R10PolyLower.sR05_re]
    norm_num
  have hC : ‖R03R10PolyLower.sR05‖ ≤ (0.85 : Real) := R05_s_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2 (by norm_num)
  have h22 : 2 * 2 = 4 := by norm_num
  rw [h22] at hgen
  have hre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  rw [hre] at hgen
  have h2c : ((((2 : Nat)) : Real)) = (2 : Real) := by norm_cast
  rw [h2c] at hgen
  have hamp := R05_rpow_neg0395_le
  have hdiv : (2 : Real) ^ (-0.395 : Real) / (0.395 : Real) ≤
      (4 / 5 : Real) / (0.395 : Real) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : Real) < 0.395)]
    exact hamp
  have hmul : (0.85 : Real) * ((2 : Real) ^ (-0.395 : Real) / (0.395 : Real)) ≤
      (0.85 : Real) * ((4 / 5 : Real) / (0.395 : Real)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (0.85 : Real) * ((4 / 5 : Real) / (0.395 : Real)) ≤ (7 / 4 : Real) := by
    norm_num
  linarith

/-- Phase-aware R05 finite zeta lower certificate at `N = 4`
(slow `793/2500` from the `Re`-route, `M = 2` tail, phase-aware factor `cF = 1`). -/
noncomputable def R05_phase_finite_zeta_certificate :
    FiniteZetaLowerCertificate R03R10PolyLower.sR05 :=
  { N := 4
    S := ∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k
    slow := 793 / 2500
    rtail := 7 / 4
    cF := 1
    hSdef := rfl
    hSlow := R05_S4_norm_phase_ge
    hTail := R05_eta_tail_2_le
    hcFpos := by norm_num
    hFac := R05_etaFactor_phase_le_one }

/-- The phase-aware R05 certificate wired through the API (negative-valued, honest). -/
theorem R05_phase_zeta_lower :
    ((R05_phase_finite_zeta_certificate.slow - R05_phase_finite_zeta_certificate.rtail) /
      R05_phase_finite_zeta_certificate.cF) ≤ ‖zeta R03R10PolyLower.sR05‖ :=
  R05_phase_finite_zeta_certificate.lower_of_re
    (by rw [R03R10PolyLower.sR05_re]; norm_num)
    (by rw [R03R10PolyLower.sR05_re]; norm_num)

/-- Exact ratio of the phase-aware R05 `N = 4` certificate:
`(793/2500 - 7/4)/1 = -1791/1250`. -/
theorem R05_phase_ratio_eq :
    ((R05_phase_finite_zeta_certificate.slow - R05_phase_finite_zeta_certificate.rtail) /
      R05_phase_finite_zeta_certificate.cF) = (-1791 / 1250 : Real) := by
  have h1 : R05_phase_finite_zeta_certificate.slow = (793 / 2500 : Real) := rfl
  have h2 : R05_phase_finite_zeta_certificate.rtail = (7 / 4 : Real) := rfl
  have h3 : R05_phase_finite_zeta_certificate.cF = (1 : Real) := rfl
  rw [h1, h2, h3]
  norm_num

#print axioms R05_log_four_eq
#print axioms R05_theta4_mem
#print axioms R05_cos_075log4_upper
#print axioms R05_cos_075log4_lower
#print axioms R05_rpow_four_neg0395_le
#print axioms R05_inv_four_cpow_re_eq
#print axioms R05_eta_fourth_eq
#print axioms R05_eta_fourth_Re_ge
#print axioms R05_pair1_Re_ge
#print axioms R05_S4_Re_phase_ge
#print axioms R05_S4_norm_phase_ge
#print axioms R05_S4_Re_phase_ratio_eq
#print axioms R05_S4_Re_phase_ratio_lt_half
#print axioms R05_eta_tail_2_le
#print axioms R05_phase_finite_zeta_certificate
#print axioms R05_phase_zeta_lower
#print axioms R05_phase_ratio_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Log-6 split (`log 6 = log 2 + log 3`) via `log (2 * 3)`. -/
theorem R05_log_six_eq :
    Real.log 6 = Real.log 2 + Real.log 3 := by
  have h6 : (6 : Real) = 2 * 3 := by norm_num
  rw [h6, Real.log_mul (by norm_num) (by norm_num)]

/-- Phase of the R05 fifth eta term (`0.75 * log 5` in `[1.207, 1.208]`)
from the banked `log 5` d9 bounds. -/
theorem R05_theta5_mem :
    (1.207 : Real) ≤ 0.75 * Real.log 5 ∧ 0.75 * Real.log 5 ≤ (1.208 : Real) := by
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  constructor <;> linarith

/-- Cosine floor at the fifth-term phase (`7/20 ≤ cos (0.75 * log 5)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log5_lower :
    (7 / 20 : Real) ≤ Real.cos (0.75 * Real.log 5) := by
  have hmem := R05_theta5_mem
  have hpos : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 5 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.207 : Real) ≤ 0.75 * Real.log 5 := hmem.1
  have hhi : 0.75 * Real.log 5 ≤ (1.208 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 5) ^ 2 ≤ (1.208 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.207 : Real) ^ 4 ≤ (0.75 * Real.log 5) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 5) ^ 6 ≤ (1.208 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (7 / 20 : Real) ≤
      1 - (1.208 : Real) ^ 2 / 2 + (1.207 : Real) ^ 4 / 24 -
        (1.208 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Phase of the R05 sixth eta term (`0.75 * log 6` in `[1.3438, 1.3439]`)
from the banked `log 2` / `log 3` d9 bounds via `R05_log_six_eq`. -/
theorem R05_theta6_mem :
    (1.3438 : Real) ≤ 0.75 * Real.log 6 ∧ 0.75 * Real.log 6 ≤ (1.3439 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hx : 0.75 * Real.log 6 = 0.75 * (Real.log 2 + Real.log 3) := by
    rw [R05_log_six_eq]
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the sixth-term phase (`cos (0.75 * log 6) ≤ 47/200`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log6_upper :
    Real.cos (0.75 * Real.log 6) ≤ (47 / 200 : Real) := by
  have hmem := R05_theta6_mem
  have hpos : (0 : Real) < Real.log 6 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 6 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.3438 : Real) ≤ 0.75 * Real.log 6 := hmem.1
  have hhi : 0.75 * Real.log 6 ≤ (1.3439 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.3438 : Real) ^ 2 ≤ (0.75 * Real.log 6) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 6) ^ 4 ≤ (1.3439 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.3438 : Real) ^ 2 / 2 + (1.3439 : Real) ^ 4 / 24 ≤
      (47 / 200 : Real) := by
    norm_num
  linarith

/-- Cosine floor at the sixth-term phase (`1/5 ≤ cos (0.75 * log 6)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log6_lower :
    (1 / 5 : Real) ≤ Real.cos (0.75 * Real.log 6) := by
  have hmem := R05_theta6_mem
  have hpos : (0 : Real) < Real.log 6 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 6 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.3438 : Real) ≤ 0.75 * Real.log 6 := hmem.1
  have hhi : 0.75 * Real.log 6 ≤ (1.3439 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 6) ^ 2 ≤ (1.3439 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.3438 : Real) ^ 4 ≤ (0.75 * Real.log 6) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 6) ^ 6 ≤ (1.3439 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (1 / 5 : Real) ≤
      1 - (1.3439 : Real) ^ 2 / 2 + (1.3438 : Real) ^ 4 / 24 -
        (1.3439 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Rpow upper (`5 ^ 0.395 ≤ 191/100`) via cleared `(5 ^ (2/5)) ^ 5 = 25`. -/
theorem R05_five_rpow_le : (5 : Real) ^ (0.395 : Real) ≤ (191 / 100 : Real) := by
  have hpow : ((((5 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((191 / 100 : Real)) ^ (5 : Nat) := by
    have e : ((((5 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (5 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 5)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 5 2
    rw [e]
    norm_num
  have hstep : (5 : Real) ^ ((2 / 5 : Real)) ≤ (191 / 100 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (5 : Real) ^ (0.395 : Real) ≤ (5 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (191 / 100 : Real) := hstep

/-- Real rpow inverse lower (`100/191 ≤ 5 ^ (-0.395)`) from `5 ^ 0.395 ≤ 191/100`. -/
theorem R05_rpow_five_neg0395_ge :
    (100 / 191 : Real) ≤ (5 : Real) ^ (-0.395 : Real) := by
  have hle := R05_five_rpow_le
  have hpos : (0 : Real) < (5 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (5 : Real) ^ (-0.395 : Real) = (((5 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (100 / 191 : Real) = ((191 / 100 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Rpow lower (`37/20 ≤ 6 ^ 0.395`) via cleared `(37/20) ^ 20 ≤ 6 ^ 7`. -/
theorem R05_six_rpow_ge : (37 / 20 : Real) ≤ (6 : Real) ^ (0.395 : Real) := by
  have h2up : ((37 / 20 : Real)) ^ (2 : Nat) ≤ (343 / 100 : Real) := by norm_num
  have h2nn : (0 : Real) ≤ ((37 / 20 : Real)) ^ (2 : Nat) :=
    pow_nonneg (by norm_num) _
  have h4le : ((((37 / 20 : Real)) ^ (2 : Nat))) ^ (2 : Nat) ≤
      ((343 / 100 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h2nn h2up 2
  have h4eq : ((((37 / 20 : Real)) ^ (2 : Nat))) ^ (2 : Nat) =
      ((37 / 20 : Real)) ^ (4 : Nat) := by
    rw [← pow_mul, show (2 * 2 : Nat) = 4 by norm_num]
  have h4up : ((37 / 20 : Real)) ^ (4 : Nat) ≤ (1177 / 100 : Real) := by
    have hcalc : ((343 / 100 : Real)) ^ (2 : Nat) ≤ (1177 / 100 : Real) := by norm_num
    rw [← h4eq]
    exact le_trans h4le hcalc
  have h4nn : (0 : Real) ≤ ((37 / 20 : Real)) ^ (4 : Nat) :=
    pow_nonneg (by norm_num) _
  have h5eq : ((37 / 20 : Real)) ^ (4 : Nat) * (37 / 20 : Real) =
      ((37 / 20 : Real)) ^ (5 : Nat) := by
    have hps := pow_succ ((37 / 20 : Real)) (4 : Nat)
    rw [show (4 + 1 : Nat) = 5 by norm_num] at hps
    exact hps.symm
  have h5le : ((37 / 20 : Real)) ^ (4 : Nat) * (37 / 20 : Real) ≤
      (1177 / 100 : Real) * (37 / 20 : Real) :=
    mul_le_mul h4up (le_refl _) (by norm_num) (by norm_num)
  have h5up : ((37 / 20 : Real)) ^ (5 : Nat) ≤ (2178 / 100 : Real) := by
    have hcalc : (1177 / 100 : Real) * (37 / 20 : Real) ≤ (2178 / 100 : Real) := by norm_num
    rw [← h5eq]
    exact le_trans h5le hcalc
  have h5nn : (0 : Real) ≤ ((37 / 20 : Real)) ^ (5 : Nat) :=
    pow_nonneg (by norm_num) _
  have h10le : ((((37 / 20 : Real)) ^ (5 : Nat))) ^ (2 : Nat) ≤
      ((2178 / 100 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h5nn h5up 2
  have h10eq : ((((37 / 20 : Real)) ^ (5 : Nat))) ^ (2 : Nat) =
      ((37 / 20 : Real)) ^ (10 : Nat) := by
    rw [← pow_mul, show (5 * 2 : Nat) = 10 by norm_num]
  have h10up : ((37 / 20 : Real)) ^ (10 : Nat) ≤ (4744 / 10 : Real) := by
    have hcalc : ((2178 / 100 : Real)) ^ (2 : Nat) ≤ (4744 / 10 : Real) := by norm_num
    rw [← h10eq]
    exact le_trans h10le hcalc
  have h10nn : (0 : Real) ≤ ((37 / 20 : Real)) ^ (10 : Nat) :=
    pow_nonneg (by norm_num) _
  have h20le : ((((37 / 20 : Real)) ^ (10 : Nat))) ^ (2 : Nat) ≤
      ((4744 / 10 : Real)) ^ (2 : Nat) :=
    pow_le_pow_left₀ h10nn h10up 2
  have h20eq : ((((37 / 20 : Real)) ^ (10 : Nat))) ^ (2 : Nat) =
      ((37 / 20 : Real)) ^ (20 : Nat) := by
    rw [← pow_mul, show (10 * 2 : Nat) = 20 by norm_num]
  have h20up : ((37 / 20 : Real)) ^ (20 : Nat) ≤ (279936 : Real) := by
    have hcalc : ((4744 / 10 : Real)) ^ (2 : Nat) ≤ (279936 : Real) := by norm_num
    rw [← h20eq]
    exact le_trans h20le hcalc
  have h67 : ((37 / 20 : Real)) ^ (20 : Nat) ≤ (6 : Real) ^ (7 : Nat) := by
    have h67num : (279936 : Real) ≤ (6 : Real) ^ (7 : Nat) := by norm_num
    exact le_trans h20up h67num
  have e : ((((6 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) = (6 : Real) ^ (7 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 6)]
    rw [show (7 / 20 : Real) * ((((20 : Nat)) : Real)) = (7 : Real) by norm_num]
    rw [show (7 : Real) = ((((7 : Nat)) : Real)) by norm_num]
    exact Real.rpow_natCast 6 7
  have hpow : ((37 / 20 : Real)) ^ (20 : Nat) ≤
      ((((6 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) := by
    rw [e]
    exact h67
  have hstep : (37 / 20 : Real) ≤ (6 : Real) ^ ((7 / 20 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (37 / 20 : Real) ≤ (6 : Real) ^ ((7 / 20 : Real)) := hstep
    _ ≤ (6 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Real rpow inverse upper (`6 ^ (-0.395) ≤ 20/37`) from `37/20 ≤ 6 ^ 0.395`. -/
theorem R05_rpow_six_neg0395_le :
    (6 : Real) ^ (-0.395 : Real) ≤ (20 / 37 : Real) := by
  have hge := R05_six_rpow_ge
  have hpos : (0 : Real) < (6 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (6 : Real) ^ (-0.395 : Real) = (((6 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (20 / 37 : Real) = ((37 / 20 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Real part of the R05 fifth eta inverse
(`Re (5 ^ s)⁻¹ = 5 ^ (-0.395) * cos (0.75 * log 5)`). -/
theorem R05_inv_five_cpow_re_eq :
    (((((5 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (5 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 5) := by
  have h5eq : ((((5 : Nat)) : Complex)) = (5 : Complex) := by norm_cast
  rw [h5eq]
  have hlog : Complex.log (5 : Complex) = (((Real.log 5 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 5)).symm
  have hlogre : (Complex.log (5 : Complex)).re = Real.log 5 := by rw [hlog]; rfl
  have hlogim : (Complex.log (5 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (5 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 5 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (5 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 5 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (5 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (5 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (5 : Complex) ≠ 0)]
  have hinv : ((5 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (5 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, ← Complex.exp_neg]
  have hnegre : (-(Complex.log (5 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 5 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (5 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 5 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (5 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 5 * 0.395)) * Real.cos (-(Real.log 5 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 5 * (-0.75))) = Real.cos (0.75 * Real.log 5) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 5 * 0.395)) = (5 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 5 * 0.395) = Real.log 5 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : Real) < 5)]
  rw [hinv, hre, hexp, hcos]

/-- Real part of the R05 sixth eta inverse
(`Re (6 ^ s)⁻¹ = 6 ^ (-0.395) * cos (0.75 * log 6)`). -/
theorem R05_inv_six_cpow_re_eq :
    (((((6 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (6 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 6) := by
  have h6eq : ((((6 : Nat)) : Complex)) = (6 : Complex) := by norm_cast
  rw [h6eq]
  have hlog : Complex.log (6 : Complex) = (((Real.log 6 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 6)).symm
  have hlogre : (Complex.log (6 : Complex)).re = Real.log 6 := by rw [hlog]; rfl
  have hlogim : (Complex.log (6 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (6 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 6 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (6 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 6 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (6 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (6 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (6 : Complex) ≠ 0)]
  have hinv : ((6 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (6 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, ← Complex.exp_neg]
  have hnegre : (-(Complex.log (6 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 6 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (6 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 6 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (6 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 6 * 0.395)) * Real.cos (-(Real.log 6 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 6 * (-0.75))) = Real.cos (0.75 * Real.log 6) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 6 * 0.395)) = (6 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 6 * 0.395) = Real.log 6 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : Real) < 6)]
  rw [hinv, hre, hexp, hcos]

/-- R05 fifth eta term in closed form (`term 4 = (5^s)⁻¹`, since `(-1)^4 = 1`). -/
theorem R05_eta_fifth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 4 =
      ((((5 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (4 + 1 : Nat) = 5 := rfl
  have hcast : ((((4 + 1 : Nat)) : Complex)) = ((((5 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (4 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- R05 sixth eta term in closed form (`term 5 = -((6 ^ s)⁻¹)`, since `(-1)^5 = -1`). -/
theorem R05_eta_sixth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 5 =
      -((((6 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (5 + 1 : Nat) = 6 := rfl
  have hcast : ((((5 + 1 : Nat)) : Complex)) = ((((6 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (5 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- Real part of the R05 fifth eta term (`9/50 ≤ Re term5`,
from `(100/191) * (7/20) = 35/191 ≥ 9/50`). -/
theorem R05_eta_fifth_Re_ge :
    (9 / 50 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 4).re := by
  rw [R05_eta_fifth_eq, R05_inv_five_cpow_re_eq]
  have hamp := R05_rpow_five_neg0395_ge
  have hcos := R05_cos_075log5_lower
  have hamp_nn : (0 : Real) ≤ (5 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hprod : (100 / 191 : Real) * (7 / 20 : Real) ≤
      (5 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 5) :=
    mul_le_mul hamp hcos (by norm_num) hamp_nn
  have heq : (100 / 191 : Real) * (7 / 20 : Real) = (35 / 191 : Real) := by
    norm_num
  have hle : (9 / 50 : Real) ≤ (35 / 191 : Real) := by norm_num
  linarith

/-- Real part of the R05 sixth eta term (`-(47/370) ≤ Re term6`,
from `-((20/37) * (47/200))`). -/
theorem R05_eta_sixth_Re_ge :
    (-(47 / 370) : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 5).re := by
  rw [R05_eta_sixth_eq, Complex.neg_re, R05_inv_six_cpow_re_eq]
  have hamp := R05_rpow_six_neg0395_le
  have hcos := R05_cos_075log6_upper
  have hamp_nn : (0 : Real) ≤ (6 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcos_nn : (0 : Real) ≤ Real.cos (0.75 * Real.log 6) := by
    have h := R05_cos_075log6_lower
    linarith
  have hprod : (6 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 6) ≤
      (20 / 37 : Real) * (47 / 200 : Real) :=
    mul_le_mul hamp hcos hcos_nn (by norm_num)
  have heq : (20 / 37 : Real) * (47 / 200 : Real) = (47 / 370 : Real) := by
    norm_num
  linarith

/-- Phase-aware second-pair real part (`1/20 ≤ Re pair 2`,
from `9/50 - 47/370 = 49/925 ≥ 1/20`). -/
theorem R05_pair2_Re_ge :
    (1 / 20 : Real) ≤ (etaPairTerm R03R10PolyLower.sR05 2).re := by
  have hp : etaPairTerm R03R10PolyLower.sR05 2 =
      etaDirichletTerm R03R10PolyLower.sR05 4 +
        etaDirichletTerm R03R10PolyLower.sR05 5 := by
    unfold etaPairTerm
    have e0 : 2 * 2 = 4 := by norm_num
    have e1 : 2 * 2 + 1 = 5 := by norm_num
    rw [e0, e1]
  rw [hp, Complex.add_re]
  have ht4 := R05_eta_fifth_Re_ge
  have ht5 := R05_eta_sixth_Re_ge
  have hle : (1 / 20 : Real) ≤ (9 / 50 : Real) - (47 / 370 : Real) := by norm_num
  linarith

/-- Six-term split (`S6 = S4 + pair 2`). -/
theorem R05_S6_eq :
    (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaPairTerm R03R10PolyLower.sR05 2 := by
  have hp : etaPairTerm R03R10PolyLower.sR05 2 =
      etaDirichletTerm R03R10PolyLower.sR05 4 +
        etaDirichletTerm R03R10PolyLower.sR05 5 := by
    unfold etaPairTerm
    have e0 : 2 * 2 = 4 := by norm_num
    have e1 : 2 * 2 + 1 = 5 := by norm_num
    rw [e0, e1]
  have h : (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 4, etaDirichletTerm R03R10PolyLower.sR05 k) +
        (etaDirichletTerm R03R10PolyLower.sR05 4 +
          etaDirichletTerm R03R10PolyLower.sR05 5) := by
    rw [show (6 : Nat) = 5 + 1 by norm_num, Finset.sum_range_succ,
      show (5 : Nat) = 4 + 1 by norm_num, Finset.sum_range_succ]
    ring
  rw [h, hp]

/-- Phase-aware R05 six-term real part (`459/1250 ≤ Re S6`,
from `793/2500 + 1/20`). -/
theorem R05_S6_Re_ge :
    (459 / 1250 : Real) ≤
      (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S6_eq, Complex.add_re]
  have hS4 := R05_S4_Re_phase_ge
  have hp := R05_pair2_Re_ge
  have hle : (459 / 1250 : Real) ≤ (793 / 2500 : Real) + (1 / 20 : Real) := by
    norm_num
  linarith

/-- Six-term slow bound (`459/1250 ≤ ‖S6‖`, `Re`-route). -/
theorem R05_S6_norm_ge :
    (459 / 1250 : Real) ≤
      ‖∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  have hRe := R05_S6_Re_ge
  have hle : (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k).re ≤
      ‖∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k‖ :=
    Complex.re_le_norm _
  linarith

/-- Honest residual: `S6 = 459/1250` with banked tail `3/20` and `cF = 1` gives
`(459/1250 - 3/20) / 1 = 543/2500 < 1/2`; the `13/20` slow target for `N = 2048`
stays open (shortfall `707/2500`). -/
theorem R05_S6_banked_ratio_eq :
    ((((459 / 1250 : Real)) - (3 / 20 : Real)) / (1 : Real)) = (543 / 2500 : Real) := by
  norm_num

theorem R05_S6_banked_ratio_lt_half : (543 / 2500 : Real) < (1 / 2 : Real) := by
  norm_num

#print axioms R05_log_six_eq
#print axioms R05_theta5_mem
#print axioms R05_cos_075log5_lower
#print axioms R05_theta6_mem
#print axioms R05_cos_075log6_upper
#print axioms R05_cos_075log6_lower
#print axioms R05_five_rpow_le
#print axioms R05_rpow_five_neg0395_ge
#print axioms R05_six_rpow_ge
#print axioms R05_rpow_six_neg0395_le
#print axioms R05_inv_five_cpow_re_eq
#print axioms R05_inv_six_cpow_re_eq
#print axioms R05_eta_fifth_eq
#print axioms R05_eta_sixth_eq
#print axioms R05_eta_fifth_Re_ge
#print axioms R05_eta_sixth_Re_ge
#print axioms R05_pair2_Re_ge
#print axioms R05_S6_eq
#print axioms R05_S6_Re_ge
#print axioms R05_S6_norm_ge
#print axioms R05_S6_banked_ratio_eq
#print axioms R05_S6_banked_ratio_lt_half

end Door3OffAxis

namespace Door3OffAxis

/-- Log-8 split (`log 8 = 3 * log 2`) via `8 = 2 ^ 3`. -/
theorem R05_log_eight_eq :
    Real.log 8 = 3 * Real.log 2 := by
  have h8 : (8 : Real) = 2 ^ (3 : Nat) := by norm_num
  rw [h8, Real.log_pow]
  have h3 : ((((3 : Nat))) : Real) = (3 : Real) := by norm_num
  rw [h3]

/-- Fresh `log 7` lower bound (`1.9365 ≤ log 7`) from `log 7 = 3 * log 2 + log (7/8)`
with the d9 `log 2` lower bound and `log (8/7) ≤ 1/7`
(no d9 lemma for `log 7` exists in Mathlib). -/
theorem R05_log_seven_ge :
    (1.9365 : Real) ≤ Real.log 7 := by
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have hub87 : Real.log (8 / 7 : Real) ≤ (1 / 7 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 8 / 7)
    have he : (8 / 7 : Real) - 1 = (1 / 7 : Real) := by norm_num
    linarith
  have hinv : Real.log (7 / 8 : Real) = -Real.log (8 / 7 : Real) := by
    have heq : (7 / 8 : Real) = (8 / 7 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hmeq : (8 : Real) * (7 / 8) = 7 := by norm_num
  have hlog7 : Real.log 7 = 3 * Real.log 2 + Real.log (7 / 8 : Real) := by
    have h := Real.log_mul (show (8 : Real) ≠ 0 by norm_num)
      (show (7 / 8 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [R05_log_eight_eq] at h
    exact h
  have hfin : (1.9365 : Real) ≤ 3 * (0.693147 : Real) - (1 / 7 : Real) := by
    norm_num
  rw [hlog7, hinv]
  linarith

/-- Fresh `log 7` upper bound (`log 7 ≤ 1.9545`) from `log 7 = 3 * log 2 + log (7/8)`
with the d9 `log 2` upper bound and `log (7/8) ≤ -1/8`. -/
theorem R05_log_seven_le :
    Real.log 7 ≤ (1.9545 : Real) := by
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have hub78 : Real.log (7 / 8 : Real) ≤ (-1 / 8 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 7 / 8)
    have he : (7 / 8 : Real) - 1 = (-1 / 8 : Real) := by norm_num
    linarith
  have hmeq : (8 : Real) * (7 / 8) = 7 := by norm_num
  have hlog7 : Real.log 7 = 3 * Real.log 2 + Real.log (7 / 8 : Real) := by
    have h := Real.log_mul (show (8 : Real) ≠ 0 by norm_num)
      (show (7 / 8 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [R05_log_eight_eq] at h
    exact h
  have hfin : 3 * (0.693148 : Real) + (-1 / 8 : Real) ≤ (1.9545 : Real) := by
    norm_num
  rw [hlog7]
  linarith

/-- Phase of the R05 seventh eta term (`0.75 * log 7` in `[1.4523, 1.4659]`)
from the fresh `log 7` bounds. -/
theorem R05_theta7_mem :
    (1.4523 : Real) ≤ 0.75 * Real.log 7 ∧ 0.75 * Real.log 7 ≤ (1.4659 : Real) := by
  have hlo := R05_log_seven_ge
  have hhi := R05_log_seven_le
  constructor <;> linarith

/-- Phase of the R05 eighth eta term (`0.75 * log 8` in `[1.5595, 1.5596]`)
from the d9 `log 2` bounds via `R05_log_eight_eq`. -/
theorem R05_theta8_mem :
    (1.5595 : Real) ≤ 0.75 * Real.log 8 ∧ 0.75 * Real.log 8 ≤ (1.5596 : Real) := by
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have he := R05_log_eight_eq
  constructor <;> rw [he] <;> linarith

/-- Cosine floor at the seventh-term phase (`1/20 ≤ cos (0.75 * log 7)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log7_lower :
    (1 / 20 : Real) ≤ Real.cos (0.75 * Real.log 7) := by
  have hmem := R05_theta7_mem
  have hpos : (0 : Real) < Real.log 7 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 7 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.4523 : Real) ≤ 0.75 * Real.log 7 := hmem.1
  have hhi : 0.75 * Real.log 7 ≤ (1.4659 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 7) ^ 2 ≤ (1.4659 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.4523 : Real) ^ 4 ≤ (0.75 * Real.log 7) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 7) ^ 6 ≤ (1.4659 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (1 / 20 : Real) ≤
      1 - (1.4659 : Real) ^ 2 / 2 + (1.4523 : Real) ^ 4 / 24 -
        (1.4659 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Cosine upper at the eighth-term phase (`cos (0.75 * log 8) ≤ 1/25`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log8_upper :
    Real.cos (0.75 * Real.log 8) ≤ (1 / 25 : Real) := by
  have hmem := R05_theta8_mem
  have hpos : (0 : Real) < Real.log 8 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 8 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.5595 : Real) ≤ 0.75 * Real.log 8 := hmem.1
  have hhi : 0.75 * Real.log 8 ≤ (1.5596 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.5595 : Real) ^ 2 ≤ (0.75 * Real.log 8) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 8) ^ 4 ≤ (1.5596 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.5595 : Real) ^ 2 / 2 + (1.5596 : Real) ^ 4 / 24 ≤
      (1 / 25 : Real) := by
    norm_num
  linarith

/-- Cosine nonnegativity at the eighth-term phase (`0 ≤ cos (0.75 * log 8)`)
since `θ8 ≤ 1.5596 < π / 2` (from `π > 3.1415`). -/
theorem R05_cos_075log8_nonneg :
    (0 : Real) ≤ Real.cos (0.75 * Real.log 8) := by
  have hmem := R05_theta8_mem
  have hpi_lo : (3.1415 : Real) < Real.pi := Real.pi_gt_d4
  have hpos : (0 : Real) < Real.log 8 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 8 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hhi : 0.75 * Real.log 8 ≤ (1.5596 : Real) := hmem.2
  have hle : (1.5596 : Real) ≤ Real.pi / 2 := by linarith
  have hm : 0.75 * Real.log 8 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  exact Real.cos_nonneg_of_mem_Icc hm

/-- Rpow upper (`7 ^ 0.395 ≤ 11/5`) via cleared `(7 ^ (2/5)) ^ 5 = 49`. -/
theorem R05_seven_rpow_le : (7 : Real) ^ (0.395 : Real) ≤ (11 / 5 : Real) := by
  have hpow : ((((7 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((11 / 5 : Real)) ^ (5 : Nat) := by
    have e : ((((7 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (7 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 7)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 7 2
    rw [e]
    norm_num
  have hstep : (7 : Real) ^ ((2 / 5 : Real)) ≤ (11 / 5 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (7 : Real) ^ (0.395 : Real) ≤ (7 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (11 / 5 : Real) := hstep

/-- Real rpow inverse lower (`5/11 ≤ 7 ^ (-0.395)`) from `7 ^ 0.395 ≤ 11/5`. -/
theorem R05_rpow_seven_neg0395_ge :
    (5 / 11 : Real) ≤ (7 : Real) ^ (-0.395 : Real) := by
  have hle := R05_seven_rpow_le
  have hpos : (0 : Real) < (7 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (7 : Real) ^ (-0.395 : Real) = (((7 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (5 / 11 : Real) = ((11 / 5 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Rpow lower (`2 ≤ 8 ^ 0.395`) via cleared `(2) ^ 20 ≤ 8 ^ 7`. -/
theorem R05_eight_rpow_ge : (2 : Real) ≤ (8 : Real) ^ (0.395 : Real) := by
  have h67 : ((2 : Real)) ^ (20 : Nat) ≤ (8 : Real) ^ (7 : Nat) := by norm_num
  have e : ((((8 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) =
      (8 : Real) ^ (7 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 8)]
    rw [show (7 / 20 : Real) * ((((20 : Nat)) : Real)) = (7 : Real) by norm_num]
    rw [show (7 : Real) = ((((7 : Nat)) : Real)) by norm_num]
    exact Real.rpow_natCast 8 7
  have hpow : ((2 : Real)) ^ (20 : Nat) ≤
      ((((8 : Real) ^ ((7 / 20 : Real)))) ^ (20 : Nat)) := by
    rw [e]
    exact h67
  have hstep : (2 : Real) ≤ (8 : Real) ^ ((7 / 20 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (2 : Real) ≤ (8 : Real) ^ ((7 / 20 : Real)) := hstep
    _ ≤ (8 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Real rpow inverse upper (`8 ^ (-0.395) ≤ 1/2`) from `2 ≤ 8 ^ 0.395`. -/
theorem R05_rpow_eight_neg0395_le :
    (8 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hge := R05_eight_rpow_ge
  have hpos : (0 : Real) < (8 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (8 : Real) ^ (-0.395 : Real) = (((8 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Real part of the R05 seventh eta inverse
(`Re (7 ^ s)⁻¹ = 7 ^ (-0.395) * cos (0.75 * log 7)`). -/
theorem R05_inv_seven_cpow_re_eq :
    (((((7 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (7 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 7) := by
  have h7eq : ((((7 : Nat)) : Complex)) = (7 : Complex) := by norm_cast
  rw [h7eq]
  have hlog : Complex.log (7 : Complex) = (((Real.log 7 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 7)).symm
  have hlogre : (Complex.log (7 : Complex)).re = Real.log 7 := by rw [hlog]; rfl
  have hlogim : (Complex.log (7 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (7 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 7 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (7 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 7 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (7 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (7 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (7 : Complex) ≠ 0)]
  have hinv : ((7 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (7 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, ← Complex.exp_neg]
  have hnegre : (-(Complex.log (7 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 7 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (7 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 7 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (7 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 7 * 0.395)) * Real.cos (-(Real.log 7 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 7 * (-0.75))) = Real.cos (0.75 * Real.log 7) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 7 * 0.395)) = (7 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 7 * 0.395) = Real.log 7 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : Real) < 7)]
  rw [hinv, hre, hexp, hcos]

/-- Real part of the R05 eighth eta inverse
(`Re (8 ^ s)⁻¹ = 8 ^ (-0.395) * cos (0.75 * log 8)`). -/
theorem R05_inv_eight_cpow_re_eq :
    (((((8 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (8 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 8) := by
  have h8eq : ((((8 : Nat)) : Complex)) = (8 : Complex) := by norm_cast
  rw [h8eq]
  have hlog : Complex.log (8 : Complex) = (((Real.log 8 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 8)).symm
  have hlogre : (Complex.log (8 : Complex)).re = Real.log 8 := by rw [hlog]; rfl
  have hlogim : (Complex.log (8 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (8 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 8 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (8 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 8 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (8 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (8 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (8 : Complex) ≠ 0)]
  have hinv : ((8 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (8 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, ← Complex.exp_neg]
  have hnegre : (-(Complex.log (8 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 8 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (8 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 8 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (8 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 8 * 0.395)) * Real.cos (-(Real.log 8 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 8 * (-0.75))) = Real.cos (0.75 * Real.log 8) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 8 * 0.395)) = (8 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 8 * 0.395) = Real.log 8 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : Real) < 8)]
  rw [hinv, hre, hexp, hcos]

/-- R05 seventh eta term in closed form (`term 6 = (7^s)⁻¹`, since `(-1)^6 = 1`). -/
theorem R05_eta_seventh_eq :
    etaDirichletTerm R03R10PolyLower.sR05 6 =
      ((((7 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (6 + 1 : Nat) = 7 := rfl
  have hcast : ((((6 + 1 : Nat)) : Complex)) = ((((7 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (6 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- R05 eighth eta term in closed form (`term 7 = -((8 ^ s)⁻¹)`, since `(-1)^7 = -1`). -/
theorem R05_eta_eighth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 7 =
      -((((8 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (7 + 1 : Nat) = 8 := rfl
  have hcast : ((((7 + 1 : Nat)) : Complex)) = ((((8 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (7 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- Real part of the R05 seventh eta term (`1/44 ≤ Re term7`,
from `(5/11) * (1/20) = 1/44`). -/
theorem R05_eta_seventh_Re_ge :
    (1 / 44 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 6).re := by
  rw [R05_eta_seventh_eq, R05_inv_seven_cpow_re_eq]
  have hamp := R05_rpow_seven_neg0395_ge
  have hcos := R05_cos_075log7_lower
  have hamp_nn : (0 : Real) ≤ (7 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hprod : (5 / 11 : Real) * (1 / 20 : Real) ≤
      (7 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 7) :=
    mul_le_mul hamp hcos (by norm_num) hamp_nn
  have heq : (5 / 11 : Real) * (1 / 20 : Real) = (1 / 44 : Real) := by
    norm_num
  linarith

/-- Real part of the R05 eighth eta term (`-(1/50) ≤ Re term8`,
from `-((1/2) * (1/25))`). -/
theorem R05_eta_eighth_Re_ge :
    (-(1 / 50) : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 7).re := by
  rw [R05_eta_eighth_eq, Complex.neg_re, R05_inv_eight_cpow_re_eq]
  have hamp := R05_rpow_eight_neg0395_le
  have hcos := R05_cos_075log8_upper
  have hamp_nn : (0 : Real) ≤ (8 : Real) ^ (-0.395 : Real) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcos_nn : (0 : Real) ≤ Real.cos (0.75 * Real.log 8) :=
    R05_cos_075log8_nonneg
  have hprod : (8 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 8) ≤
      (1 / 2 : Real) * (1 / 25 : Real) :=
    mul_le_mul hamp hcos hcos_nn (by norm_num)
  have heq : (1 / 2 : Real) * (1 / 25 : Real) = (1 / 50 : Real) := by
    norm_num
  linarith

/-- Phase-aware third-pair real part (`1/500 ≤ Re pair 3`,
from `1/44 - 1/50 = 3/1100 ≥ 1/500`).
Stop-rule verdict: the floor stays POSITIVE at m=3 (no stop here);
`θ8 ≈ 1.5596` is still below `π/2`, but `θ9 ≈ 1.648 > π/2`, so the
pair route is expected to stall at m=4. -/
theorem R05_pair3_Re_ge :
    (1 / 500 : Real) ≤ (etaPairTerm R03R10PolyLower.sR05 3).re := by
  have hp : etaPairTerm R03R10PolyLower.sR05 3 =
      etaDirichletTerm R03R10PolyLower.sR05 6 +
        etaDirichletTerm R03R10PolyLower.sR05 7 := by
    unfold etaPairTerm
    have e0 : 2 * 3 = 6 := by norm_num
    have e1 : 2 * 3 + 1 = 7 := by norm_num
    rw [e0, e1]
  rw [hp, Complex.add_re]
  have ht6 := R05_eta_seventh_Re_ge
  have ht7 := R05_eta_eighth_Re_ge
  have hle : (1 / 500 : Real) ≤ (1 / 44 : Real) - (1 / 50 : Real) := by norm_num
  linarith

#print axioms R05_log_eight_eq
#print axioms R05_log_seven_ge
#print axioms R05_log_seven_le
#print axioms R05_theta7_mem
#print axioms R05_theta8_mem
#print axioms R05_cos_075log7_lower
#print axioms R05_cos_075log8_upper
#print axioms R05_cos_075log8_nonneg
#print axioms R05_seven_rpow_le
#print axioms R05_rpow_seven_neg0395_ge
#print axioms R05_eight_rpow_ge
#print axioms R05_rpow_eight_neg0395_le
#print axioms R05_inv_seven_cpow_re_eq
#print axioms R05_inv_eight_cpow_re_eq
#print axioms R05_eta_seventh_eq
#print axioms R05_eta_eighth_eq
#print axioms R05_eta_seventh_Re_ge
#print axioms R05_eta_eighth_Re_ge
#print axioms R05_pair3_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Eight-term split (`S8 = S6 + pair 3`). -/
theorem R05_S8_eq :
    (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaPairTerm R03R10PolyLower.sR05 3 := by
  have hp : etaPairTerm R03R10PolyLower.sR05 3 =
      etaDirichletTerm R03R10PolyLower.sR05 6 +
        etaDirichletTerm R03R10PolyLower.sR05 7 := by
    unfold etaPairTerm
    have e0 : 2 * 3 = 6 := by norm_num
    have e1 : 2 * 3 + 1 = 7 := by norm_num
    rw [e0, e1]
  have h : (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 6, etaDirichletTerm R03R10PolyLower.sR05 k) +
        (etaDirichletTerm R03R10PolyLower.sR05 6 +
          etaDirichletTerm R03R10PolyLower.sR05 7) := by
    rw [show (8 : Nat) = 7 + 1 by norm_num, Finset.sum_range_succ,
      show (7 : Nat) = 6 + 1 by norm_num, Finset.sum_range_succ]
    ring
  rw [h, hp]

/-- Phase-aware R05 eight-term real part (`923/2500 ≤ Re S8`,
from `459/1250 + 1/500`). -/
theorem R05_S8_Re_ge :
    (923 / 2500 : Real) ≤
      (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S8_eq, Complex.add_re]
  have hS6 := R05_S6_Re_ge
  have hp := R05_pair3_Re_ge
  have hle : (923 / 2500 : Real) ≤ (459 / 1250 : Real) + (1 / 500 : Real) := by
    norm_num
  linarith

/-- Eight-term slow bound (`923/2500 ≤ ‖S8‖`, `Re`-route). -/
theorem R05_S8_norm_ge :
    (923 / 2500 : Real) ≤
      ‖∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k‖ := by
  have hRe := R05_S8_Re_ge
  have hle : (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k).re ≤
      ‖∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k‖ :=
    Complex.re_le_norm _
  linarith

/-- Honest residual: `S8 = 923/2500` with banked tail `3/20` and `cF = 1` gives
`(923/2500 - 3/20) / 1 = 137/625 < 1/2`; the `13/20` slow target for `N = 2048`
stays open (shortfall `702/2500`). -/
theorem R05_S8_banked_ratio_eq :
    ((((923 / 2500 : Real)) - (3 / 20 : Real)) / (1 : Real)) = (137 / 625 : Real) := by
  norm_num

theorem R05_S8_banked_ratio_lt_half : (137 / 625 : Real) < (1 / 2 : Real) := by
  norm_num

#print axioms R05_S8_eq
#print axioms R05_S8_Re_ge
#print axioms R05_S8_norm_ge
#print axioms R05_S8_banked_ratio_eq
#print axioms R05_S8_banked_ratio_lt_half

end Door3OffAxis

namespace Door3OffAxis

/-- Log-9 double (`log 9 = 2 * log 3`) via `9 = 3 * 3`. -/
theorem R05_log_nine_eq :
    Real.log 9 = 2 * Real.log 3 := by
  have h9 : (9 : Real) = 3 * 3 := by norm_num
  rw [h9, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- Log-10 split (`log 10 = log 2 + log 5`) via `10 = 2 * 5`. -/
theorem R05_log_ten_eq :
    Real.log 10 = Real.log 2 + Real.log 5 := by
  have h10 : (10 : Real) = 2 * 5 := by norm_num
  rw [h10, Real.log_mul (by norm_num) (by norm_num)]

/-- Phase of the R05 ninth eta term (`0.75 * log 9` in `[1.6479, 1.648]`)
from the banked `log 3` d9 bounds via `R05_log_nine_eq`.
Note `1.6479 > π / 2 ≈ 1.5708`: the phase has crossed the axis. -/
theorem R05_theta9_mem :
    (1.6479 : Real) ≤ 0.75 * Real.log 9 ∧ 0.75 * Real.log 9 ≤ (1.648 : Real) := by
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hx : 0.75 * Real.log 9 = 1.5 * Real.log 3 := by
    rw [R05_log_nine_eq]
    ring
  constructor <;> rw [hx] <;> linarith

/-- Phase of the R05 tenth eta term (`0.75 * log 10` in `[1.7269, 1.727]`)
from the banked `log 2` / `log 5` d9 bounds via `R05_log_ten_eq`. -/
theorem R05_theta10_mem :
    (1.7269 : Real) ≤ 0.75 * Real.log 10 ∧ 0.75 * Real.log 10 ≤ (1.727 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  have hx : 0.75 * Real.log 10 = 0.75 * (Real.log 2 + Real.log 5) := by
    rw [R05_log_ten_eq]
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the ninth-term phase (`cos (0.75 * log 9) ≤ -1/25`)
via `CG_cos_le_quartic` with per-monomial endpoints.
This is the stop-rule mechanism: the ninth-term cosine is NEGATIVE. -/
theorem R05_cos_075log9_upper :
    Real.cos (0.75 * Real.log 9) ≤ (-1 / 25 : Real) := by
  have hmem := R05_theta9_mem
  have hpos : (0 : Real) < Real.log 9 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 9 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.6479 : Real) ≤ 0.75 * Real.log 9 := hmem.1
  have hhi : 0.75 * Real.log 9 ≤ (1.648 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.6479 : Real) ^ 2 ≤ (0.75 * Real.log 9) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 9) ^ 4 ≤ (1.648 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.6479 : Real) ^ 2 / 2 + (1.648 : Real) ^ 4 / 24 ≤
      (-1 / 25 : Real) := by
    norm_num
  linarith

/-- The ninth-term cosine is strictly negative (stop-rule trigger). -/
theorem R05_cos_075log9_neg :
    Real.cos (0.75 * Real.log 9) < 0 := by
  have h := R05_cos_075log9_upper
  linarith

/-- Cosine floor at the ninth-term phase (`-1/12 ≤ cos (0.75 * log 9)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log9_lower :
    (-1 / 12 : Real) ≤ Real.cos (0.75 * Real.log 9) := by
  have hmem := R05_theta9_mem
  have hpos : (0 : Real) < Real.log 9 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 9 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.6479 : Real) ≤ 0.75 * Real.log 9 := hmem.1
  have hhi : 0.75 * Real.log 9 ≤ (1.648 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 9) ^ 2 ≤ (1.648 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.6479 : Real) ^ 4 ≤ (0.75 * Real.log 9) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 9) ^ 6 ≤ (1.648 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-1 / 12 : Real) ≤
      1 - (1.648 : Real) ^ 2 / 2 + (1.6479 : Real) ^ 4 / 24 -
        (1.648 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Cosine upper at the tenth-term phase (`cos (0.75 * log 10) ≤ -1/10`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log10_upper :
    Real.cos (0.75 * Real.log 10) ≤ (-1 / 10 : Real) := by
  have hmem := R05_theta10_mem
  have hpos : (0 : Real) < Real.log 10 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 10 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.7269 : Real) ≤ 0.75 * Real.log 10 := hmem.1
  have hhi : 0.75 * Real.log 10 ≤ (1.727 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.7269 : Real) ^ 2 ≤ (0.75 * Real.log 10) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 10) ^ 4 ≤ (1.727 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.7269 : Real) ^ 2 / 2 + (1.727 : Real) ^ 4 / 24 ≤
      (-1 / 10 : Real) := by
    norm_num
  linarith

#print axioms R05_log_nine_eq
#print axioms R05_log_ten_eq
#print axioms R05_theta9_mem
#print axioms R05_theta10_mem
#print axioms R05_cos_075log9_upper
#print axioms R05_cos_075log9_neg
#print axioms R05_cos_075log9_lower
#print axioms R05_cos_075log10_upper

end Door3OffAxis

namespace Door3OffAxis

/-- Rpow lower (`2 ≤ 9 ^ 0.395`) via cleared `(2) ^ 3 ≤ (9 ^ (1/3)) ^ 3 = 9`. -/
theorem R05_nine_rpow_ge : (2 : Real) ≤ (9 : Real) ^ (0.395 : Real) := by
  have hstep : (2 : Real) ≤ (9 : Real) ^ ((1 / 3 : Real)) := by
    have hpow : ((2 : Real)) ^ (3 : Nat) ≤
        ((((9 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((9 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (9 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 9)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 9 1
      rw [e]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (2 : Real) ≤ (9 : Real) ^ ((1 / 3 : Real)) := hstep
    _ ≤ (9 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Real rpow ninth inverse upper (`9 ^ (-0.395) ≤ 1/2`) from `2 ≤ 9 ^ 0.395`. -/
theorem R05_rpow_nine_neg0395_le :
    (9 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hle := R05_nine_rpow_ge
  have hpos : (0 : Real) < (9 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (9 : Real) ^ (-0.395 : Real) = (((9 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hle

/-- Rpow upper (`10 ^ 0.395 ≤ 8/3`) via cleared `(10 ^ (2/5)) ^ 5 = 100`. -/
theorem R05_ten_rpow_le : (10 : Real) ^ (0.395 : Real) ≤ (8 / 3 : Real) := by
  have hpow : ((((10 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((8 / 3 : Real)) ^ (5 : Nat) := by
    have e : ((((10 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (10 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 10)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 10 2
    rw [e]
    norm_num
  have hstep : (10 : Real) ^ ((2 / 5 : Real)) ≤ (8 / 3 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (10 : Real) ^ (0.395 : Real) ≤ (10 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (8 / 3 : Real) := hstep

/-- Real rpow tenth inverse lower (`3/8 ≤ 10 ^ (-0.395)`) from `10 ^ 0.395 ≤ 8/3`. -/
theorem R05_rpow_ten_neg0395_ge :
    (3 / 8 : Real) ≤ (10 : Real) ^ (-0.395 : Real) := by
  have hle := R05_ten_rpow_le
  have hpos : (0 : Real) < (10 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (10 : Real) ^ (-0.395 : Real) = (((10 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (3 / 8 : Real) = ((8 / 3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Real part of the R05 ninth eta inverse
(`Re (9 ^ s)⁻¹ = 9 ^ (-0.395) * cos (0.75 * log 9)`). -/
theorem R05_inv_nine_cpow_re_eq :
    (((((9 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (9 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 9) := by
  have h9eq : ((((9 : Nat)) : Complex)) = (9 : Complex) := by norm_cast
  rw [h9eq]
  have hlog : Complex.log (9 : Complex) = (((Real.log 9 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 9)).symm
  have hlogre : (Complex.log (9 : Complex)).re = Real.log 9 := by rw [hlog]; rfl
  have hlogim : (Complex.log (9 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (9 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 9 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (9 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 9 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (9 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (9 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (9 : Complex) ≠ 0)]
  have hinv : ((9 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (9 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (9 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 9 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (9 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 9 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (9 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 9 * 0.395)) * Real.cos (-(Real.log 9 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 9 * (-0.75))) = Real.cos (0.75 * Real.log 9) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 9 * 0.395)) = (9 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 9 * 0.395) = Real.log 9 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 9)]
  rw [hinv, hre, hexp, hcos]

/-- Real part of the R05 tenth eta inverse
(`Re (10 ^ s)⁻¹ = 10 ^ (-0.395) * cos (0.75 * log 10)`). -/
theorem R05_inv_ten_cpow_re_eq :
    (((((10 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (10 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 10) := by
  have h10eq : ((((10 : Nat)) : Complex)) = (10 : Complex) := by norm_cast
  rw [h10eq]
  have hlog : Complex.log (10 : Complex) = (((Real.log 10 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 10)).symm
  have hlogre : (Complex.log (10 : Complex)).re = Real.log 10 := by rw [hlog]; rfl
  have hlogim : (Complex.log (10 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (10 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 10 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (10 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 10 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (10 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (10 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (10 : Complex) ≠ 0)]
  have hinv : ((10 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (10 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (10 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 10 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (10 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 10 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (10 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 10 * 0.395)) * Real.cos (-(Real.log 10 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 10 * (-0.75))) = Real.cos (0.75 * Real.log 10) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 10 * 0.395)) = (10 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 10 * 0.395) = Real.log 10 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 10)]
  rw [hinv, hre, hexp, hcos]

/-- R05 ninth eta term in closed form (`term 8 = (9^s)⁻¹`, since `(-1)^8 = 1`). -/
theorem R05_eta_ninth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 8 =
      ((((9 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (8 + 1 : Nat) = 9 := rfl
  have hcast : ((((8 + 1 : Nat)) : Complex)) = ((((9 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (8 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- R05 tenth eta term in closed form (`term 9 = -((10 ^ s)⁻¹)`, since `(-1)^9 = -1`). -/
theorem R05_eta_tenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 9 =
      -((((10 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (9 + 1 : Nat) = 10 := rfl
  have hcast : ((((9 + 1 : Nat)) : Complex)) = ((((10 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (9 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- Real part of the R05 ninth eta term (`-(1/24) ≤ Re term9`,
from `(1/2) * (-1/12)` with amplitude `≤ 1/2` and the negative cosine floor). -/
theorem R05_eta_ninth_Re_ge :
    (-(1 / 24) : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 8).re := by
  rw [R05_eta_ninth_eq, R05_inv_nine_cpow_re_eq]
  have hamp := R05_rpow_nine_neg0395_le
  have hcos := R05_cos_075log9_lower
  have hamp_pos : (0 : Real) < (9 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e1 : (9 : Real) ^ (-0.395 : Real) * (-1 / 12 : Real) ≤
      (9 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 9) :=
    mul_le_mul_of_nonneg_left hcos hamp_pos.le
  have e2 : (1 / 2 : Real) * (-1 / 12 : Real) ≤
      (9 : Real) ^ (-0.395 : Real) * (-1 / 12 : Real) :=
    mul_le_mul_of_nonpos_right hamp (by norm_num)
  have heq : (1 / 2 : Real) * (-1 / 12 : Real) = (-(1 / 24) : Real) := by
    norm_num
  linarith

/-- Real part of the R05 tenth eta term (`3/80 ≤ Re term10`,
from `(3/8) * (1/10)`: the `(-1)^9` sign flips the negative tenth cosine
into a positive contribution). -/
theorem R05_eta_tenth_Re_ge :
    (3 / 80 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 9).re := by
  rw [R05_eta_tenth_eq, Complex.neg_re, R05_inv_ten_cpow_re_eq]
  have hamp := R05_rpow_ten_neg0395_ge
  have hcos := R05_cos_075log10_upper
  have hamp_pos : (0 : Real) < (10 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (1 / 10 : Real) ≤ -(Real.cos (0.75 * Real.log 10)) := by
    linarith
  have hprod : (3 / 8 : Real) * (1 / 10 : Real) ≤
      (10 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 10))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (3 / 8 : Real) * (1 / 10 : Real) = (3 / 80 : Real) := by
    norm_num
  have hsplit : (10 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 10))) =
      -((10 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 10)) := by
    ring
  linarith

/-- Phase-aware fourth-pair floor (`-1/240 ≤ Re pair 4`,
from `-1/24 + 3/80`).
STOP-RULE VERDICT: the floor is NONPOSITIVE (`-1/240 ≤ 0`), so the pair route
stalls here — do NOT push further (`θ9 ≈ 1.648 > π/2` killed the ninth cosine,
and even crediting term 10 its full `+3/80` leaves the pair floor negative). -/
theorem R05_pair4_Re_ge :
    (-1 / 240 : Real) ≤ (etaPairTerm R03R10PolyLower.sR05 4).re := by
  have hp : etaPairTerm R03R10PolyLower.sR05 4 =
      etaDirichletTerm R03R10PolyLower.sR05 8 +
        etaDirichletTerm R03R10PolyLower.sR05 9 := by
    unfold etaPairTerm
    have e0 : 2 * 4 = 8 := by norm_num
    have e1 : 2 * 4 + 1 = 9 := by norm_num
    rw [e0, e1]
  rw [hp, Complex.add_re]
  have ht8 := R05_eta_ninth_Re_ge
  have ht9 := R05_eta_tenth_Re_ge
  have hle : (-1 / 240 : Real) ≤ (-(1 / 24) : Real) + (3 / 80 : Real) := by
    norm_num
  linarith

/-- Stop-rule verdict: the banked pair-4 floor is nonpositive — the pair route ends. -/
theorem R05_pair4_stop :
    (etaPairTerm R03R10PolyLower.sR05 4).re ≥ (-1 / 240 : Real) ∧
      (-1 / 240 : Real) ≤ 0 := by
  exact ⟨R05_pair4_Re_ge, by norm_num⟩

#print axioms R05_nine_rpow_ge
#print axioms R05_rpow_nine_neg0395_le
#print axioms R05_ten_rpow_le
#print axioms R05_rpow_ten_neg0395_ge
#print axioms R05_inv_nine_cpow_re_eq
#print axioms R05_inv_ten_cpow_re_eq
#print axioms R05_eta_ninth_eq
#print axioms R05_eta_tenth_eq
#print axioms R05_eta_ninth_Re_ge
#print axioms R05_eta_tenth_Re_ge
#print axioms R05_pair4_Re_ge
#print axioms R05_pair4_stop

end Door3OffAxis

namespace Door3OffAxis

/-- Genuine R05 paired tail at `M = 4` (`‖G - S₈‖ ≤ 7/5`,
via `zetaCell_even_remainder_le` with the banked `‖sR05‖ ≤ 0.85` upper.
Mirrors banked `R05_eta_tail_2_le` (M = 2 gave `7/4`); here `2 * 4 = 8`
so the partial sum is exactly the eight-term `S₈`. -/
theorem R05_eta_tail_4_le :
    ‖(∑' m, etaPairTerm R03R10PolyLower.sR05 m) -
      (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k)‖ ≤
      (7 / 5 : Real) := by
  have hs : 0 < R03R10PolyLower.sR05.re := by
    rw [R03R10PolyLower.sR05_re]
    norm_num
  have hC : ‖R03R10PolyLower.sR05‖ ≤ (0.85 : Real) := R05_s_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4 (by norm_num)
  have h24 : 2 * 4 = 8 := by norm_num
  rw [h24] at hgen
  have hre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  rw [hre] at hgen
  have h4c : ((((4 : Nat)) : Real)) = (4 : Real) := by norm_cast
  rw [h4c] at hgen
  have hamp := R05_rpow_four_neg0395_le
  have hdiv : (4 : Real) ^ (-0.395 : Real) / (0.395 : Real) ≤
      (16 / 25 : Real) / (0.395 : Real) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : Real) < 0.395)]
    exact hamp
  have hmul : (0.85 : Real) * ((4 : Real) ^ (-0.395 : Real) / (0.395 : Real)) ≤
      (0.85 : Real) * ((16 / 25 : Real) / (0.395 : Real)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (0.85 : Real) * ((16 / 25 : Real) / (0.395 : Real)) ≤
      (7 / 5 : Real) := by
    norm_num
  linarith

/-- Honest S8 residual certificate at `N = 8`: slow `923/2500` (banked
`R05_S8_norm_ge`, `Re`-route), genuine M = 4 tail `7/5`, phase-aware
factor `cF = 1` (`R05_etaFactor_phase_le_one`). Value is negative
(`(923/2500 - 7/5)/1 = -2577/2500`), honestly recording that the
`1/2` threshold stays open on the even-remainder route. -/
noncomputable def R05_S8_finite_zeta_certificate :
    FiniteZetaLowerCertificate R03R10PolyLower.sR05 :=
  { N := 8
    S := ∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k
    slow := 923 / 2500
    rtail := 7 / 5
    cF := 1
    hSdef := rfl
    hSlow := R05_S8_norm_ge
    hTail := R05_eta_tail_4_le
    hcFpos := by norm_num
    hFac := R05_etaFactor_phase_le_one }

/-- The honest S8 certificate wired through the API. -/
theorem R05_S8_zeta_lower :
    ((R05_S8_finite_zeta_certificate.slow - R05_S8_finite_zeta_certificate.rtail) /
      R05_S8_finite_zeta_certificate.cF) ≤ ‖zeta R03R10PolyLower.sR05‖ :=
  R05_S8_finite_zeta_certificate.lower_of_re
    (by rw [R03R10PolyLower.sR05_re]; norm_num)
    (by rw [R03R10PolyLower.sR05_re]; norm_num)

/-- Exact ratio of the honest S8 certificate:
`(923/2500 - 7/5)/1 = -2577/2500`. -/
theorem R05_S8_ratio_eq :
    ((R05_S8_finite_zeta_certificate.slow - R05_S8_finite_zeta_certificate.rtail) /
      R05_S8_finite_zeta_certificate.cF) = (-2577 / 2500 : Real) := by
  have h1 : R05_S8_finite_zeta_certificate.slow = (923 / 2500 : Real) := rfl
  have h2 : R05_S8_finite_zeta_certificate.rtail = (7 / 5 : Real) := rfl
  have h3 : R05_S8_finite_zeta_certificate.cF = (1 : Real) := rfl
  rw [h1, h2, h3]
  norm_num

/-- The honest S8 value sits below `1/2` (threshold open, no overclaim). -/
theorem R05_S8_ratio_lt_half :
    ((R05_S8_finite_zeta_certificate.slow - R05_S8_finite_zeta_certificate.rtail) /
      R05_S8_finite_zeta_certificate.cF) < (1 / 2 : Real) := by
  rw [R05_S8_ratio_eq]
  norm_num

#print axioms R05_eta_tail_4_le
#print axioms R05_S8_finite_zeta_certificate
#print axioms R05_S8_zeta_lower
#print axioms R05_S8_ratio_eq
#print axioms R05_S8_ratio_lt_half

end Door3OffAxis

namespace Door3OffAxis

/-- Log-12 split (`log 12 = log 3 + 2 * log 2`) via `12 = 3 * 4`. -/
theorem R05_log_twelve_eq :
    Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
  have h12 : (12 : Real) = 3 * 4 := by norm_num
  rw [h12, Real.log_mul (by norm_num) (by norm_num)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h4e : (4 : Real) = 2 * 2 := by norm_num
    rw [h4e, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4]

/-- Phase of the R05 twelfth eta term (`0.75 * log 12` in `[1.8636, 1.8637]`)
from the banked `log 2` / `log 3` d9 bounds via `R05_log_twelve_eq`. -/
theorem R05_theta12_mem :
    (1.8636 : Real) ≤ 0.75 * Real.log 12 ∧ 0.75 * Real.log 12 ≤ (1.8637 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hx : 0.75 * Real.log 12 = 0.75 * Real.log 3 + 1.5 * Real.log 2 := by
    rw [R05_log_twelve_eq]
    ring
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the twelfth-term phase (`cos (0.75 * log 12) ≤ -1/5`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log12_upper :
    Real.cos (0.75 * Real.log 12) ≤ (-1 / 5 : Real) := by
  have hmem := R05_theta12_mem
  have hpos : (0 : Real) < Real.log 12 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 12 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.8636 : Real) ≤ 0.75 * Real.log 12 := hmem.1
  have hhi : 0.75 * Real.log 12 ≤ (1.8637 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.8636 : Real) ^ 2 ≤ (0.75 * Real.log 12) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 12) ^ 4 ≤ (1.8637 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.8636 : Real) ^ 2 / 2 + (1.8637 : Real) ^ 4 / 24 ≤
      (-1 / 5 : Real) := by
    norm_num
  linarith

#print axioms R05_log_twelve_eq
#print axioms R05_theta12_mem
#print axioms R05_cos_075log12_upper

/-- Rpow upper (`12 ^ 0.395 ≤ 3`) via cleared `(12 ^ (2/5)) ^ 5 = 144 ≤ 243`. -/
theorem R05_twelve_rpow_le : (12 : Real) ^ (0.395 : Real) ≤ (3 : Real) := by
  have hpow : ((((12 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((3 : Real)) ^ (5 : Nat) := by
    have e : ((((12 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (12 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 12)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 12 2
    rw [e]
    norm_num
  have hstep : (12 : Real) ^ ((2 / 5 : Real)) ≤ (3 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (12 : Real) ^ (0.395 : Real) ≤ (12 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (3 : Real) := hstep

/-- Real rpow twelfth inverse lower (`1/3 ≤ 12 ^ (-0.395)`) from `12 ^ 0.395 ≤ 3`. -/
theorem R05_rpow_twelve_neg0395_ge :
    (1 / 3 : Real) ≤ (12 : Real) ^ (-0.395 : Real) := by
  have hle := R05_twelve_rpow_le
  have hpos : (0 : Real) < (12 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (12 : Real) ^ (-0.395 : Real) = (((12 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 3 : Real) = ((3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_twelve_rpow_le
#print axioms R05_rpow_twelve_neg0395_ge

/-- Real part of the R05 twelfth eta inverse
(`Re (12 ^ s)⁻¹ = 12 ^ (-0.395) * cos (0.75 * log 12)`). -/
theorem R05_inv_twelve_cpow_re_eq :
    (((((12 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (12 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 12) := by
  have h12eq : ((((12 : Nat)) : Complex)) = (12 : Complex) := by norm_cast
  rw [h12eq]
  have hlog : Complex.log (12 : Complex) = (((Real.log 12 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 12)).symm
  have hlogre : (Complex.log (12 : Complex)).re = Real.log 12 := by rw [hlog]; rfl
  have hlogim : (Complex.log (12 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (12 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 12 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (12 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 12 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (12 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (12 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (12 : Complex) ≠ 0)]
  have hinv : ((12 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (12 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (12 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 12 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (12 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 12 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (12 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 12 * 0.395)) * Real.cos (-(Real.log 12 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 12 * (-0.75))) = Real.cos (0.75 * Real.log 12) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 12 * 0.395)) = (12 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 12 * 0.395) = Real.log 12 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 12)]
  rw [hinv, hre, hexp, hcos]

/-- R05 twelfth eta term in closed form (`term 11 = -((12 ^ s)⁻¹)`, since `(-1)^11 = -1`). -/
theorem R05_eta_twelfth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 11 =
      -((((12 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (11 + 1 : Nat) = 12 := rfl
  have hcast : ((((11 + 1 : Nat)) : Complex)) = ((((12 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (11 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

#print axioms R05_inv_twelve_cpow_re_eq
#print axioms R05_eta_twelfth_eq

/-- Real part of the R05 twelfth eta term (`1/15 ≤ Re term12`,
from `(1/3) * (1/5)`: the `(-1)^11` sign flips the negative twelfth cosine
into a positive contribution). -/
theorem R05_eta_twelfth_Re_ge :
    (1 / 15 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 11).re := by
  rw [R05_eta_twelfth_eq, Complex.neg_re, R05_inv_twelve_cpow_re_eq]
  have hamp := R05_rpow_twelve_neg0395_ge
  have hcos := R05_cos_075log12_upper
  have hamp_pos : (0 : Real) < (12 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (1 / 5 : Real) ≤ -(Real.cos (0.75 * Real.log 12)) := by
    linarith
  have hprod : (1 / 3 : Real) * (1 / 5 : Real) ≤
      (12 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 12))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (1 / 3 : Real) * (1 / 5 : Real) = (1 / 15 : Real) := by
    norm_num
  have hsplit : (12 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 12))) =
      -((12 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 12)) := by
    ring
  linarith

#print axioms R05_eta_twelfth_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Nine-term split (`S9 = S8 + term 8`, non-pair slow-sum step). -/
theorem R05_S9_eq :
    (∑ k ∈ Finset.range 9, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 8, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 8 := by
  rw [show (9 : Nat) = 8 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 nine-term real part (`4913/15000 ≤ Re S9`,
from `923/2500 - 1/24`). -/
theorem R05_S9_Re_ge :
    (4913 / 15000 : Real) ≤
      (∑ k ∈ Finset.range 9, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S9_eq, Complex.add_re]
  have hS8 := R05_S8_Re_ge
  have ht := R05_eta_ninth_Re_ge
  have hle : (4913 / 15000 : Real) ≤ (923 / 2500 : Real) + (-(1 / 24) : Real) := by
    norm_num
  linarith

#print axioms R05_S9_eq
#print axioms R05_S9_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Ten-term split (`S10 = S9 + term 9`, non-pair slow-sum step). -/
theorem R05_S10_eq :
    (∑ k ∈ Finset.range 10, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 9, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 9 := by
  rw [show (10 : Nat) = 9 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 ten-term real part (`10951/30000 ≤ Re S10`,
from `4913/15000 + 3/80`). -/
theorem R05_S10_Re_ge :
    (10951 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 10, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S10_eq, Complex.add_re]
  have hS9 := R05_S9_Re_ge
  have ht := R05_eta_tenth_Re_ge
  have hle : (10951 / 30000 : Real) ≤ (4913 / 15000 : Real) + (3 / 80 : Real) := by
    norm_num
  linarith

#print axioms R05_S10_eq
#print axioms R05_S10_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Log-14 split (`log 14 = log 2 + log 7`) via `14 = 2 * 7`. -/
theorem R05_log_fourteen_eq :
    Real.log 14 = Real.log 2 + Real.log 7 := by
  have h14 : (14 : Real) = 2 * 7 := by norm_num
  rw [h14, Real.log_mul (by norm_num) (by norm_num)]

/-- Phase of the R05 thirteenth eta term (`0.75 * log 14` in `[1.9722, 1.9858]`)
from the `log 2` d9 bounds and banked `R05_log_seven` bounds
via `R05_log_fourteen_eq`. -/
theorem R05_theta14_mem :
    (1.9722 : Real) ≤ 0.75 * Real.log 14 ∧ 0.75 * Real.log 14 ≤ (1.9858 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h7lo := R05_log_seven_ge
  have h7hi := R05_log_seven_le
  have hx : 0.75 * Real.log 14 = 0.75 * (Real.log 2 + Real.log 7) := by
    rw [R05_log_fourteen_eq]
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the thirteenth-term phase (`cos (0.75 * log 14) ≤ -1/4`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log14_upper :
    Real.cos (0.75 * Real.log 14) ≤ (-1 / 4 : Real) := by
  have hmem := R05_theta14_mem
  have hpos : (0 : Real) < Real.log 14 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 14 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (1.9722 : Real) ≤ 0.75 * Real.log 14 := hmem.1
  have hhi : 0.75 * Real.log 14 ≤ (1.9858 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (1.9722 : Real) ^ 2 ≤ (0.75 * Real.log 14) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 14) ^ 4 ≤ (1.9858 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (1.9722 : Real) ^ 2 / 2 + (1.9858 : Real) ^ 4 / 24 ≤
      (-1 / 4 : Real) := by
    norm_num
  linarith

#print axioms R05_log_fourteen_eq
#print axioms R05_theta14_mem
#print axioms R05_cos_075log14_upper

end Door3OffAxis

namespace Door3OffAxis

/-- Rpow upper (`14 ^ 0.395 ≤ 3`) via cleared `(14 ^ (2/5)) ^ 5 = 196 ≤ 243`. -/
theorem R05_fourteen_rpow_le : (14 : Real) ^ (0.395 : Real) ≤ (3 : Real) := by
  have hpow : ((((14 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((3 : Real)) ^ (5 : Nat) := by
    have e : ((((14 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (14 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 14)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 14 2
    rw [e]
    norm_num
  have hstep : (14 : Real) ^ ((2 / 5 : Real)) ≤ (3 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (14 : Real) ^ (0.395 : Real) ≤ (14 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (3 : Real) := hstep

/-- Real rpow fourteenth inverse lower (`1/3 ≤ 14 ^ (-0.395)`) from `14 ^ 0.395 ≤ 3`. -/
theorem R05_rpow_fourteen_neg0395_ge :
    (1 / 3 : Real) ≤ (14 : Real) ^ (-0.395 : Real) := by
  have hle := R05_fourteen_rpow_le
  have hpos : (0 : Real) < (14 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (14 : Real) ^ (-0.395 : Real) = (((14 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 3 : Real) = ((3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_fourteen_rpow_le
#print axioms R05_rpow_fourteen_neg0395_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 fourteenth eta inverse
(`Re (14 ^ s)⁻¹ = 14 ^ (-0.395) * cos (0.75 * log 14)`). -/
theorem R05_inv_fourteen_cpow_re_eq :
    (((((14 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (14 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 14) := by
  have h14eq : ((((14 : Nat)) : Complex)) = (14 : Complex) := by norm_cast
  rw [h14eq]
  have hlog : Complex.log (14 : Complex) = (((Real.log 14 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 14)).symm
  have hlogre : (Complex.log (14 : Complex)).re = Real.log 14 := by rw [hlog]; rfl
  have hlogim : (Complex.log (14 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (14 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 14 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (14 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 14 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (14 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (14 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (14 : Complex) ≠ 0)]
  have hinv : ((14 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (14 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (14 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 14 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (14 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 14 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (14 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 14 * 0.395)) * Real.cos (-(Real.log 14 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 14 * (-0.75))) = Real.cos (0.75 * Real.log 14) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 14 * 0.395)) = (14 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 14 * 0.395) = Real.log 14 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 14)]
  rw [hinv, hre, hexp, hcos]

/-- R05 fourteenth eta term in closed form (`term 13 = -((14 ^ s)⁻¹)`,
k = 13, n = 14, since `(-1)^13 = -1`). -/
theorem R05_eta_fourteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 13 =
      -((((14 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (13 + 1 : Nat) = 14 := rfl
  have hcast : ((((13 + 1 : Nat)) : Complex)) = ((((14 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (13 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

#print axioms R05_inv_fourteen_cpow_re_eq
#print axioms R05_eta_fourteenth_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 fourteenth eta term (`1/12 ≤ Re term14`,
from `(1/3) * (1/4)`: the `(-1)^13` sign flips the negative fourteenth cosine
into a positive contribution). -/
theorem R05_eta_fourteenth_Re_ge :
    (1 / 12 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 13).re := by
  rw [R05_eta_fourteenth_eq, Complex.neg_re, R05_inv_fourteen_cpow_re_eq]
  have hamp := R05_rpow_fourteen_neg0395_ge
  have hcos := R05_cos_075log14_upper
  have hamp_pos : (0 : Real) < (14 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (1 / 4 : Real) ≤ -(Real.cos (0.75 * Real.log 14)) := by
    linarith
  have hprod : (1 / 3 : Real) * (1 / 4 : Real) ≤
      (14 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 14))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (1 / 3 : Real) * (1 / 4 : Real) = (1 / 12 : Real) := by
    norm_num
  have hsplit : (14 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 14))) =
      -((14 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 14)) := by
    ring
  linarith

#print axioms R05_eta_fourteenth_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Log-16 double-double (`log 16 = 4 * log 2`) via `16 = 4 * 4`. -/
theorem R05_log_sixteen_eq :
    Real.log 16 = 4 * Real.log 2 := by
  have h16 : (16 : Real) = 4 * 4 := by norm_num
  rw [h16, Real.log_mul (by norm_num) (by norm_num)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h4e : (4 : Real) = 2 * 2 := by norm_num
    rw [h4e, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4]
  ring

/-- Phase of the R05 sixteenth eta term (`0.75 * log 16` in `[2.0794, 2.0795]`)
from the banked `log 2` d9 bounds via `R05_log_sixteen_eq`. -/
theorem R05_theta16_mem :
    (2.0794 : Real) ≤ 0.75 * Real.log 16 ∧ 0.75 * Real.log 16 ≤ (2.0795 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hx : 0.75 * Real.log 16 = 3 * Real.log 2 := by
    rw [R05_log_sixteen_eq]
    ring
  constructor <;> rw [hx] <;> linarith

/-- Cosine upper at the sixteenth-term phase (`cos (0.75 * log 16) ≤ -1/3`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log16_upper :
    Real.cos (0.75 * Real.log 16) ≤ (-1 / 3 : Real) := by
  have hmem := R05_theta16_mem
  have hpos : (0 : Real) < Real.log 16 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 16 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.0794 : Real) ≤ 0.75 * Real.log 16 := hmem.1
  have hhi : 0.75 * Real.log 16 ≤ (2.0795 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (2.0794 : Real) ^ 2 ≤ (0.75 * Real.log 16) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 16) ^ 4 ≤ (2.0795 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (2.0794 : Real) ^ 2 / 2 + (2.0795 : Real) ^ 4 / 24 ≤
      (-1 / 3 : Real) := by
    norm_num
  linarith

#print axioms R05_log_sixteen_eq
#print axioms R05_theta16_mem
#print axioms R05_cos_075log16_upper

end Door3OffAxis

namespace Door3OffAxis

/-- Rpow upper (`16 ^ 0.395 ≤ 16/5`) via cleared `(16 ^ (2/5)) ^ 5 = 256 ≤ 335`. -/
theorem R05_sixteen_rpow_le : (16 : Real) ^ (0.395 : Real) ≤ (16 / 5 : Real) := by
  have hpow : ((((16 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((16 / 5 : Real)) ^ (5 : Nat) := by
    have e : ((((16 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (16 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 16)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 16 2
    rw [e]
    norm_num
  have hstep : (16 : Real) ^ ((2 / 5 : Real)) ≤ (16 / 5 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (16 : Real) ^ (0.395 : Real) ≤ (16 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (16 / 5 : Real) := hstep

/-- Real rpow sixteenth inverse lower (`5/16 ≤ 16 ^ (-0.395)`)
from `16 ^ 0.395 ≤ 16/5`. -/
theorem R05_rpow_sixteen_neg0395_ge :
    (5 / 16 : Real) ≤ (16 : Real) ^ (-0.395 : Real) := by
  have hle := R05_sixteen_rpow_le
  have hpos : (0 : Real) < (16 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (16 : Real) ^ (-0.395 : Real) = (((16 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (5 / 16 : Real) = ((16 / 5 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_sixteen_rpow_le
#print axioms R05_rpow_sixteen_neg0395_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 sixteenth eta inverse
(`Re (16 ^ s)⁻¹ = 16 ^ (-0.395) * cos (0.75 * log 16)`). -/
theorem R05_inv_sixteen_cpow_re_eq :
    (((((16 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (16 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 16) := by
  have h16eq : ((((16 : Nat)) : Complex)) = (16 : Complex) := by norm_cast
  rw [h16eq]
  have hlog : Complex.log (16 : Complex) = (((Real.log 16 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 16)).symm
  have hlogre : (Complex.log (16 : Complex)).re = Real.log 16 := by rw [hlog]; rfl
  have hlogim : (Complex.log (16 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (16 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 16 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (16 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 16 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (16 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (16 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (16 : Complex) ≠ 0)]
  have hinv : ((16 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (16 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (16 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 16 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (16 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 16 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (16 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 16 * 0.395)) * Real.cos (-(Real.log 16 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 16 * (-0.75))) = Real.cos (0.75 * Real.log 16) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 16 * 0.395)) = (16 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 16 * 0.395) = Real.log 16 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 16)]
  rw [hinv, hre, hexp, hcos]

/-- R05 sixteenth eta term in closed form (`term 15 = -((16 ^ s)⁻¹)`,
k = 15, n = 16, since `(-1)^15 = -1`). -/
theorem R05_eta_sixteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 15 =
      -((((16 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (15 + 1 : Nat) = 16 := rfl
  have hcast : ((((15 + 1 : Nat)) : Complex)) = ((((16 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (15 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- Real part of the R05 sixteenth eta term (`1/10 ≤ Re term16`,
from `(5/16) * (1/3) = 5/48 ≥ 1/10`: the `(-1)^15` sign flips the negative
sixteenth cosine into a positive contribution). -/
theorem R05_eta_sixteenth_Re_ge :
    (1 / 10 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 15).re := by
  rw [R05_eta_sixteenth_eq, Complex.neg_re, R05_inv_sixteen_cpow_re_eq]
  have hamp := R05_rpow_sixteen_neg0395_ge
  have hcos := R05_cos_075log16_upper
  have hamp_pos : (0 : Real) < (16 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (1 / 3 : Real) ≤ -(Real.cos (0.75 * Real.log 16)) := by
    linarith
  have hprod : (5 / 16 : Real) * (1 / 3 : Real) ≤
      (16 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 16))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (5 / 16 : Real) * (1 / 3 : Real) = (5 / 48 : Real) := by
    norm_num
  have hle : (1 / 10 : Real) ≤ (5 / 48 : Real) := by norm_num
  have hsplit : (16 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 16))) =
      -((16 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 16)) := by
    ring
  linarith

#print axioms R05_inv_sixteen_cpow_re_eq
#print axioms R05_eta_sixteenth_eq
#print axioms R05_eta_sixteenth_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Fresh `log 11` lower bound (`2.3939 ≤ log 11`) via `log 12` and `log (11/12) ≥ -1/11`. -/
theorem R05_log_eleven_ge :
    (2.3939 : Real) ≤ Real.log 11 := by
  have h12 := R05_log_twelve_eq
  have hub : Real.log (12 / 11 : Real) ≤ (1 / 11 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 12 / 11)
    have he : (12 / 11 : Real) - 1 = (1 / 11 : Real) := by norm_num
    linarith
  have hinv : Real.log (11 / 12 : Real) = -Real.log (12 / 11 : Real) := by
    have heq : (11 / 12 : Real) = (12 / 11 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have h3lo : (1.098612 : Real) < Real.log 3 := by
    have h9 := Real.log_three_gt_d9
    linarith
  have hmeq : (12 : Real) * (11 / 12) = 11 := by norm_num
  have hlog11 : Real.log 11 = Real.log 3 + 2 * Real.log 2 + Real.log (11 / 12 : Real) := by
    have h := Real.log_mul (show (12 : Real) ≠ 0 by norm_num)
      (show (11 / 12 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h12] at h
    exact h
  have hfin : (2.3939 : Real) ≤ 1.098612 + 2 * (0.693147 : Real) - (1 / 11 : Real) := by
    norm_num
  rw [hlog11, hinv]
  linarith

/-- Fresh `log 11` upper bound (`log 11 ≤ 2.4016`) via `log 12` and `log (11/12) ≤ -1/12`. -/
theorem R05_log_eleven_le :
    Real.log 11 ≤ (2.4016 : Real) := by
  have h12 := R05_log_twelve_eq
  have hub : Real.log (11 / 12 : Real) ≤ (-1 / 12 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 11 / 12)
    have he : (11 / 12 : Real) - 1 = (-1 / 12 : Real) := by norm_num
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have h3hi : Real.log 3 < (1.098613 : Real) := by
    have h9 := Real.log_three_lt_d9
    linarith
  have hmeq : (12 : Real) * (11 / 12) = 11 := by norm_num
  have hlog11 : Real.log 11 = Real.log 3 + 2 * Real.log 2 + Real.log (11 / 12 : Real) := by
    have h := Real.log_mul (show (12 : Real) ≠ 0 by norm_num)
      (show (11 / 12 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h12] at h
    exact h
  have hfin : 1.098613 + 2 * (0.693148 : Real) + (-1 / 12 : Real) ≤ (2.4016 : Real) := by
    norm_num
  rw [hlog11]
  linarith

#print axioms R05_log_eleven_ge
#print axioms R05_log_eleven_le

end Door3OffAxis

namespace Door3OffAxis

/-- Cosine lower at the eleventh-term phase (`-1/4 ≤ cos (0.75 * log 11)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log11_lower :
    (-1 / 4 : Real) ≤ Real.cos (0.75 * Real.log 11) := by
  have hloge := R05_log_eleven_ge
  have hlogl := R05_log_eleven_le
  have hlo : (1.7954 : Real) ≤ 0.75 * Real.log 11 := by linarith
  have hhi : 0.75 * Real.log 11 ≤ (1.8012 : Real) := by linarith
  have hpos : (0 : Real) < Real.log 11 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 11 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 11) ^ 2 ≤ (1.8012 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.7954 : Real) ^ 4 ≤ (0.75 * Real.log 11) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 11) ^ 6 ≤ (1.8012 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-1 / 4 : Real) ≤
      1 - (1.8012 : Real) ^ 2 / 2 + (1.7954 : Real) ^ 4 / 24 -
        (1.8012 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real rpow eleventh inverse upper (`11 ^ (-0.395) ≤ 1/2`) from `2 ≤ 11 ^ 0.395`
(cleared `(11 ^ (1/3)) ^ 3 = 11 ≥ 8`, then `1/3 ≤ 0.395`). -/
theorem R05_rpow_eleven_neg0395_le :
    (11 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hge : (2 : Real) ≤ (11 : Real) ^ (0.395 : Real) := by
    have hpow : ((2 : Real)) ^ (3 : Nat) ≤ ((((11 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((11 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (11 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 11)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 11 1
      rw [e]
      norm_num
    have hstep : (2 : Real) ≤ (11 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc (2 : Real) ≤ (11 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (11 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (11 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (11 : Real) ^ (-0.395 : Real) = (((11 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_cos_075log11_lower
#print axioms R05_rpow_eleven_neg0395_le

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 eleventh eta inverse
(`Re (11 ^ s)⁻¹ = 11 ^ (-0.395) * cos (0.75 * log 11)`). -/
theorem R05_inv_eleven_cpow_re_eq :
    (((((11 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (11 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 11) := by
  have h11eq : ((((11 : Nat)) : Complex)) = (11 : Complex) := by norm_cast
  rw [h11eq]
  have hlog : Complex.log (11 : Complex) = (((Real.log 11 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 11)).symm
  have hlogre : (Complex.log (11 : Complex)).re = Real.log 11 := by rw [hlog]; rfl
  have hlogim : (Complex.log (11 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (11 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 11 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (11 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 11 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (11 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (11 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (11 : Complex) ≠ 0)]
  have hinv : ((11 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (11 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (11 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 11 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (11 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 11 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (11 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 11 * 0.395)) * Real.cos (-(Real.log 11 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 11 * (-0.75))) = Real.cos (0.75 * Real.log 11) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 11 * 0.395)) = (11 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 11 * 0.395) = Real.log 11 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 11)]
  rw [hinv, hre, hexp, hcos]

/-- R05 eleventh eta term in closed form (`term 10 = ((11 ^ s)⁻¹)`, since `(-1)^10 = 1`). -/
theorem R05_eta_eleventh_eq :
    etaDirichletTerm R03R10PolyLower.sR05 10 =
      ((((11 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (10 + 1 : Nat) = 11 := rfl
  have hcast : ((((10 + 1 : Nat)) : Complex)) = ((((11 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (10 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_eleven_cpow_re_eq
#print axioms R05_eta_eleventh_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 eleventh eta term (`-1/8 ≤ Re term11`, honest negative floor:
k = 10 even so the sign is `+1`, and `θ11 ≈ 1.80 past π/2` makes the cosine negative). -/
theorem R05_eta_eleventh_Re_ge :
    (-1 / 8 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 10).re := by
  rw [R05_eta_eleventh_eq, R05_inv_eleven_cpow_re_eq]
  have hamp := R05_rpow_eleven_neg0395_le
  have hcos := R05_cos_075log11_lower
  have hamp_pos : (0 : Real) < (11 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (11 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 11) + 1 / 4) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 2 - (11 : Real) ^ (-0.395 : Real)) * (1 / 4 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Eleven-term split (`S11 = S10 + term 10`, non-pair slow-sum step). -/
theorem R05_S11_eq :
    (∑ k ∈ Finset.range 11, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 10, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 10 := by
  rw [show (11 : Nat) = 10 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 eleven-term real part (`7201/30000 ≤ Re S11`, from `10951/30000 - 1/8`). -/
theorem R05_S11_Re_ge :
    (7201 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 11, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S11_eq, Complex.add_re]
  have hS10 := R05_S10_Re_ge
  have ht := R05_eta_eleventh_Re_ge
  have hle : (7201 / 30000 : Real) ≤ (10951 / 30000 : Real) + (-(1 / 8) : Real) := by
    norm_num
  linarith

/-- Twelve-term split (`S12 = S11 + term 11`, non-pair slow-sum step). -/
theorem R05_S12_eq :
    (∑ k ∈ Finset.range 12, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 11, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 11 := by
  rw [show (12 : Nat) = 11 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 twelve-term real part (`3067/10000 ≤ Re S12`, from `7201/30000 + 1/15`). -/
theorem R05_S12_Re_ge :
    (3067 / 10000 : Real) ≤
      (∑ k ∈ Finset.range 12, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S12_eq, Complex.add_re]
  have hS11 := R05_S11_Re_ge
  have ht := R05_eta_twelfth_Re_ge
  have hle : (3067 / 10000 : Real) ≤ (7201 / 30000 : Real) + (1 / 15 : Real) := by
    norm_num
  linarith

#print axioms R05_eta_eleventh_Re_ge
#print axioms R05_S11_eq
#print axioms R05_S11_Re_ge
#print axioms R05_S12_eq
#print axioms R05_S12_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Fresh `log 13` lower bound (`2.5618 ≤ log 13`) via `log 12` and `log (13/12) ≥ 1/13`. -/
theorem R05_log_thirteen_ge :
    (2.5618 : Real) ≤ Real.log 13 := by
  have h12 := R05_log_twelve_eq
  have hub : Real.log (12 / 13 : Real) ≤ (-1 / 13 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 12 / 13)
    have he : (12 / 13 : Real) - 1 = (-1 / 13 : Real) := by norm_num
    linarith
  have hinv : Real.log (13 / 12 : Real) = -Real.log (12 / 13 : Real) := by
    have heq : (13 / 12 : Real) = (12 / 13 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have h3lo : (1.098612 : Real) < Real.log 3 := by
    have h9 := Real.log_three_gt_d9
    linarith
  have hmeq : (12 : Real) * (13 / 12) = 13 := by norm_num
  have hlog13 : Real.log 13 = Real.log 3 + 2 * Real.log 2 + Real.log (13 / 12 : Real) := by
    have h := Real.log_mul (show (12 : Real) ≠ 0 by norm_num)
      (show (13 / 12 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h12] at h
    exact h
  have hfin : (2.5618 : Real) ≤ 1.098612 + 2 * (0.693147 : Real) + (1 / 13 : Real) := by
    norm_num
  rw [hlog13, hinv]
  linarith

/-- Fresh `log 13` upper bound (`log 13 ≤ 2.5683`) via `log 12` and `log (13/12) ≤ 1/12`. -/
theorem R05_log_thirteen_le :
    Real.log 13 ≤ (2.5683 : Real) := by
  have h12 := R05_log_twelve_eq
  have hub : Real.log (13 / 12 : Real) ≤ (1 / 12 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 13 / 12)
    have he : (13 / 12 : Real) - 1 = (1 / 12 : Real) := by norm_num
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have h3hi : Real.log 3 < (1.098613 : Real) := by
    have h9 := Real.log_three_lt_d9
    linarith
  have hmeq : (12 : Real) * (13 / 12) = 13 := by norm_num
  have hlog13 : Real.log 13 = Real.log 3 + 2 * Real.log 2 + Real.log (13 / 12 : Real) := by
    have h := Real.log_mul (show (12 : Real) ≠ 0 by norm_num)
      (show (13 / 12 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h12] at h
    exact h
  have hfin : 1.098613 + 2 * (0.693148 : Real) + (1 / 12 : Real) ≤ (2.5683 : Real) := by
    norm_num
  rw [hlog13]
  linarith

#print axioms R05_log_thirteen_ge
#print axioms R05_log_thirteen_le

end Door3OffAxis

namespace Door3OffAxis

/-- Cosine lower at the thirteenth-term phase (`-2/5 ≤ cos (0.75 * log 13)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log13_lower :
    (-2 / 5 : Real) ≤ Real.cos (0.75 * Real.log 13) := by
  have hloge := R05_log_thirteen_ge
  have hlogl := R05_log_thirteen_le
  have hlo : (1.9213 : Real) ≤ 0.75 * Real.log 13 := by linarith
  have hhi : 0.75 * Real.log 13 ≤ (1.9263 : Real) := by linarith
  have hpos : (0 : Real) < Real.log 13 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 13 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 13) ^ 2 ≤ (1.9263 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (1.9213 : Real) ^ 4 ≤ (0.75 * Real.log 13) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 13) ^ 6 ≤ (1.9263 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-2 / 5 : Real) ≤
      1 - (1.9263 : Real) ^ 2 / 2 + (1.9213 : Real) ^ 4 / 24 -
        (1.9263 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real rpow thirteenth inverse upper (`13 ^ (-0.395) ≤ 1/2`) from `2 ≤ 13 ^ 0.395`
(cleared `(13 ^ (1/3)) ^ 3 = 13 ≥ 8`, then `1/3 ≤ 0.395`). -/
theorem R05_rpow_thirteen_neg0395_le :
    (13 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hge : (2 : Real) ≤ (13 : Real) ^ (0.395 : Real) := by
    have hpow : ((2 : Real)) ^ (3 : Nat) ≤ ((((13 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((13 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (13 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 13)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 13 1
      rw [e]
      norm_num
    have hstep : (2 : Real) ≤ (13 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc (2 : Real) ≤ (13 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (13 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (13 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (13 : Real) ^ (-0.395 : Real) = (((13 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_cos_075log13_lower
#print axioms R05_rpow_thirteen_neg0395_le

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 thirteenth eta inverse
(`Re (13 ^ s)⁻¹ = 13 ^ (-0.395) * cos (0.75 * log 13)`). -/
theorem R05_inv_thirteen_cpow_re_eq :
    (((((13 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (13 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 13) := by
  have h13eq : ((((13 : Nat)) : Complex)) = (13 : Complex) := by norm_cast
  rw [h13eq]
  have hlog : Complex.log (13 : Complex) = (((Real.log 13 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 13)).symm
  have hlogre : (Complex.log (13 : Complex)).re = Real.log 13 := by rw [hlog]; rfl
  have hlogim : (Complex.log (13 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (13 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 13 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (13 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 13 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (13 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (13 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (13 : Complex) ≠ 0)]
  have hinv : ((13 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (13 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (13 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 13 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (13 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 13 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (13 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 13 * 0.395)) * Real.cos (-(Real.log 13 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 13 * (-0.75))) = Real.cos (0.75 * Real.log 13) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 13 * 0.395)) = (13 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 13 * 0.395) = Real.log 13 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 13)]
  rw [hinv, hre, hexp, hcos]

/-- R05 thirteenth eta term in closed form (`term 12 = ((13 ^ s)⁻¹)`, since `(-1)^12 = 1`). -/
theorem R05_eta_thirteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 12 =
      ((((13 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (12 + 1 : Nat) = 13 := rfl
  have hcast : ((((12 + 1 : Nat)) : Complex)) = ((((13 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (12 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_thirteen_cpow_re_eq
#print axioms R05_eta_thirteenth_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 thirteenth eta term (`-1/5 ≤ Re term13`, honest negative floor:
k = 12 even so the sign is `+1`, and `θ13 ≈ 1.92 past π/2` makes the cosine negative). -/
theorem R05_eta_thirteenth_Re_ge :
    (-1 / 5 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 12).re := by
  rw [R05_eta_thirteenth_eq, R05_inv_thirteen_cpow_re_eq]
  have hamp := R05_rpow_thirteen_neg0395_le
  have hcos := R05_cos_075log13_lower
  have hamp_pos : (0 : Real) < (13 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (13 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 13) + 2 / 5) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 2 - (13 : Real) ^ (-0.395 : Real)) * (2 / 5 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Thirteen-term split (`S13 = S12 + term 12`, non-pair slow-sum step). -/
theorem R05_S13_eq :
    (∑ k ∈ Finset.range 13, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 12, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 12 := by
  rw [show (13 : Nat) = 12 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 thirteen-term real part (`1067/10000 ≤ Re S13`, from `3067/10000 - 1/5`). -/
theorem R05_S13_Re_ge :
    (1067 / 10000 : Real) ≤
      (∑ k ∈ Finset.range 13, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S13_eq, Complex.add_re]
  have hS12 := R05_S12_Re_ge
  have ht := R05_eta_thirteenth_Re_ge
  have hle : (1067 / 10000 : Real) ≤ (3067 / 10000 : Real) + (-(1 / 5) : Real) := by
    norm_num
  linarith

/-- Fourteen-term split (`S14 = S13 + term 13`, non-pair slow-sum step). -/
theorem R05_S14_eq :
    (∑ k ∈ Finset.range 14, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 13, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 13 := by
  rw [show (14 : Nat) = 13 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 fourteen-term real part (`5701/30000 ≤ Re S14`, from `1067/10000 + 1/12`). -/
theorem R05_S14_Re_ge :
    (5701 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 14, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S14_eq, Complex.add_re]
  have hS13 := R05_S13_Re_ge
  have ht := R05_eta_fourteenth_Re_ge
  have hle : (5701 / 30000 : Real) ≤ (1067 / 10000 : Real) + (1 / 12 : Real) := by
    norm_num
  linarith

#print axioms R05_eta_thirteenth_Re_ge
#print axioms R05_S13_eq
#print axioms R05_S13_Re_ge
#print axioms R05_S14_eq
#print axioms R05_S14_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Fresh `log 15` lower bound (`2.7059 ≤ log 15`) via `log 16` and `log (15/16) ≥ -1/15`. -/
theorem R05_log_fifteen_ge :
    (2.7059 : Real) ≤ Real.log 15 := by
  have h16 := R05_log_sixteen_eq
  have hub : Real.log (16 / 15 : Real) ≤ (1 / 15 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 16 / 15)
    have he : (16 / 15 : Real) - 1 = (1 / 15 : Real) := by norm_num
    linarith
  have hinv : Real.log (15 / 16 : Real) = -Real.log (16 / 15 : Real) := by
    have heq : (15 / 16 : Real) = (16 / 15 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have hmeq : (16 : Real) * (15 / 16) = 15 := by norm_num
  have hlog15 : Real.log 15 = 4 * Real.log 2 + Real.log (15 / 16 : Real) := by
    have h := Real.log_mul (show (16 : Real) ≠ 0 by norm_num)
      (show (15 / 16 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h16] at h
    exact h
  have hfin : (2.7059 : Real) ≤ 4 * (0.693147 : Real) - (1 / 15 : Real) := by
    norm_num
  rw [hlog15, hinv]
  linarith

/-- Fresh `log 15` upper bound (`log 15 ≤ 2.7101`) via `log 16` and `log (15/16) ≤ -1/16`. -/
theorem R05_log_fifteen_le :
    Real.log 15 ≤ (2.7101 : Real) := by
  have h16 := R05_log_sixteen_eq
  have hub : Real.log (15 / 16 : Real) ≤ (-1 / 16 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 15 / 16)
    have he : (15 / 16 : Real) - 1 = (-1 / 16 : Real) := by norm_num
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have hmeq : (16 : Real) * (15 / 16) = 15 := by norm_num
  have hlog15 : Real.log 15 = 4 * Real.log 2 + Real.log (15 / 16 : Real) := by
    have h := Real.log_mul (show (16 : Real) ≠ 0 by norm_num)
      (show (15 / 16 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h16] at h
    exact h
  have hfin : 4 * (0.693148 : Real) + (-1 / 16 : Real) ≤ (2.7101 : Real) := by
    norm_num
  rw [hlog15]
  linarith

#print axioms R05_log_fifteen_ge
#print axioms R05_log_fifteen_le

end Door3OffAxis

namespace Door3OffAxis

/-- Cosine lower at the fifteenth-term phase (`-1/2 ≤ cos (0.75 * log 15)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log15_lower :
    (-1 / 2 : Real) ≤ Real.cos (0.75 * Real.log 15) := by
  have hloge := R05_log_fifteen_ge
  have hlogl := R05_log_fifteen_le
  have hlo : (2.0294 : Real) ≤ 0.75 * Real.log 15 := by linarith
  have hhi : 0.75 * Real.log 15 ≤ (2.0326 : Real) := by linarith
  have hpos : (0 : Real) < Real.log 15 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 15 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 15) ^ 2 ≤ (2.0326 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (2.0294 : Real) ^ 4 ≤ (0.75 * Real.log 15) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 15) ^ 6 ≤ (2.0326 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-1 / 2 : Real) ≤
      1 - (2.0326 : Real) ^ 2 / 2 + (2.0294 : Real) ^ 4 / 24 -
        (2.0326 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real rpow fifteenth inverse upper (`15 ^ (-0.395) ≤ 1/2`) from `2 ≤ 15 ^ 0.395`
(cleared `(15 ^ (1/3)) ^ 3 = 15 ≥ 8`, then `1/3 ≤ 0.395`). -/
theorem R05_rpow_fifteen_neg0395_le :
    (15 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hge : (2 : Real) ≤ (15 : Real) ^ (0.395 : Real) := by
    have hpow : ((2 : Real)) ^ (3 : Nat) ≤ ((((15 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((15 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (15 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 15)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 15 1
      rw [e]
      norm_num
    have hstep : (2 : Real) ≤ (15 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc (2 : Real) ≤ (15 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (15 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (15 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (15 : Real) ^ (-0.395 : Real) = (((15 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_cos_075log15_lower
#print axioms R05_rpow_fifteen_neg0395_le

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 fifteenth eta inverse
(`Re (15 ^ s)⁻¹ = 15 ^ (-0.395) * cos (0.75 * log 15)`). -/
theorem R05_inv_fifteen_cpow_re_eq :
    (((((15 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (15 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 15) := by
  have h15eq : ((((15 : Nat)) : Complex)) = (15 : Complex) := by norm_cast
  rw [h15eq]
  have hlog : Complex.log (15 : Complex) = (((Real.log 15 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 15)).symm
  have hlogre : (Complex.log (15 : Complex)).re = Real.log 15 := by rw [hlog]; rfl
  have hlogim : (Complex.log (15 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (15 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 15 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (15 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 15 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (15 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (15 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (15 : Complex) ≠ 0)]
  have hinv : ((15 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (15 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (15 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 15 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (15 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 15 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (15 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 15 * 0.395)) * Real.cos (-(Real.log 15 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 15 * (-0.75))) = Real.cos (0.75 * Real.log 15) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 15 * 0.395)) = (15 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 15 * 0.395) = Real.log 15 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 15)]
  rw [hinv, hre, hexp, hcos]

/-- R05 fifteenth eta term in closed form (`term 14 = ((15 ^ s)⁻¹)`, since `(-1)^14 = 1`). -/
theorem R05_eta_fifteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 14 =
      ((((15 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (14 + 1 : Nat) = 15 := rfl
  have hcast : ((((14 + 1 : Nat)) : Complex)) = ((((15 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (14 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_fifteen_cpow_re_eq
#print axioms R05_eta_fifteenth_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 fifteenth eta term (`-1/4 ≤ Re term15`, honest negative floor:
k = 14 even so the sign is `+1`, and `θ15 ≈ 2.03 past π/2` makes the cosine negative). -/
theorem R05_eta_fifteenth_Re_ge :
    (-1 / 4 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 14).re := by
  rw [R05_eta_fifteenth_eq, R05_inv_fifteen_cpow_re_eq]
  have hamp := R05_rpow_fifteen_neg0395_le
  have hcos := R05_cos_075log15_lower
  have hamp_pos : (0 : Real) < (15 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (15 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 15) + 1 / 2) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 2 - (15 : Real) ^ (-0.395 : Real)) * (1 / 2 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Fifteen-term split (`S15 = S14 + term 14`, non-pair slow-sum step). -/
theorem R05_S15_eq :
    (∑ k ∈ Finset.range 15, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 14, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 14 := by
  rw [show (15 : Nat) = 14 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 fifteen-term real part (`-1799/30000 ≤ Re S15`, from `5701/30000 - 1/4`;
honest dip: the even-k fifteenth term is genuinely negative). -/
theorem R05_S15_Re_ge :
    (-1799 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 15, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S15_eq, Complex.add_re]
  have hS14 := R05_S14_Re_ge
  have ht := R05_eta_fifteenth_Re_ge
  have hle : (-1799 / 30000 : Real) ≤ (5701 / 30000 : Real) + (-(1 / 4) : Real) := by
    norm_num
  linarith

/-- Sixteen-term split (`S16 = S15 + term 15`, non-pair slow-sum step). -/
theorem R05_S16_eq :
    (∑ k ∈ Finset.range 16, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 15, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 15 := by
  rw [show (16 : Nat) = 15 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 sixteen-term real part (`1201/30000 ≤ Re S16`, from `-1799/30000 + 1/10`). -/
theorem R05_S16_Re_ge :
    (1201 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 16, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S16_eq, Complex.add_re]
  have hS15 := R05_S15_Re_ge
  have ht := R05_eta_sixteenth_Re_ge
  have hle : (1201 / 30000 : Real) ≤ (-1799 / 30000 : Real) + (1 / 10 : Real) := by
    norm_num
  linarith

#print axioms R05_eta_fifteenth_Re_ge
#print axioms R05_S15_eq
#print axioms R05_S15_Re_ge
#print axioms R05_S16_eq
#print axioms R05_S16_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Fresh `log 17` lower bound (`2.8314 ≤ log 17`) via `log 16` and `log (16/17) ≤ -1/17`. -/
theorem R05_log_seventeen_ge :
    (2.8314 : Real) ≤ Real.log 17 := by
  have h16 := R05_log_sixteen_eq
  have hub : Real.log (16 / 17 : Real) ≤ (-1 / 17 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 16 / 17)
    have he : (16 / 17 : Real) - 1 = (-1 / 17 : Real) := by norm_num
    linarith
  have hinv : Real.log (17 / 16 : Real) = -Real.log (16 / 17 : Real) := by
    have heq : (17 / 16 : Real) = (16 / 17 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have hmeq : (16 : Real) * (17 / 16) = 17 := by norm_num
  have hlog17 : Real.log 17 = 4 * Real.log 2 + Real.log (17 / 16 : Real) := by
    have h := Real.log_mul (show (16 : Real) ≠ 0 by norm_num)
      (show (17 / 16 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h16] at h
    exact h
  have hfin : (2.8314 : Real) ≤ 4 * (0.693147 : Real) + (1 / 17 : Real) := by
    norm_num
  rw [hlog17, hinv]
  linarith

/-- Fresh `log 17` upper bound (`log 17 ≤ 2.8351`) via `log 16` and `log (17/16) ≤ 1/16`. -/
theorem R05_log_seventeen_le :
    Real.log 17 ≤ (2.8351 : Real) := by
  have h16 := R05_log_sixteen_eq
  have hub : Real.log (17 / 16 : Real) ≤ (1 / 16 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 17 / 16)
    have he : (17 / 16 : Real) - 1 = (1 / 16 : Real) := by norm_num
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have hmeq : (16 : Real) * (17 / 16) = 17 := by norm_num
  have hlog17 : Real.log 17 = 4 * Real.log 2 + Real.log (17 / 16 : Real) := by
    have h := Real.log_mul (show (16 : Real) ≠ 0 by norm_num)
      (show (17 / 16 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h16] at h
    exact h
  have hfin : 4 * (0.693148 : Real) + (1 / 16 : Real) ≤ (2.8351 : Real) := by
    norm_num
  rw [hlog17]
  linarith

#print axioms R05_log_seventeen_ge
#print axioms R05_log_seventeen_le

end Door3OffAxis

namespace Door3OffAxis

/-- Phase of the R05 seventeenth eta term (`0.75 * log 17` in `[2.1235, 2.1264]`)
from the fresh `log 17` bounds. -/
theorem R05_theta17_mem :
    (2.1235 : Real) ≤ 0.75 * Real.log 17 ∧ 0.75 * Real.log 17 ≤ (2.1264 : Real) := by
  have hge := R05_log_seventeen_ge
  have hle := R05_log_seventeen_le
  constructor <;> linarith

/-- Cosine lower at the seventeenth-term phase (`-11/20 ≤ cos (0.75 * log 17)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log17_lower :
    (-11 / 20 : Real) ≤ Real.cos (0.75 * Real.log 17) := by
  have hmem := R05_theta17_mem
  have hpos : (0 : Real) < Real.log 17 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 17 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.1235 : Real) ≤ 0.75 * Real.log 17 := hmem.1
  have hhi : 0.75 * Real.log 17 ≤ (2.1264 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 17) ^ 2 ≤ (2.1264 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (2.1235 : Real) ^ 4 ≤ (0.75 * Real.log 17) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 17) ^ 6 ≤ (2.1264 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-11 / 20 : Real) ≤
      1 - (2.1264 : Real) ^ 2 / 2 + (2.1235 : Real) ^ 4 / 24 -
        (2.1264 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Real rpow seventeenth inverse upper (`17 ^ (-0.395) ≤ 1/2`) from `2 ≤ 17 ^ 0.395`
(cleared `(17 ^ (1/3)) ^ 3 = 17 ≥ 8`, then `1/3 ≤ 0.395`). -/
theorem R05_rpow_seventeen_neg0395_le :
    (17 : Real) ^ (-0.395 : Real) ≤ (1 / 2 : Real) := by
  have hge : (2 : Real) ≤ (17 : Real) ^ (0.395 : Real) := by
    have hpow : ((2 : Real)) ^ (3 : Nat) ≤ ((((17 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((17 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (17 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 17)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 17 1
      rw [e]
      norm_num
    have hstep : (2 : Real) ≤ (17 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc (2 : Real) ≤ (17 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (17 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (17 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (17 : Real) ^ (-0.395 : Real) = (((17 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 2 : Real) = ((2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_theta17_mem
#print axioms R05_cos_075log17_lower
#print axioms R05_rpow_seventeen_neg0395_le

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 seventeenth eta inverse
(`Re (17 ^ s)⁻¹ = 17 ^ (-0.395) * cos (0.75 * log 17)`). -/
theorem R05_inv_seventeen_cpow_re_eq :
    (((((17 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (17 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 17) := by
  have h17eq : ((((17 : Nat)) : Complex)) = (17 : Complex) := by norm_cast
  rw [h17eq]
  have hlog : Complex.log (17 : Complex) = (((Real.log 17 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 17)).symm
  have hlogre : (Complex.log (17 : Complex)).re = Real.log 17 := by rw [hlog]; rfl
  have hlogim : (Complex.log (17 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (17 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 17 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (17 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 17 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (17 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (17 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (17 : Complex) ≠ 0)]
  have hinv : ((17 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (17 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (17 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 17 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (17 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 17 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (17 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 17 * 0.395)) * Real.cos (-(Real.log 17 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 17 * (-0.75))) = Real.cos (0.75 * Real.log 17) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 17 * 0.395)) = (17 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 17 * 0.395) = Real.log 17 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 17)]
  rw [hinv, hre, hexp, hcos]

/-- R05 seventeenth eta term in closed form (`term 16 = ((17 ^ s)⁻¹)`, since `(-1)^16 = 1`). -/
theorem R05_eta_seventeenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 16 =
      ((((17 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (16 + 1 : Nat) = 17 := rfl
  have hcast : ((((16 + 1 : Nat)) : Complex)) = ((((17 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (16 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_seventeen_cpow_re_eq
#print axioms R05_eta_seventeenth_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 seventeenth eta term (`-11/40 ≤ Re term17`, honest negative floor:
k = 16 even so the sign is `+1`, and `θ17 ≈ 2.12 past π/2` makes the cosine negative). -/
theorem R05_eta_seventeenth_Re_ge :
    (-11 / 40 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 16).re := by
  rw [R05_eta_seventeenth_eq, R05_inv_seventeen_cpow_re_eq]
  have hamp := R05_rpow_seventeen_neg0395_le
  have hcos := R05_cos_075log17_lower
  have hamp_pos : (0 : Real) < (17 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (17 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 17) + 11 / 20) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 2 - (17 : Real) ^ (-0.395 : Real)) * (11 / 20 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Seventeen-term split (`S17 = S16 + term 16`, non-pair slow-sum step). -/
theorem R05_S17_eq :
    (∑ k ∈ Finset.range 17, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 16, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 16 := by
  rw [show (17 : Nat) = 16 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 seventeen-term real part (`-7049/30000 ≤ Re S17`, from `1201/30000 - 11/40`;
honest dip: the even-k seventeenth term is genuinely negative). -/
theorem R05_S17_Re_ge :
    (-7049 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 17, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S17_eq, Complex.add_re]
  have hS16 := R05_S16_Re_ge
  have ht := R05_eta_seventeenth_Re_ge
  have hle : (-7049 / 30000 : Real) ≤ (1201 / 30000 : Real) + (-(11 / 40) : Real) := by
    norm_num
  linarith

#print axioms R05_eta_seventeenth_Re_ge
#print axioms R05_S17_eq
#print axioms R05_S17_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Log-18 split (`log 18 = 2 * log 3 + log 2`) via `18 = 9 * 2` and banked `log 9`. -/
theorem R05_log_eighteen_eq :
    Real.log 18 = 2 * Real.log 3 + Real.log 2 := by
  have h18 : (18 : Real) = 9 * 2 := by norm_num
  rw [h18, Real.log_mul (by norm_num) (by norm_num), R05_log_nine_eq]

/-- Phase of the R05 eighteenth eta term (`0.75 * log 18` in `[2.1677, 2.1678]`)
from the d9 `log 2` / `log 3` bounds via `R05_log_eighteen_eq`. -/
theorem R05_theta18_mem :
    (2.1677 : Real) ≤ 0.75 * Real.log 18 ∧ 0.75 * Real.log 18 ≤ (2.1678 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hx : 0.75 * Real.log 18 = 0.75 * (2 * Real.log 3 + Real.log 2) := by
    rw [R05_log_eighteen_eq]
  constructor <;> rw [hx] <;> linarith

#print axioms R05_log_eighteen_eq
#print axioms R05_theta18_mem

end Door3OffAxis

namespace Door3OffAxis

/-- Cosine upper at the eighteenth-term phase (`cos (0.75 * log 18) ≤ -2/5`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log18_upper :
    Real.cos (0.75 * Real.log 18) ≤ (-2 / 5 : Real) := by
  have hmem := R05_theta18_mem
  have hpos : (0 : Real) < Real.log 18 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 18 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.1677 : Real) ≤ 0.75 * Real.log 18 := hmem.1
  have hhi : 0.75 * Real.log 18 ≤ (2.1678 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (2.1677 : Real) ^ 2 ≤ (0.75 * Real.log 18) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 18) ^ 4 ≤ (2.1678 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (2.1677 : Real) ^ 2 / 2 + (2.1678 : Real) ^ 4 / 24 ≤
      (-2 / 5 : Real) := by
    norm_num
  linarith

/-- Rpow upper (`18 ^ 0.395 ≤ 4`) via cleared `(18 ^ (2/5)) ^ 5 = 324 ≤ 1024`. -/
theorem R05_eighteen_rpow_le : (18 : Real) ^ (0.395 : Real) ≤ (4 : Real) := by
  have hpow : ((((18 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((4 : Real)) ^ (5 : Nat) := by
    have e : ((((18 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (18 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 18)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 18 2
    rw [e]
    norm_num
  have hstep : (18 : Real) ^ ((2 / 5 : Real)) ≤ (4 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (18 : Real) ^ (0.395 : Real) ≤ (18 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (4 : Real) := hstep

/-- Real rpow eighteenth inverse lower (`1/4 ≤ 18 ^ (-0.395)`) from `18 ^ 0.395 ≤ 4`. -/
theorem R05_rpow_eighteen_neg0395_ge :
    (1 / 4 : Real) ≤ (18 : Real) ^ (-0.395 : Real) := by
  have hle := R05_eighteen_rpow_le
  have hpos : (0 : Real) < (18 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (18 : Real) ^ (-0.395 : Real) = (((18 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 4 : Real) = ((4 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_cos_075log18_upper
#print axioms R05_eighteen_rpow_le
#print axioms R05_rpow_eighteen_neg0395_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 eighteenth eta inverse
(`Re (18 ^ s)⁻¹ = 18 ^ (-0.395) * cos (0.75 * log 18)`). -/
theorem R05_inv_eighteen_cpow_re_eq :
    (((((18 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (18 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 18) := by
  have h18eq : ((((18 : Nat)) : Complex)) = (18 : Complex) := by norm_cast
  rw [h18eq]
  have hlog : Complex.log (18 : Complex) = (((Real.log 18 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 18)).symm
  have hlogre : (Complex.log (18 : Complex)).re = Real.log 18 := by rw [hlog]; rfl
  have hlogim : (Complex.log (18 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (18 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 18 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (18 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 18 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (18 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (18 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (18 : Complex) ≠ 0)]
  have hinv : ((18 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (18 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (18 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 18 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (18 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 18 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (18 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 18 * 0.395)) * Real.cos (-(Real.log 18 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 18 * (-0.75))) = Real.cos (0.75 * Real.log 18) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 18 * 0.395)) = (18 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 18 * 0.395) = Real.log 18 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 18)]
  rw [hinv, hre, hexp, hcos]

/-- R05 eighteenth eta term in closed form (`term 17 = -((18 ^ s)⁻¹)`, since `(-1)^17 = -1`). -/
theorem R05_eta_eighteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 17 =
      -((((18 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (17 + 1 : Nat) = 18 := rfl
  have hcast : ((((17 + 1 : Nat)) : Complex)) = ((((18 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (17 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

#print axioms R05_inv_eighteen_cpow_re_eq
#print axioms R05_eta_eighteenth_eq

end Door3OffAxis

namespace Door3OffAxis

/-- Real part of the R05 eighteenth eta term (`1/10 ≤ Re term18`,
from `(1/4) * (2/5)`: the `(-1)^17` sign flips the negative eighteenth cosine
into a positive contribution). -/
theorem R05_eta_eighteenth_Re_ge :
    (1 / 10 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 17).re := by
  rw [R05_eta_eighteenth_eq, Complex.neg_re, R05_inv_eighteen_cpow_re_eq]
  have hamp := R05_rpow_eighteen_neg0395_ge
  have hcos := R05_cos_075log18_upper
  have hamp_pos : (0 : Real) < (18 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (2 / 5 : Real) ≤ -(Real.cos (0.75 * Real.log 18)) := by
    linarith
  have hprod : (1 / 4 : Real) * (2 / 5 : Real) ≤
      (18 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 18))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (1 / 4 : Real) * (2 / 5 : Real) = (1 / 10 : Real) := by
    norm_num
  have hsplit : (18 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 18))) =
      -((18 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 18)) := by
    ring
  linarith

/-- Eighteen-term split (`S18 = S17 + term 17`, non-pair slow-sum step). -/
theorem R05_S18_eq :
    (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 17, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 17 := by
  rw [show (18 : Nat) = 17 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 eighteen-term real part (`-4049/30000 ≤ Re S18`, from `-7049/30000 + 1/10`). -/
theorem R05_S18_Re_ge :
    (-4049 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S18_eq, Complex.add_re]
  have hS17 := R05_S17_Re_ge
  have ht := R05_eta_eighteenth_Re_ge
  have hle : (-4049 / 30000 : Real) ≤ (-7049 / 30000 : Real) + (1 / 10 : Real) := by
    norm_num
  linarith

#print axioms R05_eta_eighteenth_Re_ge
#print axioms R05_S18_eq
#print axioms R05_S18_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Pair-5 floor (`-7/120 ≤ Re (term 10 + term 11)`, from `-1/8 + 1/15`). -/
theorem R05_pair5_Re_ge :
    (-7 / 120 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 10 + etaDirichletTerm R03R10PolyLower.sR05 11).re := by
  rw [Complex.add_re]
  have hE := R05_eta_eleventh_Re_ge
  have hO := R05_eta_twelfth_Re_ge
  have hle : (-7 / 120 : Real) ≤ (-1 / 8 : Real) + (1 / 15 : Real) := by norm_num
  linarith

/-- Pair-6 floor (`-7/60 ≤ Re (term 12 + term 13)`, from `-1/5 + 1/12`). -/
theorem R05_pair6_Re_ge :
    (-7 / 60 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 12 + etaDirichletTerm R03R10PolyLower.sR05 13).re := by
  rw [Complex.add_re]
  have hE := R05_eta_thirteenth_Re_ge
  have hO := R05_eta_fourteenth_Re_ge
  have hle : (-7 / 60 : Real) ≤ (-1 / 5 : Real) + (1 / 12 : Real) := by norm_num
  linarith

/-- Pair-7 floor (`-3/20 ≤ Re (term 14 + term 15)`, from `-1/4 + 1/10`). -/
theorem R05_pair7_Re_ge :
    (-3 / 20 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 14 + etaDirichletTerm R03R10PolyLower.sR05 15).re := by
  rw [Complex.add_re]
  have hE := R05_eta_fifteenth_Re_ge
  have hO := R05_eta_sixteenth_Re_ge
  have hle : (-3 / 20 : Real) ≤ (-1 / 4 : Real) + (1 / 10 : Real) := by norm_num
  linarith

/-- Pair-8 floor (`-7/40 ≤ Re (term 16 + term 17)`, from `-11/40 + 1/10`). -/
theorem R05_pair8_Re_ge :
    (-7 / 40 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 16 + etaDirichletTerm R03R10PolyLower.sR05 17).re := by
  rw [Complex.add_re]
  have hE := R05_eta_seventeenth_Re_ge
  have hO := R05_eta_eighteenth_Re_ge
  have hle : (-7 / 40 : Real) ≤ (-11 / 40 : Real) + (1 / 10 : Real) := by norm_num
  linarith

#print axioms R05_pair5_Re_ge
#print axioms R05_pair6_Re_ge
#print axioms R05_pair7_Re_ge
#print axioms R05_pair8_Re_ge

end Door3OffAxis

namespace Door3OffAxis

/-- Odd-k standalone credit over the banked block (k = 11, 13, 15, 17):
`1/15 + 1/12 + 1/10 + 1/10 = 7/20` (extends the banked `1/4` with the new term-18 credit). -/
theorem R05_odd_credit_11_17_eq :
    (1 / 15 : Real) + (1 / 12 : Real) + (1 / 10 : Real) + (1 / 10 : Real) =
      (7 / 20 : Real) := by
  norm_num

/-- Pair-block verdict over k = 10..17: the four pair floors sum to `-1/2`,
so contiguous honest folding alone cannot close the gap to `13/20`. -/
theorem R05_pairblock_5_8_sum_eq :
    (-7 / 120 : Real) + (-7 / 60 : Real) + (-3 / 20 : Real) + (-7 / 40 : Real) =
      (-1 / 2 : Real) := by
  norm_num

/-- Best R05 slow-sum lower bound: the S18 frontier `-4049/30000`
(contiguous folds through the pair-certified block; the highest contiguous
partial remains the S16 floor `1201/30000`). -/
theorem R05_slow_total_Re_ge :
    (-4049 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k).re :=
  R05_S18_Re_ge

/-- Exact residual from the S18 frontier to `13/20`: `23549/30000`. -/
theorem R05_slow_residual_eq :
    (13 / 20 : Real) - (-4049 / 30000 : Real) = (23549 / 30000 : Real) := by
  norm_num

/-- Exact residual from the best contiguous partial (S16) to `13/20`: `18299/30000`. -/
theorem R05_slow_residual_S16_eq :
    (13 / 20 : Real) - (1201 / 30000 : Real) = (18299 / 30000 : Real) := by
  norm_num

#print axioms R05_odd_credit_11_17_eq
#print axioms R05_pairblock_5_8_sum_eq
#print axioms R05_slow_total_Re_ge
#print axioms R05_slow_residual_eq
#print axioms R05_slow_residual_S16_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Fresh `log 19` lower bound (`2.9429 ≤ log 19`) via `log 18` and `log (18/19) ≤ -1/19`. -/
theorem R05_log_nineteen_ge :
    (2.9429 : Real) ≤ Real.log 19 := by
  have h18 := R05_log_eighteen_eq
  have hub : Real.log (18 / 19 : Real) ≤ (-1 / 19 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 18 / 19)
    have he : (18 / 19 : Real) - 1 = (-1 / 19 : Real) := by norm_num
    linarith
  have hinv : Real.log (19 / 18 : Real) = -Real.log (18 / 19 : Real) := by
    have heq : (19 / 18 : Real) = (18 / 19 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have h3lo : (1.098612 : Real) < Real.log 3 := by
    have h9 := Real.log_three_gt_d9
    linarith
  have hmeq : (18 : Real) * (19 / 18) = 19 := by norm_num
  have hlog19 : Real.log 19 =
      2 * Real.log 3 + Real.log 2 + Real.log (19 / 18 : Real) := by
    have h := Real.log_mul (show (18 : Real) ≠ 0 by norm_num)
      (show (19 / 18 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h18] at h
    exact h
  have hfin : (2.9429 : Real) ≤
      2 * (1.098612 : Real) + (0.693147 : Real) + (1 / 19 : Real) := by
    norm_num
  rw [hlog19, hinv]
  linarith

#print axioms R05_log_nineteen_ge

end Door3OffAxis


namespace Door3OffAxis

/-- Fresh `log 19` upper bound (`log 19 ≤ 2.9460`) via `log 18` and `log (19/18) ≤ 1/18`. -/
theorem R05_log_nineteen_le :
    Real.log 19 ≤ (2.9460 : Real) := by
  have h18 := R05_log_eighteen_eq
  have hub : Real.log (19 / 18 : Real) ≤ (1 / 18 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 19 / 18)
    have he : (19 / 18 : Real) - 1 = (1 / 18 : Real) := by norm_num
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have h3hi : Real.log 3 < (1.098613 : Real) := by
    have h9 := Real.log_three_lt_d9
    linarith
  have hmeq : (18 : Real) * (19 / 18) = 19 := by norm_num
  have hlog19 : Real.log 19 =
      2 * Real.log 3 + Real.log 2 + Real.log (19 / 18 : Real) := by
    have h := Real.log_mul (show (18 : Real) ≠ 0 by norm_num)
      (show (19 / 18 : Real) ≠ 0 by norm_num)
    rw [hmeq] at h
    rw [h18] at h
    exact h
  have hfin : 2 * (1.098613 : Real) + (0.693148 : Real) + (1 / 18 : Real) ≤
      (2.9460 : Real) := by
    norm_num
  rw [hlog19]
  linarith

#print axioms R05_log_nineteen_le

end Door3OffAxis

namespace Door3OffAxis

/-- Phase of the R05 nineteenth eta term (`0.75 * log 19` in `[2.2071, 2.2095]`)
from the fresh `log 19` bounds. -/
theorem R05_theta19_mem :
    (2.2071 : Real) ≤ 0.75 * Real.log 19 ∧ 0.75 * Real.log 19 ≤ (2.2095 : Real) := by
  have hge := R05_log_nineteen_ge
  have hle := R05_log_nineteen_le
  constructor <;> linarith

#print axioms R05_theta19_mem

end Door3OffAxis


namespace Door3OffAxis

/-- Cosine lower at the nineteenth-term phase (`-5/8 ≤ cos (0.75 * log 19)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log19_lower :
    (-5 / 8 : Real) ≤ Real.cos (0.75 * Real.log 19) := by
  have hmem := R05_theta19_mem
  have hpos : (0 : Real) < Real.log 19 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 19 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.2071 : Real) ≤ 0.75 * Real.log 19 := hmem.1
  have hhi : 0.75 * Real.log 19 ≤ (2.2095 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 19) ^ 2 ≤ (2.2095 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (2.2071 : Real) ^ 4 ≤ (0.75 * Real.log 19) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 19) ^ 6 ≤ (2.2095 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-5 / 8 : Real) ≤
      1 - (2.2095 : Real) ^ 2 / 2 + (2.2071 : Real) ^ 4 / 24 -
        (2.2095 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Tight base-rpow lower (`3 ≤ 19 ^ 0.395`) from cleared `19 ^ 3 = 6859 ≥ 6561 = 3 ^ 8`
with exponent `3/8 = 0.375 ≤ 0.395` (beats the coarse `2 ≤ 19 ^ 0.395`). -/
theorem R05_nineteen_rpow_ge : (3 : Real) ≤ (19 : Real) ^ (0.395 : Real) := by
  have hpow : ((3 : Real)) ^ (8 : Nat) ≤ ((((19 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) := by
    have e : ((((19 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) =
        (19 : Real) ^ (3 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 19)]
      rw [show (3 / 8 : Real) * ((((8 : Nat)) : Real)) = (3 : Real) by norm_num]
      rw [show (3 : Real) = ((((3 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 19 3
    rw [e]
    norm_num
  have hstep : (3 : Real) ≤ (19 : Real) ^ ((3 / 8 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
  calc (3 : Real) ≤ (19 : Real) ^ ((3 / 8 : Real)) := hstep
    _ ≤ (19 : Real) ^ (0.395 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Tight real rpow nineteenth inverse upper (`19 ^ (-0.395) ≤ 1/3`) from `3 ≤ 19 ^ 0.395`. -/
theorem R05_rpow_nineteen_neg0395_le :
    (19 : Real) ^ (-0.395 : Real) ≤ (1 / 3 : Real) := by
  have hge := R05_nineteen_rpow_ge
  have hpos : (0 : Real) < (19 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (19 : Real) ^ (-0.395 : Real) = (((19 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 3 : Real) = ((3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_cos_075log19_lower
#print axioms R05_nineteen_rpow_ge
#print axioms R05_rpow_nineteen_neg0395_le

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 nineteenth eta inverse
(`Re (19 ^ s)⁻¹ = 19 ^ (-0.395) * cos (0.75 * log 19)`). -/
theorem R05_inv_nineteen_cpow_re_eq :
    (((((19 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (19 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 19) := by
  have h19eq : ((((19 : Nat)) : Complex)) = (19 : Complex) := by norm_cast
  rw [h19eq]
  have hlog : Complex.log (19 : Complex) = (((Real.log 19 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 19)).symm
  have hlogre : (Complex.log (19 : Complex)).re = Real.log 19 := by rw [hlog]; rfl
  have hlogim : (Complex.log (19 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (19 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 19 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (19 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 19 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (19 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (19 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (19 : Complex) ≠ 0)]
  have hinv : ((19 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (19 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (19 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 19 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (19 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 19 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (19 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 19 * 0.395)) * Real.cos (-(Real.log 19 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 19 * (-0.75))) = Real.cos (0.75 * Real.log 19) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 19 * 0.395)) = (19 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 19 * 0.395) = Real.log 19 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 19)]
  rw [hinv, hre, hexp, hcos]

/-- R05 nineteenth eta term in closed form (`term 18 = ((19 ^ s)⁻¹)`, since `(-1)^18 = 1`). -/
theorem R05_eta_nineteenth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 18 =
      ((((19 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (18 + 1 : Nat) = 19 := rfl
  have hcast : ((((18 + 1 : Nat)) : Complex)) = ((((19 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (18 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_nineteen_cpow_re_eq
#print axioms R05_eta_nineteenth_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 nineteenth eta term (`-5/24 ≤ Re term19`, honest negative floor:
k = 18 even so the sign is `+1`, and the tight `1/3` amplitude times the `-5/8` cosine
gives `-5/24 ≈ -0.208`, beating the coarse `-11/40`). -/
theorem R05_eta_nineteenth_Re_ge :
    (-5 / 24 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 18).re := by
  rw [R05_eta_nineteenth_eq, R05_inv_nineteen_cpow_re_eq]
  have hamp := R05_rpow_nineteen_neg0395_le
  have hcos := R05_cos_075log19_lower
  have hamp_pos : (0 : Real) < (19 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (19 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 19) + 5 / 8) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 3 - (19 : Real) ^ (-0.395 : Real)) * (5 / 8 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Nineteen-term split (`S19 = S18 + term 18`, non-pair slow-sum step). -/
theorem R05_S19_eq :
    (∑ k ∈ Finset.range 19, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 18 := by
  rw [show (19 : Nat) = 18 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 nineteen-term real part (`-10299/30000 ≤ Re S19`, from `-4049/30000 - 5/24`;
honest dip: the even-k nineteenth term is genuinely negative). -/
theorem R05_S19_Re_ge :
    (-10299 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 19, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S19_eq, Complex.add_re]
  have hS18 := R05_S18_Re_ge
  have ht := R05_eta_nineteenth_Re_ge
  have hle : (-10299 / 30000 : Real) ≤ (-4049 / 30000 : Real) + (-(5 / 24) : Real) := by
    norm_num
  linarith

#print axioms R05_eta_nineteenth_Re_ge
#print axioms R05_S19_eq
#print axioms R05_S19_Re_ge

end Door3OffAxis


namespace Door3OffAxis

/-- Log-20 split (`log 20 = log 10 + log 2`) via `20 = 10 * 2` and banked `log 10`. -/
theorem R05_log_twenty_eq :
    Real.log 20 = Real.log 10 + Real.log 2 := by
  have h20 : (20 : Real) = 10 * 2 := by norm_num
  rw [h20, Real.log_mul (by norm_num) (by norm_num)]

/-- Phase of the R05 twentieth eta term (`0.75 * log 20` in `[2.2467, 2.2469]`)
from the d9 `log 2` / `log 5` bounds via `R05_log_twenty_eq` and `R05_log_ten_eq`. -/
theorem R05_theta20_mem :
    (2.2467 : Real) ≤ 0.75 * Real.log 20 ∧ 0.75 * Real.log 20 ≤ (2.2469 : Real) := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  have hx : 0.75 * Real.log 20 = 0.75 * ((Real.log 2 + Real.log 5) + Real.log 2) := by
    rw [R05_log_twenty_eq, R05_log_ten_eq]
  constructor <;> rw [hx] <;> linarith

#print axioms R05_log_twenty_eq
#print axioms R05_theta20_mem

end Door3OffAxis


namespace Door3OffAxis

/-- Cosine upper at the twentieth-term phase (`cos (0.75 * log 20) ≤ -2/5`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log20_upper :
    Real.cos (0.75 * Real.log 20) ≤ (-2 / 5 : Real) := by
  have hmem := R05_theta20_mem
  have hpos : (0 : Real) < Real.log 20 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 20 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.2467 : Real) ≤ 0.75 * Real.log 20 := hmem.1
  have hhi : 0.75 * Real.log 20 ≤ (2.2469 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (2.2467 : Real) ^ 2 ≤ (0.75 * Real.log 20) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 20) ^ 4 ≤ (2.2469 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (2.2467 : Real) ^ 2 / 2 + (2.2469 : Real) ^ 4 / 24 ≤
      (-2 / 5 : Real) := by
    norm_num
  linarith

/-- Rpow upper (`20 ^ 0.395 ≤ 4`) via cleared `(20 ^ (2/5)) ^ 5 = 400 ≤ 1024`. -/
theorem R05_twenty_rpow_le : (20 : Real) ^ (0.395 : Real) ≤ (4 : Real) := by
  have hpow : ((((20 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((4 : Real)) ^ (5 : Nat) := by
    have e : ((((20 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (20 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 20)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 20 2
    rw [e]
    norm_num
  have hstep : (20 : Real) ^ ((2 / 5 : Real)) ≤ (4 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (20 : Real) ^ (0.395 : Real) ≤ (20 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (4 : Real) := hstep

/-- Real rpow twentieth inverse lower (`1/4 ≤ 20 ^ (-0.395)`) from `20 ^ 0.395 ≤ 4`. -/
theorem R05_rpow_twenty_neg0395_ge :
    (1 / 4 : Real) ≤ (20 : Real) ^ (-0.395 : Real) := by
  have hle := R05_twenty_rpow_le
  have hpos : (0 : Real) < (20 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (20 : Real) ^ (-0.395 : Real) = (((20 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 4 : Real) = ((4 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_cos_075log20_upper
#print axioms R05_twenty_rpow_le
#print axioms R05_rpow_twenty_neg0395_ge

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 twentieth eta inverse
(`Re (20 ^ s)⁻¹ = 20 ^ (-0.395) * cos (0.75 * log 20)`). -/
theorem R05_inv_twenty_cpow_re_eq :
    (((((20 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (20 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 20) := by
  have h20eq : ((((20 : Nat)) : Complex)) = (20 : Complex) := by norm_cast
  rw [h20eq]
  have hlog : Complex.log (20 : Complex) = (((Real.log 20 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 20)).symm
  have hlogre : (Complex.log (20 : Complex)).re = Real.log 20 := by rw [hlog]; rfl
  have hlogim : (Complex.log (20 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (20 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 20 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (20 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 20 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (20 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (20 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (20 : Complex) ≠ 0)]
  have hinv : ((20 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (20 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (20 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 20 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (20 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 20 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (20 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 20 * 0.395)) * Real.cos (-(Real.log 20 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 20 * (-0.75))) = Real.cos (0.75 * Real.log 20) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 20 * 0.395)) = (20 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 20 * 0.395) = Real.log 20 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 20)]
  rw [hinv, hre, hexp, hcos]

/-- R05 twentieth eta term in closed form (`term 19 = -((20 ^ s)⁻¹)`, since `(-1)^19 = -1`). -/
theorem R05_eta_twentieth_eq :
    etaDirichletTerm R03R10PolyLower.sR05 19 =
      -((((20 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (19 + 1 : Nat) = 20 := rfl
  have hcast : ((((19 + 1 : Nat)) : Complex)) = ((((20 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (19 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

#print axioms R05_inv_twenty_cpow_re_eq
#print axioms R05_eta_twentieth_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 twentieth eta term (`1/10 ≤ Re term20`,
from `(1/4) * (2/5)`: the `(-1)^19` sign flips the negative twentieth cosine
into a positive contribution). -/
theorem R05_eta_twentieth_Re_ge :
    (1 / 10 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 19).re := by
  rw [R05_eta_twentieth_eq, Complex.neg_re, R05_inv_twenty_cpow_re_eq]
  have hamp := R05_rpow_twenty_neg0395_ge
  have hcos := R05_cos_075log20_upper
  have hamp_pos : (0 : Real) < (20 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (2 / 5 : Real) ≤ -(Real.cos (0.75 * Real.log 20)) := by
    linarith
  have hprod : (1 / 4 : Real) * (2 / 5 : Real) ≤
      (20 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 20))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (1 / 4 : Real) * (2 / 5 : Real) = (1 / 10 : Real) := by
    norm_num
  have hsplit : (20 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 20))) =
      -((20 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 20)) := by
    ring
  linarith

/-- Twenty-term split (`S20 = S19 + term 19`, non-pair slow-sum step). -/
theorem R05_S20_eq :
    (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 19, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 19 := by
  rw [show (20 : Nat) = 19 + 1 by norm_num, Finset.sum_range_succ]

/-- R05 twenty-term real part (`-7299/30000 ≤ Re S20`, from `-10299/30000 + 1/10`). -/
theorem R05_S20_Re_ge :
    (-7299 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S20_eq, Complex.add_re]
  have hS19 := R05_S19_Re_ge
  have ht := R05_eta_twentieth_Re_ge
  have hle : (-7299 / 30000 : Real) ≤ (-10299 / 30000 : Real) + (1 / 10 : Real) := by
    norm_num
  linarith

/-- Pair-9 floor (`-13/120 ≤ Re (term 19 + term 20)`, from `-5/24 + 1/10`:
the tight nineteenth amplitude makes this pair net better than pair-8). -/
theorem R05_pair9_Re_ge :
    (-13 / 120 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 18 + etaDirichletTerm R03R10PolyLower.sR05 19).re := by
  rw [Complex.add_re]
  have hE := R05_eta_nineteenth_Re_ge
  have hO := R05_eta_twentieth_Re_ge
  have hle : (-13 / 120 : Real) ≤ (-5 / 24 : Real) + (1 / 10 : Real) := by norm_num
  linarith

#print axioms R05_eta_twentieth_Re_ge
#print axioms R05_S20_eq
#print axioms R05_S20_Re_ge
#print axioms R05_pair9_Re_ge

end Door3OffAxis


namespace Door3OffAxis

/-- Best R05 slow-sum lower bound: the S20 frontier `-7299/30000`
(contiguous folds through pair-9; S20 = S19 + term 19). -/
theorem R05_slow_total20_Re_ge :
    (-7299 / 30000 : Real) ≤
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k).re :=
  R05_S20_Re_ge

/-- Exact residual from the S20 frontier to `13/20`: `26799/30000`
(`13/20 - (-7299/30000) = 26799/30000`). -/
theorem R05_slow_residual20_eq :
    (13 / 20 : Real) - (-7299 / 30000 : Real) = (26799 / 30000 : Real) := by
  norm_num

/-- Pair-block verdict over k = 10..19: the pair-5-8 block sums to `-1/2`
and pair-9 adds `-13/120`, for a five-pair total of `-73/120`. -/
theorem R05_pairblock_5_9_sum_eq :
    (-1 / 2 : Real) + (-13 / 120 : Real) = (-73 / 120 : Real) := by
  norm_num

#print axioms R05_slow_total20_Re_ge
#print axioms R05_slow_residual20_eq
#print axioms R05_pairblock_5_9_sum_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Tight eleventh inverse upper (`11 ^ (-0.395) ≤ 5/11`) from `11/5 ≤ 11 ^ 0.395`
(cleared `((11/5)) ^ 3 = 1331/125 ≤ 11`, then `1/3 ≤ 0.395`; beats `1/2`). -/
theorem R05_rpow_eleven_neg0395_le_tight :
    (11 : Real) ^ (-0.395 : Real) ≤ (5 / 11 : Real) := by
  have hge : ((11 / 5 : Real)) ≤ (11 : Real) ^ (0.395 : Real) := by
    have hpow : ((11 / 5 : Real)) ^ (3 : Nat) ≤
        ((((11 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((11 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (11 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 11)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 11 1
      rw [e]
      norm_num
    have hstep : ((11 / 5 : Real)) ≤ (11 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc ((11 / 5 : Real)) ≤ (11 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (11 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (11 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (11 : Real) ^ (-0.395 : Real) = (((11 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (5 / 11 : Real) = (((11 / 5 : Real)))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Tight thirteenth inverse upper (`13 ^ (-0.395) ≤ 3/7`) from `7/3 ≤ 13 ^ 0.395`
(cleared `(7/3) ^ 3 = 343/27 ≤ 13`, then `1/3 ≤ 0.395`; beats `1/2`). -/
theorem R05_rpow_thirteen_neg0395_le_tight :
    (13 : Real) ^ (-0.395 : Real) ≤ (3 / 7 : Real) := by
  have hge : ((7 / 3 : Real)) ≤ (13 : Real) ^ (0.395 : Real) := by
    have hpow : ((7 / 3 : Real)) ^ (3 : Nat) ≤
        ((((13 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((13 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (13 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 13)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 13 1
      rw [e]
      norm_num
    have hstep : ((7 / 3 : Real)) ≤ (13 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc ((7 / 3 : Real)) ≤ (13 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (13 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (13 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (13 : Real) ^ (-0.395 : Real) = (((13 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (3 / 7 : Real) = (((7 / 3 : Real)))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_rpow_eleven_neg0395_le_tight
#print axioms R05_rpow_thirteen_neg0395_le_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight fifteenth inverse upper (`15 ^ (-0.395) ≤ 5/12`) from `12/5 ≤ 15 ^ 0.395`
(cleared `(12/5) ^ 3 = 1728/125 ≤ 15`, then `1/3 ≤ 0.395`; beats `1/2`). -/
theorem R05_rpow_fifteen_neg0395_le_tight :
    (15 : Real) ^ (-0.395 : Real) ≤ (5 / 12 : Real) := by
  have hge : ((12 / 5 : Real)) ≤ (15 : Real) ^ (0.395 : Real) := by
    have hpow : ((12 / 5 : Real)) ^ (3 : Nat) ≤
        ((((15 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((15 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (15 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 15)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 15 1
      rw [e]
      norm_num
    have hstep : ((12 / 5 : Real)) ≤ (15 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc ((12 / 5 : Real)) ≤ (15 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (15 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (15 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (15 : Real) ^ (-0.395 : Real) = (((15 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (5 / 12 : Real) = (((12 / 5 : Real)))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Tight seventeenth inverse upper (`17 ^ (-0.395) ≤ 2/5`) from `5/2 ≤ 17 ^ 0.395`
(cleared `(5/2) ^ 3 = 125/8 ≤ 17`, then `1/3 ≤ 0.395`; beats `1/2`). -/
theorem R05_rpow_seventeen_neg0395_le_tight :
    (17 : Real) ^ (-0.395 : Real) ≤ (2 / 5 : Real) := by
  have hge : ((5 / 2 : Real)) ≤ (17 : Real) ^ (0.395 : Real) := by
    have hpow : ((5 / 2 : Real)) ^ (3 : Nat) ≤
        ((((17 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) := by
      have e : ((((17 : Real) ^ ((1 / 3 : Real)))) ^ (3 : Nat)) =
          (17 : Real) ^ (1 : Nat) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 17)]
        rw [show (1 / 3 : Real) * ((((3 : Nat)) : Real)) = (1 : Real) by norm_num]
        rw [show (1 : Real) = ((((1 : Nat)) : Real)) by norm_num]
        exact Real.rpow_natCast 17 1
      rw [e]
      norm_num
    have hstep : ((5 / 2 : Real)) ≤ (17 : Real) ^ ((1 / 3 : Real)) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
    calc ((5 / 2 : Real)) ≤ (17 : Real) ^ ((1 / 3 : Real)) := hstep
      _ ≤ (17 : Real) ^ (0.395 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hpos : (0 : Real) < (17 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (17 : Real) ^ (-0.395 : Real) = (((17 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (2 / 5 : Real) = (((5 / 2 : Real)))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_rpow_fifteen_neg0395_le_tight
#print axioms R05_rpow_seventeen_neg0395_le_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight eleventh eta floor (`-5/44 ≤ Re term11`): banked `-1/4` cosine
times the tight `5/11` amplitude (beats `-1/8`). -/
theorem R05_eta_eleventh_Re_ge_tight :
    (-5 / 44 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 10).re := by
  rw [R05_eta_eleventh_eq, R05_inv_eleven_cpow_re_eq]
  have hamp := R05_rpow_eleven_neg0395_le_tight
  have hcos := R05_cos_075log11_lower
  have hamp_pos : (0 : Real) < (11 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (11 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 11) + 1 / 4) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (5 / 11 - (11 : Real) ^ (-0.395 : Real)) * (1 / 4 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Tight thirteenth eta floor (`-6/35 ≤ Re term13`): banked `-2/5` cosine
times the tight `3/7` amplitude (beats `-1/5`). -/
theorem R05_eta_thirteenth_Re_ge_tight :
    (-6 / 35 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 12).re := by
  rw [R05_eta_thirteenth_eq, R05_inv_thirteen_cpow_re_eq]
  have hamp := R05_rpow_thirteen_neg0395_le_tight
  have hcos := R05_cos_075log13_lower
  have hamp_pos : (0 : Real) < (13 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (13 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 13) + 2 / 5) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (3 / 7 - (13 : Real) ^ (-0.395 : Real)) * (2 / 5 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

#print axioms R05_eta_eleventh_Re_ge_tight
#print axioms R05_eta_thirteenth_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight fifteenth eta floor (`-5/24 ≤ Re term15`): banked `-1/2` cosine
times the tight `5/12` amplitude (beats `-1/4`). -/
theorem R05_eta_fifteenth_Re_ge_tight :
    (-5 / 24 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 14).re := by
  rw [R05_eta_fifteenth_eq, R05_inv_fifteen_cpow_re_eq]
  have hamp := R05_rpow_fifteen_neg0395_le_tight
  have hcos := R05_cos_075log15_lower
  have hamp_pos : (0 : Real) < (15 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (15 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 15) + 1 / 2) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (5 / 12 - (15 : Real) ^ (-0.395 : Real)) * (1 / 2 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Tight seventeenth eta floor (`-11/50 ≤ Re term17`): banked `-11/20` cosine
times the tight `2/5` amplitude (beats `-11/40`). -/
theorem R05_eta_seventeenth_Re_ge_tight :
    (-11 / 50 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 16).re := by
  rw [R05_eta_seventeenth_eq, R05_inv_seventeen_cpow_re_eq]
  have hamp := R05_rpow_seventeen_neg0395_le_tight
  have hcos := R05_cos_075log17_lower
  have hamp_pos : (0 : Real) < (17 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (17 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 17) + 11 / 20) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (2 / 5 - (17 : Real) ^ (-0.395 : Real)) * (11 / 20 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

#print axioms R05_eta_fifteenth_Re_ge_tight
#print axioms R05_eta_seventeenth_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight pair-5 floor (`-31/660`, from `-5/44 + 1/15`; beats `-7/120`). -/
theorem R05_pair5_Re_ge_tight :
    (-31 / 660 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 10 + etaDirichletTerm R03R10PolyLower.sR05 11).re := by
  rw [Complex.add_re]
  have hE := R05_eta_eleventh_Re_ge_tight
  have hO := R05_eta_twelfth_Re_ge
  have hle : (-31 / 660 : Real) ≤ (-5 / 44 : Real) + (1 / 15 : Real) := by norm_num
  linarith

/-- Tight pair-6 floor (`-37/420`, from `-6/35 + 1/12`; beats `-7/60`). -/
theorem R05_pair6_Re_ge_tight :
    (-37 / 420 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 12 + etaDirichletTerm R03R10PolyLower.sR05 13).re := by
  rw [Complex.add_re]
  have hE := R05_eta_thirteenth_Re_ge_tight
  have hO := R05_eta_fourteenth_Re_ge
  have hle : (-37 / 420 : Real) ≤ (-6 / 35 : Real) + (1 / 12 : Real) := by norm_num
  linarith

/-- Tight pair-7 floor (`-13/120`, from `-5/24 + 1/10`; beats `-3/20`). -/
theorem R05_pair7_Re_ge_tight :
    (-13 / 120 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 14 + etaDirichletTerm R03R10PolyLower.sR05 15).re := by
  rw [Complex.add_re]
  have hE := R05_eta_fifteenth_Re_ge_tight
  have hO := R05_eta_sixteenth_Re_ge
  have hle : (-13 / 120 : Real) ≤ (-5 / 24 : Real) + (1 / 10 : Real) := by norm_num
  linarith

/-- Tight pair-8 floor (`-3/25`, from `-11/50 + 1/10`; beats `-7/40`). -/
theorem R05_pair8_Re_ge_tight :
    (-3 / 25 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 16 + etaDirichletTerm R03R10PolyLower.sR05 17).re := by
  rw [Complex.add_re]
  have hE := R05_eta_seventeenth_Re_ge_tight
  have hO := R05_eta_eighteenth_Re_ge
  have hle : (-3 / 25 : Real) ≤ (-11 / 50 : Real) + (1 / 10 : Real) := by norm_num
  linarith

/-- Tight pair-block sum over k = 10..17: `-16789/46200 ≈ -0.3634`
(beats the coarse `-1/2`). -/
theorem R05_pairblock_5_8_sum_eq_tight :
    (-31 / 660 : Real) + (-37 / 420 : Real) + (-13 / 120 : Real) + (-3 / 25 : Real) =
      (-16789 / 46200 : Real) := by
  norm_num

#print axioms R05_pair5_Re_ge_tight
#print axioms R05_pair6_Re_ge_tight
#print axioms R05_pair7_Re_ge_tight
#print axioms R05_pair8_Re_ge_tight
#print axioms R05_pairblock_5_8_sum_eq_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight eleven-term real part (`82961/330000 ≤ Re S11`, from `S10 - 5/44`). -/
theorem R05_S11_Re_ge_tight :
    (82961 / 330000 : Real) ≤
      (∑ k ∈ Finset.range 11, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S11_eq, Complex.add_re]
  have hS10 := R05_S10_Re_ge
  have ht := R05_eta_eleventh_Re_ge_tight
  have hle : (82961 / 330000 : Real) ≤ (10951 / 30000 : Real) + (-(5 / 44) : Real) := by
    norm_num
  linarith

/-- Tight twelve-term real part (`34987/110000 ≤ Re S12`, from `S11' + 1/15`). -/
theorem R05_S12_Re_ge_tight :
    (34987 / 110000 : Real) ≤
      (∑ k ∈ Finset.range 12, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S12_eq, Complex.add_re]
  have hS11 := R05_S11_Re_ge_tight
  have ht := R05_eta_twelfth_Re_ge
  have hle : (34987 / 110000 : Real) ≤ (82961 / 330000 : Real) + (1 / 15 : Real) := by
    norm_num
  linarith

/-- Tight thirteen-term real part (`112909/770000 ≤ Re S13`, from `S12' - 6/35`). -/
theorem R05_S13_Re_ge_tight :
    (112909 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 13, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S13_eq, Complex.add_re]
  have hS12 := R05_S12_Re_ge_tight
  have ht := R05_eta_thirteenth_Re_ge_tight
  have hle : (112909 / 770000 : Real) ≤ (34987 / 110000 : Real) + (-(6 / 35) : Real) := by
    norm_num
  linarith

/-- Tight fourteen-term real part (`531227/2310000 ≤ Re S14`, from `S13' + 1/12`). -/
theorem R05_S14_Re_ge_tight :
    (531227 / 2310000 : Real) ≤
      (∑ k ∈ Finset.range 14, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S14_eq, Complex.add_re]
  have hS13 := R05_S13_Re_ge_tight
  have ht := R05_eta_fourteenth_Re_ge
  have hle : (531227 / 2310000 : Real) ≤ (112909 / 770000 : Real) + (1 / 12 : Real) := by
    norm_num
  linarith

#print axioms R05_S11_Re_ge_tight
#print axioms R05_S12_Re_ge_tight
#print axioms R05_S13_Re_ge_tight
#print axioms R05_S14_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight fifteen-term real part (`16659/770000 ≤ Re S15`, from `S14' - 5/24`). -/
theorem R05_S15_Re_ge_tight :
    (16659 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 15, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S15_eq, Complex.add_re]
  have hS14 := R05_S14_Re_ge_tight
  have ht := R05_eta_fifteenth_Re_ge_tight
  have hle : (16659 / 770000 : Real) ≤ (531227 / 2310000 : Real) + (-(5 / 24) : Real) := by
    norm_num
  linarith

/-- Tight sixteen-term real part (`93659/770000 ≤ Re S16`, from `S15' + 1/10`). -/
theorem R05_S16_Re_ge_tight :
    (93659 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 16, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S16_eq, Complex.add_re]
  have hS15 := R05_S15_Re_ge_tight
  have ht := R05_eta_sixteenth_Re_ge
  have hle : (93659 / 770000 : Real) ≤ (16659 / 770000 : Real) + (1 / 10 : Real) := by
    norm_num
  linarith

/-- Tight seventeen-term real part (`-75741/770000 ≤ Re S17`, from `S16' - 11/50`). -/
theorem R05_S17_Re_ge_tight :
    (-75741 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 17, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S17_eq, Complex.add_re]
  have hS16 := R05_S16_Re_ge_tight
  have ht := R05_eta_seventeenth_Re_ge_tight
  have hle : (-75741 / 770000 : Real) ≤ (93659 / 770000 : Real) + (-(11 / 50) : Real) := by
    norm_num
  linarith

/-- Tight eighteen-term real part (`1259/770000 ≤ Re S18`, from `S17' + 1/10`). -/
theorem R05_S18_Re_ge_tight :
    (1259 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S18_eq, Complex.add_re]
  have hS17 := R05_S17_Re_ge_tight
  have ht := R05_eta_eighteenth_Re_ge
  have hle : (1259 / 770000 : Real) ≤ (-75741 / 770000 : Real) + (1 / 10 : Real) := by
    norm_num
  linarith

#print axioms R05_S15_Re_ge_tight
#print axioms R05_S16_Re_ge_tight
#print axioms R05_S17_Re_ge_tight
#print axioms R05_S18_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight R05 slow-sum lower bound: the S18 frontier `1259/770000 ≈ +0.00164`
(contiguous tight folds through the pair-certified block; frontier flips positive). -/
theorem R05_slow_total18_Re_ge_tight :
    (1259 / 770000 : Real) ≤
      (∑ k ∈ Finset.range 18, etaDirichletTerm R03R10PolyLower.sR05 k).re :=
  R05_S18_Re_ge_tight

/-- Exact tight residual from the S18 frontier to `13/20`: `499241/770000`. -/
theorem R05_slow_residual18_tight_eq :
    (13 / 20 : Real) - (1259 / 770000 : Real) = (499241 / 770000 : Real) := by
  norm_num

/-- Tight pair-block verdict over k = 10..19: the tight pair-5-8 block sums to
`-16789/46200` and pair-9 adds `-13/120`, for a five-pair total of `-10897/23100`. -/
theorem R05_pairblock_5_9_sum_eq_tight :
    (-16789 / 46200 : Real) + (-13 / 120 : Real) = (-10897 / 23100 : Real) := by
  norm_num

#print axioms R05_slow_total18_Re_ge_tight
#print axioms R05_slow_residual18_tight_eq
#print axioms R05_pairblock_5_9_sum_eq_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight base-rpow lower (`301/100 ≤ 19 ^ 0.395`) from cleared `(301/100) ^ 8 ≤ 19 ^ 3`
with exponent `3/8 = 0.375 ≤ 0.395` (beats the coarse `3 ≤ 19 ^ 0.395`). -/
theorem R05_nineteen_rpow_ge_tight : ((301 / 100 : Real)) ≤ (19 : Real) ^ (0.395 : Real) := by
  have hpow : (((301 / 100 : Real))) ^ (8 : Nat) ≤ ((((19 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) := by
    have e : ((((19 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) =
        (19 : Real) ^ (3 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 19)]
      rw [show (3 / 8 : Real) * ((((8 : Nat)) : Real)) = (3 : Real) by norm_num]
      rw [show (3 : Real) = ((((3 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 19 3
    rw [e]
    norm_num
  have hstep : (((301 / 100 : Real))) ≤ (19 : Real) ^ ((3 / 8 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
  calc (((301 / 100 : Real))) ≤ (19 : Real) ^ ((3 / 8 : Real)) := hstep
    _ ≤ (19 : Real) ^ (0.395 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Tight real rpow nineteenth inverse upper (`19 ^ (-0.395) ≤ 100/301`)
from `301/100 ≤ 19 ^ 0.395` (beats `1/3`). -/
theorem R05_rpow_nineteen_neg0395_le_tight :
    (19 : Real) ^ (-0.395 : Real) ≤ (100 / 301 : Real) := by
  have hge := R05_nineteen_rpow_ge_tight
  have hpos : (0 : Real) < (19 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (19 : Real) ^ (-0.395 : Real) = (((19 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (100 / 301 : Real) = (((301 / 100 : Real)))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_nineteen_rpow_ge_tight
#print axioms R05_rpow_nineteen_neg0395_le_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight rpow upper (`20 ^ 0.395 ≤ 10/3`) via cleared `(20 ^ (2/5)) ^ 5 = 400 ≤ 100000/243`
(beats the coarse `20 ^ 0.395 ≤ 4`). -/
theorem R05_twenty_rpow_le_tight : (20 : Real) ^ (0.395 : Real) ≤ (10 / 3 : Real) := by
  have hpow : ((((20 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((10 / 3 : Real)) ^ (5 : Nat) := by
    have e : ((((20 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (20 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 20)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 20 2
    rw [e]
    norm_num
  have hstep : (20 : Real) ^ ((2 / 5 : Real)) ≤ (10 / 3 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (20 : Real) ^ (0.395 : Real) ≤ (20 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (10 / 3 : Real) := hstep

/-- Tight real rpow twentieth inverse lower (`3/10 ≤ 20 ^ (-0.395)`)
from `20 ^ 0.395 ≤ 10/3` (beats `1/4`). -/
theorem R05_rpow_twenty_neg0395_ge_tight :
    (3 / 10 : Real) ≤ (20 : Real) ^ (-0.395 : Real) := by
  have hle := R05_twenty_rpow_le_tight
  have hpos : (0 : Real) < (20 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (20 : Real) ^ (-0.395 : Real) = (((20 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (3 / 10 : Real) = ((10 / 3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_twenty_rpow_le_tight
#print axioms R05_rpow_twenty_neg0395_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight nineteenth eta floor (`-125/602 ≤ Re term19`): banked `-5/8` cosine
times the tight `100/301` amplitude (beats `-5/24`). -/
theorem R05_eta_nineteenth_Re_ge_tight :
    (-125 / 602 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 18).re := by
  rw [R05_eta_nineteenth_eq, R05_inv_nineteen_cpow_re_eq]
  have hamp := R05_rpow_nineteen_neg0395_le_tight
  have hcos := R05_cos_075log19_lower
  have hamp_pos : (0 : Real) < (19 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (19 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 19) + 5 / 8) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (100 / 301 - (19 : Real) ^ (-0.395 : Real)) * (5 / 8 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Tight twentieth eta floor (`3/25 ≤ Re term20`): banked `-2/5` cosine
times the tight `3/10` amplitude (beats `1/10`). -/
theorem R05_eta_twentieth_Re_ge_tight :
    (3 / 25 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 19).re := by
  rw [R05_eta_twentieth_eq, Complex.neg_re, R05_inv_twenty_cpow_re_eq]
  have hamp := R05_rpow_twenty_neg0395_ge_tight
  have hcos := R05_cos_075log20_upper
  have hamp_pos : (0 : Real) < (20 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (2 / 5 : Real) ≤ -(Real.cos (0.75 * Real.log 20)) := by
    linarith
  have hprod : (3 / 10 : Real) * (2 / 5 : Real) ≤
      (20 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 20))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (3 / 10 : Real) * (2 / 5 : Real) = (3 / 25 : Real) := by
    norm_num
  have hsplit : (20 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 20))) =
      -((20 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 20)) := by
    ring
  linarith

#print axioms R05_eta_nineteenth_Re_ge_tight
#print axioms R05_eta_twentieth_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight nineteen-term real part (`-974409/4730000 ≤ Re S19`, from `S18' - 125/602`). -/
theorem R05_S19_Re_ge_tight :
    (-974409 / 4730000 : Real) ≤
      (∑ k ∈ Finset.range 19, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S19_eq, Complex.add_re]
  have hS18 := R05_S18_Re_ge_tight
  have ht := R05_eta_nineteenth_Re_ge_tight
  have hle : (-974409 / 4730000 : Real) ≤ (1259 / 770000 : Real) + (-(125 / 602) : Real) := by
    norm_num
  linarith

/-- Tight twenty-term real part (`-406809/4730000 ≤ Re S20`, from `S19' + 3/25`). -/
theorem R05_S20_Re_ge_tight :
    (-406809 / 4730000 : Real) ≤
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S20_eq, Complex.add_re]
  have hS19 := R05_S19_Re_ge_tight
  have ht := R05_eta_twentieth_Re_ge_tight
  have hle : (-406809 / 4730000 : Real) ≤ (-974409 / 4730000 : Real) + (3 / 25 : Real) := by
    norm_num
  linarith

/-- Tight R05 slow-sum lower bound: the S20 frontier `-406809/4730000 ≈ -0.08601`
(contiguous tight folds through pair-9; S20 = S19 + term 19). -/
theorem R05_slow_total20_Re_ge_tight :
    (-406809 / 4730000 : Real) ≤
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k).re :=
  R05_S20_Re_ge_tight

/-- Exact tight residual from the S20 frontier to `13/20`: `3481309/4730000`. -/
theorem R05_slow_residual20_tight_eq :
    (13 / 20 : Real) - (-406809 / 4730000 : Real) = (3481309 / 4730000 : Real) := by
  norm_num

#print axioms R05_S19_Re_ge_tight
#print axioms R05_S20_Re_ge_tight
#print axioms R05_slow_total20_Re_ge_tight
#print axioms R05_slow_residual20_tight_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Tight pair-9 floor (`-1319/15050 ≈ -0.08764`, from `-125/602 + 3/25`;
beats `-13/120`). -/
theorem R05_pair9_Re_ge_tight :
    (-1319 / 15050 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 18 + etaDirichletTerm R03R10PolyLower.sR05 19).re := by
  rw [Complex.add_re]
  have hE := R05_eta_nineteenth_Re_ge_tight
  have hO := R05_eta_twentieth_Re_ge_tight
  have hle : (-1319 / 15050 : Real) ≤ (-125 / 602 : Real) + (3 / 25 : Real) := by norm_num
  linarith

#print axioms R05_pair9_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Tight pair-block sum over k = 10..19: `-16789/46200 + -1319/15050 = -25601/56760`
(beats the coarse `-10897/23100`). -/
theorem R05_pairblock_5_9_sum_eq_tight2 :
    (-16789 / 46200 : Real) + (-1319 / 15050 : Real) = (-25601 / 56760 : Real) := by
  norm_num

#print axioms R05_pairblock_5_9_sum_eq_tight2

end Door3OffAxis


namespace Door3OffAxis

/-- Tight slow-assembly verdict: the best contiguous bound is the S20 frontier
`-406809/4730000 ≈ -0.08601` (tight folds through pair-9). -/
theorem R05_slow_tight_verdict_total :
    (-406809 / 4730000 : Real) ≤
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k).re :=
  R05_S20_Re_ge_tight

/-- Verdict residual from the best partial (S16 `93659/770000 ≈ 0.1216`) to `13/20`:
`406841/770000 ≈ 0.5284` still to cover. -/
theorem R05_slow_tight_verdict_S16_residual_eq :
    (13 / 20 : Real) - (93659 / 770000 : Real) = (406841 / 770000 : Real) := by
  norm_num

/-- Honest pair-route projection: the tight five-pair block (k = 10..19) totals
`-25601/56760 ≈ -0.45104`, so the pair route is net negative and the tail beyond
k = 20 must cover `62495/56760 ≈ 1.1011` to reach `13/20`. -/
theorem R05_pairblock_tight_verdict_gap_eq :
    (13 / 20 : Real) - (-25601 / 56760 : Real) = (62495 / 56760 : Real) := by
  norm_num

#print axioms R05_slow_tight_verdict_total
#print axioms R05_slow_tight_verdict_S16_residual_eq
#print axioms R05_pairblock_tight_verdict_gap_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Tight rpow upper (`21 ^ 0.395 ≤ 7/2`): amplitude half of pair-10 term 21. -/
theorem R05_twentyone_rpow_le_tight : (21 : Real) ^ (0.395 : Real) ≤ (7 / 2 : Real) := by
  have hpow : ((((21 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((7 / 2 : Real)) ^ (5 : Nat) := by
    have e : ((((21 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (21 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 21)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 21 2
    rw [e]
    norm_num
  have hstep : (21 : Real) ^ ((2 / 5 : Real)) ≤ (7 / 2 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (21 : Real) ^ (0.395 : Real) ≤ (21 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (7 / 2 : Real) := hstep
/-- Tight twenty-first inverse lower (`2/7 ≤ 21 ^ (-0.395)`) for pair-10 term 21. -/
theorem R05_rpow_twentyone_neg0395_ge_tight :
    (2 / 7 : Real) ≤ (21 : Real) ^ (-0.395 : Real) := by
  have hle := R05_twentyone_rpow_le_tight
  have hpos : (0 : Real) < (21 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (21 : Real) ^ (-0.395 : Real) = (((21 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (2 / 7 : Real) = ((7 / 2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle
/-- Tight rpow upper (`22 ^ 0.395 ≤ 7/2`): amplitude half of pair-10 term 22. -/
theorem R05_twentytwo_rpow_le_tight : (22 : Real) ^ (0.395 : Real) ≤ (7 / 2 : Real) := by
  have hpow : ((((22 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) ≤
      ((7 / 2 : Real)) ^ (5 : Nat) := by
    have e : ((((22 : Real) ^ ((2 / 5 : Real)))) ^ (5 : Nat)) =
        (22 : Real) ^ (2 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 22)]
      rw [show (2 / 5 : Real) * ((((5 : Nat)) : Real)) = (2 : Real) by norm_num]
      rw [show (2 : Real) = ((((2 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 22 2
    rw [e]
    norm_num
  have hstep : (22 : Real) ^ ((2 / 5 : Real)) ≤ (7 / 2 : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (22 : Real) ^ (0.395 : Real) ≤ (22 : Real) ^ ((2 / 5 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (7 / 2 : Real) := hstep
/-- Peak-to-frontier drop: S16 peak sits exactly one term-19 floor above S20. -/
theorem R05_S16_S20_drop_eq :
    (93659 / 770000 : Real) - (-406809 / 4730000 : Real) = (125 / 602 : Real) := by
  norm_num

#print axioms R05_twentyone_rpow_le_tight
#print axioms R05_rpow_twentyone_neg0395_ge_tight
#print axioms R05_twentytwo_rpow_le_tight
#print axioms R05_S16_S20_drop_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Fresh `log 21` bounds (`3.0433 ≤ log 21 ≤ 3.0458`) via `log 20`
(`R05_log_twenty_eq` + `R05_log_ten_eq`) and `log (21/20) ≤ 1/20`. -/
theorem R05_log_twentyone_mem :
    (3.0433 : Real) ≤ Real.log 21 ∧ Real.log 21 ≤ (3.0458 : Real) := by
  have h20 := R05_log_twenty_eq
  have h10 := R05_log_ten_eq
  have hub_lo : Real.log (20 / 21 : Real) ≤ (-1 / 21 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 20 / 21)
    have he : (20 / 21 : Real) - 1 = (-1 / 21 : Real) := by norm_num
    linarith
  have hinv : Real.log (21 / 20 : Real) = -Real.log (20 / 21 : Real) := by
    have heq : (21 / 20 : Real) = (20 / 21 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hub_hi : Real.log (21 / 20 : Real) ≤ (1 / 20 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 21 / 20)
    have he : (21 / 20 : Real) - 1 = (1 / 20 : Real) := by norm_num
    linarith
  have h2lo : (0.693147 : Real) < Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have h2hi : Real.log 2 < (0.693148 : Real) := by
    have h9 := Real.log_two_lt_d9
    linarith
  have h5lo : (1.609437 : Real) < Real.log 5 := by
    have h9 := Real.log_five_gt_d9
    linarith
  have h5hi : Real.log 5 < (1.609438 : Real) := by
    have h9 := Real.log_five_lt_d9
    linarith
  have hlog21 : Real.log 21 =
      2 * Real.log 2 + Real.log 5 + Real.log (21 / 20 : Real) := by
    have h := Real.log_mul (show (20 : Real) ≠ 0 by norm_num)
      (show (21 / 20 : Real) ≠ 0 by norm_num)
    have hmeq : (20 : Real) * (21 / 20) = 21 := by norm_num
    rw [hmeq] at h
    rw [h20, h10] at h
    linarith
  have hfin_lo : (3.0433 : Real) ≤
      2 * (0.693147 : Real) + (1.609437 : Real) + (1 / 21 : Real) := by
    norm_num
  have hfin_hi : 2 * (0.693148 : Real) + (1.609438 : Real) + (1 / 20 : Real) ≤
      (3.0458 : Real) := by
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hlog21, hinv]
    linarith
  · rw [hlog21]
    linarith

#print axioms R05_log_twentyone_mem

end Door3OffAxis


namespace Door3OffAxis

/-- Tight real rpow twenty-second inverse lower (`2/7 ≤ 22 ^ (-0.395)`)
from `22 ^ 0.395 ≤ 7/2` (completes the pair-10 amplitude halves). -/
theorem R05_rpow_twentytwo_neg0395_ge_tight :
    (2 / 7 : Real) ≤ (22 : Real) ^ (-0.395 : Real) := by
  have hle := R05_twentytwo_rpow_le_tight
  have hpos : (0 : Real) < (22 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (22 : Real) ^ (-0.395 : Real) = (((22 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (2 / 7 : Real) = ((7 / 2 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

#print axioms R05_rpow_twentytwo_neg0395_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Phase of the R05 twenty-first eta term (`0.75 * log 21` in `[2.2824, 2.2844]`)
from the banked `log 21` bounds. -/
theorem R05_theta21_mem :
    (2.2824 : Real) ≤ 0.75 * Real.log 21 ∧ 0.75 * Real.log 21 ≤ (2.2844 : Real) := by
  have h := R05_log_twentyone_mem
  constructor <;> linarith

/-- Fresh `log 22` bounds (`3.0866 ≤ log 22 ≤ 3.0958`) via `log 20`
(`R05_log_twenty_eq` + `R05_log_ten_eq`) and `log (22/20)` trapped by `x - 1`. -/
theorem R05_log_twentytwo_mem :
    (3.0866 : Real) ≤ Real.log 22 ∧ Real.log 22 ≤ (3.0958 : Real) := by
  have h20 := R05_log_twenty_eq
  have h10 := R05_log_ten_eq
  have hub_lo : Real.log (20 / 22 : Real) ≤ (-1 / 11 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 20 / 22)
    have he : (20 / 22 : Real) - 1 = (-1 / 11 : Real) := by norm_num
    linarith
  have hinv : Real.log (22 / 20 : Real) = -Real.log (20 / 22 : Real) := by
    have heq : (22 / 20 : Real) = (20 / 22 : Real)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hub_hi : Real.log (22 / 20 : Real) ≤ (1 / 10 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 22 / 20)
    have he : (22 / 20 : Real) - 1 = (1 / 10 : Real) := by norm_num
    linarith
  have hlog22 : Real.log 22 =
      2 * Real.log 2 + Real.log 5 + Real.log (22 / 20 : Real) := by
    have h := Real.log_mul (show (20 : Real) ≠ 0 by norm_num)
      (show (22 / 20 : Real) ≠ 0 by norm_num)
    have hmeq : (20 : Real) * (22 / 20) = 22 := by norm_num
    rw [hmeq] at h
    rw [h20, h10] at h
    linarith
  have hfin_lo : (3.0866 : Real) ≤
      2 * (0.693147 : Real) + (1.609437 : Real) + (1 / 11 : Real) := by
    norm_num
  have hfin_hi : 2 * (0.693148 : Real) + (1.609438 : Real) + (1 / 10 : Real) ≤
      (3.0958 : Real) := by
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hlog22, hinv]
    have h2lo : (0.693147 : Real) < Real.log 2 := by
      have h9 := Real.log_two_gt_d9
      linarith
    have h5lo : (1.609437 : Real) < Real.log 5 := by
      have h9 := Real.log_five_gt_d9
      linarith
    linarith
  · rw [hlog22]
    have h2hi : Real.log 2 < (0.693148 : Real) := by
      have h9 := Real.log_two_lt_d9
      linarith
    have h5hi : Real.log 5 < (1.609438 : Real) := by
      have h9 := Real.log_five_lt_d9
      linarith
    linarith

/-- Phase of the R05 twenty-second eta term (`0.75 * log 22` in `[2.3149, 2.3219]`)
from the fresh `log 22` bounds. -/
theorem R05_theta22_mem :
    (2.3149 : Real) ≤ 0.75 * Real.log 22 ∧ 0.75 * Real.log 22 ≤ (2.3219 : Real) := by
  have h := R05_log_twentytwo_mem
  constructor <;> linarith

#print axioms R05_theta21_mem
#print axioms R05_log_twentytwo_mem
#print axioms R05_theta22_mem

end Door3OffAxis


namespace Door3OffAxis

/-- Cosine lower at the twenty-first-term phase (`-3/4 ≤ cos (0.75 * log 21)`)
via `DZ3u_cos_sextic_lower` with per-monomial endpoints. -/
theorem R05_cos_075log21_lower :
    (-3 / 4 : Real) ≤ Real.cos (0.75 * Real.log 21) := by
  have hmem := R05_theta21_mem
  have hpos : (0 : Real) < Real.log 21 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 21 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.2824 : Real) ≤ 0.75 * Real.log 21 := hmem.1
  have hhi : 0.75 * Real.log 21 ≤ (2.2844 : Real) := hmem.2
  have hcos := DZ3u_cos_sextic_lower hnn
  have h2 : (0.75 * Real.log 21) ^ 2 ≤ (2.2844 : Real) ^ 2 :=
    pow_le_pow_left₀ hnn hhi 2
  have h4 : (2.2824 : Real) ^ 4 ≤ (0.75 * Real.log 21) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlo 4
  have h6 : (0.75 * Real.log 21) ^ 6 ≤ (2.2844 : Real) ^ 6 :=
    pow_le_pow_left₀ hnn hhi 6
  have hnum : (-3 / 4 : Real) ≤
      1 - (2.2844 : Real) ^ 2 / 2 + (2.2824 : Real) ^ 4 / 24 -
        (2.2844 : Real) ^ 6 / 720 := by
    norm_num
  linarith

/-- Cosine upper at the twenty-second-term phase (`cos (0.75 * log 22) ≤ -2/5`)
via `CG_cos_le_quartic` with per-monomial endpoints. -/
theorem R05_cos_075log22_upper :
    Real.cos (0.75 * Real.log 22) ≤ (-2 / 5 : Real) := by
  have hmem := R05_theta22_mem
  have hpos : (0 : Real) < Real.log 22 := Real.log_pos (by norm_num)
  have hnn : (0 : Real) ≤ 0.75 * Real.log 22 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hlo : (2.3149 : Real) ≤ 0.75 * Real.log 22 := hmem.1
  have hhi : 0.75 * Real.log 22 ≤ (2.3219 : Real) := hmem.2
  have hcos := CG_cos_le_quartic hnn
  have h2 : (2.3149 : Real) ^ 2 ≤ (0.75 * Real.log 22) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have h4 : (0.75 * Real.log 22) ^ 4 ≤ (2.3219 : Real) ^ 4 :=
    pow_le_pow_left₀ hnn hhi 4
  have hnum : (1 : Real) - (2.3149 : Real) ^ 2 / 2 + (2.3219 : Real) ^ 4 / 24 ≤
      (-2 / 5 : Real) := by
    norm_num
  linarith

#print axioms R05_cos_075log21_lower
#print axioms R05_cos_075log22_upper

end Door3OffAxis


namespace Door3OffAxis

/-- Base-rpow lower (`3 ≤ 21 ^ 0.395`) from cleared `21 ^ 3 = 9261 ≥ 6561 = 3 ^ 8`
with exponent `3/8 = 0.375 ≤ 0.395` (amplitude upper half of pair-10 term 21). -/
theorem R05_twentyone_rpow_ge : (3 : Real) ≤ (21 : Real) ^ (0.395 : Real) := by
  have hpow : ((3 : Real)) ^ (8 : Nat) ≤ ((((21 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) := by
    have e : ((((21 : Real) ^ ((3 / 8 : Real)))) ^ (8 : Nat)) =
        (21 : Real) ^ (3 : Nat) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 21)]
      rw [show (3 / 8 : Real) * ((((8 : Nat)) : Real)) = (3 : Real) by norm_num]
      rw [show (3 : Real) = ((((3 : Nat)) : Real)) by norm_num]
      exact Real.rpow_natCast 21 3
    rw [e]
    norm_num
  have hstep : (3 : Real) ≤ (21 : Real) ^ ((3 / 8 : Real)) :=
    le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hpow
  calc (3 : Real) ≤ (21 : Real) ^ ((3 / 8 : Real)) := hstep
    _ ≤ (21 : Real) ^ (0.395 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Real rpow twenty-first inverse upper (`21 ^ (-0.395) ≤ 1/3`) from `3 ≤ 21 ^ 0.395`. -/
theorem R05_rpow_twentyone_neg0395_le :
    (21 : Real) ^ (-0.395 : Real) ≤ (1 / 3 : Real) := by
  have hge := R05_twentyone_rpow_ge
  have hpos : (0 : Real) < (21 : Real) ^ (0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrw : (21 : Real) ^ (-0.395 : Real) = (((21 : Real) ^ (0.395 : Real)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hrw]
  rw [show (1 / 3 : Real) = ((3 : Real))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

#print axioms R05_twentyone_rpow_ge
#print axioms R05_rpow_twentyone_neg0395_le

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 twenty-first eta inverse
(`Re (21 ^ s)⁻¹ = 21 ^ (-0.395) * cos (0.75 * log 21)`). -/
theorem R05_inv_twentyone_cpow_re_eq :
    (((((21 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (21 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 21) := by
  have h21eq : ((((21 : Nat)) : Complex)) = (21 : Complex) := by norm_cast
  rw [h21eq]
  have hlog : Complex.log (21 : Complex) = (((Real.log 21 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 21)).symm
  have hlogre : (Complex.log (21 : Complex)).re = Real.log 21 := by rw [hlog]; rfl
  have hlogim : (Complex.log (21 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (21 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 21 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (21 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 21 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (21 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (21 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (21 : Complex) ≠ 0)]
  have hinv : ((21 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (21 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (21 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 21 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (21 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 21 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (21 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 21 * 0.395)) * Real.cos (-(Real.log 21 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 21 * (-0.75))) = Real.cos (0.75 * Real.log 21) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 21 * 0.395)) = (21 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 21 * 0.395) = Real.log 21 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 21)]
  rw [hinv, hre, hexp, hcos]

/-- R05 twenty-first eta term in closed form (`term 20 = ((21 ^ s)⁻¹)`, since `(-1)^20 = 1`). -/
theorem R05_eta_twentyfirst_eq :
    etaDirichletTerm R03R10PolyLower.sR05 20 =
      ((((21 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (20 + 1 : Nat) = 21 := rfl
  have hcast : ((((20 + 1 : Nat)) : Complex)) = ((((21 : Nat)) : Complex)) := by
    rw [e1]
  have hpos : (-1 : Complex) ^ (20 : Nat) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hpos, one_div]

#print axioms R05_inv_twentyone_cpow_re_eq
#print axioms R05_eta_twentyfirst_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Real part of the R05 twenty-second eta inverse
(`Re (22 ^ s)⁻¹ = 22 ^ (-0.395) * cos (0.75 * log 22)`). -/
theorem R05_inv_twentytwo_cpow_re_eq :
    (((((22 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹).re =
      (22 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 22) := by
  have h22eq : ((((22 : Nat)) : Complex)) = (22 : Complex) := by norm_cast
  rw [h22eq]
  have hlog : Complex.log (22 : Complex) = (((Real.log 22 : Real)) : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) ≤ 22)).symm
  have hlogre : (Complex.log (22 : Complex)).re = Real.log 22 := by rw [hlog]; rfl
  have hlogim : (Complex.log (22 : Complex)).im = 0 := by rw [hlog]; rfl
  have hsre : R03R10PolyLower.sR05.re = (0.395 : Real) := R03R10PolyLower.sR05_re
  have hsim : R03R10PolyLower.sR05.im = (-0.75 : Real) := R03R10PolyLower.sR05_im
  have hargre : (Complex.log (22 : Complex) * R03R10PolyLower.sR05).re =
      Real.log 22 * 0.395 := by
    rw [Complex.mul_re, hlogre, hlogim, hsre, hsim]
    ring
  have hargim : (Complex.log (22 : Complex) * R03R10PolyLower.sR05).im =
      Real.log 22 * (-0.75) := by
    rw [Complex.mul_im, hlogre, hlogim, hsre, hsim]
    ring
  have hcpow : (22 : Complex) ^ R03R10PolyLower.sR05 =
      Complex.exp (Complex.log (22 : Complex) * R03R10PolyLower.sR05) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (22 : Complex) ≠ 0)]
  have hinv : ((22 : Complex) ^ R03R10PolyLower.sR05)⁻¹ =
      Complex.exp (-(Complex.log (22 : Complex) * R03R10PolyLower.sR05)) := by
    rw [hcpow, <- Complex.exp_neg]
  have hnegre : (-(Complex.log (22 : Complex) * R03R10PolyLower.sR05)).re =
      -(Real.log 22 * 0.395) := by
    rw [Complex.neg_re, hargre]
  have hnegim : (-(Complex.log (22 : Complex) * R03R10PolyLower.sR05)).im =
      -(Real.log 22 * (-0.75)) := by
    rw [Complex.neg_im, hargim]
  have hre : (Complex.exp (-(Complex.log (22 : Complex) * R03R10PolyLower.sR05))).re =
      Real.exp (-(Real.log 22 * 0.395)) * Real.cos (-(Real.log 22 * (-0.75))) := by
    rw [Complex.exp_re, hnegre, hnegim]
  have hcos : Real.cos (-(Real.log 22 * (-0.75))) = Real.cos (0.75 * Real.log 22) := by
    congr 1
    ring
  have hexp : Real.exp (-(Real.log 22 * 0.395)) = (22 : Real) ^ (-0.395 : Real) := by
    have heq : -(Real.log 22 * 0.395) = Real.log 22 * (-0.395 : Real) := by
      ring
    rw [heq]
    rw [<- Real.rpow_def_of_pos (by norm_num : (0 : Real) < 22)]
  rw [hinv, hre, hexp, hcos]

/-- R05 twenty-second eta term in closed form (`term 21 = -((22 ^ s)⁻¹)`, since `(-1)^21 = -1`). -/
theorem R05_eta_twentysecond_eq :
    etaDirichletTerm R03R10PolyLower.sR05 21 =
      -((((22 : Nat)) : Complex) ^ R03R10PolyLower.sR05)⁻¹ := by
  have e1 : (21 + 1 : Nat) = 22 := rfl
  have hcast : ((((21 + 1 : Nat)) : Complex)) = ((((22 : Nat)) : Complex)) := by
    rw [e1]
  have hneg : (-1 : Complex) ^ (21 : Nat) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

#print axioms R05_inv_twentytwo_cpow_re_eq
#print axioms R05_eta_twentysecond_eq

end Door3OffAxis


namespace Door3OffAxis

/-- Tight twenty-first eta floor (`-1/4 ≤ Re term21`): banked `-3/4` cosine
times the tight `1/3` amplitude (beats `-5/24`). -/
theorem R05_eta_twentyfirst_Re_ge_tight :
    (-1 / 4 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 20).re := by
  rw [R05_eta_twentyfirst_eq, R05_inv_twentyone_cpow_re_eq]
  have hamp := R05_rpow_twentyone_neg0395_le
  have hcos := R05_cos_075log21_lower
  have hamp_pos : (0 : Real) < (21 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have g1 : (0 : Real) ≤ (21 : Real) ^ (-0.395 : Real) *
      (Real.cos (0.75 * Real.log 21) + 3 / 4) := by
    apply mul_nonneg hamp_pos.le
    linarith
  have g2 : (0 : Real) ≤ (1 / 3 - (21 : Real) ^ (-0.395 : Real)) * (3 / 4 : Real) := by
    apply mul_nonneg
    · linarith
    · norm_num
  linarith

/-- Tight twenty-second eta floor (`4/35 ≤ Re term22`): banked `-2/5` cosine
times the tight `2/7` amplitude with the `(-1)^21` sign flip (beats `1/10`). -/
theorem R05_eta_twentysecond_Re_ge_tight :
    (4 / 35 : Real) ≤ (etaDirichletTerm R03R10PolyLower.sR05 21).re := by
  rw [R05_eta_twentysecond_eq, Complex.neg_re, R05_inv_twentytwo_cpow_re_eq]
  have hamp := R05_rpow_twentytwo_neg0395_ge_tight
  have hcos := R05_cos_075log22_upper
  have hamp_pos : (0 : Real) < (22 : Real) ^ (-0.395 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnc : (2 / 5 : Real) ≤ -(Real.cos (0.75 * Real.log 22)) := by
    linarith
  have hprod : (2 / 7 : Real) * (2 / 5 : Real) ≤
      (22 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 22))) :=
    mul_le_mul hamp hnc (by norm_num) hamp_pos.le
  have heq : (2 / 7 : Real) * (2 / 5 : Real) = (4 / 35 : Real) := by
    norm_num
  have hsplit : (22 : Real) ^ (-0.395 : Real) * (-(Real.cos (0.75 * Real.log 22))) =
      -((22 : Real) ^ (-0.395 : Real) * Real.cos (0.75 * Real.log 22)) := by
    ring
  linarith

/-- Tight pair-10 floor (`-19/140`, from `-1/4 + 4/35`; beats `-13/120`). -/
theorem R05_pair10_Re_ge_tight :
    (-19 / 140 : Real) ≤
      (etaDirichletTerm R03R10PolyLower.sR05 20 + etaDirichletTerm R03R10PolyLower.sR05 21).re := by
  rw [Complex.add_re]
  have hE := R05_eta_twentyfirst_Re_ge_tight
  have hO := R05_eta_twentysecond_Re_ge_tight
  have hle : (-19 / 140 : Real) ≤ (-1 / 4 : Real) + (4 / 35 : Real) := by norm_num
  linarith

#print axioms R05_eta_twentyfirst_Re_ge_tight
#print axioms R05_eta_twentysecond_Re_ge_tight
#print axioms R05_pair10_Re_ge_tight

end Door3OffAxis


namespace Door3OffAxis

/-- Twenty-one-term split (`S21 = S20 + term 20`, non-pair slow-sum step). -/
theorem R05_S21_eq :
    (∑ k ∈ Finset.range 21, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 20, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 20 := by
  rw [show (21 : Nat) = 20 + 1 by norm_num, Finset.sum_range_succ]

/-- Tight twenty-one-term real part (`-1589309/4730000 ≤ Re S21`, from `S20' - 1/4`). -/
theorem R05_S21_Re_ge_tight :
    (-1589309 / 4730000 : Real) ≤
      (∑ k ∈ Finset.range 21, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S21_eq, Complex.add_re]
  have hS20 := R05_S20_Re_ge_tight
  have ht := R05_eta_twentyfirst_Re_ge_tight
  have hle : (-1589309 / 4730000 : Real) ≤ (-406809 / 4730000 : Real) + (-(1 / 4) : Real) := by
    norm_num
  linarith

/-- Twenty-two-term split (`S22 = S21 + term 21`, non-pair slow-sum step). -/
theorem R05_S22_eq :
    (∑ k ∈ Finset.range 22, etaDirichletTerm R03R10PolyLower.sR05 k) =
      (∑ k ∈ Finset.range 21, etaDirichletTerm R03R10PolyLower.sR05 k) +
        etaDirichletTerm R03R10PolyLower.sR05 21 := by
  rw [show (22 : Nat) = 21 + 1 by norm_num, Finset.sum_range_succ]

/-- Tight twenty-two-term real part (`-7341163/33110000 ≤ Re S22`, from `S21' + 4/35`). -/
theorem R05_S22_Re_ge_tight :
    (-7341163 / 33110000 : Real) ≤
      (∑ k ∈ Finset.range 22, etaDirichletTerm R03R10PolyLower.sR05 k).re := by
  rw [R05_S22_eq, Complex.add_re]
  have hS21 := R05_S21_Re_ge_tight
  have ht := R05_eta_twentysecond_Re_ge_tight
  have hle : (-7341163 / 33110000 : Real) ≤ (-1589309 / 4730000 : Real) + (4 / 35 : Real) := by
    norm_num
  linarith

#print axioms R05_S21_eq
#print axioms R05_S21_Re_ge_tight
#print axioms R05_S22_eq
#print axioms R05_S22_Re_ge_tight

end Door3OffAxis

namespace Door3OffAxis
open scoped BigOperators

/-- CutR10 slow-cert point: closed term identical to `Door3ZetaCutoff.sCut` (`1 / 2 + 10 * I`). -/
def sCutOA : ℂ := (1 / 2 : ℂ) + 10 * Complex.I

theorem sCutOA_re : sCutOA.re = (1 / 2 : ℝ) := by simp [sCutOA]
theorem sCutOA_im : sCutOA.im = (10 : ℝ) := by simp [sCutOA]

theorem sCutOA_norm_le : ‖sCutOA‖ ≤ (12 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im sCutOA
  have hre : |sCutOA.re| = (1 / 2 : ℝ) := by rw [sCutOA_re]; norm_num
  have him : |sCutOA.im| = (10 : ℝ) := by rw [sCutOA_im]; norm_num
  rw [hre, him] at h
  linarith

theorem sCutOA_term1_norm_le : ‖etaDirichletTerm sCutOA 1‖ ≤ (5 / 7 : ℝ) := by
  have hterm1_eq : etaDirichletTerm sCutOA 1 = -1 / ((((2 : ℕ)) : ℂ) ^ sCutOA) := by simp only [etaDirichletTerm]; norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = (((2 : ℝ) : ℂ)) := by norm_num
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ sCutOA)‖ = (2 : ℝ) ^ sCutOA.re := by rw [h2cast]; exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hroot : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have hpow : ((7 / 5 : ℝ) ^ (2 : ℕ)) ≤ (2 : ℝ) := by norm_num
    have hpow' : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) = 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← hpow'] at hpow
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm, sCutOA_re]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
  have hmul := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 5 / 7 by norm_num)
  have heq : (5 / 7 : ℝ) * (7 / 5 : ℝ) = 1 := by norm_num
  rw [heq] at hmul
  linarith

theorem sCutOA_slow : (2 / 7 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA k‖ := by
  have h0 : etaDirichletTerm sCutOA 0 = 1 := by simp only [etaDirichletTerm]; simp
  have hS2 : (∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA k) = 1 + etaDirichletTerm sCutOA 1 := by rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  have ht := sCutOA_term1_norm_le
  rw [hS2]
  have hrev := norm_sub_norm_le (1 : ℂ) (-(etaDirichletTerm sCutOA 1))
  rw [norm_one, norm_neg, sub_neg_eq_add] at hrev
  linarith

theorem sCutOA_rtail : ‖(∑' m, etaPairTerm sCutOA m) - (∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA k)‖ ≤ (24 : ℝ) := by
  have hspos : 0 < sCutOA.re := by rw [sCutOA_re]; norm_num
  have htail := zetaCell_even_remainder_le hspos sCutOA_norm_le (show (0 : ℝ) ≤ 12 by norm_num) 1 (by norm_num)
  have hone : ((((1 : ℕ)) : ℝ) ^ (-sCutOA.re)) = 1 := by rw [Nat.cast_one, Real.one_rpow]
  rw [hone] at htail
  have hdiv : (12 : ℝ) * (1 / sCutOA.re) ≤ 24 := by rw [sCutOA_re]; norm_num
  exact le_trans htail hdiv

/-- Certificate triple in the exact shape `cutR10_zetaRemainder_of_certificate_one` consumes, minus `hEnough` (see shortfall below). -/
theorem sCutOA_certTriple : ∃ (N : ℕ) (S : ℂ), S = ∑ k ∈ Finset.range N, etaDirichletTerm sCutOA k ∧ (2 / 7 : ℝ) ≤ ‖S‖ ∧ ‖(∑' m, etaPairTerm sCutOA m) - S‖ ≤ (24 : ℝ) := ⟨2, _, rfl, sCutOA_slow, sCutOA_rtail⟩

theorem sCutOA_hEnough_shortfall : ((7 / 5 : ℝ) + 24) - 2 / 7 = (879 / 35 : ℝ) := by norm_num

#print axioms sCutOA_slow
#print axioms sCutOA_rtail
#print axioms sCutOA_certTriple
end Door3OffAxis

namespace Door3OffAxis
open scoped BigOperators

/-- Moved cutoff point `1 / 2 + 11 * I` (premise (a)). Temp mpmath scan (50-digit):
`|η(1/2+11i)| ≈ 2.304502` vs `|η(1/2+10i)| ≈ 1.337526`; margin over `7/5`: `+0.90` vs `-0.06`. -/
def sCutOA11 : ℂ := (1 / 2 : ℂ) + 11 * Complex.I
theorem sCutOA11_re : sCutOA11.re = (1 / 2 : ℝ) := by simp [sCutOA11]
theorem sCutOA11_im : sCutOA11.im = (11 : ℝ) := by simp [sCutOA11]

theorem sCutOA11_norm_le : ‖sCutOA11‖ ≤ (12 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im sCutOA11
  have hre : |sCutOA11.re| = (1 / 2 : ℝ) := by rw [sCutOA11_re]; norm_num
  have him : |sCutOA11.im| = (11 : ℝ) := by rw [sCutOA11_im]; norm_num
  rw [hre, him] at h
  linarith

theorem sCutOA11_term1_norm_le : ‖etaDirichletTerm sCutOA11 1‖ ≤ (5 / 7 : ℝ) := by
  have hterm1_eq : etaDirichletTerm sCutOA11 1 = -1 / ((((2 : ℕ)) : ℂ) ^ sCutOA11) := by simp only [etaDirichletTerm]; norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = (((2 : ℝ) : ℂ)) := by norm_num
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ sCutOA11)‖ = (2 : ℝ) ^ sCutOA11.re := by rw [h2cast]; exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hroot : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have hpow : ((7 / 5 : ℝ) ^ (2 : ℕ)) ≤ (2 : ℝ) := by norm_num
    have hpow' : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) = 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← hpow'] at hpow
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm, sCutOA11_re]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
  have hmul := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 5 / 7 by norm_num)
  have heq : (5 / 7 : ℝ) * (7 / 5 : ℝ) = 1 := by norm_num
  rw [heq] at hmul
  linarith

theorem sCutOA11_slow : (2 / 7 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA11 k‖ := by
  have h0 : etaDirichletTerm sCutOA11 0 = 1 := by simp only [etaDirichletTerm]; simp
  have hS2 : (∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA11 k) = 1 + etaDirichletTerm sCutOA11 1 := by rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  have ht := sCutOA11_term1_norm_le
  rw [hS2]
  have hrev := norm_sub_norm_le (1 : ℂ) (-(etaDirichletTerm sCutOA11 1))
  rw [norm_one, norm_neg, sub_neg_eq_add] at hrev
  linarith

theorem sCutOA11_rtail : ‖(∑' m, etaPairTerm sCutOA11 m) - (∑ k ∈ Finset.range 2, etaDirichletTerm sCutOA11 k)‖ ≤ (24 : ℝ) := by
  have hspos : 0 < sCutOA11.re := by rw [sCutOA11_re]; norm_num
  have htail := zetaCell_even_remainder_le hspos sCutOA11_norm_le (show (0 : ℝ) ≤ 12 by norm_num) 1 (by norm_num)
  have hone : ((((1 : ℕ)) : ℝ) ^ (-sCutOA11.re)) = 1 := by rw [Nat.cast_one, Real.one_rpow]
  rw [hone] at htail
  have hdiv : (12 : ℝ) * (1 / sCutOA11.re) ≤ 24 := by rw [sCutOA11_re]; norm_num
  exact le_trans htail hdiv
/-- Triple at `t = 11` in the shape `cutR10_zetaRemainder_of_certificate_one` consumes, minus `hEnough`. -/
theorem sCutOA11_certTriple : ∃ (N : ℕ) (S : ℂ), S = ∑ k ∈ Finset.range N, etaDirichletTerm sCutOA11 k ∧ (2 / 7 : ℝ) ≤ ‖S‖ ∧ ‖(∑' m, etaPairTerm sCutOA11 m) - S‖ ≤ (24 : ℝ) := ⟨2, _, rfl, sCutOA11_slow, sCutOA11_rtail⟩
theorem sCutOA11_hEnough_shortfall : ((7 / 5 : ℝ) + 24) - 2 / 7 = (879 / 35 : ℝ) := by norm_num
/-- Sufficient improved-cert targets at `t = 11` (consistent with `|η| ≈ 2.30`): `M = 2048` gives `rtail' ≈ 0.53 ≤ 7/10`; `slow' ≥ 21/10` needs an `N`-term partial-sum bound (next-agent task). -/
theorem sCutOA11_targets (slow' rtail' : ℝ) (hs : (21 / 10 : ℝ) ≤ slow') (hr : rtail' ≤ (7 / 10 : ℝ)) :
    (7 / 5 : ℝ) + rtail' ≤ slow' := by linarith

#print axioms sCutOA11_certTriple
#print axioms sCutOA11_targets
end Door3OffAxis
