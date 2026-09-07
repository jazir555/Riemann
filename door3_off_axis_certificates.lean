import interval_arith

open Complex Real
noncomputable section

namespace Door3OffAxis

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


#print axioms R02_pi_lower_tight
#print axioms R02_center_certificate_of_zeta_ge_one
#print axioms R02_zero_free_certificate_of_zeta_ge_one

end Door3OffAxis
