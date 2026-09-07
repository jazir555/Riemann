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


#print axioms R02_pi_lower_tight
#print axioms R02_center_certificate_of_zeta_ge_one
#print axioms R02_zero_free_certificate_of_zeta_ge_one

end Door3OffAxis
