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

#print axioms R02_pi_lower_tight
#print axioms R02_center_certificate_of_zeta_ge_one
#print axioms R02_zero_free_certificate_of_zeta_ge_one

end Door3OffAxis
