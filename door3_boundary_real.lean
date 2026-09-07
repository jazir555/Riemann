import riemann_hypothesis
import door3_tail_eta_upper

/-- Unconditional real-axis zeta nonvanishing in the open critical interval.
The proof is supplied by the positive paired Dirichlet-eta series, rather than
by the RH axiom-bearing interface in `riemann_hypothesis.lean`. -/
theorem zetaRealNonzeroInCritical_proved : ZetaRealNonzeroInCritical := by
  intro t ht0 ht1
  exact Door3TailEtaUpper.zeta_real_nonzero_critical ht0 ht1

theorem zetaRealNonzeroPositive_proved {t : ℝ} (ht : 0 < t) :
    riemannZeta (t : ℂ) ≠ 0 :=
  Door3TailEtaUpper.zeta_real_nonzero_positive ht

theorem classicalXiPrefactor_ne_zero_on_real_critical_proved
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    classicalXiPrefactor (t : ℂ) ≠ 0 := by
  exact classical_prefactor_nonzero_instrip
    classical_gamma_nonzero_instrip _ (by simpa using ht0) (by simpa using ht1)

theorem classicalXi_ne_zero_on_real_critical_proved
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    classicalXi (t : ℂ) ≠ 0 := by
  intro hzero
  have hmul : classicalXiPrefactor (t : ℂ) * zeta (t : ℂ) = 0 := by
    simpa [classicalXi, XiFromPrefactor] using hzero
  have hpref := classicalXiPrefactor_ne_zero_on_real_critical_proved t ht0 ht1
  have hzeta : zeta (t : ℂ) = 0 := (mul_eq_zero.mp hmul).resolve_left hpref
  exact zetaRealNonzeroInCritical_proved t ht0 ht1 hzeta

/-- The corresponding shifted xi nonvanishing on the imaginary axis, with the
real-zeta premise discharged by the eta-pair theorem. -/
theorem xiShifted_ne_zero_on_imaginary_axis_proved
    (y : ℝ) (hyne : y ≠ 0)
    (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    xiShifted (Complex.I * (y : ℂ)) ≠ 0 := by
  exact xiShifted_ne_zero_on_imaginary_axis
    zetaRealNonzeroInCritical_proved y hyne hgt hlt

/-- The hard-difference form of the same unconditional imaginary-axis result. -/
theorem hardDifferenceNonzero_on_imaginary_axis_proved
    (y : ℝ) (hyne : y ≠ 0)
    (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    1 / ((Complex.I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS (Complex.I * (y : ℂ))) ≠ 0 := by
  exact hardDifferenceNonzero_on_imaginary_axis
      zetaRealNonzeroInCritical_proved y hyne hgt hlt

/-- The remaining point on the imaginary axis is the origin.  At this point
    `xiShifted` is the classical xi value at `1/2`; the eta-pair feeder gives
    the required zeta nonvanishing directly. -/
theorem xiShifted_ne_zero_at_origin_proved :
    xiShifted 0 ≠ 0 := by
  intro hzero
  have hz0 : classicalXi ((1 / 2 : ℂ)) = 0 := by
    simpa [xiShifted] using hzero
  have hmul :
      classicalXiPrefactor ((1 / 2 : ℂ)) *
        zeta ((1 / 2 : ℂ)) = 0 := by
    simpa [classicalXi, XiFromPrefactor] using hz0
  have hpref : classicalXiPrefactor ((1 / 2 : ℂ)) ≠ 0 := by
    exact classical_prefactor_nonzero_instrip
      classical_gamma_nonzero_instrip _ (by norm_num) (by norm_num)
  have hzeta : zeta ((1 / 2 : ℂ)) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hpref
  have hzeta' : zeta (((1 / 2 : ℝ) : ℂ)) = 0 := by
    simpa using hzeta
  exact zetaRealNonzeroInCritical_proved (1 / 2 : ℝ)
    (by norm_num) (by norm_num) hzeta'

theorem xiShifted_ne_zero_on_imaginary_axis_all_proved
    (y : ℝ) (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    xiShifted (Complex.I * (y : ℂ)) ≠ 0 := by
  by_cases hyne : y = 0
  · subst y
    simpa using xiShifted_ne_zero_at_origin_proved
  · exact xiShifted_ne_zero_on_imaginary_axis_proved y hyne hgt hlt

theorem hardDifferenceNonzero_at_origin_proved :
    1 / ((Complex.I * (0 : ℂ)) ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS (Complex.I * (0 : ℂ))) ≠ 0 := by
  have hxi : classicalXi ((1 / 2 : ℂ)) ≠ 0 := by
    simpa [xiShifted] using xiShifted_ne_zero_at_origin_proved
  have hid :
      1 / ((Complex.I * (0 : ℂ)) ^ 2 + (1 / 4 : ℂ)) -
          completedRiemannZeta₀ (shiftedS (Complex.I * (0 : ℂ))) =
        (8 : ℂ) * classicalXi ((1 / 2 : ℂ)) := by
    have hr := completedRiemannZeta₀_critical_line_remainder_eq_xi (0 : ℝ)
    norm_num [shiftedS] at hr ⊢
    linear_combination -hr
  rw [hid]
  exact mul_ne_zero (by norm_num) hxi

theorem hardDifferenceNonzero_on_imaginary_axis_all_proved
    (y : ℝ) (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    1 / ((Complex.I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS (Complex.I * (y : ℂ))) ≠ 0 := by
  by_cases hyne : y = 0
  · subst y
    simpa using hardDifferenceNonzero_at_origin_proved
  · exact hardDifferenceNonzero_on_imaginary_axis_proved y hyne hgt hlt

/-! Open top-edge points map to the imaginary axis in the `s`-coordinate.
The endpoint `x = 0` is excluded because the totalized product has the
artificial zero recorded in `door3_boundary_endpoints.lean`. -/

theorem xiShifted_ne_zero_on_top_edge_proved {x : ℝ} (hx : x ≠ 0) :
    xiShifted ((x : ℂ) + Complex.I / 2) ≠ 0 := by
  have hs : (1 / 2 : ℂ) + Complex.I * ((x : ℂ) + Complex.I / 2) =
      Complex.I * (x : ℂ) := by
    rw [mul_add]
    have hI : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      calc
        (Complex.I : ℂ) * (Complex.I / 2) =
            (Complex.I * Complex.I) / 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
    rw [hI]
    ring
  rw [show xiShifted ((x : ℂ) + Complex.I / 2) =
      classicalXi (Complex.I * (x : ℂ)) by
        unfold xiShifted
        rw [hs]]
  unfold classicalXi XiFromPrefactor classicalXiPrefactor
  have hz : riemannZeta (Complex.I * (x : ℂ)) ≠ 0 := by
    apply Door3TailEtaUpper.zeta_re_zero_nonzero
    · simp
    · simpa using hx
  have hs0 : (Complex.I * (x : ℂ)) ≠ 0 := by
    intro h
    have hi := congr_arg Complex.im h
    have hix : x = 0 := by simpa using hi
    exact hx hix
  have hs1 : Complex.I * (x : ℂ) - 1 ≠ 0 := by
    intro h
    have hr := congr_arg Complex.re h
    norm_num at hr
  have hpi : (Real.pi : ℂ) ^ (-((Complex.I * (x : ℂ)) / 2)) ≠ 0 :=
    pi_cpow_ne_zero _
  have hgam : Complex.Gamma ((Complex.I * (x : ℂ)) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hi := congr_arg Complex.im hn
    have hix : x = 0 := by simpa using hi
    exact hx hix
  have hpref : classicalXiPrefactor (Complex.I * (x : ℂ)) ≠ 0 := by
    unfold classicalXiPrefactor
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact hs0
        · exact hs1
      · exact hpi
    · exact hgam
  apply mul_ne_zero hpref
  simpa [zeta] using hz

theorem xiShifted_top_edge_center_norm_pos {x : ℝ} (hx : x ≠ 0) :
    0 < ‖xiShifted ((x : ℂ) + Complex.I / 2)‖ :=
  norm_pos_iff.mpr (xiShifted_ne_zero_on_top_edge_proved hx)

theorem xiShifted_top_edge_center_norm_nonzero {x : ℝ} (hx : x ≠ 0) :
    ‖xiShifted ((x : ℂ) + Complex.I / 2)‖ ≠ 0 :=
  ne_of_gt (xiShifted_top_edge_center_norm_pos hx)

#print axioms zetaRealNonzeroInCritical_proved
#print axioms classicalXiPrefactor_ne_zero_on_real_critical_proved
#print axioms classicalXi_ne_zero_on_real_critical_proved
#print axioms xiShifted_ne_zero_on_imaginary_axis_proved
#print axioms hardDifferenceNonzero_on_imaginary_axis_proved
#print axioms xiShifted_ne_zero_at_origin_proved
#print axioms xiShifted_ne_zero_on_imaginary_axis_all_proved
#print axioms hardDifferenceNonzero_at_origin_proved
#print axioms hardDifferenceNonzero_on_imaginary_axis_all_proved
#print axioms xiShifted_ne_zero_on_top_edge_proved
