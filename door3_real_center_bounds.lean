import riemann_hypothesis

open Complex Real

noncomputable section

/-! Explicit lower bound for the real ζ-values used by the imaginary-axis
center slice.  The only analytic input is the already-proved continuation
identity for `riemannZeta₀` and positivity of its asymptotic tail. -/

private theorem D3_termTSum_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ ZetaAsymptotics.termTSum s := by
  unfold ZetaAsymptotics.termTSum
  exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) s)

theorem D3_real_zeta_re_upper {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (riemannZeta (s : ℂ)).re ≤ -s / (1 - s) := by
  have hsne : s ≠ 1 := by linarith
  have hz := riemannZeta_eq_inv_sub_add (s := (s : ℂ)) (by norm_cast)
  have h0 := riemannZeta₀_eq_one_sub_mul_termTSum_on hs
  have ht := D3_termTSum_nonneg hs
  have hprod : 0 ≤ s * ZetaAsymptotics.termTSum s :=
    mul_nonneg hs.le ht
  have hz0 : (riemannZeta₀ (s : ℂ)).re ≤ 1 := by
    rw [h0]
    linarith
  have hinv : (((s : ℂ) - 1)⁻¹).re = 1 / (s - 1) := by
    simp only [Complex.inv_re, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, Complex.normSq_apply,
      one_im, one_re, sub_zero, zero_mul, add_zero]
    field_simp [hsne]
  rw [hz, Complex.add_re, hinv]
  have hden : 0 < 1 - s := by linarith
  have hrewrite : 1 / (s - 1) = -1 / (1 - s) := by
    field_simp [ne_of_gt hden]
    ring
  rw [hrewrite]
  have hbound : -1 / (1 - s) + 1 ≤ -s / (1 - s) := by
    field_simp [ne_of_gt hden]
    ring_nf
    linarith
  linarith

theorem D3_real_zeta_norm_lower {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    s / (1 - s) ≤ ‖riemannZeta (s : ℂ)‖ := by
  have hupper := D3_real_zeta_re_upper hs hs1
  have hpos : 0 < s / (1 - s) := div_pos hs (by linarith)
  have hnegquot : -s / (1 - s) < 0 := by
    have heq : -s / (1 - s) = -(s / (1 - s)) := by ring
    rw [heq]
    exact neg_neg_of_pos hpos
  have hneg : (riemannZeta (s : ℂ)).re < 0 := by
    linarith
  have hquot : -s / (1 - s) = -(s / (1 - s)) := by ring
  calc
    s / (1 - s) ≤ |(riemannZeta (s : ℂ)).re| := by
      rw [abs_of_neg hneg]
      rw [hquot] at hupper
      linarith
    _ ≤ ‖riemannZeta (s : ℂ)‖ := Complex.abs_re_le_norm _

theorem D3_zeta_real_nonzero_in_critical : ZetaRealNonzeroInCritical := by
  intro t ht ht1 hz
  have hz' : riemannZeta (t : ℂ) = 0 := by
    simpa only [zeta] using hz
  have hnorm : ‖riemannZeta (t : ℂ)‖ = 0 := by
    rw [hz', norm_zero]
  have hlower := D3_real_zeta_norm_lower ht ht1
  have hpos : 0 < t / (1 - t) := div_pos ht (by linarith)
  linarith

theorem D3_imag_axis_nonzero_unconditional {y : ℝ}
    (hyne : y ≠ 0) (hy0 : -(1 / 2 : ℝ) < y) (hy1 : y < (1 / 2 : ℝ)) :
    xiShifted (Complex.I * (y : ℂ)) ≠ 0 :=
  xiShifted_ne_zero_on_imaginary_axis D3_zeta_real_nonzero_in_critical y
    hyne hy0 hy1

private theorem D3_real_gamma_lower {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    1 ≤ Real.Gamma (s / 2) := by
  have hx : s / 2 ∈ Set.Ioc (0 : ℝ) 1 := by constructor <;> linarith
  have hy : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have h := Real.Gamma_strictAntiOn_Ioc.antitoneOn hx hy (by linarith : s / 2 ≤ 1)
  simpa [Real.Gamma_one] using h

private theorem D3_real_cpow_lower {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (1 / 2 : ℝ) ≤ ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ := by
  have hcpow : (Real.pi : ℂ) ^ (-(s / 2 : ℂ)) =
      ((Real.pi ^ (-(s / 2 : ℝ)) : ℝ) : ℂ) := by
    have hexp : -(s / 2 : ℂ) = (-(s / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp]
    simpa using (Complex.ofReal_cpow (x := Real.pi) (y := -(s / 2 : ℝ))
      (le_of_lt Real.pi_pos)).symm
  rw [hcpow]
  simp only [Complex.norm_real]
  change (1 / 2 : ℝ) ≤ |Real.pi ^ (-(s / 2 : ℝ))|
  rw [abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _)]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp : -(1 / 2 : ℝ) ≤ -(s / 2 : ℝ) := by linarith
  have hp : Real.pi ^ (-(1 / 2 : ℝ)) ≤ Real.pi ^ (-(s / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hpi hexp
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hsqrt : Real.sqrt Real.pi < 2 := by
    nlinarith [Real.sq_sqrt (le_of_lt Real.pi_pos)]
  have hinv : (1 / 2 : ℝ) < Real.pi ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt Real.pi_pos), ← Real.sqrt_eq_rpow]
    have h := one_div_lt_one_div_of_lt (Real.sqrt_pos.2 Real.pi_pos) hsqrt
    simpa [one_div] using h
  linarith

theorem D3_real_prefactor_norm_lower {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    s * (1 - s) / 4 ≤ ‖classicalXiPrefactor (s : ℂ)‖ := by
  unfold classicalXiPrefactor
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Complex.Gamma_ofReal]
  have hsabs : ‖s‖ = s := by simp [abs_of_pos hs]
  have hsm1 : ‖(s : ℂ) - 1‖ = 1 - s := by
    have heq : (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub]
      norm_num
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : s - 1 < 0)]
    ring
  have hcpow := D3_real_cpow_lower hs hs1
  have hgamma : (1 : ℝ) ≤ ‖Complex.Gamma ((s : ℂ) / 2)‖ := by
    have heq : (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) := by norm_num
    rw [heq, Complex.Gamma_ofReal]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by positivity : 0 < s / 2))]
    exact D3_real_gamma_lower hs hs1
  rw [hsabs, hsm1]
  norm_num
  have hq : 0 ≤ s * (1 - s) := mul_nonneg hs.le (by linarith)
  have h1 : s * (1 - s) / 4 ≤ s * (1 - s) / 2 *
      ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ := by
    nlinarith
  have h2 : s * (1 - s) / 2 * ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ ≤
      s * (1 - s) / 2 * ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ *
        ‖Complex.Gamma ((s : ℂ) / 2)‖ :=
    le_mul_of_one_le_right (by positivity) hgamma
  calc
    s * (1 - s) / 4 ≤ s * (1 - s) / 2 *
        ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ := h1
    _ ≤ s * (1 - s) / 2 * ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ *
        ‖Complex.Gamma ((s : ℂ) / 2)‖ := h2
    _ ≤ (1 / 2 : ℝ) * s * (1 - s) *
        ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ *
        ‖Complex.Gamma ((s : ℂ) / 2)‖ := by
      have heq : (1 / 2 : ℝ) * s * (1 - s) *
          ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ *
          ‖Complex.Gamma ((s : ℂ) / 2)‖ =
          s * (1 - s) / 2 * ‖(Real.pi : ℂ) ^ (-(s / 2 : ℂ))‖ *
            ‖Complex.Gamma ((s : ℂ) / 2)‖ := by ring
      rw [heq]

def D3_real_xi_explicit_center_lower (s : ℝ) : ℝ := s ^ 2 / 8

theorem D3_real_xi_explicit_center_lower_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    D3_real_xi_explicit_center_lower s ≤ ‖classicalXi (s : ℂ)‖ := by
  unfold D3_real_xi_explicit_center_lower classicalXi XiFromPrefactor
  have hz := D3_real_zeta_norm_lower hs hs1
  have hp := D3_real_prefactor_norm_lower hs hs1
  have hq : 0 ≤ s / (1 - s) := div_nonneg hs.le (by linarith)
  have hmul : (s / (1 - s)) * (s * (1 - s) / 4) ≤
      ‖riemannZeta (s : ℂ)‖ * ‖classicalXiPrefactor (s : ℂ)‖ := by
    have hleft : (s / (1 - s)) * (s * (1 - s) / 4) ≤
        (s / (1 - s)) * ‖classicalXiPrefactor (s : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hp hq
    have hright : (s / (1 - s)) * ‖classicalXiPrefactor (s : ℂ)‖ ≤
        ‖riemannZeta (s : ℂ)‖ * ‖classicalXiPrefactor (s : ℂ)‖ := by
      have hh := mul_le_mul_of_nonneg_right hz
        (norm_nonneg (classicalXiPrefactor (s : ℂ)))
      simpa [mul_comm] using hh
    exact hleft.trans hright
  rw [norm_mul]
  simp only [zeta]
  have hid : s ^ 2 / 8 = (s / (1 - s)) * (s * (1 - s) / 4) / 2 := by
    field_simp [ne_of_gt (show 0 < 1 - s by linarith)]
    ring
  have hprod : 0 ≤ ‖classicalXiPrefactor (s : ℂ)‖ * ‖riemannZeta (s : ℂ)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hhalf := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
  have hhalf' : (s / (1 - s)) * (s * (1 - s) / 4) / 2 ≤
      ‖classicalXiPrefactor (s : ℂ)‖ * ‖riemannZeta (s : ℂ)‖ / 2 := by
    simpa [mul_comm] using hhalf
  rw [hid]
  nlinarith [hhalf', hprod]

def D3_real_xi_explicit_center_lower_strong (s : ℝ) : ℝ := s ^ 2 / 4

theorem D3_real_xi_explicit_center_lower_strong_le {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    D3_real_xi_explicit_center_lower_strong s ≤ ‖classicalXi (s : ℂ)‖ := by
  unfold D3_real_xi_explicit_center_lower_strong classicalXi XiFromPrefactor
  have hz := D3_real_zeta_norm_lower hs hs1
  have hp := D3_real_prefactor_norm_lower hs hs1
  have hq : 0 ≤ s / (1 - s) := div_nonneg hs.le (by linarith)
  have hmul : (s / (1 - s)) * (s * (1 - s) / 4) ≤
      ‖riemannZeta (s : ℂ)‖ * ‖classicalXiPrefactor (s : ℂ)‖ := by
    have hleft : (s / (1 - s)) * (s * (1 - s) / 4) ≤
        (s / (1 - s)) * ‖classicalXiPrefactor (s : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hp hq
    have hright : (s / (1 - s)) * ‖classicalXiPrefactor (s : ℂ)‖ ≤
        ‖riemannZeta (s : ℂ)‖ * ‖classicalXiPrefactor (s : ℂ)‖ := by
      have hh := mul_le_mul_of_nonneg_right hz
        (norm_nonneg (classicalXiPrefactor (s : ℂ)))
      simpa [mul_comm] using hh
    exact hleft.trans hright
  rw [norm_mul]
  simp only [zeta]
  have hid : s ^ 2 / 4 = (s / (1 - s)) * (s * (1 - s) / 4) := by
    field_simp [ne_of_gt (show 0 < 1 - s by linarith)]
  rw [hid]
  nlinarith [hmul]

def D3_imag_axis_explicit_center_lower (y : ℝ) : ℝ :=
  (1 / 2 - y) ^ 2 / 4

theorem D3_imag_axis_explicit_center_lower_le {y : ℝ}
    (hy0 : -(1 / 2 : ℝ) < y) (hy1 : y < (1 / 2 : ℝ)) :
    D3_imag_axis_explicit_center_lower y ≤
      ‖xiShifted (Complex.I * (y : ℂ))‖ := by
  unfold D3_imag_axis_explicit_center_lower
  have hs0 : 0 < (1 / 2 : ℝ) - y := by linarith
  have hs1 : (1 / 2 : ℝ) - y < 1 := by linarith
  have h := D3_real_xi_explicit_center_lower_strong_le hs0 hs1
  have hsarg : (1 / 2 : ℂ) + Complex.I * (Complex.I * (y : ℂ)) =
      ((1 / 2 - y : ℝ) : ℂ) := by
    calc
      (1 / 2 : ℂ) + Complex.I * (Complex.I * (y : ℂ)) =
          (1 / 2 : ℂ) + Complex.I ^ 2 * (y : ℂ) := by ring
      _ = (1 / 2 - y : ℝ) := by
        rw [Complex.I_sq]
        push_cast
        ring
  rw [show xiShifted (Complex.I * (y : ℂ)) =
      classicalXi ((1 / 2 - y : ℝ) : ℂ) by
        unfold xiShifted
        rw [hsarg]]
  exact h

theorem D3_explicit_center_lower_21 :
    (6241 / 160000 : ℝ) ≤
      ‖xiShifted (Complex.I * ((21 / 200 : ℝ) : ℂ))‖ := by
  convert D3_imag_axis_explicit_center_lower_le (y := (21 / 200 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
    norm_num [D3_imag_axis_explicit_center_lower]

theorem D3_explicit_center_lower_1_4 :
    (1 / 64 : ℝ) ≤
      ‖xiShifted (Complex.I * ((1 / 4 : ℝ) : ℂ))‖ := by
  convert D3_imag_axis_explicit_center_lower_le (y := (1 / 4 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
    norm_num [D3_imag_axis_explicit_center_lower]

theorem D3_explicit_center_lower_7_20 :
    (9 / 1600 : ℝ) ≤
      ‖xiShifted (Complex.I * ((7 / 20 : ℝ) : ℂ))‖ := by
  convert D3_imag_axis_explicit_center_lower_le (y := (7 / 20 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
    norm_num [D3_imag_axis_explicit_center_lower]

theorem D3_explicit_center_lower_89 :
    (121 / 160000 : ℝ) ≤
      ‖xiShifted (Complex.I * ((89 / 200 : ℝ) : ℂ))‖ := by
  convert D3_imag_axis_explicit_center_lower_le (y := (89 / 200 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
    norm_num [D3_imag_axis_explicit_center_lower]

theorem D3_explicit_center_lower_0 :
    (1 / 16 : ℝ) ≤ ‖xiShifted (0 : ℂ)‖ := by
  convert D3_imag_axis_explicit_center_lower_le (y := (0 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
    norm_num [D3_imag_axis_explicit_center_lower]

theorem D3_imag_axis_explicit_center_uniform {y : ℝ}
    (hy0 : -(49 / 100 : ℝ) ≤ y) (hy1 : y ≤ (49 / 100 : ℝ)) :
    (1 / 40000 : ℝ) ≤ ‖xiShifted (Complex.I * (y : ℂ))‖ := by
  have h := D3_imag_axis_explicit_center_lower_le
    (y := y) (by linarith) (by linarith)
  have hs : (1 / 100 : ℝ) ≤ 1 / 2 - y := by linarith
  have hsquare : (1 / 100 : ℝ) ^ 2 ≤ (1 / 2 - y) ^ 2 := by
    nlinarith [sq_nonneg ((1 / 2 - y) - (1 / 100 : ℝ))]
  unfold D3_imag_axis_explicit_center_lower at h
  nlinarith

theorem D3_imag_axis_explicit_center_nonzero_uniform {y : ℝ}
    (hy0 : -(49 / 100 : ℝ) ≤ y) (hy1 : y ≤ (49 / 100 : ℝ)) :
    xiShifted (Complex.I * (y : ℂ)) ≠ 0 := by
  have h := D3_imag_axis_explicit_center_uniform hy0 hy1
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

def D3_real_xi_center_lower (s : ℝ) : ℝ :=
  (s / (1 - s)) * ‖classicalXiPrefactor (s : ℂ)‖ / 2

theorem D3_real_xi_center_lower_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < D3_real_xi_center_lower s := by
  unfold D3_real_xi_center_lower
  have hq : 0 < s / (1 - s) := div_pos hs (by linarith)
  have hp : classicalXiPrefactor (s : ℂ) ≠ 0 :=
    classical_prefactor_nonzero_instrip classical_gamma_nonzero_instrip
      (s : ℂ) (by simpa using hs) (by simpa using hs1)
  have hpn : 0 < ‖classicalXiPrefactor (s : ℂ)‖ := norm_pos_iff.mpr hp
  positivity

theorem D3_real_xi_center_lower_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    D3_real_xi_center_lower s ≤ ‖classicalXi (s : ℂ)‖ := by
  unfold D3_real_xi_center_lower classicalXi XiFromPrefactor
  have hq := D3_real_zeta_norm_lower hs hs1
  have hqnonneg : 0 ≤ s / (1 - s) := div_nonneg hs.le (by linarith)
  have hp : 0 ≤ ‖classicalXiPrefactor (s : ℂ)‖ := norm_nonneg _
  have hmul : ‖classicalXiPrefactor (s : ℂ)‖ * (s / (1 - s)) ≤
      ‖classicalXiPrefactor (s : ℂ)‖ * ‖riemannZeta (s : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hq hp
  rw [norm_mul]
  simp only [zeta]
  nlinarith [hmul, hqnonneg, hp]

def D3_imag_axis_xi_center_lower (y : ℝ) : ℝ :=
  D3_real_xi_center_lower (1 / 2 - y)

theorem D3_imag_axis_xi_center_lower_pos {y : ℝ}
    (hy0 : -(1 / 2 : ℝ) < y) (hy1 : y < (1 / 2 : ℝ)) :
    0 < D3_imag_axis_xi_center_lower y := by
  unfold D3_imag_axis_xi_center_lower
  apply D3_real_xi_center_lower_pos <;> linarith

theorem D3_imag_axis_xi_center_lower_le {y : ℝ}
    (hy0 : -(1 / 2 : ℝ) < y) (hy1 : y < (1 / 2 : ℝ)) :
    D3_imag_axis_xi_center_lower y ≤
      ‖xiShifted (Complex.I * (y : ℂ))‖ := by
  have hσ0 : 0 < (1 / 2 : ℝ) - y := by linarith
  have hσ1 : (1 / 2 : ℝ) - y < 1 := by linarith
  have h := D3_real_xi_center_lower_le hσ0 hσ1
  have hsarg : (1 / 2 : ℂ) + Complex.I * (Complex.I * (y : ℂ)) =
      ((1 / 2 - y : ℝ) : ℂ) := by
    calc
      (1 / 2 : ℂ) + Complex.I * (Complex.I * (y : ℂ)) =
          (1 / 2 : ℂ) + Complex.I ^ 2 * (y : ℂ) := by ring
      _ = (1 / 2 - y : ℝ) := by
        rw [Complex.I_sq]
        push_cast
        ring
  rw [show xiShifted (Complex.I * (y : ℂ)) =
      classicalXi ((1 / 2 - y : ℝ) : ℂ) by
        unfold xiShifted
        rw [hsarg]]
  exact h

#print axioms D3_real_xi_center_lower_pos
#print axioms D3_real_xi_center_lower_le
#print axioms D3_imag_axis_xi_center_lower_pos
#print axioms D3_imag_axis_xi_center_lower_le

#print axioms D3_real_zeta_re_upper
#print axioms D3_real_zeta_norm_lower
