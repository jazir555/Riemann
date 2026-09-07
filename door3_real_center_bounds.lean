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
