import zeta_rigorous

open Complex Real Set Topology

/-! A tighter lower bound for the first four reflected eta terms.  This is an
unconditional finite-sum certificate and is independent of the unresolved
tail estimate. -/

theorem D3_term1_im_upper :
    (etaDirichletTerm (1 - zetaCellS0) 1).im ≤ (-1 / 8 : ℝ) := by
  rw [D3_eta_im]
  have hpow : ((-1 : ℝ) ^ (1 : ℕ)) = -1 := by norm_num
  rw [hpow]
  have ha : (5 / 8 : ℝ) ≤ D3_amp 1 := D3_amp_two_lower
  have hs : Real.sin (D3_phase 1) ≤ (-1 / 5 : ℝ) := by
    have h := D3_sin_theta_two_mem.2
    norm_num at h ⊢
    exact h
  have ha0 : (0 : ℝ) ≤ D3_amp 1 := D3_amp_nonneg 1
  have hs0 : Real.sin (D3_phase 1) ≤ 0 := by linarith
  have hmul : D3_amp 1 * Real.sin (D3_phase 1) ≤
      (5 / 8 : ℝ) * Real.sin (D3_phase 1) := by
    exact mul_le_mul_of_nonpos_right ha hs0
  have hmul2 : (5 / 8 : ℝ) * Real.sin (D3_phase 1) ≤
      (5 / 8 : ℝ) * (-1 / 5 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  linarith

theorem D3_term2_im_upper :
    (etaDirichletTerm (1 - zetaCellS0) 2).im ≤ (13 / 25 : ℝ) * (1 / 5 : ℝ) := by
  rw [D3_eta_im]
  have hpow : ((-1 : ℝ) ^ (2 : ℕ)) = 1 := by norm_num
  rw [hpow, one_mul]
  have ha : D3_amp 2 ≤ (13 / 25 : ℝ) := D3_amp_three_upper
  have ha0 : (0 : ℝ) ≤ D3_amp 2 := D3_amp_nonneg 2
  have hslo : (-1 / 5 : ℝ) ≤ Real.sin (D3_phase 2) := by
    have h := D3_sin_theta_three_mem.1
    norm_num at h ⊢
    exact h
  have hs0 : (0 : ℝ) ≤ -Real.sin (D3_phase 2) := by
    have h := D3_sin_theta_three_mem.2
    norm_num at h ⊢
    linarith
  have hmul : D3_amp 2 * (-Real.sin (D3_phase 2)) ≤
      (13 / 25 : ℝ) * (-Real.sin (D3_phase 2)) := by
    exact mul_le_mul_of_nonneg_right ha hs0
  have hsupper : -Real.sin (D3_phase 2) ≤ (1 / 5 : ℝ) := by linarith
  have hmul2 : (13 / 25 : ℝ) * (-Real.sin (D3_phase 2)) ≤
      (13 / 25 : ℝ) * (1 / 5 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hsupper (by norm_num)
  linarith

theorem D3_term3_im_upper :
    (etaDirichletTerm (1 - zetaCellS0) 3).im ≤ (-41 / 100 : ℝ) * (5 / 12 : ℝ) := by
  rw [D3_eta_im]
  have hpow : ((-1 : ℝ) ^ (3 : ℕ)) = -1 := by norm_num
  rw [hpow]
  have ha : (5 / 12 : ℝ) ≤ D3_amp 3 := D3_amp_four_lower
  have hs : Real.sin (D3_phase 3) ≤ (-41 / 100 : ℝ) := by
    have h := D3_sin_theta_four_mem.2
    norm_num at h ⊢
    exact h
  have ha0 : (0 : ℝ) ≤ D3_amp 3 := D3_amp_nonneg 3
  have hs0 : Real.sin (D3_phase 3) ≤ 0 := by linarith
  have hmul : D3_amp 3 * Real.sin (D3_phase 3) ≤
      (5 / 12 : ℝ) * Real.sin (D3_phase 3) := by
    exact mul_le_mul_of_nonpos_right ha hs0
  have hmul2 : (5 / 12 : ℝ) * Real.sin (D3_phase 3) ≤
      (5 / 12 : ℝ) * (-41 / 100 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  linarith

theorem D3_S4_imag_upper :
    (∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k).im ≤
      (-1 / 8 : ℝ) + (13 / 25 : ℝ) * (1 / 5 : ℝ) +
        (-41 / 100 : ℝ) * (5 / 12 : ℝ) := by
  rw [show (∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k).im =
      ∑ k ∈ Finset.range 4, (etaDirichletTerm (1 - zetaCellS0) k).im by
        exact D3_sum_im_eq 4 (fun k => etaDirichletTerm (1 - zetaCellS0) k)]
  have hsum : (∑ k ∈ Finset.range 4, (etaDirichletTerm (1 - zetaCellS0) k).im) =
      (etaDirichletTerm (1 - zetaCellS0) 0).im +
      (etaDirichletTerm (1 - zetaCellS0) 1).im +
      (etaDirichletTerm (1 - zetaCellS0) 2).im +
      (etaDirichletTerm (1 - zetaCellS0) 3).im := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsum]
  have h0 : (etaDirichletTerm (1 - zetaCellS0) 0).im = 0 := by
    rw [D3_eta_im]
    norm_num [D3_phase_zero]
  rw [h0]
  linarith [D3_term1_im_upper, D3_term2_im_upper, D3_term3_im_upper]

theorem D3_S4_norm_ge_one_sixth :
    (1 / 6 : ℝ) ≤
      ‖∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  calc
    (1 / 6 : ℝ) ≤ |(∑ k ∈ Finset.range 4,
        etaDirichletTerm (1 - zetaCellS0) k).im| := by
      have h := D3_S4_imag_upper
      norm_num at h ⊢
      rw [abs_of_neg (by linarith [h])]
      linarith
    _ ≤ ‖∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k‖ :=
      Complex.abs_im_le_norm _

/-! The strengthened head certificate plugs directly into the existing
split lemma.  The remaining premise is exactly the middle-block estimate;
keeping it explicit prevents an analytic assumption from being hidden in the
certificate. -/
theorem D3_S1024_of_S4_imag (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 4 1024,
        etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (1 / 6 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024,
        etaDirichletTerm (1 - zetaCellS0) k‖ :=
  D3_S1024_split_lower 4 (by norm_num) (1 / 6) U
    D3_S4_norm_ge_one_sixth hU

#print axioms D3_S4_imag_upper
#print axioms D3_S4_norm_ge_one_sixth
#print axioms D3_S1024_of_S4_imag
