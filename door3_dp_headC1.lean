import Mathlib
import door3_dp_trig
import door3_dp_terms
theorem dp_headC1_log5_lo : 16094 / 10000 ≤ Real.log 5 := by
  have h := Real.log_five_gt_d9
  norm_num at h ⊢
  linarith
theorem dp_headC1_log5_hi : Real.log 5 ≤ 16095 / 10000 := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith
theorem dp_headC1_log2401_eq : Real.log 2401 = 4 * Real.log 7 := by
  have heq : (2401 : ℝ) = 7 * (7 * (7 * 7)) := by norm_num
  have h1 : Real.log (7 * (7 * (7 * 7))) = Real.log 7 + Real.log (7 * (7 * 7)) := Real.log_mul (by norm_num) (by norm_num)
  have h2 : Real.log (7 * (7 * 7)) = Real.log 7 + Real.log (7 * 7) := Real.log_mul (by norm_num) (by norm_num)
  have h3 : Real.log (7 * 7) = Real.log 7 + Real.log 7 := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, h1, h2, h3]
  ring
theorem dp_headC1_log2400_eq : Real.log 2400 = 5 * Real.log 2 + (Real.log 3 + 2 * Real.log 5) := by
  have heq : (2400 : ℝ) = (2 * (2 * (2 * (2 * 2)))) * (3 * (5 * 5)) := by norm_num
  have ha : Real.log (2 * (2 * (2 * (2 * 2)))) = Real.log 2 + Real.log (2 * (2 * (2 * 2))) := Real.log_mul (by norm_num) (by norm_num)
  have hb : Real.log (2 * (2 * (2 * 2))) = Real.log 2 + Real.log (2 * (2 * 2)) := Real.log_mul (by norm_num) (by norm_num)
  have hc : Real.log (2 * (2 * 2)) = Real.log 2 + Real.log (2 * 2) := Real.log_mul (by norm_num) (by norm_num)
  have hd : Real.log (2 * 2) = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
  have he : Real.log (3 * (5 * 5)) = Real.log 3 + Real.log (5 * 5) := Real.log_mul (by norm_num) (by norm_num)
  have hf : Real.log (5 * 5) = Real.log 5 + Real.log 5 := Real.log_mul (by norm_num) (by norm_num)
  have hg : Real.log ((2 * (2 * (2 * (2 * 2)))) * (3 * (5 * 5))) = Real.log (2 * (2 * (2 * (2 * 2)))) + Real.log (3 * (5 * 5)) := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, hg, ha, hb, hc, hd, he, hf]
  ring
theorem dp_headC1_delta_lo : (1 : ℝ) / 2401 ≤ Real.log (2401 / 2400) := by
  have hpos : (0 : ℝ) < 2400 / 2401 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (2401 / 2400) = -Real.log (2400 / 2401) := by
    have e : (2401 / 2400 : ℝ) = (2400 / 2401 : ℝ)⁻¹ := by norm_num
    rw [e, Real.log_inv]
  have heq : (2400 : ℝ) / 2401 - 1 = -(1 / 2401) := by norm_num
  rw [heq] at hub
  linarith [hub, hinv]
theorem dp_headC1_delta_hi : Real.log (2401 / 2400) ≤ (1 : ℝ) / 2400 := by
  have hpos : (0 : ℝ) < 2401 / 2400 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have heq : (2401 : ℝ) / 2400 - 1 = 1 / 2400 := by norm_num
  rw [heq] at hub
  exact hub
theorem dp_headC1_log7_lo : 19458 / 10000 ≤ Real.log 7 := by
  have h2lo := dp_log2_lo
  have h3lo := dp_log3_lo
  have h5lo := dp_headC1_log5_lo
  have hdlo := dp_headC1_delta_lo
  have h2401 := dp_headC1_log2401_eq
  have h2400 := dp_headC1_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 := Real.log_div (by norm_num) (by norm_num)
  linarith [h2lo, h3lo, h5lo, hdlo, h2401, h2400, hdiv]
theorem dp_headC1_log7_hi : Real.log 7 ≤ 19461 / 10000 := by
  have h2hi := dp_log2_hi
  have h3hi := dp_log3_hi
  have h5hi := dp_headC1_log5_hi
  have hdhi := dp_headC1_delta_hi
  have h2401 := dp_headC1_log2401_eq
  have h2400 := dp_headC1_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 := Real.log_div (by norm_num) (by norm_num)
  linarith [h2hi, h3hi, h5hi, hdhi, h2401, h2400, hdiv]
theorem dp_headC1_log45_eq : Real.log 45 = 2 * Real.log 3 + Real.log 5 := by
  have heq : (45 : ℝ) = (3 * 3) * 5 := by norm_num
  have h1 : Real.log (3 * 3) = Real.log 3 + Real.log 3 := Real.log_mul (by norm_num) (by norm_num)
  have h2 : Real.log ((3 * 3) * 5) = Real.log (3 * 3) + Real.log 5 := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, h2, h1]
  ring
theorem dp_headC1_log48_eq : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
  have heq : (48 : ℝ) = (2 * (2 * (2 * 2))) * 3 := by norm_num
  have ha : Real.log (2 * (2 * (2 * 2))) = Real.log 2 + Real.log (2 * (2 * 2)) := Real.log_mul (by norm_num) (by norm_num)
  have hb : Real.log (2 * (2 * 2)) = Real.log 2 + Real.log (2 * 2) := Real.log_mul (by norm_num) (by norm_num)
  have hc : Real.log (2 * 2) = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
  have hd : Real.log ((2 * (2 * (2 * 2))) * 3) = Real.log (2 * (2 * (2 * 2))) + Real.log 3 := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, hd, ha, hb, hc]
  ring
theorem dp_headC1_log49_eq : Real.log 49 = 2 * Real.log 7 := by
  have heq : (49 : ℝ) = 7 * 7 := by norm_num
  have h1 : Real.log (7 * 7) = Real.log 7 + Real.log 7 := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, h1]
  ring
theorem dp_headC1_delta46_lo : (1 : ℝ) / 46 ≤ Real.log (46 / 45) := by
  have hpos : (0 : ℝ) < 45 / 46 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (46 / 45) = -Real.log (45 / 46) := by
    have e : (46 / 45 : ℝ) = (45 / 46 : ℝ)⁻¹ := by norm_num
    rw [e, Real.log_inv]
  have heq : (45 : ℝ) / 46 - 1 = -(1 / 46) := by norm_num
  rw [heq] at hub
  linarith [hub, hinv]
theorem dp_headC1_delta46_hi : Real.log (46 / 45) ≤ (1 : ℝ) / 45 := by
  have hpos : (0 : ℝ) < 46 / 45 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have heq : (46 : ℝ) / 45 - 1 = 1 / 45 := by norm_num
  rw [heq] at hub
  exact hub
theorem dp_headC1_delta4847_lo : (1 : ℝ) / 48 ≤ Real.log (48 / 47) := by
  have hpos : (0 : ℝ) < 47 / 48 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (48 / 47) = -Real.log (47 / 48) := by
    have e : (48 / 47 : ℝ) = (47 / 48 : ℝ)⁻¹ := by norm_num
    rw [e, Real.log_inv]
  have heq : (47 : ℝ) / 48 - 1 = -(1 / 48) := by norm_num
  rw [heq] at hub
  linarith [hub, hinv]
theorem dp_headC1_delta4847_hi : Real.log (48 / 47) ≤ (1 : ℝ) / 47 := by
  have hpos : (0 : ℝ) < 48 / 47 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have heq : (48 : ℝ) / 47 - 1 = 1 / 47 := by norm_num
  rw [heq] at hub
  exact hub

noncomputable def dp_headC1_c45 : ℂ := ⟨(1391 / 10000 : ℝ), (538 / 10000 : ℝ)⟩
noncomputable def dp_headC1_c46 : ℂ := ⟨(1226 / 10000 : ℝ), (818 / 10000 : ℝ)⟩
noncomputable def dp_headC1_c47 : ℂ := ⟨(1013 / 10000 : ℝ), (1046 / 10000 : ℝ)⟩
noncomputable def dp_headC1_c48 : ℂ := ⟨(762 / 10000 : ℝ), (1225 / 10000 : ℝ)⟩
noncomputable def dp_headC1_c49 : ℂ := ⟨(490 / 10000 : ℝ), (1342 / 10000 : ℝ)⟩
theorem dp_headC1_n45_tight : ‖((((45 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_headC1_c45‖ ≤ 1 / 100 := by
  have h3lo := dp_log3_lo
  have h3hi := dp_log3_hi
  have h5lo := dp_headC1_log5_lo
  have h5hi := dp_headC1_log5_hi
  have h45 := dp_headC1_log45_eq
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx : |(10 : ℝ) * Real.log 45| ≤ 40 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45]
  have hr_le : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ≤ 1 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi) - 3689 / 10000| ≤ 30 / 10000 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
  have hr_abs : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ≤ 2 / 5 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 45 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 45) hx 6 ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 45) hx 6 ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) (3689 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) (3689 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 ≤ (2 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hr_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 2 / 10000 := by
    have h0 : (2 / 5 : ℝ) ^ 5 / 100 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (2 / 5 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (2 / 5 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (2 / 5 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 45) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)| ≤ 50 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 45) - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 100 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq]
      · linarith [hs_hi, hs_hi_eq]
    have h2 : |((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6 - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (30 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith [hlip_s, hmul]
    have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 45) - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6)) ((((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6))
    have heq : Real.sin ((10 : ℝ) * Real.log 45) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 45) - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_s]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 45) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 95 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 45) - (1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hc_lo, hc_lo_eq]
      · linarith [hc_hi, hc_hi_eq]
    have h2 : |(1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (30 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 45) - (1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 45) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 45) - (1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 45 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_c]
  have hsqrt_lo : 6708 / 1000 ≤ Real.sqrt 45 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 45 ≤ 6709 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_eq : (45 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 45)⁻¹ := by
    have hsqrt_eq : Real.sqrt 45 = (45 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 45
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (45 : ℝ) ^ (-1 / 2 : ℝ) = ((45 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (1490 / 10000 : ℝ) ≤ (45 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (6709 / 1000) ≤ 1 / Real.sqrt 45 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (1490 / 10000 : ℝ) ≤ 1 / (6709 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (45 : ℝ) ^ (-1 / 2 : ℝ) ≤ (1492 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 45 ≤ 1 / (6708 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (6708 / 1000) ≤ 1492 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]; constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 45 (by norm_num)
  have him := dp_cpow10_im 45 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 45)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 45)
  have hcenter_re : |(1491 / 10000 : ℝ) * (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1391 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1491 / 10000 : ℝ) * ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6) - 538 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((45 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1391 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headC1_c45 : ℂ)).re = 1391 / 10000 := by simp [dp_headC1_c45]
    rw [hre]
    have ha0 : |(1491 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 45)| ≤ 1 := hcos_le1
    have e1 : |(45 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 45) - 1491 / 10000 * (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 6 * (95 / 10000) := by
      have hsplit : (45 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 45) - 1491 / 10000 * (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000) * Real.cos (10 * Real.log 45) + 1491 / 10000 * (Real.cos (10 * Real.log 45) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000) * Real.cos (10 * Real.log 45)) (1491 / 10000 * (Real.cos (10 * Real.log 45) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000)| * |Real.cos (10 * Real.log 45)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(1491 / 10000 : ℝ)| * |Real.cos (10 * Real.log 45) - (1 - 2 * ((3689 / 10000 : ℝ) / 2 - ((3689 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 6) * (95 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((45 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (538 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headC1_c45 : ℂ)).im = 538 / 10000 := by simp [dp_headC1_c45]
    rw [him]
    have ha0 : |(1491 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 45)| ≤ 1 := hsin_le1
    have e1 : |(45 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 45) - 1491 / 10000 * ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 / 6 * (50 / 10000) := by
      have hsplit : (45 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 45) - 1491 / 10000 * ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6) = ((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000) * Real.sin (10 * Real.log 45) + 1491 / 10000 * (Real.sin (10 * Real.log 45) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000) * Real.sin (10 * Real.log 45)) (1491 / 10000 * (Real.sin (10 * Real.log 45) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((45 : ℝ) ^ (-1 / 2 : ℝ) - 1491 / 10000)| * |Real.sin (10 * Real.log 45)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(1491 / 10000 : ℝ)| * |Real.sin (10 * Real.log 45) - ((3689 / 10000 : ℝ) - (3689 / 10000 : ℝ) ^ 3 / 6)| ≤ (1 / 6) * (50 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((45 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headC1_c45 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_headC1_n46_tight : ‖((((46 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_headC1_c46‖ ≤ 1 / 100 := by
  have h3lo := dp_log3_lo
  have h3hi := dp_log3_hi
  have h5lo := dp_headC1_log5_lo
  have h5hi := dp_headC1_log5_hi
  have h45 := dp_headC1_log45_eq
  have hdlo := dp_headC1_delta46_lo
  have hdhi := dp_headC1_delta46_hi
  have hdiv : Real.log (46 / 45) = Real.log 46 - Real.log 45 := Real.log_div (by norm_num) (by norm_num)
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx : |(10 : ℝ) * Real.log 46| ≤ 40 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv]
  have hr_le : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ≤ 1 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi) - 5887 / 10000| ≤ 55 / 10000 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hr_abs : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ≤ 3 / 5 := by
    rw [abs_le]; constructor
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h3lo, h3hi, h5lo, h5hi, h45, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 46 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 46) hx 6 ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 46) hx 6 ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) (5887 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) (5887 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 ≤ (3 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hr_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 8 / 10000 := by
    have h0 : (3 / 5 : ℝ) ^ 5 / 100 ≤ 8 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (3 / 5 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 2 / 10000 := by
    have h0 : (3 / 5 : ℝ) ^ 5 / 800 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (3 / 5 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 46) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)| ≤ 95 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 46) - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 100 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq]
      · linarith [hs_hi, hs_hi_eq]
    have h2 : |((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6 - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (55 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith [hlip_s, hmul]
    have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 46) - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6)) ((((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6))
    have heq : Real.sin ((10 : ℝ) * Real.log 46) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 46) - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_s]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 46) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 170 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 46) - (1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hc_lo, hc_lo_eq]
      · linarith [hc_hi, hc_hi_eq]
    have h2 : |(1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (55 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 46) - (1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 46) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 46) - (1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 46 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_c]
  have hsqrt_lo : 6782 / 1000 ≤ Real.sqrt 46 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 46 ≤ 6783 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_eq : (46 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 46)⁻¹ := by
    have hsqrt_eq : Real.sqrt 46 = (46 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 46
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (46 : ℝ) ^ (-1 / 2 : ℝ) = ((46 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (1473 / 10000 : ℝ) ≤ (46 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (6783 / 1000) ≤ 1 / Real.sqrt 46 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (1473 / 10000 : ℝ) ≤ 1 / (6783 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (46 : ℝ) ^ (-1 / 2 : ℝ) ≤ (1475 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 46 ≤ 1 / (6782 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (6782 / 1000) ≤ 1475 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]; constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 46 (by norm_num)
  have him := dp_cpow10_im 46 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 46)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 46)
  have hcenter_re : |(1474 / 10000 : ℝ) * (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1226 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1474 / 10000 : ℝ) * ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6) - 818 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((46 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1226 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headC1_c46 : ℂ)).re = 1226 / 10000 := by simp [dp_headC1_c46]
    rw [hre]
    have ha0 : |(1474 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 46)| ≤ 1 := hcos_le1
    have e1 : |(46 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 46) - 1474 / 10000 * (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 6 * (170 / 10000) := by
      have hsplit : (46 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 46) - 1474 / 10000 * (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000) * Real.cos (10 * Real.log 46) + 1474 / 10000 * (Real.cos (10 * Real.log 46) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000) * Real.cos (10 * Real.log 46)) (1474 / 10000 * (Real.cos (10 * Real.log 46) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000)| * |Real.cos (10 * Real.log 46)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(1474 / 10000 : ℝ)| * |Real.cos (10 * Real.log 46) - (1 - 2 * ((5887 / 10000 : ℝ) / 2 - ((5887 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 6) * (170 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((46 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (818 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headC1_c46 : ℂ)).im = 818 / 10000 := by simp [dp_headC1_c46]
    rw [him]
    have ha0 : |(1474 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 46)| ≤ 1 := hsin_le1
    have e1 : |(46 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 46) - 1474 / 10000 * ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 / 6 * (95 / 10000) := by
      have hsplit : (46 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 46) - 1474 / 10000 * ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6) = ((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000) * Real.sin (10 * Real.log 46) + 1474 / 10000 * (Real.sin (10 * Real.log 46) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000) * Real.sin (10 * Real.log 46)) (1474 / 10000 * (Real.sin (10 * Real.log 46) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((46 : ℝ) ^ (-1 / 2 : ℝ) - 1474 / 10000)| * |Real.sin (10 * Real.log 46)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(1474 / 10000 : ℝ)| * |Real.sin (10 * Real.log 46) - ((5887 / 10000 : ℝ) - (5887 / 10000 : ℝ) ^ 3 / 6)| ≤ (1 / 6) * (95 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((46 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headC1_c46 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_headC1_n47_tight : ‖((((47 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_headC1_c47‖ ≤ 1 / 100 := by
  have h2lo := dp_log2_lo
  have h2hi := dp_log2_hi
  have h3lo := dp_log3_lo
  have h3hi := dp_log3_hi
  have h48 := dp_headC1_log48_eq
  have hdlo := dp_headC1_delta4847_lo
  have hdhi := dp_headC1_delta4847_hi
  have hdiv : Real.log (48 / 47) = Real.log 48 - Real.log 47 := Real.log_div (by norm_num) (by norm_num)
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx : |(10 : ℝ) * Real.log 47| ≤ 40 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv]
  have hr_le : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ≤ 1 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi) - 8034 / 10000| ≤ 60 / 10000 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hr_abs : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ≤ 81 / 100 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hdlo, hdhi, hdiv, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 47 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 47) hx 6 ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 47) hx 6 ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) (8034 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) (8034 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 ≤ (81 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hr_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 35 / 10000 := by
    have h0 : (81 / 100 : ℝ) ^ 5 / 100 ≤ 35 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (81 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 5 / 10000 := by
    have h0 : (81 / 100 : ℝ) ^ 5 / 800 ≤ 5 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (81 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 47) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)| ≤ 130 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 47) - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 100 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq]
      · linarith [hs_hi, hs_hi_eq]
    have h2 : |((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6 - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (60 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith [hlip_s, hmul]
    have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 47) - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6)) ((((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6))
    have heq : Real.sin ((10 : ℝ) * Real.log 47) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 47) - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_s]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 47) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 190 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 47) - (1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hc_lo, hc_lo_eq]
      · linarith [hc_hi, hc_hi_eq]
    have h2 : |(1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (60 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 47) - (1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 47) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 47) - (1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 47 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_c]
  have hsqrt_lo : 6855 / 1000 ≤ Real.sqrt 47 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 47 ≤ 6856 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_eq : (47 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 47)⁻¹ := by
    have hsqrt_eq : Real.sqrt 47 = (47 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 47
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (47 : ℝ) ^ (-1 / 2 : ℝ) = ((47 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (1458 / 10000 : ℝ) ≤ (47 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (6856 / 1000) ≤ 1 / Real.sqrt 47 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (1458 / 10000 : ℝ) ≤ 1 / (6856 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (47 : ℝ) ^ (-1 / 2 : ℝ) ≤ (1460 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 47 ≤ 1 / (6855 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (6855 / 1000) ≤ 1460 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]; constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 47 (by norm_num)
  have him := dp_cpow10_im 47 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 47)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 47)
  have hcenter_re : |(1459 / 10000 : ℝ) * (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1013 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1459 / 10000 : ℝ) * ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6) - 1046 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((47 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1013 / 10000 : ℝ)| ≤ 55 / 10000 := by
    have hCre : ((dp_headC1_c47 : ℂ)).re = 1013 / 10000 := by simp [dp_headC1_c47]
    rw [hre]
    have ha0 : |(1459 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 47)| ≤ 1 := hcos_le1
    have e1 : |(47 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 47) - 1459 / 10000 * (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 6 * (190 / 10000) := by
      have hsplit : (47 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 47) - 1459 / 10000 * (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000) * Real.cos (10 * Real.log 47) + 1459 / 10000 * (Real.cos (10 * Real.log 47) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000) * Real.cos (10 * Real.log 47)) (1459 / 10000 * (Real.cos (10 * Real.log 47) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000)| * |Real.cos (10 * Real.log 47)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(1459 / 10000 : ℝ)| * |Real.cos (10 * Real.log 47) - (1 - 2 * ((8034 / 10000 : ℝ) / 2 - ((8034 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 6) * (190 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((47 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1046 / 10000 : ℝ)| ≤ 45 / 10000 := by
    have hCim : ((dp_headC1_c47 : ℂ)).im = 1046 / 10000 := by simp [dp_headC1_c47]
    rw [him]
    have ha0 : |(1459 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 47)| ≤ 1 := hsin_le1
    have e1 : |(47 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 47) - 1459 / 10000 * ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 / 6 * (130 / 10000) := by
      have hsplit : (47 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 47) - 1459 / 10000 * ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6) = ((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000) * Real.sin (10 * Real.log 47) + 1459 / 10000 * (Real.sin (10 * Real.log 47) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000) * Real.sin (10 * Real.log 47)) (1459 / 10000 * (Real.sin (10 * Real.log 47) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((47 : ℝ) ^ (-1 / 2 : ℝ) - 1459 / 10000)| * |Real.sin (10 * Real.log 47)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(1459 / 10000 : ℝ)| * |Real.sin (10 * Real.log 47) - ((8034 / 10000 : ℝ) - (8034 / 10000 : ℝ) ^ 3 / 6)| ≤ (1 / 6) * (130 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((47 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headC1_c47 (55 / 10000) (45 / 10000) hre_bound him_bound
  linarith [h]
theorem dp_headC1_n48_tight : ‖((((48 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_headC1_c48‖ ≤ 1 / 100 := by
  have h2lo := dp_log2_lo
  have h2hi := dp_log2_hi
  have h3lo := dp_log3_lo
  have h3hi := dp_log3_hi
  have h48 := dp_headC1_log48_eq
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx : |(10 : ℝ) * Real.log 48| ≤ 40 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48]
  have he_le : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ≤ 1 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2 - (-5569 / 10000)| ≤ 40 / 10000 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ≤ 3 / 5 := by
    rw [abs_le]; constructor
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
    · linarith [h2lo, h2hi, h3lo, h3hi, h48, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 48 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2 = ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 48) ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) hx 6 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 48) ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) hx 6 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) (-5569 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) (-5569 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 ≤ (3 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 ≤ 8 / 10000 := by
    have h0 : (3 / 5 : ℝ) ^ 5 / 100 ≤ 8 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 ≤ (3 / 5 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 ≤ 2 / 10000 := by
    have h0 : (3 / 5 : ℝ) ^ 5 / 800 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 ≤ (3 / 5 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 48) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 125 / 10000 := by
    have ha : |Real.cos ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq, hs_eq]
      · linarith [hs_hi, hs_hi_eq, hs_eq]
    have hb : |(1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (40 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    rw [hs_eq]
    linarith [htri, ha, hb, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 48) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))| ≤ 70 / 10000 := by
    have hpoly : |(-Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2)) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)| := by
      have e : (-Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2)) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [e, abs_neg]
    have h1 : |Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)| ≤ 8 / 10000 + 3 / 2 * (40 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (40 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 48 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    rw [hc_eq]
    linarith [hpoly, h1, hrem_s]
  have hsqrt_lo : 6928 / 1000 ≤ Real.sqrt 48 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 48 ≤ 6929 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_eq : (48 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 48)⁻¹ := by
    have hsqrt_eq : Real.sqrt 48 = (48 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 48
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (48 : ℝ) ^ (-1 / 2 : ℝ) = ((48 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (1442 / 10000 : ℝ) ≤ (48 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (6929 / 1000) ≤ 1 / Real.sqrt 48 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (1442 / 10000 : ℝ) ≤ 1 / (6929 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (48 : ℝ) ^ (-1 / 2 : ℝ) ≤ (1444 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 48 ≤ 1 / (6928 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (6928 / 1000) ≤ 1444 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]; constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 48 (by norm_num)
  have him := dp_cpow10_im 48 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 48)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 48)
  have hcenter_re : |(1443 / 10000 : ℝ) * (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)) - 762 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1443 / 10000 : ℝ) * (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1225 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((48 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (762 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headC1_c48 : ℂ)).re = 762 / 10000 := by simp [dp_headC1_c48]
    rw [hre]
    have ha0 : |(1443 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 48)| ≤ 1 := hcos_le1
    have e1 : |(48 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 48) - 1443 / 10000 * (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))| ≤ 1 / 1000 * 1 + 1 / 6 * (70 / 10000) := by
      have hsplit : (48 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 48) - 1443 / 10000 * (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6)) = ((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000) * Real.cos (10 * Real.log 48) + 1443 / 10000 * (Real.cos (10 * Real.log 48) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000) * Real.cos (10 * Real.log 48)) (1443 / 10000 * (Real.cos (10 * Real.log 48) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000)| * |Real.cos (10 * Real.log 48)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(1443 / 10000 : ℝ)| * |Real.cos (10 * Real.log 48) - (-((-5569 / 10000 : ℝ) - (-5569 / 10000 : ℝ) ^ 3 / 6))| ≤ (1 / 6) * (70 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((48 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1225 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headC1_c48 : ℂ)).im = 1225 / 10000 := by simp [dp_headC1_c48]
    rw [him]
    have ha0 : |(1443 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 48)| ≤ 1 := hsin_le1
    have e1 : |(48 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 48) - 1443 / 10000 * (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 6 * (125 / 10000) := by
      have hsplit : (48 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 48) - 1443 / 10000 * (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000) * Real.sin (10 * Real.log 48) + 1443 / 10000 * (Real.sin (10 * Real.log 48) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000) * Real.sin (10 * Real.log 48)) (1443 / 10000 * (Real.sin (10 * Real.log 48) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((48 : ℝ) ^ (-1 / 2 : ℝ) - 1443 / 10000)| * |Real.sin (10 * Real.log 48)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(1443 / 10000 : ℝ)| * |Real.sin (10 * Real.log 48) - (1 - 2 * ((-5569 / 10000 : ℝ) / 2 - ((-5569 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 6) * (125 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((48 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headC1_c48 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_headC1_n49_tight : ‖((((49 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_headC1_c49‖ ≤ 1 / 100 := by
  have h7lo := dp_headC1_log7_lo
  have h7hi := dp_headC1_log7_hi
  have h49 := dp_headC1_log49_eq
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx : |(10 : ℝ) * Real.log 49| ≤ 40 := by
    rw [abs_le]; constructor
    · linarith [h7lo, h7hi, h49]
    · linarith [h7lo, h7hi, h49]
  have he_le : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ≤ 1 := by
    rw [abs_le]; constructor
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2 - (-3504 / 10000)| ≤ 45 / 10000 := by
    rw [abs_le]; constructor
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ≤ 2 / 5 := by
    rw [abs_le]; constructor
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
    · linarith [h7lo, h7hi, h49, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 49 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2 = ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 49) ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) hx 6 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 49) ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) hx 6 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) (-3504 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) (-3504 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 ≤ (2 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 ≤ 2 / 10000 := by
    have h0 : (2 / 5 : ℝ) ^ 5 / 100 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 ≤ (2 / 5 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (2 / 5 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 ≤ (2 / 5 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 49) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 140 / 10000 := by
    have ha : |Real.cos ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq, hs_eq]
      · linarith [hs_hi, hs_hi_eq, hs_eq]
    have hb : |(1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (45 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    rw [hs_eq]
    linarith [htri, ha, hb, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 49) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))| ≤ 75 / 10000 := by
    have hpoly : |(-Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2)) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)| := by
      have e : (-Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2)) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [e, abs_neg]
    have h1 : |Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)| ≤ 2 / 10000 + 3 / 2 * (45 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (45 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - (((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) - ((10 : ℝ) * Real.log 49 - 6 * (2 * Real.pi) - Real.pi / 2) ^ 3 / 6) - ((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    rw [hc_eq]
    linarith [hpoly, h1, hrem_s]
  have hsqrt_lo : 7000 / 1000 ≤ Real.sqrt 49 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 49 ≤ 7000 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_eq : (49 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 49)⁻¹ := by
    have hsqrt_eq : Real.sqrt 49 = (49 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 49
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (49 : ℝ) ^ (-1 / 2 : ℝ) = ((49 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (1428 / 10000 : ℝ) ≤ (49 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (7000 / 1000) ≤ 1 / Real.sqrt 49 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (1428 / 10000 : ℝ) ≤ 1 / (7000 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (49 : ℝ) ^ (-1 / 2 : ℝ) ≤ (1430 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 49 ≤ 1 / (7000 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (7000 / 1000) ≤ 1430 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]; constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 49 (by norm_num)
  have him := dp_cpow10_im 49 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 49)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 49)
  have hcenter_re : |(1429 / 10000 : ℝ) * (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)) - 490 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1429 / 10000 : ℝ) * (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1342 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((49 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (490 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headC1_c49 : ℂ)).re = 490 / 10000 := by simp [dp_headC1_c49]
    rw [hre]
    have ha0 : |(1429 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 49)| ≤ 1 := hcos_le1
    have e1 : |(49 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 49) - 1429 / 10000 * (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))| ≤ 1 / 1000 * 1 + 1 / 6 * (75 / 10000) := by
      have hsplit : (49 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 49) - 1429 / 10000 * (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6)) = ((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000) * Real.cos (10 * Real.log 49) + 1429 / 10000 * (Real.cos (10 * Real.log 49) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000) * Real.cos (10 * Real.log 49)) (1429 / 10000 * (Real.cos (10 * Real.log 49) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000)| * |Real.cos (10 * Real.log 49)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(1429 / 10000 : ℝ)| * |Real.cos (10 * Real.log 49) - (-((-3504 / 10000 : ℝ) - (-3504 / 10000 : ℝ) ^ 3 / 6))| ≤ (1 / 6) * (75 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((49 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1342 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headC1_c49 : ℂ)).im = 1342 / 10000 := by simp [dp_headC1_c49]
    rw [him]
    have ha0 : |(1429 / 10000 : ℝ)| ≤ 1 / 6 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 49)| ≤ 1 := hsin_le1
    have e1 : |(49 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 49) - 1429 / 10000 * (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 6 * (140 / 10000) := by
      have hsplit : (49 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 49) - 1429 / 10000 * (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000) * Real.sin (10 * Real.log 49) + 1429 / 10000 * (Real.sin (10 * Real.log 49) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000) * Real.sin (10 * Real.log 49)) (1429 / 10000 * (Real.sin (10 * Real.log 49) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((49 : ℝ) ^ (-1 / 2 : ℝ) - 1429 / 10000)| * |Real.sin (10 * Real.log 49)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(1429 / 10000 : ℝ)| * |Real.sin (10 * Real.log 49) - (1 - 2 * ((-3504 / 10000 : ℝ) / 2 - ((-3504 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 6) * (140 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((49 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headC1_c49 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
