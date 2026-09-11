import Mathlib
import door3_dp_trig
import door3_dp_terms

theorem dp_headA_log5_lo : 16094 / 10000 ≤ Real.log 5 := by
  have h := Real.log_five_gt_d9
  norm_num at h ⊢
  linarith

theorem dp_headA_log5_hi : Real.log 5 ≤ 16095 / 10000 := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith

theorem dp_headA_log2401_eq : Real.log 2401 = 4 * Real.log 7 := by
  have heq : (2401 : ℝ) = 7 * (7 * (7 * 7)) := by norm_num
  have h1 : Real.log (7 * (7 * (7 * 7))) = Real.log 7 + Real.log (7 * (7 * 7)) := Real.log_mul (by norm_num) (by norm_num)
  have h2 : Real.log (7 * (7 * 7)) = Real.log 7 + Real.log (7 * 7) := Real.log_mul (by norm_num) (by norm_num)
  have h3 : Real.log (7 * 7) = Real.log 7 + Real.log 7 := Real.log_mul (by norm_num) (by norm_num)
  rw [heq, h1, h2, h3]
  ring

theorem dp_headA_log2400_eq : Real.log 2400 = 5 * Real.log 2 + (Real.log 3 + 2 * Real.log 5) := by
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

theorem dp_headA_delta_lo : (1 : ℝ) / 2401 ≤ Real.log (2401 / 2400) := by
  have hpos : (0 : ℝ) < 2400 / 2401 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (2401 / 2400) = -Real.log (2400 / 2401) := by
    have e : (2401 / 2400 : ℝ) = (2400 / 2401 : ℝ)⁻¹ := by norm_num
    rw [e, Real.log_inv]
  have heq : (2400 : ℝ) / 2401 - 1 = -(1 / 2401) := by norm_num
  rw [heq] at hub
  linarith [hub, hinv]

theorem dp_headA_delta_hi : Real.log (2401 / 2400) ≤ (1 : ℝ) / 2400 := by
  have hpos : (0 : ℝ) < 2401 / 2400 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have heq : (2401 : ℝ) / 2400 - 1 = 1 / 2400 := by norm_num
  rw [heq] at hub
  exact hub

theorem dp_headA_log7_lo : 19458 / 10000 ≤ Real.log 7 := by
  have h2lo := dp_log2_lo
  have h3lo := dp_log3_lo
  have h5lo := dp_headA_log5_lo
  have hdlo := dp_headA_delta_lo
  have h2401 := dp_headA_log2401_eq
  have h2400 := dp_headA_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 := Real.log_div (by norm_num) (by norm_num)
  linarith [h2lo, h3lo, h5lo, hdlo, h2401, h2400, hdiv]

theorem dp_headA_log7_hi : Real.log 7 ≤ 19461 / 10000 := by
  have h2hi := dp_log2_hi
  have h3hi := dp_log3_hi
  have h5hi := dp_headA_log5_hi
  have hdhi := dp_headA_delta_hi
  have h2401 := dp_headA_log2401_eq
  have h2400 := dp_headA_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 := Real.log_div (by norm_num) (by norm_num)
  linarith [h2hi, h3hi, h5hi, hdhi, h2401, h2400, hdiv]

noncomputable def dp_headA_c5 : ℂ := ⟨(-4142 / 10000 : ℝ), (-1685 / 10000 : ℝ)⟩
noncomputable def dp_headA_c6 : ℂ := ⟨(2434 / 10000 : ℝ), (-3277 / 10000 : ℝ)⟩
noncomputable def dp_headA_c7 : ℂ := ⟨(3099 / 10000 : ℝ), (2164 / 10000 : ℝ)⟩
noncomputable def dp_headA_c8 : ℂ := ⟨(-1292 / 10000 : ℝ), (3291 / 10000 : ℝ)⟩

theorem dp_headA_6_tight : ‖(((6 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headA_c6‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    have e : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num)]
  have hx6 : |(10 : ℝ) * Real.log 6| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6]
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6]
  have he_le : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2 - 6395 / 10000| ≤ 15 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ≤ 65 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog6, hpi_lo, hpi_hi]
  have hrdef6 : (10 : ℝ) * Real.log 6 - 3 * (2 * Real.pi) = (10 : ℝ) * Real.log 6 - ((3 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef6 : (10 : ℝ) * Real.log 6 - 11 * Real.pi / 2 = ((10 : ℝ) * Real.log 6 - 3 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 6) ((10 : ℝ) * Real.log 6 - 3 * (2 * Real.pi)) ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) hx6 3 hrdef6 hedef6 he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 6) ((10 : ℝ) * Real.log 6 - 3 * (2 * Real.pi)) ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) hx6 3 hrdef6 hedef6 he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) (6395 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) (6395 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 ≤ (65 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 100 ≤ 12 / 10000 := by
    have h0 : (65 / 100 : ℝ) ^ 5 / 100 ≤ 12 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 100 ≤ (65 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 800 ≤ 2 / 10000 := by
    have h0 : (65 / 100 : ℝ) ^ 5 / 800 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 800 ≤ (65 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 6) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ 50 / 10000 := by
    have hpoly : |(-Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2)) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| := by
      have e : (-Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2)) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [e, abs_neg]
    have h1 : |Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 + 3 * (15 / 10000) := by
      have ha : |Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 800 := by
        rw [abs_le]
        constructor
        · linarith [hs_lo, hs_lo_eq, hs_eq]
        · linarith [hs_hi, hs_hi_eq, hs_eq]
      have hb : |(1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (15 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
        linarith [hlip_c, hmul]
      have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
      have heq : Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_c]
    rw [hs_eq]
    linarith [hpoly, h1, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)| ≤ 40 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)| ≤ 12 / 10000 + 3 / 2 * (15 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 6 - 11 * Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (15 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - (((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) - ((10 : ℝ) * Real.log 6 - 11 * Real.pi / 2) ^ 3 / 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    rw [hc_eq]
    linarith [h1, hrem_s]
  have hsqrt_lo : 2449 / 1000 ≤ Real.sqrt 6 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrt_hi : Real.sqrt 6 ≤ 2450 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hamp_eq : (6 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 6)⁻¹ := by
    have hsqrt_eq : Real.sqrt 6 = (6 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 6
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (6 : ℝ) ^ (-1 / 2 : ℝ) = ((6 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (4081 / 10000 : ℝ) ≤ (6 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (2450 / 1000) ≤ 1 / Real.sqrt 6 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (4081 / 10000 : ℝ) ≤ 1 / (2450 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (6 : ℝ) ^ (-1 / 2 : ℝ) ≤ (4083 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 6 ≤ 1 / (2449 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (2449 / 1000) ≤ 4083 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 6 (by norm_num)
  have him := dp_cpow10_im 6 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 6)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 6)
  have hcenter_re : |(4082 / 10000 : ℝ) * ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6) - 2434 / 10000| ≤ 10 / 10000 := by norm_num
  have hcenter_im : |(4082 / 10000 : ℝ) * (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) - (-3277 / 10000)| ≤ 10 / 10000 := by norm_num
  have hre_bound : |((((((6 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (2434 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headA_c6 : ℂ)).re = 2434 / 10000 := by simp [dp_headA_c6]
    rw [hre]
    have ha0 : |(4082 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 6)| ≤ 1 := hcos_le1
    have e1 : |(6 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 6) - 4082 / 10000 * ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 / 2 * (40 / 10000) := by
      have hsplit : (6 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 6) - 4082 / 10000 * ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6) = ((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000) * Real.cos (10 * Real.log 6) + 4082 / 10000 * (Real.cos (10 * Real.log 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000) * Real.cos (10 * Real.log 6)) (4082 / 10000 * (Real.cos (10 * Real.log 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000)| * |Real.cos (10 * Real.log 6)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(4082 / 10000 : ℝ)| * |Real.cos (10 * Real.log 6) - ((6395 / 10000 : ℝ) - (6395 / 10000 : ℝ) ^ 3 / 6)| ≤ (1 / 2) * (40 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((6 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-3277 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headA_c6 : ℂ)).im = -3277 / 10000 := by simp [dp_headA_c6]
    rw [him]
    have ha0 : |(4082 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 6)| ≤ 1 := hsin_le1
    have e1 : |(6 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 6) - 4082 / 10000 * (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 1000 * 1 + 1 / 2 * (50 / 10000) := by
      have hsplit : (6 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 6) - 4082 / 10000 * (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) = ((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000) * Real.sin (10 * Real.log 6) + 4082 / 10000 * (Real.sin (10 * Real.log 6) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000) * Real.sin (10 * Real.log 6)) (4082 / 10000 * (Real.sin (10 * Real.log 6) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((6 : ℝ) ^ (-1 / 2 : ℝ) - 4082 / 10000)| * |Real.sin (10 * Real.log 6)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(4082 / 10000 : ℝ)| * |Real.sin (10 * Real.log 6) - (-(1 - 2 * ((6395 / 10000 : ℝ) / 2 - ((6395 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ (1 / 2) * (50 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((6 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headA_c6 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headA_7_tight : ‖(((7 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headA_c7‖ ≤ 1 / 100 := by
  have hlog_lo := dp_headA_log7_lo
  have hlog_hi := dp_headA_log7_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx7 : |(10 : ℝ) * Real.log 7| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi]
    · linarith [hlog_lo, hlog_hi]
  have hr_le : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi) - 6100 / 10000| ≤ 15 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hr_abs : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ≤ 62 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hrdef7 : (10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi) = (10 : ℝ) * Real.log 7 - ((3 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 7) hx7 3 ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) hrdef7 hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 7) hx7 3 ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) hrdef7 hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) (6100 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) (6100 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow_s : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 ≤ (62 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hr_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 100 ≤ 10 / 10000 := by
    have h0 : (62 / 100 : ℝ) ^ 5 / 100 ≤ 10 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 100 ≤ (62 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow_s (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 800 ≤ 2 / 10000 := by
    have h0 : (62 / 100 : ℝ) ^ 5 / 800 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 800 ≤ (62 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow_s (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 7) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)| ≤ 35 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 7) - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 100 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq]
      · linarith [hs_hi, hs_hi_eq]
    have h2 : |((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6 - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (15 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith [hlip_s, hmul]
    have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 7) - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6)) ((((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6))
    have heq : Real.sin ((10 : ℝ) * Real.log 7) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 7) - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) ^ 3 / 6) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_s]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 7) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 50 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 7) - (1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hc_lo, hc_lo_eq]
      · linarith [hc_hi, hc_hi_eq]
    have h2 : |(1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (15 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 7) - (1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 7) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 7) - (1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 7 - 3 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_c]
  have hsqrt_lo : 2645 / 1000 ≤ Real.sqrt 7 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrt_hi : Real.sqrt 7 ≤ 2646 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hamp_eq : (7 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 7)⁻¹ := by
    have hsqrt_eq : Real.sqrt 7 = (7 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 7
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (7 : ℝ) ^ (-1 / 2 : ℝ) = ((7 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (3779 / 10000 : ℝ) ≤ (7 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (2646 / 1000) ≤ 1 / Real.sqrt 7 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (3779 / 10000 : ℝ) ≤ 1 / (2646 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (7 : ℝ) ^ (-1 / 2 : ℝ) ≤ (3781 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 7 ≤ 1 / (2645 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (2645 / 1000) ≤ 3781 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 7 (by norm_num)
  have him := dp_cpow10_im 7 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 7)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 7)
  have hcenter_re : |(3780 / 10000 : ℝ) * (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 3099 / 10000| ≤ 10 / 10000 := by norm_num
  have hcenter_im : |(3780 / 10000 : ℝ) * ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6) - 2164 / 10000| ≤ 10 / 10000 := by norm_num
  have hre_bound : |((((((7 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (3099 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headA_c7 : ℂ)).re = 3099 / 10000 := by simp [dp_headA_c7]
    rw [hre]
    have ha0 : |(3780 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 7)| ≤ 1 := hcos_le1
    have e1 : |(7 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 7) - 3780 / 10000 * (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 2 * (50 / 10000) := by
      have hsplit : (7 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 7) - 3780 / 10000 * (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000) * Real.cos (10 * Real.log 7) + 3780 / 10000 * (Real.cos (10 * Real.log 7) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000) * Real.cos (10 * Real.log 7)) (3780 / 10000 * (Real.cos (10 * Real.log 7) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000)| * |Real.cos (10 * Real.log 7)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(3780 / 10000 : ℝ)| * |Real.cos (10 * Real.log 7) - (1 - 2 * ((6100 / 10000 : ℝ) / 2 - ((6100 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 2) * (50 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((7 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (2164 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headA_c7 : ℂ)).im = 2164 / 10000 := by simp [dp_headA_c7]
    rw [him]
    have ha0 : |(3780 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 7)| ≤ 1 := hsin_le1
    have e1 : |(7 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 7) - 3780 / 10000 * ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 / 2 * (35 / 10000) := by
      have hsplit : (7 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 7) - 3780 / 10000 * ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6) = ((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000) * Real.sin (10 * Real.log 7) + 3780 / 10000 * (Real.sin (10 * Real.log 7) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000) * Real.sin (10 * Real.log 7)) (3780 / 10000 * (Real.sin (10 * Real.log 7) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((7 : ℝ) ^ (-1 / 2 : ℝ) - 3780 / 10000)| * |Real.sin (10 * Real.log 7)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(3780 / 10000 : ℝ)| * |Real.sin (10 * Real.log 7) - ((6100 / 10000 : ℝ) - (6100 / 10000 : ℝ) ^ 3 / 6)| ≤ (1 / 2) * (35 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((7 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headA_c7 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headA_8_tight : ‖(((8 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headA_c8‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    have e : (8 : ℝ) = 2 * (2 * 2) := by norm_num
    have h1 : Real.log (2 * (2 * 2)) = Real.log 2 + Real.log (2 * 2) := Real.log_mul (by norm_num) (by norm_num)
    have h2 : Real.log (2 * 2) = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
    rw [e, h1, h2]
    ring
  have hx8 : |(10 : ℝ) * Real.log 8| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog8]
    · linarith [hlog2_lo, hlog2_hi, hlog8]
  have he_le : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2 - 3744 / 10000| ≤ 20 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ≤ 38 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
    · linarith [hlog2_lo, hlog2_hi, hlog8, hpi_lo, hpi_hi]
  have hrdef8 : (10 : ℝ) * Real.log 8 - 3 * (2 * Real.pi) = (10 : ℝ) * Real.log 8 - ((3 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef8 : (10 : ℝ) * Real.log 8 - 13 * Real.pi / 2 = ((10 : ℝ) * Real.log 8 - 3 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 8) ((10 : ℝ) * Real.log 8 - 3 * (2 * Real.pi)) ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) hx8 3 hrdef8 hedef8 he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 8) ((10 : ℝ) * Real.log 8 - 3 * (2 * Real.pi)) ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) hx8 3 hrdef8 hedef8 he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) (3744 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) (3744 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 ≤ (38 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 10000 := by
    have h0 : (38 / 100 : ℝ) ^ 5 / 100 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 100 ≤ (38 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (38 / 100 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 800 ≤ (38 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 8) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 70 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 10000 + 3 * (20 / 10000) := by
      have ha : |Real.cos ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 800 := by
        rw [abs_le]
        constructor
        · linarith [hs_lo, hs_lo_eq, hs_eq]
        · linarith [hs_hi, hs_hi_eq, hs_eq]
      have hb : |(1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (20 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
        linarith [hlip_c, hmul]
      have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
      have heq : Real.cos ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_c]
    rw [hs_eq]
    linarith [h1, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 8) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))| ≤ 40 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 10000 + 3 / 2 * (20 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 8 - 13 * Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (20 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - (((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) ^ 3 / 6) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    have hneg : |(-Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2)) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)| := by
      have e : (-Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2)) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 8 - 13 * Real.pi / 2) - ((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [e, abs_neg]
    rw [hc_eq]
    linarith [hneg, h1, hrem_s]
  have hsqrt_lo : 2828 / 1000 ≤ Real.sqrt 8 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrt_hi : Real.sqrt 8 ≤ 2829 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hamp_eq : (8 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 8)⁻¹ := by
    have hsqrt_eq : Real.sqrt 8 = (8 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 8
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (8 : ℝ) ^ (-1 / 2 : ℝ) = ((8 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (3534 / 10000 : ℝ) ≤ (8 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (2829 / 1000) ≤ 1 / Real.sqrt 8 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (3534 / 10000 : ℝ) ≤ 1 / (2829 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (8 : ℝ) ^ (-1 / 2 : ℝ) ≤ (3536 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 8 ≤ 1 / (2828 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (2828 / 1000) ≤ 3536 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 8 (by norm_num)
  have him := dp_cpow10_im 8 (by norm_num)
  have hcenter_re : |(3535 / 10000 : ℝ) * (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)) - (-1292 / 10000)| ≤ 10 / 10000 := by norm_num
  have hcenter_im : |(3535 / 10000 : ℝ) * (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 3291 / 10000| ≤ 10 / 10000 := by norm_num
  have hre_bound : |((((((8 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1292 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headA_c8 : ℂ)).re = -1292 / 10000 := by simp [dp_headA_c8]
    rw [hre]
    have ha0 : |(3535 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 8)| ≤ 1 := Real.abs_cos_le_one _
    have e1 : |(8 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 8) - 3535 / 10000 * (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))| ≤ 1 / 1000 * 1 + 1 / 2 * (40 / 10000) := by
      have hsplit : (8 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 8) - 3535 / 10000 * (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6)) = ((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000) * Real.cos (10 * Real.log 8) + 3535 / 10000 * (Real.cos (10 * Real.log 8) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000) * Real.cos (10 * Real.log 8)) (3535 / 10000 * (Real.cos (10 * Real.log 8) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000)| * |Real.cos (10 * Real.log 8)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(3535 / 10000 : ℝ)| * |Real.cos (10 * Real.log 8) - (-((3744 / 10000 : ℝ) - (3744 / 10000 : ℝ) ^ 3 / 6))| ≤ (1 / 2) * (40 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((8 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (3291 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headA_c8 : ℂ)).im = 3291 / 10000 := by simp [dp_headA_c8]
    rw [him]
    have ha0 : |(3535 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 8)| ≤ 1 := Real.abs_sin_le_one _
    have e1 : |(8 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 8) - 3535 / 10000 * (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 2 * (70 / 10000) := by
      have hsplit : (8 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 8) - 3535 / 10000 * (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000) * Real.sin (10 * Real.log 8) + 3535 / 10000 * (Real.sin (10 * Real.log 8) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000) * Real.sin (10 * Real.log 8)) (3535 / 10000 * (Real.sin (10 * Real.log 8) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((8 : ℝ) ^ (-1 / 2 : ℝ) - 3535 / 10000)| * |Real.sin (10 * Real.log 8)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(3535 / 10000 : ℝ)| * |Real.sin (10 * Real.log 8) - (1 - 2 * ((3744 / 10000 : ℝ) / 2 - ((3744 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ (1 / 2) * (70 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((8 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headA_c8 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headA_5_tight : ‖(((5 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headA_c5‖ ≤ 1 / 20 := by
  have hlog5_lo := dp_headA_log5_lo
  have hlog5_hi := dp_headA_log5_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hxth : |(5 : ℝ) * Real.log 5| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog5_lo, hlog5_hi]
    · linarith [hlog5_lo, hlog5_hi]
  have he_le : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
  have he_close : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2 - 1934 / 10000| ≤ 10 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
  have he_abs : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ≤ 20 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
    · linarith [hlog5_lo, hlog5_hi, hpi_lo, hpi_hi]
  have hrdef : (5 : ℝ) * Real.log 5 - 1 * (2 * Real.pi) = (5 : ℝ) * Real.log 5 - ((1 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (5 : ℝ) * Real.log 5 - 5 * Real.pi / 2 = ((5 : ℝ) * Real.log 5 - 1 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((5 : ℝ) * Real.log 5) ((5 : ℝ) * Real.log 5 - 1 * (2 * Real.pi)) ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) hxth 1 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((5 : ℝ) * Real.log 5) ((5 : ℝ) * Real.log 5 - 1 * (2 * Real.pi)) ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) hxth 1 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) (1934 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) (1934 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 ≤ (20 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 10000 := by
    have h0 : (20 / 100 : ℝ) ^ 5 / 100 ≤ 1 / 10000 := by norm_num
    have hle : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 100 ≤ (20 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (20 / 100 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 800 ≤ (20 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_half_close : |Real.sin ((5 : ℝ) * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 40 / 10000 := by
    have h1 : |Real.cos ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 10000 + 3 * (10 / 10000) := by
      have ha : |Real.cos ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 800 := by
        rw [abs_le]
        constructor
        · linarith [hs_lo, hs_lo_eq, hs_eq]
        · linarith [hs_hi, hs_hi_eq, hs_eq]
      have hb : |(1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (10 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
        linarith [hlip_c, hmul]
      have htri := abs_add_le (Real.cos ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
      have heq : Real.cos ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2 - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_c]
    rw [hs_eq]
    linarith [h1, hrem_c]
  have hcos_half_close : |Real.cos ((5 : ℝ) * Real.log 5) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| ≤ 30 / 10000 := by
    have h1 : |Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 10000 + 3 / 2 * (10 / 10000) := by
      have ha : |Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6)| ≤ |(5 : ℝ) * Real.log 5 - 5 * Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (10 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6)) ((((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - (((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6)) + ((((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) ^ 3 / 6) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    have hneg : |(-Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2)) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| = |Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)| := by
      have e : (-Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2)) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) = -(Real.sin ((5 : ℝ) * Real.log 5 - 5 * Real.pi / 2) - ((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [e, abs_neg]
    rw [hc_eq]
    linarith [hneg, h1, hrem_s]
  have hsqrt_lo : 2236 / 1000 ≤ Real.sqrt 5 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrt_hi : Real.sqrt 5 ≤ 2237 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hamp_eq : (5 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 5)⁻¹ := by
    have hsqrt_eq : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 5
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (5 : ℝ) ^ (-1 / 2 : ℝ) = ((5 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (4471 / 10000 : ℝ) ≤ (5 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (2237 / 1000) ≤ 1 / Real.sqrt 5 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (4471 / 10000 : ℝ) ≤ 1 / (2237 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (5 : ℝ) ^ (-1 / 2 : ℝ) ≤ (4473 / 10000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 5 ≤ 1 / (2236 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (2236 / 1000) ≤ 4473 / 10000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 5 (by norm_num)
  have him := dp_cpow10_im 5 (by norm_num)
  have hlog5_double : (10 : ℝ) * Real.log 5 = 2 * ((5 : ℝ) * Real.log 5) := by ring
  have hsin2 : Real.sin (10 * Real.log 5) = 2 * Real.sin (5 * Real.log 5) * Real.cos (5 * Real.log 5) := by
    have h := Real.sin_two_mul (5 * Real.log 5)
    rw [hlog5_double]
    linarith [h]
  have hcos2 : Real.cos (10 * Real.log 5) = Real.cos (5 * Real.log 5) ^ 2 - Real.sin (5 * Real.log 5) ^ 2 := by
    have h := Real.cos_two_mul (5 * Real.log 5)
    have heq : Real.cos (2 * (5 * Real.log 5)) = Real.cos (5 * Real.log 5) ^ 2 - Real.sin (5 * Real.log 5) ^ 2 := by
      rw [Real.cos_two_mul']
    rw [hlog5_double]
    linarith [h, heq]
  have hC0le : |(1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 := by norm_num
  have hS0le : |((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 := by norm_num
  have hsin_half_le1 : |Real.sin (5 * Real.log 5)| ≤ 1 := Real.abs_sin_le_one _
  have hcos_half_le1 : |Real.cos (5 * Real.log 5)| ≤ 1 := Real.abs_cos_le_one _
  have hsin_full_close : |Real.sin (10 * Real.log 5) - 2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| ≤ 160 / 10000 := by
    rw [hsin2]
    have e1 : |Real.sin (5 * Real.log 5) * Real.cos (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| ≤ 1 * (30 / 10000) + 1 * (40 / 10000) := by
      have hsplit : Real.sin (5 * Real.log 5) * Real.cos (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) = (Real.sin (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) * Real.cos (5 * Real.log 5) + (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (Real.cos (5 * Real.log 5) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))) := by ring
      rw [hsplit]
      have htri := abs_add_le ((Real.sin (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) * Real.cos (5 * Real.log 5)) ((1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (Real.cos (5 * Real.log 5) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |Real.sin (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| * |Real.cos (5 * Real.log 5)| ≤ (40 / 10000) * 1 := by
        exact mul_le_mul hsin_half_close hcos_half_le1 (abs_nonneg _) (by norm_num)
      have m2 : |(1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| * |Real.cos (5 * Real.log 5) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| ≤ 1 * (30 / 10000) := by
        exact mul_le_mul hC0le hcos_half_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    have hmul2 : |2 * (Real.sin (5 * Real.log 5) * Real.cos (5 * Real.log 5)) - 2 * ((1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)))| = 2 * |Real.sin (5 * Real.log 5) * Real.cos (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| := by
      rw [← mul_sub, abs_mul]
      norm_num
    linarith [hmul2, e1]
  have hcos_full_close : |Real.cos (10 * Real.log 5) - ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)| ≤ 140 / 10000 := by
    rw [hcos2]
    have hsq1 : |Real.cos (5 * Real.log 5) ^ 2 - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2| ≤ (30 / 10000) * 2 := by
      have heq : Real.cos (5 * Real.log 5) ^ 2 - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 = (Real.cos (5 * Real.log 5) - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))) * (Real.cos (5 * Real.log 5) + (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))) := by ring
      rw [heq, abs_mul]
      have hsum : |Real.cos (5 * Real.log 5) + (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))| ≤ 2 := by
        have h := abs_add_le (Real.cos (5 * Real.log 5)) (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))
        linarith [h, hcos_half_le1, hS0le]
      have hm := mul_le_mul hcos_half_close hsum (abs_nonneg _) (by norm_num)
      linarith [hm]
    have hsq2 : |Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2| ≤ (40 / 10000) * 2 := by
      have heq : Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2 = (Real.sin (5 * Real.log 5) - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) * (Real.sin (5 * Real.log 5) + (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [heq, abs_mul]
      have hsum : |Real.sin (5 * Real.log 5) + (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 := by
        have h := abs_add_le (Real.sin (5 * Real.log 5)) (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)
        linarith [h, hsin_half_le1, hC0le]
      have hm := mul_le_mul hsin_half_close hsum (abs_nonneg _) (by norm_num)
      linarith [hm]
    have htri := abs_add_le (Real.cos (5 * Real.log 5) ^ 2 - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2) (-(Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2))
    have heq2 : (Real.cos (5 * Real.log 5) ^ 2 - Real.sin (5 * Real.log 5) ^ 2) - ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2) = (Real.cos (5 * Real.log 5) ^ 2 - (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2) + (-(Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)) := by ring
    have habsneg : |(-(Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2))| = |Real.sin (5 * Real.log 5) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2| := abs_neg _
    rw [← heq2, habsneg] at htri
    linarith [htri, hsq1, hsq2]
  have hcenter_re : |(4472 / 10000 : ℝ) * ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2) - (-4142 / 10000)| ≤ 10 / 10000 := by norm_num
  have hcenter_im : |(4472 / 10000 : ℝ) * (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))) - (-1685 / 10000)| ≤ 10 / 10000 := by norm_num
  have hre_bound : |((((((5 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-4142 / 10000) : ℝ)| ≤ 1 / 40 := by
    have hCre : ((dp_headA_c5 : ℂ)).re = -4142 / 10000 := by simp [dp_headA_c5]
    rw [hre]
    have ha0 : |(4472 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 5)| ≤ 1 := Real.abs_cos_le_one _
    have e1 : |(5 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 5) - 4472 / 10000 * ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)| ≤ 1 / 1000 * 1 + 1 / 2 * (140 / 10000) := by
      have hsplit : (5 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 5) - 4472 / 10000 * ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2) = ((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000) * Real.cos (10 * Real.log 5) + 4472 / 10000 * (Real.cos (10 * Real.log 5) - ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000) * Real.cos (10 * Real.log 5)) (4472 / 10000 * (Real.cos (10 * Real.log 5) - ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000)| * |Real.cos (10 * Real.log 5)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(4472 / 10000 : ℝ)| * |Real.cos (10 * Real.log 5) - ((-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)) ^ 2 - (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) ^ 2)| ≤ (1 / 2) * (140 / 10000) := by
        exact mul_le_mul ha0 hcos_full_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((5 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1685 / 10000) : ℝ)| ≤ 1 / 40 := by
    have hCim : ((dp_headA_c5 : ℂ)).im = -1685 / 10000 := by simp [dp_headA_c5]
    rw [him]
    have ha0 : |(4472 / 10000 : ℝ)| ≤ 1 / 2 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 5)| ≤ 1 := Real.abs_sin_le_one _
    have e1 : |(5 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 5) - 4472 / 10000 * (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)))| ≤ 1 / 1000 * 1 + 1 / 2 * (160 / 10000) := by
      have hsplit : (5 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 5) - 4472 / 10000 * (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6))) = ((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000) * Real.sin (10 * Real.log 5) + 4472 / 10000 * (Real.sin (10 * Real.log 5) - (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000) * Real.sin (10 * Real.log 5)) (4472 / 10000 * (Real.sin (10 * Real.log 5) - (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((5 : ℝ) ^ (-1 / 2 : ℝ) - 4472 / 10000)| * |Real.sin (10 * Real.log 5)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(4472 / 10000 : ℝ)| * |Real.sin (10 * Real.log 5) - (2 * (1 - 2 * ((1934 / 10000 : ℝ) / 2 - ((1934 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) * (-((1934 / 10000 : ℝ) - (1934 / 10000 : ℝ) ^ 3 / 6)))| ≤ (1 / 2) * (160 / 10000) := by
        exact mul_le_mul ha0 hsin_full_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((5 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headA_c5 (1 / 40) (1 / 40) hre_bound him_bound
  linarith [h]
