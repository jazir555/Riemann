import Mathlib
import door3_dp_trig
import door3_dp_terms

theorem headB_log1p_hi (x : ℝ) (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  have heq : (1 + x) - 1 = x := by ring
  linarith

theorem headB_log1p_lo (x : ℝ) (hx : -1 < x) : x / (1 + x) ≤ Real.log (1 + x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hinv_pos : (0 : ℝ) < ((1 + x)⁻¹) := inv_pos.mpr hpos
  have hup := Real.log_le_sub_one_of_pos hinv_pos
  have hlog_inv : Real.log ((1 + x)⁻¹) = -Real.log (1 + x) := Real.log_inv _
  have heq : ((1 + x)⁻¹) - 1 = -x / (1 + x) := by field_simp; ring
  linarith

theorem headB_amp_of_sqrt_bounds (n lo hi : ℝ) (hn : (0 : ℝ) < n) (hlo_pos : (0 : ℝ) < lo) (hs_lo : lo ≤ Real.sqrt n) (hs_hi : Real.sqrt n ≤ hi) : (1 / hi ≤ n ^ (-1 / 2 : ℝ)) ∧ (n ^ (-1 / 2 : ℝ) ≤ 1 / lo) := by
  have hsqrt_eq : Real.sqrt n = n ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
  have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  have hamp_eq : n ^ (-1 / 2 : ℝ) = (Real.sqrt n)⁻¹ := by rw [e, Real.rpow_neg (le_of_lt hn), hsqrt_eq]
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn
  constructor
  · rw [hamp_eq, inv_eq_one_div]
    exact one_div_le_one_div_of_le hsqrt_pos hs_hi
  · rw [hamp_eq, inv_eq_one_div]
    exact one_div_le_one_div_of_le hlo_pos hs_lo

theorem headB_mul_close (a a0 b b0 ea eb : ℝ) (hea : (0 : ℝ) ≤ ea) (ha : |a - a0| ≤ ea) (hb : |b - b0| ≤ eb) (ha0 : |a0| ≤ 1) (hb1 : |b| ≤ 1) : |a * b - a0 * b0| ≤ ea * 1 + 1 * eb := by
  have hsplit : a * b - a0 * b0 = (a - a0) * b + a0 * (b - b0) := by ring
  rw [hsplit]
  have htri := abs_add_le ((a - a0) * b) (a0 * (b - b0))
  rw [abs_mul, abs_mul] at htri
  have m1 : |a - a0| * |b| ≤ ea * 1 := mul_le_mul ha hb1 (abs_nonneg _) hea
  have m2 : |a0| * |b - b0| ≤ 1 * eb := mul_le_mul ha0 hb (abs_nonneg _) (by norm_num)
  linarith

noncomputable def dp_headB_c25 : ℂ := ⟨(1432 / 10000 : ℝ), (1396 / 10000 : ℝ)⟩
noncomputable def dp_headB_c26 : ℂ := ⟨(774 / 10000 : ℝ), (1802 / 10000 : ℝ)⟩
noncomputable def dp_headB_c27 : ℂ := ⟨(55 / 10000 : ℝ), (1924 / 10000 : ℝ)⟩
noncomputable def dp_headB_c28 : ℂ := ⟨(-622 / 10000 : ℝ), (1785 / 10000 : ℝ)⟩
noncomputable def dp_headB_c29 : ℂ := ⟨(-1177 / 10000 : ℝ), (1437 / 10000 : ℝ)⟩
noncomputable def dp_headB_c30 : ℂ := ⟨(-1561 / 10000 : ℝ), (947 / 10000 : ℝ)⟩
noncomputable def dp_headB_c31 : ℂ := ⟨(-1754 / 10000 : ℝ), (388 / 10000 : ℝ)⟩
noncomputable def dp_headB_c32 : ℂ := ⟨(-1759 / 10000 : ℝ), (-176 / 10000 : ℝ)⟩
noncomputable def dp_headB_c33 : ℂ := ⟨(-1598 / 10000 : ℝ), (-690 / 10000 : ℝ)⟩
noncomputable def dp_headB_c34 : ℂ := ⟨(-1305 / 10000 : ℝ), (-1113 / 10000 : ℝ)⟩
noncomputable def dp_headB_c35 : ℂ := ⟨(-919 / 10000 : ℝ), (-1419 / 10000 : ℝ)⟩
noncomputable def dp_headB_c36 : ℂ := ⟨(-482 / 10000 : ℝ), (-1596 / 10000 : ℝ)⟩
noncomputable def dp_headB_c37 : ℂ := ⟨(-31 / 10000 : ℝ), (-1644 / 10000 : ℝ)⟩
noncomputable def dp_headB_c38 : ℂ := ⟨(397 / 10000 : ℝ), (-1573 / 10000 : ℝ)⟩
noncomputable def dp_headB_c39 : ℂ := ⟨(778 / 10000 : ℝ), (-1400 / 10000 : ℝ)⟩
noncomputable def dp_headB_c40 : ℂ := ⟨(1090 / 10000 : ℝ), (-1146 / 10000 : ℝ)⟩
noncomputable def dp_headB_c41 : ℂ := ⟨(1320 / 10000 : ℝ), (-834 / 10000 : ℝ)⟩
noncomputable def dp_headB_c42 : ℂ := ⟨(1464 / 10000 : ℝ), (-489 / 10000 : ℝ)⟩
noncomputable def dp_headB_c43 : ℂ := ⟨(1519 / 10000 : ℝ), (-133 / 10000 : ℝ)⟩
noncomputable def dp_headB_c44 : ℂ := ⟨(1492 / 10000 : ℝ), (215 / 10000 : ℝ)⟩

theorem dp_headB_n25_tight : ‖(((25 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c25‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt25 : Real.sqrt (25 : ℝ) = 5 := by have h25 : (25 : ℝ) = 5 ^ 2 := by norm_num; rw [h25]; rw [Real.sqrt_sq (by norm_num)]
  have hamp25 : (25 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 5 := by have hsqrt_eq : Real.sqrt (25 : ℝ) = (25 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 25; have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring; have hrw : (25 : ℝ) ^ (-1 / 2 : ℝ) = (((25 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by rw [e]; exact Real.rpow_neg (by norm_num) _; rw [hrw, ← hsqrt_eq, hsqrt25]; norm_num
  have hlogm : Real.log (15552 : ℝ) = 6 * Real.log 2 + 5 * Real.log 3 := by have h1 : (15552 : ℝ) = 2 ^ 6 * 3 ^ 5 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (25 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (15552 : ℝ) := by norm_num
  have hratio_eq : (25 : ℝ) ^ 3 / 15552 = 1 + 73 / 15552 := by norm_num
  have hlog_ratio_hi : Real.log ((25 : ℝ) ^ 3 / 15552) ≤ 73 / 15552 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (73 / 15552) / (1 + 73 / 15552) ≤ Real.log ((25 : ℝ) ^ 3 / 15552) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((25 : ℝ) ^ 3) = 3 * Real.log 25 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((25 : ℝ) ^ 3 / 15552) = Real.log ((25 : ℝ) ^ 3) - Real.log 15552 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 25| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have hr_le : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi) - 7728 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 25 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 25) hx 5 ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 25) hx 5 ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) (7728 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) (7728 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [hr_le])
  have hrem_s : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.sin ((10 : ℝ) * Real.log 25) - (((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
  have hb_s : |(((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) ^ 3 / 6) - ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 25) - ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_s hb_s (by linarith [hrem_s])
  have ha_c : |Real.cos ((10 : ℝ) * Real.log 25) - (1 - 2 * (((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
  have hb_c : |(1 - 2 * (((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 25 - 5 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 25) - (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_c hb_c (by linarith [hrem_c])
  have hre := dp_cpow10_re 25 (by norm_num)
  have him := dp_cpow10_im 25 (by norm_num)
  have hcenter_re : |(1 / 5 : ℝ) * (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1432 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1 / 5 : ℝ) * ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6) - 1396 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((25 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1432 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c25 : ℂ)).re = 1432 / 10000 := by simp [dp_headB_c25]
    rw [hre, hamp25]
    have e1 : |(1 / 5 : ℝ) * Real.cos (10 * Real.log 25) - 1 / 5 * (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 5 * (1 / 800 + 3 * (50 / 10000)) := by have hsplit : (1 / 5 : ℝ) * Real.cos (10 * Real.log 25) - 1 / 5 * (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = 1 / 5 * (Real.cos (10 * Real.log 25) - (1 - 2 * ((7728 / 10000 : ℝ) / 2 - ((7728 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [hsplit, abs_mul]; have hhalf : |(1 / 5 : ℝ)| = 1 / 5 := by norm_num; rw [hhalf]; exact mul_le_mul_of_nonneg_left hcos_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((25 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1396 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c25 : ℂ)).im = 1396 / 10000 := by simp [dp_headB_c25]
    rw [him, hamp25]
    have e1 : |(1 / 5 : ℝ) * Real.sin (10 * Real.log 25) - 1 / 5 * ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 5 * (1 / 100 + 3 / 2 * (50 / 10000)) := by have hsplit : (1 / 5 : ℝ) * Real.sin (10 * Real.log 25) - 1 / 5 * ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6) = 1 / 5 * (Real.sin (10 * Real.log 25) - ((7728 / 10000 : ℝ) - (7728 / 10000 : ℝ) ^ 3 / 6)) := by ring; rw [hsplit, abs_mul]; have hhalf : |(1 / 5 : ℝ)| = 1 / 5 := by norm_num; rw [hhalf]; exact mul_le_mul_of_nonneg_left hsin_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((25 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c25 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n26_tight : ‖(((26 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c26‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5099 / 1000 : ℝ) ≤ Real.sqrt 26 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 26 ≤ (5100 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 26 (5099 / 1000) (5100 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(26 : ℝ) ^ (-1 / 2 : ℝ) - 1961 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (17496 : ℝ) = 3 * Real.log 2 + 7 * Real.log 3 := by have h1 : (17496 : ℝ) = 2 ^ 3 * 3 ^ 7 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (26 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (17496 : ℝ) := by norm_num
  have hratio_eq : (26 : ℝ) ^ 3 / 17496 = 1 + 80 / 17496 := by norm_num
  have hlog_ratio_hi : Real.log ((26 : ℝ) ^ 3 / 17496) ≤ 80 / 17496 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (80 / 17496) / (1 + 80 / 17496) ≤ Real.log ((26 : ℝ) ^ 3 / 17496) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((26 : ℝ) ^ 3) = 3 * Real.log 26 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((26 : ℝ) ^ 3 / 17496) = Real.log ((26 : ℝ) ^ 3) - Real.log 17496 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 26| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2 - (-4058 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 26 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 26 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 26 - 21 * Real.pi / 2 = ((10 : ℝ) * Real.log 26 - 5 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 26) ((10 : ℝ) * Real.log 26 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 26) ((10 : ℝ) * Real.log 26 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) (-4058 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) (-4058 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.cos ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - (1 - 2 * (((-4058 / 10000 : ℝ)) / 2 - (((-4058 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-4058 / 10000 : ℝ)) / 2 - (((-4058 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 26) - (1 - 2 * (((-4058 / 10000 : ℝ)) / 2 - (((-4058 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hs_eq]; linarith [ha_s, hrem_c]
  have hb_c : |Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - (((-4058 / 10000 : ℝ)) - ((-4058 / 10000 : ℝ)) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 26 - 21 * Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2))) ^ 3 / 6) - (((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hneg_c : |(-Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) - (-(((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - (((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2)) - (-(((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 26 - 21 * Real.pi / 2) - (((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 26) - (-(((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hneg_c, hb_c, hrem_s]
  have hre := dp_cpow10_re 26 (by norm_num)
  have him := dp_cpow10_im 26 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 26)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 26)
  have hcenter_re : |(1961 / 10000 : ℝ) * (-(((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6)) - 774 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1961 / 10000 : ℝ) * (1 - 2 * (((-4058 / 10000 : ℝ)) / 2 - (((-4058 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2) - 1802 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((26 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (774 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c26 : ℂ)).re = 774 / 10000 := by simp [dp_headB_c26]
    rw [hre]
    have ha0 : |(1961 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(26 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 26) - 1961 / 10000 * (-(((-4058 / 10000 : ℝ)) - (((-4058 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((26 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1802 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c26 : ℂ)).im = 1802 / 10000 := by simp [dp_headB_c26]
    rw [him]
    have ha0 : |(1961 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(26 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 26) - 1961 / 10000 * (1 - 2 * (((-4058 / 10000 : ℝ)) / 2 - (((-4058 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((26 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c26 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n27_tight : ‖(((27 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c27‖ ≤ 1 / 100 := by
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5196 / 1000 : ℝ) ≤ Real.sqrt 27 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 27 ≤ (5197 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 27 (5196 / 1000) (5197 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(27 : ℝ) ^ (-1 / 2 : ℝ) - 1925 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by have h1 : (27 : ℝ) = 3 ^ 3 := by norm_num; rw [h1, Real.log_pow]
  have hx : |(10 : ℝ) * Real.log 27| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlog27]
  have he_le : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlog27, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2 - (-284 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlog27, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 27 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 27 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 27 - 21 * Real.pi / 2 = ((10 : ℝ) * Real.log 27 - 5 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 27) ((10 : ℝ) * Real.log 27 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 27) ((10 : ℝ) * Real.log 27 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) (-284 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) (-284 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.cos ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - (1 - 2 * (((-284 / 10000 : ℝ)) / 2 - (((-284 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-284 / 10000 : ℝ)) / 2 - (((-284 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 27) - (1 - 2 * (((-284 / 10000 : ℝ)) / 2 - (((-284 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hs_eq]; linarith [ha_s, hrem_c]
  have hb_c : |Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - (((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 27 - 21 * Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2))) ^ 3 / 6) - (((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hneg_c : |(-Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) - (-(((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - (((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2)) - (-(((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 27 - 21 * Real.pi / 2) - (((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 27) - (-(((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hneg_c, hb_c, hrem_s]
  have hre := dp_cpow10_re 27 (by norm_num)
  have him := dp_cpow10_im 27 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 27)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 27)
  have hcenter_re : |(1925 / 10000 : ℝ) * (-(((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6)) - 55 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1925 / 10000 : ℝ) * (1 - 2 * (((-284 / 10000 : ℝ)) / 2 - (((-284 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2) - 1924 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((27 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (55 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c27 : ℂ)).re = 55 / 10000 := by simp [dp_headB_c27]
    rw [hre]
    have ha0 : |(1925 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(27 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 27) - 1925 / 10000 * (-(((-284 / 10000 : ℝ)) - (((-284 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((27 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1924 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c27 : ℂ)).im = 1924 / 10000 := by simp [dp_headB_c27]
    rw [him]
    have ha0 : |(1925 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(27 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 27) - 1925 / 10000 * (1 - 2 * (((-284 / 10000 : ℝ)) / 2 - (((-284 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((27 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c27 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n28_tight : ‖(((28 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c28‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5291 / 1000 : ℝ) ≤ Real.sqrt 28 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 28 ≤ (5292 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 28 (5291 / 1000) (5292 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(28 : ℝ) ^ (-1 / 2 : ℝ) - 1890 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (629856 : ℝ) = 5 * Real.log 2 + 9 * Real.log 3 := by have h1 : (629856 : ℝ) = 2 ^ 5 * 3 ^ 9 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (28 : ℝ) ^ 4 := by norm_num
  have hm_pos : (0 : ℝ) < (629856 : ℝ) := by norm_num
  have hratio_eq : (28 : ℝ) ^ 4 / 629856 = 1 + (-15200 / 629856) := by norm_num
  have hlog_ratio_hi : Real.log ((28 : ℝ) ^ 4 / 629856) ≤ (-15200 / 629856) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-15200 / 629856) / (1 + (-15200 / 629856)) ≤ Real.log ((28 : ℝ) ^ 4 / 629856) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((28 : ℝ) ^ 4) = 4 * Real.log 28 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((28 : ℝ) ^ 4 / 629856) = Real.log ((28 : ℝ) ^ 4) - Real.log 629856 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 28| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2 - 3353 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 28 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 28 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 28 - 21 * Real.pi / 2 = ((10 : ℝ) * Real.log 28 - 5 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 28) ((10 : ℝ) * Real.log 28 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 28) ((10 : ℝ) * Real.log 28 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) (3353 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) (3353 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.cos ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - (1 - 2 * (((3353 / 10000 : ℝ)) / 2 - (((3353 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((3353 / 10000 : ℝ)) / 2 - (((3353 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 28) - (1 - 2 * (((3353 / 10000 : ℝ)) / 2 - (((3353 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hs_eq]; linarith [ha_s, hrem_c]
  have hb_c : |Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - (((3353 / 10000 : ℝ)) - (((3353 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 28 - 21 * Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2))) ^ 3 / 6) - (((3353 / 10000 : ℝ)) - (((3353 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hneg_c : |(-Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) - (-((((3353 / 10000 : ℝ))) - (((3353 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - (((3353 / 10000 : ℝ)) - (((3353 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2)) - (-((((3353 / 10000 : ℝ))) - (((3353 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 28 - 21 * Real.pi / 2) - (((3353 / 10000 : ℝ)) - (((3353 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 28) - (-((((3353 / 10000 : ℝ))) - (((3353 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hneg_c, hb_c, hrem_s]
  have hre := dp_cpow10_re 28 (by norm_num)
  have him := dp_cpow10_im 28 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 28)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 28)
  have hcenter_re : |(1890 / 10000 : ℝ) * (-((((3353 / 10000 : ℝ))) - (((3353 / 10000 : ℝ))) ^ 3 / 6)) - (-622 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1890 / 10000 : ℝ) * (1 - 2 * (((3353 / 10000 : ℝ)) / 2 - (((3353 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2) - 1785 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((28 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-622 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c28 : ℂ)).re = -622 / 10000 := by simp [dp_headB_c28]
    rw [hre]
    have ha0 : |(1890 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(28 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 28) - 1890 / 10000 * (-((((3353 / 10000 : ℝ))) - (((3353 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((28 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1785 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c28 : ℂ)).im = 1785 / 10000 := by simp [dp_headB_c28]
    rw [him]
    have ha0 : |(1890 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(28 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 28) - 1890 / 10000 * (1 - 2 * (((3353 / 10000 : ℝ)) / 2 - (((3353 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((28 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c28 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n29_tight : ‖(((29 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c29‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5385 / 1000 : ℝ) ≤ Real.sqrt 29 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 29 ≤ (5386 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 29 (5385 / 1000) (5386 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(29 : ℝ) ^ (-1 / 2 : ℝ) - 1857 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (708588 : ℝ) = 2 * Real.log 2 + 11 * Real.log 3 := by have h1 : (708588 : ℝ) = 2 ^ 2 * 3 ^ 11 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (29 : ℝ) ^ 4 := by norm_num
  have hm_pos : (0 : ℝ) < (708588 : ℝ) := by norm_num
  have hratio_eq : (29 : ℝ) ^ 4 / 708588 = 1 + (-1307 / 708588) := by norm_num
  have hlog_ratio_hi : Real.log ((29 : ℝ) ^ 4 / 708588) ≤ (-1307 / 708588) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-1307 / 708588) / (1 + (-1307 / 708588)) ≤ Real.log ((29 : ℝ) ^ 4 / 708588) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((29 : ℝ) ^ 4) = 4 * Real.log 29 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((29 : ℝ) ^ 4 / 708588) = Real.log ((29 : ℝ) ^ 4) - Real.log 708588 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 29| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2 - 6862 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 29 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 29 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 29 - 21 * Real.pi / 2 = ((10 : ℝ) * Real.log 29 - 5 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 29) ((10 : ℝ) * Real.log 29 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 29) ((10 : ℝ) * Real.log 29 - 5 * (2 * Real.pi)) ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) hx 5 hrdef hedef he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) (6862 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) (6862 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.cos ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - (1 - 2 * (((6862 / 10000 : ℝ)) / 2 - (((6862 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((6862 / 10000 : ℝ)) / 2 - (((6862 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 29) - (1 - 2 * (((6862 / 10000 : ℝ)) / 2 - (((6862 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hs_eq]; linarith [ha_s, hrem_c]
  have hb_c : |Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - (((6862 / 10000 : ℝ)) - (((6862 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 29 - 21 * Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) - ((((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2))) ^ 3 / 6) - (((6862 / 10000 : ℝ)) - (((6862 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hneg_c : |(-Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) - (-((((6862 / 10000 : ℝ))) - (((6862 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - (((6862 / 10000 : ℝ)) - (((6862 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2)) - (-((((6862 / 10000 : ℝ))) - (((6862 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 29 - 21 * Real.pi / 2) - (((6862 / 10000 : ℝ)) - (((6862 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 29) - (-((((6862 / 10000 : ℝ))) - (((6862 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hneg_c, hb_c, hrem_s]
  have hre := dp_cpow10_re 29 (by norm_num)
  have him := dp_cpow10_im 29 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 29)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 29)
  have hcenter_re : |(1857 / 10000 : ℝ) * (-((((6862 / 10000 : ℝ))) - (((6862 / 10000 : ℝ))) ^ 3 / 6)) - (-1177 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1857 / 10000 : ℝ) * (1 - 2 * (((6862 / 10000 : ℝ)) / 2 - (((6862 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2) - 1437 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((29 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1177 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c29 : ℂ)).re = -1177 / 10000 := by simp [dp_headB_c29]
    rw [hre]
    have ha0 : |(1857 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(29 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 29) - 1857 / 10000 * (-((((6862 / 10000 : ℝ))) - (((6862 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((29 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (1437 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c29 : ℂ)).im = 1437 / 10000 := by simp [dp_headB_c29]
    rw [him]
    have ha0 : |(1857 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(29 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 29) - 1857 / 10000 * (1 - 2 * (((6862 / 10000 : ℝ)) / 2 - (((6862 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((29 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c29 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n30_tight : ‖(((30 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c30‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5477 / 1000 : ℝ) ≤ Real.sqrt 30 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 30 ≤ (5478 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 30 (5477 / 1000) (5478 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(30 : ℝ) ^ (-1 / 2 : ℝ) - 1826 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (26244 : ℝ) = 2 * Real.log 2 + 8 * Real.log 3 := by have h1 : (26244 : ℝ) = 2 ^ 2 * 3 ^ 8 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (30 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (26244 : ℝ) := by norm_num
  have hratio_eq : (30 : ℝ) ^ 3 / 26244 = 1 + 756 / 26244 := by norm_num
  have hlog_ratio_hi : Real.log ((30 : ℝ) ^ 3 / 26244) ≤ 756 / 26244 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (756 / 26244) / (1 + 756 / 26244) ≤ Real.log ((30 : ℝ) ^ 3 / 26244) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((30 : ℝ) ^ 3) = 3 * Real.log 30 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((30 : ℝ) ^ 3 / 26244) = Real.log ((30 : ℝ) ^ 3) - Real.log 26244 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 30| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 30 - 11 * Real.pi - (-5455 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 30 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hr_pi : ((10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi)) + Real.pi = (10 : ℝ) * Real.log 30 - 11 * Real.pi + 2 * Real.pi := by ring
  have hr_pi2 : (10 : ℝ) * Real.log 30 - 11 * Real.pi + 2 * Real.pi = (10 : ℝ) * Real.log 30 - 11 * Real.pi + 2 * Real.pi := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (by simp) he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (by simp) he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (-5455 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 30 - 11 * Real.pi) (-5455 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e_close : |Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - ((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 30 - 11 * Real.pi))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
    have hb0 : |((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 30 - 11 * Real.pi))) ^ 3 / 6) - (((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_e_close : |Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (1 - 2 * ((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 30 - 11 * Real.pi| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 30 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hred_s : Real.sin ((10 : ℝ) * Real.log 30) = Real.sin ((10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_sin_reduce _ _).symm
  have hred_c : Real.cos ((10 : ℝ) * Real.log 30) = Real.cos ((10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_cos_reduce _ _).symm
  have hpi_s : Real.sin ((10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi)) = -Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) := by
    have h1 : (10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 30 - 11 * Real.pi + Real.pi := by ring
    rw [h1, Real.sin_add_pi]
  have hpi_c : Real.cos ((10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi)) = -Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) := by
    have h1 : (10 : ℝ) * Real.log 30 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 30 - 11 * Real.pi + Real.pi := by ring
    rw [h1, Real.cos_add_pi]
  have hneg_s : |-Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (-(((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi)) - (-(((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hneg_c : |-Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (-(1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi)) - (-(1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 30 - 11 * Real.pi) - (1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 30) - (-(((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hred_s, hpi_s]; linarith [hneg_s, hsin_e_close]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 30) - (-(1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hred_c, hpi_c]; linarith [hneg_c, hcos_e_close]
  have hre := dp_cpow10_re 30 (by norm_num)
  have him := dp_cpow10_im 30 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 30)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 30)
  have hcenter_re : |(1826 / 10000 : ℝ) * (-(1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1561 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1826 / 10000 : ℝ) * (-(((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6)) - 947 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((30 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1561 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c30 : ℂ)).re = -1561 / 10000 := by simp [dp_headB_c30]
    rw [hre]
    have ha0 : |(1826 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(30 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 30) - 1826 / 10000 * (-(1 - 2 * (((-5455 / 10000 : ℝ)) / 2 - (((-5455 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((30 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (947 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c30 : ℂ)).im = 947 / 10000 := by simp [dp_headB_c30]
    rw [him]
    have ha0 : |(1826 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(30 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 30) - 1826 / 10000 * (-(((-5455 / 10000 : ℝ)) - (((-5455 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((30 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c30 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n31_tight : ‖(((31 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c31‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5567 / 1000 : ℝ) ≤ Real.sqrt 31 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 31 ≤ (5568 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 31 (5567 / 1000) (5568 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(31 : ℝ) ^ (-1 / 2 : ℝ) - 1796 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (972 : ℝ) = 2 * Real.log 2 + 5 * Real.log 3 := by have h1 : (972 : ℝ) = 2 ^ 2 * 3 ^ 5 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (31 : ℝ) ^ 2 := by norm_num
  have hm_pos : (0 : ℝ) < (972 : ℝ) := by norm_num
  have hratio_eq : (31 : ℝ) ^ 2 / 972 = 1 + (-11 / 972) := by norm_num
  have hlog_ratio_hi : Real.log ((31 : ℝ) ^ 2 / 972) ≤ (-11 / 972) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-11 / 972) / (1 + (-11 / 972)) ≤ Real.log ((31 : ℝ) ^ 2 / 972) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((31 : ℝ) ^ 2) = 2 * Real.log 31 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((31 : ℝ) ^ 2 / 972) = Real.log ((31 : ℝ) ^ 2) - Real.log 972 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 31| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 31 - 11 * Real.pi - (-2176 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 31 - ((5 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (by simp) he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (by simp) he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (-2176 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 31 - 11 * Real.pi) (-2176 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e_close : |Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - ((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 31 - 11 * Real.pi))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
    have hb0 : |((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 31 - 11 * Real.pi))) ^ 3 / 6) - (((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_e_close : |Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (1 - 2 * ((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 31 - 11 * Real.pi| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 31 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hred_s : Real.sin ((10 : ℝ) * Real.log 31) = Real.sin ((10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_sin_reduce _ _).symm
  have hred_c : Real.cos ((10 : ℝ) * Real.log 31) = Real.cos ((10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_cos_reduce _ _).symm
  have hpi_s : Real.sin ((10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi)) = -Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 31 - 11 * Real.pi + Real.pi := by ring; rw [h1, Real.sin_add_pi]
  have hpi_c : Real.cos ((10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi)) = -Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 31 - 5 * (2 * Real.pi) = (10 : ℝ) * Real.log 31 - 11 * Real.pi + Real.pi := by ring; rw [h1, Real.cos_add_pi]
  have hneg_s : |-Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (-(((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi)) - (-(((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hneg_c : |-Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (-(1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi)) - (-(1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 31 - 11 * Real.pi) - (1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 31) - (-(((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hred_s, hpi_s]; linarith [hneg_s, hsin_e_close]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 31) - (-(1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hred_c, hpi_c]; linarith [hneg_c, hcos_e_close]
  have hre := dp_cpow10_re 31 (by norm_num)
  have him := dp_cpow10_im 31 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 31)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 31)
  have hcenter_re : |(1796 / 10000 : ℝ) * (-(1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1754 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1796 / 10000 : ℝ) * (-(((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6)) - 388 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((31 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1754 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c31 : ℂ)).re = -1754 / 10000 := by simp [dp_headB_c31]
    rw [hre]
    have ha0 : |(1796 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(31 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 31) - 1796 / 10000 * (-(1 - 2 * (((-2176 / 10000 : ℝ)) / 2 - (((-2176 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((31 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (388 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c31 : ℂ)).im = 388 / 10000 := by simp [dp_headB_c31]
    rw [him]
    have ha0 : |(1796 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(31 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 31) - 1796 / 10000 * (-(((-2176 / 10000 : ℝ)) - (((-2176 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((31 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c31 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n32_tight : ‖(((32 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c32‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5656 / 1000 : ℝ) ≤ Real.sqrt 32 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 32 ≤ (5657 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 32 (5656 / 1000) (5657 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(32 : ℝ) ^ (-1 / 2 : ℝ) - 1768 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by have h1 : (32 : ℝ) = 2 ^ 5 := by norm_num; rw [h1, Real.log_pow]
  have hx : |(10 : ℝ) * Real.log 32| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog32]
  have he_le : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog32, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 32 - 11 * Real.pi - 998 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog32, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 32 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (by simp) he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (by simp) he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (998 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 32 - 11 * Real.pi) (998 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e_close : |Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - ((998 / 10000 : ℝ) - ((998 / 10000 : ℝ)) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - ((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 32 - 11 * Real.pi))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
    have hb0 : |((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 32 - 11 * Real.pi))) ^ 3 / 6) - (((998 / 10000 : ℝ)) - (((998 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_e_close : |Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (1 - 2 * ((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 32 - 11 * Real.pi| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 32 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hred_s : Real.sin ((10 : ℝ) * Real.log 32) = Real.sin ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_sin_reduce _ _).symm
  have hred_c : Real.cos ((10 : ℝ) * Real.log 32) = Real.cos ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_cos_reduce _ _).symm
  have hpi_s : Real.sin ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)) = -Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi) + Real.pi = (10 : ℝ) * Real.log 32 - 11 * Real.pi := by ring; have h2 := Real.sin_add_pi ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)); rw [h1] at h2; linarith [h2]
  have hpi_c : Real.cos ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)) = -Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi) + Real.pi = (10 : ℝ) * Real.log 32 - 11 * Real.pi := by ring; have h2 := Real.cos_add_pi ((10 : ℝ) * Real.log 32 - 6 * (2 * Real.pi)); rw [h1] at h2; linarith [h2]
  have hneg_s : |-Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (-(((998 / 10000 : ℝ)) - (((998 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (((998 / 10000 : ℝ)) - (((998 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi)) - (-((((998 / 10000 : ℝ))) - (((998 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (((998 / 10000 : ℝ)) - (((998 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hneg_c : |-Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (-(1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi)) - (-(1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 32 - 11 * Real.pi) - (1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 32) - (-((((998 / 10000 : ℝ))) - (((998 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hred_s, hpi_s]; linarith [hneg_s, hsin_e_close]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 32) - (-(1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hred_c, hpi_c]; linarith [hneg_c, hcos_e_close]
  have hre := dp_cpow10_re 32 (by norm_num)
  have him := dp_cpow10_im 32 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 32)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 32)
  have hcenter_re : |(1768 / 10000 : ℝ) * (-(1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1759 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1768 / 10000 : ℝ) * (-((((998 / 10000 : ℝ))) - (((998 / 10000 : ℝ))) ^ 3 / 6)) - (-176 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((32 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1759 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c32 : ℂ)).re = -1759 / 10000 := by simp [dp_headB_c32]
    rw [hre]
    have ha0 : |(1768 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(32 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 32) - 1768 / 10000 * (-(1 - 2 * (((998 / 10000 : ℝ)) / 2 - (((998 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((32 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-176 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c32 : ℂ)).im = -176 / 10000 := by simp [dp_headB_c32]
    rw [him]
    have ha0 : |(1768 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(32 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 32) - 1768 / 10000 * (-((((998 / 10000 : ℝ))) - (((998 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((32 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c32 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n33_tight : ‖(((33 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c33‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5744 / 1000 : ℝ) ≤ Real.sqrt 33 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 33 ≤ (5745 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 33 (5744 / 1000) (5745 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(33 : ℝ) ^ (-1 / 2 : ℝ) - 1741 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (34992 : ℝ) = 4 * Real.log 2 + 7 * Real.log 3 := by have h1 : (34992 : ℝ) = 2 ^ 4 * 3 ^ 7 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (33 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (34992 : ℝ) := by norm_num
  have hratio_eq : (33 : ℝ) ^ 3 / 34992 = 1 + 945 / 34992 := by norm_num
  have hlog_ratio_hi : Real.log ((33 : ℝ) ^ 3 / 34992) ≤ 945 / 34992 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (945 / 34992) / (1 + 945 / 34992) ≤ Real.log ((33 : ℝ) ^ 3 / 34992) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((33 : ℝ) ^ 3) = 3 * Real.log 33 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((33 : ℝ) ^ 3 / 34992) = Real.log ((33 : ℝ) ^ 3) - Real.log 34992 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 33| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 33 - 11 * Real.pi - 4076 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 33 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (by simp) he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (by rw [abs_le]; constructor <;> linarith [he_le]) 0 ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (by simp) he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (4076 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 33 - 11 * Real.pi) (4076 / 10000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_le])
  have hrem_s : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e_close : |Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - ((4076 / 10000 : ℝ) - ((4076 / 10000 : ℝ)) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - ((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 33 - 11 * Real.pi))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
    have hb0 : |((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) - ((((10 : ℝ) * Real.log 33 - 11 * Real.pi))) ^ 3 / 6) - (((4076 / 10000 : ℝ)) - (((4076 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_e_close : |Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (1 - 2 * ((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 33 - 11 * Real.pi| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) / 2 - ((((10 : ℝ) * Real.log 33 - 11 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hred_s : Real.sin ((10 : ℝ) * Real.log 33) = Real.sin ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_sin_reduce _ _).symm
  have hred_c : Real.cos ((10 : ℝ) * Real.log 33) = Real.cos ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)) := by rw [hrdef]; exact (dp_cos_reduce _ _).symm
  have hpi_s : Real.sin ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)) = -Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi) + Real.pi = (10 : ℝ) * Real.log 33 - 11 * Real.pi := by ring; have h2 := Real.sin_add_pi ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)); rw [h1] at h2; linarith [h2]
  have hpi_c : Real.cos ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)) = -Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) := by have h1 : (10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi) + Real.pi = (10 : ℝ) * Real.log 33 - 11 * Real.pi := by ring; have h2 := Real.cos_add_pi ((10 : ℝ) * Real.log 33 - 6 * (2 * Real.pi)); rw [h1] at h2; linarith [h2]
  have hneg_s : |-Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (-(((4076 / 10000 : ℝ)) - (((4076 / 10000 : ℝ))) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (((4076 / 10000 : ℝ)) - (((4076 / 10000 : ℝ))) ^ 3 / 6)| := by have e : (-Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi)) - (-((((4076 / 10000 : ℝ))) - (((4076 / 10000 : ℝ))) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (((4076 / 10000 : ℝ)) - (((4076 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [e, abs_neg]
  have hneg_c : |-Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (-(1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi)) - (-(1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 33 - 11 * Real.pi) - (1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 33) - (-((((4076 / 10000 : ℝ))) - (((4076 / 10000 : ℝ))) ^ 3 / 6))| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hred_s, hpi_s]; linarith [hneg_s, hsin_e_close]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 33) - (-(1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by rw [hred_c, hpi_c]; linarith [hneg_c, hcos_e_close]
  have hre := dp_cpow10_re 33 (by norm_num)
  have him := dp_cpow10_im 33 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 33)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 33)
  have hcenter_re : |(1741 / 10000 : ℝ) * (-(1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1598 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1741 / 10000 : ℝ) * (-((((4076 / 10000 : ℝ))) - (((4076 / 10000 : ℝ))) ^ 3 / 6)) - (-690 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((33 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1598 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c33 : ℂ)).re = -1598 / 10000 := by simp [dp_headB_c33]
    rw [hre]
    have ha0 : |(1741 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(33 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 33) - 1741 / 10000 * (-(1 - 2 * (((4076 / 10000 : ℝ)) / 2 - (((4076 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((33 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-690 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c33 : ℂ)).im = -690 / 10000 := by simp [dp_headB_c33]
    rw [him]
    have ha0 : |(1741 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(33 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 33) - 1741 / 10000 * (-((((4076 / 10000 : ℝ))) - (((4076 / 10000 : ℝ))) ^ 3 / 6))| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((33 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c33 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n34_tight : ‖(((34 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c34‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5830 / 1000 : ℝ) ≤ Real.sqrt 34 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 34 ≤ (5831 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 34 (5830 / 1000) (5831 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(34 : ℝ) ^ (-1 / 2 : ℝ) - 1715 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (39366 : ℝ) = 1 * Real.log 2 + 9 * Real.log 3 := by have h1 : (39366 : ℝ) = 2 ^ 1 * 3 ^ 9 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (34 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (39366 : ℝ) := by norm_num
  have hratio_eq : (34 : ℝ) ^ 3 / 39366 = 1 + (-62 / 39366) := by norm_num
  have hlog_ratio_hi : Real.log ((34 : ℝ) ^ 3 / 39366) ≤ (-62 / 39366) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-62 / 39366) / (1 + (-62 / 39366)) ≤ Real.log ((34 : ℝ) ^ 3 / 39366) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((34 : ℝ) ^ 3) = 3 * Real.log 34 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((34 : ℝ) ^ 3 / 39366) = Real.log ((34 : ℝ) ^ 3) - Real.log 39366 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 34| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_le : |(10 : ℝ) * Real.log 34 - 23 * Real.pi / 2 + 2 * Real.pi| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_le2 : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by have heq : (10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2 = (10 : ℝ) * Real.log 34 - 23 * Real.pi / 2 + 2 * Real.pi - Real.pi + Real.pi / 2 := by ring; linarith [he_le, heq]
  have he_close : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2 - (-8647 / 10000)| ≤ 50 / 10000 := by have heq : (10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2 = (10 : ℝ) * Real.log 34 - 23 * Real.pi / 2 + 2 * Real.pi - Real.pi + Real.pi / 2 := by ring; rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 34 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  have he_mem : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by linarith [he_le2]
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 34) ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 34) ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) (-8647 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) (-8647 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 34) - (-(1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - (((-8647 / 10000 : ℝ)) - (((-8647 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 34 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((-8647 / 10000 : ℝ)) - (((-8647 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 34) - (((-8647 / 10000 : ℝ)) - (((-8647 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 34 (by norm_num)
  have him := dp_cpow10_im 34 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 34)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 34)
  have hcenter_re : |(1715 / 10000 : ℝ) * (((-8647 / 10000 : ℝ)) - (((-8647 / 10000 : ℝ))) ^ 3 / 6) - (-1305 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1715 / 10000 : ℝ) * (-(1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1113 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((34 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-1305 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c34 : ℂ)).re = -1305 / 10000 := by simp [dp_headB_c34]
    rw [hre]
    have ha0 : |(1715 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(34 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 34) - 1715 / 10000 * (((-8647 / 10000 : ℝ)) - (((-8647 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((34 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1113 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c34 : ℂ)).im = -1113 / 10000 := by simp [dp_headB_c34]
    rw [him]
    have ha0 : |(1715 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(34 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 34) - 1715 / 10000 * (-(1 - 2 * (((-8647 / 10000 : ℝ)) / 2 - (((-8647 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((34 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c34 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n35_tight : ‖(((35 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c35‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (5916 / 1000 : ℝ) ≤ Real.sqrt 35 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 35 ≤ (5917 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 35 (5916 / 1000) (5917 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(35 : ℝ) ^ (-1 / 2 : ℝ) - 1690 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (41472 : ℝ) = 9 * Real.log 2 + 4 * Real.log 3 := by have h1 : (41472 : ℝ) = 2 ^ 9 * 3 ^ 4 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (35 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (41472 : ℝ) := by norm_num
  have hratio_eq : (35 : ℝ) ^ 3 / 41472 = 1 + 1403 / 41472 := by norm_num
  have hlog_ratio_hi : Real.log ((35 : ℝ) ^ 3 / 41472) ≤ 1403 / 41472 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (1403 / 41472) / (1 + 1403 / 41472) ≤ Real.log ((35 : ℝ) ^ 3 / 41472) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((35 : ℝ) ^ 3) = 3 * Real.log 35 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((35 : ℝ) ^ 3 / 41472) = Real.log ((35 : ℝ) ^ 3) - Real.log 41472 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 35| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_mem : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2 - (-5748 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 35 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 35) ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 35) ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) (-5748 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) (-5748 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 35) - (-(1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - (((-5748 / 10000 : ℝ)) - (((-5748 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 35 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((-5748 / 10000 : ℝ)) - (((-5748 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 35) - (((-5748 / 10000 : ℝ)) - (((-5748 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 35 (by norm_num)
  have him := dp_cpow10_im 35 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 35)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 35)
  have hcenter_re : |(1690 / 10000 : ℝ) * (((-5748 / 10000 : ℝ)) - (((-5748 / 10000 : ℝ))) ^ 3 / 6) - (-919 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1690 / 10000 : ℝ) * (-(1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1419 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((35 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-919 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c35 : ℂ)).re = -919 / 10000 := by simp [dp_headB_c35]
    rw [hre]
    have ha0 : |(1690 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(35 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 35) - 1690 / 10000 * (((-5748 / 10000 : ℝ)) - (((-5748 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((35 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1419 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c35 : ℂ)).im = -1419 / 10000 := by simp [dp_headB_c35]
    rw [him]
    have ha0 : |(1690 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(35 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 35) - 1690 / 10000 * (-(1 - 2 * (((-5748 / 10000 : ℝ)) / 2 - (((-5748 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((35 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c35 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n36_tight : ‖(((36 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c36‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt36 : Real.sqrt (36 : ℝ) = 6 := by have h36 : (36 : ℝ) = 6 ^ 2 := by norm_num; rw [h36]; rw [Real.sqrt_sq (by norm_num)]
  have hamp36 : (36 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 6 := by have hsqrt_eq : Real.sqrt (36 : ℝ) = (36 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 36; have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring; have hrw : (36 : ℝ) ^ (-1 / 2 : ℝ) = (((36 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by rw [e]; exact Real.rpow_neg (by norm_num) _; rw [hrw, ← hsqrt_eq, hsqrt36]; norm_num
  have hlog36 : Real.log (36 : ℝ) = 2 * Real.log 2 + 2 * Real.log 3 := by have h1 : (36 : ℝ) = 2 ^ 2 * 3 ^ 2 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hx : |(10 : ℝ) * Real.log 36| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog36]
  have he_mem : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog36, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2 - (-2931 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlog36, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 36 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 36) ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 36) ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) (-2931 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) (-2931 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 36) - (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 36 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 36) - (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 36 (by norm_num)
  have him := dp_cpow10_im 36 (by norm_num)
  have hcenter_re : |(1 / 6 : ℝ) * (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6) - (-482 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1 / 6 : ℝ) * (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1596 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((36 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-482 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c36 : ℂ)).re = -482 / 10000 := by simp [dp_headB_c36]
    rw [hre, hamp36]
    have e1 : |(1 / 6 : ℝ) * Real.cos (10 * Real.log 36) - 1 / 6 * (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 6 * (1 / 100 + 3 / 2 * (50 / 10000)) := by have hsplit : (1 / 6 : ℝ) * Real.cos (10 * Real.log 36) - 1 / 6 * (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6) = 1 / 6 * (Real.cos (10 * Real.log 36) - (((-2931 / 10000 : ℝ)) - (((-2931 / 10000 : ℝ))) ^ 3 / 6)) := by ring; rw [hsplit, abs_mul]; have hhalf : |(1 / 6 : ℝ)| = 1 / 6 := by norm_num; rw [hhalf]; exact mul_le_mul_of_nonneg_left hcos_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((36 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1596 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c36 : ℂ)).im = -1596 / 10000 := by simp [dp_headB_c36]
    rw [him, hamp36]
    have e1 : |(1 / 6 : ℝ) * Real.sin (10 * Real.log 36) - 1 / 6 * (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 6 * (1 / 800 + 3 * (50 / 10000)) := by have hsplit : (1 / 6 : ℝ) * Real.sin (10 * Real.log 36) - 1 / 6 * (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = 1 / 6 * (Real.sin (10 * Real.log 36) - (-(1 - 2 * (((-2931 / 10000 : ℝ)) / 2 - (((-2931 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))) := by ring; rw [hsplit, abs_mul]; have hhalf : |(1 / 6 : ℝ)| = 1 / 6 := by norm_num; rw [hhalf]; exact mul_le_mul_of_nonneg_left hsin_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((36 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c36 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n37_tight : ‖(((37 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c37‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6082 / 1000 : ℝ) ≤ Real.sqrt 37 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 37 ≤ (6083 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 37 (6082 / 1000) (6083 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(37 : ℝ) ^ (-1 / 2 : ℝ) - 1644 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (52488 : ℝ) = 3 * Real.log 2 + 8 * Real.log 3 := by have h1 : (52488 : ℝ) = 2 ^ 3 * 3 ^ 8 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (37 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (52488 : ℝ) := by norm_num
  have hratio_eq : (37 : ℝ) ^ 3 / 52488 = 1 + (-1835 / 52488) := by norm_num
  have hlog_ratio_hi : Real.log ((37 : ℝ) ^ 3 / 52488) ≤ (-1835 / 52488) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-1835 / 52488) / (1 + (-1835 / 52488)) ≤ Real.log ((37 : ℝ) ^ 3 / 52488) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((37 : ℝ) ^ 3) = 3 * Real.log 37 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((37 : ℝ) ^ 3 / 52488) = Real.log ((37 : ℝ) ^ 3) - Real.log 52488 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 37| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_mem : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2 - (-191 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 37 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 37) ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 37) ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) (-191 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) (-191 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 37) - (-(1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - (((-191 / 10000 : ℝ)) - (((-191 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 37 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((-191 / 10000 : ℝ)) - (((-191 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 37) - (((-191 / 10000 : ℝ)) - (((-191 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 37 (by norm_num)
  have him := dp_cpow10_im 37 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 37)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 37)
  have hcenter_re : |(1644 / 10000 : ℝ) * (((-191 / 10000 : ℝ)) - (((-191 / 10000 : ℝ))) ^ 3 / 6) - (-31 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1644 / 10000 : ℝ) * (-(1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1644 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((37 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-31 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c37 : ℂ)).re = -31 / 10000 := by simp [dp_headB_c37]
    rw [hre]
    have ha0 : |(1644 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(37 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 37) - 1644 / 10000 * (((-191 / 10000 : ℝ)) - (((-191 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((37 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1644 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c37 : ℂ)).im = -1644 / 10000 := by simp [dp_headB_c37]
    rw [him]
    have ha0 : |(1644 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(37 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 37) - 1644 / 10000 * (-(1 - 2 * (((-191 / 10000 : ℝ)) / 2 - (((-191 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((37 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c37 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n38_tight : ‖(((38 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c38‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6164 / 1000 : ℝ) ≤ Real.sqrt 38 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 38 ≤ (6165 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 38 (6164 / 1000) (6165 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(38 : ℝ) ^ (-1 / 2 : ℝ) - 1622 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (1458 : ℝ) = 1 * Real.log 2 + 6 * Real.log 3 := by have h1 : (1458 : ℝ) = 2 ^ 1 * 3 ^ 6 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (38 : ℝ) ^ 2 := by norm_num
  have hm_pos : (0 : ℝ) < (1458 : ℝ) := by norm_num
  have hratio_eq : (38 : ℝ) ^ 2 / 1458 = 1 + (-14 / 1458) := by norm_num
  have hlog_ratio_hi : Real.log ((38 : ℝ) ^ 2 / 1458) ≤ (-14 / 1458) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-14 / 1458) / (1 + (-14 / 1458)) ≤ Real.log ((38 : ℝ) ^ 2 / 1458) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((38 : ℝ) ^ 2) = 2 * Real.log 38 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((38 : ℝ) ^ 2 / 1458) = Real.log ((38 : ℝ) ^ 2) - Real.log 1458 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 38| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_mem : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2 - 2475 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 38 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 38) ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 38) ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) (2475 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) (2475 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 38) - (-(1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - (((2475 / 10000 : ℝ)) - (((2475 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 38 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((2475 / 10000 : ℝ)) - (((2475 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 38) - (((2475 / 10000 : ℝ)) - (((2475 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 38 (by norm_num)
  have him := dp_cpow10_im 38 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 38)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 38)
  have hcenter_re : |(1622 / 10000 : ℝ) * (((2475 / 10000 : ℝ)) - (((2475 / 10000 : ℝ))) ^ 3 / 6) - 397 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1622 / 10000 : ℝ) * (-(1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1573 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((38 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (397 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c38 : ℂ)).re = 397 / 10000 := by simp [dp_headB_c38]
    rw [hre]
    have ha0 : |(1622 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(38 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 38) - 1622 / 10000 * (((2475 / 10000 : ℝ)) - (((2475 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((38 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1573 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c38 : ℂ)).im = -1573 / 10000 := by simp [dp_headB_c38]
    rw [him]
    have ha0 : |(1622 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(38 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 38) - 1622 / 10000 * (-(1 - 2 * (((2475 / 10000 : ℝ)) / 2 - (((2475 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((38 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c38 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n39_tight : ‖(((39 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c39‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6244 / 1000 : ℝ) ≤ Real.sqrt 39 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 39 ≤ (6245 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 39 (6244 / 1000) (6245 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(39 : ℝ) ^ (-1 / 2 : ℝ) - 1601 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (59049 : ℝ) = 10 * Real.log 3 := by have h1 : (59049 : ℝ) = 3 ^ 10 := by norm_num; rw [h1, Real.log_pow]
  have hpe_pos : (0 : ℝ) < (39 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (59049 : ℝ) := by norm_num
  have hratio_eq : (39 : ℝ) ^ 3 / 59049 = 1 + 270 / 59049 := by norm_num
  have hlog_ratio_hi : Real.log ((39 : ℝ) ^ 3 / 59049) ≤ 270 / 59049 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (270 / 59049) / (1 + 270 / 59049) ≤ Real.log ((39 : ℝ) ^ 3 / 59049) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((39 : ℝ) ^ 3) = 3 * Real.log 39 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((39 : ℝ) ^ 3 / 59049) = Real.log ((39 : ℝ) ^ 3) - Real.log 59049 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 39| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_mem : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2 - 5073 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 39 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 39) ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 39) ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) (5073 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) (5073 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 39) - (-(1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - (((5073 / 10000 : ℝ)) - (((5073 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 39 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((5073 / 10000 : ℝ)) - (((5073 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 39) - (((5073 / 10000 : ℝ)) - (((5073 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 39 (by norm_num)
  have him := dp_cpow10_im 39 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 39)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 39)
  have hcenter_re : |(1601 / 10000 : ℝ) * (((5073 / 10000 : ℝ)) - (((5073 / 10000 : ℝ))) ^ 3 / 6) - 778 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1601 / 10000 : ℝ) * (-(1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1400 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((39 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (778 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c39 : ℂ)).re = 778 / 10000 := by simp [dp_headB_c39]
    rw [hre]
    have ha0 : |(1601 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(39 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 39) - 1601 / 10000 * (((5073 / 10000 : ℝ)) - (((5073 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((39 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1400 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c39 : ℂ)).im = -1400 / 10000 := by simp [dp_headB_c39]
    rw [him]
    have ha0 : |(1601 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(39 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 39) - 1601 / 10000 * (-(1 - 2 * (((5073 / 10000 : ℝ)) / 2 - (((5073 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((39 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c39 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n40_tight : ‖(((40 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c40‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6324 / 1000 : ℝ) ≤ Real.sqrt 40 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 40 ≤ (6325 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 40 (6324 / 1000) (6325 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(40 : ℝ) ^ (-1 / 2 : ℝ) - 1581 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (62208 : ℝ) = 8 * Real.log 2 + 5 * Real.log 3 := by have h1 : (62208 : ℝ) = 2 ^ 8 * 3 ^ 5 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (40 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (62208 : ℝ) := by norm_num
  have hratio_eq : (40 : ℝ) ^ 3 / 62208 = 1 + 1792 / 62208 := by norm_num
  have hlog_ratio_hi : Real.log ((40 : ℝ) ^ 3 / 62208) ≤ 1792 / 62208 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (1792 / 62208) / (1 + 1792 / 62208) ≤ Real.log ((40 : ℝ) ^ 3 / 62208) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((40 : ℝ) ^ 3) = 3 * Real.log 40 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((40 : ℝ) ^ 3 / 62208) = Real.log ((40 : ℝ) ^ 3) - Real.log 62208 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 40| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have he_mem : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2 - 7605 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 40 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef : (10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2 = ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 40) ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 40) ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi)) ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) hx 6 hrdef hedef he_mem
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) (7605 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) (7605 / 10000 : ℝ) (by linarith [he_mem]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [he_mem])
  have hrem_s : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have hsin_e : |Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := by
    have ha0 : |Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq, hs_eq]
    have hb0 : |(1 - 2 * ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2 - ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_c])
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 40) - (-(1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 800 + 3 * (50 / 10000) := by have hneg : |-Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (-(1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)| := by have e : (-Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) - (-(1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) := by ring; rw [e, abs_neg]; rw [hs_eq]; linarith [hneg, hsin_e]
  have hcos_e : |Real.sin ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - (((7605 / 10000 : ℝ)) - (((7605 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by
    have ha0 : |Real.sin ((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2) - ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq, hc_eq]
    have hb0 : |((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2)) - ((((10 : ℝ) * Real.log 40 - 6 * (2 * Real.pi) + Real.pi / 2))) ^ 3 / 6) - (((7605 / 10000 : ℝ)) - (((7605 / 10000 : ℝ))) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
    exact dp_abs_tri _ _ _ _ _ _ ha0 hb0 (by linarith [hrem_s])
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 40) - (((7605 / 10000 : ℝ)) - (((7605 / 10000 : ℝ))) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := by rw [hc_eq]; linarith [hcos_e, hrem_s]
  have hre := dp_cpow10_re 40 (by norm_num)
  have him := dp_cpow10_im 40 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 40)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 40)
  have hcenter_re : |(1581 / 10000 : ℝ) * (((7605 / 10000 : ℝ)) - (((7605 / 10000 : ℝ))) ^ 3 / 6) - 1090 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1581 / 10000 : ℝ) * (-(1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2)) - (-1146 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((40 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1090 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c40 : ℂ)).re = 1090 / 10000 := by simp [dp_headB_c40]
    rw [hre]
    have ha0 : |(1581 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(40 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 40) - 1581 / 10000 * (((7605 / 10000 : ℝ)) - (((7605 / 10000 : ℝ))) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((40 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-1146 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c40 : ℂ)).im = -1146 / 10000 := by simp [dp_headB_c40]
    rw [him]
    have ha0 : |(1581 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(40 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 40) - 1581 / 10000 * (-(1 - 2 * (((7605 / 10000 : ℝ)) / 2 - (((7605 / 10000 : ℝ)) / 2) ^ 3 / 6) ^ 2))| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((40 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c40 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n41_tight : ‖(((41 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c41‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6403 / 1000 : ℝ) ≤ Real.sqrt 41 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 41 ≤ (6404 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 41 (6403 / 1000) (6404 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(41 : ℝ) ^ (-1 / 2 : ℝ) - 1562 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (69984 : ℝ) = 5 * Real.log 2 + 7 * Real.log 3 := by have h1 : (69984 : ℝ) = 2 ^ 5 * 3 ^ 7 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (41 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (69984 : ℝ) := by norm_num
  have hratio_eq : (41 : ℝ) ^ 3 / 69984 = 1 + (-1063 / 69984) := by norm_num
  have hlog_ratio_hi : Real.log ((41 : ℝ) ^ 3 / 69984) ≤ (-1063 / 69984) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-1063 / 69984) / (1 + (-1063 / 69984)) ≤ Real.log ((41 : ℝ) ^ 3 / 69984) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((41 : ℝ) ^ 3) = 3 * Real.log 41 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((41 : ℝ) ^ 3 / 69984) = Real.log ((41 : ℝ) ^ 3) - Real.log 69984 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 41| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have hr_le : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi) - (-5634 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 41 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 41) hx 6 ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 41) hx 6 ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) (-5634 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) (-5634 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [hr_le])
  have hrem_s : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.sin ((10 : ℝ) * Real.log 41) - (((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
  have hb_s : |(((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((-5634 / 10000 : ℝ) - (-5634 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 41) - ((-5634 / 10000 : ℝ) - (-5634 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_s hb_s (by linarith [hrem_s])
  have ha_c : |Real.cos ((10 : ℝ) * Real.log 41) - (1 - 2 * (((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
  have hb_c : |(1 - 2 * (((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 41 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-5634 / 10000 : ℝ) / 2 - ((-5634 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 41) - (1 - 2 * ((-5634 / 10000 : ℝ) / 2 - ((-5634 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_c hb_c (by linarith [hrem_c])
  have hre := dp_cpow10_re 41 (by norm_num)
  have him := dp_cpow10_im 41 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 41)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 41)
  have hcenter_re : |(1562 / 10000 : ℝ) * (1 - 2 * ((-5634 / 10000 : ℝ) / 2 - ((-5634 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1320 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1562 / 10000 : ℝ) * ((-5634 / 10000 : ℝ) - (-5634 / 10000 : ℝ) ^ 3 / 6) - (-834 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((41 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1320 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c41 : ℂ)).re = 1320 / 10000 := by simp [dp_headB_c41]
    rw [hre]
    have ha0 : |(1562 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(41 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 41) - 1562 / 10000 * (1 - 2 * ((-5634 / 10000 : ℝ) / 2 - ((-5634 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((41 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-834 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c41 : ℂ)).im = -834 / 10000 := by simp [dp_headB_c41]
    rw [him]
    have ha0 : |(1562 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(41 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 41) - 1562 / 10000 * ((-5634 / 10000 : ℝ) - (-5634 / 10000 : ℝ) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((41 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c41 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n42_tight : ‖(((42 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c42‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6480 / 1000 : ℝ) ≤ Real.sqrt 42 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 42 ≤ (6481 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 42 (6480 / 1000) (6481 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(42 : ℝ) ^ (-1 / 2 : ℝ) - 1543 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (73728 : ℝ) = 13 * Real.log 2 + 2 * Real.log 3 := by have h1 : (73728 : ℝ) = 2 ^ 13 * 3 ^ 2 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (42 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (73728 : ℝ) := by norm_num
  have hratio_eq : (42 : ℝ) ^ 3 / 73728 = 1 + 360 / 73728 := by norm_num
  have hlog_ratio_hi : Real.log ((42 : ℝ) ^ 3 / 73728) ≤ 360 / 73728 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (360 / 73728) / (1 + 360 / 73728) ≤ Real.log ((42 : ℝ) ^ 3 / 73728) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((42 : ℝ) ^ 3) = 3 * Real.log 42 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((42 : ℝ) ^ 3 / 73728) = Real.log ((42 : ℝ) ^ 3) - Real.log 73728 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 42| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have hr_le : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi) - (-3224 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 42 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 42) hx 6 ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 42) hx 6 ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) (-3224 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) (-3224 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [hr_le])
  have hrem_s : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.sin ((10 : ℝ) * Real.log 42) - (((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
  have hb_s : |(((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((-3224 / 10000 : ℝ) - (-3224 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 42) - ((-3224 / 10000 : ℝ) - (-3224 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_s hb_s (by linarith [hrem_s])
  have ha_c : |Real.cos ((10 : ℝ) * Real.log 42) - (1 - 2 * (((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
  have hb_c : |(1 - 2 * (((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 42 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-3224 / 10000 : ℝ) / 2 - ((-3224 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 42) - (1 - 2 * ((-3224 / 10000 : ℝ) / 2 - ((-3224 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_c hb_c (by linarith [hrem_c])
  have hre := dp_cpow10_re 42 (by norm_num)
  have him := dp_cpow10_im 42 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 42)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 42)
  have hcenter_re : |(1543 / 10000 : ℝ) * (1 - 2 * ((-3224 / 10000 : ℝ) / 2 - ((-3224 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1464 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1543 / 10000 : ℝ) * ((-3224 / 10000 : ℝ) - (-3224 / 10000 : ℝ) ^ 3 / 6) - (-489 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((42 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1464 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c42 : ℂ)).re = 1464 / 10000 := by simp [dp_headB_c42]
    rw [hre]
    have ha0 : |(1543 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(42 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 42) - 1543 / 10000 * (1 - 2 * ((-3224 / 10000 : ℝ) / 2 - ((-3224 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((42 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-489 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c42 : ℂ)).im = -489 / 10000 := by simp [dp_headB_c42]
    rw [him]
    have ha0 : |(1543 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(42 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 42) - 1543 / 10000 * ((-3224 / 10000 : ℝ) - (-3224 / 10000 : ℝ) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((42 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c42 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n43_tight : ‖(((43 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c43‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6557 / 1000 : ℝ) ≤ Real.sqrt 43 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 43 ≤ (6558 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 43 (6557 / 1000) (6558 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(43 : ℝ) ^ (-1 / 2 : ℝ) - 1525 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (78732 : ℝ) = 2 * Real.log 2 + 9 * Real.log 3 := by have h1 : (78732 : ℝ) = 2 ^ 2 * 3 ^ 9 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (43 : ℝ) ^ 3 := by norm_num
  have hm_pos : (0 : ℝ) < (78732 : ℝ) := by norm_num
  have hratio_eq : (43 : ℝ) ^ 3 / 78732 = 1 + 775 / 78732 := by norm_num
  have hlog_ratio_hi : Real.log ((43 : ℝ) ^ 3 / 78732) ≤ 775 / 78732 := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (775 / 78732) / (1 + 775 / 78732) ≤ Real.log ((43 : ℝ) ^ 3 / 78732) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((43 : ℝ) ^ 3) = 3 * Real.log 43 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((43 : ℝ) ^ 3 / 78732) = Real.log ((43 : ℝ) ^ 3) - Real.log 78732 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 43| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have hr_le : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi) - (-871 / 10000)| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 43 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 43) hx 6 ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 43) hx 6 ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) (-871 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) (-871 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [hr_le])
  have hrem_s : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.sin ((10 : ℝ) * Real.log 43) - (((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
  have hb_s : |(((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((-871 / 10000 : ℝ) - (-871 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 43) - ((-871 / 10000 : ℝ) - (-871 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_s hb_s (by linarith [hrem_s])
  have ha_c : |Real.cos ((10 : ℝ) * Real.log 43) - (1 - 2 * (((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
  have hb_c : |(1 - 2 * (((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 43 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-871 / 10000 : ℝ) / 2 - ((-871 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 43) - (1 - 2 * ((-871 / 10000 : ℝ) / 2 - ((-871 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_c hb_c (by linarith [hrem_c])
  have hre := dp_cpow10_re 43 (by norm_num)
  have him := dp_cpow10_im 43 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 43)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 43)
  have hcenter_re : |(1525 / 10000 : ℝ) * (1 - 2 * ((-871 / 10000 : ℝ) / 2 - ((-871 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1519 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1525 / 10000 : ℝ) * ((-871 / 10000 : ℝ) - (-871 / 10000 : ℝ) ^ 3 / 6) - (-133 / 10000)| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((43 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1519 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c43 : ℂ)).re = 1519 / 10000 := by simp [dp_headB_c43]
    rw [hre]
    have ha0 : |(1525 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(43 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 43) - 1525 / 10000 * (1 - 2 * ((-871 / 10000 : ℝ) / 2 - ((-871 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((43 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-133 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c43 : ℂ)).im = -133 / 10000 := by simp [dp_headB_c43]
    rw [him]
    have ha0 : |(1525 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(43 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 43) - 1525 / 10000 * ((-871 / 10000 : ℝ) - (-871 / 10000 : ℝ) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((43 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c43 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]

theorem dp_headB_n44_tight : ‖(((44 : ℝ) : ℂ)) ^ (-dp_s0_10) - dp_headB_c44‖ ≤ 1 / 100 := by
  have hlog2_lo := dp_log2_lo
  have hlog2_hi := dp_log2_hi
  have hlog3_lo := dp_log3_lo
  have hlog3_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hsqrt_lo : (6633 / 1000 : ℝ) ≤ Real.sqrt 44 := by apply Real.le_sqrt_of_sq_le; norm_num
  have hsqrt_hi : Real.sqrt 44 ≤ (6634 / 1000 : ℝ) := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hamp_b := headB_amp_of_sqrt_bounds 44 (6633 / 1000) (6634 / 1000) (by norm_num) (by norm_num) hsqrt_lo hsqrt_hi
  have hamp_close : |(44 : ℝ) ^ (-1 / 2 : ℝ) - 1508 / 10000| ≤ 2 / 10000 := by rw [abs_le]; constructor <;> linarith [hamp_b.1, hamp_b.2]
  have hlogm : Real.log (1944 : ℝ) = 3 * Real.log 2 + 5 * Real.log 3 := by have h1 : (1944 : ℝ) = 2 ^ 3 * 3 ^ 5 := by norm_num; rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have hpe_pos : (0 : ℝ) < (44 : ℝ) ^ 2 := by norm_num
  have hm_pos : (0 : ℝ) < (1944 : ℝ) := by norm_num
  have hratio_eq : (44 : ℝ) ^ 2 / 1944 = 1 + (-8 / 1944) := by norm_num
  have hlog_ratio_hi : Real.log ((44 : ℝ) ^ 2 / 1944) ≤ (-8 / 1944) := by rw [hratio_eq]; exact headB_log1p_hi _ (by norm_num)
  have hlog_ratio_lo : (-8 / 1944) / (1 + (-8 / 1944)) ≤ Real.log ((44 : ℝ) ^ 2 / 1944) := by rw [hratio_eq]; exact headB_log1p_lo _ (by norm_num)
  have hlogpe : Real.log ((44 : ℝ) ^ 2) = 2 * Real.log 44 := by rw [Real.log_pow]
  have hlogdiv : Real.log ((44 : ℝ) ^ 2 / 1944) = Real.log ((44 : ℝ) ^ 2) - Real.log 1944 := by exact Real.log_div (ne_of_gt hpe_pos) (ne_of_gt hm_pos)
  have hx : |(10 : ℝ) * Real.log 44| ≤ 40 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi]
  have hr_le : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi) - 1428 / 10000| ≤ 50 / 10000 := by rw [abs_le]; constructor <;> linarith [hlog2_lo, hlog2_hi, hlog3_lo, hlog3_hi, hlogm, hlogpe, hlogdiv, hlog_ratio_lo, hlog_ratio_hi, hpi_lo, hpi_hi]
  have hrdef : (10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi) = (10 : ℝ) * Real.log 44 - ((6 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 44) hx 6 ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) hrdef hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 44) hx 6 ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) hrdef hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) (1428 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) (1428 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow5 : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith [hr_le])
  have hrem_s : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ 1 / 100 := by have hle : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 100 = 1 / 100 := by norm_num; linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ 1 / 800 := by have hle : |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 800 ≤ (1 : ℝ) ^ 5 / 800 := by apply div_le_div_of_nonneg_right hpow5 (by norm_num); have h0 : (1 : ℝ) ^ 5 / 800 = 1 / 800 := by norm_num; linarith [hle, h0]
  have ha_s : |Real.sin ((10 : ℝ) * Real.log 44) - (((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 100 := by rw [abs_le]; constructor <;> linarith [hs_lo, hs_lo_eq, hs_hi, hs_hi_eq]
  have hb_s : |(((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) ^ 3 / 6) - ((1428 / 10000 : ℝ) - (1428 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [hlip_s, hmul]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 44) - ((1428 / 10000 : ℝ) - (1428 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 100 + 3 / 2 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_s hb_s (by linarith [hrem_s])
  have ha_c : |Real.cos ((10 : ℝ) * Real.log 44) - (1 - 2 * (((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)| ^ 5 / 800 := by rw [abs_le]; constructor <;> linarith [hc_lo, hc_lo_eq, hc_hi, hc_hi_eq]
  have hb_c : |(1 - 2 * (((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 44 - 6 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((1428 / 10000 : ℝ) / 2 - ((1428 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (50 / 10000) := by have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3); linarith [hlip_c, hmul]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 44) - (1 - 2 * ((1428 / 10000 : ℝ) / 2 - ((1428 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 800 + 3 * (50 / 10000) := dp_abs_tri _ _ _ _ _ _ ha_c hb_c (by linarith [hrem_c])
  have hre := dp_cpow10_re 44 (by norm_num)
  have him := dp_cpow10_im 44 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 44)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 44)
  have hcenter_re : |(1508 / 10000 : ℝ) * (1 - 2 * ((1428 / 10000 : ℝ) / 2 - ((1428 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 1492 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(1508 / 10000 : ℝ) * ((1428 / 10000 : ℝ) - (1428 / 10000 : ℝ) ^ 3 / 6) - 215 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((44 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1492 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_headB_c44 : ℂ)).re = 1492 / 10000 := by simp [dp_headB_c44]
    rw [hre]
    have ha0 : |(1508 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(44 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 44) - 1508 / 10000 * (1 - 2 * ((1428 / 10000 : ℝ) / 2 - ((1428 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 2 / 10000 * 1 + 1 * (1 / 800 + 3 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hcos_close ha0 hcos_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((44 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (215 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_headB_c44 : ℂ)).im = 215 / 10000 := by simp [dp_headB_c44]
    rw [him]
    have ha0 : |(1508 / 10000 : ℝ)| ≤ 1 := by norm_num
    have e1 : |(44 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 44) - 1508 / 10000 * ((1428 / 10000 : ℝ) - (1428 / 10000 : ℝ) ^ 3 / 6)| ≤ 2 / 10000 * 1 + 1 * (1 / 100 + 3 / 2 * (50 / 10000)) := headB_mul_close _ _ _ _ _ _ (by norm_num) hamp_close hsin_close ha0 hsin_le1
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((44 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_headB_c44 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
