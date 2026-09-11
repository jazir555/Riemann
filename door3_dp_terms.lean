import Mathlib
import door3_dp_trig
theorem dp_cos_enclose_of_reduced (x : ℝ) (hx : |x| ≤ 40) (k : ℤ) (r : ℝ) (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hred : |r| ≤ 1) : ∃ lo hi : ℝ, lo = 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - |r| ^ 5 / 800 ∧ hi = 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + |r| ^ 5 / 800 ∧ lo ≤ Real.cos x ∧ Real.cos x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧ Real.cos x = Real.cos r := by
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  have habs2 : |r / 2| = |r| / 2 := by rw [abs_div, h2abs]
  have hu2 : |r / 2| ≤ 1 / 2 := by rw [habs2]; linarith
  have hu : |r / 2| ≤ 1 := by linarith
  have hB := Real.sin_bound hu
  have hmem := abs_le.mp hB
  have hcos_r : Real.cos r = Real.cos x := by rw [hrdef]; exact dp_cos_reduce x k
  have hcos_eq : Real.cos x = Real.cos r := hcos_r.symm
  have hcos_half : Real.cos r = 1 - 2 * Real.sin (r / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (r / 2)
    have e : 2 * (r / 2) = r := by ring
    rw [e] at h
    exact h
  have hpow5 : |r / 2| ^ 5 = |r| ^ 5 / 32 := by rw [habs2]; ring
  have heq4 : 4 * (|r / 2| ^ 5 / 100) = |r| ^ 5 / 800 := by rw [hpow5]; ring
  have hsin_abs : |Real.sin (r / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h3le : |r / 2| ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ (abs_nonneg (r / 2)) hu2 3
    have e : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
    rw [e] at h
    exact h
  have habs_pow : |(r / 2) ^ 3 / 6| = |r / 2| ^ 3 / 6 := by
    rw [abs_div, abs_pow]
    norm_num
  have hsub_eq : r / 2 - (r / 2) ^ 3 / 6 = r / 2 + (-((r / 2) ^ 3 / 6)) := by ring
  have hs0_le : |r / 2 - (r / 2) ^ 3 / 6| ≤ 1 := by
    have e : |r / 2 - (r / 2) ^ 3 / 6| = |r / 2 + (-((r / 2) ^ 3 / 6))| := by rw [hsub_eq]
    rw [e]
    have hle : |r / 2 + (-((r / 2) ^ 3 / 6))| ≤ |r / 2| + |-((r / 2) ^ 3 / 6)| := abs_add_le _ _
    have habs_neg : |-((r / 2) ^ 3 / 6)| = |(r / 2) ^ 3 / 6| := abs_neg _
    rw [habs_neg, habs_pow] at hle
    linarith
  have hsum : |Real.sin (r / 2) + (r / 2 - (r / 2) ^ 3 / 6)| ≤ 2 := by
    have h := abs_add_le (Real.sin (r / 2)) (r / 2 - (r / 2) ^ 3 / 6)
    linarith
  have he_nonneg : (0 : ℝ) ≤ |r / 2| ^ 5 / 100 := div_nonneg (pow_nonneg (abs_nonneg _) _) (by norm_num)
  have hdiff_le : |Real.sin (r / 2) - (r / 2 - (r / 2) ^ 3 / 6)| ≤ |r / 2| ^ 5 / 100 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  have hsq_eq : Real.sin (r / 2) ^ 2 - (r / 2 - (r / 2) ^ 3 / 6) ^ 2 = (Real.sin (r / 2) - (r / 2 - (r / 2) ^ 3 / 6)) * (Real.sin (r / 2) + (r / 2 - (r / 2) ^ 3 / 6)) := by ring
  have hsq_abs : |Real.sin (r / 2) ^ 2 - (r / 2 - (r / 2) ^ 3 / 6) ^ 2| = |Real.sin (r / 2) - (r / 2 - (r / 2) ^ 3 / 6)| * |Real.sin (r / 2) + (r / 2 - (r / 2) ^ 3 / 6)| := by rw [hsq_eq, abs_mul]
  have hsq_le : |Real.sin (r / 2) ^ 2 - (r / 2 - (r / 2) ^ 3 / 6) ^ 2| ≤ (|r / 2| ^ 5 / 100) * 2 := by
    rw [hsq_abs]
    exact mul_le_mul hdiff_le hsum (abs_nonneg _) he_nonneg
  have hsq_mem := abs_le.mp hsq_le
  have hpow1 : |r| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) hred
  have hwidth : (1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + |r| ^ 5 / 800) - (1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - |r| ^ 5 / 800) ≤ 1 / 50 := by linarith
  refine ⟨1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - |r| ^ 5 / 800, 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + |r| ^ 5 / 800, rfl, rfl, ?_, ?_, ?_, hcos_eq⟩
  · have hlo : 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - 4 * (|r / 2| ^ 5 / 100) ≤ Real.cos r := by linarith [hcos_half, hsq_mem.1]
    have e : 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - |r| ^ 5 / 800 = 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - 4 * (|r / 2| ^ 5 / 100) := by rw [heq4]
    rw [e]
    rw [hcos_eq]
    exact hlo
  · have hhi : Real.cos r ≤ 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + 4 * (|r / 2| ^ 5 / 100) := by linarith [hcos_half, hsq_mem.2]
    have e : 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + |r| ^ 5 / 800 = 1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2 + 4 * (|r / 2| ^ 5 / 100) := by rw [heq4]
    rw [e]
    rw [hcos_eq]
    exact hhi
  · exact hwidth
noncomputable def dp_s0 : ℂ := ⟨1 / 2, -(7 / 10)⟩
theorem dp_cpow_re (x : ℝ) (hx : 0 < x) : ((((x : ℂ)) ^ (-dp_s0))).re = x ^ (-1 / 2 : ℝ) * Real.cos ((7 / 10) * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) := (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-dp_s0).re = (-1 / 2 : ℝ) := by
    simp [dp_s0]
    norm_num
  have him_w : (-dp_s0).im = (7 / 10 : ℝ) := by simp [dp_s0]
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0)).re = Real.log x * (-1 / 2) := by rw [Complex.mul_re, hzre, hzim, hre_w]; ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0)).im = Real.log x * (7 / 10) := by rw [Complex.mul_im, hzre, hzim, him_w]; ring
  have hexp : Real.exp (Real.log x * (-1 / 2)) = x ^ (-1 / 2 : ℝ) := (Real.rpow_def_of_pos hx _).symm
  have hcos : Real.cos (Real.log x * (7 / 10)) = Real.cos ((7 / 10) * Real.log x) := by rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]
theorem dp_cpow_im (x : ℝ) (hx : 0 < x) : ((((x : ℂ)) ^ (-dp_s0))).im = x ^ (-1 / 2 : ℝ) * Real.sin ((7 / 10) * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) := (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-dp_s0).re = (-1 / 2 : ℝ) := by
    simp [dp_s0]
    norm_num
  have him_w : (-dp_s0).im = (7 / 10 : ℝ) := by simp [dp_s0]
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0)).re = Real.log x * (-1 / 2) := by rw [Complex.mul_re, hzre, hzim, hre_w]; ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0)).im = Real.log x * (7 / 10) := by rw [Complex.mul_im, hzre, hzim, him_w]; ring
  have hexp : Real.exp (Real.log x * (-1 / 2)) = x ^ (-1 / 2 : ℝ) := (Real.rpow_def_of_pos hx _).symm
  have hsin : Real.sin (Real.log x * (7 / 10)) = Real.sin ((7 / 10) * Real.log x) := by rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]
theorem dp_log2_lo : 6931 / 10000 ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith
theorem dp_log2_hi : Real.log 2 ≤ 6932 / 10000 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith
theorem dp_log3_lo : 10986 / 10000 ≤ Real.log 3 := by
  have h := Real.log_three_gt_d9
  norm_num at h ⊢
  linarith
theorem dp_log3_hi : Real.log 3 ≤ 10987 / 10000 := by
  have h := Real.log_three_lt_d9
  norm_num at h ⊢
  linarith
theorem dp_sqrt2_lo : 14141 / 10000 ≤ Real.sqrt 2 := by
  apply Real.le_sqrt_of_sq_le
  norm_num
theorem dp_sqrt2_hi : Real.sqrt 2 ≤ 14143 / 10000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num
theorem dp_sqrt3_lo : 1732 / 1000 ≤ Real.sqrt 3 := by
  apply Real.le_sqrt_of_sq_le
  norm_num
theorem dp_sqrt3_hi : Real.sqrt 3 ≤ 1733 / 1000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num
theorem dp_norm_of_re_im (z : ℂ) (C : ℂ) (e1 e2 : ℝ) (hre : |z.re - C.re| ≤ e1) (him : |z.im - C.im| ≤ e2) : ‖z - C‖ ≤ e1 + e2 := by
  have heq : ((z - C).re : ℂ) + (z - C).im * Complex.I = z - C := Complex.re_add_im _
  have hle : ‖((z - C).re : ℂ) + (z - C).im * Complex.I‖ ≤ e1 + e2 := by
    calc ‖((z - C).re : ℂ) + (z - C).im * Complex.I‖ ≤ ‖((z - C).re : ℂ)‖ + ‖(z - C).im * Complex.I‖ := norm_add_le _ _
      _ = |(z - C).re| + |(z - C).im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ = |z.re - C.re| + |z.im - C.im| := by rw [Complex.sub_re, Complex.sub_im]
      _ ≤ e1 + e2 := add_le_add hre him
  rw [heq] at hle
  exact hle
theorem dp_term_disc : ‖((((2 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 ∧ ‖((((3 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 ∧ ‖((((4 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 := by
  have hx2 : |(7 / 10) * Real.log 2| ≤ 40 := by rw [abs_le]; constructor <;> linarith [dp_log2_lo, dp_log2_hi]
  have hx3 : |(7 / 10) * Real.log 3| ≤ 40 := by rw [abs_le]; constructor <;> linarith [dp_log3_lo, dp_log3_hi]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hx4 : |(7 / 10) * Real.log 4| ≤ 40 := by rw [abs_le]; constructor <;> linarith [dp_log2_lo, dp_log2_hi, hlog4]
  have hred2 := dp_arg_reduce_mem ((7 / 10) * Real.log 2) hx2
  have hsqrt4 : Real.sqrt 4 = 2 := by
    have h42 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h42]
    rw [Real.sqrt_sq (by norm_num)]
  have hamp2_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hamp2_le1 : (2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    have hsqrt_eq : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (2 : ℝ) ^ (-1 / 2 : ℝ) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by linarith [dp_sqrt2_lo]
    exact inv_le_one_of_one_le₀ h1
  have hamp3_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hamp3_le1 : (3 : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    have hsqrt_eq : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 3
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (3 : ℝ) ^ (-1 / 2 : ℝ) = ((3 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by linarith [dp_sqrt3_lo]
    exact inv_le_one_of_one_le₀ h1
  have hamp4 : (4 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 2 := by
    have hsqrt_eq : Real.sqrt 4 = (4 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 4
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (4 : ℝ) ^ (-1 / 2 : ℝ) = ((4 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq, hsqrt4]
    norm_num
  have h2 : ‖((((2 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 := by
    have hre := dp_cpow_re 2 (by norm_num)
    have him := dp_cpow_im 2 (by norm_num)
    have hsin := Real.abs_sin_le_one ((7 / 10) * Real.log 2)
    have hcos := Real.abs_cos_le_one ((7 / 10) * Real.log 2)
    have hamp_abs : |(2 : ℝ) ^ (-1 / 2 : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [hamp2_nonneg], hamp2_le1⟩
    have hre1 : |((((((2 : ℝ) : ℂ)) ^ (-dp_s0))).re - (0 : ℂ).re)| ≤ 1 := by rw [Complex.zero_re, sub_zero, hre, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hcos
    have him1 : |((((((2 : ℝ) : ℂ)) ^ (-dp_s0))).im - (0 : ℂ).im)| ≤ 1 := by rw [Complex.zero_im, sub_zero, him, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hsin
    have h := dp_norm_of_re_im ((((2 : ℝ) : ℂ)) ^ (-dp_s0)) 0 1 1 hre1 him1
    linarith [h]
  have h3 : ‖((((3 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 := by
    have hre := dp_cpow_re 3 (by norm_num)
    have him := dp_cpow_im 3 (by norm_num)
    have hsin := Real.abs_sin_le_one ((7 / 10) * Real.log 3)
    have hcos := Real.abs_cos_le_one ((7 / 10) * Real.log 3)
    have hamp_abs : |(3 : ℝ) ^ (-1 / 2 : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [hamp3_nonneg], hamp3_le1⟩
    have hre1 : |((((((3 : ℝ) : ℂ)) ^ (-dp_s0))).re - (0 : ℂ).re)| ≤ 1 := by rw [Complex.zero_re, sub_zero, hre, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hcos
    have him1 : |((((((3 : ℝ) : ℂ)) ^ (-dp_s0))).im - (0 : ℂ).im)| ≤ 1 := by rw [Complex.zero_im, sub_zero, him, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hsin
    have h := dp_norm_of_re_im ((((3 : ℝ) : ℂ)) ^ (-dp_s0)) 0 1 1 hre1 him1
    linarith [h]
  have h4 : ‖((((4 : ℝ) : ℂ)) ^ (-dp_s0)) - 0‖ ≤ 2 := by
    have hre := dp_cpow_re 4 (by norm_num)
    have him := dp_cpow_im 4 (by norm_num)
    have hsin := Real.abs_sin_le_one ((7 / 10) * Real.log 4)
    have hcos := Real.abs_cos_le_one ((7 / 10) * Real.log 4)
    have hamp_nonneg : (0 : ℝ) ≤ (4 : ℝ) ^ (-1 / 2 : ℝ) := by rw [hamp4]; norm_num
    have hamp_le1 : (4 : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by rw [hamp4]; norm_num
    have hamp_abs : |(4 : ℝ) ^ (-1 / 2 : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [hamp_nonneg], hamp_le1⟩
    have hre1 : |((((((4 : ℝ) : ℂ)) ^ (-dp_s0))).re - (0 : ℂ).re)| ≤ 1 := by rw [Complex.zero_re, sub_zero, hre, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hcos
    have him1 : |((((((4 : ℝ) : ℂ)) ^ (-dp_s0))).im - (0 : ℂ).im)| ≤ 1 := by rw [Complex.zero_im, sub_zero, him, abs_mul]; exact mul_le_one₀ hamp_abs (abs_nonneg _) hsin
    have h := dp_norm_of_re_im ((((4 : ℝ) : ℂ)) ^ (-dp_s0)) 0 1 1 hre1 him1
    linarith [h]
  exact ⟨h2, h3, h4⟩
theorem dp_S4_Im_lower : (0 : ℝ) ≤ |((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0)) + ((((4 : ℝ) : ℂ)) ^ (-dp_s0))).im| := by exact abs_nonneg _
noncomputable def dp_s0_10 : ℂ := ⟨(1 / 2 : ℝ), (-10 : ℝ)⟩
noncomputable def dp_c2 : ℂ := ⟨(5636 / 10000 : ℝ), (4269 / 10000 : ℝ)⟩
noncomputable def dp_c3 : ℂ := ⟨(-54 / 10000 : ℝ), (-5773 / 10000 : ℝ)⟩
noncomputable def dp_c4 : ℂ := ⟨(1353 / 10000 : ℝ), (4813 / 10000 : ℝ)⟩
theorem dp_cpow10_re (x : ℝ) (hx : 0 < x) : ((((x : ℂ)) ^ (-dp_s0_10))).re = x ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) := (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-dp_s0_10).re = (-1 / 2 : ℝ) := by
    simp [dp_s0_10]
    norm_num
  have him_w : (-dp_s0_10).im = (10 : ℝ) := by simp [dp_s0_10]
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0_10)).re = Real.log x * (-1 / 2) := by rw [Complex.mul_re, hzre, hzim, hre_w]; ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0_10)).im = Real.log x * (10 : ℝ) := by rw [Complex.mul_im, hzre, hzim, him_w]; ring
  have hexp : Real.exp (Real.log x * (-1 / 2)) = x ^ (-1 / 2 : ℝ) := (Real.rpow_def_of_pos hx _).symm
  have hcos : Real.cos (Real.log x * (10 : ℝ)) = Real.cos (10 * Real.log x) := by rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]
theorem dp_cpow10_im (x : ℝ) (hx : 0 < x) : ((((x : ℂ)) ^ (-dp_s0_10))).im = x ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) := (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-dp_s0_10).re = (-1 / 2 : ℝ) := by
    simp [dp_s0_10]
    norm_num
  have him_w : (-dp_s0_10).im = (10 : ℝ) := by simp [dp_s0_10]
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0_10)).re = Real.log x * (-1 / 2) := by rw [Complex.mul_re, hzre, hzim, hre_w]; ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-dp_s0_10)).im = Real.log x * (10 : ℝ) := by rw [Complex.mul_im, hzre, hzim, him_w]; ring
  have hexp : Real.exp (Real.log x * (-1 / 2)) = x ^ (-1 / 2 : ℝ) := (Real.rpow_def_of_pos hx _).symm
  have hsin : Real.sin (Real.log x * (10 : ℝ)) = Real.sin (10 * Real.log x) := by rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]
theorem dp_poly_lip (r c : ℝ) (hr : |r| ≤ 1) (hc : |c| ≤ 1) : |(r - r ^ 3 / 6) - (c - c ^ 3 / 6)| ≤ 3 / 2 * |r - c| := by
  have hfac : (r - r ^ 3 / 6) - (c - c ^ 3 / 6) = (r - c) * (1 - (r ^ 2 + r * c + c ^ 2) / 6) := by ring
  rw [hfac, abs_mul]
  have hr2 : |r ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hr
  have hc2 : |c ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hc
  have hrc : |r * c| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hr (abs_nonneg _) hc
  have hS : |r ^ 2 + r * c + c ^ 2| ≤ 3 := by
    have h1 := abs_add_le (r ^ 2 + r * c) (c ^ 2)
    have h2 := abs_add_le (r ^ 2) (r * c)
    linarith [hr2, hc2, hrc, h1, h2]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  have hdiv : |(r ^ 2 + r * c + c ^ 2) / 6| = |r ^ 2 + r * c + c ^ 2| / 6 := by rw [abs_div, h6]
  have hdiv_le : |(r ^ 2 + r * c + c ^ 2) / 6| ≤ 1 / 2 := by rw [hdiv]; linarith [hS]
  have hone : |1 - (r ^ 2 + r * c + c ^ 2) / 6| ≤ 3 / 2 := by
    have heq : (1 : ℝ) - (r ^ 2 + r * c + c ^ 2) / 6 = 1 + (-((r ^ 2 + r * c + c ^ 2) / 6)) := by ring
    rw [heq]
    have htri := abs_add_le (1 : ℝ) (-((r ^ 2 + r * c + c ^ 2) / 6))
    have habs1 : |(1 : ℝ)| = 1 := by norm_num
    have habsneg : |-((r ^ 2 + r * c + c ^ 2) / 6)| = |(r ^ 2 + r * c + c ^ 2) / 6| := abs_neg _
    rw [habs1, habsneg] at htri
    linarith [htri, hdiv_le]
  have hmul := mul_le_mul_of_nonneg_left hone (abs_nonneg (r - c))
  have heq2 : |r - c| * (3 / 2) = 3 / 2 * |r - c| := by ring
  linarith [hmul, heq2]
theorem dp_cos_poly_lip (r c : ℝ) (hr : |r| ≤ 1) (hc : |c| ≤ 1) : |(1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (c / 2 - (c / 2) ^ 3 / 6) ^ 2)| ≤ 3 * |r - c| := by
  have er : |r / 2| = |r| / 2 := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
  have ec : |c / 2| = |c| / 2 := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
  have hrh : |r / 2| ≤ 1 := by rw [er]; linarith [hr]
  have hch : |c / 2| ≤ 1 := by rw [ec]; linarith [hc]
  have hlip := dp_poly_lip (r / 2) (c / 2) hrh hch
  have ediv : r / 2 - c / 2 = (r - c) / 2 := by ring
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  have eabs : |r / 2 - c / 2| = |r - c| / 2 := by rw [ediv, abs_div, h2]
  have hsc_le : |r / 2 - (r / 2) ^ 3 / 6 - (c / 2 - (c / 2) ^ 3 / 6)| ≤ 3 / 4 * |r - c| := by linarith [hlip, eabs]
  have hr_half : |r / 2| ≤ 1 / 2 := by rw [er]; linarith [hr]
  have hc_half : |c / 2| ≤ 1 / 2 := by rw [ec]; linarith [hc]
  have hr3 : |r / 2| ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ (abs_nonneg (r / 2)) hr_half 3
    have e : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
    rw [e] at h
    exact h
  have hc3 : |c / 2| ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ (abs_nonneg (c / 2)) hc_half 3
    have e : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
    rw [e] at h
    exact h
  have hpr : |(r / 2) ^ 3 / 6| = |r / 2| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have hpc : |(c / 2) ^ 3 / 6| = |c / 2| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have hsr : |r / 2 - (r / 2) ^ 3 / 6| ≤ 1 := by
    have heq : r / 2 - (r / 2) ^ 3 / 6 = r / 2 + (-((r / 2) ^ 3 / 6)) := by ring
    rw [heq]
    have hle := abs_add_le (r / 2) (-((r / 2) ^ 3 / 6))
    have hn : |-((r / 2) ^ 3 / 6)| = |(r / 2) ^ 3 / 6| := abs_neg _
    rw [hn, hpr] at hle
    linarith [hle, hr_half, hr3]
  have hsc : |c / 2 - (c / 2) ^ 3 / 6| ≤ 1 := by
    have heq : c / 2 - (c / 2) ^ 3 / 6 = c / 2 + (-((c / 2) ^ 3 / 6)) := by ring
    rw [heq]
    have hle := abs_add_le (c / 2) (-((c / 2) ^ 3 / 6))
    have hn : |-((c / 2) ^ 3 / 6)| = |(c / 2) ^ 3 / 6| := abs_neg _
    rw [hn, hpc] at hle
    linarith [hle, hc_half, hc3]
  have hsum : |r / 2 - (r / 2) ^ 3 / 6 + (c / 2 - (c / 2) ^ 3 / 6)| ≤ 2 := by
    have h := abs_add_le (r / 2 - (r / 2) ^ 3 / 6) (c / 2 - (c / 2) ^ 3 / 6)
    linarith [h, hsr, hsc]
  have hsq_eq : (r / 2 - (r / 2) ^ 3 / 6) ^ 2 - (c / 2 - (c / 2) ^ 3 / 6) ^ 2 = (r / 2 - (r / 2) ^ 3 / 6 - (c / 2 - (c / 2) ^ 3 / 6)) * (r / 2 - (r / 2) ^ 3 / 6 + (c / 2 - (c / 2) ^ 3 / 6)) := by ring
  have hsq_abs : |(r / 2 - (r / 2) ^ 3 / 6) ^ 2 - (c / 2 - (c / 2) ^ 3 / 6) ^ 2| = |r / 2 - (r / 2) ^ 3 / 6 - (c / 2 - (c / 2) ^ 3 / 6)| * |r / 2 - (r / 2) ^ 3 / 6 + (c / 2 - (c / 2) ^ 3 / 6)| := by rw [hsq_eq, abs_mul]
  have hsq_le : |(r / 2 - (r / 2) ^ 3 / 6) ^ 2 - (c / 2 - (c / 2) ^ 3 / 6) ^ 2| ≤ (3 / 4 * |r - c|) * 2 := by
    rw [hsq_abs]
    exact mul_le_mul hsc_le hsum (abs_nonneg _) (by norm_num)
  have hqfac : (1 - 2 * (r / 2 - (r / 2) ^ 3 / 6) ^ 2) - (1 - 2 * (c / 2 - (c / 2) ^ 3 / 6) ^ 2) = (-2) * ((r / 2 - (r / 2) ^ 3 / 6) ^ 2 - (c / 2 - (c / 2) ^ 3 / 6) ^ 2) := by ring
  rw [hqfac, abs_mul]
  have hn2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [hn2]
  have hmul := mul_le_mul_of_nonneg_left hsq_le (by norm_num : (0 : ℝ) ≤ 2)
  have heq3 : (2 : ℝ) * ((3 / 4 * |r - c|) * 2) = 3 * |r - c| := by ring
  linarith [hmul, heq3]
theorem dp_octant_sin_add_enclose (x r e : ℝ) (hx : |x| ≤ 40) (k : ℤ) (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hedef : e = r - Real.pi / 2) (hele : |e| ≤ 1) : ∃ lo hi : ℝ, lo = 1 - 2 * (e / 2 - (e / 2) ^ 3 / 6) ^ 2 - |e| ^ 5 / 800 ∧ hi = 1 - 2 * (e / 2 - (e / 2) ^ 3 / 6) ^ 2 + |e| ^ 5 / 800 ∧ lo ≤ Real.sin x ∧ Real.sin x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧ Real.sin x = Real.cos e := by
  have hsin_r : Real.sin x = Real.sin r := by rw [hrdef]; exact (dp_sin_reduce x k).symm
  have hr_eq : r = e + Real.pi / 2 := by linarith [hedef]
  have hsin_eq : Real.sin r = Real.cos e := by rw [hr_eq, Real.sin_add_pi_div_two]
  have hsx : Real.sin x = Real.cos e := by rw [hsin_r, hsin_eq]
  have he40 : |e| ≤ 40 := by linarith [hele]
  have hr0 : e = e - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, hcos_eq⟩ := dp_cos_enclose_of_reduced e he40 0 e hr0 hele
  refine ⟨lo, hi, hlo_eq, hhi_eq, by rw [hsx]; exact hlo, by rw [hsx]; exact hhi, hwidth, hsx⟩
theorem dp_octant_sin_sub_enclose (x r e : ℝ) (hx : |x| ≤ 40) (k : ℤ) (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hedef : e = r + Real.pi / 2) (hele : |e| ≤ 1) : ∃ lo hi : ℝ, lo = -(1 - 2 * (e / 2 - (e / 2) ^ 3 / 6) ^ 2 + |e| ^ 5 / 800) ∧ hi = -(1 - 2 * (e / 2 - (e / 2) ^ 3 / 6) ^ 2 - |e| ^ 5 / 800) ∧ lo ≤ Real.sin x ∧ Real.sin x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧ Real.sin x = -Real.cos e := by
  have hsin_r : Real.sin x = Real.sin r := by rw [hrdef]; exact (dp_sin_reduce x k).symm
  have hr_eq : r = e - Real.pi / 2 := by linarith [hedef]
  have hsin_eq : Real.sin r = -Real.cos e := by rw [hr_eq, Real.sin_sub_pi_div_two]
  have hsx : Real.sin x = -Real.cos e := by rw [hsin_r, hsin_eq]
  have he40 : |e| ≤ 40 := by linarith [hele]
  have hr0 : e = e - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by simp
  obtain ⟨lo_c, hi_c, hlo_eq, hhi_eq, hlo, hhi, hwidth, hcos_eq⟩ := dp_cos_enclose_of_reduced e he40 0 e hr0 hele
  refine ⟨-hi_c, -lo_c, by rw [hhi_eq], by rw [hlo_eq], by linarith [hlo, hhi, hsx], by linarith [hlo, hhi, hsx], by linarith [hwidth], hsx⟩
theorem dp_octant_cos_add_enclose (x r e : ℝ) (hx : |x| ≤ 40) (k : ℤ) (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hedef : e = r - Real.pi / 2) (hele : |e| ≤ 1) : ∃ lo hi : ℝ, lo = -(e - e ^ 3 / 6 + |e| ^ 5 / 100) ∧ hi = -(e - e ^ 3 / 6 - |e| ^ 5 / 100) ∧ lo ≤ Real.cos x ∧ Real.cos x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧ Real.cos x = -Real.sin e := by
  have hcos_r : Real.cos x = Real.cos r := by rw [hrdef]; exact (dp_cos_reduce x k).symm
  have hr_eq : r = e + Real.pi / 2 := by linarith [hedef]
  have hcos_eq2 : Real.cos r = -Real.sin e := by rw [hr_eq, Real.cos_add_pi_div_two]
  have hcx : Real.cos x = -Real.sin e := by rw [hcos_r, hcos_eq2]
  have he40 : |e| ≤ 40 := by linarith [hele]
  have hr0 : e = e - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by simp
  obtain ⟨lo_s, hi_s, hlo_eq, hhi_eq, hlo, hhi, hwidth, hsin_eq⟩ := dp_sin_enclose_of_reduced e he40 0 e hr0 hele
  refine ⟨-hi_s, -lo_s, by rw [hhi_eq], by rw [hlo_eq], by linarith [hlo, hhi, hcx], by linarith [hlo, hhi, hcx], by linarith [hwidth], hcx⟩
theorem dp_octant_cos_sub_enclose (x r e : ℝ) (hx : |x| ≤ 40) (k : ℤ) (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hedef : e = r + Real.pi / 2) (hele : |e| ≤ 1) : ∃ lo hi : ℝ, lo = e - e ^ 3 / 6 - |e| ^ 5 / 100 ∧ hi = e - e ^ 3 / 6 + |e| ^ 5 / 100 ∧ lo ≤ Real.cos x ∧ Real.cos x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧ Real.cos x = Real.sin e := by
  have hcos_r : Real.cos x = Real.cos r := by rw [hrdef]; exact (dp_cos_reduce x k).symm
  have hr_eq : r = e - Real.pi / 2 := by linarith [hedef]
  have hcos_eq2 : Real.cos r = Real.sin e := by rw [hr_eq, Real.cos_sub_pi_div_two]
  have hcx : Real.cos x = Real.sin e := by rw [hcos_r, hcos_eq2]
  have he40 : |e| ≤ 40 := by linarith [hele]
  have hr0 : e = e - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by simp
  obtain ⟨lo_s, hi_s, hlo_eq, hhi_eq, hlo, hhi, hwidth, hsin_eq⟩ := dp_sin_enclose_of_reduced e he40 0 e hr0 hele
  refine ⟨lo_s, hi_s, hlo_eq, hhi_eq, by rw [hcx]; exact hlo, by rw [hcx]; exact hhi, hwidth, hcx⟩
theorem dp_abs_tri (A B C b1 b2 b : ℝ) (e1 : |A - B| ≤ b1) (ec : |B - C| ≤ b2) (hb : b1 + b2 ≤ b) : |A - C| ≤ b := by
  have h := abs_add_le (A - B) (B - C)
  have heq : A - C = (A - B) + (B - C) := by ring
  rw [heq]
  linarith [h, e1, ec, hb]
theorem dp_term2_tight : ‖((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c2‖ ≤ 1 / 100 := by
  have hlog_lo := dp_log2_lo
  have hlog_hi := dp_log2_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx2 : |(10 : ℝ) * Real.log 2| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi]
    · linarith [hlog_lo, hlog_hi]
  have r2def : (10 : ℝ) * Real.log 2 - (1 : ℝ) * (2 * Real.pi) = (10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi) := by ring
  have hr_le : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hr_close : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi) - 6484 / 10000| ≤ 7 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hr_abs : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ≤ 649 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hrdef2 : (10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi) = (10 : ℝ) * Real.log 2 - ((1 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_sin_enclose_of_reduced ((10 : ℝ) * Real.log 2) hx2 1 ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) hrdef2 hr_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_cos_enclose_of_reduced ((10 : ℝ) * Real.log 2) hx2 1 ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) hrdef2 hr_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) (6484 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) (6484 / 10000 : ℝ) (by linarith [hr_le]) (by norm_num)
  have hpow_s : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 ≤ (649 / 1000 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hr_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 / 100 ≤ 12 / 10000 := by
    have h649 : (649 / 1000 : ℝ) ^ 5 / 100 ≤ 12 / 10000 := by norm_num
    linarith [hpow_s, h649]
  have hrem_c : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 / 800 ≤ 2 / 10000 := by
    have h649 : (649 / 1000 : ℝ) ^ 5 / 800 ≤ 2 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 / 800 ≤ (649 / 1000 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow_s (by norm_num)
    linarith [hle, h649]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 2) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)| ≤ 27 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 2) - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 / 100 := by
      rw [abs_le]
      constructor
      · linarith [hs_lo, hs_lo_eq]
      · linarith [hs_hi, hs_hi_eq]
    have h2 : |((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6 - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (7 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith [hlip_s, hmul]
    have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 2) - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6)) ((((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6))
    have heq : Real.sin ((10 : ℝ) * Real.log 2) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 2) - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) - ((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) ^ 3 / 6) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_s]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 23 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 2) - (1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)| ^ 5 / 800 := by
      rw [abs_le]
      constructor
      · linarith [hc_lo, hc_lo_eq]
      · linarith [hc_hi, hc_hi_eq]
    have h2 : |(1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (7 / 10000) := by
      have hmul := mul_le_mul_of_nonneg_left hr_close (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hlip_c, hmul]
    have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 2) - (1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2))
    have heq : Real.cos ((10 : ℝ) * Real.log 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 2) - (1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2 - (((10 : ℝ) * Real.log 2 - 1 * (2 * Real.pi)) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
    rw [← heq] at htri
    linarith [htri, h1, h2, hrem_c]
  have hsqrt_lo := dp_sqrt2_lo
  have hsqrt_hi := dp_sqrt2_hi
  have hamp_eq : (2 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    have hsqrt_eq : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (2 : ℝ) ^ (-1 / 2 : ℝ) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (707 / 1000 : ℝ) ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (14143 / 10000) ≤ 1 / Real.sqrt 2 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (707 / 1000 : ℝ) ≤ 1 / (14143 / 10000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (2 : ℝ) ^ (-1 / 2 : ℝ) ≤ (708 / 1000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 2 ≤ 1 / (14141 / 10000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (14141 / 10000) ≤ 708 / 1000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 2 (by norm_num)
  have him := dp_cpow10_im 2 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 2)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 2)
  have hcenter_re : |(7071 / 10000 : ℝ) * (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 5636 / 10000| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(7071 / 10000 : ℝ) * ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6) - 4269 / 10000| ≤ 1 / 1000 := by norm_num
  have hre_bound : |((((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (5636 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_c2 : ℂ)).re = 5636 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [hre]
    have ha0 : |(7071 / 10000 : ℝ)| ≤ 1 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 2)| ≤ 1 := hcos_le1
    have e1 : |(2 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 2) - 7071 / 10000 * (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 1000 * 1 + 1 * (23 / 10000) := by
      have hsplit : (2 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 2) - 7071 / 10000 * (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2) = ((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000) * Real.cos (10 * Real.log 2) + 7071 / 10000 * (Real.cos (10 * Real.log 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000) * Real.cos (10 * Real.log 2)) (7071 / 10000 * (Real.cos (10 * Real.log 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000)| * |Real.cos (10 * Real.log 2)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(7071 / 10000 : ℝ)| * |Real.cos (10 * Real.log 2) - (1 - 2 * ((6484 / 10000 : ℝ) / 2 - ((6484 / 10000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 * (23 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (4269 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_c2 : ℂ)).im = 4269 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [him]
    have ha0 : |(7071 / 10000 : ℝ)| ≤ 1 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 2)| ≤ 1 := hsin_le1
    have e1 : |(2 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 2) - 7071 / 10000 * ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 * (27 / 10000) := by
      have hsplit : (2 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 2) - 7071 / 10000 * ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6) = ((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000) * Real.sin (10 * Real.log 2) + 7071 / 10000 * (Real.sin (10 * Real.log 2) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000) * Real.sin (10 * Real.log 2)) (7071 / 10000 * (Real.sin (10 * Real.log 2) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((2 : ℝ) ^ (-1 / 2 : ℝ) - 7071 / 10000)| * |Real.sin (10 * Real.log 2)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(7071 / 10000 : ℝ)| * |Real.sin (10 * Real.log 2) - ((6484 / 10000 : ℝ) - (6484 / 10000 : ℝ) ^ 3 / 6)| ≤ 1 * (27 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_c2 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_term3_tight : ‖((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c3‖ ≤ 1 / 100 := by
  have hlog_lo := dp_log3_lo
  have hlog_hi := dp_log3_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx3 : |(10 : ℝ) * Real.log 3| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi]
    · linarith [hlog_lo, hlog_hi]
  have he_le : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2 - (-9 / 1000)| ≤ 8 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ≤ 1 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hpi_lo, hpi_hi]
  have hrdef3 : (10 : ℝ) * Real.log 3 - 2 * (2 * Real.pi) = (10 : ℝ) * Real.log 3 - ((2 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef3 : (10 : ℝ) * Real.log 3 - 7 * Real.pi / 2 = ((10 : ℝ) * Real.log 3 - 2 * (2 * Real.pi)) + Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_sub_enclose ((10 : ℝ) * Real.log 3) ((10 : ℝ) * Real.log 3 - 2 * (2 * Real.pi)) ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) hx3 2 hrdef3 hedef3 he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_sub_enclose ((10 : ℝ) * Real.log 3) ((10 : ℝ) * Real.log 3 - 2 * (2 * Real.pi)) ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) hx3 2 hrdef3 hedef3 he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) (-9 / 1000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) (-9 / 1000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 ≤ (1 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 10000 := by
    have h0 : (1 / 100 : ℝ) ^ 5 / 100 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 100 ≤ (1 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (1 / 100 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 800 ≤ (1 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 3) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ 34 / 10000 := by
    have hpoly : |(-Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2)) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))| = |Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| := by
      have e : (-Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2)) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) = -(Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [e, abs_neg]
    have h1 : |Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 10000 + 3 * (8 / 10000) := by
      have ha : |Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 800 := by
        rw [abs_le]
        constructor
        · linarith [hs_lo, hs_lo_eq, hs_eq]
        · linarith [hs_hi, hs_hi_eq, hs_eq]
      have hb : |(1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (8 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
        linarith [hlip_c, hmul]
      have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))
      have heq : Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_c]
    rw [hs_eq]
    linarith [hpoly, h1, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 3) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)| ≤ 22 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)| ≤ 1 / 10000 + 3 / 2 * (8 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 3 - 7 * Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (8 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - (((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) - ((10 : ℝ) * Real.log 3 - 7 * Real.pi / 2) ^ 3 / 6) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    rw [hc_eq]
    linarith [h1, hrem_s]
  have hsqrt_lo := dp_sqrt3_lo
  have hsqrt_hi := dp_sqrt3_hi
  have hamp_eq : (3 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 3)⁻¹ := by
    have hsqrt_eq : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 3
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (3 : ℝ) ^ (-1 / 2 : ℝ) = ((3 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    rw [hrw, ← hsqrt_eq]
  have hamp_lo : (577 / 1000 : ℝ) ≤ (3 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : (1 : ℝ) / (1733 / 1000) ≤ 1 / Real.sqrt 3 := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_hi
    have h2 : (577 / 1000 : ℝ) ≤ 1 / (1733 / 1000) := by norm_num
    linarith [h1, h2]
  have hamp_hi : (3 : ℝ) ^ (-1 / 2 : ℝ) ≤ (578 / 1000 : ℝ) := by
    rw [hamp_eq, inv_eq_one_div]
    have h1 : 1 / Real.sqrt 3 ≤ 1 / (1732 / 1000) := by
      apply one_div_le_one_div_of_le (by positivity) hsqrt_lo
    have h2 : (1 : ℝ) / (1732 / 1000) ≤ 578 / 1000 := by norm_num
    linarith [h1, h2]
  have hamp_close : |(3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000| ≤ 1 / 1000 := by
    rw [abs_le]
    constructor
    · linarith [hamp_lo, hamp_hi]
    · linarith [hamp_lo, hamp_hi]
  have hre := dp_cpow10_re 3 (by norm_num)
  have him := dp_cpow10_im 3 (by norm_num)
  have hsin_le1 := Real.abs_sin_le_one (10 * Real.log 3)
  have hcos_le1 := Real.abs_cos_le_one (10 * Real.log 3)
  have hcenter_re : |(5773 / 10000 : ℝ) * ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6) - (-54 / 10000)| ≤ 1 / 1000 := by norm_num
  have hcenter_im : |(5773 / 10000 : ℝ) * (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) - (-5773 / 10000)| ≤ 1 / 10000 := by norm_num
  have hre_bound : |((((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - ((-54 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_c3 : ℂ)).re = -54 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [hre]
    have ha0 : |(5773 / 10000 : ℝ)| ≤ 1 := by norm_num
    have hcos1 : |Real.cos (10 * Real.log 3)| ≤ 1 := hcos_le1
    have e1 : |(3 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 3) - 5773 / 10000 * ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)| ≤ 1 / 1000 * 1 + 1 * (22 / 10000) := by
      have hsplit : (3 : ℝ) ^ (-1 / 2 : ℝ) * Real.cos (10 * Real.log 3) - 5773 / 10000 * ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6) = ((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000) * Real.cos (10 * Real.log 3) + 5773 / 10000 * (Real.cos (10 * Real.log 3) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)) := by ring
      rw [hsplit]
      have htri := abs_add_le (((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000) * Real.cos (10 * Real.log 3)) (5773 / 10000 * (Real.cos (10 * Real.log 3) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000)| * |Real.cos (10 * Real.log 3)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hcos1 (abs_nonneg _) (by norm_num)
      have m2 : |(5773 / 10000 : ℝ)| * |Real.cos (10 * Real.log 3) - ((-9 / 1000 : ℝ) - (-9 / 1000 : ℝ) ^ 3 / 6)| ≤ 1 * (22 / 10000) := by
        exact mul_le_mul ha0 hcos_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - ((-5773 / 10000) : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_c3 : ℂ)).im = -5773 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [him]
    have ha0 : |(5773 / 10000 : ℝ)| ≤ 1 := by norm_num
    have hsin1 : |Real.sin (10 * Real.log 3)| ≤ 1 := hsin_le1
    have e1 : |(3 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 3) - 5773 / 10000 * (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ 1 / 1000 * 1 + 1 * (34 / 10000) := by
      have hsplit : (3 : ℝ) ^ (-1 / 2 : ℝ) * Real.sin (10 * Real.log 3) - 5773 / 10000 * (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) = ((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000) * Real.sin (10 * Real.log 3) + 5773 / 10000 * (Real.sin (10 * Real.log 3) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))) := by ring
      rw [hsplit]
      have htri := abs_add_le (((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000) * Real.sin (10 * Real.log 3)) (5773 / 10000 * (Real.sin (10 * Real.log 3) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))))
      rw [abs_mul, abs_mul] at htri
      have m1 : |((3 : ℝ) ^ (-1 / 2 : ℝ) - 5773 / 10000)| * |Real.sin (10 * Real.log 3)| ≤ (1 / 1000) * 1 := by
        exact mul_le_mul hamp_close hsin1 (abs_nonneg _) (by norm_num)
      have m2 : |(5773 / 10000 : ℝ)| * |Real.sin (10 * Real.log 3) - (-(1 - 2 * ((-9 / 1000 : ℝ) / 2 - ((-9 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))| ≤ 1 * (34 / 10000) := by
        exact mul_le_mul ha0 hsin_close (abs_nonneg _) (by norm_num)
      linarith [htri, m1, m2]
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_c3 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_term4_tight : ‖((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c4‖ ≤ 1 / 100 := by
  have hlog_lo := dp_log2_lo
  have hlog_hi := dp_log2_hi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hx4 : |(10 : ℝ) * Real.log 4| ≤ 40 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hlog4]
    · linarith [hlog_lo, hlog_hi, hlog4]
  have he_le : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
  have he_close : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2 - (-274 / 1000)| ≤ 13 / 10000 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
  have he_abs : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ≤ 28 / 100 := by
    rw [abs_le]
    constructor
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
    · linarith [hlog_lo, hlog_hi, hlog4, hpi_lo, hpi_hi]
  have hrdef4 : (10 : ℝ) * Real.log 4 - 2 * (2 * Real.pi) = (10 : ℝ) * Real.log 4 - ((2 : ℤ) : ℝ) * (2 * Real.pi) := by norm_num
  have hedef4 : (10 : ℝ) * Real.log 4 - 9 * Real.pi / 2 = ((10 : ℝ) * Real.log 4 - 2 * (2 * Real.pi)) - Real.pi / 2 := by ring
  obtain ⟨lo_s, hi_s, hs_lo_eq, hs_hi_eq, hs_lo, hs_hi, hs_w, hs_eq⟩ := dp_octant_sin_add_enclose ((10 : ℝ) * Real.log 4) ((10 : ℝ) * Real.log 4 - 2 * (2 * Real.pi)) ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) hx4 2 hrdef4 hedef4 he_le
  obtain ⟨lo_c, hi_c, hc_lo_eq, hc_hi_eq, hc_lo, hc_hi, hc_w, hc_eq⟩ := dp_octant_cos_add_enclose ((10 : ℝ) * Real.log 4) ((10 : ℝ) * Real.log 4 - 2 * (2 * Real.pi)) ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) hx4 2 hrdef4 hedef4 he_le
  have hlip_s := dp_poly_lip ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) (-274 / 1000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hlip_c := dp_cos_poly_lip ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) (-274 / 1000 : ℝ) (by linarith [he_le]) (by norm_num)
  have hpow : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 ≤ (28 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) he_abs 5
  have hrem_s : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 100 ≤ 1 / 10000 := by
    have h0 : (28 / 100 : ℝ) ^ 5 / 100 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 100 ≤ (28 / 100 : ℝ) ^ 5 / 100 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hrem_c : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 800 ≤ 1 / 10000 := by
    have h0 : (28 / 100 : ℝ) ^ 5 / 800 ≤ 1 / 10000 := by norm_num
    have hle : |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 800 ≤ (28 / 100 : ℝ) ^ 5 / 800 := by
      apply div_le_div_of_nonneg_right hpow (by norm_num)
    linarith [hle, h0]
  have hsin_close : |Real.sin ((10 : ℝ) * Real.log 4) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 49 / 10000 := by
    have h1 : |Real.cos ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 10000 + 3 * (13 / 10000) := by
      have ha : |Real.cos ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)| ≤ |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 800 := by
        rw [abs_le]
        constructor
        · linarith [hs_lo, hs_lo_eq, hs_eq]
        · linarith [hs_hi, hs_hi_eq, hs_eq]
      have hb : |(1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 3 * (13 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3)
        linarith [hlip_c, hmul]
      have htri := abs_add_le (Real.cos ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) ((1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2))
      have heq : Real.cos ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2) = (Real.cos ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2)) + ((1 - 2 * (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2 - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) / 2) ^ 3 / 6) ^ 2) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_c]
    rw [hs_eq]
    linarith [h1, hrem_c]
  have hcos_close : |Real.cos ((10 : ℝ) * Real.log 4) - (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6))| ≤ 30 / 10000 := by
    have h1 : |Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)| ≤ 1 / 10000 + 3 / 2 * (13 / 10000) := by
      have ha : |Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6)| ≤ |(10 : ℝ) * Real.log 4 - 9 * Real.pi / 2| ^ 5 / 100 := by
        rw [abs_le]
        constructor
        · linarith [hc_lo, hc_lo_eq, hc_eq]
        · linarith [hc_hi, hc_hi_eq, hc_eq]
      have hb : |(((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)| ≤ 3 / 2 * (13 / 10000) := by
        have hmul := mul_le_mul_of_nonneg_left he_close (by norm_num : (0 : ℝ) ≤ 3 / 2)
        linarith [hlip_s, hmul]
      have htri := abs_add_le (Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6)) ((((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6))
      have heq : Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6) = (Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - (((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6)) + ((((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) ^ 3 / 6) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)) := by ring
      rw [← heq] at htri
      linarith [htri, ha, hb, hrem_s]
    have hneg : |(-Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2)) - (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6))| = |Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)| := by
      have e : (-Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2)) - (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)) = -(Real.sin ((10 : ℝ) * Real.log 4 - 9 * Real.pi / 2) - ((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)) := by ring
      rw [e, abs_neg]
    rw [hc_eq]
    linarith [hneg, h1, hrem_s]
  have hamp4 : (4 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 2 := by
    have hsqrt_eq : Real.sqrt 4 = (4 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 4
    have e : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have hrw : (4 : ℝ) ^ (-1 / 2 : ℝ) = ((4 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [e]; exact Real.rpow_neg (by norm_num) _
    have hsqrt4 : Real.sqrt 4 = 2 := by
      have h42 : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h42]
      rw [Real.sqrt_sq (by norm_num)]
    rw [hrw, ← hsqrt_eq, hsqrt4]
    norm_num
  have hre := dp_cpow10_re 4 (by norm_num)
  have him := dp_cpow10_im 4 (by norm_num)
  have hcenter_re : |(1 / 2 : ℝ) * (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)) - 1353 / 10000| ≤ 1 / 10000 := by norm_num
  have hcenter_im : |(1 / 2 : ℝ) * (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2) - 4813 / 10000| ≤ 1 / 10000 := by norm_num
  have hre_bound : |((((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)))).re - (1353 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCre : ((dp_c4 : ℂ)).re = 1353 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [hre, hamp4]
    have e1 : |(1 / 2 : ℝ) * Real.cos (10 * Real.log 4) - 1 / 2 * (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6))| ≤ 1 / 2 * (30 / 10000) := by
      have hsplit : (1 / 2 : ℝ) * Real.cos (10 * Real.log 4) - 1 / 2 * (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6)) = 1 / 2 * (Real.cos (10 * Real.log 4) - (-((-274 / 1000 : ℝ) - (-274 / 1000 : ℝ) ^ 3 / 6))) := by ring
      rw [hsplit, abs_mul]
      have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hcos_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_re (by norm_num)
  have him_bound : |((((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (4813 / 10000 : ℝ)| ≤ 1 / 200 := by
    have hCim : ((dp_c4 : ℂ)).im = 4813 / 10000 := by simp [dp_c2, dp_c3, dp_c4]
    rw [him, hamp4]
    have e1 : |(1 / 2 : ℝ) * Real.sin (10 * Real.log 4) - 1 / 2 * (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)| ≤ 1 / 2 * (49 / 10000) := by
      have hsplit : (1 / 2 : ℝ) * Real.sin (10 * Real.log 4) - 1 / 2 * (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2) = 1 / 2 * (Real.sin (10 * Real.log 4) - (1 - 2 * ((-274 / 1000 : ℝ) / 2 - ((-274 / 1000 : ℝ) / 2) ^ 3 / 6) ^ 2)) := by ring
      rw [hsplit, abs_mul]
      have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hsin_close (by norm_num)
    exact dp_abs_tri _ _ _ _ _ _ e1 hcenter_im (by norm_num)
  have h := dp_norm_of_re_im ((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)) dp_c4 (1 / 200) (1 / 200) hre_bound him_bound
  linarith [h]
theorem dp_S4_Im_ge_3009_10000 : (3009 / 10000 : ℝ) ≤ |((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im| := by
  have h1 : ((((1 : ℝ) : ℂ)) ^ (-dp_s0_10)) = 1 := by
    have hc : (((1 : ℝ) : ℂ)) = 1 := by simp
    rw [hc]
    simp
  have him1 : (((((1 : ℝ) : ℂ)) ^ (-dp_s0_10))).im = 0 := by rw [h1]; simp
  have him2_le : abs ((((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c2).im) ≤ ‖((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c2‖ := Complex.abs_im_le_norm _
  have him3_le : abs ((((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c3).im) ≤ ‖((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c3‖ := Complex.abs_im_le_norm _
  have him4_le : abs ((((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c4).im) ≤ ‖((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c4‖ := Complex.abs_im_le_norm _
  have ht2 := dp_term2_tight
  have ht3 := dp_term3_tight
  have ht4 := dp_term4_tight
  have h2 : |((((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (4269 / 10000 : ℝ)| ≤ 1 / 100 := by
    have e : ((((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c2)).im = (((((2 : ℝ) : ℂ)) ^ (-dp_s0_10))).im - 4269 / 10000 := by rw [Complex.sub_im]; simp [dp_c2]
    rw [e] at him2_le
    linarith [him2_le, ht2]
  have h3 : |((((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - (-5773 / 10000)| ≤ 1 / 100 := by
    have e : ((((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c3)).im = (((((3 : ℝ) : ℂ)) ^ (-dp_s0_10))).im - (-5773 / 10000) := by rw [Complex.sub_im]; simp [dp_c3]
    rw [e] at him3_le
    linarith [him3_le, ht3]
  have h4 : |((((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)))).im - 4813 / 10000| ≤ 1 / 100 := by
    have e : ((((((4 : ℝ) : ℂ)) ^ (-dp_s0_10)) - dp_c4)).im = (((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im - 4813 / 10000 := by rw [Complex.sub_im]; simp [dp_c4]
    rw [e] at him4_le
    linarith [him4_le, ht4]
  have hsum : ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im = 0 + (((((2 : ℝ) : ℂ)) ^ (-dp_s0_10))).im + (((((3 : ℝ) : ℂ)) ^ (-dp_s0_10))).im + (((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im := by
    have e1 : ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im = ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10))).im + (((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im := by rw [Complex.add_im]
    have e2 : ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10))).im = ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10))).im + (((((3 : ℝ) : ℂ)) ^ (-dp_s0_10))).im := by rw [Complex.add_im]
    have e3 : ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10))).im = (1 : ℂ).im + (((((2 : ℝ) : ℂ)) ^ (-dp_s0_10))).im := by rw [Complex.add_im]
    have e4 : (1 : ℂ).im = 0 := by simp
    linarith [e1, e2, e3, e4]
  have h1im : (1 : ℂ).im = 0 := by simp
  have hge : (3009 / 10000 : ℝ) ≤ ((1 : ℂ) + ((((2 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((3 : ℝ) : ℂ)) ^ (-dp_s0_10)) + ((((4 : ℝ) : ℂ)) ^ (-dp_s0_10))).im := by
    rw [hsum]
    have b2 := abs_le.mp h2
    have b3 := abs_le.mp h3
    have b4 := abs_le.mp h4
    linarith [b2, b3, b4]
  exact le_trans hge (le_abs_self _)
