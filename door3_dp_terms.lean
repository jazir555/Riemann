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
