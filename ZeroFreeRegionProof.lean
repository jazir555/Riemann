import Mathlib

open Complex Real Topology
open scoped BigOperators

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in

noncomputable section

-- ============================================================
-- Numerical constants and the zero-free edge
-- ============================================================

noncomputable def kadiriConstant : ℝ := 1 / 57.54

theorem kadiriConstant_pos : 0 < kadiriConstant := by
  unfold kadiriConstant; exact div_pos zero_lt_one (by norm_num)

theorem log_eleven_gt_one : 1 < Real.log 11 := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h2 : (3:ℝ) < 11 := by norm_num
  rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_lt_log (Real.exp_pos 1) (lt_trans h1 h2)

theorem kadiri_div_log_eleven_lt_one_tenth :
    kadiriConstant / Real.log 11 < 1 / 10 := by
  have hlogpos : 0 < Real.log 11 := by linarith [log_eleven_gt_one]
  unfold kadiriConstant
  rw [div_lt_div_iff₀ hlogpos (by norm_num : (0:ℝ) < 10)]
  nlinarith [log_eleven_gt_one]

noncomputable def zeroFreeEdge (t : ℝ) : ℝ :=
  1 - kadiriConstant / Real.log (|t| + 10)

theorem zeroFreeEdge_lt_one (t : ℝ) : zeroFreeEdge t < 1 := by
  unfold zeroFreeEdge; apply sub_lt_self
  exact div_pos kadiriConstant_pos (by apply Real.log_pos; linarith [abs_nonneg t])

theorem zeroFreeEdge_le_one (t : ℝ) : zeroFreeEdge t ≤ 1 := le_of_lt (zeroFreeEdge_lt_one t)

theorem zeroFreeEdge_gt_nine_tenths (t : ℝ) (ht : 1 ≤ |t|) :
    (9 : ℝ) / 10 < zeroFreeEdge t := by
  unfold zeroFreeEdge
  have hlogpos : 0 < Real.log (|t| + 10) := by apply Real.log_pos; linarith [abs_nonneg t]
  have hlogpos11 : 0 < Real.log 11 := by linarith [log_eleven_gt_one]
  have hfrac : kadiriConstant / Real.log (|t| + 10) ≤ kadiriConstant / Real.log 11 := by
    rw [div_le_div_iff₀ hlogpos hlogpos11]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])) kadiriConstant_pos.le
  linarith [kadiri_div_log_eleven_lt_one_tenth]

theorem one_sub_zeroFreeEdge_lt_one_tenth (t : ℝ) (ht : 1 ≤ |t|) :
    1 - zeroFreeEdge t < 1 / 10 := by
  unfold zeroFreeEdge
  have hlogpos : 0 < Real.log (|t| + 10) := by apply Real.log_pos; linarith [abs_nonneg t]
  have hlogpos11 : 0 < Real.log 11 := by linarith [log_eleven_gt_one]
  have hfrac : kadiriConstant / Real.log (|t| + 10) ≤ kadiriConstant / Real.log 11 := by
    rw [div_le_div_iff₀ hlogpos hlogpos11]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])) kadiriConstant_pos.le
  rw [show 1 - (1 - kadiriConstant / Real.log (|t| + 10)) = kadiriConstant / Real.log (|t| + 10) from by ring]
  linarith [kadiri_div_log_eleven_lt_one_tenth]

theorem zeroFree_gap
    (s : ℂ) (ht : |s.im| ≥ 1)
    (hσ : s.re ≥ zeroFreeEdge s.im) (h1 : s.re < 1) :
    0 < 1 - s.re ∧ 1 - s.re < 1 / 10 := by
  constructor
  · linarith
  · have h := one_sub_zeroFreeEdge_lt_one_tenth s.im ht; linarith

-- ============================================================
-- The 3-4-1 product inequality
-- ============================================================

theorem norm_zeta_product_ge_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + t * I)‖ ^ 4 *
        ‖riemannZeta (σ + 2 * t * I)‖ := by
  have hσ₀ : 0 < σ - 1 := sub_pos.mpr hσ
  have hprod := DirichletCharacter.norm_LFunction_product_ge_one
    (N := 1) (χ := (1 : DirichletCharacter ℂ 1)) hσ₀ t
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq] at hprod
  have hnorm_eq : ∀ (a b c : ℂ), ‖a ^ 3 * b ^ 4 * c‖ = ‖a‖ ^ 3 * ‖b‖ ^ 4 * ‖c‖ := by
    intros; rw [norm_mul, norm_mul, norm_pow, norm_pow]
  push_cast at hprod ⊢
  rw [hnorm_eq] at hprod
  have hsimp : (1 : ℂ) + (σ - 1 : ℂ) = (σ : ℂ) := by push_cast; ring
  rw [hsimp] at hprod
  suffices h : ‖riemannZeta (↑σ + I * ↑t)‖ = ‖riemannZeta (↑σ + ↑t * I)‖ by
    have h2 : ‖riemannZeta (↑σ + 2 * I * ↑t)‖ = ‖riemannZeta (↑σ + 2 * ↑t * I)‖ := by
      congr 1; congr 1; ring
    linarith [h ▸ h2 ▸ hprod]
  rw [show (I : ℂ) * ↑t = ↑t * I from mul_comm ..]

-- ============================================================
-- Kadiri algebraic core
-- ============================================================

namespace Kadiri

private theorem continuousOn_of_continuous {α E : Type*} [TopologicalSpace α]
    [SeminormedAddCommGroup E] {f : α → E} {s : Set α} (hf : Continuous f) :
    ContinuousOn f s :=
  (continuousOn_univ.mpr hf).mono (Set.subset_univ s)

theorem center_mem_closedBall (t : ℝ) :
    (1 + I * t : ℂ) ∈ Metric.closedBall (1 + I * t) 1 :=
  Metric.mem_closedBall.mpr (by simp)

theorem left_point_mem_closedBall (t x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x + I * t : ℂ) ∈ Metric.closedBall (1 + I * t) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : (1 - x + I * t : ℂ) - (1 + I * t) = (-(x : ℂ)) := by ring
  rw [h]; simp [norm_neg, Complex.norm_real, abs_of_nonneg hx0]; exact hx1

theorem right_point_mem_closedBall (t x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x + I * t : ℂ) ∈ Metric.closedBall (1 + I * t) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : (1 + x + I * t : ℂ) - (1 + I * t) = (x : ℂ) := by ring
  rw [h]; simp [Complex.norm_real, abs_of_nonneg hx0]; exact hx1

/-- Derivative bound wraps the mean-value inequality for a holomorphic function. -/
structure DerivativeBound (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) where
  M : ℝ
  M_pos : 0 < M
  diff : ∀ z ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ f z
  bound : ∀ z ∈ Metric.closedBall z₀ r, ‖deriv f z‖ ≤ M

theorem DerivativeBound.norm_image_sub_le
    {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (db : DerivativeBound f z₀ r)
    {x y : ℂ}
    (hx : x ∈ Metric.closedBall z₀ r)
    (hy : y ∈ Metric.closedBall z₀ r) :
    ‖f x - f y‖ ≤ db.M * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    db.diff db.bound (convex_closedBall z₀ r) hy hx

theorem DerivativeBound.norm_center_le_of_zero_left
    {f : ℂ → ℂ} {t x : ℝ}
    (db : DerivativeBound f (1 + I * t) 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hzero : f (1 - x + I * t : ℂ) = 0) :
    ‖f (1 + I * t : ℂ)‖ ≤ db.M * x := by
  have h := db.norm_image_sub_le
    (left_point_mem_closedBall t x hx0 hx1) (center_mem_closedBall t)
  have hd : ‖(1 - x + I * t : ℂ) - (1 + I * t)‖ = x := by
    have : (1 - x + I * t : ℂ) - (1 + I * t) = (-(x : ℂ)) := by ring
    simp [this, norm_neg, Complex.norm_real, abs_of_nonneg hx0]
  rw [hd] at h; simpa [hzero, zero_sub, norm_neg] using h

theorem DerivativeBound.norm_right_le_two_mul
    {f : ℂ → ℂ} {t x : ℝ}
    (db : DerivativeBound f (1 + I * t) 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hzero : f (1 - x + I * t : ℂ) = 0) :
    ‖f (1 + x + I * t : ℂ)‖ ≤ 2 * db.M * x := by
  have hcenter := db.norm_center_le_of_zero_left hx0 hx1 hzero
  have hdiff := db.norm_image_sub_le
    (right_point_mem_closedBall t x hx0 hx1) (center_mem_closedBall t)
  have hd : ‖(1 + x + I * t : ℂ) - (1 + I * t)‖ = x := by
    have : (1 + x + I * t : ℂ) - (1 + I * t) = (x : ℂ) := by ring
    simp [this, Complex.norm_real, abs_of_nonneg hx0]
  rw [hd] at hdiff
  have htri :
      ‖f (1 + x + I * t : ℂ)‖ ≤
        ‖f (1 + x + I * t : ℂ) - f (1 + I * t : ℂ)‖ + ‖f (1 + I * t : ℂ)‖ := by
    have hdecomp : (f (1 + x + I * t : ℂ) : ℂ) =
          (f (1 + x + I * t : ℂ) - f (1 + I * t : ℂ)) + f (1 + I * t : ℂ) := by ring
    conv_lhs => rw [hdecomp]
    exact norm_add_le _ _
  linarith

end Kadiri

-- ============================================================
-- Main theorem
-- ============================================================

theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push_neg at h1; intro hz
    set t := s.im with htdef
    set x := 1 - s.re with hxdef
    have hx_pos : x > 0 := by linarith
    have hx_small : x < 1 / 10 := by
      have h := one_sub_zeroFreeEdge_lt_one_tenth s.im ht
      linarith [show 1 - s.re = x from hxdef ▸ by ring]
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at h1
    have hz1s : riemannZeta₁ s = 0 := by
      have h := riemannZeta_eq_inv_sub_mul hs1
      rw [h] at hz; exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (sub_ne_zero.mpr hs1))
    have h341 := norm_zeta_product_ge_one (1 + x) s.im (by linarith)
    have hdb : Kadiri.DerivativeBound riemannZeta₁ (1 + I * t) 1 := by
      have hcont_deriv : Continuous (deriv riemannZeta₁) :=
        differentiable_riemannZeta₁.contDiff.continuous_deriv_one
      have hcomp : IsCompact (Metric.closedBall (1 + I * t) 1) :=
        isCompact_closedBall (1 + I * t) 1
      have hcontOn : ContinuousOn (‖deriv riemannZeta₁ ·‖)
          (Metric.closedBall (1 + I * t) 1) :=
        continuousOn_of_continuous (continuous_norm.comp hcont_deriv)
      have hbound := hcomp.exists_bound_of_continuousOn hcontOn
      refine ⟨Classical.choose hbound + 1, ?_, fun z _ => differentiable_riemannZeta₁ z, ?_⟩
      · have h1 := Classical.choose_spec hbound (1 + I * t) (Kadiri.center_mem_closedBall t)
        linarith [norm_nonneg (deriv riemannZeta₁ (1 + I * t)), abs_of_nonneg (norm_nonneg _)]
      · intro z hz
        have := Classical.choose_spec hbound z hz
        linarith [abs_of_nonneg (norm_nonneg _)]
    have hleft : s = (1 - x + I * t : ℂ) := by
      apply Complex.ext
      · show s.re = (1 - x + I * t : ℂ).re
        simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re]
        rw [hxdef]; ring
      · show s.im = (1 - x + I * t : ℂ).im
        simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_im]
        rw [htdef]
    have hx1 : x ≤ 1 := by linarith [hx_small]
    have hz1s' : riemannZeta₁ (1 - x + I * t : ℂ) = 0 := by
      rw [← hleft]; exact hz1s
    have hupper : ‖riemannZeta₁ (1 + I * t)‖ ≤ 2 * hdb.M * x := by
      have hcenter := hdb.norm_center_le_of_zero_left hx_pos.le hx1 hz1s'
      nlinarith [hdb.M_pos.le, hx_pos.le]
    sorry

end
