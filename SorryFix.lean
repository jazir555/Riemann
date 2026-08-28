import Mathlib
import ZeroFreeRegionHadamard
set_option maxHeartbeats 400000
open Complex Finset Real HurwitzZeta
open scoped Topology

namespace SorryFix

private lemma term_le_geom (t : ℝ) (ht : 1 ≤ t) (m : ℕ) :
    Real.exp (-Real.pi * (m + 1) ^ 2 * t) ≤
    Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) ^ m := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsq : ((m : ℝ) + 1) ^ 2 ≥ (m : ℝ) + 1 := by
    calc ((m : ℝ) + 1) ^ 2 = ((m : ℝ) + 1) * ((m : ℝ) + 1) := by ring
      _ ≥ ((m : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (m : ℝ) + 1 := by ring
  have h1 : -(Real.pi) * (((m : ℝ) + 1) ^ 2) * t ≤ -(Real.pi) * ((m : ℝ) + 1) * t := by
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hsq)) ht0.le]
  have hexple := Real.exp_le_exp.mpr h1
  have hexp_add : Real.exp (-(Real.pi) * (m+1:ℝ) * t) =
      Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi) * m * t) := by
    rw [show -(Real.pi) * (m+1:ℝ) * t = -(Real.pi) * t + -(Real.pi) * m * t from by ring,
        Real.exp_add]
  have hexp_mul : Real.exp (-(Real.pi) * m * t) = Real.exp (-(Real.pi * t) * m) := by
    rw [show -(Real.pi) * m * t = -(Real.pi * t) * m from by ring]
  have hexp_nat : Real.exp (-(Real.pi * t) * m) = Real.exp (-(Real.pi * t)) ^ m := by
    rw [show -(Real.pi * t) * m = (m:ℝ) * (-(Real.pi * t)) from by ring, Real.exp_nat_mul]
  calc _ ≤ Real.exp (-(Real.pi) * (m+1:ℝ) * t) := hexple
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi) * m * t) := hexp_add
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi * t) * m) := by rw [hexp_mul]
    _ = Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi * t)) ^ m := by rw [hexp_nat]
    _ = _ := by simp only [neg_mul]

private lemma exp_le_third (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-Real.pi * t) ≤ 1 / 3 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h1 : -Real.pi * t ≤ -3 := by nlinarith [Real.pi_gt_three]
  have h2 := Real.exp_le_exp.mpr h1
  have h3 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
  have h4 : (8:ℝ) ≤ Real.exp 3 := by
    have h4a : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    rw [show (3:ℝ) = 1+1+1 from by norm_num, Real.exp_add, Real.exp_add]
    have h4b : Real.exp 1 * Real.exp 1 ≥ 4 := by
      have := mul_le_mul h4a h4a (by linarith) (by linarith)
      linarith [show (2:ℝ) * 2 = 4 from by norm_num]
    have h4c : Real.exp 1 * Real.exp 1 * Real.exp 1 ≥ 8 := by
      have := mul_le_mul h4b h4a (by linarith) (by linarith)
      linarith [show (4:ℝ) * 2 = 8 from by norm_num]
    exact h4c
  have h5 : (Real.exp 3)⁻¹ ≤ (8:ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos 3) (by norm_num : (0:ℝ) < 8)).mpr h4
  have h6 : (8:ℝ)⁻¹ ≤ (3:ℝ)⁻¹ :=
    (inv_le_inv₀ (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 3)).mpr
      (by norm_num : (3:ℝ) ≤ 8)
  have h5' : Real.exp (-3) ≤ (8:ℝ)⁻¹ := by rw [h3]; exact h5
  rw [show (1/3:ℝ) = (3:ℝ)⁻¹ from by norm_num]
  exact h2 |>.trans h5' |>.trans h6

/-- The cos-Kernel satisfies `|cosKernel 0 t - 1| ≤ 3 exp(-π t)` for `t ≥ 1`. -/
lemma cosKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |cosKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hsum := hasSum_nat_cosKernel₀ (0 : ℝ) ht0
  have hsum' : HasSum (fun n : ℕ ↦ 2 * Real.exp (-Real.pi * (n + 1) ^ 2 * t))
      (cosKernel (0 : UnitAddCircle) t - 1) :=
    hsum.congr_fun (fun n => by simp [Real.cos_zero])
  have hge : 0 ≤ cosKernel (0 : UnitAddCircle) t - 1 := by
    rw [← hsum'.tsum_eq]; exact tsum_nonneg (fun n => by positivity)
  rw [abs_of_nonneg hge, ← hsum'.tsum_eq, tsum_mul_left]
  have hexp1 : Real.exp (-Real.pi * t) < 1 := by
    rw [Real.exp_lt_one_iff]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) ht0
  have hsrc : Summable (fun n : ℕ => Real.exp (-Real.pi * (n + 1) ^ 2 * t)) := by
    have hg := summable_geometric_of_lt_one (Real.exp_nonneg _) hexp1
    exact Summable.of_norm_bounded (hg.mul_left _) (fun n => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; exact term_le_geom t ht n)
  have htsum : ∑' n : ℕ, Real.exp (-Real.pi * (n + 1) ^ 2 * t) ≤
      Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹ := by
    have hg := summable_geometric_of_lt_one (Real.exp_nonneg _) hexp1
    have htsum' := Summable.tsum_le_tsum (term_le_geom t ht) hsrc (hg.mul_left _)
    rwa [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) hexp1] at htsum'
  -- 2 * tsum ≤ 2 * exp(-πt) / (1-exp(-πt)) ≤ 3 * exp(-πt)
  have hfrac : 2 * (Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹) ≤
      3 * Real.exp (-Real.pi * t) := by
    rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ (sub_pos.mpr hexp1)]
    have hx : 0 ≤ Real.exp (-Real.pi * t) := le_of_lt (Real.exp_pos _)
    have h3x : 3 * Real.exp (-Real.pi * t) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (exp_le_third t ht) (by norm_num : (0:ℝ) ≤ 3)
      linarith [show (3:ℝ) * (1/3) = 1 from by norm_num]
    have hmid : 0 ≤ Real.exp (-Real.pi * t) * (1 - 3 * Real.exp (-Real.pi * t)) := by
      apply mul_nonneg hx; linarith [h3x]
    nlinarith [hmid]
  exact (mul_le_mul_of_nonneg_left htsum (by positivity : (0:ℝ) ≤ 2)).trans hfrac

-- The even-Kernel (and hence the Hurwitz even kernel at `a = 0`) is equal to the
-- cos-kernel, hence satisfies the same bound.
lemma evenKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |evenKernel (0 : UnitAddCircle) t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have := congr_fun evenKernel_eq_cosKernel_of_zero t
  simp only [this]
  exact cosKernel_sub_le t ht

/-- The set of real exponents `ρ` such that `‖f z‖ ≤ C·exp(‖z‖^ρ)` outside a
disk. The order of `f` is the infimum of this set (or `⊤` if it is empty).
This is the definition from `ZeroFreeRegionHadamard.lean`. -/
-- orderSet_completedRiemannZeta₀
theorem orderSet_completedRiemannZeta₀ :
    (3 / 2 : ℝ) ∈ ZeroFreeRegionHadamard.orderSet completedRiemannZeta₀ := by
  exact ZeroFreeRegionHadamard.orderSet_completedRiemannZeta₀

end SorryFix