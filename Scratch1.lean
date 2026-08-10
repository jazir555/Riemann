import Mathlib
open Complex HurwitzZeta Set MeasureTheory Filter

theorem kernel_decay (t : ℝ) (ht : 1 ≤ t) :
    |evenKernel 0 t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hsum : HasSum (fun n : ℤ => if (n:ℝ) = 0 then 0 else Real.exp (-Real.pi * (n:ℝ) ^ 2 * t))
      (evenKernel 0 t - 1) := by
    have := HurwitzZeta.hasSum_int_evenKernel₀ 0 ht0
    simpa using this
  set q : ℝ := Real.exp (-Real.pi * t) with hq
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]; nlinarith [Real.pi_gt_three]
  have hq1 : q ≤ Real.exp (-Real.pi) := by
    rw [hq]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  -- majorant
  set g : ℤ → ℝ := fun n => if n = 0 then 0 else q ^ (n.natAbs) with hg
  have hpt : ∀ n : ℤ,
      ‖(if (n:ℝ) = 0 then 0 else Real.exp (-Real.pi * (n:ℝ) ^ 2 * t))‖ ≤ g n := by
    intro n
    by_cases hn : n = 0
    · simp [hn, hg]
    · have hnR : ((n:ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
      rw [if_neg hnR, hg]
      simp only [if_neg hn]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hq, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h1 : (1:ℝ) ≤ (n.natAbs : ℝ) := by
        have : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
        exact_mod_cast this
      have hsq : ((n:ℝ))^2 = (n.natAbs : ℝ)^2 := by
        rw [show ((n.natAbs:ℝ)) = |(n:ℝ)| by simp, sq_abs]
      rw [hsq]
      obtain ⟨c, hc0, hcdef⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = Real.pi * t :=
        ⟨Real.pi * t, mul_nonneg Real.pi_pos.le ht0.le, rfl⟩
      have hkey : (n.natAbs:ℝ) ≤ (n.natAbs:ℝ)^2 := by nlinarith
      have h : (n.natAbs:ℝ) * c ≤ (n.natAbs:ℝ)^2 * c := mul_le_mul_of_nonneg_right hkey hc0
      have e1 : (n.natAbs:ℝ) * (-Real.pi * t) = -((n.natAbs:ℝ) * c) := by rw [hcdef]; ring
      have e2 : -Real.pi * (n.natAbs:ℝ)^2 * t = -((n.natAbs:ℝ)^2 * c) := by rw [hcdef]; ring
      rw [e1, e2]
      exact neg_le_neg h
  sorry
