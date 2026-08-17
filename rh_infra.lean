import Mathlib

open Set Filter Topology Real
open scoped Topology

noncomputable section

namespace ZetaAsymptotics

/-- `s ↦ x ^ s` is real-analytic for `0 < x`. -/
lemma analyticOnNhd_rpow_const_exp (x : ℝ) (hx : 0 < x) :
    AnalyticOnNhd ℝ (fun s : ℝ => x ^ s) univ := by
  have hlin : AnalyticOnNhd ℝ (fun s : ℝ => s * Real.log x) univ := by
    exact (analyticOnNhd_id (𝕜 := ℝ)).mul analyticOnNhd_const
  have hmain : AnalyticOnNhd ℝ (fun s : ℝ => Real.exp (s * Real.log x)) univ :=
    AnalyticOnNhd.rexp hlin
  exact hmain.congr isOpen_univ (by
    intro s hs
    dsimp
    rw [rpow_def_of_pos hx]
    congr 1
    ring)

/-- `s ↦ x ^ (-(s + 1))` is real-analytic for `0 < x`. -/
lemma analyticOnNhd_rpow_neg_exp (x : ℝ) (hx : 0 < x) :
    AnalyticOnNhd ℝ (fun s : ℝ => x ^ (-(s + 1))) univ := by
  have h0 := analyticOnNhd_rpow_const_exp x hx
  have hlin0 : AnalyticOnNhd ℝ (fun s : ℝ => -s - 1) univ :=
    (analyticOnNhd_id (𝕜 := ℝ)).neg.sub analyticOnNhd_const
  have hlin : AnalyticOnNhd ℝ (fun s : ℝ => -(s + 1)) univ :=
    hlin0.congr isOpen_univ (by intro s hs; ring)
  exact h0.comp hlin (fun s _ => mem_univ _)

/-- `s ↦ (a - c) * a ^ (-(s + 1))` is real-analytic for `0 < a`. -/
lemma analyticOnNhd_mul_rpow_neg (a c : ℝ) (ha : 0 < a) :
    AnalyticOnNhd ℝ (fun s : ℝ => (a - c) * a ^ (-(s + 1))) univ := by
  have h0 := analyticOnNhd_rpow_neg_exp a ha
  have hcst : AnalyticOnNhd ℝ (fun s : ℝ => (a - c)) univ := analyticOnNhd_const
  exact (h0.mul hcst).congr isOpen_univ (by intro s hs; dsimp; rw [mul_comm])

end ZetaAsymptotics

end
