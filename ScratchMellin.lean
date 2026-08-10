import Mathlib

open Complex Real HurwitzZeta Set MeasureTheory Filter
open scoped Complex

noncomputable section

def orderSet (f : ℂ → ℂ) : Set ℝ :=
  { ρ : ℝ | ∃ (C : ℝ) (r₀ : ℝ), 0 < r₀ ∧
      ∀ z, r₀ ≤ ‖z‖ → ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ) }

def a0 : UnitAddCircle := 0
def P : WeakFEPair ℂ := hurwitzEvenFEPair a0

-- exp(-π/t) ≤ t for t ∈ (0,1]
lemma exp_neg_pi_div_le_self {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    rexp (-Real.pi / t) ≤ t := by
  rcases eq_or_lt_of_le ht1 with rfl | ht1
  · -- t = 1: exp(-π) ≤ 1
    simp only [div_one]
    exact (exp_le_exp.mpr (by linarith [Real.pi_pos])).trans_eq Real.exp_zero
  · trans (rexp (Real.log t))
    · rw [exp_le_exp, div_le_iff₀ ht]
      have hlog : Real.log t < Real.log 1 :=
        (Real.log_lt_log_iff ht zero_lt_one).mpr ht1
      have h2 : Real.log t * t < 0 :=
        mul_neg_of_neg_of_pos (by linarith [Real.log_one]) ht
      have h1 : |Real.log t * t| < 1 := abs_log_mul_self_lt _ ht ht1.le
      rw [abs_of_neg h2] at h1
      linarith [show -Real.pi < -1 from neg_lt_neg (by linarith [Real.pi_gt_three])]
    · exact le_of_eq (Real.exp_log ht)

-- ln(x+1) ≤ √x for x ≥ 1
lemma log_add_one_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 1) ≤ Real.sqrt x := by
  sorry

-- |evenKernel 0 t - 1| ≤ 3 exp(-π t) for t ≥ 1
lemma evenKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |evenKernel a0 t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  sorry

-- |cosKernel 0 t - 1| ≤ 3 exp(-π t) for t ≥ 1
lemma cosKernel_sub_le (t : ℝ) (ht : 1 ≤ t) :
    |cosKernel a0 t - 1| ≤ 3 * Real.exp (-Real.pi * t) := by
  sorry

-- Γ(σ)/π^σ ≤ exp(σ^{3/2}) for σ ≥ 1
lemma gamma_over_pi_le_exp_pow {σ : ℝ} (h : 1 ≤ σ) :
    Real.Gamma σ / Real.pi ^ σ ≤ Real.exp (σ ^ (3 / 2 : ℝ)) := by
  sorry

-- (3/2 : ℝ) ∈ orderSet completedRiemannZeta₀
lemma orderSet_completedRiemannZeta₀ :
    (3 / 2 : ℝ) ∈ orderSet completedRiemannZeta₀ := by
  sorry
