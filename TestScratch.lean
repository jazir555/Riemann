import Mathlib

noncomputable section

open Complex Real MeasureTheory Filter
open scoped Topology

def termC (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))

def term (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    (x - (n : ℝ)) / x ^ (s + 1)

lemma termC_eq_term {n : ℕ} (hn : 0 < n) {s : ℝ} :
    termC n (s : ℂ) = (term n s : ℂ) := by
  unfold termC term
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only []
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
    exact le_trans (by exact_mod_cast (Nat.zero_le n)) hx.1
  rw [show -((s : ℂ) + 1) = ((-(s + 1) : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hx0 (-(s + 1))]
  rw [Real.rpow_neg hx0]
  norm_cast
