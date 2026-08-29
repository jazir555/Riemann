import Mathlib

open Filter Metric Set Function
open scoped Topology

/-- Test 1: hpow with explicit nat annotations -/
example (R : ℝ) (hR : 0 < R) : (R ^ (3 / 2 : ℝ)) ^ (4 : ℝ) = R ^ (6 : ℝ) := by
  rw [← Real.rpow_mul (by positivity) (3 / 2) (4 : ℝ)]
  norm_num

/-- Test 2: hexp4 with explicit nat annotations -/
example (x : ℝ) (hx : 0 ≤ x) : x ^ (4 : ℕ) / 256 = (x / 4) ^ (4 : ℕ) := by
  rw [div_pow]
  norm_num

/-- Test 3: hC nlinarith with pow atoms -/
example (R : ℝ) (hR : 4 ≤ R) : R ^ (2 : ℕ) ≤ R ^ (6 : ℕ) / 256 := by
  have hD : (256 : ℝ) ≤ R ^ (4 : ℕ) := by
    refine le_trans (by norm_num : (256 : ℝ) ≤ (4 : ℝ) ^ (4 : ℕ)) (pow_le_pow_left₀ (by norm_num) hR 4)
  nlinarith [hD]

/-- Test 4: hxi calc structure (parses and proves) -/
example (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (C₁ : ℝ) (hC₁0 : 0 ≤ C₁)
    (hz : ‖z‖ ≤ R) (hz1 : ‖z - 1‖ ≤ R + 1)
    (hΛ : ‖completedRiemannZeta₀ z‖ ≤ C₁ * Real.exp (R ^ (3 / 2 : ℝ))) :
    ‖z * (z - 1) * completedRiemannZeta₀ z‖ ≤ R * (R + 1) * (C₁ * Real.exp (R ^ (3 / 2 : ℝ))) := by
  calc
    ‖z * (z - 1) * completedRiemannZeta₀ z‖ = ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ R * (R + 1) * (C₁ * Real.exp (R ^ (3 / 2 : ℝ))) := by
      have h1 : ‖z‖ * ‖z - 1‖ ≤ R * (R + 1) := mul_le_mul hz hz1 (by positivity) (by positivity)
      have h2 : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ ≤
          (R * (R + 1)) * (C₁ * Real.exp (R ^ (3 / 2 : ℝ))) :=
        mul_le_mul h1 hΛ (by positivity) (by positivity)
      simpa [mul_assoc] using h2

/-- Test 5: exists_pow_two_between with tendsto_atTop_atTop -/
example {x : ℝ} (hx : 1 ≤ x) : ∃ k : ℕ, ((2 ^ k : ℕ) : ℝ) ≤ x ∧ x < ((2 ^ (k + 1) : ℕ) : ℝ) := by
  have hexists : ∃ K : ℕ, x < ((2 ^ K : ℕ) : ℝ) := by
    have ht : Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) atTop atTop := by
      simpa using tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp ht) (x + 1)
    refine ⟨i, ?_⟩
    have := hi i (le_refl i)
    linarith
  let m := Nat.find hexists
  have hm : x < ((2 ^ m : ℕ) : ℝ) := Nat.find_spec hexists
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    norm_num at hm
    linarith
  refine ⟨m - 1, ?_, ?_⟩
  · have hmin : ¬ x < ((2 ^ (m - 1) : ℕ) : ℝ) := by
      apply Nat.find_min hexists
      exact Nat.pred_lt hm0
    exact le_of_not_gt hmin
  · have hk : m - 1 + 1 = m := by omega
    rw [hk]
    exact hm

/-- Test 6: hmem with compl_ofPred -/
example (a : ℕ → ℂ) (N : ℝ) (hbounded : ∀ N : ℕ, ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ).Finite) :
    {n : ℕ | (Nat.ceil N : ℝ) ≤ ‖a n‖} ∈ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  have hfin' : ({n : ℕ | ¬ (Nat.ceil N : ℝ) ≤ ‖a n‖} : Set ℕ).Finite := by
    refine ((hbounded (Nat.ceil N)).subset ?_)
    intro n hn
    have hn' : ‖a n‖ < (Nat.ceil N : ℝ) := by simpa using hn
    exact le_of_lt hn'
  simpa [Set.compl_ofPred] using hfin'.compl_mem_cofinite

/-- Test 7: he1 fix -/
example (R : ℝ) (hRpow0 : 0 ≤ R ^ (3 / 2 : ℝ)) : 1 ≤ Real.exp (R ^ (3 / 2 : ℝ)) := by
  have hle2 : (1 : ℝ) + R ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) + 1 := by nlinarith
  exact le_trans (le_trans (by nlinarith [hRpow0] : (1 : ℝ) ≤ 1 + R ^ (3 / 2 : ℝ)) hle2)
    (Real.add_one_le_exp (R ^ (3 / 2 : ℝ)))
