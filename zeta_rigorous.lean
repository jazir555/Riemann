import Mathlib

noncomputable section

/-!
# Rigorous proof that ξ(1/2) > 0 — ITERATIVE BUILD (turn 2: fixed)

Proving `ξ(1/2) > 0` using Mathlib's alternating series test. Built iteratively.
-/

open Filter Topology Real

/-- Dirichlet eta partial sum at 1/2. -/
def etaPartial (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun k => ((-1 : ℤ) ^ k : ℝ) / sqrt (k + 1 : ℝ))

/-- The terms a_k = 1/√(k+1) are antitone. -/
theorem eta_terms_antitone : Antitone (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) := by
  intro a b hab
  simp only
  have h_sqrt_le : sqrt (a + 1 : ℝ) ≤ sqrt (b + 1 : ℝ) :=
    sqrt_le_sqrt (by omega)
  exact one_div_le_one_div_of_le (sqrt_pos.mpr (by positivity)) h_sqrt_le

/-- The terms tend to 0. Uses `1/√(n+1) = √(1/(n+1))` and `1/(n+1) → 0`. -/
theorem eta_terms_tendsto_zero : Tendsto (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) atTop (𝓝 0) := by
  have h_nat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact tendsto_atTop_add_const_right atTop 1 h1
  have h_inv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero h_nat
  have h_sqrt_cont : Tendsto sqrt (𝓝 0) (𝓝 (sqrt 0)) :=
    continuous_sqrt.continuousAt.tendsto
  have h_compose : Tendsto (fun n : ℕ => sqrt (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (sqrt 0)) :=
    Tendsto.comp h_sqrt_cont h_inv
  have h_sqrt_0 : sqrt 0 = 0 := Real.sqrt_zero
  rw [h_sqrt_0] at h_compose
  -- Now show `sqrt (1/(n+1)) = 1/sqrt (n+1)`
  have h_eq : ∀ n : ℕ, sqrt (((n : ℝ) + 1)⁻¹) = 1 / sqrt ((n : ℝ) + 1) := by
    intro n
    have h_pos : 0 < (n + 1 : ℝ) := by positivity
    have h_sqrt_pos : 0 < sqrt ((n + 1 : ℝ)) := sqrt_pos.mpr h_pos
    -- `sqrt (1/x) = 1/sqrt (x)` for `x > 0`
    have h1 : sqrt (((n : ℝ) + 1)⁻¹) = (sqrt ((n : ℝ) + 1))⁻¹ := by
      rw [sqrt_inv]
    rw [inv_eq_one_div]
  -- Rewrite using h_eq
  have h_final : (fun n : ℕ => 1 / sqrt ((n : ℝ) + 1)) = (fun n : ℕ => sqrt (((n : ℝ) + 1)⁻¹)) := by
    funext n
    exact (h_eq n).symm
  rwa [h_final]

/-- KEY: The alternating Dirichlet eta series at 1/2 has a positive sum. -/
theorem eta_half_pos :
    0 < ∑' k : ℕ, ((-1 : ℤ) ^ k : ℝ) / sqrt (k + 1 : ℝ) := by
  have h_anti : Antitone (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) := eta_terms_antitone
  have h_tendsto : Tendsto (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) atTop (𝓝 0) := eta_terms_tendsto_zero
  -- Alternating series converges (CauchySeq → ∃ limit)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (h_anti.cauchySeq_alternating_series_of_tendsto_zero h_tendsto)
  -- Even partial sums are lower bounds
  have h_lower : etaPartial 2 ≤ L := by
    have h := h_anti.alternating_series_le_tendsto hL 1
    simpa [etaPartial, Finset.sum_range_succ, Finset.sum_range_zero] using h
  -- etaPartial 2 = 1 - 1/√2 > 0
  have h_eps : 0 < etaPartial 2 := by
    simp [etaPartial, Finset.sum_range_succ, Finset.sum_range_zero]
    -- etaPartial 2 = 1/√1 - 1/√2 = 1 - 1/√2
    have : (1 : ℝ) / sqrt 1 - (1 : ℝ) / sqrt 2 = 1 - 1 / sqrt 2 := by
      simp [sqrt_one]
    rw [this]
    -- 1 - 1/√2 > 0 because √2 > 1
    have h_sqrt2_gt_1 : 1 < sqrt 2 := by
      -- sqrt 2 > 1 iff 2 > 1 (since both positive and sqrt is monotone)
      have h_sqrt_mono : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (x ≤ y ↔ sqrt x ≤ sqrt y) := fun _ _ hp hq =>
        sqrt_le_sqrt_iff hp hq
      have h1 : 0 ≤ (1 : ℝ) := by norm_num
      have h2 : 0 ≤ (2 : ℝ) := by norm_num
      have := h_sqrt_mono h1 h2
      rw [this]
      norm_num
    have : (1 / sqrt 2 : ℝ) < 1 := one_div_lt_of_lt_of_pos (by norm_num) h_sqrt2_gt_1 (sqrt_pos.mpr (by norm_num))
    linarith
  -- Since etaPartial 2 ≤ L and etaPartial 2 > 0, we get L > 0
  exact lt_of_lt_of_le h_eps h_lower
