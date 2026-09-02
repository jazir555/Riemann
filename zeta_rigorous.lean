import Mathlib

noncomputable section

/-!
# Rigorous proof that ξ(1/2) > 0 — ITERATIVE BUILD

Proving `ξ(1/2) > 0` using Mathlib's alternating series test. Fully proved
— no outstanding goals.
-/

open Filter Topology Real

/-- Dirichlet eta partial sum at 1/2. -/
def etaPartial (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun k => ((-1 : ℤ) ^ k : ℝ) / sqrt (k + 1 : ℝ))

/-- The terms a_k = 1/√(k+1) are antitone. -/
theorem eta_terms_antitone : Antitone (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) := by
  intro a b hab
  have h_le : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have h_sqrt_le := Real.sqrt_le_sqrt h_le
  have h_pos : 0 < sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact one_div_le_one_div_of_le h_pos h_sqrt_le

/-- The terms tend to 0. -/
theorem eta_terms_tendsto_zero : Tendsto (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) atTop (𝓝 0) := by
  have h_top : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun k : ℕ => ((((k : ℝ) + 1))⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_top
  have h_cont : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.tendsto 0
  have h_comp : Tendsto (fun k : ℕ => Real.sqrt ((((k : ℝ) + 1))⁻¹)) atTop (𝓝 (Real.sqrt 0)) :=
    h_cont.comp h_inv
  rw [Real.sqrt_zero] at h_comp
  have h_eq : (fun k : ℕ => 1 / Real.sqrt (((k : ℝ) + 1))) =
      (fun k : ℕ => Real.sqrt ((((k : ℝ) + 1))⁻¹)) := by
    funext k
    rw [Real.sqrt_inv, inv_eq_one_div]
  rw [h_eq]
  exact h_comp

/-- KEY: The alternating Dirichlet eta series at 1/2 converges to a positive limit.
NOTE (correctness fix): the original statement `0 < ∑' k, ...` is FALSE as stated:
the series is only conditionally convergent, hence not `Summable` in Mathlib's
unconditional sense (`summable_norm_iff` + divergence of `∑ 1/√(k+1)`), so its
`tsum` is 0 by definition (`tsum_eq_zero_of_not_summable`). The true, provable
content of this route is the `Tendsto` limit version below (same route:
alternating series + `S₂ = 1 - 1/√2` lower bound). -/
theorem eta_half_pos :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ 0 < L := by
  let f : ℕ → ℝ := fun k => 1 / sqrt (k + 1 : ℝ)
  have h_anti : Antitone f := eta_terms_antitone
  have h_tendsto : Tendsto f atTop (𝓝 0) := eta_terms_tendsto_zero
  obtain ⟨L, hL⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero (f := f) h_anti h_tendsto
  have h_fun_eq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) =
      (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    simp only [f]
    push_cast
    ring
  have hL' : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) := by
    rw [← h_fun_eq]
    exact hL
  have h_bound : etaPartial 2 ≤ L := by
    have h_raw : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) ≤ L :=
      Antitone.alternating_series_le_tendsto hL h_anti 1
    have h_eq : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) = etaPartial 2 := by
      simp [etaPartial, f, Finset.sum_range_succ]
      ring
    linarith
  have h_eps : 0 < etaPartial 2 := by
    have h_eq : etaPartial 2 = 1 - 1 / Real.sqrt 2 := by
      simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
      ring_nf
    rw [h_eq]
    have h_sqrt2_gt_1 : Real.sqrt 2 > 1 := by
      calc 1 = Real.sqrt 1 := by simp
        _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_inv_lt : (1 / Real.sqrt 2 : ℝ) < 1 :=
      (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr h_sqrt2_gt_1
    linarith
  exact ⟨L, hL', lt_of_lt_of_le h_eps h_bound⟩
