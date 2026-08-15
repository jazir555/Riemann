-- Bridge: Hadamard tsum → Kadiri zero-free edge

import Mathlib
import ZeroFreeRegionProof

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Complex Real ZeroFreeRegion
open scoped BigOperators LSeries.notation
open ArithmeticFunction hiding log

/-- **Zero-free edge from tsum factorisation.**
Tsum analogue of `ZeroFreeRegion.zeroFreeEdge_from_factorization`. -/
theorem zeroFreeEdge_from_tsum
    {a : ℕ → ℂ} (hre : ∀ n, 0 < (a n).re) (hre_lt : ∀ n, (a n).re < 1)
    {analytic : ℂ → ℂ}
    (h_decomp : ∀ (s : ℂ) (hs : 1 < s.re),
      LSeries ↗Λ s = analytic s - ∑' n, (1 / (s - a n) + 1 / a n))
    -- Summability of the zero-sum tsums at three evaluation points
    (hs₀ : Summable (fun n => (1 / (↑σ - a n) + 1 / a n : ℂ)))
    (hs₁ : Summable (fun n => (1 / (↑σ + ↑t * I - a n) + 1 / a n : ℂ)))
    (hs₂ : Summable (fun n => (1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n : ℂ)))
    (σ t : ℝ) (hσ : 1 < σ)
    (ρ₀ : ℂ) (m : ℕ) (hm : ρ₀ = a m)
    (hρ₀im : ρ₀.im = t) (hρ₀re_pos : 0 < ρ₀.re)
    (A₀ A₁ A₂ : ℝ) (_hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
    (h_analytic : 3 * (analytic (↑σ : ℂ)).re + 4 * (analytic (↑σ + ↑t * I)).re
        + (analytic (↑σ + 2 * ↑t * I)).re ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂)
    (hRHS_pos : 0 < A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) :
    σ - ρ₀.re ≥ 4 / (A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) := by
  set d : ℝ := σ - ρ₀.re with hd_def
  have hd : 0 < d := by
    have : ρ₀.re < 1 := by rw [hm]; exact hre_lt m
    linarith
  have h3f1 := three_four_one_re_LSeries_vonMangoldt hσ t
  have hρ₀eq : ρ₀ = (↑(ρ₀.re) : ℂ) + ↑t * I := by apply Complex.ext <;> simp [hρ₀im]
  have hdC : (↑d : ℂ) = ↑σ - ↑(ρ₀.re) := by rw [hd_def]; push_cast; ring
  have hρ₀_1 : ↑σ - ρ₀ = ↑d - ↑t * I := by rw [hρ₀eq, hdC]; ring
  have hρ₀_2 : ↑σ + ↑t * I - ρ₀ = ↑d := by rw [hρ₀eq, hdC]; ring
  have hρ₀_3 : ↑σ + 2 * ↑t * I - ρ₀ = ↑d + ↑t * I := by rw [hρ₀eq, hdC]; ring
  -- Per-zero combination
  let F : ℕ → ℝ := fun n =>
    3 * ((1 / (↑σ - a n) + 1 / a n : ℂ)).re
    + 4 * ((1 / (↑σ + ↑t * I - a n) + 1 / a n : ℂ)).re
    + ((1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n : ℂ)).re
  -- Each F(n) ≥ 0
  have Fnn : ∀ n, 0 ≤ F n := by
    intro n; unfold F; simp only [add_re]
    have hd' : 0 < σ - (a n).re := by nlinarith [hre n, hre_lt n, hσ]
    have hgen := re_three_four_one_one_over_sub_nonneg (σ := σ) (t := t) (ρ := a n) hd'
    have hz : 0 ≤ ((1 : ℂ) / a n).re := re_inv_nonneg_of_re_nonneg (hre n).le
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hz,
      mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hz]
  -- F(m) ≥ 4/d
  have Fm_ge : 4 / d ≤ F m := by
    unfold F
    rw [← hm, hρ₀_1, hρ₀_2, hρ₀_3]; simp only [add_re]
    have hb := re_three_four_one_one_over_sub_borderline d t hd
    simp only [one_div] at hb ⊢
    have hz : 0 ≤ (ρ₀)⁻¹.re := by
      simpa [one_div] using re_inv_nonneg_of_re_nonneg hρ₀re_pos.le
    nlinarith
  -- The 3-4-1 of LSeries equals the analytic part minus the per-zero tsum
  -- (by h_decomp at 3 points + linearity of Re/tsum)
  have hLS_eq :
      (3 * (LSeries ↗Λ (↑σ : ℂ)).re + 4 * (LSeries ↗Λ (↑σ + ↑t * I)).re
          + (LSeries ↗Λ (↑σ + 2 * ↑t * I)).re)
    = (3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re
          + (analytic (↑σ + 2 * ↑t * I)).re) - ∑' n, F n := by
    have hσs : 1 < (↑σ : ℂ).re := by simpa using hσ
    have ht1s : 1 < (↑σ + ↑t * I : ℂ).re := by simpa using hσ
    have ht2s : 1 < (↑σ + 2 * ↑t * I : ℂ).re := by simpa using hσ
    have h₀r := (Complex.hasSum_re hs₀.hasSum).summable
    have h₁r := (Complex.hasSum_re hs₁.hasSum).summable
    have h₂r := (Complex.hasSum_re hs₂.hasSum).summable
    rw [h_decomp _ hσs, h_decomp _ ht1s, h_decomp _ ht2s]
    simp only [sub_re]
    rw [Complex.re_tsum hs₀, Complex.re_tsum hs₁, Complex.re_tsum hs₂]
    -- Now: 3*(A - ∑' g₀.re) + 4*(C - ∑' g₁.re) + (D - ∑' g₂.re)
    --   = 3*A + 4*C + D - ∑' F(n)
    -- Suffices: 3*∑' g₀.re + 4*∑' g₁.re + ∑' g₂.re = ∑' F(n)
    have hkey : 3 * (∑' n, (g₀ n).re) + 4 * (∑' n, (g₁ n).re) + ∑' n, (g₂ n).re
        = ∑' n, F n := by
      rw [← h₀r.tsum_mul_left (3 : ℝ), ← h₁r.tsum_mul_left (4 : ℝ),
          ← h₀r.tsum_add h₁r, ← (h₀r.add h₁r).tsum_add h₂r]
      unfold F; ring
    rw [show (3 : ℝ) * ((analytic (↑σ : ℂ)).re - ∑' n, (g₀ n).re) =
        3 * (analytic (↑σ : ℂ)).re - 3 * ∑' n, (g₀ n).re from by ring,
      show (4 : ℝ) * ((analytic (↑σ + ↑t * I : ℂ)).re - ∑' n, (g₁ n).re) =
        4 * (analytic (↑σ + ↑t * I : ℂ)).re - 4 * ∑' n, (g₁ n).re from by ring,
      show ((analytic (↑σ + 2 * ↑t * I : ℂ)).re - ∑' n, (g₂ n).re) =
        (analytic (↑σ + 2 * ↑t * I : ℂ)).re - ∑' n, (g₂ n).re from by ring]
    rw [hkey]
  rw [hLS_eq, sub_nonneg] at h3f1
  -- Now h3f1 : ∑' F(n) ≤ analytic 3-4-1
  -- We need: 4/d ≤ ∑' F(n)
  -- This follows from: F(m) ≥ 4/d and ∑' F(n) ≥ F(m) (tsum ≥ any term)
  have hFsum : Summable F := by
    unfold F
    have h₀r := (Complex.hasSum_re hs₀.hasSum).summable
    have h₁r := (Complex.hasSum_re hs₁.hasSum).summable
    have h₂r := (Complex.hasSum_re hs₂.hasSum).summable
    exact (h₀r.mul_left 3).add (h₁r.mul_left 4) |>.add h₂r
  have hsum_ge : 4 / d ≤ ∑' n, F n :=
    le_trans Fm_ge (le_tsum Fnn hFsum m)
  have h4le : 4 / d ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := by
    linarith [h3f1, hsum_ge, h_analytic]
  rw [ge_iff_le, div_le_iff₀ hRHS_pos]
  rw [div_le_iff₀ hd] at h4le
  linarith
