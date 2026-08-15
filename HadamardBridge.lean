-- Bridge: Hadamard tsum → Kadiri zero-free edge
-- This file needs to be integrated into riemann hypothesis.lean
-- by adding `import ZeroFreeRegionProof` and `import ZeroFreeRegionHadamard`

import Mathlib
import ZeroFreeRegionProof
import ZeroFreeRegionHadamard

set_option maxHeartbeats 400000

open Complex Real ZeroFreeRegion
open scoped BigOperators LSeries.notation
open ArithmeticFunction hiding log

-- Key theorem: tsum version of zeroFreeEdge_from_factorization
theorem zeroFreeEdge_from_tsum
    {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (hre : ∀ n, 0 < (a n).re)
    {analytic : ℂ → ℂ}
    (h_decomp : ∀ (s : ℂ) (hs : 1 < s.re),
      LSeries ↗Λ s = analytic s - ∑' n, (1 / (s - a n) + 1 / a n))
    (σ t : ℝ) (hσ : 1 < σ)
    (ρ₀ : ℂ) (m : ℕ) (hm : a m = ρ₀)
    (hρ₀im : ρ₀.im = t) (hρ₀re_pos : 0 < ρ₀.re)
    (A₀ A₁ A₂ : ℝ) (_hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
    (h_analytic : 3 * (analytic (↑σ : ℂ)).re + 4 * (analytic (↑σ + ↑t * I)).re
        + (analytic (↑σ + 2 * ↑t * I)).re ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂)
    (hRHS_pos : 0 < A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) :
    σ - ρ₀.re ≥ 4 / (A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂) := by
  have hd : 0 < σ - ρ₀.re := by linarith
  set d : ℝ := σ - ρ₀.re
  -- Per-zero 3-4-1 combination
  let f : ℕ → ℝ := fun n =>
    3 * ((1 / (↑σ - a n) + 1 / a n)).re
    + 4 * ((1 / (↑σ + ↑t * I - a n) + 1 / a n)).re
    + ((1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n)).re
  -- Each f(n) ≥ 0
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n; unfold f; simp only [add_re]
    have hd' : 0 < σ - (a n).re := by linarith [hre n, hσ]
    have := re_three_four_one_one_over_sub_nonneg (ρ := a n) hd'
    have hz : 0 ≤ ((1 : ℂ) / a n).re := re_inv_nonneg_of_re_nonneg (hre n).le
    linarith
  -- Borderline term: f(m) ≥ 4/d
  have hfb : 4 / d ≤ f m := by
    unfold f; simp only [add_re]
    have hp : ρ₀ = (↑(ρ₀.re) : ℂ) + ↑t * I := by apply Complex.ext <;> simp [hρ₀im]
    have hdC : (↑d : ℂ) = ↑σ - ↑(ρ₀.re) := by rw [show d = σ - ρ₀.re from rfl]; push_cast; ring
    have h1 : ↑σ - a m = ↑d - ↑t * I := by rw [show ρ₀ = a m from hm, hp, hdC]; ring
    have h2 : ↑σ + ↑t * I - a m = ↑d := by rw [show ρ₀ = a m from hm, hp, hdC]; ring
    have h3 : ↑σ + 2 * ↑t * I - a m = ↑d + ↑t * I := by rw [show ρ₀ = a m from hm, hp, hdC]; ring
    rw [h1, h2, h3]; simp only [add_re]
    have := re_three_four_one_one_over_sub_borderline d t hd
    simp only [one_div] at this ⊢
    have hz : 0 ≤ (a m)⁻¹.re := by simpa [one_div] using re_inv_nonneg_of_re_nonneg (hre m).le
    linarith
  -- tsum ≥ 4/d
  have htsum : 4 / d ≤ ∑' n, f n := le_trans hfb (le_tsum hfnn m)
  -- Now: 3-4-1 of LSeries = 3-4-1 of analytic - ∑' f(n)
  -- Since LHS ≥ 0, we get ∑' f(n) ≤ 3-4-1 of analytic ≤ RHS
  -- Direct proof via the 3-4-1 inequality and decomposition
  have h341 := three_four_one_re_LSeries_vonMangoldt hσ t
  -- From h341 and h_decomp, derive the bound
  have hkey : ∑' n, f n ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := by
    -- Use the decomposition at three points to express LSeries in terms of analytic and ∑' f
    have hσs : 1 < (↑σ : ℂ).re := by simp; linarith
    have ht1s : 1 < (↑σ + ↑t * I : ℂ).re := by simp; linarith
    have ht2s : 1 < (↑σ + 2 * ↑t * I : ℂ).re := by simp; linarith
    -- Substitute h_decomp into 3-4-1 inequality
    -- (3·Re L(Λ,σ) + 4·Re L(Λ,σ+ti) + Re L(Λ,σ+2ti)) ≥ 0
    -- = (3·Re(analytic σ) + ...) - ∑' f(n) ≥ 0
    -- ⟹ ∑' f(n) ≤ 3·Re(analytic σ) + ... ≤ RHS
    -- This follows from linearity of Re, tsum, and the decomposition
    have hdecomp_sum : (3 * (LSeries ↗Λ (↑σ : ℂ)).re + 4 * (LSeries ↗Λ (↑σ + ↑t * I)).re
        + (LSeries ↗Λ (↑σ + 2 * ↑t * I)).re)
        = (3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re
            + (analytic (↑σ + 2 * ↑t * I)).re) - ∑' n, f n := by
      rw [h_decomp _ hσs, h_decomp _ ht1s, h_decomp _ ht2s]
      simp only [sub_re]
      rw [Complex.re_tsum (by exact (LSeriesSummable_vonMangoldt hσs).hasSum.summable.re),
          Complex.re_tsum (by exact (LSeriesSummable_vonMangoldt ht1s).hasSum.summable.re),
          Complex.re_tsum (by exact (LSeriesSummable_vonMangoldt ht2s).hasSum.summable.re)]
      sorry -- requires careful tsum algebra: distributing Re, mul_left, add
    linarith [h341, hdecomp_sum, h_analytic]
  -- Final chain: 4/d ≤ ∑' f(n) ≤ RHS
  linarith [htsum, hkey]
