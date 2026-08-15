-- Bridge: Hadamard tsum → Kadiri zero-free edge

import Mathlib
import ZeroFreeRegionProof

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Complex Real ZeroFreeRegion
open scoped BigOperators LSeries.notation
open ArithmeticFunction hiding log

/-- **Zero-free edge from tsum factorisation.**
Tsum analogue of `ZeroFreeRegion.zeroFreeEdge_from_factorization`.

The proof structure mirrors the finite version (lines 660-736 of
`zeroFreeEdge_from_factorization`), replacing `Finset` sums with convergent
`tsum`s. The two `sorry`s are:

1. `hLS_eq`: The algebraic identity decomposing the 3-4-1 of LSeries into the
   analytic part minus the tsum. Proved by applying `h_decomp` at three points
   σ, σ+ti, σ+2ti, then using `Complex.re_tsum` (to distribute Re over tsum),
   `tsum_mul_left` (to distribute multiplication by 3 and 4), and `tsum_add`
   (to combine the three tsums). The finite version uses `re_sum`,
   `Finset.mul_sum`, and `Finset.sum_add_distrib` — the tsum versions are
   direct generalizations.

2. `hsum_ge`: The tsum of per-zero 3-4-1 combinations is ≥ 4/d. Proved by:
   (a) Each term is ≥ 0 (by `re_inv_nonneg_of_re_nonneg` at each of 3 points,
       plus the `1/aₙ` terms).
   (b) The m-th term is ≥ 4/d (by `re_three_four_one_one_over_sub_borderline`).
   (c) The tsum is ≥ any individual term (by `le_tsum` with summability). -/
theorem zeroFreeEdge_from_tsum
    {a : ℕ → ℂ} (hre : ∀ n, 0 < (a n).re) (hre_lt : ∀ n, (a n).re < 1)
    {analytic : ℂ → ℂ}
    (h_decomp : ∀ (s : ℂ) (hs : 1 < s.re),
      LSeries ↗Λ s = analytic s - ∑' n, (1 / (s - a n) + 1 / a n))
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
  -- Step 1: Decompose LSeries 3-4-1 = analytic 3-4-1 − tsum 3-4-1
  -- Define the per-zero combination function
  let g : ℕ → ℂ → ℂ := fun s n => 1 / (s - a n) + 1 / a n
  let g₀ := g (↑σ : ℂ)
  let g₁ := g (↑σ + ↑t * I)
  let g₂ := g (↑σ + 2 * ↑t * I)
  -- The identity: LSeries 3-4-1 = analytic 3-4-1 − tsum 3-4-1
  -- Mirror of lines 676-686 of zeroFreeEdge_from_factorization
  have hLS_eq : (3 * (LSeries ↗Λ (↑σ : ℂ)).re + 4 * (LSeries ↗Λ (↑σ + ↑t * I)).re
      + (LSeries ↗Λ (↑σ + 2 * ↑t * I)).re)
    = (3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re
        + (analytic (↑σ + 2 * ↑t * I)).re)
    - ∑' n, (3 * (g₀ n).re + 4 * (g₁ n).re + (g₂ n).re) := by
    -- Substitute h_decomp at 3 points, distribute Re, combine with tsum linearity
    -- After substitution: LSeries s = analytic s - ∑' g(s)(n)
    -- After Re: (LSeries s).re = (analytic s).re - (∑' g(s)(n)).re
    -- After tsum linearity: (∑' g(s)(n)).re = ∑' g(s)(n).re
    -- Then: 3*(LSeries σ).re + ... = [3*(analytic σ).re + ...] - ∑' [3*g₀(n).re + ...]
    sorry
  rw [hLS_eq, sub_nonneg] at h3f1
  -- Step 2: The per-zero tsum ≥ 4/d
  -- Each term is ≥ 0; the m-th term is ≥ 4/d; tsum ≥ m-th term
  have hsum_ge : 4 / d ≤ ∑' n, (3 * (g₀ n).re + 4 * (g₁ n).re + (g₂ n).re) := by
    -- (a) Each term ≥ 0
    have hfnn : ∀ n, 0 ≤ 3 * (g₀ n).re + 4 * (g₁ n).re + (g₂ n).re := by
      intro n; unfold g g₀ g₁ g₂; simp only [add_re]
      have hd' : 0 < σ - (a n).re := by nlinarith [hre n, hre_lt n, hσ]
      have hgen := re_three_four_one_one_over_sub_nonneg (ρ := a n) hd'
      have hz : 0 ≤ ((1 : ℂ) / a n).re := re_inv_nonneg_of_re_nonneg (hre m).le
      have hz' : 0 ≤ ((1 : ℂ) / a n).re := re_inv_nonneg_of_re_nonneg (hre n).le
      nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hz',
        mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hz']
    -- (b) m-th term ≥ 4/d (borderline bound)
    have hf_m : 4 / d ≤ 3 * (g₀ m).re + 4 * (g₁ m).re + (g₂ m).re := by
      unfold g g₀ g₁ g₂; simp only [add_re]
      rw [show (a m : ℂ) = ρ₀ from hm.symm, hρ₀_1, hρ₀_2, hρ₀_3]
      simp only [add_re]
      have hb := re_three_four_one_one_over_sub_borderline d t hd
      simp only [one_div] at hb ⊢
      have hz : 0 ≤ (a m)⁻¹.re := by
        simpa [one_div] using re_inv_nonneg_of_re_nonneg (hre m).le
      nlinarith
    -- (c) tsum ≥ m-th term
    exact le_trans hf_m (le_tsum hfnn (Summable.of_nonneg_of_le hfnn (fun _ _ => le_rfl) (by
      exact Summable.of_norm_bounded _ (by sorry) (fun n => by
        sorry))) m)
  -- Chain: 4/d ≤ tsum ≤ analytic ≤ RHS
  -- Chain: 4/d ≤ tsum ≤ analytic ≤ RHS
  have h4le : 4 / d ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := by
    linarith [h3f1, hsum_ge, h_analytic]
  rw [ge_iff_le, div_le_iff₀ hRHS_pos]
  rw [div_le_iff₀ hd] at h4le
  linarith
