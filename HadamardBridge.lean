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

Given:
- A zero enumeration `a : ℕ → ℂ` with `0 < Re(aₙ) < 1`
- A tsum decomposition `LSeries ↗Λ s = analytic(s) - ∑'ₙ (1/(s - aₙ) + 1/aₙ)`
- An `O(log|t|)` bound on the 3-4-1 combination of the analytic part
- A specific zero `ρ₀ = a(m)` with `Im(ρ₀) = t`

Proves: `σ - Re(ρ₀) ≥ 4/(A₀/(σ-1) + A₁·log(|t|+2) + A₂)`. -/
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
  -- Step 1: Decompose LSeries 3-4-1 into analytic minus zero-sum tsum
  -- This is the tsum version of lines 676-686 of zeroFreeEdge_from_factorization.
  -- The identity:
  --   3·Re(LSeries σ) + 4·Re(LSeries (σ+ti)) + Re(LSeries (σ+2ti))
  --   = [3·Re(analytic σ) + ...] - ∑' n, [3·Re(zero-sum term at σ) + ...]
  -- Uses: h_decomp at 3 points, Complex.re_tsum, tsum_mul_left, tsum_add
  have hLS_eq : (3 * (LSeries ↗Λ (↑σ : ℂ)).re + 4 * (LSeries ↗Λ (↑σ + ↑t * I)).re
      + (LSeries ↗Λ (↑σ + 2 * ↑t * I)).re)
    = (3 * (analytic (↑σ)).re + 4 * (analytic (↑σ + ↑t * I)).re + (analytic (↑σ + 2 * ↑t * I)).re)
    - ∑' n, (3 * ((1 / (↑σ - a n) + 1 / a n : ℂ)).re
      + 4 * ((1 / (↑σ + ↑t * I - a n) + 1 / a n : ℂ)).re
      + ((1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n : ℂ)).re) := by
    -- This follows from h_decomp at 3 points + linearity of Re/tsum
    sorry -- tsum algebra: Re distributes over ∑', decomposition at 3 points
  rw [hLS_eq, sub_nonneg] at h3f1
  -- h3f1 : ∑' n, [3·Re(..) + 4·Re(..) + Re(..)] ≤ 3·Re(analytic σ) + ...
  -- Step 2: The tsum ≥ 4/d because each term is ≥ 0 and the m-th term is ≥ 4/d
  have hsum_ge : 4 / d ≤ ∑' n, (3 * ((1 / (↑σ - a n) + 1 / a n : ℂ)).re
      + 4 * ((1 / (↑σ + ↑t * I - a n) + 1 / a n : ℂ)).re
      + ((1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n : ℂ)).re) := by
    sorry -- tsum ≥ borderline ≥ 4/d: use tsum_nonneg + le_tsum + borderline bound
  -- Chain: 4/d ≤ tsum ≤ analytic ≤ RHS
  have h4le : 4 / d ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := by
    linarith [h3f1, hsum_ge, h_analytic]
  rw [ge_iff_le, div_le_iff₀ hRHS_pos]
  rw [div_le_iff₀ hd] at h4le
  linarith
