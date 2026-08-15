-- Bridge: Hadamard tsum → Kadiri zero-free edge

import Mathlib
import ZeroFreeRegionProof

set_option maxHeartbeats 400000

open Complex Real ZeroFreeRegion
open scoped BigOperators LSeries.notation
open ArithmeticFunction hiding log

/-- **Zero-free edge from tsum factorisation.**
Key bridge between the Hadamard infinite-sum decomposition of `-ζ'/ζ`
and the Kadiri zero-free region.

Given:
- A zero enumeration `a : ℕ → ℂ` with `0 < Re(aₙ) < 1`
- A decomposition `LSeries ↗Λ s = analytic(s) - ∑'ₙ (1/(s - aₙ) + 1/aₙ)`
- An `O(log|t|)` bound on the 3-4-1 combination of the analytic part
- A specific zero `ρ₀ = a(m)` with `Im(ρ₀) = t`

Proves: `σ - Re(ρ₀) ≥ 4/(A₀/(σ-1) + A₁·log(|t|+2) + A₂)`.

The only `sorry` is the tsum algebra identity connecting the 3-4-1 of the
LSeries to the 3-4-1 of the analytic part minus the tsum. -/
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
  -- Per-zero 3-4-1 combination is ≥ 0
  -- Borderline term for index m: ≥ 4/d (re_three_four_one_one_over_sub_borderline)
  -- So tsum ≥ 4/d
  -- 3-4-1 of LSeries ≥ 0 (three_four_one_re_LSeries_vonMangoldt)
  -- From h_decomp: 3-4-1 of LSeries = 3-4-1 of analytic - tsum
  -- So tsum ≤ 3-4-1 of analytic ≤ RHS (h_analytic)
  -- Chain: 4/d ≤ tsum ≤ analytic ≤ RHS
  sorry -- core tsum algebra (3-4-1 of LSeries decomposition at 3 points)
