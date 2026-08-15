-- Bridge: Hadamard tsum → Kadiri zero-free edge
-- Imports only ZeroFreeRegionProof (which compiles cleanly)

import Mathlib
import ZeroFreeRegionProof

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Complex Real ZeroFreeRegion
open scoped BigOperators LSeries.notation
open ArithmeticFunction hiding log

-- ============================================================
-- Tsum version of zeroFreeEdge_from_factorization
-- ============================================================

private noncomputable def tsumThreeFourOneTerm (σ t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  3 * ((1 / (↑σ - a n) + 1 / a n)).re
  + 4 * ((1 / (↑σ + ↑t * I - a n) + 1 / a n)).re
  + ((1 / (↑σ + 2 * ↑t * I - a n) + 1 / a n)).re

private theorem tsumThreeFourOneTerm_nonneg
    {σ t : ℝ} (hσ : 1 < σ) {a : ℕ → ℂ} (hre : ∀ n, 0 < (a n).re)
    (n : ℕ) : 0 ≤ tsumThreeFourOneTerm σ t a n := by
  unfold tsumThreeFourOneTerm
  simp only [add_re, mul_re, add_re]
  have hd : 0 < σ - (a n).re := by nlinarith [hre n]
  have hgen := re_three_four_one_one_over_sub_nonneg (ρ := a n) hd
  have hz : 0 ≤ ((1 : ℂ) / a n).re := re_inv_nonneg_of_re_nonneg (hre n).le
  have h1 : 0 ≤ 3 * ((1 : ℂ) / (↑σ - a n)).re := mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith [re_inv_nonneg_of_re_nonneg (by simp; linarith : 0 ≤ (↑σ - a n).re)])
  have h2 : 0 ≤ 4 * ((1 : ℂ) / (↑σ + ↑t * I - a n)).re := mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (by linarith [re_inv_nonneg_of_re_nonneg (by simp; linarith : 0 ≤ (↑σ + ↑t * I - a n).re)])
  have h3 : 0 ≤ ((1 : ℂ) / (↑σ + 2 * ↑t * I - a n)).re := re_inv_nonneg_of_re_nonneg (by simp; linarith)
  have h4 : 0 ≤ 3 * (1 / a n).re := mul_nonneg (by norm_num) hz
  have h5 : 0 ≤ 4 * (1 / a n).re := mul_nonneg (by norm_num) hz
  have h6 : 0 ≤ (1 / a n).re := hz
  linarith [hgen, h1, h2, h3, h4, h5, h6]

private theorem tsumThreeFourOneTerm_borderline
    {σ t : ℝ} {d : ℝ} (hd : 0 < d) {a : ℕ → ℂ} {ρ₀ : ℂ} {m : ℕ}
    (hm : ρ₀ = a m) (hρ₀im : ρ₀.im = t) (hre : ∀ n, 0 < (a n).re) :
    4 / d ≤ tsumThreeFourOneTerm σ t a m := by
  unfold tsumThreeFourOneTerm
  simp only [add_re]
  have hp : ρ₀ = (↑(ρ₀.re) : ℂ) + ↑t * I := by apply Complex.ext <;> simp [hρ₀im]
  have hdC : (d : ℂ) = (σ : ℂ) - (ρ₀.re : ℂ) := by
    rw [show d = σ - ρ₀.re from rfl]; push_cast; ring
  have h1 : (σ : ℂ) - a m = (d : ℂ) - ↑t * I := by
    simp only [hm, hp, hdC]; ring
  have h2 : (σ : ℂ) + ↑t * I - a m = (d : ℂ) := by
    simp only [hm, hp, hdC]; ring
  have h3 : (σ : ℂ) + 2 * ↑t * I - a m = (d : ℂ) + ↑t * I := by
    simp only [hm, hp, hdC]; ring
  rw [h1, h2, h3]
  simp only [add_re]
  have hb := re_three_four_one_one_over_sub_borderline d t hd
  simp only [one_div] at hb ⊢
  have hz : 0 ≤ (a m)⁻¹.re := by
    simpa [one_div] using re_inv_nonneg_of_re_nonneg (hre m).le
  nlinarith

theorem zeroFreeEdge_from_tsum
    {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (hre : ∀ n, 0 < (a n).re)
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
  have hd : 0 < σ - ρ₀.re := by linarith
  set d : ℝ := σ - ρ₀.re
  have hfnn : ∀ n, 0 ≤ tsumThreeFourOneTerm σ t a n :=
    tsumThreeFourOneTerm_nonneg hσ hre
  have hfb : 4 / d ≤ tsumThreeFourOneTerm σ t a m :=
    tsumThreeFourOneTerm_borderline hd hm hρ₀im hre
  have htsum : 4 / d ≤ ∑' n, tsumThreeFourOneTerm σ t a n :=
    le_trans hfb (le_tsum hfnn m)
  have h341 := three_four_one_re_LSeries_vonMangoldt hσ t
  -- Connect: the 3-4-1 of the LSeries equals analytic bound minus the tsum
  have hkey : ∑' n, tsumThreeFourOneTerm σ t a n ≤ A₀ / (σ - 1) + A₁ * Real.log (|t| + 2) + A₂ := by
    -- From h_decomp at 3 points, the 3-4-1 of LSeries = analytic - tsum
    -- Since 3-4-1 of LSeries ≥ 0, we get tsum ≤ analytic ≤ RHS
    -- This follows from h341, h_decomp, and h_analytic
    sorry -- requires: linearity of Complex.re over tsum, decomposition at 3 points
  linarith

-- ============================================================
-- Full pipeline theorem
-- ============================================================

/-- Given the Hadamard zero enumeration and all supporting hypotheses, prove
`ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ zeroFreeEdge(Im s)`.

This assembles the full pipeline:
1. `logDeriv_completedZeta` → tsum decomposition of -ζ'/ζ
2. `zeroFreeEdge_from_tsum` → edge bound
3. `edge_gap_positive` → numerical h_c
4. Digamma/Gamma bounds → h_analytic

Remaining sorry's: the tsum algebra identity, and connecting to
`logDeriv_completedZeta`'s output. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge_hadamard
    {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n)
    (hord : ∀ z, meromorphicOrderAt xi z ≤ 1)
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im)
    (σ : ℝ) (hσgt : 1 < σ) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  push Not at h1; intro hz
  -- Extract the analytic function from logDeriv_completedZeta
  -- The decomposition is: LSeries ↗Λ s' = analytic s' - ∑' n, (1/(s'-aₙ) + 1/aₙ)
  -- where analytic encodes the digamma/Gamma/derivative-g part
  sorry -- requires: logDeriv_completedZeta, edge_gap_positive,
         -- digamma_le_log, norm_Gamma_le_Gamma_re, zeroFreeEdge_from_tsum

-- ============================================================
-- Remaining work summary
-- ============================================================

/-!
## Pipeline: Hadamard → Kadiri zero-free edge → sorry #3

### What's done (sorry-free, in ZeroFreeRegionProof.lean):
- `zeroFreeEdge_from_factorization` — finite Finset version
- `riemannZeta_ne_zero_of_zeroFreeEdge` — finite version
- `three_four_one_re_LSeries_vonMangoldt` — 3-4-1 inequality
- `re_three_four_one_one_over_sub_nonneg` — term non-negativity
- `re_three_four_one_one_over_sub_borderline` — borderline bound
- `edge_gap_positive` — numerical h_c

### What's done in this file:
- `zeroFreeEdge_from_tsum` — tsum version (sorry in tsum algebra)
- `riemannZeta_ne_zero_of_zeroFreeEdge_hadamard` — assembly (sorry)

### What's needed to close:
1. **Tsum algebra** (line ~105): Prove that `3·Re(analytic σ) + ... - 3·Re(LSeries σ) - ... = ∑' tsumThreeFourOneTerm`
   - Uses: `Complex.re_tsum`, `tsum_mul_left`, `tsum_add`, `h_decomp` at 3 points
2. **Hadamard connection** (line ~125): Instantiate `analytic` and `h_decomp` from `logDeriv_completedZeta`
   - Uses: `logDeriv_completedZeta` → `neg_logDeriv_riemannZeta_eq_xi` → LSeries identity
3. **h_analytic** (line ~130): Bound the analytic part using `digamma_le_log` + `norm_Gamma_le_Gamma_re`
4. **Close sorry #3**: Use the zero-free edge to prove `xiShifted_nonvanishing_on_tail`
   - For |Im(z)| ≥ 0.494: zero-free edge covers it
   - For |Im(z)| < 0.494: need growth bounds or numerical verification
-/
