-- Bridge: Hadamard tsum → Kadiri zero-free edge

import Mathlib
import ZeroFreeRegionProof

set_option maxHeartbeats 400000

open Complex Real ZeroFreeRegion Filter
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

The proof applies the 3-4-1 inequality at `σ, σ+ti, σ+2ti`, substitutes the
tsum decomposition, extracts the borderline zero's ≥ 4/d contribution, and
discards the rest (each term ≥ 0 by `re_three_four_one_one_over_sub_nonneg`).

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
  -- Define d = σ - ρ₀.re
  set d : ℝ := σ - ρ₀.re with hd_def
  have hd : 0 < d := by
    have : ρ₀.re < 1 := by rw [hm]; exact hre_lt m
    linarith
  -- Per-zero term: each is ≥ 0 (hre, hre_lt, hσ)
  -- Borderline term for index m: ≥ 4/d (re_three_four_one_one_over_sub_borderline)
  -- So tsum ≥ 4/d
  -- 3-4-1 of LSeries ≥ 0 (three_four_one_re_LSeries_vonMangoldt)
  -- From h_decomp: 3-4-1 of LSeries = 3-4-1 of analytic - tsum
  -- So tsum ≤ 3-4-1 of analytic ≤ RHS (h_analytic)
  -- Chain: 4/d ≤ tsum ≤ analytic ≤ RHS
  sorry -- core tsum algebra (3-4-1 of LSeries decomposition at 3 points)

/-- **Full pipeline: Hadamard → Kadiri zero-free edge.**
Given the Hadamard zero enumeration and all supporting hypotheses, prove
`ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ zeroFreeEdge(Im s)`.

Remaining sorry's: (1) connecting `logDeriv_completedZeta` output to the
`tsum` decomposition, (2) the tsum algebra identity in `zeroFreeEdge_from_tsum`,
(3) the `h_analytic` bound from `digamma_le_log` + `norm_Gamma_le_Gamma_re`. -/
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
  -- For Re(s) < 1: use Hadamard decomposition → zeroFreeEdge_from_tsum → edge_gap_positive
  sorry -- assembly: logDeriv_completedZeta + zeroFreeEdge_from_tsum + edge_gap_positive

/-!
## Pipeline status

### ✅ Done (sorry-free, in ZeroFreeRegionProof.lean):
- `zeroFreeEdge_from_factorization` — finite Finset version
- `riemannZeta_ne_zero_of_zeroFreeEdge` — finite version
- `three_four_one_re_LSeries_vonMangoldt` — 3-4-1 inequality
- `re_three_four_one_one_over_sub_nonneg` — term non-negativity
- `re_three_four_one_one_over_sub_borderline` — borderline ≥ 4/d
- `edge_gap_positive` — numerical h_c

### ✅ Done (sorry-free, in ZeroFreeRegionHadamard.lean):
- `hadamard_factorization_genus_one` — factorization of ξ
- `logDeriv_xi_of_factorization` — log-derivative from factorization
- `neg_logDeriv_riemannZeta_eq_xi` — -ζ'/ζ via xi
- `logDeriv_completedZeta` — parametric decomposition
- `xi_zero_enumeration` — zero enumeration construction

### 🔧 Done in this file (sorry in tsum algebra):
- `zeroFreeEdge_from_tsum` — tsum version of zeroFreeEdge
- `riemannZeta_ne_zero_of_zeroFreeEdge_hadamard` — assembly

### 🔲 Remaining:
1. **Tsum algebra** (zeroFreeEdge_from_tsum sorry): Prove
   `3·Re(LSeries σ) + ... = 3·Re(analytic σ) + ... - ∑' tsum341`
   Uses: `Complex.re_tsum`, `tsum_mul_left`, `tsum_add`, `h_decomp` at 3 points
2. **Hadamard connection** (riemannZeta_ne_zero_of_zeroFreeEdge_hadamard sorry):
   Instantiate `analytic` and `h_decomp` from `logDeriv_completedZeta`
3. **h_analytic**: Bound analytic part from `digamma_le_log` + `norm_Gamma_le_Gamma_re`
4. **Close sorry #3**: Use zero-free edge + growth bounds to prove `xiShifted_nonvanishing_on_tail`
-/
