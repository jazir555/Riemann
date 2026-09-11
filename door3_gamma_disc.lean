import Mathlib
import central_cover_assembly
import door3_stirling_gamma
import door3_gamma_low

/-!
# Door 3 Stirling-disc enclosures for complex-Gamma LOWERS (GAMLOW remainder).

Cycle safety (verified read-only before writing):
* `door3_stirling_gamma.lean:1` imports `Mathlib` only.
* `central_cover_assembly.lean` imports `Mathlib`, `riemann_hypothesis`,
  `rh_certificate_infra` (no door3 import).
* `door3_gamma_low.lean:1-3` imports `Mathlib` + `central_cover_assembly`
  + `door3_stirling_gamma` (DAG, no cycle).
* Hence this file (`Mathlib` + `central_cover_assembly` + `door3_stirling_gamma`
  + `door3_gamma_low`) is a DAG leaf. It does NOT import `door3_premise_gamma`.

Recon (brief, read-only):
* `Door3GammaLow.gammaLow_*_ge` Props (`door3_gamma_low.lean:119-132`, `:239-640`)
  mirror `premGamma_*_ge` floors with `w = s / 2` centers; 0 of 30 closed.
* Shift infra banked: `Door3GammaLow.shift_norm_one`, `Door3GammaLow.shift_lower`,
  `Door3GammaLow.shift_lower_two`, `Door3GammaLow.w_ne_zero_of_re`,
  `Door3GammaLow.norm_le_of_sq_le` (`:58-106`).
* Denominator factor uppers banked (34 total): `Door3GammaLow.R28_w_norm_le`,
  `Door3GammaLow.R28_w1_norm_le`, `Door3GammaLow.R35_w_norm_le`,
  `Door3GammaLow.R35_w1_norm_le`, `Door3GammaLow.R38_w_norm_le`,
  `Door3GammaLow.R38_w1_norm_le`, `Door3GammaLow.R29_w_norm_le`,
  `Door3GammaLow.R29_w1_norm_le` (tight-flagged ×2) plus 26 single-factor
  uppers `R36/R34/R37/R33/R32/R39/R31/R40/R25/R26/R24/R27/R23/R22/R21/R30/
  E05/E06/E07/E08/E09/E01/E10/BA00/BA03/BA04_w_norm_le`. Referenced by exact
  name below; nothing reproved locally.
* Banked real-Gamma numerals in the stirling file are ALL uppers:
  `D3SG_Real_Gamma_095_le_four`, `D3SG_Real_Gamma_095_le_one_one`,
  `D3SG_Real_Gamma_uniform_005_095_le_20`, `D3SG_Real_Gamma_uniform_0005_005_le_200`,
  `D3SG_Gamma_one_two_le_one`, `D3SG_CHI_Real_Gamma_095_1_le_two`,
  `D3SG_CHI_Real_Gamma_1_206_le_two`. There is NO banked real-Gamma LOWER
  numeral. Using a real upper as a numerator lower would reverse
  `D3SG_Gamma_norm_le_real` (`‖Γ(w)‖ ≤ Real.Gamma (Re w)`) and is unsound.
* `D3SG_CHI_Gamma_upper_neg` (`door3_stirling_gamma.lean:1733`) does the shift
  `Γ(w+1) = w * Γ(w)` via `Complex.Gamma_add_one` at `w ≠ 0`, pays
  `‖w‖ ≥ 1` from `Complex.abs_im_le_norm`, then dispatches `w+1` into the
  banked mid/high lanes. This file mirrors that shape for lowers (norm
  identity the same; inequality direction flipped via explicit denominator
  uppers).

Technique per center: enclosing disc for `Γ(w)` at the explicit `w = s/2`:
shift `w` UP by `k` (smallest `k` with `Re(w+k)` in a would-be real-lower
range) via `Γ(w+k) = w(w+1)...(w+k-1) * Γ(w)` (`Complex.Gamma_add_one`
iterated; general `k`-step lemma proved once below, then instantiated to
one-step and two-step corollaries); lower
`‖Γ(w)‖ ≥ L_real / (‖w‖ * ... * ‖w+k-1‖)` with `L_real` a real lower at the
shifted point and denominator uppers from GAMLOW. Since no `L_real` is
banked, every unconditional lower stays OPEN; what IS closed here is the
general shift identity, its lower corollary, and per-center CONDITIONAL
lowers (`c ≤ ‖Γ(w+k)‖` implies floor-scale bound via the banked
denominators). Where banked real-lowers do not reach (`Re < 0.005` sliver
per GAMLOW note (b)), no banked reflection LOWER shape exists (reflection
with banked uppers gives only `O(10⁻⁵)-O(10⁻²)`, far below floors), so those
stay OPEN with numbers recorded.

Line budget: well under 1400. Explicit binders throughout, small numerals
only.
-/

noncomputable section

namespace Door3GammaDisc

open scoped BigOperators

/-! ## General k-step shift identity (from `Complex.Gamma_add_one`). -/

/-- Norm shift identity for `n` steps up, with explicit nonvanishing at each
factor (covers low-sigma centers where `D3SG_gamma_shift_norm` with
`0 < Re` does not apply). -/
theorem disc_shift_norm_nat (w : ℂ) (n : ℕ)
    (hvan : ∀ k : ℕ, k < n → w + (k : ℂ) ≠ 0) :
    ‖Complex.Gamma (w + (n : ℂ))‖ =
      ‖Complex.Gamma w‖ * ∏ k ∈ Finset.range n, ‖w + (k : ℂ)‖ := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hvan_n : ∀ k : ℕ, k < n → w + (k : ℂ) ≠ 0 := by
      intro k hk
      exact hvan k (Nat.lt_step hk)
    have hlast : w + (n : ℂ) ≠ 0 := hvan n (Nat.lt_succ_self n)
    have ih_eq := ih hvan_n
    have hcast : w + (((n + 1 : ℕ)) : ℂ) = (w + (n : ℂ)) + 1 := by
      push_cast
      ring
    rw [hcast, Complex.Gamma_add_one _ hlast, norm_mul, ih_eq,
      Finset.prod_range_succ]
    ring

/-- General lower via shift: a lower at `w + n` plus an upper on the product
of denominators gives a lower at `w`. -/
theorem disc_shift_lower_nat (w : ℂ) (n : ℕ) (c : ℝ) (M : ℝ)
    (hvan : ∀ k : ℕ, k < n → w + (k : ℂ) ≠ 0)
    (hc : c ≤ ‖Complex.Gamma (w + (n : ℂ))‖)
    (hM : ∏ k ∈ Finset.range n, ‖w + (k : ℂ)‖ ≤ M)
    (hMpos : 0 < M) :
    c / M ≤ ‖Complex.Gamma w‖ := by
  have hEq : ‖Complex.Gamma (w + (n : ℂ))‖ =
      ‖Complex.Gamma w‖ * ∏ k ∈ Finset.range n, ‖w + (k : ℂ)‖ :=
    disc_shift_norm_nat w n hvan
  have hnn : 0 ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  rw [hEq] at hc
  have hle : ‖Complex.Gamma w‖ * ∏ k ∈ Finset.range n, ‖w + (k : ℂ)‖ ≤
      M * ‖Complex.Gamma w‖ := by
    have h0 : ‖Complex.Gamma w‖ * ∏ k ∈ Finset.range n, ‖w + (k : ℂ)‖ ≤
        ‖Complex.Gamma w‖ * M :=
      mul_le_mul_of_nonneg_left hM hnn
    rw [mul_comm M (‖Complex.Gamma w‖)] at h0 ⊢
    rw [mul_comm (‖Complex.Gamma w‖) M] at h0 ⊢
    exact h0
  have h1 : c ≤ M * ‖Complex.Gamma w‖ := le_trans hc hle
  exact (le_div_iff₀ hMpos).mpr h1

/-- One-step instantiation (`n = 1`): matches `Door3GammaLow.shift_lower`
shape with `(1 : ℂ)` spelling. -/
theorem disc_lower_one_cast (w : ℂ) (c : ℝ) (M : ℝ) (hw : w ≠ 0)
    (hc : c ≤ ‖Complex.Gamma (w + ((1 : ℕ) : ℂ))‖)
    (hM : ‖w‖ ≤ M) (hMpos : 0 < M) :
    c / M ≤ ‖Complex.Gamma w‖ := by
  have hvan : ∀ k : ℕ, k < 1 → w + (k : ℂ) ≠ 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    rw [hk0]
    simp only [Nat.cast_zero, add_zero]
    exact hw
  have hMprod : ∏ k ∈ Finset.range 1, ‖w + (k : ℂ)‖ ≤ M := by
    rw [Finset.prod_range_one]
    simp only [Nat.cast_zero, add_zero]
    exact hM
  exact disc_shift_lower_nat w 1 c M hvan hc hMprod hMpos

/-- One-step lower with `(1 : ℂ)` spelling (bridge to banked denominators). -/
theorem disc_lower_one (w : ℂ) (c : ℝ) (M : ℝ) (hw : w ≠ 0)
    (hc : c ≤ ‖Complex.Gamma (w + 1)‖)
    (hM : ‖w‖ ≤ M) (hMpos : 0 < M) :
    c / M ≤ ‖Complex.Gamma w‖ := by
  have heq : (w + 1 : ℂ) = w + ((1 : ℕ) : ℂ) := by
    simp only [Nat.cast_one]
  rw [heq] at hc
  exact disc_lower_one_cast w c M hw hc hM hMpos

/-- Two-step lower with `(2 : ℂ)` spelling (bridge to banked denominators). -/
theorem disc_lower_two (w : ℂ) (c : ℝ) (M0 : ℝ) (M1 : ℝ)
    (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0)
    (hc : c ≤ ‖Complex.Gamma (w + 2)‖)
    (hM0 : ‖w‖ ≤ M0) (hM1 : ‖w + 1‖ ≤ M1)
    (hM0pos : 0 < M0) (hM1pos : 0 < M1) :
    c / (M0 * M1) ≤ ‖Complex.Gamma w‖ := by
  exact Door3GammaLow.shift_lower_two w hw0 hw1 c M0 M1 hc hM0 hM1 hM0pos hM1pos

/-! ## Nonvanishing at explicit centers (uniform: `‖w‖ ≥ |Im| > 0`).

Every center has `|Im| ≥ 0.375`, so `w ≠ 0` and `w + 1 ≠ 0` both follow from
`Complex.abs_im_le_norm` without any `Re` computation. -/

theorem w_ne_zero_of_im (w : ℂ) (hpos : 0 < |w.im|) : w ≠ 0 := by
  have hle := Complex.abs_im_le_norm w
  have hN : 0 < ‖w‖ := lt_of_lt_of_le hpos hle
  exact norm_pos_iff.mp hN

theorem w1_ne_zero_of_im (w : ℂ) (hpos : 0 < |w.im|) : w + 1 ≠ 0 := by
  have him : (w + 1).im = w.im := by simp
  have hpos1 : 0 < |(w + 1).im| := by rw [him]; exact hpos
  have hle := Complex.abs_im_le_norm (w + 1)
  have hN : 0 < ‖w + 1‖ := lt_of_lt_of_le hpos1 hle
  exact norm_pos_iff.mp hN

/-! ## TIGHT-FLAGGED FIRST (gate re-tier): R28 / R35 / R38 / R29.

Status: OPEN unconditionally (0 discharged). TRUE (Stirling, per premise
header): R28 ~0.0274 vs floor 0.026 (margin ~0.0014, 1.05x); R35 ~2.16 vs 2
(margin ~0.16, 1.08x); R38 ~0.0262 vs 0.024 (margin ~0.0022, 1.09x);
R29 ~0.00504 vs 0.0045 (margin ~0.00054, 1.12x). Banked reflection lower with
`D3SG_*` uppers is `~5e-05` at `|Im| = 2.625` (R28 needs 0.026) and `~0.019`
at `|Im| = 0.375` (R35 needs 2): 2-3 orders short. Closed here: per-center
CONDITIONAL lowers paying the two banked denominator factors.
-/

/-- R28 conditional (`k = 2`; denominators `Door3GammaLow.R28_w_norm_le`,
`Door3GammaLow.R28_w1_norm_le`). Shifted `Re = 2.1`: lands above the banked
`[1,2.06]` real-upper cap, and no real LOWER is banked there. -/
theorem R28_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 5.25 : ℂ)) / 2) + 2)‖) :
    c / (2.83 * 3.83) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 5.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 5.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 5.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hw1 : ((((Complex.mk 0.2 5.25 : ℂ)) / 2) + 1) ≠ 0 := w1_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 5.25 : ℂ)) / 2))‖ ≤ 2.83 :=
    Door3GammaLow.R28_w_norm_le
  have hM1 : ‖((((Complex.mk 0.2 5.25 : ℂ)) / 2) + 1)‖ ≤ 3.83 :=
    Door3GammaLow.R28_w1_norm_le
  exact disc_lower_two _ c 2.83 3.83 hw0 hw1 hc hM0 hM1 (by norm_num) (by norm_num)

/-- R35 conditional (`k = 2`; denominators `Door3GammaLow.R35_w_norm_le`,
`Door3GammaLow.R35_w1_norm_le`). Shifted `Re = 2.0525`. -/
theorem R35_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-0.75) : ℂ)) / 2) + 2)‖) :
    c / (0.58 * 1.58) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-0.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 (-0.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 (-0.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hw1 : ((((Complex.mk 0.105 (-0.75) : ℂ)) / 2) + 1) ≠ 0 := w1_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 (-0.75) : ℂ)) / 2))‖ ≤ 0.58 :=
    Door3GammaLow.R35_w_norm_le
  have hM1 : ‖((((Complex.mk 0.105 (-0.75) : ℂ)) / 2) + 1)‖ ≤ 1.58 :=
    Door3GammaLow.R35_w1_norm_le
  exact disc_lower_two _ c 0.58 1.58 hw0 hw1 hc hM0 hM1 (by norm_num) (by norm_num)

/-- R38 conditional (`k = 2`; denominators `Door3GammaLow.R38_w_norm_le`,
`Door3GammaLow.R38_w1_norm_le`). Shifted `Re = 2.0525`. -/
theorem R38_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 5.25 : ℂ)) / 2) + 2)‖) :
    c / (2.83 * 3.83) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 5.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 5.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 5.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hw1 : ((((Complex.mk 0.105 5.25 : ℂ)) / 2) + 1) ≠ 0 := w1_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 5.25 : ℂ)) / 2))‖ ≤ 2.83 :=
    Door3GammaLow.R38_w_norm_le
  have hM1 : ‖((((Complex.mk 0.105 5.25 : ℂ)) / 2) + 1)‖ ≤ 3.83 :=
    Door3GammaLow.R38_w1_norm_le
  exact disc_lower_two _ c 2.83 3.83 hw0 hw1 hc hM0 hM1 (by norm_num) (by norm_num)

/-- R29 conditional (`k = 2`; denominators `Door3GammaLow.R29_w_norm_le`,
`Door3GammaLow.R29_w1_norm_le`). Shifted `Re = 2.1`. -/
theorem R29_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 7.25 : ℂ)) / 2) + 2)‖) :
    c / (3.83 * 4.83) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 7.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 7.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 7.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hw1 : ((((Complex.mk 0.2 7.25 : ℂ)) / 2) + 1) ≠ 0 := w1_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 7.25 : ℂ)) / 2))‖ ≤ 3.83 :=
    Door3GammaLow.R29_w_norm_le
  have hM1 : ‖((((Complex.mk 0.2 7.25 : ℂ)) / 2) + 1)‖ ≤ 4.83 :=
    Door3GammaLow.R29_w1_norm_le
  exact disc_lower_two _ c 3.83 4.83 hw0 hw1 hc hM0 hM1 (by norm_num) (by norm_num)

/-! ## Remaining 26 (OPEN unconditionally) by ascending TRUE-margin.

Order below is by ascending absolute margin `TRUE − floor` from the premise
headers (tightest first); ratio notes inline. Denominators referenced by
exact `Door3GammaLow.*_w_norm_le` name (`k = 1` single factor). Needed
numerator lower `L_real` at `Re(w+1) ∈ [1.05,1.2]`: NOT banked
(`D3SG_Gamma_one_two_le_one` and `D3SG_CHI_Real_Gamma_1_206_le_two` are
uppers `≤ 1`, `≤ 2`; the reverse direction is unsound).
-/

/-- E10 conditional (OPEN; TRUE ~0.00166 vs floor 0.0015, margin ~0.00016,
1.11x; tightest of the 26). -/
theorem E10_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 8.75 : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 8.75 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 8.75 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 8.75 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 8.75 : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.E10_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-- R31 conditional (OPEN; TRUE ~0.00134 vs 0.001, margin ~0.00034, 1.34x;
feasibility-negative lane). -/
theorem R31_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-8.75) : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-8.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 (-8.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 (-8.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 (-8.75) : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.R31_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-- R40 conditional (OPEN; TRUE ~0.00134 vs 0.001, margin ~0.00034, 1.34x;
feasibility-negative lane). -/
theorem R40_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 8.75 : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 8.75 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 8.75 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 8.75 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 8.75 : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.R40_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-- R21 conditional (OPEN; TRUE ~0.00143 vs 0.001, margin ~0.00043, 1.43x;
feasibility-negative lane). -/
theorem R21_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-8.75) : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-8.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 (-8.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 (-8.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 (-8.75) : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.R21_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-- R30 conditional (OPEN; TRUE ~0.00143 vs 0.001, margin ~0.00043, 1.43x;
feasibility-negative lane). -/
theorem R30_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 8.75 : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 8.75 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 8.75 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 8.75 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 8.75 : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.R30_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-- R39 conditional (OPEN; TRUE ~0.00472 vs 0.004, margin ~0.00072, 1.18x;
feasibility-negative lane). -/
theorem R39_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 7.25 : ℂ)) / 2) + 1)‖) :
    c / 3.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 7.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 7.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 7.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 7.25 : ℂ)) / 2))‖ ≤ 3.83 :=
    Door3GammaLow.R39_w_norm_le
  exact disc_lower_one _ c 3.83 hw0 hc hM0 (by norm_num)

/-- E09 conditional (OPEN; TRUE ~0.0057 vs 0.0045, margin ~0.0012, 1.27x). -/
theorem E09_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 7.25 : ℂ)) / 2) + 1)‖) :
    c / 3.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 7.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 7.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 7.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 7.25 : ℂ)) / 2))‖ ≤ 3.83 :=
    Door3GammaLow.E09_w_norm_le
  exact disc_lower_one _ c 3.83 hw0 hc hM0 (by norm_num)

/-- R32 conditional (OPEN; TRUE ~0.00725 vs 0.006, margin ~0.00125, 1.21x;
feasibility-negative lane). -/
theorem R32_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-6.75) : ℂ)) / 2) + 1)‖) :
    c / 3.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-6.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 (-6.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 (-6.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 (-6.75) : ℂ)) / 2))‖ ≤ 3.58 :=
    Door3GammaLow.R32_w_norm_le
  exact disc_lower_one _ c 3.58 hw0 hc hM0 (by norm_num)

/-- R22 conditional (OPEN; TRUE ~0.00769 vs 0.006, margin ~0.00169, 1.28x;
conditional-feasible lane). -/
theorem R22_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-6.75) : ℂ)) / 2) + 1)‖) :
    c / 3.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-6.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 (-6.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 (-6.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 (-6.75) : ℂ)) / 2))‖ ≤ 3.58 :=
    Door3GammaLow.R22_w_norm_le
  exact disc_lower_one _ c 3.58 hw0 hc hM0 (by norm_num)

/-- E01 conditional (OPEN; TRUE ~0.013 vs 0.01, margin ~0.003, 1.30x). -/
theorem E01_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-6.25) : ℂ)) / 2) + 1)‖) :
    c / 3.33 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-6.25) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 (-6.25) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 (-6.25) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 (-6.25) : ℂ)) / 2))‖ ≤ 3.33 :=
    Door3GammaLow.E01_w_norm_le
  exact disc_lower_one _ c 3.33 hw0 hc hM0 (by norm_num)

/-- R33 conditional (OPEN; TRUE ~0.0408 vs 0.032, margin ~0.0088, 1.28x). -/
theorem R33_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-4.75) : ℂ)) / 2) + 1)‖) :
    c / 2.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-4.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 (-4.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 (-4.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 (-4.75) : ℂ)) / 2))‖ ≤ 2.58 :=
    Door3GammaLow.R33_w_norm_le
  exact disc_lower_one _ c 2.58 hw0 hc hM0 (by norm_num)

/-- E08 conditional (OPEN; TRUE ~0.03 vs 0.02, margin ~0.01, 1.50x). -/
theorem E08_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 5.25 : ℂ)) / 2) + 1)‖) :
    c / 2.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 5.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 5.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 5.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 5.25 : ℂ)) / 2))‖ ≤ 2.83 :=
    Door3GammaLow.E08_w_norm_le
  exact disc_lower_one _ c 2.83 hw0 hc hM0 (by norm_num)

/-- R23 conditional (OPEN; TRUE ~0.0426 vs 0.032, margin ~0.0106, 1.33x). -/
theorem R23_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-4.75) : ℂ)) / 2) + 1)‖) :
    c / 2.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-4.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 (-4.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 (-4.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 (-4.75) : ℂ)) / 2))‖ ≤ 2.58 :=
    Door3GammaLow.R23_w_norm_le
  exact disc_lower_one _ c 2.58 hw0 hc hM0 (by norm_num)

/-- BA03 conditional (OPEN; batch-A header floor 0.015, TRUE not quoted in
low file; denominator `Door3GammaLow.BA03_w_norm_le`). -/
theorem BA03_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-4.75) : ℂ)) / 2) + 1)‖) :
    c / 2.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-4.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 (-4.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 (-4.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 (-4.75) : ℂ)) / 2))‖ ≤ 2.58 :=
    Door3GammaLow.BA03_w_norm_le
  exact disc_lower_one _ c 2.58 hw0 hc hM0 (by norm_num)

/-- R37 conditional (OPEN; TRUE ~0.157 vs 0.12, margin ~0.037, 1.31x). -/
theorem R37_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 3.25 : ℂ)) / 2) + 1)‖) :
    c / 1.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 3.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 3.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 3.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 3.25 : ℂ)) / 2))‖ ≤ 1.83 :=
    Door3GammaLow.R37_w_norm_le
  exact disc_lower_one _ c 1.83 hw0 hc hM0 (by norm_num)

/-- R27 conditional (OPEN; TRUE ~0.161 vs 0.12, margin ~0.041, 1.34x). -/
theorem R27_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 3.25 : ℂ)) / 2) + 1)‖) :
    c / 1.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 3.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 3.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 3.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 3.25 : ℂ)) / 2))‖ ≤ 1.83 :=
    Door3GammaLow.R27_w_norm_le
  exact disc_lower_one _ c 1.83 hw0 hc hM0 (by norm_num)

/-- R34 conditional (OPEN; TRUE ~0.25 vs 0.2, margin ~0.05, 1.25x). -/
theorem R34_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-2.75) : ℂ)) / 2) + 1)‖) :
    c / 1.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-2.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 (-2.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 (-2.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 (-2.75) : ℂ)) / 2))‖ ≤ 1.58 :=
    Door3GammaLow.R34_w_norm_le
  exact disc_lower_one _ c 1.58 hw0 hc hM0 (by norm_num)

/-- R24 conditional (OPEN; TRUE ~0.254 vs 0.2, margin ~0.054, 1.27x). -/
theorem R24_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-2.75) : ℂ)) / 2) + 1)‖) :
    c / 1.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-2.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 (-2.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 (-2.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 (-2.75) : ℂ)) / 2))‖ ≤ 1.58 :=
    Door3GammaLow.R24_w_norm_le
  exact disc_lower_one _ c 1.58 hw0 hc hM0 (by norm_num)

/-- E07 conditional (OPEN; TRUE ~0.169 vs 0.1, margin ~0.069, 1.69x). -/
theorem E07_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 3.25 : ℂ)) / 2) + 1)‖) :
    c / 1.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 3.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 3.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 3.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 3.25 : ℂ)) / 2))‖ ≤ 1.83 :=
    Door3GammaLow.E07_w_norm_le
  exact disc_lower_one _ c 1.83 hw0 hc hM0 (by norm_num)

/-- BA04 conditional (OPEN; batch-A header floor 0.08; denominator
`Door3GammaLow.BA04_w_norm_le`). -/
theorem BA04_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-2.75) : ℂ)) / 2) + 1)‖) :
    c / 1.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-2.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 (-2.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 (-2.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 (-2.75) : ℂ)) / 2))‖ ≤ 1.58 :=
    Door3GammaLow.BA04_w_norm_le
  exact disc_lower_one _ c 1.58 hw0 hc hM0 (by norm_num)

/-- R36 conditional (OPEN; TRUE ~1.16 vs 1, margin ~0.16, 1.16x). -/
theorem R36_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.105 1.25 : ℂ)) / 2) + 1)‖) :
    c / 0.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.105 1.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.105 1.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.105 1.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.105 1.25 : ℂ)) / 2))‖ ≤ 0.83 :=
    Door3GammaLow.R36_w_norm_le
  exact disc_lower_one _ c 0.83 hw0 hc hM0 (by norm_num)

/-- R26 conditional (OPEN; TRUE ~1.5 vs 1, margin ~0.5, 1.50x). -/
theorem R26_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 1.25 : ℂ)) / 2) + 1)‖) :
    c / 0.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 1.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 1.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 1.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 1.25 : ℂ)) / 2))‖ ≤ 0.83 :=
    Door3GammaLow.R26_w_norm_le
  exact disc_lower_one _ c 0.83 hw0 hc hM0 (by norm_num)

/-- E06 conditional (OPEN; TRUE ~2.5 vs 1, margin ~1.5, 2.50x). -/
theorem E06_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 1.25 : ℂ)) / 2) + 1)‖) :
    c / 0.83 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 1.25 : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 1.25 : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 1.25 : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 1.25 : ℂ)) / 2))‖ ≤ 0.83 :=
    Door3GammaLow.E06_w_norm_le
  exact disc_lower_one _ c 0.83 hw0 hc hM0 (by norm_num)

/-- R25 conditional (OPEN; TRUE ~5.0 vs 2, margin ~3.0, 2.50x; widest margin). -/
theorem R25_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-0.75) : ℂ)) / 2) + 1)‖) :
    c / 0.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-0.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.2 (-0.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.2 (-0.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.2 (-0.75) : ℂ)) / 2))‖ ≤ 0.58 :=
    Door3GammaLow.R25_w_norm_le
  exact disc_lower_one _ c 0.58 hw0 hc hM0 (by norm_num)

/-- E05 conditional (OPEN; TRUE ~4.4 vs 1.5, margin ~2.9, 2.93x). -/
theorem E05_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-0.75) : ℂ)) / 2) + 1)‖) :
    c / 0.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-0.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 (-0.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 (-0.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 (-0.75) : ℂ)) / 2))‖ ≤ 0.58 :=
    Door3GammaLow.E05_w_norm_le
  exact disc_lower_one _ c 0.58 hw0 hc hM0 (by norm_num)

/-- BA00 conditional (OPEN; batch-A header floor 0.0015; denominator
`Door3GammaLow.BA00_w_norm_le`). -/
theorem BA00_cond (c : ℝ)
    (hc : c ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-8.75) : ℂ)) / 2) + 1)‖) :
    c / 4.58 ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-8.75) : ℂ)) / 2))‖ := by
  have him : 0 < |((((Complex.mk 0.395 (-8.75) : ℂ)) / 2)).im| := by
    simp
    norm_num
  have hw0 : ((((Complex.mk 0.395 (-8.75) : ℂ)) / 2)) ≠ 0 := w_ne_zero_of_im _ him
  have hM0 : ‖((((Complex.mk 0.395 (-8.75) : ℂ)) / 2))‖ ≤ 4.58 :=
    Door3GammaLow.BA00_w_norm_le
  exact disc_lower_one _ c 4.58 hw0 hc hM0 (by norm_num)

/-! ## Discharge record + remainder (honest split).

LOWERS CLOSED: 0 of 30. Every `Door3GammaLow.gammaLow_*_ge` stays OPEN
unconditionally. Closed here instead:
* general `disc_shift_norm_nat` + `disc_shift_lower_nat` (k-step, from
  `Complex.Gamma_add_one` iterated);
* instantiations `disc_lower_one_cast`, `disc_lower_one`, `disc_lower_two`;
* nonvanishing helpers `w_ne_zero_of_im`, `w1_ne_zero_of_im`;
* 30 per-center CONDITIONAL lowers `R28_cond`, `R35_cond`, `R38_cond`,
  `R29_cond`, `E10/R31/R40/R21/R30/R39/E09/R32/R22/E01/R33/E08/R23/BA03/
  R37/R27/R34/R24/E07/BA04/R36/R26/E06/R25/E05/BA00_cond`, each paying the
  exact banked denominator upper(s) named in its doc string (34 factors
  total, all by reference, none reproved).
DENOMINATORS: all 34 by reference to `Door3GammaLow.*_w_norm_le`.
FALSE FLOORS: none declared false. All 30 floors sit below the TRUE Stirling
estimates quoted per theorem, so each deficit is negative (margin positive);
tightest overall is R28 (TRUE ~0.0274 vs 0.026, margin ~0.0014, 1.05x);
tightest of the 26 is E10 (~0.00166 vs 0.0015, margin ~0.00016, 1.11x).
Nothing was forced.
REMAINDER (next wave): all 30 unconditional lowers. What blocks them:
(a) no banked complex-Gamma numerator lower exists: `D3SG_*` gives only
uppers, and every `D3SG_Real_Gamma_*` / `D3SG_CHI_Real_Gamma_*` numeral is a
real upper (`≤ 4`, `≤ 1.1`, `≤ 20`, `≤ 200`, `≤ 1` on `[1,2]`, `≤ 2`), so the
naive real-Gamma-as-lower step is unsound (reverses
`D3SG_Gamma_norm_le_real`);
(b) reflection `‖Γ(w)‖ = π / (‖sin πw‖ * ‖Γ(1-w)‖)` with banked
`D3SG_CHI_sin_le_exp_abs_im` and `D3SG_TierC_gamma_rect` (`60 * exp(-|Im|/2)`)
yields only ~0.019 at `|Im| = 0.375` (R35 needs 2) and ~5e-05 at
`|Im| = 2.625` (R28 needs 0.026): 2-3 orders short; the banked `c = 1/2`
rate cannot cancel `exp(π|Im|)` growth, so the `π/2` rate lane
(`door3_gamma_pi2.lean`, open full-tail route) plus explicit Stirling-disc
enclosures at shifted `Re ∈ [1,2]` with a real LOWER (e.g. `Γ ≥ 0.88` on
`[1,2]`) are required; no `Re < 0.005` sliver center occurs here (smallest
shifted `Re` is `1.0525`), so the sliver subcase contributes no extra
blocker beyond (a);
(c) feasibility-negative cells R31/R32/R39/R40/R21/R30 plus R22/R28
conditional cells stay in the re-tier/subdivision lane.
-/

end Door3GammaDisc
