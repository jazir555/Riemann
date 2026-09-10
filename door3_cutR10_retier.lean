import Mathlib
import central_cover_assembly

/-! # Door-3 CutR10 fencing retier (design record, write-only)

Context (taken as given, not re-derived here):
fencing needs `eps + M * radius <= center` with `CutR10.radius < 0.56`.
The banked center floor is `(401 / 8) * (3 / 4) * (1 / 2000) * (7 / 5)
= 8421 / 320000` (see `Door3CutR10Center.cutR10_center_bound_of_gamma_zeta`
in `central_cover_assembly`). The true center value is about `0.038`.
The closed-ball sup `‖xiShiftedEntire‖ <= 0.04` on
`closedBall CutR10.center (CutR10.radius + 1)` is not attainable as stated:
the honest factor-separated reach is `67 * (16 / 5) * (1 / 100) * 6
= 12.864 <= 12.87` (see `door3_cutR10_ballsup`).

This file proves only the ARITHMETIC of the tier comparison (all numeric
goals closed by `norm_num`) and states each tier as an explicit conditional
theorem with premise shapes for the matching supplier:
ball-sup-sharp, shrunken-ball deriv, or thin s-rect sups.
No existing file is touched. Central registration happens later.
-/

open CentralCoverAssembly

namespace Door3CutR10Retier

/-! ## Arithmetic: center floor and original need. -/

/-- Product floor identity used by the banked center bound. -/
theorem center_floor_eq :
    (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5) = 8421 / 320000 := by
  norm_num

/-- Original tier need at the radius cap `0.56`. -/
theorem orig_need_eq :
    (0.001 : ℝ) + 0.04 * 0.56 = 117 / 5000 := by
  norm_num

/-- Original tier closes against the certified floor (center side only). -/
theorem orig_need_le_floor :
    (117 / 5000 : ℝ) ≤ 8421 / 320000 := by
  norm_num

/-! ## Arithmetic: sharp joint sup. -/

/-- Honest factor-separated product value. -/
theorem sharp_product_eq :
    (67 : ℝ) * (16 / 5) * (1 / 100) * 6 = 12.864 := by
  norm_num

/-- Sharp product fits under the stated cap. -/
theorem sharp_product_le_cap :
    (12.864 : ℝ) ≤ 12.87 := by
  norm_num

/-! ## Tier A: keep `eps = 0.001` with honest `M` (infeasible). -/

/-- Honest need with `M = 12.87` at the radius cap. -/
theorem honest_need_eq :
    (0.001 : ℝ) + 12.87 * 0.56 = 7.2082 := by
  norm_num

/-- Honest need exceeds the certified floor. -/
theorem honest_need_gt_floor :
    (8421 / 320000 : ℝ) < (0.001 : ℝ) + 12.87 * 0.56 := by
  norm_num

/-- Honest need exceeds the true-center cap `0.037`. -/
theorem honest_need_gt_true :
    (0.037 : ℝ) < (0.001 : ℝ) + 12.87 * 0.56 := by
  norm_num

/-- Keeping `eps = 0.001` against the certified floor forces `M <= 0.046`. -/
theorem tierA_Mcap_of_floor (M : ℝ)
    (h : (0.001 : ℝ) + M * 0.56 ≤ 8421 / 320000) :
    M ≤ (0.046 : ℝ) := by
  have hfloor : (8421 / 320000 : ℝ) ≤ 0.02632 := by
    norm_num
  linarith

/-- Keeping `eps = 0.001` against the true-center cap forces `M <= 0.066`. -/
theorem tierA_Mcap_of_true (M : ℝ)
    (h : (0.001 : ℝ) + M * 0.56 ≤ 0.037) :
    M ≤ (0.066 : ℝ) := by
  linarith

/-- Sharp `M = 12.87` cannot meet the certified floor need. -/
theorem tierA_sharp_infeasible_of_floor (M : ℝ)
    (hM : M = (12.87 : ℝ))
    (h : (0.001 : ℝ) + M * 0.56 ≤ 8421 / 320000) :
    False := by
  rw [hM] at h
  have hlt := honest_need_gt_floor
  linarith

/-- Sharp `M = 12.87` cannot meet the true-center need either. -/
theorem tierA_sharp_infeasible_of_true (M : ℝ)
    (hM : M = (12.87 : ℝ))
    (h : (0.001 : ℝ) + M * 0.56 ≤ 0.037) :
    False := by
  rw [hM] at h
  have hlt := honest_need_gt_true
  linarith

/-! ## Tier B: shrunken fencing radius (feasible arithmetically). -/

/-- Triple `(0.001, 12.87, 0.001)` meets the certified floor. -/
theorem shrunken_triple_le_floor :
    (0.001 : ℝ) + 12.87 * 0.001 ≤ 8421 / 320000 := by
  norm_num

/-- Triple `(0.001, 12.87, 0.002)` meets the true-center cap. -/
theorem shrunken_triple_le_true :
    (0.001 : ℝ) + 12.87 * 0.002 ≤ 0.037 := by
  norm_num

/-- Triple `(0.001, 12.87, 0.002)` misses the certified floor. -/
theorem shrunken_002_gt_floor :
    (8421 / 320000 : ℝ) < (0.001 : ℝ) + 12.87 * 0.002 := by
  norm_num

/-! ## Premise shapes per tier (supplier-owned). -/

/-- Tier-A supplier shape: sharp joint sup over the full ball (true order). -/
def ballSupSharp : Prop :=
  ∀ (z : ℂ),
    z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (12.87 : ℝ)

/-- Tier-C supplier shapes: zeta upper on the thin s-rect
`Re in [0.01, 0.99]`, `Im in [9.75, 10.25]` (image of `CutR10`
under `s = 1 / 2 + I * z`). -/
def sRectZetaSup (C : ℝ) : Prop :=
  ∀ (s : ℂ),
    (0.01 : ℝ) ≤ s.re → s.re ≤ (0.99 : ℝ) →
      (9.75 : ℝ) ≤ s.im → s.im ≤ (10.25 : ℝ) → ‖zeta s‖ ≤ C

/-- Tier-C supplier shapes: Gamma upper on the same thin s-rect. -/
def sRectGammaSup (C : ℝ) : Prop :=
  ∀ (s : ℂ),
    (0.01 : ℝ) ≤ s.re → s.re ≤ (0.99 : ℝ) →
      (9.75 : ℝ) ≤ s.im → s.im ≤ (10.25 : ℝ) →
        ‖Complex.Gamma (s / 2)‖ ≤ C

/-- Revised deriv remainder shape: uniform bound on the thin rect only.
The supplier bridge must land this from the two s-rect sups above
instead of from the fat-ball sup. -/
def thinDerivRemainder (M : ℝ) : Prop :=
  ∀ (w : ℂ), CutR10.mem w → ‖deriv xiShifted w‖ ≤ M

/-! ## Conditional tier theorems. -/

/-- Tier B: shrunken-rect fencing from the honest `M = 12.87`.
For any rect sharing the `CutR10` center with radius at most `0.001`,
the triple `(0.001, 12.87)` fences once the floor holds at its center. -/
theorem tierB_shrunken_fencing (R : CellProofEngine.Rect2D)
    (hC : R.center = CutR10.center)
    (hRad : R.radius ≤ (0.001 : ℝ))
    (hDeriv : ∀ (w : ℂ), R.mem w → ‖deriv xiShifted w‖ ≤ (12.87 : ℝ))
    (hFloor : (8421 / 320000 : ℝ) ≤ ‖xiShifted R.center‖) :
    CellFencingHypotheses R 0.001 12.87 := by
  refine ⟨by norm_num, fun (w : ℂ) (hw : R.mem w) => hDeriv w hw, ?_⟩
  have hneed : (0.001 : ℝ) + 12.87 * R.radius ≤ 8421 / 320000 := by
    have hM : 12.87 * R.radius ≤ 12.87 * 0.001 :=
      mul_le_mul_of_nonneg_left hRad (by norm_num)
    have hcap : (0.001 : ℝ) + 12.87 * 0.001 ≤ 8421 / 320000 :=
      shrunken_triple_le_floor
    linarith
  exact le_trans hneed hFloor

/-- Tier C: keep `(0.001, 0.04)` on `CutR10`, with the deriv premise in the
revised thin-rect shape. Center side reuses the banked
`cutR10_center_bound_of_gamma_zeta`; only the deriv supplier changes. -/
theorem tierC_thin_fencing
    (hD : thinDerivRemainder 0.04)
    (hG : (1 / 2000 : ℝ) ≤
      ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2)‖)
    (hZ : (7 / 5 : ℝ) ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * CutR10.center)‖) :
    CellFencingHypotheses CutR10 0.001 0.04 := by
  refine ⟨by norm_num, fun (w : ℂ) (hw : CutR10.mem w) => hD w hw, ?_⟩
  exact Door3CutR10Center.cutR10_center_bound_of_gamma_zeta hG hZ

/-! ## Margins. -/

/-- Recommended Tier-C margin against the certified floor (at least `0.0029`). -/
theorem recommended_margin_floor_pos :
    (0.0029 : ℝ) ≤ 8421 / 320000 - (0.001 + 0.04 * 0.56) := by
  norm_num

/-- Recommended Tier-C margin against the true-center value. -/
theorem recommended_margin_true_pos :
    (0.014 : ℝ) ≤ 0.038 - (0.001 + 0.04 * 0.56) := by
  norm_num

/-- Alternative Tier-B margin against the certified floor. -/
theorem alternativeB_margin_floor_pos :
    (0.0124 : ℝ) ≤ 8421 / 320000 - (0.001 + 12.87 * 0.001) := by
  norm_num

/-! ## Recommendation (coordinator decision material).

RECOMMENDED: Tier C — keep `(eps, M) = (0.001, 0.04)` on `CutR10`
(`tierC_thin_fencing`). Numeric justification: need `0.001 + 0.04 * 0.56
= 0.0234` against floor `8421 / 320000 = 0.026315625`, margin at least
`0.0029` (`recommended_margin_floor_pos`, about 11 percent); against the
true center `0.038`, margin at least `0.014` (`recommended_margin_true_pos`,
about 38 percent). Single cell, center proof reused unchanged.

ALTERNATIVES with numbers:
* Tier A (keep `eps = 0.001`, honest `M = 12.87`): need `7.2082`
  (`honest_need_eq`), exceeds floor (`honest_need_gt_floor`) and true cap
  (`honest_need_gt_true`); feasible `M` would need `M <= 0.046` vs floor
  (`tierA_Mcap_of_floor`) or `M <= 0.066` vs true cap (`tierA_Mcap_of_true`),
  two orders below the sharp `12.87`. Infeasible.
* Tier B (shrunken radius `rho = 0.001`, `(0.001, 12.87)`):
  need `0.01387` meets floor (`shrunken_triple_le_floor`) with margin at
  least `0.0124` (`alternativeB_margin_floor_pos`); `rho = 0.002` meets only
  the true cap (`shrunken_triple_le_true`) and misses floor
  (`shrunken_002_gt_floor`). Feasible arithmetically but needs subdivision
  of `CutR10` into sub-cells of radius `0.001` plus per-cell centers:
  large patch cost versus Tier C.

PATCH REMAINDER (patch phase, not this file):
* Keep `cutR10_center_bound_of_gamma_zeta` and Gamma/zeta lower suppliers.
* Replace the deriv supplier `cutR10_derivRemainder_of_closedBall_sup`
  (fat-ball `0.04` sup) with a thin s-rect bridge landing
  `thinDerivRemainder 0.04` from `sRectZetaSup` + `sRectGammaSup` on
  `Re in [0.01, 0.99]`, `Im in [9.75, 10.25]`.
* Rewire `cutR10_fencing_of_remainders` consumers to `tierC_thin_fencing`;
  keep Tier-B triple as fallback if the thin-bridge stalls.
-/

end Door3CutR10Retier
