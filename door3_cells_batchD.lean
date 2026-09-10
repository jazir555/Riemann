import Mathlib
import central_cover_assembly

/-!
# Door 3 THIRD-ROW batch D (`door3_cells_batchD.lean`, NEW file, exclusive owner: batch-D agent)

WRITE-ONLY replication of the `door3_first_cell.lean` 12-step template for the
THIRD row only (`y = (0.2, 0.4)`, the only row with no batch). No build performed
(no lake/lean commands); patch phase later. No other repo file touched
(including `riemann hypothesis.lean` under any spelling and all sibling batches).

## CLAIMED CELLS (this file owns ONLY these ten; siblings own the rest)

Bottom row `(0.01,0.2)` (batch A + first-cell R02), second row `(0.1,0.3)`
(batch B, R11-R20), and top row `(0.3,0.49)` (batch C, R31-R40) are OUT OF
SCOPE. This file claims ONLY the ten `(0.2,0.4)` cells below (R21-R30).

| cell | x-interval | y-interval | z-center (rect center) | s-center `1/2+I*z` | radius | tier `(eps,M)` |
| R21 | (-10,-7.5) | (0.2,0.4) | -8.75+0.3I | 0.2-8.75I | sqrt(1.25^2+0.1^2)<1.26 | (0.002,0.05) outer |
| R22 | (-8,-5.5) | (0.2,0.4) | -6.75+0.3I | 0.2-6.75I | same <1.26 | (0.002,0.07) leaf-mismatch |
| R23 | (-6,-3.5) | (0.2,0.4) | -4.75+0.3I | 0.2-4.75I | same <1.26 | (0.05,0.07) mid |
| R24 | (-4,-1.5) | (0.2,0.4) | -2.75+0.3I | 0.2-2.75I | same <1.26 | (0.05,0.07) mid |
| R25 | (-2,0.5) | (0.2,0.4) | -0.75+0.3I | 0.2-0.75I | same <1.26 | (0.15,0.06) inner |
| R26 | (0,2.5) | (0.2,0.4) | 1.25+0.3I | 0.2+1.25I | same <1.26 | (0.15,0.06) inner |
| R27 | (2,4.5) | (0.2,0.4) | 3.25+0.3I | 0.2+3.25I | same <1.26 | (0.05,0.07) mid |
| R28 | (4,6.5) | (0.2,0.4) | 5.25+0.3I | 0.2+5.25I | same <1.26 | (0.05,0.07) mid |
| R29 | (6,8.5) | (0.2,0.4) | 7.25+0.3I | 0.2+7.25I | same <1.26 | (0.002,0.07) leaf-mismatch |
| R30 | (7.5,10) | (0.2,0.4) | 8.75+0.3I | 0.2+8.75I | same <1.26 | (0.002,0.05) outer |

Tiers match the banked `RXX_leaf_obligations` in `central_cover_assembly.lean`
(R21 outer, R22 leaf `(0.002,0.07)`, R23 mid, R24 mid, R25 inner, R26 inner,
R27 mid, R28 mid, R29 leaf `(0.002,0.07)`, R30 outer).
DISCREPANCY (read-only finding, flagged, same class as batch-B R12/R19): the
section headers for R22/R29 say "outer tier `(0.002,0.05)`" but the LEAF DEFS
use `M = 0.07`. This file follows the LEAF DEFS (authoritative for obligations).
Cell inventory: `CellData` (line 111), `innerGridY` (line 372, rows
`[(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]`), `fineGridX` (line 954, 10 columns
width 2.5), `gridFine` (line 1002, 40 cells), `FullCentralObligations`
(`BottomRowObligations` + `UpperRowsObligations`), H-leaf
`inner_nonvanishing_of_fenced_grid_fine` (line 1047).

## BANKED-NAME VERIFICATION RECORD (all read-only, all exist, none touched)

* `CentralCoverAssembly.R21..R30`, `RXX_strip_lo/hi`, `RXX_dx_eq/dy_eq/radius_eq`,
  `RXX_radius_lt`, `RXX_mem_gridFine`, `RXX_leaf_obligations`
  (per-cell sections ~line 3330-4160).
* `CentralCoverAssembly.sample_cell_radius_01_bound` (dy `0.1` radius cap),
  `fine_eps_outer_pos/mid_pos/inner_pos`, `CellFencingHypotheses`,
  `lowerBoundRect_of_fencingHypotheses_strip`,
  `zeroFreeRect_of_rect_center_bound_strip`,
  `xi_rect_lower_bound_of_center_bound_strip`, `xiShiftedEntire`,
  `fineGridX`/`innerGridY`/`gridFine`.
* `DerivCauchyBridge.norm_xiShifted_eq_parts`,
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`,
  `DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem`,
  `DerivCauchyBridge.polyOf/piOf/gammaOf`.
* `TailProofEngine.prod_four_ge_of_ge` (`rh_certificate_infra.lean`,
  transitive via `central_cover_assembly` import).
* Deliberately NOT cited (row-specific, do not apply to these s-centers):
  `R02Pilot.*`, `R02GammaDisc.*`, `P1_R02_unconditional`,
  `Door3DownstreamDischarge.*`. All four factor floors below are therefore
  explicit premises (honest wall).
* Imports: `Mathlib` + `central_cover_assembly` only. No extra imports
  (no cycle risk to flag).

## GAMMA IM-DECAY HONESTY (numbers)

s-centers here have `Re = 0.2` (vs `0.395` bottom, `0.3` second row, `0.105`
top). Stirling estimates for TRUE `|gammaOf|` at `s/2 = 0.1 + t*I`:
t=8.75 ~= 0.00143; 6.75 ~= 0.00769; 4.75 ~= 0.0426; 2.75 ~= 0.254;
0.75 ~= 5.0; 1.25 ~= 1.5; 3.25 ~= 0.161; 5.25 ~= 0.0274; 7.25 ~= 0.00504.
Center-true ~= poly*0.892*gamma*1 with poly ~= |s|^2/2-scale:
R21 ~= 0.049 vs budget 0.065; R30 ~= 0.049 vs 0.065.
Hence R21/R30 are FEASIBILITY-NEGATIVE at TRUE factor scales (proved
negative-margin theorems below, pattern of batch-C R31/R32/R39/R40); R22-R29
are CLOSED-CONDITIONAL (R28/R29 tight, headrooms 1.05-1.12x, flagged per cell).

## PER-CELL STATUS

* R21: feasibility-NEGATIVE (0.015 < 0.065 at TRUE-scale floors).
* R22: CLOSED-conditional (threshold 0.096 >= 0.0902; gamma headroom 1.28x).
* R23: CLOSED-conditional (threshold 0.144 >= 0.1382; gamma headroom 1.33x).
* R24: CLOSED-conditional (threshold 0.3 >= 0.1382).
* R25: CLOSED-conditional (threshold 0.25 >= 0.2256).
* R26: CLOSED-conditional (threshold 0.25 >= 0.2256).
* R27: CLOSED-conditional (threshold 0.24 >= 0.1382).
* R28: CLOSED-conditional TIGHT (threshold 0.143 >= 0.1382; gamma 1.05x).
* R29: CLOSED-conditional TIGHT (threshold 0.0918 >= 0.0902; floors 1.05-1.12x).
* R30: feasibility-NEGATIVE (0.015 < 0.065 at TRUE-scale floors).

## PATCH REMAINDER

Build verification on this file; poly/pi TRUE-floor measurement at the ten
s-centers (currently conservative premises); gamma-lower enclosures
(Stirling-disc treatment, the documented wall); zeta-lower enclosures
(complex-zeta wall); tight-premise discharge for R28/R29; re-tiering or
subdivision for R21/R30 (margin deficits -0.05 each at TRUE scale); central
registration (NOT here).
-/

noncomputable section

namespace Door3BatchD

/-! ## R21 = (-10,-7.5,0.2,0.4), outer tier (0.002,0.05): FEASIBILITY-NEGATIVE -/

def BD_rect_R21 : CellProofEngine.Rect2D := CentralCoverAssembly.R21

theorem BD_R21_x0 : BD_rect_R21.x0 = -10 := rfl
theorem BD_R21_x1 : BD_rect_R21.x1 = -7.5 := rfl
theorem BD_R21_y0 : BD_rect_R21.y0 = 0.2 := rfl
theorem BD_R21_y1 : BD_rect_R21.y1 = 0.4 := rfl

theorem BD_R21_width_eq : BD_rect_R21.x1 - BD_rect_R21.x0 = 2.5 := by
  rw [BD_R21_x0, BD_R21_x1]; norm_num

theorem BD_R21_strip_lo : -(1 / 2 : ℝ) < BD_rect_R21.y0 :=
  CentralCoverAssembly.R21_strip_lo
theorem BD_R21_strip_hi : BD_rect_R21.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R21_strip_hi

theorem BD_R21_dx : BD_rect_R21.dx = 1.25 :=
  CentralCoverAssembly.R21_dx_eq
theorem BD_R21_dy : BD_rect_R21.dy = 0.1 :=
  CentralCoverAssembly.R21_dy_eq
theorem BD_R21_radius_eq :
    BD_rect_R21.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R21_radius_eq
theorem BD_R21_radius_lt : BD_rect_R21.radius < 1.26 := by
  rw [BD_R21_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R21_strip_of_mem {w : ℂ} (hw : BD_rect_R21.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R21_y0] at hy0
  rw [BD_R21_y1] at hy1
  constructor <;> linarith

theorem BD_R21_mem_gridFine : (-10, -7.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R21_mem_gridFine

/-- R21 s-center `s = 1/2 + I*center` (z = -8.75 + 0.3*I, so s = 0.2 - 8.75*I). -/
noncomputable def BD_sC21 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R21.center

/-- Poly lower at R21 s-center. TRUE ~= 38.4 (premise floor 30, conservative). -/
def BD_polyLower_R21 : Prop :=
  (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC21‖

/-- Pi lower at R21 s-center. TRUE ~= 0.892 (premise floor 1/2). -/
def BD_piLower_R21 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC21‖

/-- Gamma lower at R21 s-center. TRUE ~= 0.00143 (floor 0.001, headroom 1.43x). -/
def BD_gammaLower_R21 : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC21‖

/-- Zeta lower at R21 s-center. TRUE unmeasured O(1) (the wall). -/
def BD_zetaLower_R21 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC21‖

/-- Tier deriv bound (matches `R21_leaf_obligations` shape). TRUE unknown. -/
def BD_derivTier_R21 : Prop :=
  ∀ w, BD_rect_R21.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

/-- Closed-ball sup for the Cauchy route (C=16800, r=0.25 pattern). -/
def BD_ballSup_R21 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R21.center (BD_rect_R21.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Negative margin at TRUE-scale floors: 30*0.5*0.001*1 = 0.015 < 0.065. -/
theorem BD_R21_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by norm_num

theorem BD_R21_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R21_deriv_of_ballSup (hBall : BD_ballSup_R21) :
    ∀ w, BD_rect_R21.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R21 0.25 16800 (by norm_num) (fun w hw => BD_R21_strip_of_mem hw) hBall

/-- Honest gap: Cauchy M = 67200 misses the (0.002,0.05) tier. -/
theorem BD_R21_cauchy_tier_mismatch :
    (0.05 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R21_sphere_of_ballSup (hBall : BD_ballSup_R21)
    (w : ℂ) (hw : BD_rect_R21.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R21 0.25 w hw hz)

theorem BD_R21_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC21‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC21‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC21‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC21‖)
    (hThresh : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R21.center = BD_sC21 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R21.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R21.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * BD_rect_R21.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R21_radius_lt) (by norm_num)
  linarith

theorem BD_R21_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R21 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BD_R21_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R21 0.002 0.05 BD_R21_strip_lo BD_R21_strip_hi
    (BD_R21_fencing_of_premises hC hD)

noncomputable def BD_R21_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R21 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BD_R21_strip_lo BD_R21_strip_hi hD hC

theorem BD_R21_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21) {z : ℂ}
    (hx0 : BD_rect_R21.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R21.x1)
    (hy0 : BD_rect_R21.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R21.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R21 0.002 0.05 BD_R21_strip_lo BD_R21_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BD_R21_H_instance
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-10, -7.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R21, 0.002, 0.05, rfl, rfl, rfl, rfl, BD_R21_strip_lo, BD_R21_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BD_R21_implies_leaf
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R21.radius ≤ ‖xiShifted BD_rect_R21.center‖)
    (hD : BD_derivTier_R21) :
    CentralCoverAssembly.R21_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R22 = (-8,-5.5,0.2,0.4), leaf tier (0.002,0.07): CLOSED-CONDITIONAL -/

def BD_rect_R22 : CellProofEngine.Rect2D := CentralCoverAssembly.R22

theorem BD_R22_x0 : BD_rect_R22.x0 = -8 := rfl
theorem BD_R22_x1 : BD_rect_R22.x1 = -5.5 := rfl
theorem BD_R22_y0 : BD_rect_R22.y0 = 0.2 := rfl
theorem BD_R22_y1 : BD_rect_R22.y1 = 0.4 := rfl

theorem BD_R22_width_eq : BD_rect_R22.x1 - BD_rect_R22.x0 = 2.5 := by
  rw [BD_R22_x0, BD_R22_x1]; norm_num

theorem BD_R22_strip_lo : -(1 / 2 : ℝ) < BD_rect_R22.y0 :=
  CentralCoverAssembly.R22_strip_lo
theorem BD_R22_strip_hi : BD_rect_R22.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R22_strip_hi

theorem BD_R22_dx : BD_rect_R22.dx = 1.25 :=
  CentralCoverAssembly.R22_dx_eq
theorem BD_R22_dy : BD_rect_R22.dy = 0.1 :=
  CentralCoverAssembly.R22_dy_eq
theorem BD_R22_radius_eq :
    BD_rect_R22.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R22_radius_eq
theorem BD_R22_radius_lt : BD_rect_R22.radius < 1.26 := by
  rw [BD_R22_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R22_strip_of_mem {w : ℂ} (hw : BD_rect_R22.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R22_y0] at hy0
  rw [BD_R22_y1] at hy1
  constructor <;> linarith

theorem BD_R22_mem_gridFine : (-8, -5.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R22_mem_gridFine

noncomputable def BD_sC22 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R22.center

/-- Poly lower at R22 s-center. TRUE ~= 22.9 (floor 20, headroom 1.15x). -/
def BD_polyLower_R22 : Prop :=
  (20 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC22‖

/-- Pi lower at R22 s-center. TRUE ~= 0.892 (floor 0.8, headroom 1.11x). -/
def BD_piLower_R22 : Prop :=
  (0.8 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC22‖

/-- Gamma lower at R22 s-center. TRUE ~= 0.00769 (floor 0.006, 1.28x). -/
def BD_gammaLower_R22 : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC22‖

/-- Zeta lower at R22 s-center. TRUE unmeasured O(1) (the wall). -/
def BD_zetaLower_R22 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC22‖

def BD_derivTier_R22 : Prop :=
  ∀ w, BD_rect_R22.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R22 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R22.center (BD_rect_R22.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 20*0.8*0.006 = 0.096 >= 0.002+0.07*1.26 = 0.0902. -/
theorem BD_R22_threshold_check :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ (20 : ℝ) * 0.8 * 0.006 * 1 := by norm_num

theorem BD_R22_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R22_deriv_of_ballSup (hBall : BD_ballSup_R22) :
    ∀ w, BD_rect_R22.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R22 0.25 16800 (by norm_num) (fun w hw => BD_R22_strip_of_mem hw) hBall

theorem BD_R22_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R22_sphere_of_ballSup (hBall : BD_ballSup_R22)
    (w : ℂ) (hw : BD_rect_R22.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R22 0.25 w hw hz)

theorem BD_R22_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC22‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC22‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC22‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC22‖)
    (hThresh : (0.002 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R22.center = BD_sC22 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R22.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R22.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R22.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R22_radius_lt) (by norm_num)
  linarith

theorem BD_R22_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R22 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BD_R22_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R22 0.002 0.07 BD_R22_strip_lo BD_R22_strip_hi
    (BD_R22_fencing_of_premises hC hD)

noncomputable def BD_R22_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R22 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    BD_R22_strip_lo BD_R22_strip_hi hD hC

theorem BD_R22_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22) {z : ℂ}
    (hx0 : BD_rect_R22.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R22.x1)
    (hy0 : BD_rect_R22.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R22.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R22 0.002 0.07 BD_R22_strip_lo BD_R22_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BD_R22_H_instance
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R22, 0.002, 0.07, rfl, rfl, rfl, rfl, BD_R22_strip_lo, BD_R22_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BD_R22_implies_leaf
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R22.radius ≤ ‖xiShifted BD_rect_R22.center‖)
    (hD : BD_derivTier_R22) :
    CentralCoverAssembly.R22_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R23 = (-6,-3.5,0.2,0.4), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BD_rect_R23 : CellProofEngine.Rect2D := CentralCoverAssembly.R23

theorem BD_R23_x0 : BD_rect_R23.x0 = -6 := rfl
theorem BD_R23_x1 : BD_rect_R23.x1 = -3.5 := rfl
theorem BD_R23_y0 : BD_rect_R23.y0 = 0.2 := rfl
theorem BD_R23_y1 : BD_rect_R23.y1 = 0.4 := rfl

theorem BD_R23_width_eq : BD_rect_R23.x1 - BD_rect_R23.x0 = 2.5 := by
  rw [BD_R23_x0, BD_R23_x1]; norm_num

theorem BD_R23_strip_lo : -(1 / 2 : ℝ) < BD_rect_R23.y0 :=
  CentralCoverAssembly.R23_strip_lo
theorem BD_R23_strip_hi : BD_rect_R23.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R23_strip_hi

theorem BD_R23_dx : BD_rect_R23.dx = 1.25 :=
  CentralCoverAssembly.R23_dx_eq
theorem BD_R23_dy : BD_rect_R23.dy = 0.1 :=
  CentralCoverAssembly.R23_dy_eq
theorem BD_R23_radius_eq :
    BD_rect_R23.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R23_radius_eq
theorem BD_R23_radius_lt : BD_rect_R23.radius < 1.26 := by
  rw [BD_R23_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R23_strip_of_mem {w : ℂ} (hw : BD_rect_R23.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R23_y0] at hy0
  rw [BD_R23_y1] at hy1
  constructor <;> linarith

theorem BD_R23_mem_gridFine : (-6, -3.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R23_mem_gridFine

noncomputable def BD_sC23 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R23.center

/-- Poly lower at R23 s-center. TRUE ~= 11.4 (floor 9, conservative). -/
def BD_polyLower_R23 : Prop :=
  (9 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC23‖

def BD_piLower_R23 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC23‖

/-- Gamma lower at R23 s-center. TRUE ~= 0.0426 (floor 0.032, 1.33x). -/
def BD_gammaLower_R23 : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC23‖

def BD_zetaLower_R23 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC23‖

def BD_derivTier_R23 : Prop :=
  ∀ w, BD_rect_R23.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R23 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R23.center (BD_rect_R23.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 9*0.5*0.032 = 0.144 >= 0.05+0.07*1.26 = 0.1382. -/
theorem BD_R23_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (9 : ℝ) * (1 / 2) * 0.032 * 1 := by norm_num

theorem BD_R23_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R23_deriv_of_ballSup (hBall : BD_ballSup_R23) :
    ∀ w, BD_rect_R23.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R23 0.25 16800 (by norm_num) (fun w hw => BD_R23_strip_of_mem hw) hBall

theorem BD_R23_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R23_sphere_of_ballSup (hBall : BD_ballSup_R23)
    (w : ℂ) (hw : BD_rect_R23.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R23 0.25 w hw hz)

theorem BD_R23_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC23‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC23‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC23‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC23‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R23.center = BD_sC23 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R23.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R23.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R23.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R23_radius_lt) (by norm_num)
  linarith

theorem BD_R23_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R23 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BD_R23_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R23 0.05 0.07 BD_R23_strip_lo BD_R23_strip_hi
    (BD_R23_fencing_of_premises hC hD)

noncomputable def BD_R23_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R23 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BD_R23_strip_lo BD_R23_strip_hi hD hC

theorem BD_R23_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23) {z : ℂ}
    (hx0 : BD_rect_R23.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R23.x1)
    (hy0 : BD_rect_R23.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R23.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R23 0.05 0.07 BD_R23_strip_lo BD_R23_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BD_R23_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-6, -3.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R23, 0.05, 0.07, rfl, rfl, rfl, rfl, BD_R23_strip_lo, BD_R23_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BD_R23_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R23.radius ≤ ‖xiShifted BD_rect_R23.center‖)
    (hD : BD_derivTier_R23) :
    CentralCoverAssembly.R23_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R24 = (-4,-1.5,0.2,0.4), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BD_rect_R24 : CellProofEngine.Rect2D := CentralCoverAssembly.R24

theorem BD_R24_x0 : BD_rect_R24.x0 = -4 := rfl
theorem BD_R24_x1 : BD_rect_R24.x1 = -1.5 := rfl
theorem BD_R24_y0 : BD_rect_R24.y0 = 0.2 := rfl
theorem BD_R24_y1 : BD_rect_R24.y1 = 0.4 := rfl

theorem BD_R24_width_eq : BD_rect_R24.x1 - BD_rect_R24.x0 = 2.5 := by
  rw [BD_R24_x0, BD_R24_x1]; norm_num

theorem BD_R24_strip_lo : -(1 / 2 : ℝ) < BD_rect_R24.y0 :=
  CentralCoverAssembly.R24_strip_lo
theorem BD_R24_strip_hi : BD_rect_R24.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R24_strip_hi

theorem BD_R24_dx : BD_rect_R24.dx = 1.25 :=
  CentralCoverAssembly.R24_dx_eq
theorem BD_R24_dy : BD_rect_R24.dy = 0.1 :=
  CentralCoverAssembly.R24_dy_eq
theorem BD_R24_radius_eq :
    BD_rect_R24.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R24_radius_eq
theorem BD_R24_radius_lt : BD_rect_R24.radius < 1.26 := by
  rw [BD_R24_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R24_strip_of_mem {w : ℂ} (hw : BD_rect_R24.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R24_y0] at hy0
  rw [BD_R24_y1] at hy1
  constructor <;> linarith

theorem BD_R24_mem_gridFine : (-4, -1.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R24_mem_gridFine

noncomputable def BD_sC24 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R24.center

/-- Poly lower at R24 s-center. TRUE ~= 3.9 (floor 3). -/
def BD_polyLower_R24 : Prop :=
  (3 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC24‖

def BD_piLower_R24 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC24‖

/-- Gamma lower at R24 s-center. TRUE ~= 0.254 (floor 0.2, 1.27x). -/
def BD_gammaLower_R24 : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC24‖

def BD_zetaLower_R24 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC24‖

def BD_derivTier_R24 : Prop :=
  ∀ w, BD_rect_R24.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R24 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R24.center (BD_rect_R24.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 3*0.5*0.2 = 0.3 >= 0.1382. -/
theorem BD_R24_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (3 : ℝ) * (1 / 2) * 0.2 * 1 := by norm_num

theorem BD_R24_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R24_deriv_of_ballSup (hBall : BD_ballSup_R24) :
    ∀ w, BD_rect_R24.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R24 0.25 16800 (by norm_num) (fun w hw => BD_R24_strip_of_mem hw) hBall

theorem BD_R24_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R24_sphere_of_ballSup (hBall : BD_ballSup_R24)
    (w : ℂ) (hw : BD_rect_R24.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R24 0.25 w hw hz)

theorem BD_R24_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC24‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC24‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC24‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC24‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R24.center = BD_sC24 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R24.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R24.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R24.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R24_radius_lt) (by norm_num)
  linarith

theorem BD_R24_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R24 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BD_R24_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R24 0.05 0.07 BD_R24_strip_lo BD_R24_strip_hi
    (BD_R24_fencing_of_premises hC hD)

noncomputable def BD_R24_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R24 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BD_R24_strip_lo BD_R24_strip_hi hD hC

theorem BD_R24_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24) {z : ℂ}
    (hx0 : BD_rect_R24.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R24.x1)
    (hy0 : BD_rect_R24.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R24.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R24 0.05 0.07 BD_R24_strip_lo BD_R24_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BD_R24_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-4, -1.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R24, 0.05, 0.07, rfl, rfl, rfl, rfl, BD_R24_strip_lo, BD_R24_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BD_R24_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R24.radius ≤ ‖xiShifted BD_rect_R24.center‖)
    (hD : BD_derivTier_R24) :
    CentralCoverAssembly.R24_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R25 = (-2,0.5,0.2,0.4), inner tier (0.15,0.06): CLOSED-CONDITIONAL -/

def BD_rect_R25 : CellProofEngine.Rect2D := CentralCoverAssembly.R25

theorem BD_R25_x0 : BD_rect_R25.x0 = -2 := rfl
theorem BD_R25_x1 : BD_rect_R25.x1 = 0.5 := rfl
theorem BD_R25_y0 : BD_rect_R25.y0 = 0.2 := rfl
theorem BD_R25_y1 : BD_rect_R25.y1 = 0.4 := rfl

theorem BD_R25_width_eq : BD_rect_R25.x1 - BD_rect_R25.x0 = 2.5 := by
  rw [BD_R25_x0, BD_R25_x1]; norm_num

theorem BD_R25_strip_lo : -(1 / 2 : ℝ) < BD_rect_R25.y0 :=
  CentralCoverAssembly.R25_strip_lo
theorem BD_R25_strip_hi : BD_rect_R25.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R25_strip_hi

theorem BD_R25_dx : BD_rect_R25.dx = 1.25 :=
  CentralCoverAssembly.R25_dx_eq
theorem BD_R25_dy : BD_rect_R25.dy = 0.1 :=
  CentralCoverAssembly.R25_dy_eq
theorem BD_R25_radius_eq :
    BD_rect_R25.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R25_radius_eq
theorem BD_R25_radius_lt : BD_rect_R25.radius < 1.26 := by
  rw [BD_R25_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R25_strip_of_mem {w : ℂ} (hw : BD_rect_R25.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R25_y0] at hy0
  rw [BD_R25_y1] at hy1
  constructor <;> linarith

theorem BD_R25_mem_gridFine : (-2, 0.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R25_mem_gridFine

noncomputable def BD_sC25 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R25.center

/-- Poly lower at R25 s-center. TRUE ~= 0.42 (floor 0.25, headroom 1.7x). -/
def BD_polyLower_R25 : Prop :=
  (0.25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC25‖

def BD_piLower_R25 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC25‖

/-- Gamma lower at R25 s-center. TRUE ~= 5.0 (floor 2, wide margin). -/
def BD_gammaLower_R25 : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC25‖

def BD_zetaLower_R25 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC25‖

def BD_derivTier_R25 : Prop :=
  ∀ w, BD_rect_R25.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BD_ballSup_R25 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R25.center (BD_rect_R25.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 0.25*0.5*2 = 0.25 >= 0.15+0.06*1.26 = 0.2256. -/
theorem BD_R25_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.25 : ℝ) * (1 / 2) * 2 * 1 := by norm_num

theorem BD_R25_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R25_deriv_of_ballSup (hBall : BD_ballSup_R25) :
    ∀ w, BD_rect_R25.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R25 0.25 16800 (by norm_num) (fun w hw => BD_R25_strip_of_mem hw) hBall

theorem BD_R25_cauchy_tier_mismatch :
    (0.06 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R25_sphere_of_ballSup (hBall : BD_ballSup_R25)
    (w : ℂ) (hw : BD_rect_R25.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R25 0.25 w hw hz)

theorem BD_R25_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC25‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC25‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC25‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC25‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R25.center = BD_sC25 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R25.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R25.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BD_rect_R25.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R25_radius_lt) (by norm_num)
  linarith

theorem BD_R25_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R25 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BD_R25_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R25 0.15 0.06 BD_R25_strip_lo BD_R25_strip_hi
    (BD_R25_fencing_of_premises hC hD)

noncomputable def BD_R25_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R25 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BD_R25_strip_lo BD_R25_strip_hi hD hC

theorem BD_R25_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25) {z : ℂ}
    (hx0 : BD_rect_R25.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R25.x1)
    (hy0 : BD_rect_R25.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R25.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R25 0.15 0.06 BD_R25_strip_lo BD_R25_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BD_R25_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R25, 0.15, 0.06, rfl, rfl, rfl, rfl, BD_R25_strip_lo, BD_R25_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BD_R25_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R25.radius ≤ ‖xiShifted BD_rect_R25.center‖)
    (hD : BD_derivTier_R25) :
    CentralCoverAssembly.R25_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R26 = (0,2.5,0.2,0.4), inner tier (0.15,0.06): CLOSED-CONDITIONAL -/

def BD_rect_R26 : CellProofEngine.Rect2D := CentralCoverAssembly.R26

theorem BD_R26_x0 : BD_rect_R26.x0 = 0 := rfl
theorem BD_R26_x1 : BD_rect_R26.x1 = 2.5 := rfl
theorem BD_R26_y0 : BD_rect_R26.y0 = 0.2 := rfl
theorem BD_R26_y1 : BD_rect_R26.y1 = 0.4 := rfl

theorem BD_R26_width_eq : BD_rect_R26.x1 - BD_rect_R26.x0 = 2.5 := by
  rw [BD_R26_x0, BD_R26_x1]; norm_num

theorem BD_R26_strip_lo : -(1 / 2 : ℝ) < BD_rect_R26.y0 :=
  CentralCoverAssembly.R26_strip_lo
theorem BD_R26_strip_hi : BD_rect_R26.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R26_strip_hi

theorem BD_R26_dx : BD_rect_R26.dx = 1.25 :=
  CentralCoverAssembly.R26_dx_eq
theorem BD_R26_dy : BD_rect_R26.dy = 0.1 :=
  CentralCoverAssembly.R26_dy_eq
theorem BD_R26_radius_eq :
    BD_rect_R26.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R26_radius_eq
theorem BD_R26_radius_lt : BD_rect_R26.radius < 1.26 := by
  rw [BD_R26_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R26_strip_of_mem {w : ℂ} (hw : BD_rect_R26.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R26_y0] at hy0
  rw [BD_R26_y1] at hy1
  constructor <;> linarith

theorem BD_R26_mem_gridFine : (0, 2.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R26_mem_gridFine

noncomputable def BD_sC26 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R26.center

/-- Poly lower at R26 s-center. TRUE ~= 0.93 (floor 0.5, 1.88x). -/
def BD_polyLower_R26 : Prop :=
  (0.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC26‖

def BD_piLower_R26 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC26‖

/-- Gamma lower at R26 s-center. TRUE ~= 1.5 (floor 1). -/
def BD_gammaLower_R26 : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC26‖

def BD_zetaLower_R26 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC26‖

def BD_derivTier_R26 : Prop :=
  ∀ w, BD_rect_R26.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BD_ballSup_R26 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R26.center (BD_rect_R26.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 0.5*0.5*1 = 0.25 >= 0.2256. -/
theorem BD_R26_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.5 : ℝ) * (1 / 2) * 1 * 1 := by norm_num

theorem BD_R26_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R26_deriv_of_ballSup (hBall : BD_ballSup_R26) :
    ∀ w, BD_rect_R26.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R26 0.25 16800 (by norm_num) (fun w hw => BD_R26_strip_of_mem hw) hBall

theorem BD_R26_cauchy_tier_mismatch :
    (0.06 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R26_sphere_of_ballSup (hBall : BD_ballSup_R26)
    (w : ℂ) (hw : BD_rect_R26.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R26 0.25 w hw hz)

theorem BD_R26_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC26‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC26‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC26‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC26‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R26.center = BD_sC26 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R26.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R26.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BD_rect_R26.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R26_radius_lt) (by norm_num)
  linarith

theorem BD_R26_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R26 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BD_R26_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R26 0.15 0.06 BD_R26_strip_lo BD_R26_strip_hi
    (BD_R26_fencing_of_premises hC hD)

noncomputable def BD_R26_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R26 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BD_R26_strip_lo BD_R26_strip_hi hD hC

theorem BD_R26_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26) {z : ℂ}
    (hx0 : BD_rect_R26.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R26.x1)
    (hy0 : BD_rect_R26.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R26.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R26 0.15 0.06 BD_R26_strip_lo BD_R26_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BD_R26_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R26, 0.15, 0.06, rfl, rfl, rfl, rfl, BD_R26_strip_lo, BD_R26_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BD_R26_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BD_rect_R26.radius ≤ ‖xiShifted BD_rect_R26.center‖)
    (hD : BD_derivTier_R26) :
    CentralCoverAssembly.R26_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R27 = (2,4.5,0.2,0.4), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BD_rect_R27 : CellProofEngine.Rect2D := CentralCoverAssembly.R27

theorem BD_R27_x0 : BD_rect_R27.x0 = 2 := rfl
theorem BD_R27_x1 : BD_rect_R27.x1 = 4.5 := rfl
theorem BD_R27_y0 : BD_rect_R27.y0 = 0.2 := rfl
theorem BD_R27_y1 : BD_rect_R27.y1 = 0.4 := rfl

theorem BD_R27_width_eq : BD_rect_R27.x1 - BD_rect_R27.x0 = 2.5 := by
  rw [BD_R27_x0, BD_R27_x1]; norm_num

theorem BD_R27_strip_lo : -(1 / 2 : ℝ) < BD_rect_R27.y0 :=
  CentralCoverAssembly.R27_strip_lo
theorem BD_R27_strip_hi : BD_rect_R27.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R27_strip_hi

theorem BD_R27_dx : BD_rect_R27.dx = 1.25 :=
  CentralCoverAssembly.R27_dx_eq
theorem BD_R27_dy : BD_rect_R27.dy = 0.1 :=
  CentralCoverAssembly.R27_dy_eq
theorem BD_R27_radius_eq :
    BD_rect_R27.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R27_radius_eq
theorem BD_R27_radius_lt : BD_rect_R27.radius < 1.26 := by
  rw [BD_R27_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R27_strip_of_mem {w : ℂ} (hw : BD_rect_R27.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R27_y0] at hy0
  rw [BD_R27_y1] at hy1
  constructor <;> linarith

theorem BD_R27_mem_gridFine : (2, 4.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R27_mem_gridFine

noncomputable def BD_sC27 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R27.center

/-- Poly lower at R27 s-center. TRUE ~= 5.4 (floor 4). -/
def BD_polyLower_R27 : Prop :=
  (4 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC27‖

def BD_piLower_R27 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC27‖

/-- Gamma lower at R27 s-center. TRUE ~= 0.161 (floor 0.12, 1.34x). -/
def BD_gammaLower_R27 : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC27‖

def BD_zetaLower_R27 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC27‖

def BD_derivTier_R27 : Prop :=
  ∀ w, BD_rect_R27.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R27 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R27.center (BD_rect_R27.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: 4*0.5*0.12 = 0.24 >= 0.1382. -/
theorem BD_R27_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (4 : ℝ) * (1 / 2) * 0.12 * 1 := by norm_num

theorem BD_R27_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R27_deriv_of_ballSup (hBall : BD_ballSup_R27) :
    ∀ w, BD_rect_R27.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R27 0.25 16800 (by norm_num) (fun w hw => BD_R27_strip_of_mem hw) hBall

theorem BD_R27_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R27_sphere_of_ballSup (hBall : BD_ballSup_R27)
    (w : ℂ) (hw : BD_rect_R27.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R27 0.25 w hw hz)

theorem BD_R27_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC27‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC27‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC27‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC27‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R27.center = BD_sC27 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R27.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R27.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R27.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R27_radius_lt) (by norm_num)
  linarith

theorem BD_R27_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R27 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BD_R27_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R27 0.05 0.07 BD_R27_strip_lo BD_R27_strip_hi
    (BD_R27_fencing_of_premises hC hD)

noncomputable def BD_R27_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R27 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BD_R27_strip_lo BD_R27_strip_hi hD hC

theorem BD_R27_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27) {z : ℂ}
    (hx0 : BD_rect_R27.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R27.x1)
    (hy0 : BD_rect_R27.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R27.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R27 0.05 0.07 BD_R27_strip_lo BD_R27_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BD_R27_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R27, 0.05, 0.07, rfl, rfl, rfl, rfl, BD_R27_strip_lo, BD_R27_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BD_R27_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R27.radius ≤ ‖xiShifted BD_rect_R27.center‖)
    (hD : BD_derivTier_R27) :
    CentralCoverAssembly.R27_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R28 = (4,6.5,0.2,0.4), mid tier (0.05,0.07): CLOSED-CONDITIONAL (TIGHT) -/

def BD_rect_R28 : CellProofEngine.Rect2D := CentralCoverAssembly.R28

theorem BD_R28_x0 : BD_rect_R28.x0 = 4 := rfl
theorem BD_R28_x1 : BD_rect_R28.x1 = 6.5 := rfl
theorem BD_R28_y0 : BD_rect_R28.y0 = 0.2 := rfl
theorem BD_R28_y1 : BD_rect_R28.y1 = 0.4 := rfl

theorem BD_R28_width_eq : BD_rect_R28.x1 - BD_rect_R28.x0 = 2.5 := by
  rw [BD_R28_x0, BD_R28_x1]; norm_num

theorem BD_R28_strip_lo : -(1 / 2 : ℝ) < BD_rect_R28.y0 :=
  CentralCoverAssembly.R28_strip_lo
theorem BD_R28_strip_hi : BD_rect_R28.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R28_strip_hi

theorem BD_R28_dx : BD_rect_R28.dx = 1.25 :=
  CentralCoverAssembly.R28_dx_eq
theorem BD_R28_dy : BD_rect_R28.dy = 0.1 :=
  CentralCoverAssembly.R28_dy_eq
theorem BD_R28_radius_eq :
    BD_rect_R28.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R28_radius_eq
theorem BD_R28_radius_lt : BD_rect_R28.radius < 1.26 := by
  rw [BD_R28_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R28_strip_of_mem {w : ℂ} (hw : BD_rect_R28.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R28_y0] at hy0
  rw [BD_R28_y1] at hy1
  constructor <;> linarith

theorem BD_R28_mem_gridFine : (4, 6.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R28_mem_gridFine

noncomputable def BD_sC28 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R28.center

/-- Poly lower at R28 s-center. TRUE ~= 13.9 (floor 11, headroom 1.26x). -/
def BD_polyLower_R28 : Prop :=
  (11 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC28‖

def BD_piLower_R28 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC28‖

/-- Gamma lower at R28 s-center. TRUE ~= 0.0274 (floor 0.026, TIGHT 1.05x). -/
def BD_gammaLower_R28 : Prop :=
  (0.026 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC28‖

def BD_zetaLower_R28 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC28‖

def BD_derivTier_R28 : Prop :=
  ∀ w, BD_rect_R28.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R28 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R28.center (BD_rect_R28.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds thinly: 11*0.5*0.026 = 0.143 >= 0.1382. -/
theorem BD_R28_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (11 : ℝ) * (1 / 2) * 0.026 * 1 := by norm_num

theorem BD_R28_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R28_deriv_of_ballSup (hBall : BD_ballSup_R28) :
    ∀ w, BD_rect_R28.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R28 0.25 16800 (by norm_num) (fun w hw => BD_R28_strip_of_mem hw) hBall

theorem BD_R28_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R28_sphere_of_ballSup (hBall : BD_ballSup_R28)
    (w : ℂ) (hw : BD_rect_R28.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R28 0.25 w hw hz)

theorem BD_R28_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC28‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC28‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC28‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC28‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R28.center = BD_sC28 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R28.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R28.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R28.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R28_radius_lt) (by norm_num)
  linarith

theorem BD_R28_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R28 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BD_R28_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R28 0.05 0.07 BD_R28_strip_lo BD_R28_strip_hi
    (BD_R28_fencing_of_premises hC hD)

noncomputable def BD_R28_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R28 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BD_R28_strip_lo BD_R28_strip_hi hD hC

theorem BD_R28_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28) {z : ℂ}
    (hx0 : BD_rect_R28.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R28.x1)
    (hy0 : BD_rect_R28.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R28.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R28 0.05 0.07 BD_R28_strip_lo BD_R28_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BD_R28_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R28, 0.05, 0.07, rfl, rfl, rfl, rfl, BD_R28_strip_lo, BD_R28_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BD_R28_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BD_rect_R28.radius ≤ ‖xiShifted BD_rect_R28.center‖)
    (hD : BD_derivTier_R28) :
    CentralCoverAssembly.R28_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R29 = (6,8.5,0.2,0.4), leaf tier (0.002,0.07): CLOSED-CONDITIONAL (TIGHT) -/

def BD_rect_R29 : CellProofEngine.Rect2D := CentralCoverAssembly.R29

theorem BD_R29_x0 : BD_rect_R29.x0 = 6 := rfl
theorem BD_R29_x1 : BD_rect_R29.x1 = 8.5 := rfl
theorem BD_R29_y0 : BD_rect_R29.y0 = 0.2 := rfl
theorem BD_R29_y1 : BD_rect_R29.y1 = 0.4 := rfl

theorem BD_R29_width_eq : BD_rect_R29.x1 - BD_rect_R29.x0 = 2.5 := by
  rw [BD_R29_x0, BD_R29_x1]; norm_num

theorem BD_R29_strip_lo : -(1 / 2 : ℝ) < BD_rect_R29.y0 :=
  CentralCoverAssembly.R29_strip_lo
theorem BD_R29_strip_hi : BD_rect_R29.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R29_strip_hi

theorem BD_R29_dx : BD_rect_R29.dx = 1.25 :=
  CentralCoverAssembly.R29_dx_eq
theorem BD_R29_dy : BD_rect_R29.dy = 0.1 :=
  CentralCoverAssembly.R29_dy_eq
theorem BD_R29_radius_eq :
    BD_rect_R29.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R29_radius_eq
theorem BD_R29_radius_lt : BD_rect_R29.radius < 1.26 := by
  rw [BD_R29_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R29_strip_of_mem {w : ℂ} (hw : BD_rect_R29.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R29_y0] at hy0
  rw [BD_R29_y1] at hy1
  constructor <;> linarith

theorem BD_R29_mem_gridFine : (6, 8.5, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R29_mem_gridFine

noncomputable def BD_sC29 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R29.center

/-- Poly lower at R29 s-center. TRUE ~= 26.4 (floor 24, headroom 1.1x, TIGHT). -/
def BD_polyLower_R29 : Prop :=
  (24 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC29‖

/-- Pi lower at R29 s-center. TRUE ~= 0.892 (floor 0.85, headroom 1.05x, TIGHT). -/
def BD_piLower_R29 : Prop :=
  (0.85 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC29‖

/-- Gamma lower at R29 s-center. TRUE ~= 0.00504 (floor 0.0045, 1.12x, TIGHT). -/
def BD_gammaLower_R29 : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC29‖

def BD_zetaLower_R29 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC29‖

def BD_derivTier_R29 : Prop :=
  ∀ w, BD_rect_R29.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BD_ballSup_R29 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R29.center (BD_rect_R29.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds thinly: 24*0.85*0.0045 = 0.0918 >= 0.0902. -/
theorem BD_R29_threshold_check :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ (24 : ℝ) * 0.85 * 0.0045 * 1 := by norm_num

theorem BD_R29_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R29_deriv_of_ballSup (hBall : BD_ballSup_R29) :
    ∀ w, BD_rect_R29.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R29 0.25 16800 (by norm_num) (fun w hw => BD_R29_strip_of_mem hw) hBall

theorem BD_R29_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R29_sphere_of_ballSup (hBall : BD_ballSup_R29)
    (w : ℂ) (hw : BD_rect_R29.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R29 0.25 w hw hz)

theorem BD_R29_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC29‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC29‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC29‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC29‖)
    (hThresh : (0.002 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R29.center = BD_sC29 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R29.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R29.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BD_rect_R29.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R29_radius_lt) (by norm_num)
  linarith

theorem BD_R29_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R29 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BD_R29_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R29 0.002 0.07 BD_R29_strip_lo BD_R29_strip_hi
    (BD_R29_fencing_of_premises hC hD)

noncomputable def BD_R29_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R29 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    BD_R29_strip_lo BD_R29_strip_hi hD hC

theorem BD_R29_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29) {z : ℂ}
    (hx0 : BD_rect_R29.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R29.x1)
    (hy0 : BD_rect_R29.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R29.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R29 0.002 0.07 BD_R29_strip_lo BD_R29_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BD_R29_H_instance
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R29, 0.002, 0.07, rfl, rfl, rfl, rfl, BD_R29_strip_lo, BD_R29_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BD_R29_implies_leaf
    (hC : (0.002 : ℝ) + 0.07 * BD_rect_R29.radius ≤ ‖xiShifted BD_rect_R29.center‖)
    (hD : BD_derivTier_R29) :
    CentralCoverAssembly.R29_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R30 = (7.5,10,0.2,0.4), outer tier (0.002,0.05): FEASIBILITY-NEGATIVE -/

def BD_rect_R30 : CellProofEngine.Rect2D := CentralCoverAssembly.R30

theorem BD_R30_x0 : BD_rect_R30.x0 = 7.5 := rfl
theorem BD_R30_x1 : BD_rect_R30.x1 = 10 := rfl
theorem BD_R30_y0 : BD_rect_R30.y0 = 0.2 := rfl
theorem BD_R30_y1 : BD_rect_R30.y1 = 0.4 := rfl

theorem BD_R30_width_eq : BD_rect_R30.x1 - BD_rect_R30.x0 = 2.5 := by
  rw [BD_R30_x0, BD_R30_x1]; norm_num

theorem BD_R30_strip_lo : -(1 / 2 : ℝ) < BD_rect_R30.y0 :=
  CentralCoverAssembly.R30_strip_lo
theorem BD_R30_strip_hi : BD_rect_R30.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R30_strip_hi

theorem BD_R30_dx : BD_rect_R30.dx = 1.25 :=
  CentralCoverAssembly.R30_dx_eq
theorem BD_R30_dy : BD_rect_R30.dy = 0.1 :=
  CentralCoverAssembly.R30_dy_eq
theorem BD_R30_radius_eq :
    BD_rect_R30.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R30_radius_eq
theorem BD_R30_radius_lt : BD_rect_R30.radius < 1.26 := by
  rw [BD_R30_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem BD_R30_strip_of_mem {w : ℂ} (hw : BD_rect_R30.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BD_R30_y0] at hy0
  rw [BD_R30_y1] at hy1
  constructor <;> linarith

theorem BD_R30_mem_gridFine : (7.5, 10, 0.2, 0.4) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R30_mem_gridFine

noncomputable def BD_sC30 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BD_rect_R30.center

/-- Poly lower at R30 s-center. TRUE ~= 38.4 (premise floor 30, conservative). -/
def BD_polyLower_R30 : Prop :=
  (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BD_sC30‖

/-- Pi lower at R30 s-center. TRUE ~= 0.892 (premise floor 1/2). -/
def BD_piLower_R30 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BD_sC30‖

/-- Gamma lower at R30 s-center. TRUE ~= 0.00143 (floor 0.001, headroom 1.43x). -/
def BD_gammaLower_R30 : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BD_sC30‖

/-- Zeta lower at R30 s-center. TRUE unmeasured O(1) (the wall). -/
def BD_zetaLower_R30 : Prop :=
  (1 : ℝ) ≤ ‖zeta BD_sC30‖

def BD_derivTier_R30 : Prop :=
  ∀ w, BD_rect_R30.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

def BD_ballSup_R30 : Prop :=
  ∀ z ∈ Metric.closedBall BD_rect_R30.center (BD_rect_R30.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Negative margin at TRUE-scale floors: 30*0.5*0.001*1 = 0.015 < 0.065. -/
theorem BD_R30_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by norm_num

theorem BD_R30_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BD_R30_deriv_of_ballSup (hBall : BD_ballSup_R30) :
    ∀ w, BD_rect_R30.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BD_rect_R30 0.25 16800 (by norm_num) (fun w hw => BD_R30_strip_of_mem hw) hBall

theorem BD_R30_cauchy_tier_mismatch :
    (0.05 : ℝ) < 16800 / 0.25 := by norm_num

theorem BD_R30_sphere_of_ballSup (hBall : BD_ballSup_R30)
    (w : ℂ) (hw : BD_rect_R30.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BD_rect_R30 0.25 w hw hz)

theorem BD_R30_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BD_sC30‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BD_sC30‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BD_sC30‖)
    (hzeta : Azeta ≤ ‖zeta BD_sC30‖)
    (hThresh : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BD_rect_R30.center = BD_sC30 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BD_rect_R30.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BD_rect_R30.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * BD_rect_R30.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BD_R30_radius_lt) (by norm_num)
  linarith

theorem BD_R30_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30) :
    CentralCoverAssembly.CellFencingHypotheses BD_rect_R30 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BD_R30_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BD_rect_R30 0.002 0.05 BD_R30_strip_lo BD_R30_strip_hi
    (BD_R30_fencing_of_premises hC hD)

noncomputable def BD_R30_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BD_rect_R30 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BD_R30_strip_lo BD_R30_strip_hi hD hC

theorem BD_R30_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30) {z : ℂ}
    (hx0 : BD_rect_R30.x0 ≤ z.re) (hx1 : z.re ≤ BD_rect_R30.x1)
    (hy0 : BD_rect_R30.y0 ≤ z.im) (hy1 : z.im ≤ BD_rect_R30.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BD_rect_R30 0.002 0.05 BD_R30_strip_lo BD_R30_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BD_R30_H_instance
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BD_rect_R30, 0.002, 0.05, rfl, rfl, rfl, rfl, BD_R30_strip_lo, BD_R30_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BD_R30_implies_leaf
    (hC : (0.002 : ℝ) + 0.05 * BD_rect_R30.radius ≤ ‖xiShifted BD_rect_R30.center‖)
    (hD : BD_derivTier_R30) :
    CentralCoverAssembly.R30_leaf_obligations :=
  ⟨hC, hD⟩

end Door3BatchD

/-! ## BATCH-D CLOSE-OUT (Step 12 honesty record)

* Claimed: R21-R30 (all `(0.2,0.4)`, all in `gridFine`); bottom/second/top rows
  untouched; no other file touched; no commits; no logs; no lakefile edits.
* Per cell: CLOSED-conditional on explicit `Prop` premises (4 factor floors +
  tier-M + ball-sup for R22-R29; R21/R30 carry the same 6 premise shapes but
  are flagged feasibility-NEGATIVE via proved arithmetic deficits
  `BD_R21_threshold_negative` / `BD_R30_threshold_negative`), every premise
  carrying its TRUE value/margin in its doc-comment. No unfinished proofs;
  explicit binders throughout; no `simpa`; all numerals at most 6 digits;
  `norm_num` only on `ℝ` goals (widths, thresholds/deficits, closed forms,
  mismatches, nonneg side conditions); membership/strip/geometry reuse banked
  `RXX` lemmas (all existence-verified read-only before writing).
* Imports: `Mathlib` + `central_cover_assembly` only; no cycle-risk extras.
* Patch remainder: 60 factor/deriv/ball premises (6/cell) + build verification
  + tight-premise discharge for R28/R29 + re-tiering or subdivision for
  R21/R30 (deficits -0.05 each at TRUE scale) + `BottomStripObligations` +
  edge strips + cutoffs + real axis + central registration. Report-and-stop.
-/
