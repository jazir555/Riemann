import central_cover_assembly

/-!
# Door 3 UPPER-ROW batch C (`door3_cells_batchC.lean`, NEW file, exclusive owner: batch-C agent)

WRITE-ONLY replication of the `door3_first_cell.lean` 12-step template for the
TOP row only (`y = (0.3, 0.49)`, Im up to the 0.49 band edge). No build performed
(no lake/lean commands); patch phase later. No other repo file touched.

## CLAIMED CELLS (this file owns ONLY these; siblings own the rest)

Bottom row `(0.01,0.2)` and second row `(0.1,0.3)` are OUT OF SCOPE (sibling
lanes). The `(0.2,0.4)` row (R21-R30) is LEFT TO SIBLINGS to avoid collision;
this file claims ONLY the ten `(0.3,0.49)` cells below.

| cell | x-interval | y-interval | center (z) | s-center (1/2+I*z) | radius | tier (eps,M) |
| R31 | (-10,-7.5) | (0.3,0.49) | -8.75+0.395I | 0.105-8.75I | sqrt(1.25^2+0.095^2)<1.26 | (0.002,0.05) outer |
| R32 | (-8,-5.5) | (0.3,0.49) | -6.75+0.395I | 0.105-6.75I | same <1.26 | (0.002,0.07) mid-outer |
| R33 | (-6,-3.5) | (0.3,0.49) | -4.75+0.395I | 0.105-4.75I | same <1.26 | (0.05,0.07) mid |
| R34 | (-4,-1.5) | (0.3,0.49) | -2.75+0.395I | 0.105-2.75I | same <1.26 | (0.05,0.07) mid |
| R35 | (-2,0.5) | (0.3,0.49) | -0.75+0.395I | 0.105-0.75I | same <1.26 | (0.15,0.06) inner |
| R36 | (0,2.5) | (0.3,0.49) | 1.25+0.395I | 0.105+1.25I | same <1.26 | (0.15,0.06) inner |
| R37 | (2,4.5) | (0.3,0.49) | 3.25+0.395I | 0.105+3.25I | same <1.26 | (0.05,0.07) mid |
| R38 | (4,6.5) | (0.3,0.49) | 5.25+0.395I | 0.105+5.25I | same <1.26 | (0.05,0.07) mid |
| R39 | (6,8.5) | (0.3,0.49) | 7.25+0.395I | 0.105+7.25I | same <1.26 | (0.002,0.07) mid-outer |
| R40 | (7.5,10) | (0.3,0.49) | 8.75+0.395I | 0.105+8.75I | same <1.26 | (0.002,0.05) outer |

Tiers match the banked `RXX_leaf_obligations` in `central_cover_assembly.lean`
(R31:4217 outer, R32:4301, R33:4385 mid, R34:4469 mid, R35:4553 inner,
R36:4637 inner, R37:4721 mid, R38:4805 mid, R39:4889, R40:4973 outer).
Cell inventory: `CellData` (:111), `innerGridY` (:372, rows
`[(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]`), `fineGridX` (:954, 10 columns
width 2.5), `gridFine` (:1002, 40 cells), `FullCentralObligations` (:5164 =
`BottomRowObligations` + `UpperRowsObligations`), `allCentral_H_of_obligations`
(:5264), H-leaf `inner_nonvanishing_of_fenced_grid_fine` (:1047).

## BANKED-NAME VERIFICATION RECORD (all read-only, all exist)

* `CentralCoverAssembly.R31..R40`, `RXX_x0/x1/y0/y1`, `RXX_strip_lo/hi`,
  `RXX_dx_eq/dy_eq/radius_eq/radius_lt` (per-cell sections ~:4177-:5020).
* `CentralCoverAssembly.sample_cell_radius_bound` (:421),
  `fine_eps_outer_pos/mid_pos/inner_pos` (:1032-1034),
  `CellFencingHypotheses` (:504),
  `lowerBoundRect_of_fencingHypotheses_strip`,
  `zeroFreeRect_of_rect_center_bound_strip`,
  `xi_rect_lower_bound_of_center_bound_strip` (:882ff),
  `xiShiftedEntire` (:823), `fineGridX`/`innerGridY`/`gridFine`.
* `DerivCauchyBridge.norm_xiShifted_eq_parts` (:6350),
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (:6233),
  `TailProofEngine.prod_four_ge_of_ge` (`rh_certificate_infra.lean:157`,
  transitive via `central_cover_assembly` import).
* `R02Pilot.*` (pilot namespace :9585) verified but R02-SPECIFIC: NOT reused
  for upper-row centers (different s-centers); poly/pi lowers are therefore
  explicit premises here, not banked cites. The small-R Cauchy pattern
  (`C = 56*1*10*10 = 5600`, `M = 5600/0.008 = 700000`) is mirrored from the
  banked `R31..R40_C_eq/M_eq` shape; no discharged Gamma/P1 bank exists for
  R31-R40 (their `RXX_gamma/zeta_upper_obligation`s are open obligations), so
  the ball-sup stays an explicit premise.
* Imports: Mathlib + `central_cover_assembly` only. `CellProofEngine.Rect2D`,
  `TailProofEngine`, root `zeta` resolve transitively through it (Rect2D in
  `rh_certificate_infra`, `zeta` in `riemann_hypothesis`); no extra imports.

## GAMMA IM-DECAY HONESTY (numbers)

s-centers here have `Re = 0.105` (vs 0.395 for the R02 pilot) and
`|Im| = |x_center|` up to 8.75. `gammaOf` is Gamma(s/2)-scale (R02 pilot:
TRUE ~= 0.0087 at t = -6.75). Stirling estimates for TRUE `|gammaOf|`:
t=8.75 ~= 0.00134; 6.75 ~= 0.00725; 4.75 ~= 0.0408; 2.75 ~= 0.25;
0.75 ~= 2.16; 1.25 ~= 1.16; 3.25 ~= 0.157; 5.25 ~= 0.0262; 7.25 ~= 0.00472.
Center-true ~= poly*0.5*gamma*1 with poly ~= |s|^2/2-scale:
R31 ~= 0.0255 vs budget 0.065; R32 ~= 0.083 vs 0.0902; R39 ~= 0.061 vs 0.0902;
R40 ~= 0.0255 vs 0.065. Hence R31/R32/R39/R40 are FEASIBILITY-NEGATIVE at
TRUE factor scales (proved negative-margin theorems below); R33-R38 are
CLOSED-CONDITIONAL (several with tight 1.08-1.36x headroom, flagged per cell).

## PER-CELL STATUS

* R31: feasibility-NEGATIVE (0.015 < 0.065 at TRUE-scale floors).
* R32: feasibility-NEGATIVE (0.054 < 0.0902 at TRUE-scale floors).
* R33: CLOSED-conditional (threshold 0.144 >= 0.1382; gamma headroom 1.27x).
* R34: CLOSED-conditional (threshold 0.3 >= 0.1382).
* R35: CLOSED-conditional TIGHT (threshold 0.25 >= 0.2256; gamma 1.08x).
* R36: CLOSED-conditional thin (threshold 0.25 >= 0.2256).
* R37: CLOSED-conditional (threshold 0.24 >= 0.1382).
* R38: CLOSED-conditional TIGHT (threshold 0.144 >= 0.1382; gamma 1.09x).
* R39: feasibility-NEGATIVE (0.04 < 0.0902 at TRUE-scale floors).
* R40: feasibility-NEGATIVE (0.015 < 0.065 at TRUE-scale floors).

## PATCH REMAINDER

Build verification (`lake env lean` on this file); poly/pi TRUE-floor
measurement at the ten s-centers (currently conservative premises);
gamma-lower enclosures (Stirling-disc treatment, the documented wall);
zeta-lower enclosures (complex-zeta wall); tight-premise discharge for
R35/R38; re-tiering or subdivision for R31/R32/R39/R40 (margin deficits
-0.05/-0.036/-0.05/-0.05 at TRUE scale); central registration (NOT here).
-/

noncomputable section

namespace Door3BatchC

/-! ## R31 = (-10,-7.5,0.3,0.49), outer tier (0.002,0.05): FEASIBILITY-NEGATIVE -/

def BC_rect_R31 : CellProofEngine.Rect2D := CentralCoverAssembly.R31

theorem BC_R31_x0 : BC_rect_R31.x0 = -10 := rfl
theorem BC_R31_x1 : BC_rect_R31.x1 = -7.5 := rfl
theorem BC_R31_y0 : BC_rect_R31.y0 = 0.3 := rfl
theorem BC_R31_y1 : BC_rect_R31.y1 = 0.49 := rfl

theorem BC_R31_width_eq : BC_rect_R31.x1 - BC_rect_R31.x0 = 2.5 := by
  rw [BC_R31_x0, BC_R31_x1]; norm_num

theorem BC_R31_strip_lo : -(1 / 2 : ℝ) < BC_rect_R31.y0 :=
  CentralCoverAssembly.R31_strip_lo
theorem BC_R31_strip_hi : BC_rect_R31.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R31_strip_hi

theorem BC_R31_dx : BC_rect_R31.dx = 1.25 :=
  CentralCoverAssembly.R31_dx_eq
theorem BC_R31_dy : BC_rect_R31.dy = 0.095 :=
  CentralCoverAssembly.R31_dy_eq
theorem BC_R31_radius_eq :
    BC_rect_R31.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R31_radius_eq
theorem BC_R31_radius_lt : BC_rect_R31.radius < 1.26 := by
  rw [BC_R31_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R31_strip_of_mem {w : ℂ} (hw : BC_rect_R31.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R31_y0] at hy0
  rw [BC_R31_y1] at hy1
  constructor <;> linarith

theorem BC_R31_mem_gridFine : (-10, -7.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-10, -7.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-10, -7.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- R31 s-center `s = 1/2 + I*center` (`R02Pilot.sCenter` pattern; `rfl`-bridge). -/
noncomputable def BC_sC31 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R31.center

/-- Poly lower at R31 s-center. TRUE ~= 38 (premise floor 30, conservative). -/
def BC_polyLower_R31 : Prop :=
  (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC31‖

/-- Pi lower at R31 s-center. TRUE O(1/2)-scale (premise floor 1/2). -/
def BC_piLower_R31 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC31‖

/-- Gamma lower at R31 s-center. TRUE ~= 0.00134 (floor 0.001, headroom 1.34x). -/
def BC_gammaLower_R31 : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC31‖

/-- Zeta lower at R31 s-center. TRUE unmeasured O(1) (the wall). -/
def BC_zetaLower_R31 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC31‖

/-- Tier deriv bound (matches `R31_leaf_obligations` shape). TRUE unknown. -/
def BC_derivTier_R31 : Prop :=
  ∀ w, BC_rect_R31.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

/-- Closed-ball sup for the small-R Cauchy route (C=5600, r=0.008 pattern). -/
def BC_ballSup_R31 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R31.center (BC_rect_R31.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Negative margin at TRUE-scale floors: 30*0.5*0.001*1 = 0.015 < 0.065. -/
theorem BC_R31_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by norm_num

theorem BC_R31_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R31_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R31_deriv_of_ballSup (hBall : BC_ballSup_R31) :
    ∀ w, BC_rect_R31.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R31 0.008 5600 (by norm_num) (fun w hw => BC_R31_strip_of_mem hw) hBall

/-- Honest gap: small-R Cauchy M = 700000 misses the (0.002,0.05) tier. -/
theorem BC_R31_cauchy_tier_mismatch :
    (0.066 : ℝ) < (0.002 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R31_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC31‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC31‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC31‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC31‖)
    (hThresh : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R31.center = BC_sC31 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R31.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R31.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * BC_rect_R31.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R31_radius_lt) (by norm_num)
  linarith

theorem BC_R31_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R31 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BC_R31_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R31 0.002 0.05 BC_R31_strip_lo BC_R31_strip_hi
    (BC_R31_fencing_of_premises hC hD)

noncomputable def BC_R31_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R31 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BC_R31_strip_lo BC_R31_strip_hi hD hC

theorem BC_R31_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31) {z : ℂ}
    (hx0 : BC_rect_R31.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R31.x1)
    (hy0 : BC_rect_R31.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R31.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R31 0.002 0.05 BC_R31_strip_lo BC_R31_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BC_R31_H_instance
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-10, -7.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R31, 0.002, 0.05, rfl, rfl, rfl, rfl, BC_R31_strip_lo, BC_R31_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BC_R31_implies_leaf
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R31.radius ≤ ‖xiShifted BC_rect_R31.center‖)
    (hD : BC_derivTier_R31) :
    CentralCoverAssembly.R31_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R32 = (-8,-5.5,0.3,0.49), tier (0.002,0.07): FEASIBILITY-NEGATIVE -/

def BC_rect_R32 : CellProofEngine.Rect2D := CentralCoverAssembly.R32

theorem BC_R32_x0 : BC_rect_R32.x0 = -8 := rfl
theorem BC_R32_x1 : BC_rect_R32.x1 = -5.5 := rfl
theorem BC_R32_y0 : BC_rect_R32.y0 = 0.3 := rfl
theorem BC_R32_y1 : BC_rect_R32.y1 = 0.49 := rfl

theorem BC_R32_width_eq : BC_rect_R32.x1 - BC_rect_R32.x0 = 2.5 := by
  rw [BC_R32_x0, BC_R32_x1]; norm_num

theorem BC_R32_strip_lo : -(1 / 2 : ℝ) < BC_rect_R32.y0 :=
  CentralCoverAssembly.R32_strip_lo
theorem BC_R32_strip_hi : BC_rect_R32.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R32_strip_hi

theorem BC_R32_dx : BC_rect_R32.dx = 1.25 :=
  CentralCoverAssembly.R32_dx_eq
theorem BC_R32_dy : BC_rect_R32.dy = 0.095 :=
  CentralCoverAssembly.R32_dy_eq
theorem BC_R32_radius_eq :
    BC_rect_R32.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R32_radius_eq
theorem BC_R32_radius_lt : BC_rect_R32.radius < 1.26 := by
  rw [BC_R32_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R32_strip_of_mem {w : ℂ} (hw : BC_rect_R32.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R32_y0] at hy0
  rw [BC_R32_y1] at hy1
  constructor <;> linarith

theorem BC_R32_mem_gridFine : (-8, -5.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-8, -5.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC32 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R32.center

/-- Poly lower at R32 s-center. TRUE ~= 23 (floor 18, conservative). -/
def BC_polyLower_R32 : Prop :=
  (18 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC32‖

/-- Pi lower at R32 s-center. TRUE O(1/2)-scale. -/
def BC_piLower_R32 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC32‖

/-- Gamma lower at R32 s-center. TRUE ~= 0.00725 (floor 0.006, 1.2x). -/
def BC_gammaLower_R32 : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC32‖

/-- Zeta lower at R32 s-center. TRUE unmeasured O(1) (the wall). -/
def BC_zetaLower_R32 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC32‖

def BC_derivTier_R32 : Prop :=
  ∀ w, BC_rect_R32.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R32 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R32.center (BC_rect_R32.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Negative margin at TRUE-scale floors: 18*0.5*0.006 = 0.054 < 0.0902. -/
theorem BC_R32_threshold_negative :
    (18 : ℝ) * (1 / 2) * 0.006 * 1 < (0.002 : ℝ) + 0.07 * 1.26 := by norm_num

theorem BC_R32_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R32_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R32_deriv_of_ballSup (hBall : BC_ballSup_R32) :
    ∀ w, BC_rect_R32.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R32 0.008 5600 (by norm_num) (fun w hw => BC_R32_strip_of_mem hw) hBall

theorem BC_R32_cauchy_tier_mismatch :
    (0.091 : ℝ) < (0.002 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R32_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC32‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC32‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC32‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC32‖)
    (hThresh : (0.002 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R32.center = BC_sC32 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R32.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R32.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R32.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R32_radius_lt) (by norm_num)
  linarith

theorem BC_R32_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R32 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BC_R32_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R32 0.002 0.07 BC_R32_strip_lo BC_R32_strip_hi
    (BC_R32_fencing_of_premises hC hD)

noncomputable def BC_R32_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R32 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    BC_R32_strip_lo BC_R32_strip_hi hD hC

theorem BC_R32_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32) {z : ℂ}
    (hx0 : BC_rect_R32.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R32.x1)
    (hy0 : BC_rect_R32.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R32.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R32 0.002 0.07 BC_R32_strip_lo BC_R32_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BC_R32_H_instance
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R32, 0.002, 0.07, rfl, rfl, rfl, rfl, BC_R32_strip_lo, BC_R32_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BC_R32_implies_leaf
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R32.radius ≤ ‖xiShifted BC_rect_R32.center‖)
    (hD : BC_derivTier_R32) :
    CentralCoverAssembly.R32_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R33 = (-6,-3.5,0.3,0.49), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BC_rect_R33 : CellProofEngine.Rect2D := CentralCoverAssembly.R33

theorem BC_R33_x0 : BC_rect_R33.x0 = -6 := rfl
theorem BC_R33_x1 : BC_rect_R33.x1 = -3.5 := rfl
theorem BC_R33_y0 : BC_rect_R33.y0 = 0.3 := rfl
theorem BC_R33_y1 : BC_rect_R33.y1 = 0.49 := rfl

theorem BC_R33_width_eq : BC_rect_R33.x1 - BC_rect_R33.x0 = 2.5 := by
  rw [BC_R33_x0, BC_R33_x1]; norm_num

theorem BC_R33_strip_lo : -(1 / 2 : ℝ) < BC_rect_R33.y0 :=
  CentralCoverAssembly.R33_strip_lo
theorem BC_R33_strip_hi : BC_rect_R33.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R33_strip_hi

theorem BC_R33_dx : BC_rect_R33.dx = 1.25 :=
  CentralCoverAssembly.R33_dx_eq
theorem BC_R33_dy : BC_rect_R33.dy = 0.095 :=
  CentralCoverAssembly.R33_dy_eq
theorem BC_R33_radius_eq :
    BC_rect_R33.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R33_radius_eq
theorem BC_R33_radius_lt : BC_rect_R33.radius < 1.26 := by
  rw [BC_R33_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R33_strip_of_mem {w : ℂ} (hw : BC_rect_R33.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R33_y0] at hy0
  rw [BC_R33_y1] at hy1
  constructor <;> linarith

theorem BC_R33_mem_gridFine : (-6, -3.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-6, -3.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-6, -3.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC33 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R33.center

/-- Poly lower at R33 s-center. TRUE ~= 11 (floor 9, conservative). -/
def BC_polyLower_R33 : Prop :=
  (9 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC33‖

def BC_piLower_R33 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC33‖

/-- Gamma lower at R33 s-center. TRUE ~= 0.0408 (floor 0.032, 1.27x). -/
def BC_gammaLower_R33 : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC33‖

def BC_zetaLower_R33 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC33‖

def BC_derivTier_R33 : Prop :=
  ∀ w, BC_rect_R33.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R33 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R33.center (BC_rect_R33.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds: 9*0.5*0.032 = 0.144 >= 0.05+0.07*1.26 = 0.1382. -/
theorem BC_R33_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (9 : ℝ) * (1 / 2) * 0.032 * 1 := by norm_num

theorem BC_R33_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R33_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R33_deriv_of_ballSup (hBall : BC_ballSup_R33) :
    ∀ w, BC_rect_R33.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R33 0.008 5600 (by norm_num) (fun w hw => BC_R33_strip_of_mem hw) hBall

theorem BC_R33_cauchy_tier_mismatch :
    (0.139 : ℝ) < (0.05 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R33_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC33‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC33‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC33‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC33‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R33.center = BC_sC33 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R33.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R33.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R33.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R33_radius_lt) (by norm_num)
  linarith

theorem BC_R33_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R33 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BC_R33_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R33 0.05 0.07 BC_R33_strip_lo BC_R33_strip_hi
    (BC_R33_fencing_of_premises hC hD)

noncomputable def BC_R33_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R33 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BC_R33_strip_lo BC_R33_strip_hi hD hC

theorem BC_R33_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33) {z : ℂ}
    (hx0 : BC_rect_R33.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R33.x1)
    (hy0 : BC_rect_R33.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R33.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R33 0.05 0.07 BC_R33_strip_lo BC_R33_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BC_R33_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-6, -3.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R33, 0.05, 0.07, rfl, rfl, rfl, rfl, BC_R33_strip_lo, BC_R33_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BC_R33_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R33.radius ≤ ‖xiShifted BC_rect_R33.center‖)
    (hD : BC_derivTier_R33) :
    CentralCoverAssembly.R33_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R34 = (-4,-1.5,0.3,0.49), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BC_rect_R34 : CellProofEngine.Rect2D := CentralCoverAssembly.R34

theorem BC_R34_x0 : BC_rect_R34.x0 = -4 := rfl
theorem BC_R34_x1 : BC_rect_R34.x1 = -1.5 := rfl
theorem BC_R34_y0 : BC_rect_R34.y0 = 0.3 := rfl
theorem BC_R34_y1 : BC_rect_R34.y1 = 0.49 := rfl

theorem BC_R34_width_eq : BC_rect_R34.x1 - BC_rect_R34.x0 = 2.5 := by
  rw [BC_R34_x0, BC_R34_x1]; norm_num

theorem BC_R34_strip_lo : -(1 / 2 : ℝ) < BC_rect_R34.y0 :=
  CentralCoverAssembly.R34_strip_lo
theorem BC_R34_strip_hi : BC_rect_R34.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R34_strip_hi

theorem BC_R34_dx : BC_rect_R34.dx = 1.25 :=
  CentralCoverAssembly.R34_dx_eq
theorem BC_R34_dy : BC_rect_R34.dy = 0.095 :=
  CentralCoverAssembly.R34_dy_eq
theorem BC_R34_radius_eq :
    BC_rect_R34.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R34_radius_eq
theorem BC_R34_radius_lt : BC_rect_R34.radius < 1.26 := by
  rw [BC_R34_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R34_strip_of_mem {w : ℂ} (hw : BC_rect_R34.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R34_y0] at hy0
  rw [BC_R34_y1] at hy1
  constructor <;> linarith

theorem BC_R34_mem_gridFine : (-4, -1.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-4, -1.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-4, -1.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC34 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R34.center

/-- Poly lower at R34 s-center. TRUE ~= 3.8 (floor 3). -/
def BC_polyLower_R34 : Prop :=
  (3 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC34‖

def BC_piLower_R34 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC34‖

/-- Gamma lower at R34 s-center. TRUE ~= 0.25 (floor 0.2, 1.25x). -/
def BC_gammaLower_R34 : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC34‖

def BC_zetaLower_R34 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC34‖

def BC_derivTier_R34 : Prop :=
  ∀ w, BC_rect_R34.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R34 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R34.center (BC_rect_R34.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds: 3*0.5*0.2 = 0.3 >= 0.1382. -/
theorem BC_R34_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (3 : ℝ) * (1 / 2) * 0.2 * 1 := by norm_num

theorem BC_R34_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R34_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R34_deriv_of_ballSup (hBall : BC_ballSup_R34) :
    ∀ w, BC_rect_R34.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R34 0.008 5600 (by norm_num) (fun w hw => BC_R34_strip_of_mem hw) hBall

theorem BC_R34_cauchy_tier_mismatch :
    (0.139 : ℝ) < (0.05 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R34_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC34‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC34‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC34‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC34‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R34.center = BC_sC34 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R34.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R34.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R34.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R34_radius_lt) (by norm_num)
  linarith

theorem BC_R34_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R34 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BC_R34_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R34 0.05 0.07 BC_R34_strip_lo BC_R34_strip_hi
    (BC_R34_fencing_of_premises hC hD)

noncomputable def BC_R34_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R34 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BC_R34_strip_lo BC_R34_strip_hi hD hC

theorem BC_R34_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34) {z : ℂ}
    (hx0 : BC_rect_R34.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R34.x1)
    (hy0 : BC_rect_R34.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R34.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R34 0.05 0.07 BC_R34_strip_lo BC_R34_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BC_R34_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-4, -1.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R34, 0.05, 0.07, rfl, rfl, rfl, rfl, BC_R34_strip_lo, BC_R34_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BC_R34_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R34.radius ≤ ‖xiShifted BC_rect_R34.center‖)
    (hD : BC_derivTier_R34) :
    CentralCoverAssembly.R34_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R35 = (-2,0.5,0.3,0.49), inner tier (0.15,0.06): CLOSED-CONDITIONAL (TIGHT) -/

def BC_rect_R35 : CellProofEngine.Rect2D := CentralCoverAssembly.R35

theorem BC_R35_x0 : BC_rect_R35.x0 = -2 := rfl
theorem BC_R35_x1 : BC_rect_R35.x1 = 0.5 := rfl
theorem BC_R35_y0 : BC_rect_R35.y0 = 0.3 := rfl
theorem BC_R35_y1 : BC_rect_R35.y1 = 0.49 := rfl

theorem BC_R35_width_eq : BC_rect_R35.x1 - BC_rect_R35.x0 = 2.5 := by
  rw [BC_R35_x0, BC_R35_x1]; norm_num

theorem BC_R35_strip_lo : -(1 / 2 : ℝ) < BC_rect_R35.y0 :=
  CentralCoverAssembly.R35_strip_lo
theorem BC_R35_strip_hi : BC_rect_R35.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R35_strip_hi

theorem BC_R35_dx : BC_rect_R35.dx = 1.25 :=
  CentralCoverAssembly.R35_dx_eq
theorem BC_R35_dy : BC_rect_R35.dy = 0.095 :=
  CentralCoverAssembly.R35_dy_eq
theorem BC_R35_radius_eq :
    BC_rect_R35.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R35_radius_eq
theorem BC_R35_radius_lt : BC_rect_R35.radius < 1.26 := by
  rw [BC_R35_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R35_strip_of_mem {w : ℂ} (hw : BC_rect_R35.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R35_y0] at hy0
  rw [BC_R35_y1] at hy1
  constructor <;> linarith

theorem BC_R35_mem_gridFine : (-2, 0.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-2, 0.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-2, 0.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC35 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R35.center

/-- Poly lower at R35 s-center. TRUE ~= 0.3 (floor 0.25, headroom 1.2x, TIGHT:
small |s| makes the quadratic factor the binding constraint here). -/
def BC_polyLower_R35 : Prop :=
  (0.25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC35‖

def BC_piLower_R35 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC35‖

/-- Gamma lower at R35 s-center. TRUE ~= 2.16 (floor 2, headroom 1.08x, TIGHT). -/
def BC_gammaLower_R35 : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC35‖

def BC_zetaLower_R35 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC35‖

def BC_derivTier_R35 : Prop :=
  ∀ w, BC_rect_R35.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BC_ballSup_R35 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R35.center (BC_rect_R35.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds thinly: 0.25*0.5*2 = 0.25 >= 0.15+0.06*1.26 = 0.2256. -/
theorem BC_R35_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.25 : ℝ) * (1 / 2) * 2 * 1 := by norm_num

theorem BC_R35_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R35_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R35_deriv_of_ballSup (hBall : BC_ballSup_R35) :
    ∀ w, BC_rect_R35.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R35 0.008 5600 (by norm_num) (fun w hw => BC_R35_strip_of_mem hw) hBall

theorem BC_R35_cauchy_tier_mismatch :
    (0.226 : ℝ) < (0.15 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R35_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC35‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC35‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC35‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC35‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R35.center = BC_sC35 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R35.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R35.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BC_rect_R35.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R35_radius_lt) (by norm_num)
  linarith

theorem BC_R35_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R35 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BC_R35_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R35 0.15 0.06 BC_R35_strip_lo BC_R35_strip_hi
    (BC_R35_fencing_of_premises hC hD)

noncomputable def BC_R35_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R35 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BC_R35_strip_lo BC_R35_strip_hi hD hC

theorem BC_R35_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35) {z : ℂ}
    (hx0 : BC_rect_R35.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R35.x1)
    (hy0 : BC_rect_R35.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R35.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R35 0.15 0.06 BC_R35_strip_lo BC_R35_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BC_R35_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R35, 0.15, 0.06, rfl, rfl, rfl, rfl, BC_R35_strip_lo, BC_R35_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BC_R35_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R35.radius ≤ ‖xiShifted BC_rect_R35.center‖)
    (hD : BC_derivTier_R35) :
    CentralCoverAssembly.R35_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R36 = (0,2.5,0.3,0.49), inner tier (0.15,0.06): CLOSED-CONDITIONAL (thin) -/

def BC_rect_R36 : CellProofEngine.Rect2D := CentralCoverAssembly.R36

theorem BC_R36_x0 : BC_rect_R36.x0 = 0 := rfl
theorem BC_R36_x1 : BC_rect_R36.x1 = 2.5 := rfl
theorem BC_R36_y0 : BC_rect_R36.y0 = 0.3 := rfl
theorem BC_R36_y1 : BC_rect_R36.y1 = 0.49 := rfl

theorem BC_R36_width_eq : BC_rect_R36.x1 - BC_rect_R36.x0 = 2.5 := by
  rw [BC_R36_x0, BC_R36_x1]; norm_num

theorem BC_R36_strip_lo : -(1 / 2 : ℝ) < BC_rect_R36.y0 :=
  CentralCoverAssembly.R36_strip_lo
theorem BC_R36_strip_hi : BC_rect_R36.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R36_strip_hi

theorem BC_R36_dx : BC_rect_R36.dx = 1.25 :=
  CentralCoverAssembly.R36_dx_eq
theorem BC_R36_dy : BC_rect_R36.dy = 0.095 :=
  CentralCoverAssembly.R36_dy_eq
theorem BC_R36_radius_eq :
    BC_rect_R36.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R36_radius_eq
theorem BC_R36_radius_lt : BC_rect_R36.radius < 1.26 := by
  rw [BC_R36_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R36_strip_of_mem {w : ℂ} (hw : BC_rect_R36.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R36_y0] at hy0
  rw [BC_R36_y1] at hy1
  constructor <;> linarith

theorem BC_R36_mem_gridFine : (0, 2.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((0, 2.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(0, 2.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC36 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R36.center

/-- Poly lower at R36 s-center. TRUE ~= 0.8 (floor 0.5, 1.6x). -/
def BC_polyLower_R36 : Prop :=
  (0.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC36‖

def BC_piLower_R36 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC36‖

/-- Gamma lower at R36 s-center. TRUE ~= 1.16 (floor 1). -/
def BC_gammaLower_R36 : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC36‖

def BC_zetaLower_R36 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC36‖

def BC_derivTier_R36 : Prop :=
  ∀ w, BC_rect_R36.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BC_ballSup_R36 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R36.center (BC_rect_R36.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds thinly: 0.5*0.5*1 = 0.25 >= 0.2256. -/
theorem BC_R36_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.5 : ℝ) * (1 / 2) * 1 * 1 := by norm_num

theorem BC_R36_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R36_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R36_deriv_of_ballSup (hBall : BC_ballSup_R36) :
    ∀ w, BC_rect_R36.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R36 0.008 5600 (by norm_num) (fun w hw => BC_R36_strip_of_mem hw) hBall

theorem BC_R36_cauchy_tier_mismatch :
    (0.226 : ℝ) < (0.15 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R36_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC36‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC36‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC36‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC36‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R36.center = BC_sC36 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R36.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R36.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BC_rect_R36.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R36_radius_lt) (by norm_num)
  linarith

theorem BC_R36_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R36 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BC_R36_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R36 0.15 0.06 BC_R36_strip_lo BC_R36_strip_hi
    (BC_R36_fencing_of_premises hC hD)

noncomputable def BC_R36_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R36 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BC_R36_strip_lo BC_R36_strip_hi hD hC

theorem BC_R36_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36) {z : ℂ}
    (hx0 : BC_rect_R36.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R36.x1)
    (hy0 : BC_rect_R36.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R36.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R36 0.15 0.06 BC_R36_strip_lo BC_R36_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BC_R36_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R36, 0.15, 0.06, rfl, rfl, rfl, rfl, BC_R36_strip_lo, BC_R36_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BC_R36_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BC_rect_R36.radius ≤ ‖xiShifted BC_rect_R36.center‖)
    (hD : BC_derivTier_R36) :
    CentralCoverAssembly.R36_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R37 = (2,4.5,0.3,0.49), mid tier (0.05,0.07): CLOSED-CONDITIONAL -/

def BC_rect_R37 : CellProofEngine.Rect2D := CentralCoverAssembly.R37

theorem BC_R37_x0 : BC_rect_R37.x0 = 2 := rfl
theorem BC_R37_x1 : BC_rect_R37.x1 = 4.5 := rfl
theorem BC_R37_y0 : BC_rect_R37.y0 = 0.3 := rfl
theorem BC_R37_y1 : BC_rect_R37.y1 = 0.49 := rfl

theorem BC_R37_width_eq : BC_rect_R37.x1 - BC_rect_R37.x0 = 2.5 := by
  rw [BC_R37_x0, BC_R37_x1]; norm_num

theorem BC_R37_strip_lo : -(1 / 2 : ℝ) < BC_rect_R37.y0 :=
  CentralCoverAssembly.R37_strip_lo
theorem BC_R37_strip_hi : BC_rect_R37.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R37_strip_hi

theorem BC_R37_dx : BC_rect_R37.dx = 1.25 :=
  CentralCoverAssembly.R37_dx_eq
theorem BC_R37_dy : BC_rect_R37.dy = 0.095 :=
  CentralCoverAssembly.R37_dy_eq
theorem BC_R37_radius_eq :
    BC_rect_R37.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R37_radius_eq
theorem BC_R37_radius_lt : BC_rect_R37.radius < 1.26 := by
  rw [BC_R37_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R37_strip_of_mem {w : ℂ} (hw : BC_rect_R37.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R37_y0] at hy0
  rw [BC_R37_y1] at hy1
  constructor <;> linarith

theorem BC_R37_mem_gridFine : (2, 4.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((2, 4.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(2, 4.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC37 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R37.center

/-- Poly lower at R37 s-center. TRUE ~= 5.3 (floor 4). -/
def BC_polyLower_R37 : Prop :=
  (4 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC37‖

def BC_piLower_R37 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC37‖

/-- Gamma lower at R37 s-center. TRUE ~= 0.157 (floor 0.12, 1.3x). -/
def BC_gammaLower_R37 : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC37‖

def BC_zetaLower_R37 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC37‖

def BC_derivTier_R37 : Prop :=
  ∀ w, BC_rect_R37.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R37 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R37.center (BC_rect_R37.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds: 4*0.5*0.12 = 0.24 >= 0.1382. -/
theorem BC_R37_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (4 : ℝ) * (1 / 2) * 0.12 * 1 := by norm_num

theorem BC_R37_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R37_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R37_deriv_of_ballSup (hBall : BC_ballSup_R37) :
    ∀ w, BC_rect_R37.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R37 0.008 5600 (by norm_num) (fun w hw => BC_R37_strip_of_mem hw) hBall

theorem BC_R37_cauchy_tier_mismatch :
    (0.139 : ℝ) < (0.05 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R37_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC37‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC37‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC37‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC37‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R37.center = BC_sC37 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R37.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R37.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R37.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R37_radius_lt) (by norm_num)
  linarith

theorem BC_R37_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R37 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BC_R37_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R37 0.05 0.07 BC_R37_strip_lo BC_R37_strip_hi
    (BC_R37_fencing_of_premises hC hD)

noncomputable def BC_R37_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R37 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BC_R37_strip_lo BC_R37_strip_hi hD hC

theorem BC_R37_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37) {z : ℂ}
    (hx0 : BC_rect_R37.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R37.x1)
    (hy0 : BC_rect_R37.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R37.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R37 0.05 0.07 BC_R37_strip_lo BC_R37_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BC_R37_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R37, 0.05, 0.07, rfl, rfl, rfl, rfl, BC_R37_strip_lo, BC_R37_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BC_R37_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R37.radius ≤ ‖xiShifted BC_rect_R37.center‖)
    (hD : BC_derivTier_R37) :
    CentralCoverAssembly.R37_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R38 = (4,6.5,0.3,0.49), mid tier (0.05,0.07): CLOSED-CONDITIONAL (TIGHT) -/

def BC_rect_R38 : CellProofEngine.Rect2D := CentralCoverAssembly.R38

theorem BC_R38_x0 : BC_rect_R38.x0 = 4 := rfl
theorem BC_R38_x1 : BC_rect_R38.x1 = 6.5 := rfl
theorem BC_R38_y0 : BC_rect_R38.y0 = 0.3 := rfl
theorem BC_R38_y1 : BC_rect_R38.y1 = 0.49 := rfl

theorem BC_R38_width_eq : BC_rect_R38.x1 - BC_rect_R38.x0 = 2.5 := by
  rw [BC_R38_x0, BC_R38_x1]; norm_num

theorem BC_R38_strip_lo : -(1 / 2 : ℝ) < BC_rect_R38.y0 :=
  CentralCoverAssembly.R38_strip_lo
theorem BC_R38_strip_hi : BC_rect_R38.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R38_strip_hi

theorem BC_R38_dx : BC_rect_R38.dx = 1.25 :=
  CentralCoverAssembly.R38_dx_eq
theorem BC_R38_dy : BC_rect_R38.dy = 0.095 :=
  CentralCoverAssembly.R38_dy_eq
theorem BC_R38_radius_eq :
    BC_rect_R38.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R38_radius_eq
theorem BC_R38_radius_lt : BC_rect_R38.radius < 1.26 := by
  rw [BC_R38_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R38_strip_of_mem {w : ℂ} (hw : BC_rect_R38.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R38_y0] at hy0
  rw [BC_R38_y1] at hy1
  constructor <;> linarith

theorem BC_R38_mem_gridFine : (4, 6.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((4, 6.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(4, 6.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC38 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R38.center

/-- Poly lower at R38 s-center. TRUE ~= 14 (floor 12, 1.17x). -/
def BC_polyLower_R38 : Prop :=
  (12 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC38‖

def BC_piLower_R38 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC38‖

/-- Gamma lower at R38 s-center. TRUE ~= 0.0262 (floor 0.024, 1.09x, TIGHT). -/
def BC_gammaLower_R38 : Prop :=
  (0.024 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC38‖

def BC_zetaLower_R38 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC38‖

def BC_derivTier_R38 : Prop :=
  ∀ w, BC_rect_R38.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R38 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R38.center (BC_rect_R38.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Threshold holds tightly: 12*0.5*0.024 = 0.144 >= 0.1382. -/
theorem BC_R38_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (12 : ℝ) * (1 / 2) * 0.024 * 1 := by norm_num

theorem BC_R38_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R38_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R38_deriv_of_ballSup (hBall : BC_ballSup_R38) :
    ∀ w, BC_rect_R38.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R38 0.008 5600 (by norm_num) (fun w hw => BC_R38_strip_of_mem hw) hBall

theorem BC_R38_cauchy_tier_mismatch :
    (0.139 : ℝ) < (0.05 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R38_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC38‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC38‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC38‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC38‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R38.center = BC_sC38 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R38.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R38.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R38.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R38_radius_lt) (by norm_num)
  linarith

theorem BC_R38_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R38 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BC_R38_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R38 0.05 0.07 BC_R38_strip_lo BC_R38_strip_hi
    (BC_R38_fencing_of_premises hC hD)

noncomputable def BC_R38_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R38 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BC_R38_strip_lo BC_R38_strip_hi hD hC

theorem BC_R38_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38) {z : ℂ}
    (hx0 : BC_rect_R38.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R38.x1)
    (hy0 : BC_rect_R38.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R38.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R38 0.05 0.07 BC_R38_strip_lo BC_R38_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BC_R38_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R38, 0.05, 0.07, rfl, rfl, rfl, rfl, BC_R38_strip_lo, BC_R38_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BC_R38_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BC_rect_R38.radius ≤ ‖xiShifted BC_rect_R38.center‖)
    (hD : BC_derivTier_R38) :
    CentralCoverAssembly.R38_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R39 = (6,8.5,0.3,0.49), tier (0.002,0.07): FEASIBILITY-NEGATIVE -/

def BC_rect_R39 : CellProofEngine.Rect2D := CentralCoverAssembly.R39

theorem BC_R39_x0 : BC_rect_R39.x0 = 6 := rfl
theorem BC_R39_x1 : BC_rect_R39.x1 = 8.5 := rfl
theorem BC_R39_y0 : BC_rect_R39.y0 = 0.3 := rfl
theorem BC_R39_y1 : BC_rect_R39.y1 = 0.49 := rfl

theorem BC_R39_width_eq : BC_rect_R39.x1 - BC_rect_R39.x0 = 2.5 := by
  rw [BC_R39_x0, BC_R39_x1]; norm_num

theorem BC_R39_strip_lo : -(1 / 2 : ℝ) < BC_rect_R39.y0 :=
  CentralCoverAssembly.R39_strip_lo
theorem BC_R39_strip_hi : BC_rect_R39.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R39_strip_hi

theorem BC_R39_dx : BC_rect_R39.dx = 1.25 :=
  CentralCoverAssembly.R39_dx_eq
theorem BC_R39_dy : BC_rect_R39.dy = 0.095 :=
  CentralCoverAssembly.R39_dy_eq
theorem BC_R39_radius_eq :
    BC_rect_R39.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R39_radius_eq
theorem BC_R39_radius_lt : BC_rect_R39.radius < 1.26 := by
  rw [BC_R39_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R39_strip_of_mem {w : ℂ} (hw : BC_rect_R39.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R39_y0] at hy0
  rw [BC_R39_y1] at hy1
  constructor <;> linarith

theorem BC_R39_mem_gridFine : (6, 8.5, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((6, 8.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(6, 8.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC39 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R39.center

/-- Poly lower at R39 s-center. TRUE ~= 26 (floor 20). -/
def BC_polyLower_R39 : Prop :=
  (20 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC39‖

def BC_piLower_R39 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC39‖

/-- Gamma lower at R39 s-center. TRUE ~= 0.00472 (floor 0.004, 1.18x). -/
def BC_gammaLower_R39 : Prop :=
  (0.004 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC39‖

def BC_zetaLower_R39 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC39‖

def BC_derivTier_R39 : Prop :=
  ∀ w, BC_rect_R39.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BC_ballSup_R39 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R39.center (BC_rect_R39.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Negative margin at TRUE-scale floors: 20*0.5*0.004 = 0.04 < 0.0902. -/
theorem BC_R39_threshold_negative :
    (20 : ℝ) * (1 / 2) * 0.004 * 1 < (0.002 : ℝ) + 0.07 * 1.26 := by norm_num

theorem BC_R39_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R39_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R39_deriv_of_ballSup (hBall : BC_ballSup_R39) :
    ∀ w, BC_rect_R39.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R39 0.008 5600 (by norm_num) (fun w hw => BC_R39_strip_of_mem hw) hBall

theorem BC_R39_cauchy_tier_mismatch :
    (0.091 : ℝ) < (0.002 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R39_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC39‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC39‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC39‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC39‖)
    (hThresh : (0.002 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R39.center = BC_sC39 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R39.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R39.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BC_rect_R39.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R39_radius_lt) (by norm_num)
  linarith

theorem BC_R39_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R39 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BC_R39_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R39 0.002 0.07 BC_R39_strip_lo BC_R39_strip_hi
    (BC_R39_fencing_of_premises hC hD)

noncomputable def BC_R39_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R39 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    BC_R39_strip_lo BC_R39_strip_hi hD hC

theorem BC_R39_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39) {z : ℂ}
    (hx0 : BC_rect_R39.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R39.x1)
    (hy0 : BC_rect_R39.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R39.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R39 0.002 0.07 BC_R39_strip_lo BC_R39_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BC_R39_H_instance
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R39, 0.002, 0.07, rfl, rfl, rfl, rfl, BC_R39_strip_lo, BC_R39_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BC_R39_implies_leaf
    (hC : (0.002 : ℝ) + 0.07 * BC_rect_R39.radius ≤ ‖xiShifted BC_rect_R39.center‖)
    (hD : BC_derivTier_R39) :
    CentralCoverAssembly.R39_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## R40 = (7.5,10,0.3,0.49), outer tier (0.002,0.05): FEASIBILITY-NEGATIVE -/

def BC_rect_R40 : CellProofEngine.Rect2D := CentralCoverAssembly.R40

theorem BC_R40_x0 : BC_rect_R40.x0 = 7.5 := rfl
theorem BC_R40_x1 : BC_rect_R40.x1 = 10 := rfl
theorem BC_R40_y0 : BC_rect_R40.y0 = 0.3 := rfl
theorem BC_R40_y1 : BC_rect_R40.y1 = 0.49 := rfl

theorem BC_R40_width_eq : BC_rect_R40.x1 - BC_rect_R40.x0 = 2.5 := by
  rw [BC_R40_x0, BC_R40_x1]; norm_num

theorem BC_R40_strip_lo : -(1 / 2 : ℝ) < BC_rect_R40.y0 :=
  CentralCoverAssembly.R40_strip_lo
theorem BC_R40_strip_hi : BC_rect_R40.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R40_strip_hi

theorem BC_R40_dx : BC_rect_R40.dx = 1.25 :=
  CentralCoverAssembly.R40_dx_eq
theorem BC_R40_dy : BC_rect_R40.dy = 0.095 :=
  CentralCoverAssembly.R40_dy_eq
theorem BC_R40_radius_eq :
    BC_rect_R40.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R40_radius_eq
theorem BC_R40_radius_lt : BC_rect_R40.radius < 1.26 := by
  rw [BC_R40_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BC_R40_strip_of_mem {w : ℂ} (hw : BC_rect_R40.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BC_R40_y0] at hy0
  rw [BC_R40_y1] at hy1
  constructor <;> linarith

theorem BC_R40_mem_gridFine : (7.5, 10, 0.3, 0.49) ∈ CentralCoverAssembly.gridFine := by
  have hX : ((7.5, 10) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.3, 0.49) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(7.5, 10), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

noncomputable def BC_sC40 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BC_rect_R40.center

/-- Poly lower at R40 s-center. TRUE ~= 38 (floor 30). -/
def BC_polyLower_R40 : Prop :=
  (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BC_sC40‖

def BC_piLower_R40 : Prop :=
  (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf BC_sC40‖

/-- Gamma lower at R40 s-center. TRUE ~= 0.00134 (floor 0.001, 1.34x). -/
def BC_gammaLower_R40 : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BC_sC40‖

def BC_zetaLower_R40 : Prop :=
  (1 : ℝ) ≤ ‖zeta BC_sC40‖

def BC_derivTier_R40 : Prop :=
  ∀ w, BC_rect_R40.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

def BC_ballSup_R40 : Prop :=
  ∀ z ∈ Metric.closedBall BC_rect_R40.center (BC_rect_R40.radius + 0.008),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600

/-- Negative margin at TRUE-scale floors: 30*0.5*0.001 = 0.015 < 0.065. -/
theorem BC_R40_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by norm_num

theorem BC_R40_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
theorem BC_R40_M_eq : (5600 : ℝ) / 0.008 = 700000 := by norm_num

theorem BC_R40_deriv_of_ballSup (hBall : BC_ballSup_R40) :
    ∀ w, BC_rect_R40.mem w → ‖deriv xiShifted w‖ ≤ 5600 / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BC_rect_R40 0.008 5600 (by norm_num) (fun w hw => BC_R40_strip_of_mem hw) hBall

theorem BC_R40_cauchy_tier_mismatch :
    (0.066 : ℝ) < (0.002 : ℝ) + 700000 * 1.26 := by norm_num

theorem BC_R40_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BC_sC40‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BC_sC40‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BC_sC40‖)
    (hzeta : Azeta ≤ ‖zeta BC_sC40‖)
    (hThresh : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BC_rect_R40.center = BC_sC40 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BC_rect_R40.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BC_rect_R40.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * BC_rect_R40.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BC_R40_radius_lt) (by norm_num)
  linarith

theorem BC_R40_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40) :
    CentralCoverAssembly.CellFencingHypotheses BC_rect_R40 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BC_R40_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BC_rect_R40 0.002 0.05 BC_R40_strip_lo BC_R40_strip_hi
    (BC_R40_fencing_of_premises hC hD)

noncomputable def BC_R40_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BC_rect_R40 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BC_R40_strip_lo BC_R40_strip_hi hD hC

theorem BC_R40_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40) {z : ℂ}
    (hx0 : BC_rect_R40.x0 ≤ z.re) (hx1 : z.re ≤ BC_rect_R40.x1)
    (hy0 : BC_rect_R40.y0 ≤ z.im) (hy1 : z.im ≤ BC_rect_R40.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BC_rect_R40 0.002 0.05 BC_R40_strip_lo BC_R40_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BC_R40_H_instance
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BC_rect_R40, 0.002, 0.05, rfl, rfl, rfl, rfl, BC_R40_strip_lo, BC_R40_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BC_R40_implies_leaf
    (hC : (0.002 : ℝ) + 0.05 * BC_rect_R40.radius ≤ ‖xiShifted BC_rect_R40.center‖)
    (hD : BC_derivTier_R40) :
    CentralCoverAssembly.R40_leaf_obligations :=
  ⟨hC, hD⟩

end Door3BatchC
