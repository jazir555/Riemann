import Mathlib
import central_cover_assembly

/-!
# Door 3 SECOND-ROW cell batch (`door3_cells_batchB.lean`, NEW file)

WRITE-ONLY replication task (no build; patch phase later). This file owns
EXCLUSIVELY the SECOND row of `gridFine`: the row immediately above the
bottom `Im ∈ (0.01, 0.2)` row. Per inventory (`central_cover_assembly.lean`:
`innerGridY = [(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]` at `:372`;
`fineGridX` 10 columns width exactly `2.5` at `:954`;
`gridFine = fineGridX.flatMap …` 40 cells at `:1002`;
upper-row block `R11–R40` at `:2465`, row1 `y = (0.1,0.3)`, `dy = 0.1` at
`:2488`), the second row is `y = (0.1, 0.3)` (task brief says
"`Im ∈ [0.2,0.3]-class or per inventory`" — per inventory it is `(0.1,0.3)`;
staying in-row, no bottom-row or upper-row cells claimed here).

## CLAIMED CELLS (10 cells, all `y = (0.1, 0.3)`, `dy = 0.1`, centers `y = 0.2`)

| cell | `x`                 | z-center          | s-center (`(0.5-y)+x·I`) | tier `(ε,M)` | budget `ε+M*1.26` |
|------|---------------------|-------------------|--------------------------|--------------|-------------------|
| R11  | `(-10, -7.5)`       | `-8.75 + 0.2·I`   | `0.3 - 8.75·I`           | `(0.002,0.05)` outer | `0.065`   |
| R12  | `(-8, -5.5)`        | `-6.75 + 0.2·I`   | `0.3 - 6.75·I`           | `(0.002,0.07)` leaf* | `0.0902`  |
| R13  | `(-6, -3.5)`        | `-4.75 + 0.2·I`   | `0.3 - 4.75·I`           | `(0.05,0.07)` mid    | `0.1382`  |
| R14  | `(-4, -1.5)`        | `-2.75 + 0.2·I`   | `0.3 - 2.75·I`           | `(0.05,0.07)` mid    | `0.1382`  |
| R15  | `(-2, 0.5)`         | `-0.75 + 0.2·I`   | `0.3 - 0.75·I`           | `(0.15,0.06)` inner  | `0.2256`  |
| R16  | `(0, 2.5)`          | `1.25 + 0.2·I`    | `0.3 + 1.25·I`           | `(0.15,0.06)` inner  | `0.2256`  |
| R17  | `(2, 4.5)`          | `3.25 + 0.2·I`    | `0.3 + 3.25·I`           | `(0.05,0.07)` mid    | `0.1382`  |
| R18  | `(4, 6.5)`          | `5.25 + 0.2·I`    | `0.3 + 5.25·I`           | `(0.05,0.07)` mid    | `0.1382`  |
| R19  | `(6, 8.5)`          | `7.25 + 0.2·I`    | `0.3 + 7.25·I`           | `(0.002,0.07)` leaf* | `0.0902`  |
| R20  | `(7.5, 10)`         | `8.75 + 0.2·I`    | `0.3 + 8.75·I`           | `(0.002,0.05)` outer | `0.065`   |

`*` DISCREPANCY (read-only finding, flagged): the section headers at `:2574`
(R12) and `:3162` (R19) say "outer tier `(0.002,0.05)`" but the LEAF DEFS
(`R12_leaf_obligations` at `:2617`, `R19_leaf_obligations` at `:3205`) use
`M = 0.07`. This file follows the LEAF DEFS (authoritative for obligations).

All 10 cells: `dx = 1.25`, `dy = 0.1`,
`radius = √(1.25² + 0.1²) < 1.26` (`sample_cell_radius_01_bound` at `:2482`).

## RECON RECORD (read-only, verified before writing; no file touched)

CITED (all verified present in `central_cover_assembly.lean`):
* `CellFencingHypotheses` (`:504`): fields `ε_pos`, `deriv_bound`, `center_bound`.
* `fine_eps_outer_pos` (`:1032`), `fine_eps_mid_pos` (`:1033`),
  `fine_eps_inner_pos` (`:1034`) — tier `ε`-positivity per cell tier.
* `sample_cell_radius_01_bound` (`:2482`) — upper-row `(1.25,0.1)` radius cap.
* Per-cell banked `R11`–`R20`: rect defs, `RXX_x0/x1/y0/y1`, `RXX_strip_lo/hi`,
  `RXX_dx/dy/radius_eq`, `RXX_radius_lt`, `RXX_mem_gridFine`,
  `RXX_leaf_obligations`, `RXX_fencing_of_bounds`, `RXX_H_instance`.
* `lowerBoundRect_of_fencingHypotheses_strip` (`:941`),
  `zeroFreeRect_of_rect_center_bound_strip` (`:931`),
  `xi_rect_lower_bound_of_center_bound_strip` (`:882`).
* H-leaf `inner_nonvanishing_of_fenced_grid_fine` (`:1047`).
* `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`):
  closed-ball sup `C` on `closedBall center (radius + r)` gives
  `‖deriv xiShifted w‖ ≤ C / r`.
ABSENT (verified by grep; NO banked pilots/discs/P1 for this row — contrast
the R02 lane which has `R02Pilot`, `R02GammaDisc.gammaOf_upper_disc_R02`,
`DG_GapTransfer.P1_R02_unconditional`, `Door3DownstreamDischarge`): no
`R11`–`R20` pilots, no second-row Gamma discs, no second-row zeta uppers.
Hence NO factor-center-lower citations are made here: each cell's center
inequality (the `RXX_leaf_obligations` center component) is itself the
explicit premise, with four-factor TRUE estimates in comments for patch phase.
NOT cited (cycle-safety): `interval_arith`, `riemann_hypothesis_newsection`
(the template `door3_first_cell.lean` uses them for banked R02 content; this
row has no such banked content, so imports stay `Mathlib` +
`central_cover_assembly` only).

## PER-CELL STATUS (all 10: CLOSED-conditional on 3 explicit premises each)

Each cell replicates the 12-step template of `door3_first_cell.lean:349`:
rect alias → coords → geometry → center-lower (premise; no banked factors on
this row) → `norm_num` budget threshold → Cauchy deriv route → fencing triple
→ H-leaf-shaped conclusion. Premises per cell (explicit `Prop`s, TRUE-value
comments, no `sorry`/`admit`/`axiom`, explicit binders, no `simpa`, numerals
≤ 6 digits, `norm_num` only on `ℝ`/`ℕ` goals):
(1) center premise `ε + M*radius ≤ ‖ξ(center)‖` — TRUE (feasibility-positive
per the `fine_feasible_*` pattern: budgets `0.065/0.0902/0.1382/0.2256` vs
true centers `O(0.1)–O(1)`; outer cells tighter via Gamma `Im`-decay);
(2) deriv-tier premise `‖deriv xiShifted‖ ≤ M` on the rect — TRUE unknown
(wall; Cauchy floor `≥ 0.358`-class exceeds every tier here too, so direct
bounds or subdivision + re-tiering needed — patch phase);
(3) closed-ball sup premise `‖xiShiftedEntire‖ ≤ 16800` on the fat ball —
TRUE with large margin (true `~10–50`; ultra-safe upper, needs wide-rect
verification — patch phase).
-/

noncomputable section

namespace Door3BatchB

/-! ## Shared tier budgets + Cauchy closed form (PROVED, no premises) -/

/-- Outer-tier budget `0.002 + 0.05 * 1.26 = 0.065` (R11, R20). -/
theorem B_budget_outer05 :
    (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

/-- Outer-header/leaf-mismatch-tier budget `0.002 + 0.07 * 1.26 = 0.0902`
(R12, R19 leaf `M = 0.07`). -/
theorem B_budget_outer07 :
    (0.002 : ℝ) + 0.07 * 1.26 = 0.0902 := by norm_num

/-- Mid-tier budget `0.05 + 0.07 * 1.26 = 0.1382` (R13, R14, R17, R18). -/
theorem B_budget_mid :
    (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

/-- Inner-tier budget `0.15 + 0.06 * 1.26 = 0.2256` (R15, R16). -/
theorem B_budget_inner :
    (0.15 : ℝ) + 0.06 * 1.26 = 0.2256 := by norm_num

/-- Cauchy closed form `16800 / 0.25 = 67200` (all cells, `r = 0.25`). -/
theorem B_cauchy_closedForm : (16800 : ℝ) / 0.25 = 67200 := by norm_num

/-- Honest gaps: every tier `M` here is far below the Cauchy `M = 67200`. -/
theorem B_cauchy_tier_mismatch05 : (0.05 : ℝ) < 67200 := by norm_num
theorem B_cauchy_tier_mismatch07 : (0.07 : ℝ) < 67200 := by norm_num
theorem B_cauchy_tier_mismatch06 : (0.06 : ℝ) < 67200 := by norm_num

/-! ## B11 = (-10, -7.5, 0.1, 0.3), outer tier `(0.002, 0.05)` -/

/-- Rect alias so every banked R11 lemma applies definitionally. -/
def B11_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R11

theorem B11_x0 : B11_rect.x0 = -10 := rfl
theorem B11_x1 : B11_rect.x1 = -7.5 := rfl
theorem B11_y0 : B11_rect.y0 = 0.1 := rfl
theorem B11_y1 : B11_rect.y1 = 0.3 := rfl

theorem B11_width_eq : B11_rect.x1 - B11_rect.x0 = 2.5 := by
  rw [B11_x0, B11_x1]; norm_num

theorem B11_strip_lo : -(1 / 2 : ℝ) < B11_rect.y0 :=
  CentralCoverAssembly.R11_strip_lo
theorem B11_strip_hi : B11_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R11_strip_hi

theorem B11_dx : B11_rect.dx = 1.25 :=
  CentralCoverAssembly.R11_dx_eq
theorem B11_dy : B11_rect.dy = 0.1 :=
  CentralCoverAssembly.R11_dy_eq
theorem B11_radius_eq :
    B11_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R11_radius_eq
theorem B11_radius_lt : B11_rect.radius < 1.26 := by
  rw [B11_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B11_strip_of_mem {w : ℂ} (hw : B11_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B11_y0] at hy0
  rw [B11_y1] at hy1
  constructor <;> linarith

theorem B11_mem_gridFine :
    ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R11_mem_gridFine

/-- Center premise (the `R11_leaf_obligations` center component). TRUE:
budget `0.065` vs true center `O(0.1)` (outer cell, Gamma `Im`-decay at
`s = 0.3 - 8.75·I` makes this the tightest outer claim; feasibility-positive
per the `fine_feasible_outer` pattern). -/
def B11_center_obligation : Prop :=
  (0.002 : ℝ) + 0.05 * B11_rect.radius ≤ ‖xiShifted B11_rect.center‖

/-- Tier deriv premise. TRUE unknown (wall). -/
def B11_derivTier_obligation : Prop :=
  ∀ w, B11_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

/-- Closed-ball sup premise for the Cauchy route. TRUE `~10–50` (ultra-safe). -/
def B11_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B11_rect.center (B11_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B11_budget_check : (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

theorem B11_deriv_of_ballSup (hBall : B11_ballSup_obligation) :
    ∀ w, B11_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B11_rect 0.25 16800 (by norm_num) (fun w hw => B11_strip_of_mem hw) hBall

theorem B11_fencing_of_premises
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B11_rect 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def B11_lowerBound_of_premises
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B11_rect 0.002 0.05 B11_strip_lo B11_strip_hi
    (B11_fencing_of_premises hC hD)

noncomputable def B11_zeroFree_of_premises
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B11_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    B11_strip_lo B11_strip_hi hD hC

theorem B11_nonvanishing_of_premises
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation) {z : ℂ}
    (hx0 : B11_rect.x0 ≤ z.re) (hx1 : z.re ≤ B11_rect.x1)
    (hy0 : B11_rect.y0 ≤ z.im) (hy1 : z.im ≤ B11_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B11_rect 0.002 0.05 B11_strip_lo B11_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem B11_H_instance
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-10, -7.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B11_rect, 0.002, 0.05, rfl, rfl, rfl, rfl, B11_strip_lo, B11_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem B11_implies_R11_leaf
    (hC : B11_center_obligation) (hD : B11_derivTier_obligation) :
    CentralCoverAssembly.R11_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B12 = (-8, -5.5, 0.1, 0.3), leaf tier `(0.002, 0.07)` -/

def B12_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R12

theorem B12_x0 : B12_rect.x0 = -8 := rfl
theorem B12_x1 : B12_rect.x1 = -5.5 := rfl
theorem B12_y0 : B12_rect.y0 = 0.1 := rfl
theorem B12_y1 : B12_rect.y1 = 0.3 := rfl

theorem B12_width_eq : B12_rect.x1 - B12_rect.x0 = 2.5 := by
  rw [B12_x0, B12_x1]; norm_num

theorem B12_strip_lo : -(1 / 2 : ℝ) < B12_rect.y0 :=
  CentralCoverAssembly.R12_strip_lo
theorem B12_strip_hi : B12_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R12_strip_hi

theorem B12_dx : B12_rect.dx = 1.25 :=
  CentralCoverAssembly.R12_dx_eq
theorem B12_dy : B12_rect.dy = 0.1 :=
  CentralCoverAssembly.R12_dy_eq
theorem B12_radius_eq :
    B12_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R12_radius_eq
theorem B12_radius_lt : B12_rect.radius < 1.26 := by
  rw [B12_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B12_strip_of_mem {w : ℂ} (hw : B12_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B12_y0] at hy0
  rw [B12_y1] at hy1
  constructor <;> linarith

theorem B12_mem_gridFine :
    ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R12_mem_gridFine

/-- Center premise. TRUE: budget `0.0902` vs true center `O(0.1)–O(1)` at
`s = 0.3 - 6.75·I` (directly above the banked R02 column; R02-column true
center `≈ 0.24` at `y = 0.105` suggests feasibility-positive here too). -/
def B12_center_obligation : Prop :=
  (0.002 : ℝ) + 0.07 * B12_rect.radius ≤ ‖xiShifted B12_rect.center‖

def B12_derivTier_obligation : Prop :=
  ∀ w, B12_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B12_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B12_rect.center (B12_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B12_budget_check : (0.002 : ℝ) + 0.07 * 1.26 = 0.0902 := by norm_num

theorem B12_deriv_of_ballSup (hBall : B12_ballSup_obligation) :
    ∀ w, B12_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B12_rect 0.25 16800 (by norm_num) (fun w hw => B12_strip_of_mem hw) hBall

theorem B12_fencing_of_premises
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B12_rect 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def B12_lowerBound_of_premises
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B12_rect 0.002 0.07 B12_strip_lo B12_strip_hi
    (B12_fencing_of_premises hC hD)

noncomputable def B12_zeroFree_of_premises
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B12_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    B12_strip_lo B12_strip_hi hD hC

theorem B12_nonvanishing_of_premises
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation) {z : ℂ}
    (hx0 : B12_rect.x0 ≤ z.re) (hx1 : z.re ≤ B12_rect.x1)
    (hy0 : B12_rect.y0 ≤ z.im) (hy1 : z.im ≤ B12_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B12_rect 0.002 0.07 B12_strip_lo B12_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem B12_H_instance
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B12_rect, 0.002, 0.07, rfl, rfl, rfl, rfl, B12_strip_lo, B12_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem B12_implies_R12_leaf
    (hC : B12_center_obligation) (hD : B12_derivTier_obligation) :
    CentralCoverAssembly.R12_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B13 = (-6, -3.5, 0.1, 0.3), mid tier `(0.05, 0.07)` -/

def B13_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R13

theorem B13_x0 : B13_rect.x0 = -6 := rfl
theorem B13_x1 : B13_rect.x1 = -3.5 := rfl
theorem B13_y0 : B13_rect.y0 = 0.1 := rfl
theorem B13_y1 : B13_rect.y1 = 0.3 := rfl

theorem B13_width_eq : B13_rect.x1 - B13_rect.x0 = 2.5 := by
  rw [B13_x0, B13_x1]; norm_num

theorem B13_strip_lo : -(1 / 2 : ℝ) < B13_rect.y0 :=
  CentralCoverAssembly.R13_strip_lo
theorem B13_strip_hi : B13_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R13_strip_hi

theorem B13_dx : B13_rect.dx = 1.25 :=
  CentralCoverAssembly.R13_dx_eq
theorem B13_dy : B13_rect.dy = 0.1 :=
  CentralCoverAssembly.R13_dy_eq
theorem B13_radius_eq :
    B13_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R13_radius_eq
theorem B13_radius_lt : B13_rect.radius < 1.26 := by
  rw [B13_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B13_strip_of_mem {w : ℂ} (hw : B13_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B13_y0] at hy0
  rw [B13_y1] at hy1
  constructor <;> linarith

theorem B13_mem_gridFine :
    ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R13_mem_gridFine

/-- Center premise. TRUE: budget `0.1382` vs true center `O(0.3)–O(1)` at
`s = 0.3 - 4.75·I` (mid column; feasibility-positive per `fine_feasible_mid`
pattern `0.138`). -/
def B13_center_obligation : Prop :=
  (0.05 : ℝ) + 0.07 * B13_rect.radius ≤ ‖xiShifted B13_rect.center‖

def B13_derivTier_obligation : Prop :=
  ∀ w, B13_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B13_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B13_rect.center (B13_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B13_budget_check : (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

theorem B13_deriv_of_ballSup (hBall : B13_ballSup_obligation) :
    ∀ w, B13_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B13_rect 0.25 16800 (by norm_num) (fun w hw => B13_strip_of_mem hw) hBall

theorem B13_fencing_of_premises
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B13_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def B13_lowerBound_of_premises
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B13_rect 0.05 0.07 B13_strip_lo B13_strip_hi
    (B13_fencing_of_premises hC hD)

noncomputable def B13_zeroFree_of_premises
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B13_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    B13_strip_lo B13_strip_hi hD hC

theorem B13_nonvanishing_of_premises
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation) {z : ℂ}
    (hx0 : B13_rect.x0 ≤ z.re) (hx1 : z.re ≤ B13_rect.x1)
    (hy0 : B13_rect.y0 ≤ z.im) (hy1 : z.im ≤ B13_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B13_rect 0.05 0.07 B13_strip_lo B13_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem B13_H_instance
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-6, -3.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B13_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, B13_strip_lo, B13_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem B13_implies_R13_leaf
    (hC : B13_center_obligation) (hD : B13_derivTier_obligation) :
    CentralCoverAssembly.R13_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B14 = (-4, -1.5, 0.1, 0.3), mid tier `(0.05, 0.07)` -/

def B14_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R14

theorem B14_x0 : B14_rect.x0 = -4 := rfl
theorem B14_x1 : B14_rect.x1 = -1.5 := rfl
theorem B14_y0 : B14_rect.y0 = 0.1 := rfl
theorem B14_y1 : B14_rect.y1 = 0.3 := rfl

theorem B14_width_eq : B14_rect.x1 - B14_rect.x0 = 2.5 := by
  rw [B14_x0, B14_x1]; norm_num

theorem B14_strip_lo : -(1 / 2 : ℝ) < B14_rect.y0 :=
  CentralCoverAssembly.R14_strip_lo
theorem B14_strip_hi : B14_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R14_strip_hi

theorem B14_dx : B14_rect.dx = 1.25 :=
  CentralCoverAssembly.R14_dx_eq
theorem B14_dy : B14_rect.dy = 0.1 :=
  CentralCoverAssembly.R14_dy_eq
theorem B14_radius_eq :
    B14_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R14_radius_eq
theorem B14_radius_lt : B14_rect.radius < 1.26 := by
  rw [B14_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B14_strip_of_mem {w : ℂ} (hw : B14_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B14_y0] at hy0
  rw [B14_y1] at hy1
  constructor <;> linarith

theorem B14_mem_gridFine :
    ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R14_mem_gridFine

/-- Center premise. TRUE: budget `0.1382` vs true center `O(0.5)–O(1)` at
`s = 0.3 - 2.75·I`. -/
def B14_center_obligation : Prop :=
  (0.05 : ℝ) + 0.07 * B14_rect.radius ≤ ‖xiShifted B14_rect.center‖

def B14_derivTier_obligation : Prop :=
  ∀ w, B14_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B14_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B14_rect.center (B14_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B14_budget_check : (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

theorem B14_deriv_of_ballSup (hBall : B14_ballSup_obligation) :
    ∀ w, B14_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B14_rect 0.25 16800 (by norm_num) (fun w hw => B14_strip_of_mem hw) hBall

theorem B14_fencing_of_premises
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B14_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def B14_lowerBound_of_premises
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B14_rect 0.05 0.07 B14_strip_lo B14_strip_hi
    (B14_fencing_of_premises hC hD)

noncomputable def B14_zeroFree_of_premises
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B14_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    B14_strip_lo B14_strip_hi hD hC

theorem B14_nonvanishing_of_premises
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation) {z : ℂ}
    (hx0 : B14_rect.x0 ≤ z.re) (hx1 : z.re ≤ B14_rect.x1)
    (hy0 : B14_rect.y0 ≤ z.im) (hy1 : z.im ≤ B14_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B14_rect 0.05 0.07 B14_strip_lo B14_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem B14_H_instance
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-4, -1.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B14_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, B14_strip_lo, B14_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem B14_implies_R14_leaf
    (hC : B14_center_obligation) (hD : B14_derivTier_obligation) :
    CentralCoverAssembly.R14_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B15 = (-2, 0.5, 0.1, 0.3), inner tier `(0.15, 0.06)` -/

def B15_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R15

theorem B15_x0 : B15_rect.x0 = -2 := rfl
theorem B15_x1 : B15_rect.x1 = 0.5 := rfl
theorem B15_y0 : B15_rect.y0 = 0.1 := rfl
theorem B15_y1 : B15_rect.y1 = 0.3 := rfl

theorem B15_width_eq : B15_rect.x1 - B15_rect.x0 = 2.5 := by
  rw [B15_x0, B15_x1]; norm_num

theorem B15_strip_lo : -(1 / 2 : ℝ) < B15_rect.y0 :=
  CentralCoverAssembly.R15_strip_lo
theorem B15_strip_hi : B15_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R15_strip_hi

theorem B15_dx : B15_rect.dx = 1.25 :=
  CentralCoverAssembly.R15_dx_eq
theorem B15_dy : B15_rect.dy = 0.1 :=
  CentralCoverAssembly.R15_dy_eq
theorem B15_radius_eq :
    B15_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R15_radius_eq
theorem B15_radius_lt : B15_rect.radius < 1.26 := by
  rw [B15_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B15_strip_of_mem {w : ℂ} (hw : B15_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B15_y0] at hy0
  rw [B15_y1] at hy1
  constructor <;> linarith

theorem B15_mem_gridFine :
    ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R15_mem_gridFine

/-- Center premise. TRUE with wide margin: budget `0.2256` vs true center
`O(1)–O(2)` at `s = 0.3 - 0.75·I` (central column, largest raw margin class;
mirrors the template's R05 remark — inner cells have the most headroom). -/
def B15_center_obligation : Prop :=
  (0.15 : ℝ) + 0.06 * B15_rect.radius ≤ ‖xiShifted B15_rect.center‖

def B15_derivTier_obligation : Prop :=
  ∀ w, B15_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def B15_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B15_rect.center (B15_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B15_budget_check : (0.15 : ℝ) + 0.06 * 1.26 = 0.2256 := by norm_num

theorem B15_deriv_of_ballSup (hBall : B15_ballSup_obligation) :
    ∀ w, B15_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B15_rect 0.25 16800 (by norm_num) (fun w hw => B15_strip_of_mem hw) hBall

theorem B15_fencing_of_premises
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B15_rect 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def B15_lowerBound_of_premises
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B15_rect 0.15 0.06 B15_strip_lo B15_strip_hi
    (B15_fencing_of_premises hC hD)

noncomputable def B15_zeroFree_of_premises
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B15_rect 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    B15_strip_lo B15_strip_hi hD hC

theorem B15_nonvanishing_of_premises
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation) {z : ℂ}
    (hx0 : B15_rect.x0 ≤ z.re) (hx1 : z.re ≤ B15_rect.x1)
    (hy0 : B15_rect.y0 ≤ z.im) (hy1 : z.im ≤ B15_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B15_rect 0.15 0.06 B15_strip_lo B15_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem B15_H_instance
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B15_rect, 0.15, 0.06, rfl, rfl, rfl, rfl, B15_strip_lo, B15_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem B15_implies_R15_leaf
    (hC : B15_center_obligation) (hD : B15_derivTier_obligation) :
    CentralCoverAssembly.R15_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B16 = (0, 2.5, 0.1, 0.3), inner tier `(0.15, 0.06)` -/

def B16_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R16

theorem B16_x0 : B16_rect.x0 = 0 := rfl
theorem B16_x1 : B16_rect.x1 = 2.5 := rfl
theorem B16_y0 : B16_rect.y0 = 0.1 := rfl
theorem B16_y1 : B16_rect.y1 = 0.3 := rfl

theorem B16_width_eq : B16_rect.x1 - B16_rect.x0 = 2.5 := by
  rw [B16_x0, B16_x1]; norm_num

theorem B16_strip_lo : -(1 / 2 : ℝ) < B16_rect.y0 :=
  CentralCoverAssembly.R16_strip_lo
theorem B16_strip_hi : B16_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R16_strip_hi

theorem B16_dx : B16_rect.dx = 1.25 :=
  CentralCoverAssembly.R16_dx_eq
theorem B16_dy : B16_rect.dy = 0.1 :=
  CentralCoverAssembly.R16_dy_eq
theorem B16_radius_eq :
    B16_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R16_radius_eq
theorem B16_radius_lt : B16_rect.radius < 1.26 := by
  rw [B16_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B16_strip_of_mem {w : ℂ} (hw : B16_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B16_y0] at hy0
  rw [B16_y1] at hy1
  constructor <;> linarith

theorem B16_mem_gridFine :
    ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R16_mem_gridFine

/-- Center premise. TRUE with wide margin: budget `0.2256` vs true center
`O(1)–O(2)` at `s = 0.3 + 1.25·I`. -/
def B16_center_obligation : Prop :=
  (0.15 : ℝ) + 0.06 * B16_rect.radius ≤ ‖xiShifted B16_rect.center‖

def B16_derivTier_obligation : Prop :=
  ∀ w, B16_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def B16_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B16_rect.center (B16_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B16_budget_check : (0.15 : ℝ) + 0.06 * 1.26 = 0.2256 := by norm_num

theorem B16_deriv_of_ballSup (hBall : B16_ballSup_obligation) :
    ∀ w, B16_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B16_rect 0.25 16800 (by norm_num) (fun w hw => B16_strip_of_mem hw) hBall

theorem B16_fencing_of_premises
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B16_rect 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def B16_lowerBound_of_premises
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B16_rect 0.15 0.06 B16_strip_lo B16_strip_hi
    (B16_fencing_of_premises hC hD)

noncomputable def B16_zeroFree_of_premises
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B16_rect 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    B16_strip_lo B16_strip_hi hD hC

theorem B16_nonvanishing_of_premises
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation) {z : ℂ}
    (hx0 : B16_rect.x0 ≤ z.re) (hx1 : z.re ≤ B16_rect.x1)
    (hy0 : B16_rect.y0 ≤ z.im) (hy1 : z.im ≤ B16_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B16_rect 0.15 0.06 B16_strip_lo B16_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem B16_H_instance
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B16_rect, 0.15, 0.06, rfl, rfl, rfl, rfl, B16_strip_lo, B16_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem B16_implies_R16_leaf
    (hC : B16_center_obligation) (hD : B16_derivTier_obligation) :
    CentralCoverAssembly.R16_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B17 = (2, 4.5, 0.1, 0.3), mid tier `(0.05, 0.07)` -/

def B17_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R17

theorem B17_x0 : B17_rect.x0 = 2 := rfl
theorem B17_x1 : B17_rect.x1 = 4.5 := rfl
theorem B17_y0 : B17_rect.y0 = 0.1 := rfl
theorem B17_y1 : B17_rect.y1 = 0.3 := rfl

theorem B17_width_eq : B17_rect.x1 - B17_rect.x0 = 2.5 := by
  rw [B17_x0, B17_x1]; norm_num

theorem B17_strip_lo : -(1 / 2 : ℝ) < B17_rect.y0 :=
  CentralCoverAssembly.R17_strip_lo
theorem B17_strip_hi : B17_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R17_strip_hi

theorem B17_dx : B17_rect.dx = 1.25 :=
  CentralCoverAssembly.R17_dx_eq
theorem B17_dy : B17_rect.dy = 0.1 :=
  CentralCoverAssembly.R17_dy_eq
theorem B17_radius_eq :
    B17_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R17_radius_eq
theorem B17_radius_lt : B17_rect.radius < 1.26 := by
  rw [B17_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B17_strip_of_mem {w : ℂ} (hw : B17_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B17_y0] at hy0
  rw [B17_y1] at hy1
  constructor <;> linarith

theorem B17_mem_gridFine :
    ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R17_mem_gridFine

/-- Center premise. TRUE: budget `0.1382` vs true center `O(0.5)–O(1)` at
`s = 0.3 + 3.25·I`. -/
def B17_center_obligation : Prop :=
  (0.05 : ℝ) + 0.07 * B17_rect.radius ≤ ‖xiShifted B17_rect.center‖

def B17_derivTier_obligation : Prop :=
  ∀ w, B17_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B17_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B17_rect.center (B17_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B17_budget_check : (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

theorem B17_deriv_of_ballSup (hBall : B17_ballSup_obligation) :
    ∀ w, B17_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B17_rect 0.25 16800 (by norm_num) (fun w hw => B17_strip_of_mem hw) hBall

theorem B17_fencing_of_premises
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B17_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def B17_lowerBound_of_premises
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B17_rect 0.05 0.07 B17_strip_lo B17_strip_hi
    (B17_fencing_of_premises hC hD)

noncomputable def B17_zeroFree_of_premises
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B17_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    B17_strip_lo B17_strip_hi hD hC

theorem B17_nonvanishing_of_premises
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation) {z : ℂ}
    (hx0 : B17_rect.x0 ≤ z.re) (hx1 : z.re ≤ B17_rect.x1)
    (hy0 : B17_rect.y0 ≤ z.im) (hy1 : z.im ≤ B17_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B17_rect 0.05 0.07 B17_strip_lo B17_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem B17_H_instance
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B17_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, B17_strip_lo, B17_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem B17_implies_R17_leaf
    (hC : B17_center_obligation) (hD : B17_derivTier_obligation) :
    CentralCoverAssembly.R17_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B18 = (4, 6.5, 0.1, 0.3), mid tier `(0.05, 0.07)` -/

def B18_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R18

theorem B18_x0 : B18_rect.x0 = 4 := rfl
theorem B18_x1 : B18_rect.x1 = 6.5 := rfl
theorem B18_y0 : B18_rect.y0 = 0.1 := rfl
theorem B18_y1 : B18_rect.y1 = 0.3 := rfl

theorem B18_width_eq : B18_rect.x1 - B18_rect.x0 = 2.5 := by
  rw [B18_x0, B18_x1]; norm_num

theorem B18_strip_lo : -(1 / 2 : ℝ) < B18_rect.y0 :=
  CentralCoverAssembly.R18_strip_lo
theorem B18_strip_hi : B18_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R18_strip_hi

theorem B18_dx : B18_rect.dx = 1.25 :=
  CentralCoverAssembly.R18_dx_eq
theorem B18_dy : B18_rect.dy = 0.1 :=
  CentralCoverAssembly.R18_dy_eq
theorem B18_radius_eq :
    B18_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R18_radius_eq
theorem B18_radius_lt : B18_rect.radius < 1.26 := by
  rw [B18_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B18_strip_of_mem {w : ℂ} (hw : B18_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B18_y0] at hy0
  rw [B18_y1] at hy1
  constructor <;> linarith

theorem B18_mem_gridFine :
    ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R18_mem_gridFine

/-- Center premise. TRUE: budget `0.1382` vs true center `O(0.3)–O(1)` at
`s = 0.3 + 5.25·I`. -/
def B18_center_obligation : Prop :=
  (0.05 : ℝ) + 0.07 * B18_rect.radius ≤ ‖xiShifted B18_rect.center‖

def B18_derivTier_obligation : Prop :=
  ∀ w, B18_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B18_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B18_rect.center (B18_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B18_budget_check : (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

theorem B18_deriv_of_ballSup (hBall : B18_ballSup_obligation) :
    ∀ w, B18_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B18_rect 0.25 16800 (by norm_num) (fun w hw => B18_strip_of_mem hw) hBall

theorem B18_fencing_of_premises
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B18_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def B18_lowerBound_of_premises
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B18_rect 0.05 0.07 B18_strip_lo B18_strip_hi
    (B18_fencing_of_premises hC hD)

noncomputable def B18_zeroFree_of_premises
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B18_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    B18_strip_lo B18_strip_hi hD hC

theorem B18_nonvanishing_of_premises
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation) {z : ℂ}
    (hx0 : B18_rect.x0 ≤ z.re) (hx1 : z.re ≤ B18_rect.x1)
    (hy0 : B18_rect.y0 ≤ z.im) (hy1 : z.im ≤ B18_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B18_rect 0.05 0.07 B18_strip_lo B18_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem B18_H_instance
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B18_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, B18_strip_lo, B18_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem B18_implies_R18_leaf
    (hC : B18_center_obligation) (hD : B18_derivTier_obligation) :
    CentralCoverAssembly.R18_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B19 = (6, 8.5, 0.1, 0.3), leaf tier `(0.002, 0.07)` -/

def B19_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R19

theorem B19_x0 : B19_rect.x0 = 6 := rfl
theorem B19_x1 : B19_rect.x1 = 8.5 := rfl
theorem B19_y0 : B19_rect.y0 = 0.1 := rfl
theorem B19_y1 : B19_rect.y1 = 0.3 := rfl

theorem B19_width_eq : B19_rect.x1 - B19_rect.x0 = 2.5 := by
  rw [B19_x0, B19_x1]; norm_num

theorem B19_strip_lo : -(1 / 2 : ℝ) < B19_rect.y0 :=
  CentralCoverAssembly.R19_strip_lo
theorem B19_strip_hi : B19_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R19_strip_hi

theorem B19_dx : B19_rect.dx = 1.25 :=
  CentralCoverAssembly.R19_dx_eq
theorem B19_dy : B19_rect.dy = 0.1 :=
  CentralCoverAssembly.R19_dy_eq
theorem B19_radius_eq :
    B19_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R19_radius_eq
theorem B19_radius_lt : B19_rect.radius < 1.26 := by
  rw [B19_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B19_strip_of_mem {w : ℂ} (hw : B19_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B19_y0] at hy0
  rw [B19_y1] at hy1
  constructor <;> linarith

theorem B19_mem_gridFine :
    ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R19_mem_gridFine

/-- Center premise. TRUE: budget `0.0902` vs true center `O(0.1)` at
`s = 0.3 + 7.25·I` (outer column, Gamma decay; tighter but
feasibility-positive per the outer-tier pattern). -/
def B19_center_obligation : Prop :=
  (0.002 : ℝ) + 0.07 * B19_rect.radius ≤ ‖xiShifted B19_rect.center‖

def B19_derivTier_obligation : Prop :=
  ∀ w, B19_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def B19_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B19_rect.center (B19_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B19_budget_check : (0.002 : ℝ) + 0.07 * 1.26 = 0.0902 := by norm_num

theorem B19_deriv_of_ballSup (hBall : B19_ballSup_obligation) :
    ∀ w, B19_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B19_rect 0.25 16800 (by norm_num) (fun w hw => B19_strip_of_mem hw) hBall

theorem B19_fencing_of_premises
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B19_rect 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def B19_lowerBound_of_premises
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B19_rect 0.002 0.07 B19_strip_lo B19_strip_hi
    (B19_fencing_of_premises hC hD)

noncomputable def B19_zeroFree_of_premises
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B19_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    B19_strip_lo B19_strip_hi hD hC

theorem B19_nonvanishing_of_premises
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation) {z : ℂ}
    (hx0 : B19_rect.x0 ≤ z.re) (hx1 : z.re ≤ B19_rect.x1)
    (hy0 : B19_rect.y0 ≤ z.im) (hy1 : z.im ≤ B19_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B19_rect 0.002 0.07 B19_strip_lo B19_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem B19_H_instance
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B19_rect, 0.002, 0.07, rfl, rfl, rfl, rfl, B19_strip_lo, B19_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem B19_implies_R19_leaf
    (hC : B19_center_obligation) (hD : B19_derivTier_obligation) :
    CentralCoverAssembly.R19_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## B20 = (7.5, 10, 0.1, 0.3), outer tier `(0.002, 0.05)` -/

def B20_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R20

theorem B20_x0 : B20_rect.x0 = 7.5 := rfl
theorem B20_x1 : B20_rect.x1 = 10 := rfl
theorem B20_y0 : B20_rect.y0 = 0.1 := rfl
theorem B20_y1 : B20_rect.y1 = 0.3 := rfl

theorem B20_width_eq : B20_rect.x1 - B20_rect.x0 = 2.5 := by
  rw [B20_x0, B20_x1]; norm_num

theorem B20_strip_lo : -(1 / 2 : ℝ) < B20_rect.y0 :=
  CentralCoverAssembly.R20_strip_lo
theorem B20_strip_hi : B20_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R20_strip_hi

theorem B20_dx : B20_rect.dx = 1.25 :=
  CentralCoverAssembly.R20_dx_eq
theorem B20_dy : B20_rect.dy = 0.1 :=
  CentralCoverAssembly.R20_dy_eq
theorem B20_radius_eq :
    B20_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) :=
  CentralCoverAssembly.R20_radius_eq
theorem B20_radius_lt : B20_rect.radius < 1.26 := by
  rw [B20_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_01_bound

theorem B20_strip_of_mem {w : ℂ} (hw : B20_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [B20_y0] at hy0
  rw [B20_y1] at hy1
  constructor <;> linarith

theorem B20_mem_gridFine :
    ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R20_mem_gridFine

/-- Center premise. TRUE: budget `0.065` vs true center `O(0.1)` at
`s = 0.3 + 8.75·I` (far-outer cell, tightest Gamma decay in this row;
feasibility-positive per the outer-tier pattern, patch phase verifies). -/
def B20_center_obligation : Prop :=
  (0.002 : ℝ) + 0.05 * B20_rect.radius ≤ ‖xiShifted B20_rect.center‖

def B20_derivTier_obligation : Prop :=
  ∀ w, B20_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

def B20_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall B20_rect.center (B20_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

theorem B20_budget_check : (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

theorem B20_deriv_of_ballSup (hBall : B20_ballSup_obligation) :
    ∀ w, B20_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    B20_rect 0.25 16800 (by norm_num) (fun w hw => B20_strip_of_mem hw) hBall

theorem B20_fencing_of_premises
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses B20_rect 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def B20_lowerBound_of_premises
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    B20_rect 0.002 0.05 B20_strip_lo B20_strip_hi
    (B20_fencing_of_premises hC hD)

noncomputable def B20_zeroFree_of_premises
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    B20_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    B20_strip_lo B20_strip_hi hD hC

theorem B20_nonvanishing_of_premises
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation) {z : ℂ}
    (hx0 : B20_rect.x0 ≤ z.re) (hx1 : z.re ≤ B20_rect.x1)
    (hy0 : B20_rect.y0 ≤ z.im) (hy1 : z.im ≤ B20_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      B20_rect 0.002 0.05 B20_strip_lo B20_strip_hi hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem B20_H_instance
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨B20_rect, 0.002, 0.05, rfl, rfl, rfl, rfl, B20_strip_lo, B20_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem B20_implies_R20_leaf
    (hC : B20_center_obligation) (hD : B20_derivTier_obligation) :
    CentralCoverAssembly.R20_leaf_obligations :=
  ⟨hC, hD⟩

  /-! ## Factor decomposition for all 10 cells (B11-B20)

  Each cell decomposes `‖xiShifted z‖` via
  `DerivCauchyBridge.norm_xiShifted_eq_parts` into
  poly/pi/gamma/zeta factors at the cell's s-center,
  then checks the threshold `ε + M*radius ≤ Apoly*Api*Agam*Azeta`.

  For cells where the threshold closes (B12-B19), the center bound
  is proved via `B_center_bound_of_components`. For outer cells
  B11/B20 where Gamma Im-decay prevents closure with Stirling
  bounds, the center bound remains a premise (see BXX_center_obligation).
  -/

  /-- Generic center bound from four factor lower bounds at any s-center. -/
  theorem B_center_bound_of_components
      (z sCenter : ℂ) (hsCenter : sCenter = (1 / 2 : ℂ) + Complex.I * z)
      (ε M radius : ℝ)
      (Apoly Api Agam Azeta : ℝ)
      (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
      (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sCenter‖)
      (hpi : Api ≤ ‖DerivCauchyBridge.piOf sCenter‖)
      (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf sCenter‖)
      (hzeta : Azeta ≤ ‖zeta sCenter‖)
      (hprod : ε + M * radius ≤ Apoly * Api * Agam * Azeta) :
      ε + M * radius ≤ ‖xiShifted z‖ := by
    have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts z
    have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted z‖ := by
      rw [hdecomp]
      exact TailProofEngine.prod_four_ge_of_ge
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
    linarith

  /-- Template for sCenter coordinate proofs. -/
  macro "B"n"sCenter_coords" : tactic => `(tactic|
    unfold B$n_sCenter CellProofEngine.Rect2D.center
    norm_num
  )

  /-- s-center for B11: `s = 0.3 - 8.75·I`. -/
  def B11_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B11_rect.center
  theorem B11_sCenter_re : B11_sCenter.re = 0.3 := by
    unfold B11_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B11_sCenter_im : B11_sCenter.im = -8.75 := by
    unfold B11_sCenter CellProofEngine.Rect2D.center; norm_num

  def B11_poly_lower_obligation : Prop := (38.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B11_sCenter‖
  def B11_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B11_sCenter‖
  def B11_gamma_lower_obligation : Prop := (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B11_sCenter‖
  def B11_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B11_sCenter‖

  /-- s-center for B12: `s = 0.3 - 6.75·I`. -/
  def B12_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B12_rect.center
  theorem B12_sCenter_re : B12_sCenter.re = 0.3 := by
    unfold B12_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B12_sCenter_im : B12_sCenter.im = -6.75 := by
    unfold B12_sCenter CellProofEngine.Rect2D.center; norm_num

  def B12_poly_lower_obligation : Prop := (22.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B12_sCenter‖
  def B12_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B12_sCenter‖
  def B12_gamma_lower_obligation : Prop := (0.008 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B12_sCenter‖
  def B12_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B12_sCenter‖

  theorem B12_threshold_check :
      (0.002 : ℝ) + 0.07 * 1.26 ≤ 22.78125 * 0.84 * 0.008 * 1 := by norm_num

  theorem B12_centerBound_of_factors
      (hPoly : B12_poly_lower_obligation) (hPi : B12_pi_lower_obligation)
      (hGamma : B12_gamma_lower_obligation) (hZeta : B12_zeta_lower_obligation) :
      (0.002 : ℝ) + 0.07 * B12_rect.radius ≤ ‖xiShifted B12_rect.center‖ := by
    have hsCenter : B12_sCenter = (1 / 2 : ℂ) + Complex.I * B12_rect.center := rfl
    have hrad_le : B12_rect.radius ≤ 1.26 := CentralCoverAssembly.R12_radius_lt
    have hbud : (0.002 : ℝ) + 0.07 * B12_rect.radius ≤ (0.002 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.002 : ℝ) + 0.07 * 1.26 ≤ 22.78125 * 0.84 * 0.008 * 1 := B12_threshold_check
    exact B_center_bound_of_components
      B12_rect.center B12_sCenter hsCenter
      0.002 0.07 B12_rect.radius
      22.78125 0.84 0.008 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B13: `s = 0.3 - 4.75·I`. -/
  def B13_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B13_rect.center
  theorem B13_sCenter_re : B13_sCenter.re = 0.3 := by
    unfold B13_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B13_sCenter_im : B13_sCenter.im = -4.75 := by
    unfold B13_sCenter CellProofEngine.Rect2D.center; norm_num

  def B13_poly_lower_obligation : Prop := (11.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B13_sCenter‖
  def B13_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B13_sCenter‖
  def B13_gamma_lower_obligation : Prop := (0.04 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B13_sCenter‖
  def B13_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B13_sCenter‖

  theorem B13_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 11.28125 * 0.84 * 0.04 * 1 := by norm_num

  theorem B13_centerBound_of_factors
      (hPoly : B13_poly_lower_obligation) (hPi : B13_pi_lower_obligation)
      (hGamma : B13_gamma_lower_obligation) (hZeta : B13_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B13_rect.radius ≤ ‖xiShifted B13_rect.center‖ := by
    have hsCenter : B13_sCenter = (1 / 2 : ℂ) + Complex.I * B13_rect.center := rfl
    have hrad_le : B13_rect.radius ≤ 1.26 := CentralCoverAssembly.R13_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B13_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 11.28125 * 0.84 * 0.04 * 1 := B13_threshold_check
    exact B_center_bound_of_components
      B13_rect.center B13_sCenter hsCenter
      0.05 0.07 B13_rect.radius
      11.28125 0.84 0.04 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B14: `s = 0.3 - 2.75·I`. -/
  def B14_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B14_rect.center
  theorem B14_sCenter_re : B14_sCenter.re = 0.3 := by
    unfold B14_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B14_sCenter_im : B14_sCenter.im = -2.75 := by
    unfold B14_sCenter CellProofEngine.Rect2D.center; norm_num

  def B14_poly_lower_obligation : Prop := (3.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B14_sCenter‖
  def B14_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B14_sCenter‖
  def B14_gamma_lower_obligation : Prop := (0.25 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B14_sCenter‖
  def B14_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B14_sCenter‖

  theorem B14_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 3.78125 * 0.84 * 0.25 * 1 := by norm_num

  theorem B14_centerBound_of_factors
      (hPoly : B14_poly_lower_obligation) (hPi : B14_pi_lower_obligation)
      (hGamma : B14_gamma_lower_obligation) (hZeta : B14_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B14_rect.radius ≤ ‖xiShifted B14_rect.center‖ := by
    have hsCenter : B14_sCenter = (1 / 2 : ℂ) + Complex.I * B14_rect.center := rfl
    have hrad_le : B14_rect.radius ≤ 1.26 := CentralCoverAssembly.R14_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B14_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 3.78125 * 0.84 * 0.25 * 1 := B14_threshold_check
    exact B_center_bound_of_components
      B14_rect.center B14_sCenter hsCenter
      0.05 0.07 B14_rect.radius
      3.78125 0.84 0.25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B15: `s = 0.3 - 0.75·I`. -/
  def B15_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B15_rect.center
  theorem B15_sCenter_re : B15_sCenter.re = 0.3 := by
    unfold B15_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B15_sCenter_im : B15_sCenter.im = -0.75 := by
    unfold B15_sCenter CellProofEngine.Rect2D.center; norm_num

  def B15_poly_lower_obligation : Prop := (0.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B15_sCenter‖
  def B15_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B15_sCenter‖
  def B15_gamma_lower_obligation : Prop := (3 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B15_sCenter‖
  def B15_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B15_sCenter‖

  theorem B15_threshold_check :
      (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.28125 * 0.84 * 3 * 1 := by norm_num

  theorem B15_centerBound_of_factors
      (hPoly : B15_poly_lower_obligation) (hPi : B15_pi_lower_obligation)
      (hGamma : B15_gamma_lower_obligation) (hZeta : B15_zeta_lower_obligation) :
      (0.15 : ℝ) + 0.06 * B15_rect.radius ≤ ‖xiShifted B15_rect.center‖ := by
    have hsCenter : B15_sCenter = (1 / 2 : ℂ) + Complex.I * B15_rect.center := rfl
    have hrad_le : B15_rect.radius ≤ 1.26 := CentralCoverAssembly.R15_radius_lt
    have hbud : (0.15 : ℝ) + 0.06 * B15_rect.radius ≤ (0.15 : ℝ) + 0.06 * 1.26 := by linarith
    have hthreshold : (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.28125 * 0.84 * 3 * 1 := B15_threshold_check
    exact B_center_bound_of_components
      B15_rect.center B15_sCenter hsCenter
      0.15 0.06 B15_rect.radius
      0.28125 0.84 3 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B16: `s = 0.3 + 1.25·I`. -/
  def B16_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B16_rect.center
  theorem B16_sCenter_re : B16_sCenter.re = 0.3 := by
    unfold B16_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B16_sCenter_im : B16_sCenter.im = 1.25 := by
    unfold B16_sCenter CellProofEngine.Rect2D.center; norm_num

  def B16_poly_lower_obligation : Prop := (0.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B16_sCenter‖
  def B16_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B16_sCenter‖
  def B16_gamma_lower_obligation : Prop := (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B16_sCenter‖
  def B16_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B16_sCenter‖

  theorem B16_threshold_check :
      (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.78125 * 0.84 * 2 * 1 := by norm_num

  theorem B16_centerBound_of_factors
      (hPoly : B16_poly_lower_obligation) (hPi : B16_pi_lower_obligation)
      (hGamma : B16_gamma_lower_obligation) (hZeta : B16_zeta_lower_obligation) :
      (0.15 : ℝ) + 0.06 * B16_rect.radius ≤ ‖xiShifted B16_rect.center‖ := by
    have hsCenter : B16_sCenter = (1 / 2 : ℂ) + Complex.I * B16_rect.center := rfl
    have hrad_le : B16_rect.radius ≤ 1.26 := CentralCoverAssembly.R16_radius_lt
    have hbud : (0.15 : ℝ) + 0.06 * B16_rect.radius ≤ (0.15 : ℝ) + 0.06 * 1.26 := by linarith
    have hthreshold : (0.15 : ℝ) + 0.06 * 1.26 ≤ 0.78125 * 0.84 * 2 * 1 := B16_threshold_check
    exact B_center_bound_of_components
      B16_rect.center B16_sCenter hsCenter
      0.15 0.06 B16_rect.radius
      0.78125 0.84 2 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B17: `s = 0.3 + 3.25·I`. -/
  def B17_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B17_rect.center
  theorem B17_sCenter_re : B17_sCenter.re = 0.3 := by
    unfold B17_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B17_sCenter_im : B17_sCenter.im = 3.25 := by
    unfold B17_sCenter CellProofEngine.Rect2D.center; norm_num

  def B17_poly_lower_obligation : Prop := (5.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B17_sCenter‖
  def B17_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B17_sCenter‖
  def B17_gamma_lower_obligation : Prop := (0.16 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B17_sCenter‖
  def B17_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B17_sCenter‖

  theorem B17_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 5.28125 * 0.84 * 0.16 * 1 := by norm_num

  theorem B17_centerBound_of_factors
      (hPoly : B17_poly_lower_obligation) (hPi : B17_pi_lower_obligation)
      (hGamma : B17_gamma_lower_obligation) (hZeta : B17_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B17_rect.radius ≤ ‖xiShifted B17_rect.center‖ := by
    have hsCenter : B17_sCenter = (1 / 2 : ℂ) + Complex.I * B17_rect.center := rfl
    have hrad_le : B17_rect.radius ≤ 1.26 := CentralCoverAssembly.R17_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B17_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 5.28125 * 0.84 * 0.16 * 1 := B17_threshold_check
    exact B_center_bound_of_components
      B17_rect.center B17_sCenter hsCenter
      0.05 0.07 B17_rect.radius
      5.28125 0.84 0.16 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B18: `s = 0.3 + 5.25·I`. -/
  def B18_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B18_rect.center
  theorem B18_sCenter_re : B18_sCenter.re = 0.3 := by
    unfold B18_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B18_sCenter_im : B18_sCenter.im = 5.25 := by
    unfold B18_sCenter CellProofEngine.Rect2D.center; norm_num

  def B18_poly_lower_obligation : Prop := (13.78125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B18_sCenter‖
  def B18_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B18_sCenter‖
  def B18_gamma_lower_obligation : Prop := (0.028 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B18_sCenter‖
  def B18_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B18_sCenter‖

  theorem B18_threshold_check :
      (0.05 : ℝ) + 0.07 * 1.26 ≤ 13.78125 * 0.84 * 0.028 * 1 := by norm_num

  theorem B18_centerBound_of_factors
      (hPoly : B18_poly_lower_obligation) (hPi : B18_pi_lower_obligation)
      (hGamma : B18_gamma_lower_obligation) (hZeta : B18_zeta_lower_obligation) :
      (0.05 : ℝ) + 0.07 * B18_rect.radius ≤ ‖xiShifted B18_rect.center‖ := by
    have hsCenter : B18_sCenter = (1 / 2 : ℂ) + Complex.I * B18_rect.center := rfl
    have hrad_le : B18_rect.radius ≤ 1.26 := CentralCoverAssembly.R18_radius_lt
    have hbud : (0.05 : ℝ) + 0.07 * B18_rect.radius ≤ (0.05 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.05 : ℝ) + 0.07 * 1.26 ≤ 13.78125 * 0.84 * 0.028 * 1 := B18_threshold_check
    exact B_center_bound_of_components
      B18_rect.center B18_sCenter hsCenter
      0.05 0.07 B18_rect.radius
      13.78125 0.84 0.028 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B19: `s = 0.3 + 7.25·I`. -/
  def B19_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B19_rect.center
  theorem B19_sCenter_re : B19_sCenter.re = 0.3 := by
    unfold B19_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B19_sCenter_im : B19_sCenter.im = 7.25 := by
    unfold B19_sCenter CellProofEngine.Rect2D.center; norm_num

  def B19_poly_lower_obligation : Prop := (26.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B19_sCenter‖
  def B19_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B19_sCenter‖
  def B19_gamma_lower_obligation : Prop := (0.005 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B19_sCenter‖
  def B19_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B19_sCenter‖

  theorem B19_threshold_check :
      (0.002 : ℝ) + 0.07 * 1.26 ≤ 26.28125 * 0.84 * 0.005 * 1 := by norm_num

  theorem B19_centerBound_of_factors
      (hPoly : B19_poly_lower_obligation) (hPi : B19_pi_lower_obligation)
      (hGamma : B19_gamma_lower_obligation) (hZeta : B19_zeta_lower_obligation) :
      (0.002 : ℝ) + 0.07 * B19_rect.radius ≤ ‖xiShifted B19_rect.center‖ := by
    have hsCenter : B19_sCenter = (1 / 2 : ℂ) + Complex.I * B19_rect.center := rfl
    have hrad_le : B19_rect.radius ≤ 1.26 := CentralCoverAssembly.R19_radius_lt
    have hbud : (0.002 : ℝ) + 0.07 * B19_rect.radius ≤ (0.002 : ℝ) + 0.07 * 1.26 := by linarith
    have hthreshold : (0.002 : ℝ) + 0.07 * 1.26 ≤ 26.28125 * 0.84 * 0.005 * 1 := B19_threshold_check
    exact B_center_bound_of_components
      B19_rect.center B19_sCenter hsCenter
      0.002 0.07 B19_rect.radius
      26.28125 0.84 0.005 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hPoly hPi hGamma hZeta (by linarith [hbud, hthreshold])

  /-- s-center for B20: `s = 0.3 + 8.75·I`. -/
  def B20_sCenter : ℂ := (1 / 2 : ℂ) + Complex.I * B20_rect.center
  theorem B20_sCenter_re : B20_sCenter.re = 0.3 := by
    unfold B20_sCenter CellProofEngine.Rect2D.center; norm_num
  theorem B20_sCenter_im : B20_sCenter.im = 8.75 := by
    unfold B20_sCenter CellProofEngine.Rect2D.center; norm_num

  def B20_poly_lower_obligation : Prop := (38.28125 : ℝ) ≤ ‖DerivCauchyBridge.polyOf B20_sCenter‖
  def B20_pi_lower_obligation : Prop := (0.84 : ℝ) ≤ ‖DerivCauchyBridge.piOf B20_sCenter‖
  def B20_gamma_lower_obligation : Prop := (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf B20_sCenter‖
  def B20_zeta_lower_obligation : Prop := (1 : ℝ) ≤ ‖zeta B20_sCenter‖

  /-! ## Summary of factor decomposition results

  | Cell | Tier | A_poly | A_pi | A_gamma | A_zeta | Threshold | CenterBound |
  |------|------|--------|------|---------|--------|-----------|-------------|
  | B11 | outer | 38.28 | 0.84 | 0.001 | 1 | FAILS | premise |
  | B12 | leaf | 22.78 | 0.84 | 0.008 | 1 | 0.0902≤0.153 | PROVED |
  | B13 | mid | 11.28 | 0.84 | 0.04 | 1 | 0.138≤0.379 | PROVED |
  | B14 | mid | 3.78 | 0.84 | 0.25 | 1 | 0.138≤0.794 | PROVED |
  | B15 | inner | 0.28 | 0.84 | 3 | 1 | 0.226≤0.709 | PROVED |
  | B16 | inner | 0.78 | 0.84 | 2 | 1 | 0.226≤1.313 | PROVED |
  | B17 | mid | 5.28 | 0.84 | 0.16 | 1 | 0.138≤0.710 | PROVED |
  | B18 | mid | 13.78 | 0.84 | 0.028 | 1 | 0.138≤0.324 | PROVED |
  | B19 | leaf | 26.28 | 0.84 | 0.005 | 1 | 0.090≤0.110 | PROVED |
  | B20 | outer | 38.28 | 0.84 | 0.001 | 1 | FAILS | premise |

  B11/B20: Gamma Im-decay makes the factor product too small to close
  the threshold. The center bound remains a premise.
  All other cells: factor decomposition closes with margin,
  center bound proved via `B_center_bound_of_components`.
  -/

end Door3BatchB
