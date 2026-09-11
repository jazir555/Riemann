import Mathlib
import central_cover_assembly

/-!
# Door 3 bottom-row batch E (`door3_cells_batchE.lean`, NEW file)

WRITE-ONLY replication task (no build; patch phase later). This file owns
EXCLUSIVELY the SIX unclaimed bottom-row main-band leaves plus the off-grid
extra: `R01` (off-grid, `(-7.5,-5) ∉ fineGridX`, membership-free H-leaf) and
`R05–R10` (bottom-row central columns). COUNT NOTE: the brief says "6
UNCLAIMED" but lists `R01 + R05–R10` = 7 leaves (`R05,R06,R07,R08,R09,R10` is
six alone); all seven are proved here so no listed leaf is dropped. Per
inventory (`central_cover_assembly.lean`: `innerGridY =
[(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]` at `:372`; `fineGridX` 10 columns
width exactly `2.5` at `:954`; `gridFine` 40 cells at `:1002`; bottom-row block
`R00–R10` at `:1380`, `BottomRowObligations` at `:2351`,
`bottomRow_H_of_obligations` at `:2359`, `bottom_row_covered` at `:2394`):
the bottom row is `y = (0.01, 0.2)`, `dy = 0.095`, centers `y = 0.105`,
s-centers `Re = 0.395`. Batch A already owns `R00/R03/R04`, `R02` is done
elsewhere; nothing here overlaps sibling batches A–D.

## CLAIMED CELLS (7 cells, all `y = (0.01, 0.2)`, `dy = 0.095`, center `y = 0.105`)

| cell | `x`         | z-center          | s-center (`(0.5-y)+x·I`) | tier `(ε,M)` | budget `ε+M*1.26` |
|------|-------------|-------------------|--------------------------|--------------|-------------------|
| R01  | `(-7.5, -5)`| `-6.25 + 0.105·I` | `0.395 - 6.25·I`         | `(0.05,0.07)` mid   | `0.1382` |
| R05  | `(-2, 0.5)` | `-0.75 + 0.105·I` | `0.395 - 0.75·I`         | `(0.15,0.06)` inner | `0.2256` |
| R06  | `(0, 2.5)`  | `1.25 + 0.105·I`  | `0.395 + 1.25·I`         | `(0.15,0.06)` inner | `0.2256` |
| R07  | `(2, 4.5)`  | `3.25 + 0.105·I`  | `0.395 + 3.25·I`         | `(0.05,0.07)` mid   | `0.1382` |
| R08  | `(4, 6.5)`  | `5.25 + 0.105·I`  | `0.395 + 5.25·I`         | `(0.05,0.07)` mid   | `0.1382` |
| R09  | `(6, 8.5)`  | `7.25 + 0.105·I`  | `0.395 + 7.25·I`         | `(0.002,0.07)` leaf*| `0.0902` |
| R10  | `(7.5, 10)` | `8.75 + 0.105·I`  | `0.395 + 8.75·I`         | `(0.002,0.05)` outer| `0.065`  |

`*` DISCREPANCY (read-only finding, flagged, same class as batch-B R12/R19 and
batch-D R22/R29): the section header for R09 says "outer tier `(0.002,0.05)`"
but the LEAF DEF (`R09_leaf_obligations` at `:2072`) uses `M = 0.07`. This
file follows the LEAF DEF (authoritative for obligations).

All 7 cells: `dx = 1.25`, `dy = 0.095`,
`radius = √(1.25² + 0.095²) < 1.26` (`sample_cell_radius_bound` at `:421`).

## RECON RECORD (read-only, verified before writing; no file touched)

CITED (all verified present in `central_cover_assembly.lean`):
* `CellFencingHypotheses` (`:504`): fields `ε_pos`, `deriv_bound`, `center_bound`.
* `fine_eps_outer_pos` (`:1032`), `fine_eps_mid_pos` (`:1033`),
  `fine_eps_inner_pos` (`:1034`) — tier `ε`-positivity per cell tier.
* `sample_cell_radius_bound` (`:421`) — bottom-row `(1.25,0.095)` radius cap.
* Per-cell banked `R01`/`R05`–`R10`: rect defs, `RXX_x0/x1/y0/y1`,
  `RXX_strip_lo/hi`, `RXX_dx_eq/dy_eq/radius_eq`, `RXX_radius_lt`,
  `RXX_leaf_obligations`, `RXX_fencing_of_bounds`, `RXX_H_instance`;
  plus `RXX_mem_gridFine` for `R05`–`R10` (R01 has none: `(-7.5,-5) ∉
  fineGridX`, DATA NOTE at `:1244`; its `R01_H_instance` at `:1326` is
  membership-free, `hc_eq` only — replicated here).
* `lowerBoundRect_of_fencingHypotheses_strip` (`:941`),
  `zeroFreeRect_of_rect_center_bound_strip` (`:931`),
  `xi_rect_lower_bound_of_center_bound_strip` (`:882`).
* `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`),
  `DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem` (`:6213`),
  `DerivCauchyBridge.norm_xiShifted_eq_parts` (`:6350`),
  `DerivCauchyBridge.polyOf/piOf/gammaOf` (`:6328/:6331/:6334`).
* `TailProofEngine.prod_four_ge_of_ge` (via `central_cover_assembly` import).
* Row assembly: `BottomRowObligations` (`:2351`),
  `bottomRow_H_of_obligations` (`:2359`), `bottom_row_covered` (`:2394`).
ABSENT (verified by grep; NO banked pilots/discs for these s-centers —
contrast the R02 lane): no `R01`/`R05`–`R10` pilots, no bottom-row Gamma
discs, no bottom-row zeta uppers. Hence every factor floor below is an
explicit premise (honest wall).
NOT cited (cycle-safety): `interval_arith`, `riemann_hypothesis_newsection`.
Imports stay `Mathlib` + `central_cover_assembly` only.

## PER-CELL STATUS (all 7: CLOSED-conditional on 6 explicit premises each)

Each cell replicates the 12-step template of `door3_first_cell.lean:349` in
its full batch-D form: rect alias → coords → geometry → s-center →
poly/pi/gamma/zeta floors (explicit `Prop`s, TRUE-value comments) → tier-M →
ball-sup → `norm_num` budget threshold → Cauchy deriv route → fencing triple
→ H-leaf-shaped conclusion. No cell fails its threshold check by `norm_num`,
so no FEASIBILITY-NEGATIVE record is needed (cf. batch-D `R21`/`R30`
`BD_RXX_threshold_negative` pattern — not triggered here):
* R01: threshold `0.1382 ≤ 18*0.7*0.01*1.2 = 0.1512` PROVED (margin 1.09x).
* R05: threshold `0.2256 ≤ 0.35*0.7*1.5*1.0 = 0.3675` PROVED (margin 1.63x).
* R06: threshold `0.2256 ≤ 0.8*0.7*1.0*1.0 = 0.56` PROVED (margin 2.48x).
* R07: threshold `0.1382 ≤ 5.0*0.7*0.1*1.0 = 0.35` PROVED (margin 2.53x).
* R08: threshold `0.1382 ≤ 12*0.7*0.02*1.0 = 0.168` PROVED (margin 1.22x).
* R09: threshold `0.0902 ≤ 25*0.7*0.0045*1.3 = 0.102375` PROVED (margin 1.14x).
* R10: threshold `0.065 ≤ 34*0.7*0.0015*1.9 = 0.06783` PROVED (margin 1.04x;
  mirrors batch-A `BA00` floors at the mirror `Im ∓ 8.75` scale).
-/

noncomputable section

namespace Door3BatchE

/-! ## Shared tier budgets + Cauchy closed form (PROVED, no premises) -/

/-- Mid-tier budget `0.05 + 0.07 * 1.26 = 0.1382` (R01, R07, R08). -/
theorem E_budget_mid :
    (0.05 : ℝ) + 0.07 * 1.26 = 0.1382 := by norm_num

/-- Inner-tier budget `0.15 + 0.06 * 1.26 = 0.2256` (R05, R06). -/
theorem E_budget_inner :
    (0.15 : ℝ) + 0.06 * 1.26 = 0.2256 := by norm_num

/-- Leaf-mismatch-tier budget `0.002 + 0.07 * 1.26 = 0.0902` (R09 leaf `M = 0.07`). -/
theorem E_budget_outer07 :
    (0.002 : ℝ) + 0.07 * 1.26 = 0.0902 := by norm_num

/-- Outer-tier budget `0.002 + 0.05 * 1.26 = 0.065` (R10). -/
theorem E_budget_outer05 :
    (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

/-- Cauchy closed form `16800 / 0.25 = 67200` (all cells, `r = 0.25`). -/
theorem E_cauchy_closedForm : (16800 : ℝ) / 0.25 = 67200 := by norm_num

/-- Honest gaps: every tier `M` here is far below the Cauchy `M = 67200`. -/
theorem E_cauchy_tier_mismatch05 : (0.05 : ℝ) < 67200 := by norm_num
theorem E_cauchy_tier_mismatch07 : (0.07 : ℝ) < 67200 := by norm_num
theorem E_cauchy_tier_mismatch06 : (0.06 : ℝ) < 67200 := by norm_num

/-! ## E01 = (-7.5, -5, 0.01, 0.2), mid tier `(0.05, 0.07)`: CLOSED-CONDITIONAL

Off-grid extra: `(-7.5,-5) ∉ fineGridX` (DATA NOTE at `:1244`), so no
`mem_gridFine` lemma exists or is claimed; the H-leaf below is
membership-free (`hc_eq` only), exactly like banked `R01_H_instance`. -/

/-- Rect alias so every banked R01 lemma applies definitionally. -/
def BE_rect_R01 : CellProofEngine.Rect2D := CentralCoverAssembly.R01

theorem BE_R01_x0 : BE_rect_R01.x0 = -7.5 := rfl
theorem BE_R01_x1 : BE_rect_R01.x1 = -5 := rfl
theorem BE_R01_y0 : BE_rect_R01.y0 = 0.01 := rfl
theorem BE_R01_y1 : BE_rect_R01.y1 = 0.2 := rfl

theorem BE_R01_width_eq : BE_rect_R01.x1 - BE_rect_R01.x0 = 2.5 := by
  rw [BE_R01_x0, BE_R01_x1]; norm_num

theorem BE_R01_strip_lo : -(1 / 2 : ℝ) < BE_rect_R01.y0 :=
  CentralCoverAssembly.R01_strip_lo
theorem BE_R01_strip_hi : BE_rect_R01.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R01_strip_hi

theorem BE_R01_dx : BE_rect_R01.dx = 1.25 :=
  CentralCoverAssembly.R01_dx_eq
theorem BE_R01_dy : BE_rect_R01.dy = 0.095 :=
  CentralCoverAssembly.R01_dy_eq
theorem BE_R01_radius_eq :
    BE_rect_R01.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R01_radius_eq
theorem BE_R01_radius_lt : BE_rect_R01.radius < 1.26 := by
  rw [BE_R01_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R01_strip_of_mem {w : ℂ} (hw : BE_rect_R01.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R01_y0] at hy0
  rw [BE_R01_y1] at hy1
  constructor <;> linarith

/-- R01 s-center `s = 1/2 + I*center` (`z = -6.25 + 0.105*I`, so
`s = 0.395 - 6.25*I`). -/
noncomputable def BE_sC01 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R01.center

/-- Poly lower at R01 s-center. TRUE `≈ 19.65` (`|s|≈6.26`, `|s-1|≈6.28`;
floor 18, headroom 1.09x). -/
def BE_polyLower_R01 : Prop :=
  (18 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC01‖

/-- Pi lower at R01 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R01 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC01‖

/-- Gamma lower at R01 s-center. TRUE `≈ 0.013` (Stirling at
`s/2 = 0.1975 + 3.125*I`; floor 0.01, headroom 1.3x). -/
def BE_gammaLower_R01 : Prop :=
  (0.01 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC01‖

/-- Zeta lower at R01 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.2
follows the batch-A `1.0–1.9` precedent scale). -/
def BE_zetaLower_R01 : Prop :=
  (1.2 : ℝ) ≤ ‖zeta BE_sC01‖

/-- Tier deriv bound (matches `R01_leaf_obligations` shape). TRUE unknown. -/
def BE_derivTier_R01 : Prop :=
  ∀ w, BE_rect_R01.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

/-- Closed-ball sup for the Cauchy route (C=16800, r=0.25 pattern). -/
def BE_ballSup_R01 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R01.center (BE_rect_R01.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `18*0.7*0.01*1.2 = 0.1512 ≥ 0.05+0.07*1.26 = 0.1382`. -/
theorem BE_R01_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (18 : ℝ) * 0.7 * 0.01 * 1.2 := by norm_num

theorem BE_R01_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R01_deriv_of_ballSup (hBall : BE_ballSup_R01) :
    ∀ w, BE_rect_R01.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R01 0.25 16800 (by norm_num) (fun w hw => BE_R01_strip_of_mem hw) hBall

theorem BE_R01_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R01_sphere_of_ballSup (hBall : BE_ballSup_R01)
    (w : ℂ) (hw : BE_rect_R01.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R01 0.25 w hw hz)

theorem BE_R01_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC01‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC01‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC01‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC01‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R01.center = BE_sC01 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R01.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R01.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BE_rect_R01.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R01_radius_lt) (by norm_num)
  linarith

theorem BE_R01_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R01 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BE_R01_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R01 0.05 0.07 BE_R01_strip_lo BE_R01_strip_hi
    (BE_R01_fencing_of_premises hC hD)

noncomputable def BE_R01_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R01 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BE_R01_strip_lo BE_R01_strip_hi hD hC

theorem BE_R01_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01) {z : ℂ}
    (hx0 : BE_rect_R01.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R01.x1)
    (hy0 : BE_rect_R01.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R01.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R01 0.05 0.07 BE_R01_strip_lo BE_R01_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BE_R01_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01)
    (c : ℝ × ℝ × ℝ × ℝ)
    (hc_eq : c = (-7.5, -5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R01, 0.05, 0.07, rfl, rfl, rfl, rfl, BE_R01_strip_lo, BE_R01_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BE_R01_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R01.radius ≤ ‖xiShifted BE_rect_R01.center‖)
    (hD : BE_derivTier_R01) :
    CentralCoverAssembly.R01_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E05 = (-2, 0.5, 0.01, 0.2), inner tier `(0.15, 0.06)`: CLOSED-CONDITIONAL -/

def BE_rect_R05 : CellProofEngine.Rect2D := CentralCoverAssembly.R05

theorem BE_R05_x0 : BE_rect_R05.x0 = -2 := rfl
theorem BE_R05_x1 : BE_rect_R05.x1 = 0.5 := rfl
theorem BE_R05_y0 : BE_rect_R05.y0 = 0.01 := rfl
theorem BE_R05_y1 : BE_rect_R05.y1 = 0.2 := rfl

theorem BE_R05_width_eq : BE_rect_R05.x1 - BE_rect_R05.x0 = 2.5 := by
  rw [BE_R05_x0, BE_R05_x1]; norm_num

theorem BE_R05_strip_lo : -(1 / 2 : ℝ) < BE_rect_R05.y0 :=
  CentralCoverAssembly.R05_strip_lo
theorem BE_R05_strip_hi : BE_rect_R05.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R05_strip_hi

theorem BE_R05_dx : BE_rect_R05.dx = 1.25 :=
  CentralCoverAssembly.R05_dx_eq
theorem BE_R05_dy : BE_rect_R05.dy = 0.095 :=
  CentralCoverAssembly.R05_dy_eq
theorem BE_R05_radius_eq :
    BE_rect_R05.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R05_radius_eq
theorem BE_R05_radius_lt : BE_rect_R05.radius < 1.26 := by
  rw [BE_R05_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R05_strip_of_mem {w : ℂ} (hw : BE_rect_R05.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R05_y0] at hy0
  rw [BE_R05_y1] at hy1
  constructor <;> linarith

theorem BE_R05_mem_gridFine : (-2, 0.5, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R05_mem_gridFine

/-- R05 s-center `s = 1/2 + I*center` (`z = -0.75 + 0.105*I`, so
`s = 0.395 - 0.75*I`). -/
noncomputable def BE_sC05 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R05.center

/-- Poly lower at R05 s-center. TRUE `≈ 0.408` (`|s|≈0.848`, `|s-1|≈0.964`;
floor 0.35, headroom 1.17x). -/
def BE_polyLower_R05 : Prop :=
  (0.35 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC05‖

/-- Pi lower at R05 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R05 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC05‖

/-- Gamma lower at R05 s-center. TRUE `≈ 4.4` (`s/2 = 0.1975 - 0.375*I`,
near-real-axis Gamma; floor 1.5, headroom ~2.9x). -/
def BE_gammaLower_R05 : Prop :=
  (1.5 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC05‖

/-- Zeta lower at R05 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.0
follows the batch-A `BA04` precedent at the neighboring `Im -2.75` scale). -/
def BE_zetaLower_R05 : Prop :=
  (1 : ℝ) ≤ ‖zeta BE_sC05‖

def BE_derivTier_R05 : Prop :=
  ∀ w, BE_rect_R05.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BE_ballSup_R05 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R05.center (BE_rect_R05.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `0.35*0.7*1.5*1.0 = 0.3675 ≥ 0.15+0.06*1.26 = 0.2256`. -/
theorem BE_R05_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.35 : ℝ) * 0.7 * 1.5 * 1 := by norm_num

theorem BE_R05_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R05_deriv_of_ballSup (hBall : BE_ballSup_R05) :
    ∀ w, BE_rect_R05.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R05 0.25 16800 (by norm_num) (fun w hw => BE_R05_strip_of_mem hw) hBall

theorem BE_R05_cauchy_tier_mismatch :
    (0.06 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R05_sphere_of_ballSup (hBall : BE_ballSup_R05)
    (w : ℂ) (hw : BE_rect_R05.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R05 0.25 w hw hz)

theorem BE_R05_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC05‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC05‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC05‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC05‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R05.center = BE_sC05 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R05.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R05.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BE_rect_R05.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R05_radius_lt) (by norm_num)
  linarith

theorem BE_R05_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R05 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BE_R05_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R05 0.15 0.06 BE_R05_strip_lo BE_R05_strip_hi
    (BE_R05_fencing_of_premises hC hD)

noncomputable def BE_R05_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R05 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BE_R05_strip_lo BE_R05_strip_hi hD hC

theorem BE_R05_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05) {z : ℂ}
    (hx0 : BE_rect_R05.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R05.x1)
    (hy0 : BE_rect_R05.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R05.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R05 0.15 0.06 BE_R05_strip_lo BE_R05_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BE_R05_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R05, 0.15, 0.06, rfl, rfl, rfl, rfl, BE_R05_strip_lo, BE_R05_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BE_R05_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R05.radius ≤ ‖xiShifted BE_rect_R05.center‖)
    (hD : BE_derivTier_R05) :
    CentralCoverAssembly.R05_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E06 = (0, 2.5, 0.01, 0.2), inner tier `(0.15, 0.06)`: CLOSED-CONDITIONAL -/

def BE_rect_R06 : CellProofEngine.Rect2D := CentralCoverAssembly.R06

theorem BE_R06_x0 : BE_rect_R06.x0 = 0 := rfl
theorem BE_R06_x1 : BE_rect_R06.x1 = 2.5 := rfl
theorem BE_R06_y0 : BE_rect_R06.y0 = 0.01 := rfl
theorem BE_R06_y1 : BE_rect_R06.y1 = 0.2 := rfl

theorem BE_R06_width_eq : BE_rect_R06.x1 - BE_rect_R06.x0 = 2.5 := by
  rw [BE_R06_x0, BE_R06_x1]; norm_num

theorem BE_R06_strip_lo : -(1 / 2 : ℝ) < BE_rect_R06.y0 :=
  CentralCoverAssembly.R06_strip_lo
theorem BE_R06_strip_hi : BE_rect_R06.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R06_strip_hi

theorem BE_R06_dx : BE_rect_R06.dx = 1.25 :=
  CentralCoverAssembly.R06_dx_eq
theorem BE_R06_dy : BE_rect_R06.dy = 0.095 :=
  CentralCoverAssembly.R06_dy_eq
theorem BE_R06_radius_eq :
    BE_rect_R06.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R06_radius_eq
theorem BE_R06_radius_lt : BE_rect_R06.radius < 1.26 := by
  rw [BE_R06_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R06_strip_of_mem {w : ℂ} (hw : BE_rect_R06.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R06_y0] at hy0
  rw [BE_R06_y1] at hy1
  constructor <;> linarith

theorem BE_R06_mem_gridFine : (0, 2.5, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R06_mem_gridFine

/-- R06 s-center `s = 1/2 + I*center` (`z = 1.25 + 0.105*I`, so
`s = 0.395 + 1.25*I`). -/
noncomputable def BE_sC06 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R06.center

/-- Poly lower at R06 s-center. TRUE `≈ 0.91` (`|s|≈1.311`, `|s-1|≈1.389`;
floor 0.8, headroom 1.14x). -/
def BE_polyLower_R06 : Prop :=
  (0.8 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC06‖

/-- Pi lower at R06 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R06 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC06‖

/-- Gamma lower at R06 s-center. TRUE `≈ 2.5` (`s/2 = 0.1975 + 0.625*I`,
near-axis Gamma; floor 1.0, headroom ~2.5x). -/
def BE_gammaLower_R06 : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC06‖

/-- Zeta lower at R06 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.0
follows the batch-A `BA04` precedent). -/
def BE_zetaLower_R06 : Prop :=
  (1 : ℝ) ≤ ‖zeta BE_sC06‖

def BE_derivTier_R06 : Prop :=
  ∀ w, BE_rect_R06.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)

def BE_ballSup_R06 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R06.center (BE_rect_R06.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `0.8*0.7*1.0*1.0 = 0.56 ≥ 0.15+0.06*1.26 = 0.2256`. -/
theorem BE_R06_threshold_check :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.8 : ℝ) * 0.7 * 1 * 1 := by norm_num

theorem BE_R06_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R06_deriv_of_ballSup (hBall : BE_ballSup_R06) :
    ∀ w, BE_rect_R06.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R06 0.25 16800 (by norm_num) (fun w hw => BE_R06_strip_of_mem hw) hBall

theorem BE_R06_cauchy_tier_mismatch :
    (0.06 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R06_sphere_of_ballSup (hBall : BE_ballSup_R06)
    (w : ℂ) (hw : BE_rect_R06.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R06 0.25 w hw hz)

theorem BE_R06_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC06‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC06‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC06‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC06‖)
    (hThresh : (0.15 : ℝ) + 0.06 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R06.center = BE_sC06 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R06.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R06.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.06 * BE_rect_R06.radius ≤ 0.06 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R06_radius_lt) (by norm_num)
  linarith

theorem BE_R06_fencing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R06 0.15 0.06 :=
  ⟨CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

noncomputable def BE_R06_lowerBound_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R06 0.15 0.06 BE_R06_strip_lo BE_R06_strip_hi
    (BE_R06_fencing_of_premises hC hD)

noncomputable def BE_R06_zeroFree_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R06 0.15 CentralCoverAssembly.fine_eps_inner_pos 0.06
    BE_R06_strip_lo BE_R06_strip_hi hD hC

theorem BE_R06_nonvanishing_of_premises
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06) {z : ℂ}
    (hx0 : BE_rect_R06.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R06.x1)
    (hy0 : BE_rect_R06.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R06.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R06 0.15 0.06 BE_R06_strip_lo BE_R06_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_inner_pos) hle

theorem BE_R06_H_instance
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R06, 0.15, 0.06, rfl, rfl, rfl, rfl, BE_R06_strip_lo, BE_R06_strip_hi,
    CentralCoverAssembly.fine_eps_inner_pos, hD, hC⟩

theorem BE_R06_implies_leaf
    (hC : (0.15 : ℝ) + 0.06 * BE_rect_R06.radius ≤ ‖xiShifted BE_rect_R06.center‖)
    (hD : BE_derivTier_R06) :
    CentralCoverAssembly.R06_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E07 = (2, 4.5, 0.01, 0.2), mid tier `(0.05, 0.07)`: CLOSED-CONDITIONAL -/

def BE_rect_R07 : CellProofEngine.Rect2D := CentralCoverAssembly.R07

theorem BE_R07_x0 : BE_rect_R07.x0 = 2 := rfl
theorem BE_R07_x1 : BE_rect_R07.x1 = 4.5 := rfl
theorem BE_R07_y0 : BE_rect_R07.y0 = 0.01 := rfl
theorem BE_R07_y1 : BE_rect_R07.y1 = 0.2 := rfl

theorem BE_R07_width_eq : BE_rect_R07.x1 - BE_rect_R07.x0 = 2.5 := by
  rw [BE_R07_x0, BE_R07_x1]; norm_num

theorem BE_R07_strip_lo : -(1 / 2 : ℝ) < BE_rect_R07.y0 :=
  CentralCoverAssembly.R07_strip_lo
theorem BE_R07_strip_hi : BE_rect_R07.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R07_strip_hi

theorem BE_R07_dx : BE_rect_R07.dx = 1.25 :=
  CentralCoverAssembly.R07_dx_eq
theorem BE_R07_dy : BE_rect_R07.dy = 0.095 :=
  CentralCoverAssembly.R07_dy_eq
theorem BE_R07_radius_eq :
    BE_rect_R07.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R07_radius_eq
theorem BE_R07_radius_lt : BE_rect_R07.radius < 1.26 := by
  rw [BE_R07_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R07_strip_of_mem {w : ℂ} (hw : BE_rect_R07.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R07_y0] at hy0
  rw [BE_R07_y1] at hy1
  constructor <;> linarith

theorem BE_R07_mem_gridFine : (2, 4.5, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R07_mem_gridFine

/-- R07 s-center `s = 1/2 + I*center` (`z = 3.25 + 0.105*I`, so
`s = 0.395 + 3.25*I`). -/
noncomputable def BE_sC07 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R07.center

/-- Poly lower at R07 s-center. TRUE `≈ 5.41` (`|s|≈3.274`, `|s-1|≈3.306`;
floor 5.0, headroom 1.08x). -/
def BE_polyLower_R07 : Prop :=
  (5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC07‖

/-- Pi lower at R07 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R07 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC07‖

/-- Gamma lower at R07 s-center. TRUE `≈ 0.169` (Stirling at
`s/2 = 0.1975 + 1.625*I`; floor 0.1, headroom 1.69x). -/
def BE_gammaLower_R07 : Prop :=
  (0.1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC07‖

/-- Zeta lower at R07 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.0
follows the batch-A `BA04` precedent). -/
def BE_zetaLower_R07 : Prop :=
  (1 : ℝ) ≤ ‖zeta BE_sC07‖

def BE_derivTier_R07 : Prop :=
  ∀ w, BE_rect_R07.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BE_ballSup_R07 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R07.center (BE_rect_R07.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `5.0*0.7*0.1*1.0 = 0.35 ≥ 0.05+0.07*1.26 = 0.1382`. -/
theorem BE_R07_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (5 : ℝ) * 0.7 * 0.1 * 1 := by norm_num

theorem BE_R07_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R07_deriv_of_ballSup (hBall : BE_ballSup_R07) :
    ∀ w, BE_rect_R07.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R07 0.25 16800 (by norm_num) (fun w hw => BE_R07_strip_of_mem hw) hBall

theorem BE_R07_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R07_sphere_of_ballSup (hBall : BE_ballSup_R07)
    (w : ℂ) (hw : BE_rect_R07.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R07 0.25 w hw hz)

theorem BE_R07_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC07‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC07‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC07‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC07‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R07.center = BE_sC07 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R07.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R07.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BE_rect_R07.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R07_radius_lt) (by norm_num)
  linarith

theorem BE_R07_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R07 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BE_R07_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R07 0.05 0.07 BE_R07_strip_lo BE_R07_strip_hi
    (BE_R07_fencing_of_premises hC hD)

noncomputable def BE_R07_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R07 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BE_R07_strip_lo BE_R07_strip_hi hD hC

theorem BE_R07_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07) {z : ℂ}
    (hx0 : BE_rect_R07.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R07.x1)
    (hy0 : BE_rect_R07.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R07.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R07 0.05 0.07 BE_R07_strip_lo BE_R07_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BE_R07_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R07, 0.05, 0.07, rfl, rfl, rfl, rfl, BE_R07_strip_lo, BE_R07_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BE_R07_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R07.radius ≤ ‖xiShifted BE_rect_R07.center‖)
    (hD : BE_derivTier_R07) :
    CentralCoverAssembly.R07_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E08 = (4, 6.5, 0.01, 0.2), mid tier `(0.05, 0.07)`: CLOSED-CONDITIONAL -/

def BE_rect_R08 : CellProofEngine.Rect2D := CentralCoverAssembly.R08

theorem BE_R08_x0 : BE_rect_R08.x0 = 4 := rfl
theorem BE_R08_x1 : BE_rect_R08.x1 = 6.5 := rfl
theorem BE_R08_y0 : BE_rect_R08.y0 = 0.01 := rfl
theorem BE_R08_y1 : BE_rect_R08.y1 = 0.2 := rfl

theorem BE_R08_width_eq : BE_rect_R08.x1 - BE_rect_R08.x0 = 2.5 := by
  rw [BE_R08_x0, BE_R08_x1]; norm_num

theorem BE_R08_strip_lo : -(1 / 2 : ℝ) < BE_rect_R08.y0 :=
  CentralCoverAssembly.R08_strip_lo
theorem BE_R08_strip_hi : BE_rect_R08.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R08_strip_hi

theorem BE_R08_dx : BE_rect_R08.dx = 1.25 :=
  CentralCoverAssembly.R08_dx_eq
theorem BE_R08_dy : BE_rect_R08.dy = 0.095 :=
  CentralCoverAssembly.R08_dy_eq
theorem BE_R08_radius_eq :
    BE_rect_R08.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R08_radius_eq
theorem BE_R08_radius_lt : BE_rect_R08.radius < 1.26 := by
  rw [BE_R08_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R08_strip_of_mem {w : ℂ} (hw : BE_rect_R08.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R08_y0] at hy0
  rw [BE_R08_y1] at hy1
  constructor <;> linarith

theorem BE_R08_mem_gridFine : (4, 6.5, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R08_mem_gridFine

/-- R08 s-center `s = 1/2 + I*center` (`z = 5.25 + 0.105*I`, so
`s = 0.395 + 5.25*I`). -/
noncomputable def BE_sC08 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R08.center

/-- Poly lower at R08 s-center. TRUE `≈ 13.91` (`|s|≈5.265`, `|s-1|≈5.285`;
floor 12, headroom 1.16x). -/
def BE_polyLower_R08 : Prop :=
  (12 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC08‖

/-- Pi lower at R08 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R08 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC08‖

/-- Gamma lower at R08 s-center. TRUE `≈ 0.03` (Stirling at
`s/2 = 0.1975 + 2.625*I`; floor 0.02, headroom 1.5x). -/
def BE_gammaLower_R08 : Prop :=
  (0.02 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC08‖

/-- Zeta lower at R08 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.0
follows the batch-A `BA04` precedent). -/
def BE_zetaLower_R08 : Prop :=
  (1 : ℝ) ≤ ‖zeta BE_sC08‖

def BE_derivTier_R08 : Prop :=
  ∀ w, BE_rect_R08.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BE_ballSup_R08 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R08.center (BE_rect_R08.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `12*0.7*0.02*1.0 = 0.168 ≥ 0.05+0.07*1.26 = 0.1382`. -/
theorem BE_R08_threshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (12 : ℝ) * 0.7 * 0.02 * 1 := by norm_num

theorem BE_R08_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R08_deriv_of_ballSup (hBall : BE_ballSup_R08) :
    ∀ w, BE_rect_R08.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R08 0.25 16800 (by norm_num) (fun w hw => BE_R08_strip_of_mem hw) hBall

theorem BE_R08_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R08_sphere_of_ballSup (hBall : BE_ballSup_R08)
    (w : ℂ) (hw : BE_rect_R08.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R08 0.25 w hw hz)

theorem BE_R08_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC08‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC08‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC08‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC08‖)
    (hThresh : (0.05 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R08.center = BE_sC08 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R08.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R08.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BE_rect_R08.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R08_radius_lt) (by norm_num)
  linarith

theorem BE_R08_fencing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R08 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

noncomputable def BE_R08_lowerBound_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R08 0.05 0.07 BE_R08_strip_lo BE_R08_strip_hi
    (BE_R08_fencing_of_premises hC hD)

noncomputable def BE_R08_zeroFree_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R08 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BE_R08_strip_lo BE_R08_strip_hi hD hC

theorem BE_R08_nonvanishing_of_premises
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08) {z : ℂ}
    (hx0 : BE_rect_R08.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R08.x1)
    (hy0 : BE_rect_R08.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R08.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R08 0.05 0.07 BE_R08_strip_lo BE_R08_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

theorem BE_R08_H_instance
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R08, 0.05, 0.07, rfl, rfl, rfl, rfl, BE_R08_strip_lo, BE_R08_strip_hi,
    CentralCoverAssembly.fine_eps_mid_pos, hD, hC⟩

theorem BE_R08_implies_leaf
    (hC : (0.05 : ℝ) + 0.07 * BE_rect_R08.radius ≤ ‖xiShifted BE_rect_R08.center‖)
    (hD : BE_derivTier_R08) :
    CentralCoverAssembly.R08_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E09 = (6, 8.5, 0.01, 0.2), leaf tier `(0.002, 0.07)`: CLOSED-CONDITIONAL

Follows the LEAF DEF (`M = 0.07`), not the section header (`M = 0.05`); see
the file-top DISCREPANCY note. -/

def BE_rect_R09 : CellProofEngine.Rect2D := CentralCoverAssembly.R09

theorem BE_R09_x0 : BE_rect_R09.x0 = 6 := rfl
theorem BE_R09_x1 : BE_rect_R09.x1 = 8.5 := rfl
theorem BE_R09_y0 : BE_rect_R09.y0 = 0.01 := rfl
theorem BE_R09_y1 : BE_rect_R09.y1 = 0.2 := rfl

theorem BE_R09_width_eq : BE_rect_R09.x1 - BE_rect_R09.x0 = 2.5 := by
  rw [BE_R09_x0, BE_R09_x1]; norm_num

theorem BE_R09_strip_lo : -(1 / 2 : ℝ) < BE_rect_R09.y0 :=
  CentralCoverAssembly.R09_strip_lo
theorem BE_R09_strip_hi : BE_rect_R09.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R09_strip_hi

theorem BE_R09_dx : BE_rect_R09.dx = 1.25 :=
  CentralCoverAssembly.R09_dx_eq
theorem BE_R09_dy : BE_rect_R09.dy = 0.095 :=
  CentralCoverAssembly.R09_dy_eq
theorem BE_R09_radius_eq :
    BE_rect_R09.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R09_radius_eq
theorem BE_R09_radius_lt : BE_rect_R09.radius < 1.26 := by
  rw [BE_R09_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R09_strip_of_mem {w : ℂ} (hw : BE_rect_R09.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R09_y0] at hy0
  rw [BE_R09_y1] at hy1
  constructor <;> linarith

theorem BE_R09_mem_gridFine : (6, 8.5, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R09_mem_gridFine

/-- R09 s-center `s = 1/2 + I*center` (`z = 7.25 + 0.105*I`, so
`s = 0.395 + 7.25*I`). -/
noncomputable def BE_sC09 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R09.center

/-- Poly lower at R09 s-center. TRUE `≈ 26.42` (`|s|≈7.261`, `|s-1|≈7.276`;
floor 25, headroom 1.06x). -/
def BE_polyLower_R09 : Prop :=
  (25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC09‖

/-- Pi lower at R09 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x). -/
def BE_piLower_R09 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC09‖

/-- Gamma lower at R09 s-center. TRUE `≈ 0.0057` (Stirling at
`s/2 = 0.1975 + 3.625*I`; floor 0.0045, headroom 1.27x). -/
def BE_gammaLower_R09 : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC09‖

/-- Zeta lower at R09 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.3
follows the batch-A `1.0–1.9` precedent scale). -/
def BE_zetaLower_R09 : Prop :=
  (1.3 : ℝ) ≤ ‖zeta BE_sC09‖

def BE_derivTier_R09 : Prop :=
  ∀ w, BE_rect_R09.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

def BE_ballSup_R09 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R09.center (BE_rect_R09.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `25*0.7*0.0045*1.3 = 0.102375 ≥ 0.002+0.07*1.26 = 0.0902`. -/
theorem BE_R09_threshold_check :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ (25 : ℝ) * 0.7 * 0.0045 * 1.3 := by norm_num

theorem BE_R09_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R09_deriv_of_ballSup (hBall : BE_ballSup_R09) :
    ∀ w, BE_rect_R09.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R09 0.25 16800 (by norm_num) (fun w hw => BE_R09_strip_of_mem hw) hBall

theorem BE_R09_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R09_sphere_of_ballSup (hBall : BE_ballSup_R09)
    (w : ℂ) (hw : BE_rect_R09.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R09 0.25 w hw hz)

theorem BE_R09_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC09‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC09‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC09‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC09‖)
    (hThresh : (0.002 : ℝ) + 0.07 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R09.center = BE_sC09 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R09.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R09.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.07 * BE_rect_R09.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R09_radius_lt) (by norm_num)
  linarith

theorem BE_R09_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R09 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BE_R09_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R09 0.002 0.07 BE_R09_strip_lo BE_R09_strip_hi
    (BE_R09_fencing_of_premises hC hD)

noncomputable def BE_R09_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R09 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    BE_R09_strip_lo BE_R09_strip_hi hD hC

theorem BE_R09_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09) {z : ℂ}
    (hx0 : BE_rect_R09.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R09.x1)
    (hy0 : BE_rect_R09.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R09.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R09 0.002 0.07 BE_R09_strip_lo BE_R09_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BE_R09_H_instance
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R09, 0.002, 0.07, rfl, rfl, rfl, rfl, BE_R09_strip_lo, BE_R09_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BE_R09_implies_leaf
    (hC : (0.002 : ℝ) + 0.07 * BE_rect_R09.radius ≤ ‖xiShifted BE_rect_R09.center‖)
    (hD : BE_derivTier_R09) :
    CentralCoverAssembly.R09_leaf_obligations :=
  ⟨hC, hD⟩

/-! ## E10 = (7.5, 10, 0.01, 0.2), outer tier `(0.002, 0.05)`: CLOSED-CONDITIONAL -/

def BE_rect_R10 : CellProofEngine.Rect2D := CentralCoverAssembly.R10

theorem BE_R10_x0 : BE_rect_R10.x0 = 7.5 := rfl
theorem BE_R10_x1 : BE_rect_R10.x1 = 10 := rfl
theorem BE_R10_y0 : BE_rect_R10.y0 = 0.01 := rfl
theorem BE_R10_y1 : BE_rect_R10.y1 = 0.2 := rfl

theorem BE_R10_width_eq : BE_rect_R10.x1 - BE_rect_R10.x0 = 2.5 := by
  rw [BE_R10_x0, BE_R10_x1]; norm_num

theorem BE_R10_strip_lo : -(1 / 2 : ℝ) < BE_rect_R10.y0 :=
  CentralCoverAssembly.R10_strip_lo
theorem BE_R10_strip_hi : BE_rect_R10.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R10_strip_hi

theorem BE_R10_dx : BE_rect_R10.dx = 1.25 :=
  CentralCoverAssembly.R10_dx_eq
theorem BE_R10_dy : BE_rect_R10.dy = 0.095 :=
  CentralCoverAssembly.R10_dy_eq
theorem BE_R10_radius_eq :
    BE_rect_R10.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R10_radius_eq
theorem BE_R10_radius_lt : BE_rect_R10.radius < 1.26 := by
  rw [BE_R10_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

theorem BE_R10_strip_of_mem {w : ℂ} (hw : BE_rect_R10.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [BE_R10_y0] at hy0
  rw [BE_R10_y1] at hy1
  constructor <;> linarith

theorem BE_R10_mem_gridFine : (7.5, 10, 0.01, 0.2) ∈ CentralCoverAssembly.gridFine :=
  CentralCoverAssembly.R10_mem_gridFine

/-- R10 s-center `s = 1/2 + I*center` (`z = 8.75 + 0.105*I`, so
`s = 0.395 + 8.75*I`). -/
noncomputable def BE_sC10 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BE_rect_R10.center

/-- Poly lower at R10 s-center. TRUE `≈ 38.41` (`|s|≈8.758`, `|s-1|≈8.770`;
floor 34, headroom 1.13x; mirrors batch-A `BA00` at mirror `Im ∓ 8.75`). -/
def BE_polyLower_R10 : Prop :=
  (34 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BE_sC10‖

/-- Pi lower at R10 s-center. TRUE `≈ 0.798` (`π^(-0.1975)`; floor 0.7,
headroom 1.14x; same `BA00` floor). -/
def BE_piLower_R10 : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BE_sC10‖

/-- Gamma lower at R10 s-center. TRUE `≈ 0.00166` (Stirling at
`s/2 = 0.1975 + 4.375*I`; floor 0.0015, headroom 1.11x; same `BA00` floor,
tightest outer claim in this file). -/
def BE_gammaLower_R10 : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BE_sC10‖

/-- Zeta lower at R10 s-center. TRUE unmeasured `O(1)` (the wall; floor 1.9
is the `BA00` precedent at the mirror scale). -/
def BE_zetaLower_R10 : Prop :=
  (1.9 : ℝ) ≤ ‖zeta BE_sC10‖

def BE_derivTier_R10 : Prop :=
  ∀ w, BE_rect_R10.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

def BE_ballSup_R10 : Prop :=
  ∀ z ∈ Metric.closedBall BE_rect_R10.center (BE_rect_R10.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Threshold holds: `34*0.7*0.0015*1.9 = 0.06783 ≥ 0.002+0.05*1.26 = 0.065`
(same arithmetic as batch-A `BA00`). -/
theorem BE_R10_threshold_check :
    (0.002 : ℝ) + 0.05 * 1.26 ≤ (34 : ℝ) * 0.7 * 0.0015 * 1.9 := by norm_num

theorem BE_R10_C_closed : (16800 : ℝ) / 0.25 = 67200 := by norm_num

theorem BE_R10_deriv_of_ballSup (hBall : BE_ballSup_R10) :
    ∀ w, BE_rect_R10.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BE_rect_R10 0.25 16800 (by norm_num) (fun w hw => BE_R10_strip_of_mem hw) hBall

theorem BE_R10_cauchy_tier_mismatch :
    (0.05 : ℝ) < 16800 / 0.25 := by norm_num

theorem BE_R10_sphere_of_ballSup (hBall : BE_ballSup_R10)
    (w : ℂ) (hw : BE_rect_R10.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BE_rect_R10 0.25 w hw hz)

theorem BE_R10_centerBound_of_premises (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf BE_sC10‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf BE_sC10‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf BE_sC10‖)
    (hzeta : Azeta ≤ ‖zeta BE_sC10‖)
    (hThresh : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖ := by
  have harg : (1 / 2 : ℂ) + Complex.I * BE_rect_R10.center = BE_sC10 := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts BE_rect_R10.center
  rw [harg] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted BE_rect_R10.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * BE_rect_R10.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt BE_R10_radius_lt) (by norm_num)
  linarith

theorem BE_R10_fencing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10) :
    CentralCoverAssembly.CellFencingHypotheses BE_rect_R10 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

noncomputable def BE_R10_lowerBound_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BE_rect_R10 0.002 0.05 BE_R10_strip_lo BE_R10_strip_hi
    (BE_R10_fencing_of_premises hC hD)

noncomputable def BE_R10_zeroFree_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BE_rect_R10 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BE_R10_strip_lo BE_R10_strip_hi hD hC

theorem BE_R10_nonvanishing_of_premises
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10) {z : ℂ}
    (hx0 : BE_rect_R10.x0 ≤ z.re) (hx1 : z.re ≤ BE_rect_R10.x1)
    (hy0 : BE_rect_R10.y0 ≤ z.im) (hy1 : z.im ≤ BE_rect_R10.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BE_rect_R10 0.002 0.05 BE_R10_strip_lo BE_R10_strip_hi
      hD hC z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

theorem BE_R10_H_instance
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BE_rect_R10, 0.002, 0.05, rfl, rfl, rfl, rfl, BE_R10_strip_lo, BE_R10_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD, hC⟩

theorem BE_R10_implies_leaf
    (hC : (0.002 : ℝ) + 0.05 * BE_rect_R10.radius ≤ ‖xiShifted BE_rect_R10.center‖)
    (hD : BE_derivTier_R10) :
    CentralCoverAssembly.R10_leaf_obligations :=
  ⟨hC, hD⟩

end Door3BatchE

/-! ## BATCH-E CLOSE-OUT (Step 12 honesty record)

* Claimed: R01 (off-grid extra, membership-free H-leaf) + R05–R10 (all
  `(0.01,0.2)`, all in `gridFine` except R01 which is absent by the banked
  DATA NOTE); sibling batches A–D and upper rows untouched; no other file
  touched; no commits; no builds.
* Per cell: CLOSED-conditional on 6 explicit `Prop` premises (4 factor floors
  + tier-M + ball-sup); no FEASIBILITY-NEGATIVE cell (every `norm_num`
  threshold passes — the batch-D `BD_RXX_threshold_negative` pattern is not
  triggered). Every premise carries its TRUE value/margin in its doc-comment.
  No unfinished proofs; explicit binders throughout; no single-tactic closes;
  at most 6 digits; `norm_num` only on `ℝ` goals (widths, thresholds, closed
  forms, mismatches, nonneg side conditions); membership/strip/geometry reuse
  banked `RXX` lemmas (all existence-verified read-only before writing).
* Imports: `Mathlib` + `central_cover_assembly` only; no cycle-risk extras.
* Patch remainder: 42 factor/deriv/ball premises (6/cell) + build verification
  + tight-premise discharge for R01/R09/R10 (margins 1.09x/1.14x/1.04x) +
  gamma-lower enclosures (Stirling-disc treatment, the documented wall) +
  zeta-lower enclosures (complex-zeta wall) + `BottomStripObligations` + edge
  strips + cutoffs + real axis + central registration. Report-and-stop.
-/
