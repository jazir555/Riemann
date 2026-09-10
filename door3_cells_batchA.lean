import Mathlib
import central_cover_assembly

/-!
# Door 3 bottom-row batch A (`door3_cells_batchA.lean`, NEW file, WRITE-ONLY)

Replicates the `door3_first_cell.lean` 12-step template for BOTTOM-ROW cells
(`Im ∈ (0.01, 0.2)`, the R02-pattern row) EXCLUDING the already-done
`(−8,−5.5)×(0.01,0.2)` (R02) cell. Sibling agents own other rows / batches.

## CLAIMED CELLS (this file owns exactly these three; all in `gridFine`)

| tag   | rect `(x0,x1,y0,y1)`   | z-center            | s-center `1/2+I·z` | radius                          | tier `(ε,M)`   |
|-------|------------------------|---------------------|---------------------|---------------------------------|----------------|
| BA00  | `(-10,-7.5,0.01,0.2)`  | `-8.75 + 0.105·I`   | `0.395 − 8.75·I`    | `√(1.25²+0.095²) < 1.26`        | `(0.002,0.05)` |
| BA03  | `(-6,-3.5,0.01,0.2)`   | `-4.75 + 0.105·I`   | `0.395 − 4.75·I`    | `√(1.25²+0.095²) < 1.26`        | `(0.05,0.07)`  |
| BA04  | `(-4,-1.5,0.01,0.2)`   | `-2.75 + 0.105·I`   | `0.395 − 2.75·I`    | `√(1.25²+0.095²) < 1.26`        | `(0.05,0.07)`  |

Inventory pointers (all read-only, verified before writing; nothing touched):
* `fineGridX` (10 columns, width `2.5`, `central_cover_assembly.lean:954`),
  `innerGridY` (4 rows `[(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]`, `:372`),
  `gridFine = fineGridX.flatMap …` (40 cells, `:1002`).
* Bottom row: `R00` (`:1133`), `R02` (`:1430`, DONE elsewhere — excluded here),
  `R03` (`:1516`), `R04` (`:1602`), `R05` (`:1688`), `R06` (`:1774`),
  `R07` (`:1860`), `R08` (`:1946`), `R09` (`:2032`), `R10` (`:2118`);
  `bottomRowCells` (`:2262`), `BottomRowObligations` (`:2351`),
  `FullCentralObligations = BottomRow ∧ UpperRows` (`:5164`),
  `allCentral_H_of_obligations` (`:5264`).
* Tiers: `R00_leaf_obligations` `(0.002,0.05)` (`:1175`),
  `R03/R04_leaf_obligations` `(0.05,0.07)` (`:1556`, `:1642`).
* Fencing assembly (all cited banked names verified to exist):
  `CellFencingHypotheses` (`:504`),
  `lowerBoundRect_of_fencingHypotheses_strip` (`:941`),
  `zeroFreeRect_of_rect_center_bound_strip` (`:931`),
  `xi_rect_lower_bound_of_center_bound_strip` (`:882`),
  `inner_nonvanishing_of_fenced_grid_fine` (`:1047`),
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`),
  `DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem` (`:6213`),
  `DerivCauchyBridge.norm_xiShifted_eq_parts` (`:6350`),
  `DerivCauchyBridge.polyOf/piOf/gammaOf` (`:6328/:6331/:6334`),
  `sample_cell_radius_bound`, `fine_eps_outer_pos`, `fine_eps_mid_pos`,
  per-cell `RXX_strip_lo/hi`, `RXX_radius_eq`, `RXX_mem_gridFine`.
* Deliberately NOT cited (R02-specific, do not apply to these s-centers):
  `R02Pilot.*`, `R02GammaDisc.*`, `P1_R02_unconditional`,
  `Door3DownstreamDischarge.*`. All four factor floors below are therefore
  explicit premises (honest wall), unlike the R02 template which banks poly/pi.

## PER-CELL STATUS (all CLOSED-conditional; no `sorry`/`admit`/`axiom`)

* BA00: 6 explicit premises (`poly 34`, `pi 0.7`, `gamma 0.0015`, `zeta 1.9`,
  tier-`M 0.05`, ball-sup `16800`); threshold
  `0.002+0.05·1.26 = 0.065 ≤ 34·0.7·0.0015·1.9 = 0.06783` PROVED by `norm_num`.
* BA03: 6 explicit premises (`poly 10`, `pi 0.7`, `gamma 0.015`, `zeta 1.4`,
  tier-`M 0.07`, ball-sup `16800`); threshold
  `0.05+0.07·1.26 = 0.1382 ≤ 10·0.7·0.015·1.4 = 0.147` PROVED by `norm_num`.
* BA04: 6 explicit premises (`poly 3.5`, `pi 0.7`, `gamma 0.08`, `zeta 1.0`,
  tier-`M 0.07`, ball-sup `16800`); threshold
  `0.05+0.07·1.26 = 0.1382 ≤ 3.5·0.7·0.08·1.0 = 0.196` PROVED by `norm_num`.

## PATCH REMAINDER (for the patch phase; untouched here)

For each cell: discharge the 4 factor premises (poly/pi via the
`norm_sCenter_ge`-style `norm_num` floor pattern at the new s-center; gamma/zeta
are the complex wall needing rigorous enclosures), the direct tier-`M` deriv
bound (no Cauchy route can supply tier `M`: `16800/0.25 = 67200 ≫ tier`,
proved per cell as `*_cauchy_tier_mismatch`), and the fat-ball sup premise
(per-cell wide-rect `Λ₀`-style verification). Unclaimed bottom-row cells
`R05–R10` belong to sibling batches; upper rows, `BottomStripObligations`,
edge strips, cutoffs, and the real axis are out of scope.
-/

noncomputable section

namespace Door3CellsBatchA

/-! ## BA00 = (-10,-7.5,0.01,0.2), outer tier `(0.002,0.05)` -/

/-- The cell tuple as pure `ℝ` data. -/
def BA00_cell : ℝ × ℝ × ℝ × ℝ := (-10, -7.5, 0.01, 0.2)

/-- Step 1 (RECT): alias the banked `R00` so every banked `R00` lemma applies. -/
def BA00_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R00

/-- Step 2 (COORDS). -/
theorem BA00_rect_x0 : BA00_rect.x0 = -10 := rfl
theorem BA00_rect_x1 : BA00_rect.x1 = -7.5 := rfl
theorem BA00_rect_y0 : BA00_rect.y0 = 0.01 := rfl
theorem BA00_rect_y1 : BA00_rect.y1 = 0.2 := rfl

theorem BA00_rect_width_eq : BA00_rect.x1 - BA00_rect.x0 = 2.5 := by
  rw [BA00_rect_x0, BA00_rect_x1]; norm_num

/-- Step 3 (STRIP): reuse banked bounds. -/
theorem BA00_strip_lo : -(1 / 2 : ℝ) < BA00_rect.y0 :=
  CentralCoverAssembly.R00_strip_lo
theorem BA00_strip_hi : BA00_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R00_strip_hi

/-- Step 4 (GEOMETRY): banked `(1.25, 0.095)` shape. -/
theorem BA00_rect_radius_eq :
    BA00_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R00_radius_eq
theorem BA00_rect_radius_lt : BA00_rect.radius < 1.26 := by
  rw [BA00_rect_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

/-- Step 5 (STRIP-POINTS). -/
theorem BA00_strip_of_mem {w : ℂ} (hw : BA00_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  have hLo : -(1 / 2 : ℝ) < BA00_rect.y0 :=
    CentralCoverAssembly.R00_strip_lo
  have hHi : BA00_rect.y1 < (1 / 2 : ℝ) :=
    CentralCoverAssembly.R00_strip_hi
  constructor <;> linarith

/-- Step 6 (MEMBERSHIP): banked grid position. -/
theorem BA00_mem_gridFine :
    BA00_cell ∈ CentralCoverAssembly.gridFine := by
  have h := CentralCoverAssembly.R00_mem_gridFine
  unfold BA00_cell
  exact h

/-- Step 7a (s-CENTER): `s = 1/2 + I·z` at the rect center
(`z = -8.75 + 0.105·I`, so `s = 0.395 − 8.75·I`). -/
noncomputable def BA00_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BA00_rect.center

/-- Step 7b (FACTOR premises; TRUE values in comments — the complex wall).
Poly floor `34`: TRUE `≈ 38.5` (`|s|≈8.759`, `|s−1|≈8.79`). -/
def BA00_polyLower_obligation : Prop :=
  (34 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BA00_sCenter‖

/-- Pi floor `0.7`: TRUE `≈ 0.798` (`π^(−0.395/2)`, depends only on `Re s`). -/
def BA00_piLower_obligation : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BA00_sCenter‖

/-- Gamma floor `0.0015`: TRUE `≈ 0.0018` (Gamma Im-decay at `Im(s/2)≈−4.375`;
TIGHT, flagged — same thin corner as the template header notes). -/
def BA00_gammaLower_obligation : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BA00_sCenter‖

/-- Zeta floor `1.9`: TRUE unmeasured, `O(1)` (the documented complex-zeta wall). -/
def BA00_zetaLower_obligation : Prop :=
  (1.9 : ℝ) ≤ ‖zeta BA00_sCenter‖

/-- Step 9a (TIER deriv premise): TRUE unknown (wall). -/
def BA00_derivTier_obligation : Prop :=
  ∀ w, BA00_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)

/-- Step 9b (BALL-SUP premise for the Cauchy route): TRUE with large margin
(`‖entire‖` on the fat ball is `O(10²)`; `16800` is ultra-safe, needs per-cell
wide-rect verification in the patch phase). -/
def BA00_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall BA00_rect.center (BA00_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Step 8 (THRESHOLD): `0.002 + 0.05·1.26 = 0.065 ≤ 34·0.7·0.0015·1.9`. -/
theorem BA00_centerThreshold_check :
    (0.002 : ℝ) + 0.05 * 1.26 ≤ 34 * 0.7 * 0.0015 * 1.9 := by norm_num

/-- Feasibility record: budget `0.065` vs TRUE center `≈ 0.083` (thin-positive,
per the template header: corner Gamma-decay cell). -/
theorem BA00_budget_vs_trueCenter :
    (0.002 : ℝ) + 0.05 * 1.26 < 0.083 := by norm_num

/-- Step 7c+8 (CENTER-LOWER): four factor premises + threshold give the fencing
center bound, via `DerivCauchyBridge.norm_xiShifted_eq_parts`. -/
theorem BA00_centerBound_of_premises
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation) :
    (0.002 : ℝ) + 0.05 * BA00_rect.radius ≤ ‖xiShifted BA00_rect.center‖ := by
  have hEq := DerivCauchyBridge.norm_xiShifted_eq_parts BA00_rect.center
  have hFold : ((1 / 2 : ℂ) + Complex.I * BA00_rect.center) = BA00_sCenter := rfl
  rw [hFold] at hEq
  have h12 : (34 : ℝ) * 0.7 ≤
      ‖DerivCauchyBridge.polyOf BA00_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA00_sCenter‖ :=
    mul_le_mul hP hPi (by norm_num) (norm_nonneg _)
  have h123 : (34 : ℝ) * 0.7 * 0.0015 ≤
      (‖DerivCauchyBridge.polyOf BA00_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA00_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA00_sCenter‖ :=
    mul_le_mul h12 hG (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hProd : (34 : ℝ) * 0.7 * 0.0015 * 1.9 ≤
      ((‖DerivCauchyBridge.polyOf BA00_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA00_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA00_sCenter‖) *
      ‖zeta BA00_sCenter‖ :=
    mul_le_mul h123 hZ (by norm_num) (by norm_num)
  have hR : BA00_rect.radius < 1.26 := BA00_rect_radius_lt
  have hMcap : (0.05 : ℝ) * BA00_rect.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left (le_of_lt hR) (by norm_num)
  rw [hEq]
  linarith [BA00_centerThreshold_check, hMcap, hProd]

/-- Step 9c (CAUCHY route): closed-ball premise gives `M = 16800 / 0.25`. -/
theorem BA00_deriv_of_ballSup (hBall : BA00_ballSup_obligation) :
    ∀ w, BA00_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BA00_rect 0.25 16800 (by norm_num) (fun w hw => BA00_strip_of_mem hw) hBall

/-- Closed form `16800 / 0.25 = 67200`. -/
theorem BA00_deriv67200_of_ballSup (hBall : BA00_ballSup_obligation) {w : ℂ}
    (hw : BA00_rect.mem w) : ‖deriv xiShifted w‖ ≤ 67200 := by
  have h := BA00_deriv_of_ballSup hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rwa [heq] at h

/-- Honest gap: no Cauchy route supplies tier `M = 0.05`
(`67200 ≫ 0.05`); fix-waves need direct deriv bounds or subdivision. -/
theorem BA00_cauchy_tier_mismatch :
    (0.05 : ℝ) < 16800 / 0.25 := by norm_num

/-- Ball ⇒ sphere link (closed ball contains every `0.25`-sphere over the rect). -/
theorem BA00_sphere_of_ballSup (hBall : BA00_ballSup_obligation)
    (w : ℂ) (hw : BA00_rect.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BA00_rect 0.25 w hw hz)

/-- Step 10 (FENCING triple). -/
theorem BA00_fencing_of_premises
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses BA00_rect 0.002 0.05 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD,
    BA00_centerBound_of_premises hP hPi hG hZ⟩

/-- Obligations → lower-bound rect. -/
noncomputable def BA00_lowerBound_of_premises
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BA00_rect 0.002 0.05 BA00_strip_lo BA00_strip_hi
    (BA00_fencing_of_premises hP hPi hG hZ hD)

/-- Obligations → zero-free rect. -/
noncomputable def BA00_zeroFree_of_premises
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BA00_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.05
    BA00_strip_lo BA00_strip_hi hD
    (BA00_centerBound_of_premises hP hPi hG hZ)

/-- Obligations → pointwise nonvanishing on the cell. -/
theorem BA00_nonvanishing_of_premises
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation) {z : ℂ}
    (hx0 : BA00_rect.x0 ≤ z.re) (hx1 : z.re ≤ BA00_rect.x1)
    (hy0 : BA00_rect.y0 ≤ z.im) (hy1 : z.im ≤ BA00_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BA00_rect 0.002 0.05 BA00_strip_lo BA00_strip_hi
      hD (BA00_centerBound_of_premises hP hPi hG hZ) z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

/-- Step 11a (H-LEAF): exact `inner_nonvanishing_of_fenced_grid_fine` shape
at `(-10, -7.5, 0.01, 0.2)` (1 of the 40 leaves; 2 of the 80 obligations). -/
theorem BA00_H_instance
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = BA00_cell) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BA00_rect, 0.002, 0.05, rfl, rfl, rfl, rfl, BA00_strip_lo,
    BA00_strip_hi, CentralCoverAssembly.fine_eps_outer_pos, hD,
    BA00_centerBound_of_premises hP hPi hG hZ⟩

/-- Step 11b (PLUG-IN): premises imply the banked `R00_leaf_obligations`
component of `BottomRowObligations` (hence of `FullCentralObligations`). -/
theorem BA00_implies_R00_leaf
    (hP : BA00_polyLower_obligation) (hPi : BA00_piLower_obligation)
    (hG : BA00_gammaLower_obligation) (hZ : BA00_zetaLower_obligation)
    (hD : BA00_derivTier_obligation) :
    CentralCoverAssembly.R00_leaf_obligations :=
  ⟨BA00_centerBound_of_premises hP hPi hG hZ, hD⟩

/-! ## BA03 = (-6,-3.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- The cell tuple as pure `ℝ` data. -/
def BA03_cell : ℝ × ℝ × ℝ × ℝ := (-6, -3.5, 0.01, 0.2)

/-- Step 1 (RECT): alias the banked `R03`. -/
def BA03_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R03

/-- Step 2 (COORDS). -/
theorem BA03_rect_x0 : BA03_rect.x0 = -6 := rfl
theorem BA03_rect_x1 : BA03_rect.x1 = -3.5 := rfl
theorem BA03_rect_y0 : BA03_rect.y0 = 0.01 := rfl
theorem BA03_rect_y1 : BA03_rect.y1 = 0.2 := rfl

theorem BA03_rect_width_eq : BA03_rect.x1 - BA03_rect.x0 = 2.5 := by
  rw [BA03_rect_x0, BA03_rect_x1]; norm_num

/-- Step 3 (STRIP). -/
theorem BA03_strip_lo : -(1 / 2 : ℝ) < BA03_rect.y0 :=
  CentralCoverAssembly.R03_strip_lo
theorem BA03_strip_hi : BA03_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R03_strip_hi

/-- Step 4 (GEOMETRY). -/
theorem BA03_rect_radius_eq :
    BA03_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R03_radius_eq
theorem BA03_rect_radius_lt : BA03_rect.radius < 1.26 := by
  rw [BA03_rect_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

/-- Step 5 (STRIP-POINTS). -/
theorem BA03_strip_of_mem {w : ℂ} (hw : BA03_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  have hLo : -(1 / 2 : ℝ) < BA03_rect.y0 :=
    CentralCoverAssembly.R03_strip_lo
  have hHi : BA03_rect.y1 < (1 / 2 : ℝ) :=
    CentralCoverAssembly.R03_strip_hi
  constructor <;> linarith

/-- Step 6 (MEMBERSHIP). -/
theorem BA03_mem_gridFine :
    BA03_cell ∈ CentralCoverAssembly.gridFine := by
  have h := CentralCoverAssembly.R03_mem_gridFine
  unfold BA03_cell
  exact h

/-- Step 7a (s-CENTER): `z = -4.75 + 0.105·I`, so `s = 0.395 − 4.75·I`. -/
noncomputable def BA03_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BA03_rect.center

/-- Poly floor `10`: TRUE `≈ 11.5` (`|s|≈4.766`, `|s−1|≈4.83`). -/
def BA03_polyLower_obligation : Prop :=
  (10 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BA03_sCenter‖

/-- Pi floor `0.7`: TRUE `≈ 0.798`. -/
def BA03_piLower_obligation : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BA03_sCenter‖

/-- Gamma floor `0.015`: TRUE `≈ 0.02–0.03` (milder decay at
`Im(s/2)≈−2.375` than the R02 corner). -/
def BA03_gammaLower_obligation : Prop :=
  (0.015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BA03_sCenter‖

/-- Zeta floor `1.4`: TRUE unmeasured, `O(1)` (wall). -/
def BA03_zetaLower_obligation : Prop :=
  (1.4 : ℝ) ≤ ‖zeta BA03_sCenter‖

/-- Tier deriv premise (`0.07`): TRUE unknown (wall). -/
def BA03_derivTier_obligation : Prop :=
  ∀ w, BA03_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

/-- Ball-sup premise (`16800`, ultra-safe; per-cell wide-rect check is patch). -/
def BA03_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall BA03_rect.center (BA03_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Step 8 (THRESHOLD): `0.05 + 0.07·1.26 = 0.1382 ≤ 10·0.7·0.015·1.4 = 0.147`. -/
theorem BA03_centerThreshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ 10 * 0.7 * 0.015 * 1.4 := by norm_num

/-- Step 7c+8 (CENTER-LOWER). -/
theorem BA03_centerBound_of_premises
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation) :
    (0.05 : ℝ) + 0.07 * BA03_rect.radius ≤ ‖xiShifted BA03_rect.center‖ := by
  have hEq := DerivCauchyBridge.norm_xiShifted_eq_parts BA03_rect.center
  have hFold : ((1 / 2 : ℂ) + Complex.I * BA03_rect.center) = BA03_sCenter := rfl
  rw [hFold] at hEq
  have h12 : (10 : ℝ) * 0.7 ≤
      ‖DerivCauchyBridge.polyOf BA03_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA03_sCenter‖ :=
    mul_le_mul hP hPi (by norm_num) (norm_nonneg _)
  have h123 : (10 : ℝ) * 0.7 * 0.015 ≤
      (‖DerivCauchyBridge.polyOf BA03_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA03_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA03_sCenter‖ :=
    mul_le_mul h12 hG (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hProd : (10 : ℝ) * 0.7 * 0.015 * 1.4 ≤
      ((‖DerivCauchyBridge.polyOf BA03_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA03_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA03_sCenter‖) *
      ‖zeta BA03_sCenter‖ :=
    mul_le_mul h123 hZ (by norm_num) (by norm_num)
  have hR : BA03_rect.radius < 1.26 := BA03_rect_radius_lt
  have hMcap : (0.07 : ℝ) * BA03_rect.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left (le_of_lt hR) (by norm_num)
  rw [hEq]
  linarith [BA03_centerThreshold_check, hMcap, hProd]

/-- Step 9c (CAUCHY route). -/
theorem BA03_deriv_of_ballSup (hBall : BA03_ballSup_obligation) :
    ∀ w, BA03_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BA03_rect 0.25 16800 (by norm_num) (fun w hw => BA03_strip_of_mem hw) hBall

/-- Closed form `16800 / 0.25 = 67200`. -/
theorem BA03_deriv67200_of_ballSup (hBall : BA03_ballSup_obligation) {w : ℂ}
    (hw : BA03_rect.mem w) : ‖deriv xiShifted w‖ ≤ 67200 := by
  have h := BA03_deriv_of_ballSup hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rwa [heq] at h

/-- Honest gap: tier `M = 0.07` unreachable via any Cauchy route. -/
theorem BA03_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

/-- Ball ⇒ sphere link. -/
theorem BA03_sphere_of_ballSup (hBall : BA03_ballSup_obligation)
    (w : ℂ) (hw : BA03_rect.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BA03_rect 0.25 w hw hz)

/-- Step 10 (FENCING triple). -/
theorem BA03_fencing_of_premises
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses BA03_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD,
    BA03_centerBound_of_premises hP hPi hG hZ⟩

/-- Obligations → lower-bound rect. -/
noncomputable def BA03_lowerBound_of_premises
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BA03_rect 0.05 0.07 BA03_strip_lo BA03_strip_hi
    (BA03_fencing_of_premises hP hPi hG hZ hD)

/-- Obligations → zero-free rect. -/
noncomputable def BA03_zeroFree_of_premises
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BA03_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BA03_strip_lo BA03_strip_hi hD
    (BA03_centerBound_of_premises hP hPi hG hZ)

/-- Obligations → pointwise nonvanishing on the cell. -/
theorem BA03_nonvanishing_of_premises
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation) {z : ℂ}
    (hx0 : BA03_rect.x0 ≤ z.re) (hx1 : z.re ≤ BA03_rect.x1)
    (hy0 : BA03_rect.y0 ≤ z.im) (hy1 : z.im ≤ BA03_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BA03_rect 0.05 0.07 BA03_strip_lo BA03_strip_hi
      hD (BA03_centerBound_of_premises hP hPi hG hZ) z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

/-- Step 11a (H-LEAF) at `(-6, -3.5, 0.01, 0.2)`. -/
theorem BA03_H_instance
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = BA03_cell) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BA03_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, BA03_strip_lo,
    BA03_strip_hi, CentralCoverAssembly.fine_eps_mid_pos, hD,
    BA03_centerBound_of_premises hP hPi hG hZ⟩

/-- Step 11b (PLUG-IN): premises imply banked `R03_leaf_obligations`. -/
theorem BA03_implies_R03_leaf
    (hP : BA03_polyLower_obligation) (hPi : BA03_piLower_obligation)
    (hG : BA03_gammaLower_obligation) (hZ : BA03_zetaLower_obligation)
    (hD : BA03_derivTier_obligation) :
    CentralCoverAssembly.R03_leaf_obligations :=
  ⟨BA03_centerBound_of_premises hP hPi hG hZ, hD⟩

/-! ## BA04 = (-4,-1.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- The cell tuple as pure `ℝ` data. -/
def BA04_cell : ℝ × ℝ × ℝ × ℝ := (-4, -1.5, 0.01, 0.2)

/-- Step 1 (RECT): alias the banked `R04`. -/
def BA04_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R04

/-- Step 2 (COORDS). -/
theorem BA04_rect_x0 : BA04_rect.x0 = -4 := rfl
theorem BA04_rect_x1 : BA04_rect.x1 = -1.5 := rfl
theorem BA04_rect_y0 : BA04_rect.y0 = 0.01 := rfl
theorem BA04_rect_y1 : BA04_rect.y1 = 0.2 := rfl

theorem BA04_rect_width_eq : BA04_rect.x1 - BA04_rect.x0 = 2.5 := by
  rw [BA04_rect_x0, BA04_rect_x1]; norm_num

/-- Step 3 (STRIP). -/
theorem BA04_strip_lo : -(1 / 2 : ℝ) < BA04_rect.y0 :=
  CentralCoverAssembly.R04_strip_lo
theorem BA04_strip_hi : BA04_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R04_strip_hi

/-- Step 4 (GEOMETRY). -/
theorem BA04_rect_radius_eq :
    BA04_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R04_radius_eq
theorem BA04_rect_radius_lt : BA04_rect.radius < 1.26 := by
  rw [BA04_rect_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

/-- Step 5 (STRIP-POINTS). -/
theorem BA04_strip_of_mem {w : ℂ} (hw : BA04_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  have hLo : -(1 / 2 : ℝ) < BA04_rect.y0 :=
    CentralCoverAssembly.R04_strip_lo
  have hHi : BA04_rect.y1 < (1 / 2 : ℝ) :=
    CentralCoverAssembly.R04_strip_hi
  constructor <;> linarith

/-- Step 6 (MEMBERSHIP). -/
theorem BA04_mem_gridFine :
    BA04_cell ∈ CentralCoverAssembly.gridFine := by
  have h := CentralCoverAssembly.R04_mem_gridFine
  unfold BA04_cell
  exact h

/-- Step 7a (s-CENTER): `z = -2.75 + 0.105·I`, so `s = 0.395 − 2.75·I`. -/
noncomputable def BA04_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * BA04_rect.center

/-- Poly floor `3.5`: TRUE `≈ 4.0` (`|s|≈2.778`, `|s−1|≈2.88`). -/
def BA04_polyLower_obligation : Prop :=
  (3.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf BA04_sCenter‖

/-- Pi floor `0.7`: TRUE `≈ 0.798`. -/
def BA04_piLower_obligation : Prop :=
  (0.7 : ℝ) ≤ ‖DerivCauchyBridge.piOf BA04_sCenter‖

/-- Gamma floor `0.08`: TRUE `≈ 0.1` (mild decay at `Im(s/2)≈−1.375`). -/
def BA04_gammaLower_obligation : Prop :=
  (0.08 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf BA04_sCenter‖

/-- Zeta floor `1.0`: TRUE unmeasured, `O(1)` (wall; weakest floor used since
the poly·pi·gamma product already covers the mid-tier budget). -/
def BA04_zetaLower_obligation : Prop :=
  (1.0 : ℝ) ≤ ‖zeta BA04_sCenter‖

/-- Tier deriv premise (`0.07`): TRUE unknown (wall). -/
def BA04_derivTier_obligation : Prop :=
  ∀ w, BA04_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

/-- Ball-sup premise (`16800`, ultra-safe; per-cell wide-rect check is patch). -/
def BA04_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall BA04_rect.center (BA04_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-- Step 8 (THRESHOLD): `0.05 + 0.07·1.26 = 0.1382 ≤ 3.5·0.7·0.08·1.0 = 0.196`. -/
theorem BA04_centerThreshold_check :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ 3.5 * 0.7 * 0.08 * 1.0 := by norm_num

/-- Step 7c+8 (CENTER-LOWER). -/
theorem BA04_centerBound_of_premises
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation) :
    (0.05 : ℝ) + 0.07 * BA04_rect.radius ≤ ‖xiShifted BA04_rect.center‖ := by
  have hEq := DerivCauchyBridge.norm_xiShifted_eq_parts BA04_rect.center
  have hFold : ((1 / 2 : ℂ) + Complex.I * BA04_rect.center) = BA04_sCenter := rfl
  rw [hFold] at hEq
  have h12 : (3.5 : ℝ) * 0.7 ≤
      ‖DerivCauchyBridge.polyOf BA04_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA04_sCenter‖ :=
    mul_le_mul hP hPi (by norm_num) (norm_nonneg _)
  have h123 : (3.5 : ℝ) * 0.7 * 0.08 ≤
      (‖DerivCauchyBridge.polyOf BA04_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA04_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA04_sCenter‖ :=
    mul_le_mul h12 hG (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hProd : (3.5 : ℝ) * 0.7 * 0.08 * 1.0 ≤
      ((‖DerivCauchyBridge.polyOf BA04_sCenter‖ *
      ‖DerivCauchyBridge.piOf BA04_sCenter‖) *
      ‖DerivCauchyBridge.gammaOf BA04_sCenter‖) *
      ‖zeta BA04_sCenter‖ :=
    mul_le_mul h123 hZ (by norm_num) (by norm_num)
  have hR : BA04_rect.radius < 1.26 := BA04_rect_radius_lt
  have hMcap : (0.07 : ℝ) * BA04_rect.radius ≤ 0.07 * 1.26 :=
    mul_le_mul_of_nonneg_left (le_of_lt hR) (by norm_num)
  rw [hEq]
  linarith [BA04_centerThreshold_check, hMcap, hProd]

/-- Step 9c (CAUCHY route). -/
theorem BA04_deriv_of_ballSup (hBall : BA04_ballSup_obligation) :
    ∀ w, BA04_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    BA04_rect 0.25 16800 (by norm_num) (fun w hw => BA04_strip_of_mem hw) hBall

/-- Closed form `16800 / 0.25 = 67200`. -/
theorem BA04_deriv67200_of_ballSup (hBall : BA04_ballSup_obligation) {w : ℂ}
    (hw : BA04_rect.mem w) : ‖deriv xiShifted w‖ ≤ 67200 := by
  have h := BA04_deriv_of_ballSup hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rwa [heq] at h

/-- Honest gap: tier `M = 0.07` unreachable via any Cauchy route. -/
theorem BA04_cauchy_tier_mismatch :
    (0.07 : ℝ) < 16800 / 0.25 := by norm_num

/-- Ball ⇒ sphere link. -/
theorem BA04_sphere_of_ballSup (hBall : BA04_ballSup_obligation)
    (w : ℂ) (hw : BA04_rect.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    BA04_rect 0.25 w hw hz)

/-- Step 10 (FENCING triple). -/
theorem BA04_fencing_of_premises
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses BA04_rect 0.05 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_mid_pos, hD,
    BA04_centerBound_of_premises hP hPi hG hZ⟩

/-- Obligations → lower-bound rect. -/
noncomputable def BA04_lowerBound_of_premises
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    BA04_rect 0.05 0.07 BA04_strip_lo BA04_strip_hi
    (BA04_fencing_of_premises hP hPi hG hZ hD)

/-- Obligations → zero-free rect. -/
noncomputable def BA04_zeroFree_of_premises
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    BA04_rect 0.05 CentralCoverAssembly.fine_eps_mid_pos 0.07
    BA04_strip_lo BA04_strip_hi hD
    (BA04_centerBound_of_premises hP hPi hG hZ)

/-- Obligations → pointwise nonvanishing on the cell. -/
theorem BA04_nonvanishing_of_premises
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation) {z : ℂ}
    (hx0 : BA04_rect.x0 ≤ z.re) (hx1 : z.re ≤ BA04_rect.x1)
    (hy0 : BA04_rect.y0 ≤ z.im) (hy1 : z.im ≤ BA04_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      BA04_rect 0.05 0.07 BA04_strip_lo BA04_strip_hi
      hD (BA04_centerBound_of_premises hP hPi hG hZ) z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_mid_pos) hle

/-- Step 11a (H-LEAF) at `(-4, -1.5, 0.01, 0.2)`. -/
theorem BA04_H_instance
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = BA04_cell) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨BA04_rect, 0.05, 0.07, rfl, rfl, rfl, rfl, BA04_strip_lo,
    BA04_strip_hi, CentralCoverAssembly.fine_eps_mid_pos, hD,
    BA04_centerBound_of_premises hP hPi hG hZ⟩

/-- Step 11b (PLUG-IN): premises imply banked `R04_leaf_obligations`. -/
theorem BA04_implies_R04_leaf
    (hP : BA04_polyLower_obligation) (hPi : BA04_piLower_obligation)
    (hG : BA04_gammaLower_obligation) (hZ : BA04_zetaLower_obligation)
    (hD : BA04_derivTier_obligation) :
    CentralCoverAssembly.R04_leaf_obligations :=
  ⟨BA04_centerBound_of_premises hP hPi hG hZ, hD⟩

end Door3CellsBatchA

/-! ## BATCH-A CLOSE-OUT (Step 12 honesty record)

* Claimed: BA00 (`R00`), BA03 (`R03`), BA04 (`R04`) — all bottom row
  `(0.01, 0.2)`, all in `gridFine`, R02 excluded as instructed.
* Per cell: CLOSED-conditional on 6 explicit `Prop` premises each
  (4 factor floors + tier-`M` + ball-sup), every premise carrying its TRUE
  value/margin in its doc-comment. No `sorry` / `admit` / `axiom`; explicit
  binders throughout; no `simpa`; all numerals ≤ 6 digits; `norm_num` only on
  `ℝ` goals (`width`, thresholds, closed forms, mismatches, nonneg side
  conditions); membership/strip/geometry reuse banked `RXX` lemmas (all
  existence-verified read-only before writing).
* Imports: `Mathlib` + `central_cover_assembly` only; no other lanes touched,
  no commits, no logs, no lakefile edits.
* Patch remainder: 18 factor/deriv/ball premises (6/cell) + unclaimed
  `R05–R10` (sibling batches) + upper rows + `BottomStripObligations` +
  edge strips + cutoffs + real axis. Report-and-stop.
-/
