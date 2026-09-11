import Mathlib
import central_cover_assembly

/-!
# Door 3 poly-premise discharge (wave 1 of 5: poly only)

WRITE-ONLY task output. No build/lean/lake command run. No commit/push.
Imports: Mathlib + `central_cover_assembly` only.

## Recon (read-only, brief)

* `door3_first_cell.lean`: poly lower is banked (`FC_poly_lower_banked`,
  `22 <= ||polyOf R02Pilot.sCenter||`, re-proved here as `premPoly_R02_ge`).
  `R02Pilot.sCenter`: re `0.395`, im `-6.75`.
* `door3_cells_batchA.lean`: 3 poly obligations —
  BA00(`R00`, s `0.395-8.75I`) floor `34`;
  BA03(`R03`, s `0.395-4.75I`) floor `10`;
  BA04(`R04`, s `0.395-2.75I`) floor `3.5`.
* `door3_cells_batchB.lean`: row 2 (`R11-R20`) carries NO poly premises
  (center premise directly, 3 premises per cell: center/deriv/ballsup).
  Nothing for this wave.
* `door3_cells_batchC.lean`: 10 poly lowers `BC_polyLower_R31..R40`,
  floors `30/18/9/3/0.25/0.5/4/12/20/30` at re `0.105`,
  im `-8.75/-6.75/-4.75/-2.75/-0.75/1.25/3.25/5.25/7.25/8.75`.
* `door3_cells_batchD.lean`: 10 poly lowers `BD_polyLower_R21..R30`,
  floors `30/20/9/3/0.25/0.5/4/11/24/30` at re `0.2`,
  same im ladder as batch C.
* `door3_cells_batchE.lean`: 7 poly lowers `BE_polyLower_R01/R05..R10`,
  floors `18/0.35/0.8/5/12/25/34` at re `0.395`,
  im `-6.25/-0.75/1.25/3.25/5.25/7.25/8.75`.
* Total explicit poly floors: 31 (`1 + 3 + 10 + 10 + 7`; batch B has none).
  The brief's "~40" counts sibling waves (pi/gamma/zeta/tier live elsewhere).

## Method (uniform, direct evaluation)

`DerivCauchyBridge.polyOf s = s * (s - 1) / 2`.
For explicit `s = <a, b>`, `Re (s * (s-1)) = a * (a - 1) - b * b`,
proved by `simp only [Complex.mul_re, Complex.sub_re,
Complex.one_re, Complex.one_im]` + `norm_num` (real arithmetic only).
Then `||s*(s-1)|| >= |Re|` (`Complex.abs_re_le_norm`) and
`||polyOf s|| = ||s*(s-1)|| / 2` (`norm_div` + `||(2:Complex)|| = 2`
via `Complex.norm_real`). All numerals short (<= 6 digits);
only truncated thresholds appear, never long exact decimals.

## Premises closed (31) + margins (true |Re poly| vs floor)

* R28 `13.86 >= 11` (true `13.86`, margin `+2.86`)
* R29 `26.36 >= 24` (true `26.36`, margin `+2.36`)
* R01 `19.65 >= 18` (true `19.65`, margin `+1.65`)
* R09 `26.40 >= 25` (true `26.40`, margin `+1.40`)
* R10 `38.40 >= 34` (true `38.40`, margin `+4.40`)
* R02 `22.90 >= 22` (true `22.90`, margin `+0.90`)
* R00 `38.40 >= 34` (margin `+4.40`)
* R03 `11.40 >= 10` (margin `+1.40`)
* R04 `3.90 >= 3.5` (margin `+0.40`)
* R05 `0.40 >= 0.35` (true `0.4007`, margin `+0.05`)
* R06 `0.90 >= 0.8` (true `0.9007`, margin `+0.10`)
* R07 `5.40 >= 5` (margin `+0.40`)
* R08 `13.90 >= 12` (margin `+1.90`)
* R21 `38.36 >= 30` (margin `+8.36`)
* R22 `22.86 >= 20` (margin `+2.86`)
* R23 `11.36 >= 9` (margin `+2.36`)
* R24 `3.86 >= 3` (margin `+0.86`)
* R25 `0.36 >= 0.25` (margin `+0.11`)
* R26 `0.86 >= 0.5` (margin `+0.36`)
* R27 `5.36 >= 4` (margin `+1.36`)
* R30 `38.36 >= 30` (margin `+8.36`)
* R31 `38.32 >= 30` (margin `+8.32`)
* R32 `22.82 >= 18` (margin `+4.82`)
* R33 `11.32 >= 9` (margin `+2.32`)
* R34 `3.82 >= 3` (margin `+0.82`)
* R35 `0.32 >= 0.25` (true `0.328`, margin `+0.07`)
* R36 `0.82 >= 0.5` (margin `+0.32`)
* R37 `5.32 >= 4` (margin `+1.32`)
* R38 `13.82 >= 12` (margin `+1.82`)
* R39 `26.32 >= 20` (margin `+6.32`)
* R40 `38.32 >= 30` (margin `+8.32`)

False floors: none. Every stated floor holds with positive margin, so no
`premPoly_RXX_true_ge` variant was needed and no cell needs re-tiering
on poly grounds.

## Patch remainder

Poly wave complete (full prefix of 31 centers, no remainder).
Remaining waves (siblings, other files): pi / gamma / zeta / tier-deriv /
ball-sup per cell.
-/

/-! ## R28 (mid, s = 0.2 + 5.25 I): floor 11 -/

noncomputable def sR28 : ℂ := ⟨(0.2 : ℝ), (5.25 : ℝ)⟩

theorem premPoly_R28_ge : (11 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR28‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR28‖ = ‖sR28 * (sR28 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR28 * (sR28 - 1)).re ≤ (-27.72 : ℝ) := by
    unfold sR28
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR28 * (sR28 - 1)).re| ≤ ‖sR28 * (sR28 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR28 * (sR28 - 1)).re < 0 := by linarith
  have heq : |(sR28 * (sR28 - 1)).re| = -((sR28 * (sR28 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (27.72 : ℝ) ≤ ‖sR28 * (sR28 - 1)‖ := by linarith
  have hfin : (11 : ℝ) ≤ (27.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R29 (leaf-mismatch, s = 0.2 + 7.25 I): floor 24 -/

noncomputable def sR29 : ℂ := ⟨(0.2 : ℝ), (7.25 : ℝ)⟩

theorem premPoly_R29_ge : (24 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR29‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR29‖ = ‖sR29 * (sR29 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR29 * (sR29 - 1)).re ≤ (-52.72 : ℝ) := by
    unfold sR29
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR29 * (sR29 - 1)).re| ≤ ‖sR29 * (sR29 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR29 * (sR29 - 1)).re < 0 := by linarith
  have heq : |(sR29 * (sR29 - 1)).re| = -((sR29 * (sR29 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (52.72 : ℝ) ≤ ‖sR29 * (sR29 - 1)‖ := by linarith
  have hfin : (24 : ℝ) ≤ (52.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R01 (off-grid mid, s = 0.395 - 6.25 I): floor 18 -/

noncomputable def sR01 : ℂ := ⟨(0.395 : ℝ), (-6.25 : ℝ)⟩

theorem premPoly_R01_ge : (18 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR01‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR01‖ = ‖sR01 * (sR01 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR01 * (sR01 - 1)).re ≤ (-39.3 : ℝ) := by
    unfold sR01
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR01 * (sR01 - 1)).re| ≤ ‖sR01 * (sR01 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR01 * (sR01 - 1)).re < 0 := by linarith
  have heq : |(sR01 * (sR01 - 1)).re| = -((sR01 * (sR01 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (39.3 : ℝ) ≤ ‖sR01 * (sR01 - 1)‖ := by linarith
  have hfin : (18 : ℝ) ≤ (39.3 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R09 (leaf, s = 0.395 + 7.25 I): floor 25 -/

noncomputable def sR09 : ℂ := ⟨(0.395 : ℝ), (7.25 : ℝ)⟩

theorem premPoly_R09_ge : (25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR09‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR09‖ = ‖sR09 * (sR09 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR09 * (sR09 - 1)).re ≤ (-52.8 : ℝ) := by
    unfold sR09
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR09 * (sR09 - 1)).re| ≤ ‖sR09 * (sR09 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR09 * (sR09 - 1)).re < 0 := by linarith
  have heq : |(sR09 * (sR09 - 1)).re| = -((sR09 * (sR09 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (52.8 : ℝ) ≤ ‖sR09 * (sR09 - 1)‖ := by linarith
  have hfin : (25 : ℝ) ≤ (52.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R10 (outer, s = 0.395 + 8.75 I): floor 34 -/

noncomputable def sR10 : ℂ := ⟨(0.395 : ℝ), (8.75 : ℝ)⟩

theorem premPoly_R10_ge : (34 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR10‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR10‖ = ‖sR10 * (sR10 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR10 * (sR10 - 1)).re ≤ (-76.8 : ℝ) := by
    unfold sR10
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR10 * (sR10 - 1)).re| ≤ ‖sR10 * (sR10 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR10 * (sR10 - 1)).re < 0 := by linarith
  have heq : |(sR10 * (sR10 - 1)).re| = -((sR10 * (sR10 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.8 : ℝ) ≤ ‖sR10 * (sR10 - 1)‖ := by linarith
  have hfin : (34 : ℝ) ≤ (76.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R02 first-cell (s = 0.395 - 6.75 I): floor 22 -/

noncomputable def sR02 : ℂ := ⟨(0.395 : ℝ), (-6.75 : ℝ)⟩

theorem premPoly_R02_ge : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR02‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR02‖ = ‖sR02 * (sR02 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR02 * (sR02 - 1)).re ≤ (-45.8 : ℝ) := by
    unfold sR02
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR02 * (sR02 - 1)).re| ≤ ‖sR02 * (sR02 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR02 * (sR02 - 1)).re < 0 := by linarith
  have heq : |(sR02 * (sR02 - 1)).re| = -((sR02 * (sR02 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (45.8 : ℝ) ≤ ‖sR02 * (sR02 - 1)‖ := by linarith
  have hfin : (22 : ℝ) ≤ (45.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R00 = BA00 (outer, s = 0.395 - 8.75 I): floor 34 -/

noncomputable def sR00 : ℂ := ⟨(0.395 : ℝ), (-8.75 : ℝ)⟩

theorem premPoly_R00_ge : (34 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR00‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR00‖ = ‖sR00 * (sR00 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR00 * (sR00 - 1)).re ≤ (-76.8 : ℝ) := by
    unfold sR00
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR00 * (sR00 - 1)).re| ≤ ‖sR00 * (sR00 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR00 * (sR00 - 1)).re < 0 := by linarith
  have heq : |(sR00 * (sR00 - 1)).re| = -((sR00 * (sR00 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.8 : ℝ) ≤ ‖sR00 * (sR00 - 1)‖ := by linarith
  have hfin : (34 : ℝ) ≤ (76.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R03 = BA03 (mid, s = 0.395 - 4.75 I): floor 10 -/

noncomputable def sR03 : ℂ := ⟨(0.395 : ℝ), (-4.75 : ℝ)⟩

theorem premPoly_R03_ge : (10 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR03‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR03‖ = ‖sR03 * (sR03 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR03 * (sR03 - 1)).re ≤ (-22.8 : ℝ) := by
    unfold sR03
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR03 * (sR03 - 1)).re| ≤ ‖sR03 * (sR03 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR03 * (sR03 - 1)).re < 0 := by linarith
  have heq : |(sR03 * (sR03 - 1)).re| = -((sR03 * (sR03 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (22.8 : ℝ) ≤ ‖sR03 * (sR03 - 1)‖ := by linarith
  have hfin : (10 : ℝ) ≤ (22.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R04 = BA04 (mid, s = 0.395 - 2.75 I): floor 3.5 -/

noncomputable def sR04 : ℂ := ⟨(0.395 : ℝ), (-2.75 : ℝ)⟩

theorem premPoly_R04_ge : (3.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR04‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR04‖ = ‖sR04 * (sR04 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR04 * (sR04 - 1)).re ≤ (-7.8 : ℝ) := by
    unfold sR04
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR04 * (sR04 - 1)).re| ≤ ‖sR04 * (sR04 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR04 * (sR04 - 1)).re < 0 := by linarith
  have heq : |(sR04 * (sR04 - 1)).re| = -((sR04 * (sR04 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (7.8 : ℝ) ≤ ‖sR04 * (sR04 - 1)‖ := by linarith
  have hfin : (3.5 : ℝ) ≤ (7.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R05 (inner, s = 0.395 - 0.75 I): floor 0.35 -/

noncomputable def sR05 : ℂ := ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩

theorem premPoly_R05_ge : (0.35 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR05‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR05‖ = ‖sR05 * (sR05 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR05 * (sR05 - 1)).re ≤ (-0.8 : ℝ) := by
    unfold sR05
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR05 * (sR05 - 1)).re| ≤ ‖sR05 * (sR05 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR05 * (sR05 - 1)).re < 0 := by linarith
  have heq : |(sR05 * (sR05 - 1)).re| = -((sR05 * (sR05 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (0.8 : ℝ) ≤ ‖sR05 * (sR05 - 1)‖ := by linarith
  have hfin : (0.35 : ℝ) ≤ (0.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R06 (inner, s = 0.395 + 1.25 I): floor 0.8 -/

noncomputable def sR06 : ℂ := ⟨(0.395 : ℝ), (1.25 : ℝ)⟩

theorem premPoly_R06_ge : (0.8 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR06‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR06‖ = ‖sR06 * (sR06 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR06 * (sR06 - 1)).re ≤ (-1.8 : ℝ) := by
    unfold sR06
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR06 * (sR06 - 1)).re| ≤ ‖sR06 * (sR06 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR06 * (sR06 - 1)).re < 0 := by linarith
  have heq : |(sR06 * (sR06 - 1)).re| = -((sR06 * (sR06 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (1.8 : ℝ) ≤ ‖sR06 * (sR06 - 1)‖ := by linarith
  have hfin : (0.8 : ℝ) ≤ (1.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R07 (mid, s = 0.395 + 3.25 I): floor 5 -/

noncomputable def sR07 : ℂ := ⟨(0.395 : ℝ), (3.25 : ℝ)⟩

theorem premPoly_R07_ge : (5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR07‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR07‖ = ‖sR07 * (sR07 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR07 * (sR07 - 1)).re ≤ (-10.8 : ℝ) := by
    unfold sR07
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR07 * (sR07 - 1)).re| ≤ ‖sR07 * (sR07 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR07 * (sR07 - 1)).re < 0 := by linarith
  have heq : |(sR07 * (sR07 - 1)).re| = -((sR07 * (sR07 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (10.8 : ℝ) ≤ ‖sR07 * (sR07 - 1)‖ := by linarith
  have hfin : (5 : ℝ) ≤ (10.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R08 (mid, s = 0.395 + 5.25 I): floor 12 -/

noncomputable def sR08 : ℂ := ⟨(0.395 : ℝ), (5.25 : ℝ)⟩

theorem premPoly_R08_ge : (12 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR08‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR08‖ = ‖sR08 * (sR08 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR08 * (sR08 - 1)).re ≤ (-27.8 : ℝ) := by
    unfold sR08
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR08 * (sR08 - 1)).re| ≤ ‖sR08 * (sR08 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR08 * (sR08 - 1)).re < 0 := by linarith
  have heq : |(sR08 * (sR08 - 1)).re| = -((sR08 * (sR08 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (27.8 : ℝ) ≤ ‖sR08 * (sR08 - 1)‖ := by linarith
  have hfin : (12 : ℝ) ≤ (27.8 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R21 (outer, s = 0.2 - 8.75 I): floor 30 -/

noncomputable def sR21 : ℂ := ⟨(0.2 : ℝ), (-8.75 : ℝ)⟩

theorem premPoly_R21_ge : (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR21‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR21‖ = ‖sR21 * (sR21 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR21 * (sR21 - 1)).re ≤ (-76.72 : ℝ) := by
    unfold sR21
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR21 * (sR21 - 1)).re| ≤ ‖sR21 * (sR21 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR21 * (sR21 - 1)).re < 0 := by linarith
  have heq : |(sR21 * (sR21 - 1)).re| = -((sR21 * (sR21 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.72 : ℝ) ≤ ‖sR21 * (sR21 - 1)‖ := by linarith
  have hfin : (30 : ℝ) ≤ (76.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R22 (leaf, s = 0.2 - 6.75 I): floor 20 -/

noncomputable def sR22 : ℂ := ⟨(0.2 : ℝ), (-6.75 : ℝ)⟩

theorem premPoly_R22_ge : (20 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR22‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR22‖ = ‖sR22 * (sR22 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR22 * (sR22 - 1)).re ≤ (-45.72 : ℝ) := by
    unfold sR22
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR22 * (sR22 - 1)).re| ≤ ‖sR22 * (sR22 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR22 * (sR22 - 1)).re < 0 := by linarith
  have heq : |(sR22 * (sR22 - 1)).re| = -((sR22 * (sR22 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (45.72 : ℝ) ≤ ‖sR22 * (sR22 - 1)‖ := by linarith
  have hfin : (20 : ℝ) ≤ (45.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R23 (mid, s = 0.2 - 4.75 I): floor 9 -/

noncomputable def sR23 : ℂ := ⟨(0.2 : ℝ), (-4.75 : ℝ)⟩

theorem premPoly_R23_ge : (9 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR23‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR23‖ = ‖sR23 * (sR23 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR23 * (sR23 - 1)).re ≤ (-22.72 : ℝ) := by
    unfold sR23
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR23 * (sR23 - 1)).re| ≤ ‖sR23 * (sR23 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR23 * (sR23 - 1)).re < 0 := by linarith
  have heq : |(sR23 * (sR23 - 1)).re| = -((sR23 * (sR23 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (22.72 : ℝ) ≤ ‖sR23 * (sR23 - 1)‖ := by linarith
  have hfin : (9 : ℝ) ≤ (22.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R24 (mid, s = 0.2 - 2.75 I): floor 3 -/

noncomputable def sR24 : ℂ := ⟨(0.2 : ℝ), (-2.75 : ℝ)⟩

theorem premPoly_R24_ge : (3 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR24‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR24‖ = ‖sR24 * (sR24 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR24 * (sR24 - 1)).re ≤ (-7.72 : ℝ) := by
    unfold sR24
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR24 * (sR24 - 1)).re| ≤ ‖sR24 * (sR24 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR24 * (sR24 - 1)).re < 0 := by linarith
  have heq : |(sR24 * (sR24 - 1)).re| = -((sR24 * (sR24 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (7.72 : ℝ) ≤ ‖sR24 * (sR24 - 1)‖ := by linarith
  have hfin : (3 : ℝ) ≤ (7.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R25 (inner, s = 0.2 - 0.75 I): floor 0.25 -/

noncomputable def sR25 : ℂ := ⟨(0.2 : ℝ), (-0.75 : ℝ)⟩

theorem premPoly_R25_ge : (0.25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR25‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR25‖ = ‖sR25 * (sR25 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR25 * (sR25 - 1)).re ≤ (-0.72 : ℝ) := by
    unfold sR25
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR25 * (sR25 - 1)).re| ≤ ‖sR25 * (sR25 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR25 * (sR25 - 1)).re < 0 := by linarith
  have heq : |(sR25 * (sR25 - 1)).re| = -((sR25 * (sR25 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (0.72 : ℝ) ≤ ‖sR25 * (sR25 - 1)‖ := by linarith
  have hfin : (0.25 : ℝ) ≤ (0.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R26 (inner, s = 0.2 + 1.25 I): floor 0.5 -/

noncomputable def sR26 : ℂ := ⟨(0.2 : ℝ), (1.25 : ℝ)⟩

theorem premPoly_R26_ge : (0.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR26‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR26‖ = ‖sR26 * (sR26 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR26 * (sR26 - 1)).re ≤ (-1.72 : ℝ) := by
    unfold sR26
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR26 * (sR26 - 1)).re| ≤ ‖sR26 * (sR26 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR26 * (sR26 - 1)).re < 0 := by linarith
  have heq : |(sR26 * (sR26 - 1)).re| = -((sR26 * (sR26 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (1.72 : ℝ) ≤ ‖sR26 * (sR26 - 1)‖ := by linarith
  have hfin : (0.5 : ℝ) ≤ (1.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R27 (mid, s = 0.2 + 3.25 I): floor 4 -/

noncomputable def sR27 : ℂ := ⟨(0.2 : ℝ), (3.25 : ℝ)⟩

theorem premPoly_R27_ge : (4 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR27‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR27‖ = ‖sR27 * (sR27 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR27 * (sR27 - 1)).re ≤ (-10.72 : ℝ) := by
    unfold sR27
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR27 * (sR27 - 1)).re| ≤ ‖sR27 * (sR27 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR27 * (sR27 - 1)).re < 0 := by linarith
  have heq : |(sR27 * (sR27 - 1)).re| = -((sR27 * (sR27 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (10.72 : ℝ) ≤ ‖sR27 * (sR27 - 1)‖ := by linarith
  have hfin : (4 : ℝ) ≤ (10.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R30 (outer, s = 0.2 + 8.75 I): floor 30 -/

noncomputable def sR30 : ℂ := ⟨(0.2 : ℝ), (8.75 : ℝ)⟩

theorem premPoly_R30_ge : (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR30‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR30‖ = ‖sR30 * (sR30 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR30 * (sR30 - 1)).re ≤ (-76.72 : ℝ) := by
    unfold sR30
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR30 * (sR30 - 1)).re| ≤ ‖sR30 * (sR30 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR30 * (sR30 - 1)).re < 0 := by linarith
  have heq : |(sR30 * (sR30 - 1)).re| = -((sR30 * (sR30 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.72 : ℝ) ≤ ‖sR30 * (sR30 - 1)‖ := by linarith
  have hfin : (30 : ℝ) ≤ (76.72 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R31 (outer, s = 0.105 - 8.75 I): floor 30 -/

noncomputable def sR31 : ℂ := ⟨(0.105 : ℝ), (-8.75 : ℝ)⟩

theorem premPoly_R31_ge : (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR31‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR31‖ = ‖sR31 * (sR31 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR31 * (sR31 - 1)).re ≤ (-76.64 : ℝ) := by
    unfold sR31
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR31 * (sR31 - 1)).re| ≤ ‖sR31 * (sR31 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR31 * (sR31 - 1)).re < 0 := by linarith
  have heq : |(sR31 * (sR31 - 1)).re| = -((sR31 * (sR31 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.64 : ℝ) ≤ ‖sR31 * (sR31 - 1)‖ := by linarith
  have hfin : (30 : ℝ) ≤ (76.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R32 (mid-outer, s = 0.105 - 6.75 I): floor 18 -/

noncomputable def sR32 : ℂ := ⟨(0.105 : ℝ), (-6.75 : ℝ)⟩

theorem premPoly_R32_ge : (18 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR32‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR32‖ = ‖sR32 * (sR32 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR32 * (sR32 - 1)).re ≤ (-45.64 : ℝ) := by
    unfold sR32
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR32 * (sR32 - 1)).re| ≤ ‖sR32 * (sR32 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR32 * (sR32 - 1)).re < 0 := by linarith
  have heq : |(sR32 * (sR32 - 1)).re| = -((sR32 * (sR32 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (45.64 : ℝ) ≤ ‖sR32 * (sR32 - 1)‖ := by linarith
  have hfin : (18 : ℝ) ≤ (45.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R33 (mid, s = 0.105 - 4.75 I): floor 9 -/

noncomputable def sR33 : ℂ := ⟨(0.105 : ℝ), (-4.75 : ℝ)⟩

theorem premPoly_R33_ge : (9 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR33‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR33‖ = ‖sR33 * (sR33 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR33 * (sR33 - 1)).re ≤ (-22.64 : ℝ) := by
    unfold sR33
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR33 * (sR33 - 1)).re| ≤ ‖sR33 * (sR33 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR33 * (sR33 - 1)).re < 0 := by linarith
  have heq : |(sR33 * (sR33 - 1)).re| = -((sR33 * (sR33 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (22.64 : ℝ) ≤ ‖sR33 * (sR33 - 1)‖ := by linarith
  have hfin : (9 : ℝ) ≤ (22.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R34 (mid, s = 0.105 - 2.75 I): floor 3 -/

noncomputable def sR34 : ℂ := ⟨(0.105 : ℝ), (-2.75 : ℝ)⟩

theorem premPoly_R34_ge : (3 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR34‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR34‖ = ‖sR34 * (sR34 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR34 * (sR34 - 1)).re ≤ (-7.64 : ℝ) := by
    unfold sR34
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR34 * (sR34 - 1)).re| ≤ ‖sR34 * (sR34 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR34 * (sR34 - 1)).re < 0 := by linarith
  have heq : |(sR34 * (sR34 - 1)).re| = -((sR34 * (sR34 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (7.64 : ℝ) ≤ ‖sR34 * (sR34 - 1)‖ := by linarith
  have hfin : (3 : ℝ) ≤ (7.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R35 (inner, s = 0.105 - 0.75 I): floor 0.25 -/

noncomputable def sR35 : ℂ := ⟨(0.105 : ℝ), (-0.75 : ℝ)⟩

theorem premPoly_R35_ge : (0.25 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR35‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR35‖ = ‖sR35 * (sR35 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR35 * (sR35 - 1)).re ≤ (-0.64 : ℝ) := by
    unfold sR35
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR35 * (sR35 - 1)).re| ≤ ‖sR35 * (sR35 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR35 * (sR35 - 1)).re < 0 := by linarith
  have heq : |(sR35 * (sR35 - 1)).re| = -((sR35 * (sR35 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (0.64 : ℝ) ≤ ‖sR35 * (sR35 - 1)‖ := by linarith
  have hfin : (0.25 : ℝ) ≤ (0.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R36 (inner, s = 0.105 + 1.25 I): floor 0.5 -/

noncomputable def sR36 : ℂ := ⟨(0.105 : ℝ), (1.25 : ℝ)⟩

theorem premPoly_R36_ge : (0.5 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR36‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR36‖ = ‖sR36 * (sR36 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR36 * (sR36 - 1)).re ≤ (-1.64 : ℝ) := by
    unfold sR36
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR36 * (sR36 - 1)).re| ≤ ‖sR36 * (sR36 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR36 * (sR36 - 1)).re < 0 := by linarith
  have heq : |(sR36 * (sR36 - 1)).re| = -((sR36 * (sR36 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (1.64 : ℝ) ≤ ‖sR36 * (sR36 - 1)‖ := by linarith
  have hfin : (0.5 : ℝ) ≤ (1.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R37 (mid, s = 0.105 + 3.25 I): floor 4 -/

noncomputable def sR37 : ℂ := ⟨(0.105 : ℝ), (3.25 : ℝ)⟩

theorem premPoly_R37_ge : (4 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR37‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR37‖ = ‖sR37 * (sR37 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR37 * (sR37 - 1)).re ≤ (-10.64 : ℝ) := by
    unfold sR37
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR37 * (sR37 - 1)).re| ≤ ‖sR37 * (sR37 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR37 * (sR37 - 1)).re < 0 := by linarith
  have heq : |(sR37 * (sR37 - 1)).re| = -((sR37 * (sR37 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (10.64 : ℝ) ≤ ‖sR37 * (sR37 - 1)‖ := by linarith
  have hfin : (4 : ℝ) ≤ (10.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R38 (mid, s = 0.105 + 5.25 I): floor 12 -/

noncomputable def sR38 : ℂ := ⟨(0.105 : ℝ), (5.25 : ℝ)⟩

theorem premPoly_R38_ge : (12 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR38‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR38‖ = ‖sR38 * (sR38 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR38 * (sR38 - 1)).re ≤ (-27.64 : ℝ) := by
    unfold sR38
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR38 * (sR38 - 1)).re| ≤ ‖sR38 * (sR38 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR38 * (sR38 - 1)).re < 0 := by linarith
  have heq : |(sR38 * (sR38 - 1)).re| = -((sR38 * (sR38 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (27.64 : ℝ) ≤ ‖sR38 * (sR38 - 1)‖ := by linarith
  have hfin : (12 : ℝ) ≤ (27.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R39 (mid-outer, s = 0.105 + 7.25 I): floor 20 -/

noncomputable def sR39 : ℂ := ⟨(0.105 : ℝ), (7.25 : ℝ)⟩

theorem premPoly_R39_ge : (20 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR39‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR39‖ = ‖sR39 * (sR39 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR39 * (sR39 - 1)).re ≤ (-52.64 : ℝ) := by
    unfold sR39
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR39 * (sR39 - 1)).re| ≤ ‖sR39 * (sR39 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR39 * (sR39 - 1)).re < 0 := by linarith
  have heq : |(sR39 * (sR39 - 1)).re| = -((sR39 * (sR39 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (52.64 : ℝ) ≤ ‖sR39 * (sR39 - 1)‖ := by linarith
  have hfin : (20 : ℝ) ≤ (52.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith

/-! ## R40 (outer, s = 0.105 + 8.75 I): floor 30 -/

noncomputable def sR40 : ℂ := ⟨(0.105 : ℝ), (8.75 : ℝ)⟩

theorem premPoly_R40_ge : (30 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR40‖ := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hdiv : ‖DerivCauchyBridge.polyOf sR40‖ = ‖sR40 * (sR40 - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, h2]
  have hre : (sR40 * (sR40 - 1)).re ≤ (-76.64 : ℝ) := by
    unfold sR40
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im]
    norm_num
  have habs : |(sR40 * (sR40 - 1)).re| ≤ ‖sR40 * (sR40 - 1)‖ :=
    Complex.abs_re_le_norm _
  have hneg : (sR40 * (sR40 - 1)).re < 0 := by linarith
  have heq : |(sR40 * (sR40 - 1)).re| = -((sR40 * (sR40 - 1)).re) :=
    abs_of_neg hneg
  rw [heq] at habs
  have hprod : (76.64 : ℝ) ≤ ‖sR40 * (sR40 - 1)‖ := by linarith
  have hfin : (30 : ℝ) ≤ (76.64 : ℝ) / 2 := by norm_num
  rw [hdiv]
  linarith
