import Mathlib
import central_cover_assembly

/-!
# Door 3 pi-power premise discharge (`door3_premise_pi.lean`, NEW file, WRITE-ONLY)

Job: premise-class wave 2 of 5 — discharge ALL pi-power premises across the
40 batch cells (plus the R02 first-cell center, already banked, reproduced
here for completeness).

## RECON (read-only, verified before writing; nothing touched)

Explicit s-center pi lowers (`(floor) ≤ ‖DerivCauchyBridge.piOf sC‖`):

| cells | batch file | premise names | floor | s.re | TRUE `π^(-re/2)` | margin |
|-------|-----------|---------------|-------|------|------------------|--------|
| R00 (BA00), R03 (BA03), R04 (BA04) | `door3_cells_batchA.lean:134,350,555` | `BA00/BA03/BA04_piLower_obligation` | `0.7` | `0.395` | `≈ 0.7977` | `0.0977` |
| R01,R05–R10 (BE) | `door3_cells_batchE.lean:172,339,504,669,834,1002,1167` | `BE_piLower_R01/R05–R10` | `0.7` | `0.395` | `≈ 0.7977` | `0.0977` |
| R02 (first cell) | `door3_first_cell.lean:198` (`FC_pi_lower_banked`, banked) | floor `1/2` | `1/2` | `0.395` | `≈ 0.7977` | `0.2977` |
| R11–R20 (BB) | `door3_cells_batchB.lean` — NO pi-factor premises (whole-center form) | remainder cover | `0.7` | `0.3` | `≈ 0.8422` | `0.1422` |
| R21–R30 (BD) | `door3_cells_batchD.lean:151,313,471,628,785,942,1099,1256,1414,1572` | `BD_piLower_R21–R30` | `1/2` | `0.2` | `≈ 0.8919` | `0.3919` |
| R31–R40 (BC) | `door3_cells_batchC.lean:155,317,475,632,790,947,1104,1261,1418,1575` | `BC_piLower_R31–R40` | `1/2` | `0.105` | `≈ 0.9417` | `0.4417` |

Pi uppers: per-center `‖piOf sC‖ ≤ 1` (all rows, TRUE since `re > 0`);
the ten `R31–R40_pi_upper_obligation` rect-`∀` uppers
(`central_cover_assembly.lean:11023,11411,11743,12039,12349,12624,12922,
13197,13495,13770`) are discharged by the generic `piOf_upper_rect` below
(each obligation's `0.001 ≤ s.re` hypothesis gives `0 ≤ s.re` by `linarith`).

Row s-values used: bottom `y=(0.01,0.2)` → `im=0.105` → `re=0.395`;
row2 `y=(0.1,0.3)` → `im=0.2` → `re=0.3`;
row3 `y=(0.2,0.4)` → `im=0.3` → `re=0.2`;
row4 `y=(0.3,0.49)` → `im=0.395` → `re=0.105`
(banked `RXX_y0/y1`: `:1138,:1257,:1435,:1521,:1607,:1693,:1779,:1865,:1951,
:2037,:2123` bottom; `:2498`–`:3254` row2; `:3340`–`:4096` row3;
`:4182`–`:4938` row4).

## BANKED TECHNIQUE (reproved locally; `interval_arith` NOT imported)

* `cutR10_endpoint_pi_lower` / `cutL10_endpoint_pi_lower` shape
  (`door3_cutR10_ballsup.lean:1455`, `door3_cutL10_remainders.lean:1091`):
  `7/10 ≤ π^(-1/4)` from `π ≤ (10/7)^4 = 10000/2401` (via `Real.pi_lt_d2`)
  through `Complex.norm_cpow_eq_rpow_re_of_pos`.
* `CpowInterval.pi_rpow_quarter_le_two / pi_rpow_neg_quarter_ge_half`
  (`interval_arith.lean:197,217`; also `central_cover_assembly.lean:9662,9683`):
  subsumed by the stronger `7/10` chain (`7/10 > 1/2`).
* Per-center extraction: `‖piOf s‖ = π^(-s.re/2)` (`R02Pilot.pi_lower`
  `:9692`, `CellUniform.pi_lower_of_re` `interval_arith.lean:1752` shape).

Since every batch s-center has `s.re ≤ 1/2`, `-s.re/2 ≥ -1/4`, and `π > 1`,
`π^(-s.re/2) ≥ π^(-1/4) ≥ 7/10` uniformly — one generic lemma closes all
`0.7` floors, hence all `1/2` floors a fortiori. Tightest margin first
(bottom row `0.0977`), then row2, row3, row4.

## FALSE-FLOOR AUDIT: none. Every pi floor is TRUE (see TRUE column above);
no deficit recorded, nothing forced.
-/

noncomputable section

namespace Door3PremisePi

/-! ## Real core: `π^(1/4) ≤ 10/7`, hence `7/10 ≤ π^(-1/4)` (cutL10 pattern). -/

/-- `π^(1/4) ≤ 10/7` from `π ≤ (10/7)^4 = 10000/2401` via `Real.pi_lt_d2`. -/
theorem pi_pow_quarter_le_ten_sevenths :
    Real.pi ^ ((1 / 4 : ℝ)) ≤ (10 / 7 : ℝ) := by
  have hpi4 : Real.pi ≤ ((10 / 7 : ℝ) ^ (4 : ℕ)) := by
    have h := Real.pi_lt_d2
    have h4 : ((10 / 7 : ℝ) ^ (4 : ℕ)) = (10000 / 2401 : ℝ) := by norm_num
    rw [h4]
    norm_num at h ⊢
    linarith
  have h14nn : (0 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
  have hstep : Real.pi ^ ((1 / 4 : ℝ))
      ≤ ((((10 / 7 : ℝ) ^ (4 : ℕ))) ^ ((1 / 4 : ℝ))) :=
    Real.rpow_le_rpow (le_of_lt Real.pi_pos) hpi4 h14nn
  have heq : ((((10 / 7 : ℝ) ^ (4 : ℕ))) ^ ((1 / 4 : ℝ))) = (10 / 7 : ℝ) := by
    have hnn : (0 : ℝ) ≤ (10 / 7) := by norm_num
    calc ((((10 / 7 : ℝ) ^ (4 : ℕ))) ^ ((1 / 4 : ℝ)))
        = ((10 / 7) ^ ((((4 : ℕ)) : ℝ) * (1 / 4))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
      _ = ((10 / 7) ^ (1 : ℝ)) := by
          congr 1
          norm_num
      _ = (10 / 7) := Real.rpow_one _
  rw [heq] at hstep
  exact hstep

/-- `7/10 ≤ π^(-1/4)` by inversion of the quarter bound. -/
theorem pi_neg_quarter_ge_seven_tenths :
    (7 / 10 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
  have hposP : (0 : ℝ) < Real.pi ^ ((1 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have hmul : (7 / 10 : ℝ) * Real.pi ^ ((1 / 4 : ℝ)) ≤ 1 := by
    calc (7 / 10 : ℝ) * Real.pi ^ ((1 / 4 : ℝ)) ≤ (7 / 10) * (10 / 7) :=
          mul_le_mul_of_nonneg_left pi_pow_quarter_le_ten_sevenths (by norm_num)
      _ = 1 := by norm_num
  rw [Real.rpow_neg (le_of_lt Real.pi_pos), ← one_div, le_div_iff₀ hposP]
  exact hmul

/-! ## Generic `piOf` bridge + floors/upper (all explicit binders). -/

/-- Norm extraction: `‖piOf s‖ = π^(-s.re/2)` (Re-only dependence). -/
theorem piOf_norm (s : ℂ) :
    ‖DerivCauchyBridge.piOf s‖ = Real.pi ^ (-(s.re) / 2) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-(s / 2))
  unfold DerivCauchyBridge.piOf
  rw [h]
  congr 1
  rw [Complex.neg_re, Complex.div_ofNat_re]
  ring

/-- Uniform lower `7/10 ≤ ‖piOf s‖` for every `s.re ≤ 1/2`
(covers all 40 batch s-centers; tightest instance `re = 0.395`). -/
theorem piOf_ge_of_re_le_half (s : ℂ) (hre : s.re ≤ (1 / 2 : ℝ)) :
    (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf s‖ := by
  rw [piOf_norm]
  have hexp : (-(1 / 4 : ℝ)) ≤ -(s.re) / 2 := by linarith
  calc (7 / 10 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := pi_neg_quarter_ge_seven_tenths
    _ ≤ Real.pi ^ (-(s.re) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp

/-- Half-floor corollary (batch-C/D premise shape `1/2 ≤ ‖piOf s‖`). -/
theorem piOf_half_of_re_le_half (s : ℂ) (hre : s.re ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf s‖ := by
  have h := piOf_ge_of_re_le_half s hre
  norm_num at h ⊢
  linarith

/-- Uniform upper `‖piOf s‖ ≤ 1` for every `0 ≤ s.re`. -/
theorem piOf_le_one_of_re_nonneg (s : ℂ) (hre : (0 : ℝ) ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 := by
  rw [piOf_norm]
  have hle : (-(s.re) / 2 : ℝ) ≤ 0 := by linarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact Real.rpow_le_one_of_one_le_of_nonpos hpi1 hle

/-- Generic rect-upper discharger: every `R31–R40_pi_upper_obligation`
(`∀ s` on the rect, cap `1`) follows, since each gives `0 ≤ s.re`. -/
theorem piOf_upper_rect (s : ℂ) (hre : (0 : ℝ) ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : ℝ) :=
  piOf_le_one_of_re_nonneg s hre

/-! ## Bottom row (`re = 0.395`, TRUE `≈ 0.7977`, margin `0.0977` — tightest).
Discharges `BA00/BA03/BA04_piLower_obligation` (batch A, floor `0.7`),
`BE_piLower_R01/R05–R10` (batch E, floor `0.7`), and the R02 banked floor. -/

noncomputable def sPiR00 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center
theorem sRePi_R00 : sPiR00.re = 0.395 := by
  have him : (CentralCoverAssembly.R00.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R00_x0, CentralCoverAssembly.R00_x1,
      CentralCoverAssembly.R00_y0, CentralCoverAssembly.R00_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center).re =
      1 / 2 - (CentralCoverAssembly.R00.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR00
  rw [hsre, him]
  norm_num
theorem premPi_R00_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR00‖ :=
  piOf_ge_of_re_le_half sPiR00 (by rw [sRePi_R00]; norm_num)
theorem premPi_R00_le : ‖DerivCauchyBridge.piOf sPiR00‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR00 (by rw [sRePi_R00]; norm_num)

noncomputable def sPiR01 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R01.center
theorem sRePi_R01 : sPiR01.re = 0.395 := by
  have him : (CentralCoverAssembly.R01.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R01_x0, CentralCoverAssembly.R01_x1,
      CentralCoverAssembly.R01_y0, CentralCoverAssembly.R01_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R01.center).re =
      1 / 2 - (CentralCoverAssembly.R01.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR01
  rw [hsre, him]
  norm_num
theorem premPi_R01_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR01‖ :=
  piOf_ge_of_re_le_half sPiR01 (by rw [sRePi_R01]; norm_num)
theorem premPi_R01_le : ‖DerivCauchyBridge.piOf sPiR01‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR01 (by rw [sRePi_R01]; norm_num)

noncomputable def sPiR02 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center
theorem sRePi_R02 : sPiR02.re = 0.395 := by
  have him : (CentralCoverAssembly.R02.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R02_x0, CentralCoverAssembly.R02_x1,
      CentralCoverAssembly.R02_y0, CentralCoverAssembly.R02_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center).re =
      1 / 2 - (CentralCoverAssembly.R02.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR02
  rw [hsre, him]
  norm_num
theorem premPi_R02_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR02‖ :=
  piOf_ge_of_re_le_half sPiR02 (by rw [sRePi_R02]; norm_num)
theorem premPi_R02_le : ‖DerivCauchyBridge.piOf sPiR02‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR02 (by rw [sRePi_R02]; norm_num)

noncomputable def sPiR03 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R03.center
theorem sRePi_R03 : sPiR03.re = 0.395 := by
  have him : (CentralCoverAssembly.R03.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R03_x0, CentralCoverAssembly.R03_x1,
      CentralCoverAssembly.R03_y0, CentralCoverAssembly.R03_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R03.center).re =
      1 / 2 - (CentralCoverAssembly.R03.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR03
  rw [hsre, him]
  norm_num
theorem premPi_R03_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR03‖ :=
  piOf_ge_of_re_le_half sPiR03 (by rw [sRePi_R03]; norm_num)
theorem premPi_R03_le : ‖DerivCauchyBridge.piOf sPiR03‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR03 (by rw [sRePi_R03]; norm_num)

noncomputable def sPiR04 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R04.center
theorem sRePi_R04 : sPiR04.re = 0.395 := by
  have him : (CentralCoverAssembly.R04.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R04_x0, CentralCoverAssembly.R04_x1,
      CentralCoverAssembly.R04_y0, CentralCoverAssembly.R04_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R04.center).re =
      1 / 2 - (CentralCoverAssembly.R04.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR04
  rw [hsre, him]
  norm_num
theorem premPi_R04_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR04‖ :=
  piOf_ge_of_re_le_half sPiR04 (by rw [sRePi_R04]; norm_num)
theorem premPi_R04_le : ‖DerivCauchyBridge.piOf sPiR04‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR04 (by rw [sRePi_R04]; norm_num)

noncomputable def sPiR05 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R05.center
theorem sRePi_R05 : sPiR05.re = 0.395 := by
  have him : (CentralCoverAssembly.R05.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R05_x0, CentralCoverAssembly.R05_x1,
      CentralCoverAssembly.R05_y0, CentralCoverAssembly.R05_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R05.center).re =
      1 / 2 - (CentralCoverAssembly.R05.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR05
  rw [hsre, him]
  norm_num
theorem premPi_R05_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR05‖ :=
  piOf_ge_of_re_le_half sPiR05 (by rw [sRePi_R05]; norm_num)
theorem premPi_R05_le : ‖DerivCauchyBridge.piOf sPiR05‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR05 (by rw [sRePi_R05]; norm_num)

noncomputable def sPiR06 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R06.center
theorem sRePi_R06 : sPiR06.re = 0.395 := by
  have him : (CentralCoverAssembly.R06.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R06_x0, CentralCoverAssembly.R06_x1,
      CentralCoverAssembly.R06_y0, CentralCoverAssembly.R06_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R06.center).re =
      1 / 2 - (CentralCoverAssembly.R06.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR06
  rw [hsre, him]
  norm_num
theorem premPi_R06_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR06‖ :=
  piOf_ge_of_re_le_half sPiR06 (by rw [sRePi_R06]; norm_num)
theorem premPi_R06_le : ‖DerivCauchyBridge.piOf sPiR06‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR06 (by rw [sRePi_R06]; norm_num)

noncomputable def sPiR07 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R07.center
theorem sRePi_R07 : sPiR07.re = 0.395 := by
  have him : (CentralCoverAssembly.R07.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R07_x0, CentralCoverAssembly.R07_x1,
      CentralCoverAssembly.R07_y0, CentralCoverAssembly.R07_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R07.center).re =
      1 / 2 - (CentralCoverAssembly.R07.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR07
  rw [hsre, him]
  norm_num
theorem premPi_R07_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR07‖ :=
  piOf_ge_of_re_le_half sPiR07 (by rw [sRePi_R07]; norm_num)
theorem premPi_R07_le : ‖DerivCauchyBridge.piOf sPiR07‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR07 (by rw [sRePi_R07]; norm_num)

noncomputable def sPiR08 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R08.center
theorem sRePi_R08 : sPiR08.re = 0.395 := by
  have him : (CentralCoverAssembly.R08.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R08_x0, CentralCoverAssembly.R08_x1,
      CentralCoverAssembly.R08_y0, CentralCoverAssembly.R08_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R08.center).re =
      1 / 2 - (CentralCoverAssembly.R08.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR08
  rw [hsre, him]
  norm_num
theorem premPi_R08_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR08‖ :=
  piOf_ge_of_re_le_half sPiR08 (by rw [sRePi_R08]; norm_num)
theorem premPi_R08_le : ‖DerivCauchyBridge.piOf sPiR08‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR08 (by rw [sRePi_R08]; norm_num)

noncomputable def sPiR09 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R09.center
theorem sRePi_R09 : sPiR09.re = 0.395 := by
  have him : (CentralCoverAssembly.R09.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R09_x0, CentralCoverAssembly.R09_x1,
      CentralCoverAssembly.R09_y0, CentralCoverAssembly.R09_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R09.center).re =
      1 / 2 - (CentralCoverAssembly.R09.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR09
  rw [hsre, him]
  norm_num
theorem premPi_R09_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR09‖ :=
  piOf_ge_of_re_le_half sPiR09 (by rw [sRePi_R09]; norm_num)
theorem premPi_R09_le : ‖DerivCauchyBridge.piOf sPiR09‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR09 (by rw [sRePi_R09]; norm_num)

noncomputable def sPiR10 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R10.center
theorem sRePi_R10 : sPiR10.re = 0.395 := by
  have him : (CentralCoverAssembly.R10.center).im = 0.105 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R10_x0, CentralCoverAssembly.R10_x1,
      CentralCoverAssembly.R10_y0, CentralCoverAssembly.R10_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R10.center).re =
      1 / 2 - (CentralCoverAssembly.R10.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR10
  rw [hsre, him]
  norm_num
theorem premPi_R10_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR10‖ :=
  piOf_ge_of_re_le_half sPiR10 (by rw [sRePi_R10]; norm_num)
theorem premPi_R10_le : ‖DerivCauchyBridge.piOf sPiR10‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR10 (by rw [sRePi_R10]; norm_num)

/-! ## Second row R11–R20 (`re = 0.3`, TRUE `≈ 0.8422`, margin `0.1422`).
Batch B states no pi-factor premises (whole-center form); these ten are
remainder coverage so every batch s-center carries a pi certificate. -/

noncomputable def sPiR11 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R11.center
theorem sRePi_R11 : sPiR11.re = 0.3 := by
  have him : (CentralCoverAssembly.R11.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R11_x0, CentralCoverAssembly.R11_x1,
      CentralCoverAssembly.R11_y0, CentralCoverAssembly.R11_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R11.center).re =
      1 / 2 - (CentralCoverAssembly.R11.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR11
  rw [hsre, him]
  norm_num
theorem premPi_R11_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR11‖ :=
  piOf_ge_of_re_le_half sPiR11 (by rw [sRePi_R11]; norm_num)
theorem premPi_R11_le : ‖DerivCauchyBridge.piOf sPiR11‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR11 (by rw [sRePi_R11]; norm_num)

noncomputable def sPiR12 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R12.center
theorem sRePi_R12 : sPiR12.re = 0.3 := by
  have him : (CentralCoverAssembly.R12.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R12_x0, CentralCoverAssembly.R12_x1,
      CentralCoverAssembly.R12_y0, CentralCoverAssembly.R12_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R12.center).re =
      1 / 2 - (CentralCoverAssembly.R12.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR12
  rw [hsre, him]
  norm_num
theorem premPi_R12_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR12‖ :=
  piOf_ge_of_re_le_half sPiR12 (by rw [sRePi_R12]; norm_num)
theorem premPi_R12_le : ‖DerivCauchyBridge.piOf sPiR12‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR12 (by rw [sRePi_R12]; norm_num)

noncomputable def sPiR13 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R13.center
theorem sRePi_R13 : sPiR13.re = 0.3 := by
  have him : (CentralCoverAssembly.R13.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R13_x0, CentralCoverAssembly.R13_x1,
      CentralCoverAssembly.R13_y0, CentralCoverAssembly.R13_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R13.center).re =
      1 / 2 - (CentralCoverAssembly.R13.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR13
  rw [hsre, him]
  norm_num
theorem premPi_R13_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR13‖ :=
  piOf_ge_of_re_le_half sPiR13 (by rw [sRePi_R13]; norm_num)
theorem premPi_R13_le : ‖DerivCauchyBridge.piOf sPiR13‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR13 (by rw [sRePi_R13]; norm_num)

noncomputable def sPiR14 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R14.center
theorem sRePi_R14 : sPiR14.re = 0.3 := by
  have him : (CentralCoverAssembly.R14.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R14_x0, CentralCoverAssembly.R14_x1,
      CentralCoverAssembly.R14_y0, CentralCoverAssembly.R14_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R14.center).re =
      1 / 2 - (CentralCoverAssembly.R14.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR14
  rw [hsre, him]
  norm_num
theorem premPi_R14_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR14‖ :=
  piOf_ge_of_re_le_half sPiR14 (by rw [sRePi_R14]; norm_num)
theorem premPi_R14_le : ‖DerivCauchyBridge.piOf sPiR14‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR14 (by rw [sRePi_R14]; norm_num)

noncomputable def sPiR15 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R15.center
theorem sRePi_R15 : sPiR15.re = 0.3 := by
  have him : (CentralCoverAssembly.R15.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R15_x0, CentralCoverAssembly.R15_x1,
      CentralCoverAssembly.R15_y0, CentralCoverAssembly.R15_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R15.center).re =
      1 / 2 - (CentralCoverAssembly.R15.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR15
  rw [hsre, him]
  norm_num
theorem premPi_R15_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR15‖ :=
  piOf_ge_of_re_le_half sPiR15 (by rw [sRePi_R15]; norm_num)
theorem premPi_R15_le : ‖DerivCauchyBridge.piOf sPiR15‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR15 (by rw [sRePi_R15]; norm_num)

noncomputable def sPiR16 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R16.center
theorem sRePi_R16 : sPiR16.re = 0.3 := by
  have him : (CentralCoverAssembly.R16.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R16_x0, CentralCoverAssembly.R16_x1,
      CentralCoverAssembly.R16_y0, CentralCoverAssembly.R16_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R16.center).re =
      1 / 2 - (CentralCoverAssembly.R16.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR16
  rw [hsre, him]
  norm_num
theorem premPi_R16_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR16‖ :=
  piOf_ge_of_re_le_half sPiR16 (by rw [sRePi_R16]; norm_num)
theorem premPi_R16_le : ‖DerivCauchyBridge.piOf sPiR16‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR16 (by rw [sRePi_R16]; norm_num)

noncomputable def sPiR17 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R17.center
theorem sRePi_R17 : sPiR17.re = 0.3 := by
  have him : (CentralCoverAssembly.R17.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R17_x0, CentralCoverAssembly.R17_x1,
      CentralCoverAssembly.R17_y0, CentralCoverAssembly.R17_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R17.center).re =
      1 / 2 - (CentralCoverAssembly.R17.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR17
  rw [hsre, him]
  norm_num
theorem premPi_R17_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR17‖ :=
  piOf_ge_of_re_le_half sPiR17 (by rw [sRePi_R17]; norm_num)
theorem premPi_R17_le : ‖DerivCauchyBridge.piOf sPiR17‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR17 (by rw [sRePi_R17]; norm_num)

noncomputable def sPiR18 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R18.center
theorem sRePi_R18 : sPiR18.re = 0.3 := by
  have him : (CentralCoverAssembly.R18.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R18_x0, CentralCoverAssembly.R18_x1,
      CentralCoverAssembly.R18_y0, CentralCoverAssembly.R18_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R18.center).re =
      1 / 2 - (CentralCoverAssembly.R18.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR18
  rw [hsre, him]
  norm_num
theorem premPi_R18_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR18‖ :=
  piOf_ge_of_re_le_half sPiR18 (by rw [sRePi_R18]; norm_num)
theorem premPi_R18_le : ‖DerivCauchyBridge.piOf sPiR18‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR18 (by rw [sRePi_R18]; norm_num)

noncomputable def sPiR19 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R19.center
theorem sRePi_R19 : sPiR19.re = 0.3 := by
  have him : (CentralCoverAssembly.R19.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R19_x0, CentralCoverAssembly.R19_x1,
      CentralCoverAssembly.R19_y0, CentralCoverAssembly.R19_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R19.center).re =
      1 / 2 - (CentralCoverAssembly.R19.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR19
  rw [hsre, him]
  norm_num
theorem premPi_R19_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR19‖ :=
  piOf_ge_of_re_le_half sPiR19 (by rw [sRePi_R19]; norm_num)
theorem premPi_R19_le : ‖DerivCauchyBridge.piOf sPiR19‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR19 (by rw [sRePi_R19]; norm_num)

noncomputable def sPiR20 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R20.center
theorem sRePi_R20 : sPiR20.re = 0.3 := by
  have him : (CentralCoverAssembly.R20.center).im = 0.2 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R20_x0, CentralCoverAssembly.R20_x1,
      CentralCoverAssembly.R20_y0, CentralCoverAssembly.R20_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R20.center).re =
      1 / 2 - (CentralCoverAssembly.R20.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR20
  rw [hsre, him]
  norm_num
theorem premPi_R20_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR20‖ :=
  piOf_ge_of_re_le_half sPiR20 (by rw [sRePi_R20]; norm_num)
theorem premPi_R20_le : ‖DerivCauchyBridge.piOf sPiR20‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR20 (by rw [sRePi_R20]; norm_num)

/-! ## Third row R21–R30 (`re = 0.2`, TRUE `≈ 0.8919`).
Discharges `BD_piLower_R21–R30` (batch D, floor `1/2`) via the `_half`
corollaries; the `7/10` lemmas carry margin `0.1919`. -/

noncomputable def sPiR21 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R21.center
theorem sRePi_R21 : sPiR21.re = 0.2 := by
  have him : (CentralCoverAssembly.R21.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R21_x0, CentralCoverAssembly.R21_x1,
      CentralCoverAssembly.R21_y0, CentralCoverAssembly.R21_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R21.center).re =
      1 / 2 - (CentralCoverAssembly.R21.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR21
  rw [hsre, him]
  norm_num
theorem premPi_R21_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR21‖ :=
  piOf_ge_of_re_le_half sPiR21 (by rw [sRePi_R21]; norm_num)
theorem premPi_R21_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR21‖ :=
  piOf_half_of_re_le_half sPiR21 (by rw [sRePi_R21]; norm_num)
theorem premPi_R21_le : ‖DerivCauchyBridge.piOf sPiR21‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR21 (by rw [sRePi_R21]; norm_num)

noncomputable def sPiR22 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R22.center
theorem sRePi_R22 : sPiR22.re = 0.2 := by
  have him : (CentralCoverAssembly.R22.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R22_x0, CentralCoverAssembly.R22_x1,
      CentralCoverAssembly.R22_y0, CentralCoverAssembly.R22_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R22.center).re =
      1 / 2 - (CentralCoverAssembly.R22.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR22
  rw [hsre, him]
  norm_num
theorem premPi_R22_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR22‖ :=
  piOf_ge_of_re_le_half sPiR22 (by rw [sRePi_R22]; norm_num)
theorem premPi_R22_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR22‖ :=
  piOf_half_of_re_le_half sPiR22 (by rw [sRePi_R22]; norm_num)
theorem premPi_R22_le : ‖DerivCauchyBridge.piOf sPiR22‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR22 (by rw [sRePi_R22]; norm_num)

noncomputable def sPiR23 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R23.center
theorem sRePi_R23 : sPiR23.re = 0.2 := by
  have him : (CentralCoverAssembly.R23.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R23_x0, CentralCoverAssembly.R23_x1,
      CentralCoverAssembly.R23_y0, CentralCoverAssembly.R23_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R23.center).re =
      1 / 2 - (CentralCoverAssembly.R23.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR23
  rw [hsre, him]
  norm_num
theorem premPi_R23_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR23‖ :=
  piOf_ge_of_re_le_half sPiR23 (by rw [sRePi_R23]; norm_num)
theorem premPi_R23_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR23‖ :=
  piOf_half_of_re_le_half sPiR23 (by rw [sRePi_R23]; norm_num)
theorem premPi_R23_le : ‖DerivCauchyBridge.piOf sPiR23‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR23 (by rw [sRePi_R23]; norm_num)

noncomputable def sPiR24 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R24.center
theorem sRePi_R24 : sPiR24.re = 0.2 := by
  have him : (CentralCoverAssembly.R24.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R24_x0, CentralCoverAssembly.R24_x1,
      CentralCoverAssembly.R24_y0, CentralCoverAssembly.R24_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R24.center).re =
      1 / 2 - (CentralCoverAssembly.R24.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR24
  rw [hsre, him]
  norm_num
theorem premPi_R24_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR24‖ :=
  piOf_ge_of_re_le_half sPiR24 (by rw [sRePi_R24]; norm_num)
theorem premPi_R24_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR24‖ :=
  piOf_half_of_re_le_half sPiR24 (by rw [sRePi_R24]; norm_num)
theorem premPi_R24_le : ‖DerivCauchyBridge.piOf sPiR24‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR24 (by rw [sRePi_R24]; norm_num)

noncomputable def sPiR25 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R25.center
theorem sRePi_R25 : sPiR25.re = 0.2 := by
  have him : (CentralCoverAssembly.R25.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R25_x0, CentralCoverAssembly.R25_x1,
      CentralCoverAssembly.R25_y0, CentralCoverAssembly.R25_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R25.center).re =
      1 / 2 - (CentralCoverAssembly.R25.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR25
  rw [hsre, him]
  norm_num
theorem premPi_R25_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR25‖ :=
  piOf_ge_of_re_le_half sPiR25 (by rw [sRePi_R25]; norm_num)
theorem premPi_R25_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR25‖ :=
  piOf_half_of_re_le_half sPiR25 (by rw [sRePi_R25]; norm_num)
theorem premPi_R25_le : ‖DerivCauchyBridge.piOf sPiR25‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR25 (by rw [sRePi_R25]; norm_num)

noncomputable def sPiR26 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R26.center
theorem sRePi_R26 : sPiR26.re = 0.2 := by
  have him : (CentralCoverAssembly.R26.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R26_x0, CentralCoverAssembly.R26_x1,
      CentralCoverAssembly.R26_y0, CentralCoverAssembly.R26_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R26.center).re =
      1 / 2 - (CentralCoverAssembly.R26.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR26
  rw [hsre, him]
  norm_num
theorem premPi_R26_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR26‖ :=
  piOf_ge_of_re_le_half sPiR26 (by rw [sRePi_R26]; norm_num)
theorem premPi_R26_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR26‖ :=
  piOf_half_of_re_le_half sPiR26 (by rw [sRePi_R26]; norm_num)
theorem premPi_R26_le : ‖DerivCauchyBridge.piOf sPiR26‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR26 (by rw [sRePi_R26]; norm_num)

noncomputable def sPiR27 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R27.center
theorem sRePi_R27 : sPiR27.re = 0.2 := by
  have him : (CentralCoverAssembly.R27.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R27_x0, CentralCoverAssembly.R27_x1,
      CentralCoverAssembly.R27_y0, CentralCoverAssembly.R27_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R27.center).re =
      1 / 2 - (CentralCoverAssembly.R27.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR27
  rw [hsre, him]
  norm_num
theorem premPi_R27_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR27‖ :=
  piOf_ge_of_re_le_half sPiR27 (by rw [sRePi_R27]; norm_num)
theorem premPi_R27_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR27‖ :=
  piOf_half_of_re_le_half sPiR27 (by rw [sRePi_R27]; norm_num)
theorem premPi_R27_le : ‖DerivCauchyBridge.piOf sPiR27‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR27 (by rw [sRePi_R27]; norm_num)

noncomputable def sPiR28 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R28.center
theorem sRePi_R28 : sPiR28.re = 0.2 := by
  have him : (CentralCoverAssembly.R28.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R28_x0, CentralCoverAssembly.R28_x1,
      CentralCoverAssembly.R28_y0, CentralCoverAssembly.R28_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R28.center).re =
      1 / 2 - (CentralCoverAssembly.R28.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR28
  rw [hsre, him]
  norm_num
theorem premPi_R28_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR28‖ :=
  piOf_ge_of_re_le_half sPiR28 (by rw [sRePi_R28]; norm_num)
theorem premPi_R28_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR28‖ :=
  piOf_half_of_re_le_half sPiR28 (by rw [sRePi_R28]; norm_num)
theorem premPi_R28_le : ‖DerivCauchyBridge.piOf sPiR28‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR28 (by rw [sRePi_R28]; norm_num)

noncomputable def sPiR29 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R29.center
theorem sRePi_R29 : sPiR29.re = 0.2 := by
  have him : (CentralCoverAssembly.R29.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R29_x0, CentralCoverAssembly.R29_x1,
      CentralCoverAssembly.R29_y0, CentralCoverAssembly.R29_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R29.center).re =
      1 / 2 - (CentralCoverAssembly.R29.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR29
  rw [hsre, him]
  norm_num
theorem premPi_R29_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR29‖ :=
  piOf_ge_of_re_le_half sPiR29 (by rw [sRePi_R29]; norm_num)
theorem premPi_R29_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR29‖ :=
  piOf_half_of_re_le_half sPiR29 (by rw [sRePi_R29]; norm_num)
theorem premPi_R29_le : ‖DerivCauchyBridge.piOf sPiR29‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR29 (by rw [sRePi_R29]; norm_num)

noncomputable def sPiR30 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R30.center
theorem sRePi_R30 : sPiR30.re = 0.2 := by
  have him : (CentralCoverAssembly.R30.center).im = 0.3 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R30_x0, CentralCoverAssembly.R30_x1,
      CentralCoverAssembly.R30_y0, CentralCoverAssembly.R30_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R30.center).re =
      1 / 2 - (CentralCoverAssembly.R30.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR30
  rw [hsre, him]
  norm_num
theorem premPi_R30_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR30‖ :=
  piOf_ge_of_re_le_half sPiR30 (by rw [sRePi_R30]; norm_num)
theorem premPi_R30_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR30‖ :=
  piOf_half_of_re_le_half sPiR30 (by rw [sRePi_R30]; norm_num)
theorem premPi_R30_le : ‖DerivCauchyBridge.piOf sPiR30‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR30 (by rw [sRePi_R30]; norm_num)

/-! ## Fourth row R31–R40 (`re = 0.105`, TRUE `≈ 0.9417`).
Discharges `BC_piLower_R31–R40` (batch C, floor `1/2`) via the `_half`
corollaries; the `7/10` lemmas carry margin `0.2417`. -/

noncomputable def sPiR31 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R31.center
theorem sRePi_R31 : sPiR31.re = 0.105 := by
  have him : (CentralCoverAssembly.R31.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R31_x0, CentralCoverAssembly.R31_x1,
      CentralCoverAssembly.R31_y0, CentralCoverAssembly.R31_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R31.center).re =
      1 / 2 - (CentralCoverAssembly.R31.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR31
  rw [hsre, him]
  norm_num
theorem premPi_R31_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR31‖ :=
  piOf_ge_of_re_le_half sPiR31 (by rw [sRePi_R31]; norm_num)
theorem premPi_R31_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR31‖ :=
  piOf_half_of_re_le_half sPiR31 (by rw [sRePi_R31]; norm_num)
theorem premPi_R31_le : ‖DerivCauchyBridge.piOf sPiR31‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR31 (by rw [sRePi_R31]; norm_num)

noncomputable def sPiR32 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R32.center
theorem sRePi_R32 : sPiR32.re = 0.105 := by
  have him : (CentralCoverAssembly.R32.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R32_x0, CentralCoverAssembly.R32_x1,
      CentralCoverAssembly.R32_y0, CentralCoverAssembly.R32_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R32.center).re =
      1 / 2 - (CentralCoverAssembly.R32.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR32
  rw [hsre, him]
  norm_num
theorem premPi_R32_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR32‖ :=
  piOf_ge_of_re_le_half sPiR32 (by rw [sRePi_R32]; norm_num)
theorem premPi_R32_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR32‖ :=
  piOf_half_of_re_le_half sPiR32 (by rw [sRePi_R32]; norm_num)
theorem premPi_R32_le : ‖DerivCauchyBridge.piOf sPiR32‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR32 (by rw [sRePi_R32]; norm_num)

noncomputable def sPiR33 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R33.center
theorem sRePi_R33 : sPiR33.re = 0.105 := by
  have him : (CentralCoverAssembly.R33.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R33_x0, CentralCoverAssembly.R33_x1,
      CentralCoverAssembly.R33_y0, CentralCoverAssembly.R33_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R33.center).re =
      1 / 2 - (CentralCoverAssembly.R33.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR33
  rw [hsre, him]
  norm_num
theorem premPi_R33_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR33‖ :=
  piOf_ge_of_re_le_half sPiR33 (by rw [sRePi_R33]; norm_num)
theorem premPi_R33_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR33‖ :=
  piOf_half_of_re_le_half sPiR33 (by rw [sRePi_R33]; norm_num)
theorem premPi_R33_le : ‖DerivCauchyBridge.piOf sPiR33‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR33 (by rw [sRePi_R33]; norm_num)

noncomputable def sPiR34 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R34.center
theorem sRePi_R34 : sPiR34.re = 0.105 := by
  have him : (CentralCoverAssembly.R34.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R34_x0, CentralCoverAssembly.R34_x1,
      CentralCoverAssembly.R34_y0, CentralCoverAssembly.R34_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R34.center).re =
      1 / 2 - (CentralCoverAssembly.R34.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR34
  rw [hsre, him]
  norm_num
theorem premPi_R34_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR34‖ :=
  piOf_ge_of_re_le_half sPiR34 (by rw [sRePi_R34]; norm_num)
theorem premPi_R34_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR34‖ :=
  piOf_half_of_re_le_half sPiR34 (by rw [sRePi_R34]; norm_num)
theorem premPi_R34_le : ‖DerivCauchyBridge.piOf sPiR34‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR34 (by rw [sRePi_R34]; norm_num)

noncomputable def sPiR35 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R35.center
theorem sRePi_R35 : sPiR35.re = 0.105 := by
  have him : (CentralCoverAssembly.R35.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R35_x0, CentralCoverAssembly.R35_x1,
      CentralCoverAssembly.R35_y0, CentralCoverAssembly.R35_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R35.center).re =
      1 / 2 - (CentralCoverAssembly.R35.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR35
  rw [hsre, him]
  norm_num
theorem premPi_R35_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR35‖ :=
  piOf_ge_of_re_le_half sPiR35 (by rw [sRePi_R35]; norm_num)
theorem premPi_R35_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR35‖ :=
  piOf_half_of_re_le_half sPiR35 (by rw [sRePi_R35]; norm_num)
theorem premPi_R35_le : ‖DerivCauchyBridge.piOf sPiR35‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR35 (by rw [sRePi_R35]; norm_num)

noncomputable def sPiR36 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R36.center
theorem sRePi_R36 : sPiR36.re = 0.105 := by
  have him : (CentralCoverAssembly.R36.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R36_x0, CentralCoverAssembly.R36_x1,
      CentralCoverAssembly.R36_y0, CentralCoverAssembly.R36_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R36.center).re =
      1 / 2 - (CentralCoverAssembly.R36.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR36
  rw [hsre, him]
  norm_num
theorem premPi_R36_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR36‖ :=
  piOf_ge_of_re_le_half sPiR36 (by rw [sRePi_R36]; norm_num)
theorem premPi_R36_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR36‖ :=
  piOf_half_of_re_le_half sPiR36 (by rw [sRePi_R36]; norm_num)
theorem premPi_R36_le : ‖DerivCauchyBridge.piOf sPiR36‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR36 (by rw [sRePi_R36]; norm_num)

noncomputable def sPiR37 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R37.center
theorem sRePi_R37 : sPiR37.re = 0.105 := by
  have him : (CentralCoverAssembly.R37.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R37_x0, CentralCoverAssembly.R37_x1,
      CentralCoverAssembly.R37_y0, CentralCoverAssembly.R37_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R37.center).re =
      1 / 2 - (CentralCoverAssembly.R37.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR37
  rw [hsre, him]
  norm_num
theorem premPi_R37_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR37‖ :=
  piOf_ge_of_re_le_half sPiR37 (by rw [sRePi_R37]; norm_num)
theorem premPi_R37_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR37‖ :=
  piOf_half_of_re_le_half sPiR37 (by rw [sRePi_R37]; norm_num)
theorem premPi_R37_le : ‖DerivCauchyBridge.piOf sPiR37‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR37 (by rw [sRePi_R37]; norm_num)

noncomputable def sPiR38 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R38.center
theorem sRePi_R38 : sPiR38.re = 0.105 := by
  have him : (CentralCoverAssembly.R38.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R38_x0, CentralCoverAssembly.R38_x1,
      CentralCoverAssembly.R38_y0, CentralCoverAssembly.R38_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R38.center).re =
      1 / 2 - (CentralCoverAssembly.R38.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR38
  rw [hsre, him]
  norm_num
theorem premPi_R38_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR38‖ :=
  piOf_ge_of_re_le_half sPiR38 (by rw [sRePi_R38]; norm_num)
theorem premPi_R38_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR38‖ :=
  piOf_half_of_re_le_half sPiR38 (by rw [sRePi_R38]; norm_num)
theorem premPi_R38_le : ‖DerivCauchyBridge.piOf sPiR38‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR38 (by rw [sRePi_R38]; norm_num)

noncomputable def sPiR39 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R39.center
theorem sRePi_R39 : sPiR39.re = 0.105 := by
  have him : (CentralCoverAssembly.R39.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R39_x0, CentralCoverAssembly.R39_x1,
      CentralCoverAssembly.R39_y0, CentralCoverAssembly.R39_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R39.center).re =
      1 / 2 - (CentralCoverAssembly.R39.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR39
  rw [hsre, him]
  norm_num
theorem premPi_R39_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR39‖ :=
  piOf_ge_of_re_le_half sPiR39 (by rw [sRePi_R39]; norm_num)
theorem premPi_R39_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR39‖ :=
  piOf_half_of_re_le_half sPiR39 (by rw [sRePi_R39]; norm_num)
theorem premPi_R39_le : ‖DerivCauchyBridge.piOf sPiR39‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR39 (by rw [sRePi_R39]; norm_num)

noncomputable def sPiR40 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R40.center
theorem sRePi_R40 : sPiR40.re = 0.105 := by
  have him : (CentralCoverAssembly.R40.center).im = 0.395 := by
    unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num
  have hsre : ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R40.center).re =
      1 / 2 - (CentralCoverAssembly.R40.center).im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  unfold sPiR40
  rw [hsre, him]
  norm_num
theorem premPi_R40_ge : (7 / 10 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR40‖ :=
  piOf_ge_of_re_le_half sPiR40 (by rw [sRePi_R40]; norm_num)
theorem premPi_R40_half : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sPiR40‖ :=
  piOf_half_of_re_le_half sPiR40 (by rw [sRePi_R40]; norm_num)
theorem premPi_R40_le : ‖DerivCauchyBridge.piOf sPiR40‖ ≤ 1 :=
  piOf_le_one_of_re_nonneg sPiR40 (by rw [sRePi_R40]; norm_num)

end Door3PremisePi
