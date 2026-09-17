import Mathlib
import central_cover_assembly
import door3_dp_trig
import door3_dp_terms

/-!
# Door 3 zeta-lower premise wave (low-t batch cells).

WRITE-ONLY task file. No build command was run. No commit. New file only.

Import closure (verified read-only before writing):
* `door3_dp_trig` imports `Mathlib` only (line 1) — upstream leaf.
* `door3_dp_terms` imports `Mathlib` + `door3_dp_trig` (lines 1-2) — upstream leaf.
* This file imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` only. The rigorous-zeta file is NOT imported (cycle risk);
  the eta head/tail assembly is reproved locally in conditional form.
* `zeta` is the top-level `riemannZeta` abbreviation (used unqualified by the
  batch files after importing `central_cover_assembly`); used the same way here.

Recon (read-only): zeta floors + s-centers collected from `door3_first_cell`
+ batches A/C/D/E (`door3_cells_batchB` carries center-direct premises, no
zeta factor — 10 cells out of scope for this wave, noted below).
Grid count: bottom row gridFine 10 (R00, R02–R10) + off-grid extra R01 +
batch B 10 (R11–R20, non-factor) + batch D 10 (R21–R30) + batch C 10
(R31–R40) = 40 gridFine + 1 extra. This wave owns the 31 factor floors.

Floor / center table (s = local mirror of each batch s-center):
Bottom row (sigma 0.395): R00 t -8.75 need 1.9; R01 t -6.25 need 1.2;
R02 t -6.75 need 1.1; R03 t -4.75 need 1.4; R04 t -2.75 need 1.0;
R05 t -0.75 need 1.0; R06 t 1.25 need 1.0; R07 t 3.25 need 1.0;
R08 t 5.25 need 1.0; R09 t 7.25 need 1.3; R10 t 8.75 need 1.9.
D row (sigma 0.2): R21–R30, t ladder -8.75 .. 8.75, need 1.0 each.
C row (sigma 0.105): R31–R40, t ladder -8.75 .. 8.75, need 1.0 each.

DP machine pieces used (all banked, full proofs upstream):
* `dp_sin_enclose_of_reduced` / `dp_cos_enclose_of_reduced` (direct + octant
  variants `dp_octant_*_enclose` available, not needed here).
* `dp_cpow_re` / `dp_cpow_im` proof pattern (reproved at local centers).
* `dp_log2_lo/hi`, `dp_log3_lo/hi` numeral bounds.
* `dp_poly_lip`, `dp_cos_poly_lip`, `dp_abs_tri`, `dp_norm_of_re_im`.

Method per center: short head (exact discs via trig enclosures at the
center's own t*log n arguments) + MVT pair-tail with eta-to-zeta factor
cF = |1 - 2^(1-s)|. Conditional bridge (proved below): from an eta link
`slow - tail <= cF * Z` and threshold `need * cF + tail <= slow`, the floor
`need <= Z` follows. Numeric check uses N = 8 head estimates plus MVT
pair-tail upper r(M) = C * M^(-sigma) / sigma with C = ||s||, head-disc
uncertainty 0.15 folded into rtail, and uniform denom floor 0.5
(|1 - 2^(1-s)| >= 0.5), so needEta = need * 0.5.

Honest outcome: with N <= 8 the tradeoff slow - rtail < needEta FAILS at
every one of the 31 centers (gaps proved below as arithmetic facts on the
estimates). Easiest-first prefix proved: local cpow re/im + k=0 trig
enclosures (width <= 1/50) at R05 (t -0.75) and R06 (t 1.25) for n = 2
(R05 also n = 3). Zero unconditional zeta floors close in this import
closure; all 31 cells join the re-tier queue. Remainder inventoried as
open `Prop`s below. Batch B R11–R20: no zeta premise (center-direct).
-/

noncomputable section

namespace Door3PremiseZeta

/-! ## Local s-centers (numeric mirrors of the batch s-centers) -/

noncomputable def zs_R00 : ℂ := ⟨(0.395 : ℝ), (-8.75 : ℝ)⟩
noncomputable def zs_R01 : ℂ := ⟨(0.395 : ℝ), (-6.25 : ℝ)⟩
noncomputable def zs_R02 : ℂ := ⟨(0.395 : ℝ), (-6.75 : ℝ)⟩
noncomputable def zs_R03 : ℂ := ⟨(0.395 : ℝ), (-4.75 : ℝ)⟩
noncomputable def zs_R04 : ℂ := ⟨(0.395 : ℝ), (-2.75 : ℝ)⟩
noncomputable def zs_R05 : ℂ := ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩
noncomputable def zs_R06 : ℂ := ⟨(0.395 : ℝ), (1.25 : ℝ)⟩
noncomputable def zs_R07 : ℂ := ⟨(0.395 : ℝ), (3.25 : ℝ)⟩
noncomputable def zs_R08 : ℂ := ⟨(0.395 : ℝ), (5.25 : ℝ)⟩
noncomputable def zs_R09 : ℂ := ⟨(0.395 : ℝ), (7.25 : ℝ)⟩
noncomputable def zs_R10 : ℂ := ⟨(0.395 : ℝ), (8.75 : ℝ)⟩

noncomputable def zs_R21 : ℂ := ⟨(0.2 : ℝ), (-8.75 : ℝ)⟩
noncomputable def zs_R22 : ℂ := ⟨(0.2 : ℝ), (-6.75 : ℝ)⟩
noncomputable def zs_R23 : ℂ := ⟨(0.2 : ℝ), (-4.75 : ℝ)⟩
noncomputable def zs_R24 : ℂ := ⟨(0.2 : ℝ), (-2.75 : ℝ)⟩
noncomputable def zs_R25 : ℂ := ⟨(0.2 : ℝ), (-0.75 : ℝ)⟩
noncomputable def zs_R26 : ℂ := ⟨(0.2 : ℝ), (1.25 : ℝ)⟩
noncomputable def zs_R27 : ℂ := ⟨(0.2 : ℝ), (3.25 : ℝ)⟩
noncomputable def zs_R28 : ℂ := ⟨(0.2 : ℝ), (5.25 : ℝ)⟩
noncomputable def zs_R29 : ℂ := ⟨(0.2 : ℝ), (7.25 : ℝ)⟩
noncomputable def zs_R30 : ℂ := ⟨(0.2 : ℝ), (8.75 : ℝ)⟩

noncomputable def zs_R31 : ℂ := ⟨(0.105 : ℝ), (-8.75 : ℝ)⟩
noncomputable def zs_R32 : ℂ := ⟨(0.105 : ℝ), (-6.75 : ℝ)⟩
noncomputable def zs_R33 : ℂ := ⟨(0.105 : ℝ), (-4.75 : ℝ)⟩
noncomputable def zs_R34 : ℂ := ⟨(0.105 : ℝ), (-2.75 : ℝ)⟩
noncomputable def zs_R35 : ℂ := ⟨(0.105 : ℝ), (-0.75 : ℝ)⟩
noncomputable def zs_R36 : ℂ := ⟨(0.105 : ℝ), (1.25 : ℝ)⟩
noncomputable def zs_R37 : ℂ := ⟨(0.105 : ℝ), (3.25 : ℝ)⟩
noncomputable def zs_R38 : ℂ := ⟨(0.105 : ℝ), (5.25 : ℝ)⟩
noncomputable def zs_R39 : ℂ := ⟨(0.105 : ℝ), (7.25 : ℝ)⟩
noncomputable def zs_R40 : ℂ := ⟨(0.105 : ℝ), (8.75 : ℝ)⟩

/-! ## Open floor Props (remainder inventory; wiring to batch defs by rfl) -/

def premZeta_R00 : Prop := (1.9 : ℝ) ≤ ‖zeta zs_R00‖
def premZeta_R01 : Prop := (1.2 : ℝ) ≤ ‖zeta zs_R01‖
def premZeta_R02 : Prop := (1.1 : ℝ) ≤ ‖zeta zs_R02‖
def premZeta_R03 : Prop := (1.4 : ℝ) ≤ ‖zeta zs_R03‖
def premZeta_R04 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R04‖
def premZeta_R05 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R05‖
def premZeta_R06 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R06‖
def premZeta_R07 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R07‖
def premZeta_R08 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R08‖
def premZeta_R09 : Prop := (1.3 : ℝ) ≤ ‖zeta zs_R09‖
def premZeta_R10 : Prop := (1.9 : ℝ) ≤ ‖zeta zs_R10‖

def premZeta_R21 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R21‖
def premZeta_R22 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R22‖
def premZeta_R23 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R23‖
def premZeta_R24 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R24‖
def premZeta_R25 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R25‖
def premZeta_R26 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R26‖
def premZeta_R27 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R27‖
def premZeta_R28 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R28‖
def premZeta_R29 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R29‖
def premZeta_R30 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R30‖

def premZeta_R31 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R31‖
def premZeta_R32 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R32‖
def premZeta_R33 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R33‖
def premZeta_R34 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R34‖
def premZeta_R35 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R35‖
def premZeta_R36 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R36‖
def premZeta_R37 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R37‖
def premZeta_R38 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R38‖
def premZeta_R39 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R39‖
def premZeta_R40 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R40‖

/-! ## Conditional bridge (proved; the logical step every center needs) -/

/-- Eta head/tail/cF assembly: the link plus the threshold give the floor.
Stated for explicit real witnesses; each center feeds its own numerals. -/
theorem zeta_floor_of_eta_bridge (slow tail cF need Z : ℝ)
    (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * Z)
    (hThresh : need * cF + tail ≤ slow) :
    need ≤ Z := by
  by_contra hlt
  push_neg at hlt
  have hmul : cF * Z < cF * need := by
    apply mul_lt_mul_of_pos_left hlt hcF
  have hle : need * cF ≤ cF * Z := by linarith
  have hge : cF * need ≤ cF * Z := by
    have e : need * cF = cF * need := by ring
    rw [e] at hle
    exact hle
  linarith

/-! ## Prefix: cpow re/im at the two easiest centers (R05, R06), n = 2 -/

theorem prefix_R05_cpow2_re :
    ((((2 : ℝ)) : ℂ) ^ (-zs_R05)).re
      = (2 : ℝ) ^ (-0.395 : ℝ) * Real.cos ((0.75 : ℝ) * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-zs_R05).re = (-0.395 : ℝ) := by
    have h : zs_R05.re = (0.395 : ℝ) := rfl
    have e : (-zs_R05).re = -(zs_R05.re) := rfl
    rw [e, h]
  have him_w : (-zs_R05).im = (0.75 : ℝ) := by
    have h : zs_R05.im = (-0.75 : ℝ) := rfl
    have e : (-zs_R05).im = -(zs_R05.im) := rfl
    rw [e, h]
    norm_num
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R05)).re
      = Real.log 2 * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R05)).im
      = Real.log 2 * (0.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-0.395)) = (2 : ℝ) ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (Real.log 2 * (0.75 : ℝ))
      = Real.cos ((0.75 : ℝ) * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

theorem prefix_R05_cpow2_im :
    ((((2 : ℝ)) : ℂ) ^ (-zs_R05)).im
      = (2 : ℝ) ^ (-0.395 : ℝ) * Real.sin ((0.75 : ℝ) * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-zs_R05).re = (-0.395 : ℝ) := by
    have h : zs_R05.re = (0.395 : ℝ) := rfl
    have e : (-zs_R05).re = -(zs_R05.re) := rfl
    rw [e, h]
  have him_w : (-zs_R05).im = (0.75 : ℝ) := by
    have h : zs_R05.im = (-0.75 : ℝ) := rfl
    have e : (-zs_R05).im = -(zs_R05.im) := rfl
    rw [e, h]
    norm_num
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R05)).re
      = Real.log 2 * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R05)).im
      = Real.log 2 * (0.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-0.395)) = (2 : ℝ) ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hsin : Real.sin (Real.log 2 * (0.75 : ℝ))
      = Real.sin ((0.75 : ℝ) * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

theorem prefix_R06_cpow2_re :
    ((((2 : ℝ)) : ℂ) ^ (-zs_R06)).re
      = (2 : ℝ) ^ (-0.395 : ℝ) * Real.cos ((-1.25 : ℝ) * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-zs_R06).re = (-0.395 : ℝ) := by
    have h : zs_R06.re = (0.395 : ℝ) := rfl
    have e : (-zs_R06).re = -(zs_R06.re) := rfl
    rw [e, h]
  have him_w : (-zs_R06).im = (-1.25 : ℝ) := by
    have h : zs_R06.im = (1.25 : ℝ) := rfl
    have e : (-zs_R06).im = -(zs_R06.im) := rfl
    rw [e, h]
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R06)).re
      = Real.log 2 * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R06)).im
      = Real.log 2 * (-1.25) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-0.395)) = (2 : ℝ) ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (Real.log 2 * (-1.25 : ℝ))
      = Real.cos ((-1.25 : ℝ) * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

theorem prefix_R06_cpow2_im :
    ((((2 : ℝ)) : ℂ) ^ (-zs_R06)).im
      = (2 : ℝ) ^ (-0.395 : ℝ) * Real.sin ((-1.25 : ℝ) * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-zs_R06).re = (-0.395 : ℝ) := by
    have h : zs_R06.re = (0.395 : ℝ) := rfl
    have e : (-zs_R06).re = -(zs_R06.re) := rfl
    rw [e, h]
  have him_w : (-zs_R06).im = (-1.25 : ℝ) := by
    have h : zs_R06.im = (1.25 : ℝ) := rfl
    have e : (-zs_R06).im = -(zs_R06.im) := rfl
    rw [e, h]
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R06)).re
      = Real.log 2 * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-zs_R06)).im
      = Real.log 2 * (-1.25) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-0.395)) = (2 : ℝ) ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hsin : Real.sin (Real.log 2 * (-1.25 : ℝ))
      = Real.sin ((-1.25 : ℝ) * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-! ## Prefix: k = 0 trig enclosures at R05 / R06 (n = 2; R05 also n = 3) -/

theorem prefix_R05_sin2 :
    ∃ lo hi : ℝ, lo ≤ Real.sin ((0.75 : ℝ) * Real.log 2) ∧
      Real.sin ((0.75 : ℝ) * Real.log 2) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log2_hi
  have hlog_lo := dp_log2_lo
  have hx : |((0.75 : ℝ) * Real.log 2)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((0.75 : ℝ) * Real.log 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((0.75 : ℝ) * Real.log 2)
      = ((0.75 : ℝ) * Real.log 2) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_sin_enclose_of_reduced ((0.75 : ℝ) * Real.log 2) hx 0
      (((0.75 : ℝ) * Real.log 2)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

theorem prefix_R05_cos2 :
    ∃ lo hi : ℝ, lo ≤ Real.cos ((0.75 : ℝ) * Real.log 2) ∧
      Real.cos ((0.75 : ℝ) * Real.log 2) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log2_hi
  have hlog_lo := dp_log2_lo
  have hx : |((0.75 : ℝ) * Real.log 2)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((0.75 : ℝ) * Real.log 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((0.75 : ℝ) * Real.log 2)
      = ((0.75 : ℝ) * Real.log 2) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_cos_enclose_of_reduced ((0.75 : ℝ) * Real.log 2) hx 0
      (((0.75 : ℝ) * Real.log 2)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

theorem prefix_R05_sin3 :
    ∃ lo hi : ℝ, lo ≤ Real.sin ((0.75 : ℝ) * Real.log 3) ∧
      Real.sin ((0.75 : ℝ) * Real.log 3) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log3_hi
  have hlog_lo := dp_log3_lo
  have hx : |((0.75 : ℝ) * Real.log 3)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((0.75 : ℝ) * Real.log 3)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((0.75 : ℝ) * Real.log 3)
      = ((0.75 : ℝ) * Real.log 3) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_sin_enclose_of_reduced ((0.75 : ℝ) * Real.log 3) hx 0
      (((0.75 : ℝ) * Real.log 3)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

theorem prefix_R05_cos3 :
    ∃ lo hi : ℝ, lo ≤ Real.cos ((0.75 : ℝ) * Real.log 3) ∧
      Real.cos ((0.75 : ℝ) * Real.log 3) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log3_hi
  have hlog_lo := dp_log3_lo
  have hx : |((0.75 : ℝ) * Real.log 3)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((0.75 : ℝ) * Real.log 3)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((0.75 : ℝ) * Real.log 3)
      = ((0.75 : ℝ) * Real.log 3) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_cos_enclose_of_reduced ((0.75 : ℝ) * Real.log 3) hx 0
      (((0.75 : ℝ) * Real.log 3)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

theorem prefix_R06_sin2 :
    ∃ lo hi : ℝ, lo ≤ Real.sin ((-1.25 : ℝ) * Real.log 2) ∧
      Real.sin ((-1.25 : ℝ) * Real.log 2) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log2_hi
  have hlog_lo := dp_log2_lo
  have hx : |((-1.25 : ℝ) * Real.log 2)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((-1.25 : ℝ) * Real.log 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((-1.25 : ℝ) * Real.log 2)
      = ((-1.25 : ℝ) * Real.log 2) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_sin_enclose_of_reduced ((-1.25 : ℝ) * Real.log 2) hx 0
      (((-1.25 : ℝ) * Real.log 2)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

theorem prefix_R06_cos2 :
    ∃ lo hi : ℝ, lo ≤ Real.cos ((-1.25 : ℝ) * Real.log 2) ∧
      Real.cos ((-1.25 : ℝ) * Real.log 2) ≤ hi ∧ hi - lo ≤ 1 / 50 := by
  have hlog_hi := dp_log2_hi
  have hlog_lo := dp_log2_lo
  have hx : |((-1.25 : ℝ) * Real.log 2)| ≤ 40 := by
    rw [abs_le]
    constructor <;> linarith
  have hred : |((-1.25 : ℝ) * Real.log 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrdef : ((-1.25 : ℝ) * Real.log 2)
      = ((-1.25 : ℝ) * Real.log 2) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp
  obtain ⟨lo, hi, hlo_eq, hhi_eq, hlo, hhi, hwidth, heq⟩ :=
    dp_cos_enclose_of_reduced ((-1.25 : ℝ) * Real.log 2) hx 0
      (((-1.25 : ℝ) * Real.log 2)) hrdef hred
  exact ⟨lo, hi, hlo, hhi, hwidth⟩

/-! ## Recon-negative gaps (N = 8 estimates; each gap is arithmetic fact).

Per center: slow = generous N = 8 eta-head lower estimate; rtail = MVT
pair-tail upper + 0.15 head-disc uncertainty; needEta = need * 0.5
(uniform denom floor). Gap slow - rtail - needEta < 0 means the head
cannot cover the tail plus the floor at this N: re-tier queue. -/

/-- R05: slow 1.0, rtail 0.63, needEta 0.5; gap -0.13. -/
theorem reconNeg_R05_gap : (1.0 : ℝ) - 0.63 - 0.5 < 0 := by norm_num
/-- R06: slow 1.0, rtail 0.89, needEta 0.5; gap -0.39. -/
theorem reconNeg_R06_gap : (1.0 : ℝ) - 0.89 - 0.5 < 0 := by norm_num
/-- R04: slow 0.8, rtail 1.71, needEta 0.5; gap -1.41. -/
theorem reconNeg_R04_gap : (0.8 : ℝ) - 1.71 - 0.5 < 0 := by norm_num
/-- R07: slow 0.8, rtail 1.99, needEta 0.5; gap -1.69. -/
theorem reconNeg_R07_gap : (0.8 : ℝ) - 1.99 - 0.5 < 0 := by norm_num
/-- R03: slow 0.7, rtail 2.82, needEta 0.7; gap -2.82. -/
theorem reconNeg_R03_gap : (0.7 : ℝ) - 2.82 - 0.7 < 0 := by norm_num
/-- R01: slow 0.6, rtail 3.66, needEta 0.6; gap -3.66. -/
theorem reconNeg_R01_gap : (0.6 : ℝ) - 3.66 - 0.6 < 0 := by norm_num
/-- R02: slow 0.6, rtail 3.94, needEta 0.55; gap -3.89. -/
theorem reconNeg_R02_gap : (0.6 : ℝ) - 3.94 - 0.55 < 0 := by norm_num
/-- R08: slow 0.6, rtail 3.10, needEta 0.5; gap -3.0. -/
theorem reconNeg_R08_gap : (0.6 : ℝ) - 3.10 - 0.5 < 0 := by norm_num
/-- R09: slow 0.6, rtail 4.22, needEta 0.65; gap -4.27. -/
theorem reconNeg_R09_gap : (0.6 : ℝ) - 4.22 - 0.65 < 0 := by norm_num
/-- R00: slow 0.6, rtail 5.06, needEta 0.95; gap -5.41. -/
theorem reconNeg_R00_gap : (0.6 : ℝ) - 5.06 - 0.95 < 0 := by norm_num
/-- R10: slow 0.6, rtail 5.06, needEta 0.95; gap -5.41. -/
theorem reconNeg_R10_gap : (0.6 : ℝ) - 5.06 - 0.95 < 0 := by norm_num

/-- R25: slow 0.6, rtail 1.44, needEta 0.5; gap -1.34. -/
theorem reconNeg_R25_gap : (0.6 : ℝ) - 1.44 - 0.5 < 0 := by norm_num
/-- R26: slow 0.6, rtail 2.25, needEta 0.5; gap -2.15. -/
theorem reconNeg_R26_gap : (0.6 : ℝ) - 2.25 - 0.5 < 0 := by norm_num
/-- R24: slow 0.6, rtail 4.70, needEta 0.5; gap -4.6. -/
theorem reconNeg_R24_gap : (0.6 : ℝ) - 4.70 - 0.5 < 0 := by norm_num
/-- R27: slow 0.6, rtail 5.53, needEta 0.5; gap -5.43. -/
theorem reconNeg_R27_gap : (0.6 : ℝ) - 5.53 - 0.5 < 0 := by norm_num
/-- R23: slow 0.6, rtail 8.00, needEta 0.5; gap -7.9. -/
theorem reconNeg_R23_gap : (0.6 : ℝ) - 8.00 - 0.5 < 0 := by norm_num
/-- R22: slow 0.6, rtail 11.30, needEta 0.5; gap -11.2. -/
theorem reconNeg_R22_gap : (0.6 : ℝ) - 11.30 - 0.5 < 0 := by norm_num
/-- R21: slow 0.6, rtail 14.60, needEta 0.5; gap -14.5. -/
theorem reconNeg_R21_gap : (0.6 : ℝ) - 14.60 - 0.5 < 0 := by norm_num
/-- R28: slow 0.6, rtail 8.83, needEta 0.5; gap -8.73. -/
theorem reconNeg_R28_gap : (0.6 : ℝ) - 8.83 - 0.5 < 0 := by norm_num
/-- R29: slow 0.6, rtail 12.13, needEta 0.5; gap -12.03. -/
theorem reconNeg_R29_gap : (0.6 : ℝ) - 12.13 - 0.5 < 0 := by norm_num
/-- R30: slow 0.6, rtail 14.60, needEta 0.5; gap -14.5. -/
theorem reconNeg_R30_gap : (0.6 : ℝ) - 14.60 - 0.5 < 0 := by norm_num

/-- R35: slow 0.6, rtail 3.07, needEta 0.5; gap -2.97. -/
theorem reconNeg_R35_gap : (0.6 : ℝ) - 3.07 - 0.5 < 0 := by norm_num
/-- R36: slow 0.6, rtail 4.99, needEta 0.5; gap -4.89. -/
theorem reconNeg_R36_gap : (0.6 : ℝ) - 4.99 - 0.5 < 0 := by norm_num
/-- R34: slow 0.6, rtail 10.75, needEta 0.5; gap -10.65. -/
theorem reconNeg_R34_gap : (0.6 : ℝ) - 10.75 - 0.5 < 0 := by norm_num
/-- R37: slow 0.6, rtail 12.67, needEta 0.5; gap -12.57. -/
theorem reconNeg_R37_gap : (0.6 : ℝ) - 12.67 - 0.5 < 0 := by norm_num
/-- R33: slow 0.6, rtail 18.43, needEta 0.5; gap -18.33. -/
theorem reconNeg_R33_gap : (0.6 : ℝ) - 18.43 - 0.5 < 0 := by norm_num
/-- R32: slow 0.6, rtail 26.11, needEta 0.5; gap -26.01. -/
theorem reconNeg_R32_gap : (0.6 : ℝ) - 26.11 - 0.5 < 0 := by norm_num
/-- R31: slow 0.6, rtail 33.79, needEta 0.5; gap -33.69. -/
theorem reconNeg_R31_gap : (0.6 : ℝ) - 33.79 - 0.5 < 0 := by norm_num
/-- R38: slow 0.6, rtail 20.35, needEta 0.5; gap -20.25. -/
theorem reconNeg_R38_gap : (0.6 : ℝ) - 20.35 - 0.5 < 0 := by norm_num
/-- R39: slow 0.6, rtail 28.03, needEta 0.5; gap -27.93. -/
theorem reconNeg_R39_gap : (0.6 : ℝ) - 28.03 - 0.5 < 0 := by norm_num
/-- R40: slow 0.6, rtail 33.79, needEta 0.5; gap -33.69. -/
theorem reconNeg_R40_gap : (0.6 : ℝ) - 33.79 - 0.5 < 0 := by norm_num

end Door3PremiseZeta
