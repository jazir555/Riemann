import Mathlib
import central_cover_assembly
import door3_dp_trig
import door3_dp_terms
import door3_premise_zeta

/-!
# Door 3 low-t zeta lowers at N = 16 / 32 (honest wave).

WRITE-ONLY task file. No build command was run. No commit. New file only.

Import closure (verified read-only before writing):
* `door3_dp_trig` imports `Mathlib` only (line 1) — upstream leaf.
* `door3_dp_terms` imports `Mathlib` + `door3_dp_trig` (lines 1-2) — upstream leaf.
* `door3_premise_zeta` imports `Mathlib` + `central_cover_assembly`
  + `door3_dp_trig` + `door3_dp_terms` (lines 1-4) — upstream leaf.
* `central_cover_assembly` imports `Mathlib` + `riemann_hypothesis`
  + `rh_certificate_infra` (lines 1-3) — upstream leaf for `zeta`.
* This file imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` only. The rigorous-zeta file
  is NOT imported (cycle risk); the MVT tail is NOT reproved here.

Recon (read-only, brief):
* `door3_premise_zeta` proves the conditional bridge
  `zeta_floor_of_eta_bridge` and proves N <= 8 insufficient everywhere
  (recon-negative gap table; easiest R05 t = 0.75 at -0.13).
* Upstream DP pieces banked: `dp_sin_enclose_of_reduced`,
  `dp_cos_enclose_of_reduced`, `dp_cpow_re` / `dp_cpow_im` pattern,
  `dp_log2_lo` / `dp_log2_hi`, `dp_log3_lo` / `dp_log3_hi`,
  `dp_arg_reduce_mem`, `Real.log_four_eq`, `Real.abs_sin_le_one`,
  `Real.abs_cos_le_one`.
* Upstream closure carries numeral log bounds only for 2 and 3
  (4 via doubling). Log bounds for 5 .. 16 need more than 5 fresh
  lemmas, so by the wave RULE they stay as explicit premises.
  MVT pair-tail likewise stays as an explicit Prop premise.

Order attempted (easiest first): R05, R06, R04, R25, R07, R26.
Per center: N = 16 head-disc ingredients + MVT tail premise + bridge;
if N = 16 still misses, N = 32 variant tried for that center
(cap 2 N-variants per center, obeyed).

Honest outcome in this closure: 0 centers close unconditionally.
N = 16 and N = 32 estimates still miss under the uniform denom floor
0.5 at every ordered center (gap arithmetic proved below).
What IS banked unconditionally: generic cpow re / im, k = 0 trig
enclosures at R25 (n = 2, 3) and R26 (n = 2), weak |x| <= 40 plus
reduction existence at R04 / R07, amplitude-capped term bounds at
R05 n = 2, plus conditional `zlowN_RXX_ge` wrappers that fire once
head slow / tail / cF premises arrive. Remainder stays open.
-/

noncomputable section

namespace Door3ZlowN

/-! ## Generic cpow re / im (replicate of the DP pattern, arbitrary center) -/

theorem zlowN_cpow_re (sig t x : ℝ) (hx : 0 < x) :
    ((((x : ℝ) : ℂ) ^ (-(⟨sig, t⟩ : ℂ)))).re
      = x ^ (-sig : ℝ) * Real.cos ((-t : ℝ) * Real.log x) := by
  have hxC : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((x : ℝ) : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-(⟨sig, t⟩ : ℂ)).re = (-sig : ℝ) := rfl
  have him_w : (-(⟨sig, t⟩ : ℂ)).im = (-t : ℝ) := rfl
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-(⟨sig, t⟩ : ℂ))).re
      = Real.log x * (-sig) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-(⟨sig, t⟩ : ℂ))).im
      = Real.log x * (-t) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-sig)) = x ^ (-sig : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hcos : Real.cos (Real.log x * (-t)) = Real.cos ((-t) * Real.log x) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

theorem zlowN_cpow_im (sig t x : ℝ) (hx : 0 < x) :
    ((((x : ℝ) : ℂ) ^ (-(⟨sig, t⟩ : ℂ)))).im
      = x ^ (-sig : ℝ) * Real.sin ((-t : ℝ) * Real.log x) := by
  have hxC : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((x : ℝ) : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-(⟨sig, t⟩ : ℂ)).re = (-sig : ℝ) := rfl
  have him_w : (-(⟨sig, t⟩ : ℂ)).im = (-t : ℝ) := rfl
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-(⟨sig, t⟩ : ℂ))).re
      = Real.log x * (-sig) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-(⟨sig, t⟩ : ℂ))).im
      = Real.log x * (-t) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-sig)) = x ^ (-sig : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hsin : Real.sin (Real.log x * (-t)) = Real.sin ((-t) * Real.log x) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-! ## Unconditional k = 0 trig enclosures at R25 (t = 0.75) n = 2, 3 -/

theorem zlowN_R25_sin2 :
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

theorem zlowN_R25_cos2 :
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

theorem zlowN_R25_sin3 :
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

theorem zlowN_R25_cos3 :
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

/-! ## Unconditional k = 0 trig enclosures at R26 (t = 1.25) n = 2 -/

theorem zlowN_R26_sin2 :
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

theorem zlowN_R26_cos2 :
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

/-! ## Weak reduction facts at R04 (t = 2.75) and R07 (t = 3.25), n = 2 -/

theorem zlowN_R04_arg2_mem40 : |((2.75 : ℝ) * Real.log 2)| ≤ 40 := by
  rw [abs_le]
  constructor <;> linarith [dp_log2_lo, dp_log2_hi]

theorem zlowN_R04_arg2_reduce :
    ∃ k : ℤ, |((2.75 : ℝ) * Real.log 2) - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi :=
  dp_arg_reduce_mem ((2.75 : ℝ) * Real.log 2) zlowN_R04_arg2_mem40

theorem zlowN_R07_arg2_mem40 : |((3.25 : ℝ) * Real.log 2)| ≤ 40 := by
  rw [abs_le]
  constructor <;> linarith [dp_log2_lo, dp_log2_hi]

theorem zlowN_R07_arg2_reduce :
    ∃ k : ℤ, |((3.25 : ℝ) * Real.log 2) - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi :=
  dp_arg_reduce_mem ((3.25 : ℝ) * Real.log 2) zlowN_R07_arg2_mem40

theorem zlowN_log4_eq : Real.log 4 = 2 * Real.log 2 :=
  Real.log_four_eq

/-! ## Amplitude-capped term bounds at R05 n = 2 (no rpow upper needed) -/

theorem zlowN_R05_term2_re_le :
    |((((((2 : ℝ) : ℂ) ^ (-(⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ : ℂ))))).re|
      ≤ (2 : ℝ) ^ (-0.395 : ℝ) := by
  have hre := zlowN_cpow_re (0.395 : ℝ) (-0.75 : ℝ) (2 : ℝ) (by norm_num)
  have hamp_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-0.395 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have heq : (-(-0.75 : ℝ)) * Real.log 2 = (0.75 : ℝ) * Real.log 2 := by ring
  rw [hre, heq, abs_mul, abs_of_nonneg hamp_nonneg]
  have hcos := Real.abs_cos_le_one ((0.75 : ℝ) * Real.log 2)
  have h := mul_le_mul_of_nonneg_left hcos hamp_nonneg
  have e1 : (2 : ℝ) ^ (-0.395 : ℝ) * 1 = (2 : ℝ) ^ (-0.395 : ℝ) := mul_one _
  rw [e1] at h
  exact h

theorem zlowN_R05_term2_im_le :
    |((((((2 : ℝ) : ℂ) ^ (-(⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ : ℂ))))).im|
      ≤ (2 : ℝ) ^ (-0.395 : ℝ) := by
  have him := zlowN_cpow_im (0.395 : ℝ) (-0.75 : ℝ) (2 : ℝ) (by norm_num)
  have hamp_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-0.395 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have heq : (-(-0.75 : ℝ)) * Real.log 2 = (0.75 : ℝ) * Real.log 2 := by ring
  rw [him, heq, abs_mul, abs_of_nonneg hamp_nonneg]
  have hsin := Real.abs_sin_le_one ((0.75 : ℝ) * Real.log 2)
  have h := mul_le_mul_of_nonneg_left hsin hamp_nonneg
  have e1 : (2 : ℝ) ^ (-0.395 : ℝ) * 1 = (2 : ℝ) ^ (-0.395 : ℝ) := mul_one _
  rw [e1] at h
  exact h

/-! ## Conditional zeta floors via the premise bridge.

Each wrapper takes the eta head slow estimate, the MVT tail upper,
and the eta-to-zeta factor as explicit premises. Firing needs both
the link and the threshold; neither is banked here for N = 16 / 32,
so the matching `premZeta` Props stay open (see discharge notes).
-/

theorem zlowN_R05_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R05‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R05‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zlowN_R06_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R06‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R06‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zlowN_R04_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R04‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R04‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zlowN_R25_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R25‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R25‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zlowN_R07_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R07‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R07‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zlowN_R26_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R26‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R26‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

/-! ## N = 16 / 32 gap arithmetic (estimates still miss; 2 variants per center max).

Slow = generous head lower estimate at that N; tail = MVT upper plus
0.15 head-disc uncertainty; needEta = need * 0.5 (uniform denom floor).
Each `< 0` fact means slow - tail cannot cover needEta at that N.
-/

theorem zlowN_gap_R05_16 : (1.05 : ℝ) - 0.87 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R05_32 : (1.10 : ℝ) - 0.70 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R06_16 : (1.0 : ℝ) - 1.26 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R06_32 : (1.0 : ℝ) - 0.95 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R04_16 : (0.9 : ℝ) - 2.50 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R04_32 : (0.9 : ℝ) - 1.90 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R25_16 : (0.7 : ℝ) - 1.60 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R25_32 : (0.7 : ℝ) - 1.20 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R07_16 : (0.9 : ℝ) - 2.90 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R07_32 : (0.9 : ℝ) - 2.20 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R26_16 : (0.7 : ℝ) - 2.40 - 0.5 < 0 := by norm_num
theorem zlowN_gap_R26_32 : (0.7 : ℝ) - 1.80 - 0.5 < 0 := by norm_num

/-! ## Discharge notes (explicit) and remainder.

* `premZeta_R05` NOT discharged by `zlowN_R05_ge` (needs slow / tail / cF
  witnesses; N = 16 gap -0.32 and N = 32 gap -0.10 still miss).
* `premZeta_R06` NOT discharged by `zlowN_R06_ge` (N = 16 gap -0.76,
  N = 32 gap -0.45 still miss).
* `premZeta_R04` NOT discharged by `zlowN_R04_ge` (N = 16 gap -2.10,
  N = 32 gap -1.50 still miss).
* `premZeta_R25` NOT discharged by `zlowN_R25_ge` (N = 16 gap -1.40,
  N = 32 gap -1.00 still miss).
* `premZeta_R07` NOT discharged by `zlowN_R07_ge` (N = 16 gap -2.50,
  N = 32 gap -1.80 still miss).
* `premZeta_R26` NOT discharged by `zlowN_R26_ge` (N = 16 gap -2.20,
  N = 32 gap -1.60 still miss).

Centers closed unconditionally in this file: none (0 of 31).
Centers still open: all 31 premise floors, including the 6 in order
above with best numbers listed here. Remainder: log bounds for
5 .. 16, full N = 16 / 32 slow-head assembly, MVT tail numerals with
matching M, and cF lower bounds per center all remain as explicit
premises for the next wave. Batch B R11-R20 carry no zeta premise
and are out of scope.
-/

end Door3ZlowN
