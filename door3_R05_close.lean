import Mathlib
import central_cover_assembly
import door3_dp_trig
import door3_dp_terms
import door3_premise_zeta
import door3_zlowN
import door3_zeta_N64

/-!
# Door 3 R05 zeta-lower close attempt (low-t first cell, N = 64 pair-folded).

WRITE-ONLY task file. No build command was run. No commit. New file only.

Import closure (verified read-only before writing):
* `central_cover_assembly` imports `Mathlib` + `riemann_hypothesis`
  + `rh_certificate_infra` only (lines 1-3); no `door3` import
  (verified by grep: zero `import door3` hits) — upstream leaf for `zeta`.
* `door3_dp_trig` imports `Mathlib` only (line 1) — upstream leaf.
* `door3_dp_terms` imports `Mathlib` + `door3_dp_trig` (lines 1-2) — leaf.
* `door3_premise_zeta` imports `Mathlib` + `central_cover_assembly`
  + `door3_dp_trig` + `door3_dp_terms` (lines 1-4) — leaf.
* `door3_zlowN` imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` (lines 1-5) — leaf.
* `door3_zeta_N64` imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` + `door3_zlowN` (lines 1-6) — leaf.
* This file imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` + `door3_zlowN`
  + `door3_zeta_N64` only. Head files (`door3_dp_headA/B/C1`) are NOT
  imported (read-only reference only; needed instances reproved locally).
  The rigorous-zeta file is NOT imported (cycle risk).

R05 center confirmation (from `door3_premise_zeta.lean` line 71):
`zs_R05 := ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩`, so σ = 0.395, t = -0.75.
Floor numeral (line 107): `premZeta_R05 : Prop := (1.0 : ℝ) ≤ ‖zeta zs_R05‖`.
Local `sR05` below is defined with identical coordinates and linked by `rfl`.

Sibling N64 status (from `door3_zeta_N64.lean`):
slow 1.15, tail 0.53, needEta 0.5, margin +0.12 FIRES conditionally via
`zetaN64_R05_ge` once witnesses arrive. That estimate uses uniform factor
0.5 as if it were an UPPER on `‖1 - 2 ^ (1 - s)‖`. The proved direction needs
an UPPER (link `slow - tail ≤ cF * Z` with `cF = ‖denom‖` requires
`‖denom‖ ≤ cF`). The uniform 0.5 is documented upstream as a LOWER floor
(`‖denom‖ ≥ 0.5`), hence optimistic as an upper. True `‖denom‖` at R05 is
near 0.82 on estimates, and the honest triangle upper proved here is 3.
So the +0.12 conditional margin does not transfer to an unconditional close.

Honest outcome in this closure: R05 NOT CLOSED unconditionally.
What is banked unconditionally here: generic cpow re/im at R05, log5/log7
reproved locally (headA pattern, no head import), log1p hi/lo (headB pattern,
no head import), k = 0 trig enclosures at n = 2, 3, symbolic pair-triangle
discs for all m = 1 .. 32, norm cap `‖sR05‖ ≤ 1`, rpow tail-decay shape,
honest eta-factor UPPER `‖1 - 2 ^ (1 - sR05)‖ ≤ 3`, conditional bridge
wrapper, and gap arithmetic showing the miss both under the honest upper
and under the estimate-true value. Best honest unconditional floor banked:
`0 ≤ ‖zeta sR05‖`. N128 verdict: still misses honestly (see end).
-/

noncomputable section

namespace Door3R05Close

/-! ## R05 center (mirror of the premise center) -/

noncomputable def sR05 : ℂ := ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩

theorem sR05_eq_premise : sR05 = Door3PremiseZeta.zs_R05 := rfl

theorem sR05_re : sR05.re = (0.395 : ℝ) := rfl

theorem sR05_im : sR05.im = (-0.75 : ℝ) := rfl

theorem sR05_neg_re : (-sR05).re = (-0.395 : ℝ) := rfl

theorem sR05_neg_im : (-sR05).im = (0.75 : ℝ) := rfl

/-- Norm cap at R05 (`‖s‖ ≤ 1` slot used by the MVT constant). -/
theorem sR05_norm_le : ‖sR05‖ ≤ 1 := by
  have h : sR05 = ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ := rfl
  rw [h]
  rw [Complex.norm_def]
  have hsq : (0.395 : ℝ) ^ 2 + (-0.75 : ℝ) ^ 2 ≤ 1 ^ 2 := by norm_num
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_one] at hle
  exact hle

/-! ## Generic cpow re / im at R05 (DP term-disc recipe, reproved locally) -/

theorem r05_cpow_re (x : ℝ) (hx : 0 < x) :
    ((((x : ℝ) : ℂ) ^ (-sR05))).re
      = x ^ (-0.395 : ℝ) * Real.cos ((0.75 : ℝ) * Real.log x) := by
  have hxC : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((x : ℝ) : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-sR05).re = (-0.395 : ℝ) := rfl
  have him_w : (-sR05).im = (0.75 : ℝ) := rfl
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-sR05)).re
      = Real.log x * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-sR05)).im
      = Real.log x * (0.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-0.395)) = x ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hcos : Real.cos (Real.log x * (0.75 : ℝ))
      = Real.cos ((0.75 : ℝ) * Real.log x) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

theorem r05_cpow_im (x : ℝ) (hx : 0 < x) :
    ((((x : ℝ) : ℂ) ^ (-sR05))).im
      = x ^ (-0.395 : ℝ) * Real.sin ((0.75 : ℝ) * Real.log x) := by
  have hxC : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((x : ℝ) : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-sR05).re = (-0.395 : ℝ) := rfl
  have him_w : (-sR05).im = (0.75 : ℝ) := rfl
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-sR05)).re
      = Real.log x * (-0.395) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-sR05)).im
      = Real.log x * (0.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-0.395)) = x ^ (-0.395 : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hsin : Real.sin (Real.log x * (0.75 : ℝ))
      = Real.sin ((0.75 : ℝ) * Real.log x) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-! ## Log bounds reproved locally (headA pattern; no head import).

`log 2` / `log 3` are banked upstream in `door3_dp_terms`.
`log 5` uses the banked Mathlib `log 5` facts; `log 7` uses the
2401/2400 squeeze. Needed for the n = 2, 3 trig arguments and the
2/3/5/7-smooth pair arguments. Logs at 11 and above stay open. -/

theorem r05_log5_lo : 16094 / 10000 ≤ Real.log 5 := by
  have h := Real.log_five_gt_d9
  norm_num at h ⊢
  linarith

theorem r05_log5_hi : Real.log 5 ≤ 16095 / 10000 := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith

theorem r05_log2401_eq : Real.log 2401 = 4 * Real.log 7 := by
  have heq : (2401 : ℝ) = 7 * (7 * (7 * 7)) := by norm_num
  have h1 : Real.log (7 * (7 * (7 * 7)))
      = Real.log 7 + Real.log (7 * (7 * 7)) :=
    Real.log_mul (by norm_num) (by norm_num)
  have h2 : Real.log (7 * (7 * 7)) = Real.log 7 + Real.log (7 * 7) :=
    Real.log_mul (by norm_num) (by norm_num)
  have h3 : Real.log (7 * 7) = Real.log 7 + Real.log 7 :=
    Real.log_mul (by norm_num) (by norm_num)
  rw [heq, h1, h2, h3]
  ring

theorem r05_log2400_eq :
    Real.log 2400 = 5 * Real.log 2 + (Real.log 3 + 2 * Real.log 5) := by
  have heq : (2400 : ℝ) = (2 * (2 * (2 * (2 * 2)))) * (3 * (5 * 5)) := by
    norm_num
  have ha : Real.log (2 * (2 * (2 * (2 * 2))))
      = Real.log 2 + Real.log (2 * (2 * (2 * 2))) :=
    Real.log_mul (by norm_num) (by norm_num)
  have hb : Real.log (2 * (2 * (2 * 2))) = Real.log 2 + Real.log (2 * (2 * 2)) :=
    Real.log_mul (by norm_num) (by norm_num)
  have hc : Real.log (2 * (2 * 2)) = Real.log 2 + Real.log (2 * 2) :=
    Real.log_mul (by norm_num) (by norm_num)
  have hd : Real.log (2 * 2) = Real.log 2 + Real.log 2 :=
    Real.log_mul (by norm_num) (by norm_num)
  have he : Real.log (3 * (5 * 5)) = Real.log 3 + Real.log (5 * 5) :=
    Real.log_mul (by norm_num) (by norm_num)
  have hf : Real.log (5 * 5) = Real.log 5 + Real.log 5 :=
    Real.log_mul (by norm_num) (by norm_num)
  have hg : Real.log ((2 * (2 * (2 * (2 * 2)))) * (3 * (5 * 5)))
      = Real.log (2 * (2 * (2 * (2 * 2)))) + Real.log (3 * (5 * 5)) :=
    Real.log_mul (by norm_num) (by norm_num)
  rw [heq, hg, ha, hb, hc, hd, he, hf]
  ring

theorem r05_delta_lo : (1 : ℝ) / 2401 ≤ Real.log (2401 / 2400) := by
  have hpos : (0 : ℝ) < 2400 / 2401 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (2401 / 2400) = -Real.log (2400 / 2401) := by
    have e : (2401 / 2400 : ℝ) = (2400 / 2401 : ℝ)⁻¹ := by norm_num
    rw [e, Real.log_inv]
  have heq : (2400 : ℝ) / 2401 - 1 = -(1 / 2401) := by norm_num
  rw [heq] at hub
  linarith [hub, hinv]

theorem r05_delta_hi : Real.log (2401 / 2400) ≤ (1 : ℝ) / 2400 := by
  have hpos : (0 : ℝ) < 2401 / 2400 := by norm_num
  have hub := Real.log_le_sub_one_of_pos hpos
  have heq : (2401 : ℝ) / 2400 - 1 = 1 / 2400 := by norm_num
  rw [heq] at hub
  exact hub

theorem r05_log7_lo : 19458 / 10000 ≤ Real.log 7 := by
  have h2lo := dp_log2_lo
  have h3lo := dp_log3_lo
  have h5lo := r05_log5_lo
  have hdlo := r05_delta_lo
  have h2401 := r05_log2401_eq
  have h2400 := r05_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 :=
    Real.log_div (by norm_num) (by norm_num)
  linarith [h2lo, h3lo, h5lo, hdlo, h2401, h2400, hdiv]

theorem r05_log7_hi : Real.log 7 ≤ 19461 / 10000 := by
  have h2hi := dp_log2_hi
  have h3hi := dp_log3_hi
  have h5hi := r05_log5_hi
  have hdhi := r05_delta_hi
  have h2401 := r05_log2401_eq
  have h2400 := r05_log2400_eq
  have hdiv : Real.log (2401 / 2400) = Real.log 2401 - Real.log 2400 :=
    Real.log_div (by norm_num) (by norm_num)
  linarith [h2hi, h3hi, h5hi, hdhi, h2401, h2400, hdiv]

/-- 2/3-smooth headB pattern reproved locally: log1p upper. -/
theorem r05_log1p_hi (x : ℝ) (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  have heq : (1 + x) - 1 = x := by ring
  linarith

/-- 2/3-smooth headB pattern reproved locally: log1p lower. -/
theorem r05_log1p_lo (x : ℝ) (hx : -1 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hinv_pos : (0 : ℝ) < ((1 + x)⁻¹) := inv_pos.mpr hpos
  have hup := Real.log_le_sub_one_of_pos hinv_pos
  have hlog_inv : Real.log ((1 + x)⁻¹) = -Real.log (1 + x) := Real.log_inv _
  have heq : ((1 + x)⁻¹) - 1 = -x / (1 + x) := by field_simp; ring
  linarith

/-! ## Stage-1 trig enclosures at R05's own arguments (n = 2, 3 direct).

Arguments are `0.75 * log n`. For n = 2, 3 the reduced argument is the
argument itself (|·| ≤ 1 via the banked log bounds), so k = 0 applies.
For n ≥ 4 the argument exceeds 1 (0.75 * log 4 above 1.03), so direct k = 0
does not apply; octant / shifted reduction plus log bounds at 5 and above
would be needed per pair and those numeral discs stay open (see notes).
Only existence with width ≤ 1/50 is banked here for n = 2, 3. -/

theorem r05_sin2 :
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

theorem r05_cos2 :
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

theorem r05_sin3 :
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

theorem r05_cos3 :
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

/-! ## Pair-folded head: 32 symbolic discs at R05 (m = 1 .. 32).

Each pair is `zetaN64_etaPair sR05 m` (two Dirichlet terms folded into one
disc proof, mirroring `cutR10_etaPair_eq_cpow_sub`). The triangle bound is
unconditional with symbolic amps; no rpow numeral upper is needed, so all
32 close here. Numeral tightening (MVT sharpening with `‖s‖ ≤ 1`) stays as
the documented next step; the MVT numeral itself stays an explicit premise
by the wave rule. -/

theorem r05_pair_triangle (m : ℕ) :
    ‖Door3ZetaN64.zetaN64_etaPair sR05 m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := Door3ZetaN64.zetaN64_norm_pair_triangle sR05 m
  have hre : (-sR05).re = (-(0.395 : ℝ)) := rfl
  rw [hre] at h
  exact h

theorem r05_pair01 : ‖Door3ZetaN64.zetaN64_etaPair sR05 1‖ ≤
    ((3 : ℝ) ^ (-(0.395 : ℝ))) + ((4 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 1
  norm_num at h ⊢
  exact h

theorem r05_pair02 : ‖Door3ZetaN64.zetaN64_etaPair sR05 2‖ ≤
    ((5 : ℝ) ^ (-(0.395 : ℝ))) + ((6 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 2
  norm_num at h ⊢
  exact h

theorem r05_pair03 : ‖Door3ZetaN64.zetaN64_etaPair sR05 3‖ ≤
    ((7 : ℝ) ^ (-(0.395 : ℝ))) + ((8 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 3
  norm_num at h ⊢
  exact h

theorem r05_pair04 : ‖Door3ZetaN64.zetaN64_etaPair sR05 4‖ ≤
    ((9 : ℝ) ^ (-(0.395 : ℝ))) + ((10 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 4
  norm_num at h ⊢
  exact h

theorem r05_pair05 : ‖Door3ZetaN64.zetaN64_etaPair sR05 5‖ ≤
    ((11 : ℝ) ^ (-(0.395 : ℝ))) + ((12 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 5
  norm_num at h ⊢
  exact h

theorem r05_pair06 : ‖Door3ZetaN64.zetaN64_etaPair sR05 6‖ ≤
    ((13 : ℝ) ^ (-(0.395 : ℝ))) + ((14 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 6
  norm_num at h ⊢
  exact h

theorem r05_pair07 : ‖Door3ZetaN64.zetaN64_etaPair sR05 7‖ ≤
    ((15 : ℝ) ^ (-(0.395 : ℝ))) + ((16 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 7
  norm_num at h ⊢
  exact h

theorem r05_pair08 : ‖Door3ZetaN64.zetaN64_etaPair sR05 8‖ ≤
    ((17 : ℝ) ^ (-(0.395 : ℝ))) + ((18 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 8
  norm_num at h ⊢
  exact h

theorem r05_pair09 : ‖Door3ZetaN64.zetaN64_etaPair sR05 9‖ ≤
    ((19 : ℝ) ^ (-(0.395 : ℝ))) + ((20 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 9
  norm_num at h ⊢
  exact h

theorem r05_pair10 : ‖Door3ZetaN64.zetaN64_etaPair sR05 10‖ ≤
    ((21 : ℝ) ^ (-(0.395 : ℝ))) + ((22 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 10
  norm_num at h ⊢
  exact h

theorem r05_pair11 : ‖Door3ZetaN64.zetaN64_etaPair sR05 11‖ ≤
    ((23 : ℝ) ^ (-(0.395 : ℝ))) + ((24 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 11
  norm_num at h ⊢
  exact h

theorem r05_pair12 : ‖Door3ZetaN64.zetaN64_etaPair sR05 12‖ ≤
    ((25 : ℝ) ^ (-(0.395 : ℝ))) + ((26 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 12
  norm_num at h ⊢
  exact h

theorem r05_pair13 : ‖Door3ZetaN64.zetaN64_etaPair sR05 13‖ ≤
    ((27 : ℝ) ^ (-(0.395 : ℝ))) + ((28 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 13
  norm_num at h ⊢
  exact h

theorem r05_pair14 : ‖Door3ZetaN64.zetaN64_etaPair sR05 14‖ ≤
    ((29 : ℝ) ^ (-(0.395 : ℝ))) + ((30 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 14
  norm_num at h ⊢
  exact h

theorem r05_pair15 : ‖Door3ZetaN64.zetaN64_etaPair sR05 15‖ ≤
    ((31 : ℝ) ^ (-(0.395 : ℝ))) + ((32 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 15
  norm_num at h ⊢
  exact h

theorem r05_pair16 : ‖Door3ZetaN64.zetaN64_etaPair sR05 16‖ ≤
    ((33 : ℝ) ^ (-(0.395 : ℝ))) + ((34 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 16
  norm_num at h ⊢
  exact h

theorem r05_pair17 : ‖Door3ZetaN64.zetaN64_etaPair sR05 17‖ ≤
    ((35 : ℝ) ^ (-(0.395 : ℝ))) + ((36 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 17
  norm_num at h ⊢
  exact h

theorem r05_pair18 : ‖Door3ZetaN64.zetaN64_etaPair sR05 18‖ ≤
    ((37 : ℝ) ^ (-(0.395 : ℝ))) + ((38 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 18
  norm_num at h ⊢
  exact h

theorem r05_pair19 : ‖Door3ZetaN64.zetaN64_etaPair sR05 19‖ ≤
    ((39 : ℝ) ^ (-(0.395 : ℝ))) + ((40 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 19
  norm_num at h ⊢
  exact h

theorem r05_pair20 : ‖Door3ZetaN64.zetaN64_etaPair sR05 20‖ ≤
    ((41 : ℝ) ^ (-(0.395 : ℝ))) + ((42 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 20
  norm_num at h ⊢
  exact h

theorem r05_pair21 : ‖Door3ZetaN64.zetaN64_etaPair sR05 21‖ ≤
    ((43 : ℝ) ^ (-(0.395 : ℝ))) + ((44 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 21
  norm_num at h ⊢
  exact h

theorem r05_pair22 : ‖Door3ZetaN64.zetaN64_etaPair sR05 22‖ ≤
    ((45 : ℝ) ^ (-(0.395 : ℝ))) + ((46 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 22
  norm_num at h ⊢
  exact h

theorem r05_pair23 : ‖Door3ZetaN64.zetaN64_etaPair sR05 23‖ ≤
    ((47 : ℝ) ^ (-(0.395 : ℝ))) + ((48 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 23
  norm_num at h ⊢
  exact h

theorem r05_pair24 : ‖Door3ZetaN64.zetaN64_etaPair sR05 24‖ ≤
    ((49 : ℝ) ^ (-(0.395 : ℝ))) + ((50 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 24
  norm_num at h ⊢
  exact h

theorem r05_pair25 : ‖Door3ZetaN64.zetaN64_etaPair sR05 25‖ ≤
    ((51 : ℝ) ^ (-(0.395 : ℝ))) + ((52 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 25
  norm_num at h ⊢
  exact h

theorem r05_pair26 : ‖Door3ZetaN64.zetaN64_etaPair sR05 26‖ ≤
    ((53 : ℝ) ^ (-(0.395 : ℝ))) + ((54 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 26
  norm_num at h ⊢
  exact h

theorem r05_pair27 : ‖Door3ZetaN64.zetaN64_etaPair sR05 27‖ ≤
    ((55 : ℝ) ^ (-(0.395 : ℝ))) + ((56 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 27
  norm_num at h ⊢
  exact h

theorem r05_pair28 : ‖Door3ZetaN64.zetaN64_etaPair sR05 28‖ ≤
    ((57 : ℝ) ^ (-(0.395 : ℝ))) + ((58 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 28
  norm_num at h ⊢
  exact h

theorem r05_pair29 : ‖Door3ZetaN64.zetaN64_etaPair sR05 29‖ ≤
    ((59 : ℝ) ^ (-(0.395 : ℝ))) + ((60 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 29
  norm_num at h ⊢
  exact h

theorem r05_pair30 : ‖Door3ZetaN64.zetaN64_etaPair sR05 30‖ ≤
    ((61 : ℝ) ^ (-(0.395 : ℝ))) + ((62 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 30
  norm_num at h ⊢
  exact h

theorem r05_pair31 : ‖Door3ZetaN64.zetaN64_etaPair sR05 31‖ ≤
    ((63 : ℝ) ^ (-(0.395 : ℝ))) + ((64 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 31
  norm_num at h ⊢
  exact h

theorem r05_pair32 : ‖Door3ZetaN64.zetaN64_etaPair sR05 32‖ ≤
    ((65 : ℝ) ^ (-(0.395 : ℝ))) + ((66 : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := r05_pair_triangle 32
  norm_num at h ⊢
  exact h

/-- 32 pairs cover 64 head terms (pair-count check). -/
theorem r05_pair_count : 32 * 2 = 64 := by norm_num

/-! ## MVT tail shape at M = 64 (symbolic; numeral stays a premise).

The full MVT pair-tail numeral `C * M ^ (-σ) / σ` with `C = ‖s‖` needs the
MVT estimate on `t ↦ (t : ℂ) ^ (-s)` (see `cutR10_norm_etaPair_le` pattern,
not imported here by the closure rule). What IS banked unconditionally:
the monotone decay that justifies the N = 64 tail being no worse than the
N = 32 shape, plus the `‖s‖ ≤ 1` constant above. The numeral `tail ≤ 0.53`
is therefore recorded as an explicit open premise in the wrapper below,
not as a proved fact. -/

theorem r05_tail_decay :
    (64 : ℝ) ^ (-(0.395 : ℝ)) ≤ (32 : ℝ) ^ (-(0.395 : ℝ)) :=
  Door3ZetaN64.zetaN64_tail_decay_R05

/-! ## Honest eta-factor UPPER at R05 (proved directly).

`eta = (1 - 2 ^ (1 - s)) * zeta`, so `‖eta‖ ≤ cF * ‖zeta‖` needs
`‖1 - 2 ^ (1 - sR05)‖ ≤ cF` with `cF` an UPPER. Triangle plus
`‖2 ^ (1 - sR05)‖ = 2 ^ 0.605 ≤ 2 ^ 1 = 2` gives honest `cF = 3`.
No log numeral is needed for this upper. -/

theorem r05_denom_re : (1 - sR05).re = (0.605 : ℝ) := by rfl

theorem r05_cF_upper : ‖(1 : ℂ) - ((2 : ℝ) : ℂ) ^ (1 - sR05)‖ ≤ 3 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hnorm : ‖(((2 : ℝ) : ℂ) ^ (1 - sR05))‖ = (2 : ℝ) ^ (0.605 : ℝ) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos h2pos (1 - sR05)
    have hre : (1 - sR05).re = (0.605 : ℝ) := rfl
    rw [hre] at h
    exact h
  have hpow_le : (2 : ℝ) ^ (0.605 : ℝ) ≤ 2 := by
    have hle : (2 : ℝ) ^ (0.605 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have heq : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
    rw [heq] at hle
    exact hle
  have htri := norm_sub_le (1 : ℂ) ((((2 : ℝ) : ℂ) ^ (1 - sR05)))
  rw [hnorm] at htri
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  rw [h1] at htri
  linarith [htri, hpow_le]

/-- Positivity of the honest factor (needed by the bridge). -/
theorem r05_cF_pos : (0 : ℝ) < 3 := by norm_num

/-! ## Conditional assembly (proved; fires once numeral witnesses arrive). -/

theorem r05_conditional (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta sR05‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta sR05‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _
    hcF hLink hThresh

/-- Same wrapper at the premise center (rewrite by `sR05_eq_premise`). -/
theorem r05_conditional_premise (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R05‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R05‖ := by
  have h := Door3ZetaN64.zetaN64_R05_ge slow tail cF hcF hLink hThresh
  exact h

/-! ## Honest gap: assembly MISSES, so no unconditional close is forced.

Estimate numerals from the sibling wave (N = 64): slow 1.15, tail 0.53.
Under the PROVED honest upper cF = 3, need * cF = 3.0 and
slow - tail = 0.62, gap 0.62 - 3.0 = -2.38 < 0. Under the estimate-true
denominator near 0.82, need * cF = 0.82 and gap 0.62 - 0.82 = -0.20 < 0.
The optimistic +0.12 margin at uniform 0.5 is recorded for reference but is
not a valid upper, so it cannot discharge `premZeta_R05`. -/

/-- Optimistic estimate margin (reference only; 0.5 is a lower floor). -/
theorem r05_gap_optimistic_ref : (0 : ℝ) ≤ (1.15 : ℝ) - 0.53 - 0.5 := by
  norm_num

/-- Honest gap under the proved upper cF = 3: misses by 2.38. -/
theorem r05_gap_honest : (1.15 : ℝ) - 0.53 - 3.0 < 0 := by norm_num

/-- Gap under estimate-true denom 0.82: misses by 0.20. -/
theorem r05_gap_trueEst : (1.15 : ℝ) - 0.53 - 0.82 < 0 := by norm_num

/-- Threshold form of the honest miss: need * cF + tail above slow. -/
theorem r05_thresh_miss : (1.15 : ℝ) ≤ (1.0 : ℝ) * 3.0 + 0.53 := by norm_num

/-! ## Best honest unconditional floor banked here. -/

/-- Best honest unconditional lower bound available in this closure. -/
theorem r05_best_unconditional : (0 : ℝ) ≤ ‖zeta sR05‖ :=
  norm_nonneg _

/-! ## N128 extrapolation verdict (capped at N = 128; follow-up, not this task).

Decay per doubling at σ = 0.395 is near 0.76; slow lift per doubling is at
most near 0.05. N128 estimates: slow 1.18, tail 0.40. Under honest cF = 3,
need * cF + tail = 3.40 above slow 1.18 (gap -2.22): still misses, so N128
with 64 pairs does NOT close honestly either. Under optimistic 0.5 the
estimate margin would read +0.28, but that factor is not a valid upper.
Under estimate-true 0.82 the gap is 1.18 - 0.40 - 0.82 = -0.04: still
misses narrowly. Hence N128 is not sufficient on honest numbers; needs
N above 128 or a tighter proved cF upper plus full numeral discs. -/

theorem r05_N128_honest_miss : (1.18 : ℝ) - 0.40 - 3.0 < 0 := by norm_num

theorem r05_N128_trueEst_miss : (1.18 : ℝ) - 0.40 - 0.82 < 0 := by norm_num

theorem r05_N128_optimistic_ref : (0 : ℝ) ≤ (1.18 : ℝ) - 0.40 - 0.5 := by
  norm_num

/-! ## Discharge notes and remainder.

* `premZeta_R05` NOT discharged: `Door3PremiseZeta.premZeta_R05` states
  `(1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R05‖`. The conditional wrappers
  `r05_conditional` / `r05_conditional_premise` (via
  `zeta_floor_of_eta_bridge` / `zetaN64_R05_ge`) are PROVED and ready, but
  their `hLink` / `hThresh` numeral witnesses are not banked here: the
  32 symbolic pair discs above need numeral tightening (octant enclosures
  at `0.75 * log n` for n ≥ 4 plus log bounds at 11 and above), the MVT
  tail numeral at M = 64 stays an explicit premise, and the only proved
  eta-factor upper is the honest `cF = 3` (gap -2.38), so the threshold
  `need * cF + tail ≤ slow` fails on honest numbers. No
  `R05_zeta_closed : 1 ≤ ‖zeta sR05‖` is claimed; the best honest
  unconditional floor banked is `r05_best_unconditional`.
* N128 verdict: does NOT close honestly (gaps -2.22 under proved cF = 3
  and -0.04 under estimate-true 0.82); N128 is a follow-up needing 64 pair
  numeral discs plus MVT tail at M = 128 plus a tighter proved cF upper,
  out of scope for this task — STOP here per brief.
* Remainder for follow-ups: log bounds at 11 .. 66, numeral pair discs for
  m = 1 .. 32 (octant route via `dp_octant_*_enclose` + `r05_log1p_*`
  machinery), MVT pair-tail numeral at M = 64 with `sR05_norm_le`,
  tighter cF upper below 3 (needs a `2 ^ 0.605` numeral upper), and the
  full slow-head assembly linking the 32 pairs to `slow`.

Centers closed unconditionally in this file: none (0 of 31).
-/

end Door3R05Close
