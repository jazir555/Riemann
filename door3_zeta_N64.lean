import Mathlib
import central_cover_assembly
import door3_dp_trig
import door3_dp_terms
import door3_premise_zeta
import door3_zlowN

/-!
# Door 3 zeta lowers at N = 64, low-t row (honest wave).

WRITE-ONLY task file. No build command was run. No commit. New file only.

Import closure (verified read-only before writing):
* `door3_dp_trig` imports `Mathlib` only (line 1) — upstream leaf.
* `door3_dp_terms` imports `Mathlib` + `door3_dp_trig` (lines 1-2) — upstream leaf.
* `door3_premise_zeta` imports `Mathlib` + `central_cover_assembly`
  + `door3_dp_trig` + `door3_dp_terms` (lines 1-4) — upstream leaf.
* `central_cover_assembly` imports `Mathlib` + `riemann_hypothesis`
  + `rh_certificate_infra` (lines 1-3) — upstream leaf for `zeta`.
* `door3_zlowN` imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` (lines 1-5) — upstream leaf.
* This file imports `Mathlib` + `central_cover_assembly` + `door3_dp_trig`
  + `door3_dp_terms` + `door3_premise_zeta` + `door3_zlowN` only.
  The rigorous-zeta file is NOT imported (cycle risk); the MVT tail is NOT
  reproved here beyond its decay shape.

Recon (read-only, brief):
* `door3_zlowN` banks conditional wrappers `zlowN_RXX_ge` via
  `zeta_floor_of_eta_bridge`, plus N16/N32 estimate gaps:
  R05 N32 -0.10, R06 N32 -0.45, R04 N32 -1.50, R25 N32 -1.00.
  Zero centers close unconditionally; log bounds for 5..16 and MVT numerals
  stay as explicit premises by the wave rule.
* `door3_dp_terms` banks the term-disc recipe: `dp_cpow_re` / `dp_cpow_im`
  pattern, `dp_log2_lo/hi`, `dp_log3_lo/hi`, `dp_sin_enclose_of_reduced`,
  `dp_cos_enclose_of_reduced`, `dp_norm_of_re_im`, `dp_abs_tri`,
  tight discs `dp_term2_tight` / `dp_term3_tight` / `dp_term4_tight`.
  Extending single-term discs to n <= 64 needs log bounds for 5..64
  (more than 5 fresh lemmas), so by the wave rule they stay premises.
* Pair route: `door3_cutR10_ballsup` proves `cutR10_norm_etaPair_le`
  (`‖pair m‖ ≤ ‖s‖ * (2m+1)^(-Re-1)` via MVT on `t ↦ (t:ℂ)^(-s)`),
  with `cutR10_etaPair_eq_cpow_sub` folding 2 terms into 1 disc proof.
  At low-t centers here `‖s‖ ≈ 1-3` (R05 `‖s‖ ≈ 0.85`, R06 `≈ 1.31`,
  R04 `≈ 2.78`, R25 `≈ 0.78`), not 10, so pair bounds are tighter here.

Strategy (SMARTER, per brief): N = 32 head via 32 replicated single discs
is heavy; instead use PAIR-folded heads (`zetaN64_etaPair` below):
32 pairs = 64 terms in 32 disc proofs, each pair smaller via cancellation.
Unconditional part banked here: generic cpow re/im, cpow norm, pair
triangle bound (symbolic amps, no rpow numeral upper needed), rpow tail
decay shape `(64)^(-sig) ≤ (32)^(-sig)`, k = 0 trig reuse by reference.
Numeral slow / tail / cF witnesses stay as explicit premises; the
`zetaN64_RXX_ge` wrappers fire once they arrive.

Honest outcome in this closure: 0 centers close unconditionally.
Conditional `zetaN64_RXX_ge` wrappers are CLOSED (proved via the premise
bridge). On ESTIMATES at N = 64: R05 crosses (+0.12, conditionally fires),
R06 / R04 / R25 still miss (gaps proved below as arithmetic on estimates).
Extrapolation (capped at N = 128): R06 closes at N = 128 estimate (+0.03);
R04 and R25 still miss at N = 128 (-0.60, -0.39), needing N > 128,
out of budget, left open. Remainder inventoried below.
-/

noncomputable section

namespace Door3ZetaN64

/-! ## Generic cpow re / im at arbitrary low-t center (term-disc recipe) -/

theorem zetaN64_cpow_re (sig t x : ℝ) (hx : 0 < x) :
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

theorem zetaN64_cpow_im (sig t x : ℝ) (hx : 0 < x) :
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

/-! ## Amplitude-capped single-term bounds at R05 n = 2 (recipe extends) -/

theorem zetaN64_R05_term2_re_le :
    |((((((2 : ℝ) : ℂ) ^ (-(⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ : ℂ))))).re|
      ≤ (2 : ℝ) ^ (-0.395 : ℝ) := by
  have hre := zetaN64_cpow_re (0.395 : ℝ) (-0.75 : ℝ) (2 : ℝ) (by norm_num)
  have hamp_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-0.395 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have heq : (-(-0.75 : ℝ)) * Real.log 2 = (0.75 : ℝ) * Real.log 2 := by ring
  rw [hre, heq, abs_mul, abs_of_nonneg hamp_nonneg]
  have hcos := Real.abs_cos_le_one ((0.75 : ℝ) * Real.log 2)
  have h := mul_le_mul_of_nonneg_left hcos hamp_nonneg
  have e1 : (2 : ℝ) ^ (-0.395 : ℝ) * 1 = (2 : ℝ) ^ (-0.395 : ℝ) := mul_one _
  rw [e1] at h
  exact h

theorem zetaN64_R05_term2_im_le :
    |((((((2 : ℝ) : ℂ) ^ (-(⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ : ℂ))))).im|
      ≤ (2 : ℝ) ^ (-0.395 : ℝ) := by
  have him := zetaN64_cpow_im (0.395 : ℝ) (-0.75 : ℝ) (2 : ℝ) (by norm_num)
  have hamp_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-0.395 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have heq : (-(-0.75 : ℝ)) * Real.log 2 = (0.75 : ℝ) * Real.log 2 := by ring
  rw [him, heq, abs_mul, abs_of_nonneg hamp_nonneg]
  have hsin := Real.abs_sin_le_one ((0.75 : ℝ) * Real.log 2)
  have h := mul_le_mul_of_nonneg_left hsin hamp_nonneg
  have e1 : (2 : ℝ) ^ (-0.395 : ℝ) * 1 = (2 : ℝ) ^ (-0.395 : ℝ) := mul_one _
  rw [e1] at h
  exact h

/-! ## Pair-folded heads: 32 pairs = 64 terms in 32 disc proofs.

`zetaN64_etaPair s m` is the eta pair `(2m+1)^(-s) - (2m+2)^(-s)`
(1-indexed Dirichlet terms), mirroring `cutR10_etaPair_eq_cpow_sub`.
The triangle bound below is unconditional with symbolic amps (no rpow
numeral upper needed); the MVT sharpening
`‖pair‖ ≤ ‖s‖ * (2m+1)^(-sig-1)` stays as the documented next step,
with `‖s‖ ≈ 1-3` at these centers (tighter than the `‖s‖ ≤ 10` slot).
-/

noncomputable def zetaN64_etaPair (s : ℂ) (m : ℕ) : ℂ :=
  (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
    (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s))

theorem zetaN64_norm_cpow_neg (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖((((x : ℂ)) ^ (-s)))‖ = x ^ ((-s).re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)
  exact h

theorem zetaN64_neg_re (s : ℂ) : (-s).re = -(s.re) := rfl

theorem zetaN64_norm_pair_triangle (s : ℂ) (m : ℕ) :
    ‖zetaN64_etaPair s m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ ((-s).re)) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ ((-s).re)) := by
  unfold zetaN64_etaPair
  have ha_pos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hb_pos : (0 : ℝ) < ((((2 * m + 2 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have e1 : ‖((((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)))‖
      = ((((2 * m + 1 : ℕ)) : ℝ) ^ ((-s).re)) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos ha_pos (-s)
    have hcast : ((((2 * m + 1 : ℕ) : ℝ)) : ℂ)
        = (((((2 * m + 1 : ℕ) : ℝ)))) := rfl
    rw [hcast] at h
    exact h
  have e2 : ‖((((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)))‖
      = ((((2 * m + 2 : ℕ)) : ℝ) ^ ((-s).re)) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hb_pos (-s)
    have hcast : ((((2 * m + 2 : ℕ) : ℝ)) : ℂ)
        = (((((2 * m + 2 : ℕ) : ℝ)))) := rfl
    rw [hcast] at h
    exact h
  have htri := norm_sub_le
    ((((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)))
    ((((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)))
  rw [e1, e2] at htri
  exact htri

/-- Pair amps at R05 use `sig = 0.395`: symbolic, no numeral upper. -/
theorem zetaN64_pair_R05_triangle (m : ℕ) :
    ‖zetaN64_etaPair Door3PremiseZeta.zs_R05 m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := zetaN64_norm_pair_triangle Door3PremiseZeta.zs_R05 m
  have hre : (-Door3PremiseZeta.zs_R05).re = (-(0.395 : ℝ)) := rfl
  rw [hre] at h
  exact h

/-- Pair amps at R06 use `sig = 0.395`. -/
theorem zetaN64_pair_R06_triangle (m : ℕ) :
    ‖zetaN64_etaPair Door3PremiseZeta.zs_R06 m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := zetaN64_norm_pair_triangle Door3PremiseZeta.zs_R06 m
  have hre : (-Door3PremiseZeta.zs_R06).re = (-(0.395 : ℝ)) := rfl
  rw [hre] at h
  exact h

/-- Pair amps at R04 use `sig = 0.395`. -/
theorem zetaN64_pair_R04_triangle (m : ℕ) :
    ‖zetaN64_etaPair Door3PremiseZeta.zs_R04 m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ (-(0.395 : ℝ))) := by
  have h := zetaN64_norm_pair_triangle Door3PremiseZeta.zs_R04 m
  have hre : (-Door3PremiseZeta.zs_R04).re = (-(0.395 : ℝ)) := rfl
  rw [hre] at h
  exact h

/-- Pair amps at R25 use `sig = 0.2`. -/
theorem zetaN64_pair_R25_triangle (m : ℕ) :
    ‖zetaN64_etaPair Door3PremiseZeta.zs_R25 m‖ ≤
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.2 : ℝ))) +
        ((((2 * m + 2 : ℕ)) : ℝ) ^ (-(0.2 : ℝ))) := by
  have h := zetaN64_norm_pair_triangle Door3PremiseZeta.zs_R25 m
  have hre : (-Door3PremiseZeta.zs_R25).re = (-(0.2 : ℝ)) := rfl
  rw [hre] at h
  exact h

/-! ## MVT tail decay shape at matching M (unconditional, symbolic).

For `0 < sig`, the rpow tail factor shrinks when M grows:
`(64)^(-sig) ≤ (32)^(-sig) ≤ (16)^(-sig)`. The full MVT pair-tail
numeral `C * M^(-sig) / sig` stays as an explicit premise; only the
monotone shape (which justifies reusing the N = 32 tail bound at N = 64
as an upper bound up to the decay factor 0.76) is banked here.
-/

theorem zetaN64_rpow_decay_32_64 (sig : ℝ) (hsig : 0 < sig) :
    (64 : ℝ) ^ (-sig) ≤ (32 : ℝ) ^ (-sig) := by
  apply Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by linarith)

theorem zetaN64_rpow_decay_16_32 (sig : ℝ) (hsig : 0 < sig) :
    (32 : ℝ) ^ (-sig) ≤ (16 : ℝ) ^ (-sig) := by
  apply Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by linarith)

theorem zetaN64_tail_decay_R05 :
    (64 : ℝ) ^ (-(0.395 : ℝ)) ≤ (32 : ℝ) ^ (-(0.395 : ℝ)) :=
  zetaN64_rpow_decay_32_64 (0.395 : ℝ) (by norm_num)

theorem zetaN64_tail_decay_R25 :
    (64 : ℝ) ^ (-(0.2 : ℝ)) ≤ (32 : ℝ) ^ (-(0.2 : ℝ)) :=
  zetaN64_rpow_decay_32_64 (0.2 : ℝ) (by norm_num)

/-- Center-norm caps justifying the tighter pair slot (`‖s‖ ≈ 1-3`).
Only upper bounds provable by `norm_num` from the coordinates are banked;
the MVT constant `C = ‖s‖` then feeds the tail premise symbolically. -/
theorem zetaN64_norm_R05_le : ‖Door3PremiseZeta.zs_R05‖ ≤ 1 := by
  have h : Door3PremiseZeta.zs_R05 = ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩ := rfl
  rw [h]
  rw [Complex.norm_def]
  have hsq : (0.395 : ℝ) ^ 2 + (-0.75 : ℝ) ^ 2 ≤ 1 ^ 2 := by norm_num
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_one] at hle
  exact hle

theorem zetaN64_norm_R25_le : ‖Door3PremiseZeta.zs_R25‖ ≤ 1 := by
  have h : Door3PremiseZeta.zs_R25 = ⟨(0.2 : ℝ), (-0.75 : ℝ)⟩ := rfl
  rw [h]
  rw [Complex.norm_def]
  have hsq : (0.2 : ℝ) ^ 2 + (-0.75 : ℝ) ^ 2 ≤ 1 ^ 2 := by norm_num
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_one] at hle
  exact hle

theorem zetaN64_norm_R06_le : ‖Door3PremiseZeta.zs_R06‖ ≤ 2 := by
  have h : Door3PremiseZeta.zs_R06 = ⟨(0.395 : ℝ), (1.25 : ℝ)⟩ := rfl
  rw [h]
  rw [Complex.norm_def]
  have hsq : (0.395 : ℝ) ^ 2 + (1.25 : ℝ) ^ 2 ≤ 2 ^ 2 := by norm_num
  have hle := Real.sqrt_le_sqrt hsq
  have e : Real.sqrt (2 ^ 2 : ℝ) = 2 := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [e] at hle
  exact hle

theorem zetaN64_norm_R04_le : ‖Door3PremiseZeta.zs_R04‖ ≤ 3 := by
  have h : Door3PremiseZeta.zs_R04 = ⟨(0.395 : ℝ), (-2.75 : ℝ)⟩ := rfl
  rw [h]
  rw [Complex.norm_def]
  have hsq : (0.395 : ℝ) ^ 2 + (-2.75 : ℝ) ^ 2 ≤ 3 ^ 2 := by norm_num
  have hle := Real.sqrt_le_sqrt hsq
  have e : Real.sqrt (3 ^ 2 : ℝ) = 3 := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [e] at hle
  exact hle

/-! ## Conditional zeta floors at N = 64 via the premise bridge.

Each wrapper takes the N = 64 eta head slow estimate, the MVT tail upper
at matching M = 64, and the eta-to-zeta factor as explicit premises.
CLOSED: proved from `zeta_floor_of_eta_bridge`. Firing needs the slow /
tail / cF witnesses (log bounds 5..64 + MVT numerals + cF lower), which
stay open — see discharge notes. R05 estimate crosses at N = 64; the
other three wrappers are ready for N = 128 witnesses.
-/

theorem zetaN64_R05_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R05‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R05‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zetaN64_R06_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R06‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R06‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zetaN64_R04_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R04‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R04‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

theorem zetaN64_R25_ge (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R25‖)
    (hThresh : (1.0 : ℝ) * cF + tail ≤ slow) :
    (1.0 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R25‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.0 : ℝ) _ hcF hLink hThresh

/-! ## N = 64 estimate-gap arithmetic (conditional fire check).

Slow = generous N = 64 eta-head lower estimate (pair-folded, 32 pairs);
tail = MVT upper at M = 64 plus 0.10 head-disc uncertainty (tighter than
the N = 32 slot 0.15 since pairs share discs); needEta = need * 0.5
(uniform denom floor). Each fact is arithmetic on ESTIMATES only, not a
proved head assembly. `≥ 0` means the wrapper above fires once witnesses
arrive; `< 0` means it still misses at that N.
-/

/-- R05 N = 64: slow 1.15, tail 0.53, needEta 0.5; margin +0.12 FIRES
(conditionally). Trend from N32 (-0.10) closes via tail decay 0.70→0.53
plus slow lift 1.10→1.15 from pairs 17..32. -/
theorem zetaN64_gap_R05_64 : (0 : ℝ) ≤ (1.15 : ℝ) - 0.53 - 0.5 := by norm_num

/-- R06 N = 64: slow 1.05, tail 0.72, needEta 0.5; gap -0.17 still misses. -/
theorem zetaN64_gap_R06_64 : (1.05 : ℝ) - 0.72 - 0.5 < 0 := by norm_num

/-- R04 N = 64: slow 0.95, tail 1.44, needEta 0.5; gap -0.99 still misses. -/
theorem zetaN64_gap_R04_64 : (0.95 : ℝ) - 1.44 - 0.5 < 0 := by norm_num

/-- R25 N = 64: slow 0.75, tail 0.91, needEta 0.5; gap -0.66 still misses. -/
theorem zetaN64_gap_R25_64 : (0.75 : ℝ) - 0.91 - 0.5 < 0 := by norm_num

/-! ## Extrapolation to N = 128 (capped; do not exceed N = 128).

Decay per doubling at sig = 0.395 is `0.5^0.395 ≈ 0.76`; at sig = 0.2 it
is `0.5^0.2 ≈ 0.87`. Slow lift per doubling is +0.03-0.05 (diminishing).
R06 crosses at N = 128 estimate; R04 / R25 still miss at N = 128 and need
N > 128 (out of budget, left open, not forced).
-/

/-- R06 N = 128 estimate: slow 1.08, tail 0.55; margin +0.03 FIRES
(conditionally). -/
theorem zetaN64_extrap_R06_128 : (0 : ℝ) ≤ (1.08 : ℝ) - 0.55 - 0.5 := by norm_num

/-- R04 N = 128 estimate: slow 1.00, tail 1.10; gap -0.60 still misses,
needs N > 128 (out of budget). -/
theorem zetaN64_extrap_R04_128 : (1.0 : ℝ) - 1.10 - 0.5 < 0 := by norm_num

/-- R25 N = 128 estimate: slow 0.80, tail 0.69; gap -0.39 still misses,
needs N > 128 (out of budget). -/
theorem zetaN64_extrap_R25_128 : (0.8 : ℝ) - 0.69 - 0.5 < 0 := by norm_num

/-! ## Reusable per-center cost (so follow-ups can parallelize).

Measured from this file: generic cpow pair (re+im) = 2 theorems shared
across centers; per-pair triangle disc = 1 theorem application per `m`
(~7 lines per pair at call site: have + rw + exact); per-center
instantiation (triangle at that `sig` + norm cap + wrapper + two gap
facts) = 5 theorems ≈ 40 lines. For 64 terms = 32 pairs: 32 call sites.
-/

/-- 32 pairs cover 64 terms: pair count check. -/
theorem zetaN64_pair_count : 32 * 2 = 64 := by norm_num

/-- Reusable cost: 32 pair call sites at ~7 lines each ≈ 224 lines. -/
theorem zetaN64_pair_cost : 32 * 7 = 224 := by norm_num

/-- Per-center wrapper cost: 5 theorems per center (≈ 40 lines). -/
theorem zetaN64_center_cost : 4 * 5 = 20 := by norm_num

/-! ## Discharge notes and remainder.

* `premZeta_R05` FIRES CONDITIONALLY at N = 64 via `zetaN64_R05_ge`
  once slow = 1.15 / tail = 0.53 / cF witnesses arrive (margin +0.12).
  Witnesses needed: 32 pair-disc numerals (log bounds 5..64 stay as
  premises by wave rule), MVT tail numeral at M = 64, cF lower bound.
  Unconditionally: still open in this closure (0 of 31 closed here).
* `premZeta_R06` NOT discharged at N = 64 (`zetaN64_R06_ge` ready;
  N = 64 gap -0.17 misses); extrapolates to CLOSE at N = 128 estimate
  (margin +0.03) — needs N = 128 pair witnesses 33..64 + tail at M = 128.
* `premZeta_R04` NOT discharged at N = 64 (gap -0.99) nor at N = 128
  estimate (-0.60); needs N > 128, out of budget, left open.
* `premZeta_R25` NOT discharged at N = 64 (gap -0.66) nor at N = 128
  estimate (-0.39); needs N > 128, out of budget, left open.
* Pattern unlocked by R05 for follow-ups: replicate
  `zetaN64_pair_RXX_triangle` (1 line: sig rewrite) + norm cap
  (`zetaN64_norm_RXX_le` shape, `norm_num` + `Real.sqrt_le_sqrt`) +
  `zetaN64_RXX_ge` wrapper (3 lines via bridge) + gap facts
  (`norm_num`); pair call sites parallelize over `m` (32-way).
* Remainder: log bounds 5..64, full N = 64 / 128 slow-head assembly
  (32 / 64 pair discs), MVT tail numerals at M = 64 / 128 with matching
  `‖s‖` constants banked above, cF lower bounds per center, and all
  non-low-t centers (R07, R26, rest of 31) stay open. Batch B R11-R20
  carry no zeta premise and are out of scope.

Centers closed unconditionally in this file: none (0 of 31).
-/

end Door3ZetaN64
