import Mathlib
import door3_stirling_gamma
import door3_stirling_rem

/-!
# Door-3 complex Wendel transfer: real bounds to complex Gamma (WRITE-ONLY).

No build / lean / lake command run. No commit / push. Exactly one new file.
`door3_complex_wendel.lean` was verified absent via glob before writing.
Import DAG checked read-only:
`door3_stirling_gamma.lean:1` imports `Mathlib` only;
`door3_stirling_rem.lean:1-2` imports `Mathlib` + `door3_stirling_gamma` only.
This file imports `Mathlib` + those two upstream leaves only.

## Centers (confirmed read-only from `door3_digamma.lean:126-138` wire theorems)

`wOuter = mk 0.1975 (-4.375)`, `wLeaf = mk 0.1 (-3.375)`,
`wMid = mk 0.1975 (-2.375)`, `wInner = mk 0.1975 (-0.375)`.
Local defs below restate exactly these values (`rfl` facts).

## Recon (read-only, route-determining)

1. Hölder-for-integrals route: Mathlib banks `Real.convexOn_log_Gamma`
(BohrMollerup) and the two integral reps (`Complex.Gamma_eq_integral`,
`Real.Gamma_eq_integral`, both used by `D3SG_Gamma_norm_le_real`), plus
finite-sum Hölder (`inner_le_Lp_mul_Lq` family). No integral (Bochner) Hölder
with the right integrability side conditions is directly citable; threading
measurability + integrability of the split integrands + conjugate-exponent
setup + rpow algebra needs well over 8 supporting lemmas. PIVOT per brief.
2. Gautschi-via-recurrence route: the banked shift identity
`D3SG_gamma_shift_norm` gives `‖Γ(z+n)‖ = ‖Γ(z)‖ * Π‖z+k‖`, so
`‖Γ(z)‖ = ‖Γ(z+n)‖ / Π‖z+k‖` with fully explicit polynomial denominator.
The numerator at `w+n` is still complex, so this transports (does not create)
lowers. Norm-vs-real in Mathlib/banked set is UPPER-only
(`D3SG_Gamma_norm_le_real`); the only banked lower is the reflection bridge
`D3SR_gamma_lower_of_refl` (needs a sine upper `S` plus a companion upper).
Its Tier-C instantiation `D3SR_gamma_lower_TierC_of_sin` already covers
`Re ∈ [0.05, 0.95]` (all four centers qualify) modulo `S`, and its residual
names the missing lemma M1: `‖sin(πs)‖ ≤ exp(π|s.im|)` (up to constants).
This file CLOSES M1 (with constant 2) from the banked `Complex.sin_eq`
decomposition plus elementary real bounds, discharging the sine premise
unconditionally at all four centers.
3. Sibling shapes: PSI-SLOPE remainder M1-M4 (`door3_psi_slope.lean:360-366`):
(M1) complex Wendel two-sided, (M2) Gauss rep / digamma remainder,
(M3) real-to-complex digamma bridge, (M4) tight gamma uppers at
`Re ∈ {0.1, 0.1975}`. GAMMA-FEED (`door3_gamma_feed.lean:45-76`): 24
conditional implications `(0.77 ≤ ‖Γ(w+k)‖) → floor ≤ ‖gammaOf center‖`
with undischarged complex numerator premises; direct plug of `0.77` is
numerically false at large `|Im|` (shifted TRUE `‖Γ‖ ~ 0.001`).
Shape-mismatch notes: the conditional Wendel here is in norm/rpow form
(`‖Γ‖`, real powers of `‖z‖`), not the real log form, so it feeds (M1) only
after the interpolation premise lands; it does not touch (M2)/(M3). The
lowers here are at the `w` centers; feeding shifted `w+k` numerators uses
`wendel_complex_norm_div` (same `|Im|`, explicit denominator).

## Verdict (honest): FRAGMENT that closes priority (1) with a weak-but-explicit
discount `D`, plus conditional priority (2). No inflation: outer/leaf/mid
discounts are far below every in-lane floor; inner is marginal (see table).

All proofs full, explicit binders, small numerals only, no placeholders.
-/

noncomputable section

open scoped BigOperators

namespace Door3ComplexWendel

/-! ## 0. Centers (exact restatements of the digamma wire values). -/

noncomputable def wOuter : ℂ := Complex.mk 0.1975 (-4.375)

noncomputable def wLeaf : ℂ := Complex.mk 0.1 (-3.375)

noncomputable def wMid : ℂ := Complex.mk 0.1975 (-2.375)

noncomputable def wInner : ℂ := Complex.mk 0.1975 (-0.375)

theorem wOuter_re : wOuter.re = (0.1975 : ℝ) := rfl

theorem wOuter_im : wOuter.im = (-4.375 : ℝ) := rfl

theorem wLeaf_re : wLeaf.re = (0.1 : ℝ) := rfl

theorem wLeaf_im : wLeaf.im = (-3.375 : ℝ) := rfl

theorem wMid_re : wMid.re = (0.1975 : ℝ) := rfl

theorem wMid_im : wMid.im = (-2.375 : ℝ) := rfl

theorem wInner_re : wInner.re = (0.1975 : ℝ) := rfl

theorem wInner_im : wInner.im = (-0.375 : ℝ) := rfl

/-! ## 1. Sine upper M1 (closed): `‖sin z‖ ≤ 2 * exp |z.im|`.

Via banked `Complex.sin_eq`: `sin z = sin(x) * cosh(y) + cos(x) * sinh(y) * I`
with real `x = z.re`, `y = z.im`, using `|sin|,|cos| ≤ 1` and
`|sinh y| ≤ cosh y ≤ exp |y|` from `Real.cosh_add_sinh` / `Real.cosh_sub_sinh`.
-/

theorem sin_norm_le (z : ℂ) :
    ‖Complex.sin z‖ ≤ 2 * Real.exp |z.im| := by
  have hdecomp := Complex.sin_eq z
  rw [hdecomp]
  have hcosh_nn : (0 : ℝ) ≤ Real.cosh z.im := by
    have h4 := Real.cosh_add_sinh z.im
    have h2 := Real.cosh_sub_sinh z.im
    have e1 := (Real.exp_pos z.im).le
    have e2 := (Real.exp_pos (-z.im)).le
    linarith
  have hsinh_le : |Real.sinh z.im| ≤ Real.cosh z.im := by
    rw [abs_le]
    have h4 := Real.cosh_add_sinh z.im
    have h2 := Real.cosh_sub_sinh z.im
    have e1 := (Real.exp_pos z.im).le
    have e2 := (Real.exp_pos (-z.im)).le
    constructor <;> linarith
  have hexp : Real.cosh z.im ≤ Real.exp |z.im| := by
    have h4 := Real.cosh_add_sinh z.im
    have h2 := Real.cosh_sub_sinh z.im
    have e1 : Real.exp z.im ≤ Real.exp |z.im| :=
      Real.exp_le_exp.mpr (le_abs_self z.im)
    have e2 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
      Real.exp_le_exp.mpr (neg_le_abs z.im)
    linarith
  have hA : ‖((Real.sin z.re : ℝ) : ℂ) * ((Real.cosh z.im : ℝ) : ℂ)‖ ≤
      Real.exp |z.im| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcosh_nn]
    calc |Real.sin z.re| * Real.cosh z.im
        ≤ 1 * Real.cosh z.im :=
          mul_le_mul (Real.abs_sin_le_one _) (le_rfl _) hcosh_nn zero_le_one
      _ = Real.cosh z.im := one_mul _
      _ ≤ Real.exp |z.im| := hexp
  have hB : ‖((Real.cos z.re : ℝ) : ℂ) * ((Real.sinh z.im : ℝ) : ℂ) *
      Complex.I‖ ≤ Real.exp |z.im| := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |Real.cos z.re| * |Real.sinh z.im|
        ≤ 1 * Real.cosh z.im :=
          mul_le_mul (Real.abs_cos_le_one _) hsinh_le (abs_nonneg _) zero_le_one
      _ = Real.cosh z.im := one_mul _
      _ ≤ Real.exp |z.im| := hexp
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add hA hB) (le_of_eq ?_))
  ring

/-! ## 2. Sine nonvanishing on the strip (generic; needed by reflection). -/

theorem sin_pi_ne_zero (s : ℂ) (hlo : 0.05 ≤ s.re) (hhi : s.re ≤ 0.95) :
    Complex.sin (Real.pi * s) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hpi0 : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : s * ((Real.pi : ℝ) : ℂ) = ((k : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) := by
    rw [mul_comm s _]
    exact hk
  have hsk : s = ((k : ℤ) : ℂ) := mul_right_cancel₀ hpi0 h2
  have hre : s.re = ((k : ℤ) : ℝ) := by
    rw [hsk]
    simp
  have h1 : (0 : ℝ) < ((k : ℤ) : ℝ) := by linarith
  have h2r : (((k : ℤ)) : ℝ) < 1 := by linarith
  have g1 : (0 : ℤ) < k := by exact_mod_cast h1
  have g3 : k < 1 := by exact_mod_cast h2r
  omega

/-! ## 3. Real companion caps: `Γ ≤ 1` on `[1,2]`, shifted to `0.8025/0.9`. -/

theorem gamma_le_one_Icc12 (t : ℝ) (h1 : 1 ≤ t) (h2 : t ≤ 2) :
    Real.Gamma t ≤ 1 := by
  have ha : (0 : ℝ) ≤ 2 - t := by linarith
  have hb : (0 : ℝ) ≤ t - 1 := by linarith
  have hab : (2 - t) + (t - 1) = 1 := by ring
  have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have h2mem : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have hJ := Real.convexOn_Gamma.2 h1mem h2mem ha hb hab
  simp only [smul_eq_mul] at hJ
  have hpt : (2 - t) * 1 + (t - 1) * 2 = t := by ring
  rw [hpt, Real.Gamma_one, Real.Gamma_two] at hJ
  have he : (2 - t) * 1 + (t - 1) * 1 = 1 := by ring
  exact le_trans hJ (le_of_eq he)

theorem gamma_cap_08025 : Real.Gamma 0.8025 ≤ 1.25 := by
  have h1 : Real.Gamma (0.8025 + 1) ≤ 1 :=
    gamma_le_one_Icc12 _ (by norm_num) (by norm_num)
  have hne : (0.8025 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (0.8025 + 1) = 0.8025 * Real.Gamma 0.8025 :=
    Real.Gamma_add_one hne
  have hle : Real.Gamma 0.8025 ≤ 1 / 0.8025 := by
    rw [le_div_iff₀ (by norm_num), mul_comm, ← hshift]
    exact h1
  have hfin : (1 : ℝ) / 0.8025 ≤ 1.25 := by norm_num
  exact le_trans hle hfin

theorem gamma_cap_09 : Real.Gamma 0.9 ≤ 1.12 := by
  have h1 : Real.Gamma (0.9 + 1) ≤ 1 :=
    gamma_le_one_Icc12 _ (by norm_num) (by norm_num)
  have hne : (0.9 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (0.9 + 1) = 0.9 * Real.Gamma 0.9 :=
    Real.Gamma_add_one hne
  have hle : Real.Gamma 0.9 ≤ 1 / 0.9 := by
    rw [le_div_iff₀ (by norm_num), mul_comm, ← hshift]
    exact h1
  have hfin : (1 : ℝ) / 0.9 ≤ 1.12 := by norm_num
  exact le_trans hle hfin

/-! ## 4. Generic Im-discount lower (priority (1), closed).

`‖Γ(s)‖ ≥ π / (2 * exp(π|s.im|) * C)` for `Re s ∈ [0.05, 0.95]` with a real
companion cap `Γ(1 - Re s) ≤ C`. Proof: reflection bridge
`D3SR_gamma_lower_of_refl` + sine upper `sin_norm_le` + companion upper
`D3SG_Gamma_norm_le_real`.
-/

theorem im_discount_lower (s : ℂ) (hlo : 0.05 ≤ s.re) (hhi : s.re ≤ 0.95)
    (C : ℝ) (hC : Real.Gamma (1 - s.re) ≤ C) (hCpos : 0 < C) :
    Real.pi / (2 * Real.exp (Real.pi * |s.im|) * C) ≤
      ‖Complex.Gamma s‖ := by
  have hre1 : (1 - s).re = 1 - s.re := by simp
  have hpos1 : (0 : ℝ) < (1 - s).re := by
    rw [hre1]
    linarith
  have hG : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hpos1
  have hsin : Complex.sin (Real.pi * s) ≠ 0 :=
    sin_pi_ne_zero s hlo hhi
  have hbase := Door3StirlingRem.D3SR_gamma_lower_of_refl s hsin hG
  have him : (Real.pi * s).im = Real.pi * s.im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have habs : |Real.pi * s.im| = Real.pi * |s.im| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hS : ‖Complex.sin (Real.pi * s)‖ ≤
      2 * Real.exp (Real.pi * |s.im|) := by
    have h := sin_norm_le (Real.pi * s)
    rw [him, habs] at h
    exact h
  have hSpos : (0 : ℝ) < 2 * Real.exp (Real.pi * |s.im|) := by positivity
  have hGup : ‖Complex.Gamma (1 - s)‖ ≤ C := by
    have h := D3SG_Gamma_norm_le_real (1 - s) hpos1
    rw [hre1] at h
    exact le_trans h hC
  have hden : ‖Complex.sin (Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖ ≤
      (2 * Real.exp (Real.pi * |s.im|)) * C :=
    mul_le_mul hS hGup (norm_nonneg _) (le_of_lt hSpos)
  have hBIG : (0 : ℝ) < (2 * Real.exp (Real.pi * |s.im|)) * C :=
    mul_pos hSpos hCpos
  have hsinNorm : (0 : ℝ) < ‖Complex.sin (Real.pi * s)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hsin))
  have hGNorm : (0 : ℝ) < ‖Complex.Gamma (1 - s)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hG))
  have hle : Real.pi / ((2 * Real.exp (Real.pi * |s.im|)) * C) ≤
      Real.pi / (‖Complex.sin (Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    rw [div_le_div_left Real.pi_pos hBIG (mul_pos hsinNorm hGNorm)]
    exact hden
  exact le_trans hle hbase

/-! ## 5. Per-center discount lowers (closed, explicit `D`). -/

theorem lower_outer :
    Real.pi / (2 * Real.exp (Real.pi * 4.375) * 1.25) ≤
      ‖Complex.Gamma wOuter‖ := by
  have hlo : (0.05 : ℝ) ≤ wOuter.re := by
    rw [wOuter_re]
    norm_num
  have hhi : wOuter.re ≤ (0.95 : ℝ) := by
    rw [wOuter_re]
    norm_num
  have him : |wOuter.im| = (4.375 : ℝ) := by
    rw [wOuter_im]
    norm_num
  have hcomp : (1 : ℝ) - wOuter.re = 0.8025 := by
    rw [wOuter_re]
    norm_num
  have hC : Real.Gamma (1 - wOuter.re) ≤ 1.25 := by
    rw [hcomp]
    exact gamma_cap_08025
  have h := im_discount_lower wOuter hlo hhi 1.25 hC (by norm_num)
  rw [him] at h
  exact h

theorem lower_leaf :
    Real.pi / (2 * Real.exp (Real.pi * 3.375) * 1.12) ≤
      ‖Complex.Gamma wLeaf‖ := by
  have hlo : (0.05 : ℝ) ≤ wLeaf.re := by
    rw [wLeaf_re]
    norm_num
  have hhi : wLeaf.re ≤ (0.95 : ℝ) := by
    rw [wLeaf_re]
    norm_num
  have him : |wLeaf.im| = (3.375 : ℝ) := by
    rw [wLeaf_im]
    norm_num
  have hcomp : (1 : ℝ) - wLeaf.re = 0.9 := by
    rw [wLeaf_re]
    norm_num
  have hC : Real.Gamma (1 - wLeaf.re) ≤ 1.12 := by
    rw [hcomp]
    exact gamma_cap_09
  have h := im_discount_lower wLeaf hlo hhi 1.12 hC (by norm_num)
  rw [him] at h
  exact h

theorem lower_mid :
    Real.pi / (2 * Real.exp (Real.pi * 2.375) * 1.25) ≤
      ‖Complex.Gamma wMid‖ := by
  have hlo : (0.05 : ℝ) ≤ wMid.re := by
    rw [wMid_re]
    norm_num
  have hhi : wMid.re ≤ (0.95 : ℝ) := by
    rw [wMid_re]
    norm_num
  have him : |wMid.im| = (2.375 : ℝ) := by
    rw [wMid_im]
    norm_num
  have hcomp : (1 : ℝ) - wMid.re = 0.8025 := by
    rw [wMid_re]
    norm_num
  have hC : Real.Gamma (1 - wMid.re) ≤ 1.25 := by
    rw [hcomp]
    exact gamma_cap_08025
  have h := im_discount_lower wMid hlo hhi 1.25 hC (by norm_num)
  rw [him] at h
  exact h

theorem lower_inner :
    Real.pi / (2 * Real.exp (Real.pi * 0.375) * 1.25) ≤
      ‖Complex.Gamma wInner‖ := by
  have hlo : (0.05 : ℝ) ≤ wInner.re := by
    rw [wInner_re]
    norm_num
  have hhi : wInner.re ≤ (0.95 : ℝ) := by
    rw [wInner_re]
    norm_num
  have him : |wInner.im| = (0.375 : ℝ) := by
    rw [wInner_im]
    norm_num
  have hcomp : (1 : ℝ) - wInner.re = 0.8025 := by
    rw [wInner_re]
    norm_num
  have hC : Real.Gamma (1 - wInner.re) ≤ 1.25 := by
    rw [hcomp]
    exact gamma_cap_08025
  have h := im_discount_lower wInner hlo hhi 1.25 hC (by norm_num)
  rw [him] at h
  exact h

/-! ## 6. Per-center size audit (formal implications; numeric premises explicit).

Hand evaluation (reported honestly, not inflated):
outer `π/(2·e^13.75·1.25) ≈ 1.4e-6`, leaf `π/(2·e^10.60·1.12) ≈ 3.5e-5`,
mid `π/(2·e^7.46·1.25) ≈ 7.3e-4`, inner `π/(2·e^1.18·1.25) ≈ 0.39`.
The `exp` premises below are true hand-checked numerals, kept as explicit
hypotheses (not claimed as machine-checked facts).
-/

theorem outer_small (hpi : Real.pi ≤ 3.15)
    (he : (900000 : ℝ) ≤ Real.exp (Real.pi * 4.375)) :
    Real.pi / (2 * Real.exp (Real.pi * 4.375) * 1.25) ≤ 0.000002 := by
  have hden : (0 : ℝ) < 2 * Real.exp (Real.pi * 4.375) * 1.25 := by positivity
  rw [div_le_iff₀ hden]
  linarith

theorem leaf_small (hpi : Real.pi ≤ 3.15)
    (he : (40000 : ℝ) ≤ Real.exp (Real.pi * 3.375)) :
    Real.pi / (2 * Real.exp (Real.pi * 3.375) * 1.12) ≤ 0.00004 := by
  have hden : (0 : ℝ) < 2 * Real.exp (Real.pi * 3.375) * 1.12 := by positivity
  rw [div_le_iff₀ hden]
  linarith

theorem mid_small (hpi : Real.pi ≤ 3.15)
    (he : (1700 : ℝ) ≤ Real.exp (Real.pi * 2.375)) :
    Real.pi / (2 * Real.exp (Real.pi * 2.375) * 1.25) ≤ 0.0008 := by
  have hden : (0 : ℝ) < 2 * Real.exp (Real.pi * 2.375) * 1.25 := by positivity
  rw [div_le_iff₀ hden]
  linarith

theorem inner_big (hpi : (3.14 : ℝ) ≤ Real.pi)
    (he : Real.exp (Real.pi * 0.375) ≤ 3.3) :
    (0.38 : ℝ) ≤ Real.pi / (2 * Real.exp (Real.pi * 0.375) * 1.25) := by
  have hden : (0 : ℝ) < 2 * Real.exp (Real.pi * 0.375) * 1.25 := by positivity
  rw [le_div_iff₀ hden]
  linarith

/-! ## 7. Tier-C cross-check at the outer center (closed).

Uses the banked `D3SR_gamma_lower_TierC_of_sin` with the now-closed sine
upper. Weaker than `lower_outer` (constant 600 vs companion cap 1.25);
kept as the composition witness with the sibling lane.
-/

theorem tierC_outer :
    Real.pi / ((2 * Real.exp (Real.pi * 4.375)) *
      (600 * Real.exp (-(1 / 2) * 4.375))) ≤
      ‖Complex.Gamma wOuter‖ := by
  have hlo : (0.05 : ℝ) ≤ wOuter.re := by
    rw [wOuter_re]
    norm_num
  have hhi : wOuter.re ≤ (0.95 : ℝ) := by
    rw [wOuter_re]
    norm_num
  have him : |wOuter.im| = (4.375 : ℝ) := by
    rw [wOuter_im]
    norm_num
  have hre1 : (1 - wOuter).re = 1 - wOuter.re := by simp
  have hpos1 : (0 : ℝ) < (1 - wOuter).re := by
    rw [hre1, wOuter_re]
    norm_num
  have hG : Complex.Gamma (1 - wOuter) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hpos1
  have hsin : Complex.sin (Real.pi * wOuter) ≠ 0 :=
    sin_pi_ne_zero wOuter hlo hhi
  have him2 : (Real.pi * wOuter).im = Real.pi * wOuter.im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have habs : |Real.pi * wOuter.im| = Real.pi * |wOuter.im| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hS : ‖Complex.sin (Real.pi * wOuter)‖ ≤
      2 * Real.exp (Real.pi * 4.375) := by
    have h := sin_norm_le (Real.pi * wOuter)
    rw [him2, habs, him] at h
    exact h
  have hSpos : (0 : ℝ) < 2 * Real.exp (Real.pi * 4.375) := by positivity
  have h := Door3StirlingRem.D3SR_gamma_lower_TierC_of_sin
    wOuter hlo hhi _ hS hSpos hsin hG
  rw [him] at h
  exact h

/-! ## 8. Recurrence transport (closed, generic): the Gautschi division.

`‖Γ(z)‖ = ‖Γ(z+n)‖ / Π‖z+k‖` for `Re z > 0`. The denominator is fully
explicit; the numerator premise is the (still missing) shifted complex lower.
This is the exact shape GAMMA-FEED conditionals need at `n = 1, 2`.
-/

theorem prod_norm_pos (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    (0 : ℝ) < ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
  apply Finset.prod_pos
  intro k hk
  rw [norm_pos_iff]
  intro h
  have hRe := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
  have hkn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
  linarith

theorem wendel_complex_norm (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ * ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ =
      ‖Complex.Gamma (z + (n : ℂ))‖ := by
  have h := D3SG_gamma_shift_norm hz n
  exact h.symm

theorem wendel_complex_norm_div (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + (n : ℂ))‖ /
      ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
  have hpos := prod_norm_pos z hz n
  rw [eq_div_iff (ne_of_gt hpos)]
  exact (D3SG_gamma_shift_norm hz n).symm

/-! ## 9. Conditional complex Wendel (priority (2) fragment, closed).

Exactly one unproved premise is isolated: the Hölder interpolation upper
`hinterp` (proving it from the integral rep needs the measure-theoretic
Hölder chain, over budget). Given it, both complex Wendel halves follow by
the same recurrence mechanism as the real `D3SR_wendel_upper/lower` proofs,
in norm/rpow form. This does NOT yield psi discs: the slope-to-digamma limit
passage (PSI-SLOPE M3) and the Gauss rep (M2) remain open.
-/

theorem mk_ne_zero_of_re_pos (u y : ℝ) (hu : 0 < u) :
    Complex.mk u y ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  have hmx : (Complex.mk u y).re = u := rfl
  have hz : ((0 : ℂ)).re = 0 := Complex.zero_re
  rw [hmx] at hRe
  rw [hz] at hRe
  linarith

theorem gamma_mk_shift_norm (u y : ℝ) (hu : 0 < u) :
    ‖Complex.Gamma (Complex.mk (u + 1) y)‖ =
      ‖Complex.mk u y‖ * ‖Complex.Gamma (Complex.mk u y)‖ := by
  have hsh : Complex.mk u y + 1 = Complex.mk (u + 1) y := by
    ext <;> simp <;> norm_num
  have hne := mk_ne_zero_of_re_pos u y hu
  have hrec : Complex.Gamma (Complex.mk u y + 1) =
      Complex.mk u y * Complex.Gamma (Complex.mk u y) :=
    Complex.Gamma_add_one _ hne
  rw [hsh] at hrec
  rw [hrec, norm_mul]

theorem wendel_complex_upper_of_interp (x y s : ℝ) (hx : 0 < x)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hinterp : ∀ (u v : ℝ), 0 < u → 0 ≤ v → v ≤ 1 →
      ‖Complex.Gamma (Complex.mk (u + v) y)‖ ≤
        ‖Complex.Gamma (Complex.mk u y)‖ ^ (1 - v) *
          ‖Complex.Gamma (Complex.mk (u + 1) y)‖ ^ v) :
    ‖Complex.Gamma (Complex.mk (x + s) y)‖ ≤
      ‖Complex.mk x y‖ ^ s * ‖Complex.Gamma (Complex.mk x y)‖ := by
  have hGpos : (0 : ℝ) < ‖Complex.Gamma (Complex.mk x y)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by
      show (0 : ℝ) < (Complex.mk x y).re
      rw [show (Complex.mk x y).re = x from rfl]
      exact hx)
  have hzpos : (0 : ℝ) ≤ ‖Complex.mk x y‖ := norm_nonneg _
  have hup := hinterp x s hx hs0 hs1
  have hnorm1 := gamma_mk_shift_norm x y hx
  rw [hnorm1, Real.mul_rpow hzpos (le_of_lt hGpos)] at hup
  have hfold : ‖Complex.Gamma (Complex.mk x y)‖ ^ (1 - s) *
      ‖Complex.Gamma (Complex.mk x y)‖ ^ s =
      ‖Complex.Gamma (Complex.mk x y)‖ := by
    rw [← Real.rpow_add hGpos]
    have hrs : (1 - s) + s = 1 := by ring
    rw [hrs, Real.rpow_one]
  calc ‖Complex.Gamma (Complex.mk (x + s) y)‖
      ≤ ‖Complex.Gamma (Complex.mk x y)‖ ^ (1 - s) *
        (‖Complex.mk x y‖ ^ s * ‖Complex.Gamma (Complex.mk x y)‖ ^ s) := hup
    _ = ‖Complex.mk x y‖ ^ s *
        (‖Complex.Gamma (Complex.mk x y)‖ ^ (1 - s) *
          ‖Complex.Gamma (Complex.mk x y)‖ ^ s) := by ring
    _ = ‖Complex.mk x y‖ ^ s * ‖Complex.Gamma (Complex.mk x y)‖ := by
        rw [hfold]

theorem wendel_complex_lower_of_interp (x y s : ℝ) (hx : 0 < x)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hinterp : ∀ (u v : ℝ), 0 < u → 0 ≤ v → v ≤ 1 →
      ‖Complex.Gamma (Complex.mk (u + v) y)‖ ≤
        ‖Complex.Gamma (Complex.mk u y)‖ ^ (1 - v) *
          ‖Complex.Gamma (Complex.mk (u + 1) y)‖ ^ v) :
    ‖Complex.mk x y‖ * ‖Complex.Gamma (Complex.mk x y)‖ ≤
      ‖Complex.mk (x + s) y‖ ^ (1 - s) *
        ‖Complex.Gamma (Complex.mk (x + s) y)‖ := by
  have hxs : (0 : ℝ) < x + s := by linarith
  have h1s0 : (0 : ℝ) ≤ 1 - s := by linarith
  have h1s1 : 1 - s ≤ 1 := by linarith
  have hup := wendel_complex_upper_of_interp (x + s) y (1 - s)
    hxs h1s0 h1s1 hinterp
  have hcomb : (x + s) + (1 - s) = x + 1 := by ring
  rw [hcomb] at hup
  have hnorm1 := gamma_mk_shift_norm x y hx
  rw [hnorm1] at hup
  exact hup

theorem wendel_complex_two_sided (x y s : ℝ) (hx : 0 < x)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hinterp : ∀ (u v : ℝ), 0 < u → 0 ≤ v → v ≤ 1 →
      ‖Complex.Gamma (Complex.mk (u + v) y)‖ ≤
        ‖Complex.Gamma (Complex.mk u y)‖ ^ (1 - v) *
          ‖Complex.Gamma (Complex.mk (u + 1) y)‖ ^ v) :
    ‖Complex.mk x y‖ * ‖Complex.Gamma (Complex.mk x y)‖ ≤
      ‖Complex.mk (x + s) y‖ ^ (1 - s) *
        ‖Complex.Gamma (Complex.mk (x + s) y)‖ ∧
    ‖Complex.Gamma (Complex.mk (x + s) y)‖ ≤
      ‖Complex.mk x y‖ ^ s * ‖Complex.Gamma (Complex.mk x y)‖ :=
  And.intro
    (wendel_complex_lower_of_interp x y s hx hs0 hs1 hinterp)
    (wendel_complex_upper_of_interp x y s hx hs0 hs1 hinterp)

/-! ## 10. Remainder and bridge status.

Bridge status: FRAGMENT (priority (1) closed-but-weak; priority (2)
conditional on one named premise; full transfer impossible with these
numbers — see table).

Per-center sufficiency table (discount `D` = closed lower; need = in-lane
floors / numerator thresholds; hand values from section 6):
* outer `|y| = 4.375`: `D ≈ 1.4e-6` (formal: `≤ 2e-6`). Need: BA00 floor
  `0.0015`; GAMMA-FEED numerator threshold at `0.77` is `0.00687`.
  INSUFFICIENT by ~3 orders of magnitude. Matches the brief's warning that
  `e^{-π|y|}`-scale discounts cannot touch floors `~0.026`.
* leaf `|y| = 3.375`: `D ≈ 3.5e-5` (formal: `≤ 4e-5`). Need: leaf-adjacent
  floors `≥ 0.001`, thresholds `≥ 0.00458`. INSUFFICIENT by ~2 orders.
* mid `|y| = 2.375`: `D ≈ 7.3e-4` (formal: `≤ 8e-4`). Need: BA03 floor
  `0.015`, thresholds `≥ 0.00458`. INSUFFICIENT (within ~20x of the floor,
  closest of the three large-`|Im|` centers, still short).
* inner `|y| = 0.375`: `D ≈ 0.39` (formal: `≥ 0.38`). Need: inner floors
  (`0.2`-scale cells pass; floor `2` fails). MARGINAL/PARTIAL: the only
  center where the discount is mild enough to feed small floors. The
  shifted-numerator use additionally needs `wendel_complex_norm_div`.

Remainder (precise missing-lemma names):
* H1 (sole premise of section 9): Hölder interpolation upper for the complex
  Gamma integral, `‖Γ((u+v)+iy)‖ ≤ ‖Γ(u+iy)‖^(1-v) * ‖Γ((u+1)+iy)‖^v`
  (`u > 0`, `v ∈ [0,1]`, uniform in `y`). Needs the Bochner-Hölder chain
  with integrability side conditions: over the 10-lemma cap, hence isolated
  as hypothesis rather than proved.
* H2: polynomial factor `|y|^{x-1/2}` for a Stirling-rate complex lower
  (needs complex log-Gamma remainder / Binet bounds; unbanked).
* H3: slope-to-digamma limit passage `‖digamma w - (log w - 1/(2w))‖ ≤ C/‖w‖^2`
  (needs the Gauss rep; Mathlib TODO). PSI-SLOPE M2/M3/M4 untouched here.
* Honest finding: the Im-discount route via reflection tops out at
  `π/(2·e^{π|y|}·C)` — rate `π ≈ 3.14` in the exponent — so no tuning of
  this lane can reach large-`|Im|` floors. Full complex Stirling is required.

This file was written without running any build; it is not machine-checked.
-/

end Door3ComplexWendel
