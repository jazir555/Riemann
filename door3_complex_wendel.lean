import Mathlib
import door3_stirling_gamma
import door3_stirling_rem
import Zeta23.GammaFacts.StirlingVert

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

/-! ## 11. H3 attempt (WENDEL-H2 wave): verdict GAP, filed without force.

Greps (this file + banked leaves, before edit):
- this file: zero hits for `Complex.log`, `1 / (2`, `digamma_apply_add_one`,
  `Binet`, `logGamma` outside comments (only M2 Gauss-rep mentions `:44,469,592-593`).
- banked `D3SG_*` (`door3_stirling_gamma`): uppers / shift-norm / real caps only
  (`D3SG_Gamma_norm_le_real`, `D3SG_gamma_shift_norm`); no `log w`, no `1/(2*w)`.
- banked `D3SR_*` (`door3_stirling_rem:63-265`): real Wendel / slope / reflection
  lower only; `:272-281` names M2 (Binet / complex log-Gamma remainder, unbanked)
  and M3 (Gauss digamma rep, Mathlib TODO, unbanked).
- Mathlib banked feeder: `Complex.digamma_apply_add_one`
  (reused `door3_digamma.lean:183-185` `psi_up_one`, `:187-223` `psi_shift_nat`).
- Mathlib TODO (unbanked): Gauss integral rep of digamma
  (`door3_stirling_rem:277-281`, `door3_digamma.lean:14,45,53,555`).

Pick: H3 over H2. H2/Binet has zero feeders anywhere (in-repo Binet unsupported);
H3 has one banked recurrence feeder. H3 still does NOT close from banked pieces:
`‖digamma w - (log w - 1/(2*w))‖ ≤ C/‖w‖^2` needs a Gauss disc at a large shift
plus the log-shift expansion, both unbanked. Filed below as explicit hypotheses.
-/

theorem digamma_shift_banked (w : ℂ) (h : ∀ m : ℕ, w ≠ -(m : ℂ)) :
    Complex.digamma (w + 1) = Complex.digamma w + w⁻¹ :=
  Complex.digamma_apply_add_one w h

theorem h3_transport_of_shifted_disc (w cN S : ℂ) (N : ℕ) (rN : ℝ)
    (hEq : Complex.digamma (w + ((N : ℕ) : ℂ)) = Complex.digamma w + S)
    (hDisc : ‖Complex.digamma (w + ((N : ℕ) : ℂ)) - cN‖ ≤ rN) :
    ‖Complex.digamma w - (cN - S)‖ ≤ rN := by
  have hEq2 : Complex.digamma w =
      Complex.digamma (w + ((N : ℕ) : ℂ)) - S := by
    rw [hEq]
    ring
  have hSame : Complex.digamma w - (cN - S) =
      Complex.digamma (w + ((N : ℕ) : ℂ)) - cN := by
    rw [hEq2]
    ring
  rw [hSame]
  exact hDisc

/-! H3 GAP (exact missing feeders, no force):
G1 (Gauss disc, unbanked): `‖digamma (w+N) - (log (w+N) - 1/(2*(w+N)))‖ ≤ rN`
  with `rN = C/‖w+N‖^2` for the four `w` centers at some explicit `N, C`.
  Needs the Gauss integral rep of `Complex.digamma` (Mathlib TODO cited above).
G2 (log-shift link, unbanked): `‖(cN - S) - (log w - 1/(2*w))‖` bound where
  `S = ∑ k ∈ range N, (w+k)⁻¹`, i.e. the Stirling log-expansion of the
  recurrence sum. Needs complex log-Gamma remainder / Binet bounds (unbanked).
With G1+G2, `h3_transport_of_shifted_disc` + triangle inequality would yield H3;
neither G1 nor G2 is banked, so H3 is NOT proved here. H2 not attempted (strictly
farther: Binet zero feeders). No `sorry`/`admit`/`axiom`; no new imports.
-/

/-! ## 12. WENDEL-G1 attempt (PROOF-ONLY, FENCED, no build): verdict GAP, filed without force.

Target (ONE large-Re point): `wOuter + 8 = mk 8.1975 (-4.375)` (Re 8.1975 > 0,
same Im as `wOuter`; matches `door3_digamma` shift `N = 8` landing Re ~ 8.1).
Desired G1 disc: `‖digamma (wOuter+8) - (log (wOuter+8) - 1/(2*(wOuter+8)))‖ ≤ rN`
with `rN = C/‖wOuter+8‖^2` for explicit `C`.

Integral-rep greps (before edit, this turn):
- `Complex.GammaIntegral` def + `Complex.Gamma_eq_integral` +
  `Real.Gamma_eq_integral` + `tendsto_partialGamma`:
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:110,149,318`
  (Gamma ONLY; indefinite `partialGamma` + limit to `GammaIntegral`).
- `Complex.digamma` def `:= logDeriv Gamma`:
  `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean:39`;
  `digamma_def:41`, `digamma_apply_add_one:55`, `meromorphic_digamma:61`;
  TODO `Digamma.lean:31` "Prove Gauss integral representation of digamma".
  Zero hits for a digamma integral rep (no `GammaIntegral`-analogue for psi).
- `BohrMollerup.logGammaSeq`:
  `Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:140`
  (real-only, qualitative limit, no rate, no complex `logGamma`, no Binet).
- Real secant banked: `door3_psi_slope.lean:99-114` (`slopeS/loBound/hiBound/midPt/radPt`)
  + slope bounds; `door3_psi_slope.lean:37-44,56-59,350-366` explicitly bars
  complex-`w` use (no complex log-Gamma convexity, no psi bridge).
- Recurrence feeder banked: `Complex.digamma_apply_add_one` reused
  `door3_digamma.lean:184-185,204-206`, `door3_complex_wendel.lean:619-621`;
  transports a disc down but does not create the large-Re disc.

Why recurrence + real secant does NOT honestly close G1 here:
1. Recurrence shifts `psi w <-> psi (w+N)` exactly but needs the large-Re disc
   as premise (`h3_transport_of_shifted_disc` above); it cannot manufacture
   `‖psi (w+N) - cN‖ ≤ rN`.
2. Real secant controls `(logG (X+h) - logG (X-h))/(2*h)` at real `X ~ 8.1`
   with zero Im; `wOuter+8` has Im `-4.375`; no banked lemma moves a real
   secant bound to a `Complex.digamma` disc at nonzero Im
   (PSI-SLOPE M3 open; this file section 9 H1 open).
3. Gamma-integral reps bound `‖Gamma‖` (upper-only `D3SG_Gamma_norm_le_real`),
   not psi; differentiating under the integral to reach psi needs the missing
   Gauss psi rep + log-Gamma remainder chain (over budget).

Verdict: GAP (no force). No `sorry`/`admit`/`axiom`/`simpa`; no new imports;
no other files touched.

Exact missing piece G1 (formal shape, filed as Prop, NOT claimed):
`G1_outerN8_prop C` below. Needs Gauss integral rep of `Complex.digamma`
(Mathlib TODO `Digamma.lean:31`) + Stirling remainder.

Note (not claimed as G1, out-of-scope provenance, for coordinator):
`Zeta23/GammaFacts/StirlingVert.lean:483-484` `digamma_stirling` proves
`‖psi w - log w + (1/2)/w‖ ≤ 3/Im^2` for `0 < Re w`, `1/2 ≤ |Im w|`
via DigammaSeries (not Gauss integral), which would apply at `wOuter+8`
(`|Im| = 4.375`) with radius `3/4.375^2` -- but denominator is `Im^2` not
`‖w‖^2`, and importing `Zeta23.GammaFacts.StirlingVert` is outside this
file's `Mathlib + two leaves` DAG and outside the fenced
Gauss-integral / recurrence+secant brief, so NOT used here.
-/

noncomputable def G1_outerN8_prop (C : ℝ) : Prop :=
  ‖Complex.digamma (wOuter + (8 : ℂ)) -
    (Complex.log (wOuter + (8 : ℂ)) - (1 : ℂ) / (2 * (wOuter + (8 : ℂ))))‖ ≤
    C / ‖wOuter + (8 : ℂ)‖ ^ 2

/-! ## 13. WENDEL-G2 attempt (PROOF-ONLY, FENCED, no build): verdict GAP, filed without force.

Target (matches G1, section 12): `w = wOuter`, `N = 8`.
Desired G2 link: `‖(cN - S) - (log w - 1/(2*w))‖ ≤ C2/‖w‖^2` where
`cN = log (w+8) - 1/(2*(w+8))`, `S = ∑ k ∈ range 8, (w+k)⁻¹`.

Log-shift greps (before edit, this turn):
- this file: `Complex.log` only at `G1_outerN8_prop` (`:708`);
  `1 / (2` only at `:708` (G1 shape); `cN`/`S` sum shapes only in
  `h3_transport_of_shifted_disc` (`:623-636`) and the H3-GAP note
  (`:642-644`); zero hits for `Binet`, `logGamma` outside comments
  (`:591,602,606,613`); zero hits for a `Complex.log`-Taylor remainder
  chain yielding the `log (w+N)`-to-`log w` expansion with `1/(2w)`.
- banked `D3SG_*`: uppers / shift-norm / real caps only; no `Complex.log`,
  no `1/(2*w)` (this file `:603-604`).
- banked `D3SR_*` (`door3_stirling_rem:63-265`): real Wendel / slope /
  reflection lower only; `:272-281` names the complex log-Gamma remainder /
  Binet route as unbanked (this file `:605-607`).
- Mathlib real log bounds (`log_le_sub_one_of_pos`, `add_one_le_exp` in
  `Log/Basic.lean`): real-only, no complex `log` expansion, no `1/(2w)`
  Stirling correction term.
- Mathlib complex log Taylor (`Log/Deriv.lean:217-404`
  `abs_log_sub_add_sum_range_le`, `hasSum_log_sub_log_of_abs_lt_one`):
  real-variable (`x : ℝ`, `|x| < 1`) series bounds only; no
  `Complex.log (w+k)`-vs-`Complex.log w` shift expansion at `‖w‖ ~ 4-9`
  with nonzero Im, and nothing producing the `-1/(2w)` term.
- `harmonic_le_one_add_log` (used `KadiriDigammaBound.lean:194`): real
  harmonic head `H_N ≤ 1 + log N` only; no `∑ (w+k)⁻¹` vs `log` link at
  complex shifts, no `1/(2w)` correction.

Why no honest close: the G2 link is the Stirling expansion of the digamma
recurrence sum `S = ∑ (w+k)⁻¹` against `log (w+N) - log w` with the
`-1/(2w)` endpoint correction. Its remainder is exactly the complex
log-Gamma / Binet remainder, unbanked everywhere (in-repo `Binet` is
Fibonacci/CrossProduct only; `Complex.logGamma` absent as API;
`BohrMollerup.logGammaSeq` real-only qualitative limit, no rate). The
real-variable log Taylor bounds above cannot supply the complex shift
expansion plus correction term. Filed below as explicit Prop, no force.

Banked here (proved, no new axioms): `h3_outer_of_G1_G2` — G1 disc + G2
link + shift identity imply the H3 disc at `wOuter` by the transport
mechanism of `h3_transport_of_shifted_disc` plus triangle inequality.
The shift identity itself (`hEq`) stays a hypothesis (eightfold iteration
of `digamma_shift_banked`); G1/G2 remain Props.

Verdict: GAP (no force). No `sorry`/`admit`/`axiom`/`simpa`; no new imports;
no other files touched.
-/

noncomputable def S_outerN8 : ℂ :=
  ∑ k ∈ Finset.range 8, (wOuter + (k : ℂ))⁻¹

noncomputable def cN_outerN8 : ℂ :=
  Complex.log (wOuter + (8 : ℂ)) - (1 : ℂ) / (2 * (wOuter + (8 : ℂ)))

noncomputable def target_outer : ℂ :=
  Complex.log wOuter - (1 : ℂ) / (2 * wOuter)

noncomputable def G2_outerN8_prop (C2 : ℝ) : Prop :=
  ‖(cN_outerN8 - S_outerN8) - target_outer‖ ≤ C2 / ‖wOuter‖ ^ 2

theorem h3_outer_of_G1_G2 (C1 C2 : ℝ)
    (hEq : Complex.digamma (wOuter + (8 : ℂ)) =
      Complex.digamma wOuter + S_outerN8)
    (hG1 : G1_outerN8_prop C1) (hG2 : G2_outerN8_prop C2) :
    ‖Complex.digamma wOuter - target_outer‖ ≤
      C1 / ‖wOuter + (8 : ℂ)‖ ^ 2 + C2 / ‖wOuter‖ ^ 2 := by
  have hDisc : ‖Complex.digamma (wOuter + (8 : ℂ)) - cN_outerN8‖ ≤
      C1 / ‖wOuter + (8 : ℂ)‖ ^ 2 := hG1
  have hLink : ‖(cN_outerN8 - S_outerN8) - target_outer‖ ≤
      C2 / ‖wOuter‖ ^ 2 := hG2
  have hT : ‖Complex.digamma wOuter - (cN_outerN8 - S_outerN8)‖ ≤
      C1 / ‖wOuter + (8 : ℂ)‖ ^ 2 := by
    have hSame : Complex.digamma wOuter - (cN_outerN8 - S_outerN8) =
        Complex.digamma (wOuter + (8 : ℂ)) - cN_outerN8 := by
      rw [hEq]
      ring
    rw [hSame]
    exact hDisc
  have hSplit : Complex.digamma wOuter - target_outer =
      (Complex.digamma wOuter - (cN_outerN8 - S_outerN8)) +
        ((cN_outerN8 - S_outerN8) - target_outer) := by
    ring
  calc ‖Complex.digamma wOuter - target_outer‖
      ≤ ‖Complex.digamma wOuter - (cN_outerN8 - S_outerN8)‖ +
        ‖(cN_outerN8 - S_outerN8) - target_outer‖ := by
          rw [hSplit]
          exact norm_add_le _ _
    _ ≤ C1 / ‖wOuter + (8 : ℂ)‖ ^ 2 + C2 / ‖wOuter‖ ^ 2 :=
          add_le_add hT hLink

/-! ## 14. WENDEL-G1 StirlingVert lead (PROOF-ONLY, FENCED, no build): native instance BANKED.

Lead: `Zeta23/GammaFacts/StirlingVert.lean:483-484` `digamma_stirling`
(qualified `Zeta23.StirlingVert.digamma_stirling`; `section Seq (:169)` adds no
namespace component; `variable {w : ℂ}` at `:170`, so `w` is implicit;
exact hypotheses `0 < w.re`, `1 / 2 ≤ |w.im|`; conclusion
`‖ψ w - log w + (1/2)/w‖ ≤ 3 / w.im ^ 2`; proof body `:484-540`).

Import DAG (read-only checks this turn, no cycle):
- `StirlingVert.lean:16` imports `Zeta23.GammaFacts.Mu` + Mathlib libs only;
  `Mu.lean:14` imports `Zeta23.Analytic.Stirling` + Mathlib only.
- grep `door3` over the `Zeta23/` tree: zero hits, so no Zeta23 module imports
  any `door3_*` leaf; grep `import.*door3_complex_wendel` over the repo:
  zero hits, so nothing imports this file. Hence the added
  `import Zeta23.GammaFacts.StirlingVert` creates no cycle.
- Cost (not a blocker): this widens the file DAG beyond the header's
  `Mathlib + two leaves` claim (header left intact as write-history; this
  section records the superseding import). No other file touched.

Applicability at `wOuter + 8`: `Re = 8.1975 > 0`, `Im = -4.375`,
`|Im| = 4.375 ≥ 1/2` — both hypotheses discharge below (via a
`((8:ℕ):ℂ) = (8:ℂ)` cast bridge since only `Complex.natCast_re/im`
(`Basic.lean:355-356`) are simp; no `OfNat_re` simp lemma exists).
Banked in NATIVE `Im^2` form; numeral `3 / (-4.375)^2 ≤ 0.157` by `norm_num`
(exact value `192/1225 ≈ 0.156735`).

Residual (filed, no force): the section-12 `G1_outerN8_prop` wants
`C / ‖wOuter + 8‖^2` with `‖wOuter+8‖^2 = 8.1975^2 + 4.375^2 ≈ 86.34`,
while the banked denominator is `Im^2 = 19.140625`. Since `Im^2 ≤ ‖w‖^2`
the native radius goes the wrong way for small `C`; conversion needs
`C ≥ 3 * 86.34 / 19.14 ≈ 13.54` (hand arithmetic, not claimed checked).
So G1-as-filed stays Prop; the Gauss-`‖w‖^2`-shape claim is NOT closed here.
No `sorry`/`admit`/`axiom`/`simpa`.
-/

theorem wOuter_add8_re : (wOuter + (8 : ℂ)).re = 8.1975 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_re, wOuter_re, Complex.natCast_re]
  norm_num

theorem wOuter_add8_im : (wOuter + (8 : ℂ)).im = -4.375 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_im, wOuter_im, Complex.natCast_im]
  norm_num

theorem stirling_wOuter_add8 :
    ‖Complex.digamma (wOuter + (8 : ℂ)) - Complex.log (wOuter + (8 : ℂ)) +
      (1 / 2 : ℂ) / (wOuter + (8 : ℂ))‖ ≤ 3 / (-4.375) ^ 2 := by
  have hre : (0 : ℝ) < (wOuter + (8 : ℂ)).re := by
    rw [wOuter_add8_re]
    norm_num
  have him : (1 / 2 : ℝ) ≤ |(wOuter + (8 : ℂ)).im| := by
    rw [wOuter_add8_im]
    norm_num
  have h := Zeta23.StirlingVert.digamma_stirling (w := wOuter + (8 : ℂ)) hre him
  rw [wOuter_add8_im] at h
  exact h

theorem stirling_wOuter_add8_cap :
    ‖Complex.digamma (wOuter + (8 : ℂ)) - Complex.log (wOuter + (8 : ℂ)) +
      (1 / 2 : ℂ) / (wOuter + (8 : ℂ))‖ ≤ 0.157 := by
  refine le_trans stirling_wOuter_add8 ?_
  norm_num

This file was written without running any build; it is not machine-checked.
-/

/-! ## 15. WENDEL-HEQ 8-fold shift (PROOF-ONLY, FENCED): BANKED.

Greps (before edit, this turn):
- exact one-step shift `digamma_shift_banked` at `:620-622`:
  `(w : ℂ) (h : ∀ m : ℕ, w ≠ -(m : ℂ)) :
   Complex.digamma (w + 1) = Complex.digamma w + w⁻¹`
  proved by `Complex.digamma_apply_add_one`.
- pole-avoidance pattern mirrored from `door3_digamma.lean:247-258`
  (`shift_avoid_of_re_pos` + `avoid_outer` at `N = 8`): Re-positive
  center gives `(w + (k : ℂ)) ≠ -((m : ℕ) : ℂ)` via `Complex.re`.
- `h3_outer_of_G1_G2` hypothesis `:774-775`:
  `Complex.digamma (wOuter + (8 : ℂ)) = Complex.digamma wOuter + S_outerN8`.

Banked here (proved, induction on `digamma_shift_banked`, no new axioms):
`digamma_shift_nat` (general N) → `digamma_shift_8fold` (N = 8) →
`digamma_shift_wOuter_8` (exact `hEq` shape for `h3_outer_of_G1_G2`).
H3 then needs only G1 + G2. No `sorry`/`admit`/`axiom`; no `simpa` tactic;
no new imports; no other files touched.
-/

theorem wOuter_re_pos : 0 < wOuter.re := by
  rw [wOuter_re]
  norm_num

theorem shift_avoid_of_re_pos (w : ℂ) (N : ℕ) (hw : 0 < w.re) (k : ℕ)
    (hk : k ≤ N) (m : ℕ) : (w + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
  intro hCon
  have hR := congrArg Complex.re hCon
  simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at hR
  have hm : (0 : ℝ) ≤ (((m : ℕ)) : ℝ) := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ (((k : ℕ)) : ℝ) := Nat.cast_nonneg k
  linarith

theorem wOuter_shift_avoid (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wOuter + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) :=
  shift_avoid_of_re_pos wOuter 8 wOuter_re_pos k hk m

theorem digamma_shift_nat (w : ℂ) (N : ℕ)
    (h : ∀ (k : ℕ), k ≤ N → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ)) :
    Complex.digamma (w + (((N : ℕ)) : ℂ)) =
      Complex.digamma w + ∑ k ∈ Finset.range N, (w + (((k : ℕ)) : ℂ))⁻¹ := by
  revert h
  induction N with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro h
    have hle : ∀ (k : ℕ), k ≤ n → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
      intro k hk m
      exact h k (le_trans hk (Nat.le_succ n)) m
    have ihw := ih hle
    have hcast : (((n + 1 : ℕ)) : ℂ) = (((n : ℕ)) : ℂ) + 1 := by
      push_cast
    have hstep : Complex.digamma ((w + (((n : ℕ)) : ℂ)) + 1) =
        Complex.digamma (w + (((n : ℕ)) : ℂ)) + (w + (((n : ℕ)) : ℂ))⁻¹ :=
      digamma_shift_banked _ (h n (Nat.le_succ n))
    have hsum : ∑ k ∈ Finset.range (n + 1), (w + (((k : ℕ)) : ℂ))⁻¹ =
        (∑ k ∈ Finset.range n, (w + (((k : ℕ)) : ℂ))⁻¹) +
          (w + (((n : ℕ)) : ℂ))⁻¹ :=
      Finset.sum_range_succ _ n
    calc Complex.digamma (w + (((n + 1 : ℕ)) : ℂ))
        = Complex.digamma ((w + (((n : ℕ)) : ℂ)) + 1) := by
          rw [hcast, add_assoc]
      _ = Complex.digamma (w + (((n : ℕ)) : ℂ)) +
          (w + (((n : ℕ)) : ℂ))⁻¹ := hstep
      _ = (Complex.digamma w +
          ∑ k ∈ Finset.range n, (w + (((k : ℕ)) : ℂ))⁻¹) +
          (w + (((n : ℕ)) : ℂ))⁻¹ := by
          rw [ihw]
      _ = Complex.digamma w +
          ∑ k ∈ Finset.range (n + 1), (w + (((k : ℕ)) : ℂ))⁻¹ := by
          rw [hsum]
          ring

theorem digamma_shift_8fold (w : ℂ)
    (h : ∀ (k : ℕ), k ≤ 8 → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ)) :
    Complex.digamma (w + (((8 : ℕ)) : ℂ)) =
      Complex.digamma w + ∑ k ∈ Finset.range 8, (w + (((k : ℕ)) : ℂ))⁻¹ :=
  digamma_shift_nat w 8 h

theorem digamma_shift_wOuter_8 :
    Complex.digamma (wOuter + (8 : ℂ)) =
      Complex.digamma wOuter + S_outerN8 := by
  have hAvoid : ∀ (k : ℕ), k ≤ 8 → ∀ (m : ℕ),
      (wOuter + ((k : ℕ) : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
    intro k hk m
    exact wOuter_shift_avoid k hk m
  have h := digamma_shift_8fold wOuter hAvoid
  have hcast8 : (((8 : ℕ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast8] at h
  unfold S_outerN8
  exact h

/-! ## 16. WENDEL-G1 chain attempt (hEq + StirlingVert lead): GAP with exact residual.

Greps (before edit, this turn, this file only):
- `G1_outerN8_prop` at `:707` (def), `:694,719,776,829` (cites);
  `G2_outerN8_prop` at `:770` (def), `:776` (use);
  `S_outerN8/:761`, `cN_outerN8/:764`, `target_outer/:767`;
- `hEq` binder at `:625,774` (`h3_outer_of_G1_G2` hypothesis shape
  `digamma (wOuter+8) = digamma wOuter + S_outerN8`);
  banked close `digamma_shift_wOuter_8` at `:951`;
- H3 combiner `h3_outer_of_G1_G2` at `:773`;
  lead `stirling_wOuter_add8` at `:848`, cap `:861`;
- tactic greps `sorry|admit|axiom|simpa`: comment-only mentions
  (`:648,690,757,835,886`); zero tactic uses.

Attempt (honest chain): rewrite the StirlingVert lead into the exact G1
expression shape (`half_div_eq`), bank it in native `Im^2` form
(`stirling_G1expr_im2`), then give the exact inflation conditional
(`G1_of_normcap`) plus the hEq+lead+G2 H3 chain
(`h3_outer_of_lead_normcap_G2`). The `‖w‖^2`-denominator G1 as filed
(`G1_outerN8_prop`) does NOT follow from the lead alone: `Im^2 ≤ ‖w‖^2`
goes the wrong way, so conversion needs an explicit norm cap
`‖wOuter+8‖^2 ≤ U` plus `3*U ≤ C*(-4.375)^2`, filed as hypotheses.
G2 stays Prop. Hence G1/G2 open, H3 not closed here.
No `sorry`/`admit`/`axiom`/`simpa`; no new imports; this section only.
-/

theorem half_div_eq (w : ℂ) : (1 / 2 : ℂ) / w = 1 / (2 * w) := by
  ring

theorem stirling_G1expr_im2 :
    ‖Complex.digamma (wOuter + (8 : ℂ)) -
      (Complex.log (wOuter + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wOuter + (8 : ℂ))))‖ ≤
      3 / (-4.375) ^ 2 := by
  have hhalf : (1 / 2 : ℂ) / (wOuter + (8 : ℂ)) =
      (1 : ℂ) / (2 * (wOuter + (8 : ℂ))) :=
    half_div_eq _
  have hrewrite : Complex.digamma (wOuter + (8 : ℂ)) -
      (Complex.log (wOuter + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wOuter + (8 : ℂ)))) =
      Complex.digamma (wOuter + (8 : ℂ)) - Complex.log (wOuter + (8 : ℂ)) +
        (1 / 2 : ℂ) / (wOuter + (8 : ℂ)) := by
    rw [hhalf]
    ring
  rw [hrewrite]
  exact stirling_wOuter_add8

theorem G1_of_normcap (C U : ℝ)
    (hU : ‖wOuter + (8 : ℂ)‖ ^ 2 ≤ U)
    (hC : 3 * U ≤ C * (-4.375) ^ 2) :
    G1_outerN8_prop C := by
  have hIm2pos : (0 : ℝ) < (-4.375) ^ 2 := by
    norm_num
  have hne : wOuter + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wOuter_add8_re, Complex.zero_re] at hR
    norm_num at hR
  have hnormpos : (0 : ℝ) < ‖wOuter + (8 : ℂ)‖ :=
    norm_pos_iff.mpr hne
  have hnorm2pos : (0 : ℝ) < ‖wOuter + (8 : ℂ)‖ ^ 2 :=
    pow_pos hnormpos 2
  have hle : 3 / (-4.375) ^ 2 ≤ C / ‖wOuter + (8 : ℂ)‖ ^ 2 := by
    rw [div_le_div_iff hIm2pos hnorm2pos]
    have h3 : 3 * ‖wOuter + (8 : ℂ)‖ ^ 2 ≤ 3 * U :=
      mul_le_mul_of_nonneg_left hU (by norm_num)
    linarith
  have hmain := stirling_G1expr_im2
  unfold G1_outerN8_prop
  exact le_trans hmain hle

theorem h3_outer_of_lead_normcap_G2 (C U C2 : ℝ)
    (hU : ‖wOuter + (8 : ℂ)‖ ^ 2 ≤ U)
    (hC : 3 * U ≤ C * (-4.375) ^ 2)
    (hG2 : G2_outerN8_prop C2) :
    ‖Complex.digamma wOuter - target_outer‖ ≤
      C / ‖wOuter + (8 : ℂ)‖ ^ 2 + C2 / ‖wOuter‖ ^ 2 := by
  have hG1 : G1_outerN8_prop C :=
    G1_of_normcap C U hU hC
  have hEq : Complex.digamma (wOuter + (8 : ℂ)) =
      Complex.digamma wOuter + S_outerN8 :=
    digamma_shift_wOuter_8
  exact h3_outer_of_G1_G2 C C2 hEq hG1 hG2

/-! G1 residual (exact, no force): `G1_outerN8_prop C` needs
`hU : ‖wOuter+8‖^2 ≤ U` (explicit norm cap, e.g. from
`‖w‖^2 = Re^2+Im^2 = 8.1975^2+4.375^2`) plus
`hC : 3*U ≤ C*(-4.375)^2` (C-inflation, hand ratio `≈ 13.54`);
`G2_outerN8_prop C2` (log-shift link, Binet remainder, unbanked) still open;
hence H3 via `h3_outer_of_lead_normcap_G2` stays conditional. Value banked:
native-`Im^2` G1-expression disc `stirling_G1expr_im2`; gap: norm-cap U + G2.
-/

/-! ## 17. WENDEL-G2 chain attempt (PROOF-ONLY, FENCED, no build): GAP with exact residual.

Greps (before edit, this turn, this file only):
- `G2_outerN8_prop` at `:770` (def), `:776` (H3 combiner use), `:1039` (lead-chain use),
  `:1053` (G1-residual cites as open);
- `S_outerN8/:761`, `cN_outerN8/:764`, `target_outer/:767`;
- `hEq` shape at `:625,774`; banked close `digamma_shift_wOuter_8` at `:951`;
- lead banked: `stirling_wOuter_add8/:848`, `stirling_G1expr_im2/:994`;
  conditionals `G1_of_normcap/:1012`, `h3_outer_of_lead_normcap_G2/:1036`;
- tactic grep `sorry|admit|axiom|simpa`: comment-only mentions, zero tactic uses.
- banked-leaf grep (read-only): `D3SG_*` no `Complex.log`, no `1/(2*w)`;
  `D3SR_*` names complex log-Gamma/Binet remainder unbanked (`:272-281`);
  in-repo `Binet` is Fibonacci/CrossProduct only; `Complex.logGamma` absent as API.
- StirlingVert lead audit (read-only, same DAG as section 14):
  finite-interval pair `integral_inv_add_eq_log_sub` + `integral_inv_add_eq`
  (`StirlingVert.lean:68,98`) gives the per-step log identity with `eps` remainder;
  `norm_eps_le` (`:136`) bounds each `eps`; `digamma_stirling` (`:483`) is the
  tsum-closed psi disc already used for G1. Nothing banked gives the 8-fold
  telescoped `‖w‖^2`-denominator G2 directly; the step + finite-sum work below
  is the honest mirror of the G1 route at finite N.

Attempt (honest mirror of G1 route): G1 went lead (`digamma_stirling`) ->
rewrite (`half_div_eq`) -> native-`Im^2` disc (`stirling_G1expr_im2`) ->
inflation conditional (`G1_of_normcap`). Here the mirror is per-step log
identity (`g2_log_step`, from the same StirlingVert finite-interval pair) ->
telescope over 8 steps -> eps-sum + `1/(2w)`-endpoint bounds -> `G2_outerN8_prop`.
Banked here (proved, no new axioms): the per-step identity at general `w`
plus its `wOuter` eps bound and denominator floor. The 8-fold telescoping sum
identity plus the explicit `C2` assembly is NOT banked (needs the `Finset.sum`
telescope over `Complex.log` steps with `ℝ`-to-`ℕ` cast alignment plus the
`S_outerN8`/`cN_outerN8`/`target_outer` fold, over budget for this fenced turn).
Hence G2 stays Prop, H3 stays conditional via `h3_outer_of_lead_normcap_G2`.
No `sorry`/`admit`/`axiom`/`simpa`; no new imports; this section only.
-/

theorem g2_log_step (w : ℂ) (hw : 0 < w.re) (m : ℝ) (hm : 0 ≤ m) :
    Complex.log ((((m + 1 : ℝ)) : ℂ) + w) - Complex.log ((m : ℂ) + w) =
      ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 +
        Zeta23.StirlingVert.eps w m := by
  exact (Zeta23.StirlingVert.integral_inv_add_eq_log_sub (w := w) (m := m) hw hm).symm.trans
    (Zeta23.StirlingVert.integral_inv_add_eq (w := w) (m := m) hw hm)

theorem g2_eps_bound_wOuter (m : ℝ) (hm : 0 ≤ m) :
    ‖Zeta23.StirlingVert.eps wOuter m‖ ≤
      1 / (3 * ‖(m : ℂ) + wOuter‖ ^ 2 * 4.375) := by
  have ht : (1 / 2 : ℝ) ≤ |wOuter.im| := by
    rw [wOuter_im]
    norm_num
  have h := Zeta23.StirlingVert.norm_eps_le (w := wOuter) (m := m)
    wOuter_re_pos ht hm
  have him : |wOuter.im| = (4.375 : ℝ) := by
    rw [wOuter_im]
    norm_num
  rw [him] at h
  exact h

theorem g2_denom_lower_wOuter (m : ℝ) :
    (4.375 : ℝ) ≤ ‖(m : ℂ) + wOuter‖ := by
  have hle : |(((m : ℂ) + wOuter)).im| ≤ ‖(m : ℂ) + wOuter‖ :=
    Complex.abs_im_le_norm _
  have him2 : ((((m : ℂ) + wOuter)).im) = (-4.375 : ℝ) := by
    simp [wOuter_im]
  have habs : |((((m : ℂ) + wOuter)).im)| = (4.375 : ℝ) := by
    rw [him2]
    norm_num
  linarith

/-! G2 residual (exact, no force): with `g2_log_step` at `w := wOuter`,
`m := (k : ℝ)` for `k = 0..7`, telescoping gives
`log (wOuter+8) - log wOuter = S_outerN8 - (1/2) * T + E` where
`T = ∑ k ∈ range 8, ((k:ℂ)+wOuter)⁻¹^2`-shape and
`E = ∑ k ∈ range 8, eps wOuter (k:ℝ)`; then
`(cN_outerN8 - S_outerN8) - target_outer = -(1/2)*T + E - D` with
`D = 1/(2*(wOuter+8)) - 1/(2*wOuter)`. Each summand is controlled by
`g2_eps_bound_wOuter` + `g2_denom_lower_wOuter`, but the 8-fold
`Finset.sum_range_succ` telescope plus the `S/cN/target` fold to the exact
`G2_outerN8_prop C2` shape is not assembled here. Value banked: per-step
identity `g2_log_step`, eps cap `g2_eps_bound_wOuter`, floor
`g2_denom_lower_wOuter`; hEq banked (`digamma_shift_wOuter_8`); G1 conditional
chain banked (`stirling_G1expr_im2`, `G1_of_normcap`, `h3_outer_of_lead_normcap_G2`).
Gap: 8-fold telescope assembly + explicit `C2` (hand estimate `C2 ~ 10` from
`8/(2*19.14) + 8/(3*19.14*4.375) + 4/19.14` times `‖wOuter‖^2`, not claimed checked).
Hence H3 not closed here.
-/

/-! ## 18. WENDEL-TELE 8-fold telescope (PROOF-ONLY, FENCED, no build): telescope banked, G2 conditional.

Greps (before edit, this turn, this file only):
- `G2_outerN8_prop` at `:770` (def), `:776,1039` (uses);
  `S_outerN8/:761`, `cN_outerN8/:764`, `target_outer/:767`;
- `g2_log_step/:1093`, `g2_eps_bound_wOuter/:1100`, `g2_denom_lower_wOuter/:1114`;
- `digamma_shift_wOuter_8` at `:951`; `stirling_G1expr_im2/:994`, `G1_of_normcap/:1012`;
- tactic grep `sorry|admit|axiom|simpa`: prior sections comment-only mentions;
  zero tactic uses in banked code (this section keeps that).

Attempt (honest 8-step sum): specialize `g2_log_step` at `wOuter`, `m = (k : ℝ)`
(`g2_step_nat`), telescope via `Finset.sum_range_sub` (`g2_telescope8`), align
endpoints to `log (wOuter + 8) - log wOuter` (`g2_log_endpoints`) and `∑ inv`
to `S_outerN8` (`g2_S_align`), combine to `g2_log_link8`. Then fold to the exact
G2 shape (`g2_residual_eq`) and bound Q/E/D uniformly (`g2_Q_unif`, `g2_eps_unif`,
`g2_Q_sum_le`, `g2_eps_sum_le`, `g2_D_eq`, `g2_D_norm_le`), closing G2
conditionally on a norm cap (`g2_G2_of_telescope_normcap`). No numerics
discharged here; explicit caps filed below.

Banked here (proved, no new imports, this section only): `g2_step_nat`,
`g2_telescope8`, `g2_log_endpoints`, `g2_S_align`, `g2_log_link8`,
`g2_norm_wOuter_lower`, `g2_norm_wOuter8_lower`, `g2_D_eq`, `g2_D_norm_le`,
`g2_Q_unif`, `g2_eps_unif`, `g2_Q_sum_le`, `g2_eps_sum_le`, `g2_residual_eq`,
`g2_G2_of_telescope_normcap`.
-/

theorem g2_step_nat (k : ℕ) :
    Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wOuter) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wOuter) =
      (((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2 +
        Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)) := by
  have h := g2_log_step wOuter wOuter_re_pos (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hnat : ((k + 1 : ℕ) : ℝ) = (((k : ℕ) : ℝ) + 1 : ℝ) := by
    push_cast
    ring
  have hbridge : ((((k + 1 : ℕ) : ℝ)) : ℂ) = ((((((k : ℕ) : ℝ) + 1 : ℝ))) : ℂ) := by
    rw [hnat]
  rw [hbridge]
  exact h

theorem g2_telescope8 :
    ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wOuter) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wOuter)) =
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wOuter) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wOuter) := by
  have h := Finset.sum_range_sub
    (fun j : ℕ => Complex.log (((((j : ℕ) : ℝ)) : ℂ) + wOuter)) 8
  exact h

theorem g2_log_endpoints :
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wOuter) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wOuter) =
    Complex.log (wOuter + (8 : ℂ)) - Complex.log wOuter := by
  have h8 : ((((8 : ℕ) : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  have h0 : ((((0 : ℕ) : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [h8, h0, zero_add, add_comm (8 : ℂ) wOuter]

theorem g2_S_align :
    ∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ = S_outerN8 := by
  unfold S_outerN8
  apply Finset.sum_congr rfl
  intro k _
  have hcast : ((((k : ℕ) : ℝ)) : ℂ) = ((k : ℕ) : ℂ) := by
    simp
  rw [hcast, add_comm _ wOuter]

theorem g2_log_link8 :
    Complex.log (wOuter + (8 : ℂ)) - Complex.log wOuter =
    S_outerN8 -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) := by
  have hTel := g2_telescope8
  have hEnd := g2_log_endpoints
  have hStep : ∀ k ∈ Finset.range 8,
      (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wOuter) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wOuter)) =
      (((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2 +
        Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)) := by
    intro k _
    exact g2_step_nat k
  have hSum : ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wOuter) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wOuter)) =
      ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2 +
        Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) :=
    Finset.sum_congr rfl hStep
  have hSplit : ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ -
      (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2 +
      Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) =
      (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹) -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc Complex.log (wOuter + (8 : ℂ)) - Complex.log wOuter
      = Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wOuter) -
        Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wOuter) := hEnd.symm
    _ = ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wOuter) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wOuter)) := hTel.symm
    _ = ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2 +
        Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) := hSum
    _ = (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wOuter)⁻¹) -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) :=
      hSplit
    _ = S_outerN8 -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))) := by
      rw [g2_S_align]

theorem g2_norm_wOuter_lower : (4.375 : ℝ) ≤ ‖wOuter‖ := by
  have h := g2_denom_lower_wOuter 0
  have hcast : (((0 : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [hcast, zero_add] at h
  exact h

theorem g2_norm_wOuter8_lower : (4.375 : ℝ) ≤ ‖wOuter + (8 : ℂ)‖ := by
  have h := g2_denom_lower_wOuter 8
  have hcast : (((8 : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast, add_comm] at h
  exact h

theorem g2_D_eq :
    (1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter) =
      (-4 : ℂ) / (wOuter * (wOuter + (8 : ℂ))) := by
  have hw0 : wOuter ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wOuter_re, Complex.zero_re] at hR
    norm_num at hR
  have hw80 : wOuter + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wOuter_add8_re, Complex.zero_re] at hR
    norm_num at hR
  field_simp
  ring

theorem g2_D_norm_le :
    ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ ≤
      4 / (4.375 * 4.375) := by
  have hlow0 := g2_norm_wOuter_lower
  have hlow8 := g2_norm_wOuter8_lower
  have hpos0 : (0 : ℝ) < ‖wOuter‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hpos8 : (0 : ℝ) < ‖wOuter + (8 : ℂ)‖ := lt_of_lt_of_le (by norm_num) hlow8
  have hfloor : (4.375 * 4.375 : ℝ) ≤ ‖wOuter‖ * ‖wOuter + (8 : ℂ)‖ :=
    mul_le_mul hlow0 hlow8 (by norm_num) (le_of_lt hpos0)
  have h4 : ‖(-4 : ℂ)‖ = (4 : ℝ) := by
    simp
    norm_num
  rw [g2_D_eq, norm_div, norm_mul, h4]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor

theorem g2_Q_unif (k : ℕ) :
    ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖ ≤
      (1 / 2 : ℝ) / (4.375) ^ 2 := by
  have hfloor := g2_denom_lower_wOuter (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (4.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp
    norm_num
  rw [norm_div, norm_pow, hhalf]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq

theorem g2_eps_unif (k : ℕ) :
    ‖Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖ ≤
      1 / (3 * (4.375) ^ 2 * 4.375) := by
  have hbound := g2_eps_bound_wOuter (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hfloor := g2_denom_lower_wOuter (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (4.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have h3a : 3 * (4.375 : ℝ) ^ 2 ≤ 3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hfloor2 : 3 * (4.375 : ℝ) ^ 2 * 4.375 ≤
      3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ ^ 2 * 4.375 :=
    mul_le_mul_of_nonneg_right h3a (by norm_num)
  have hle : 1 / (3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wOuter‖ ^ 2 * 4.375) ≤
      1 / (3 * (4.375) ^ 2 * 4.375) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor2
  exact le_trans hbound hle

theorem g2_Q_sum_le :
    ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖ ≤
      8 * ((1 / 2 : ℝ) / (4.375) ^ 2) := by
  calc ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖
      ≤ ∑ k in Finset.range 8, ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, ((1 / 2 : ℝ) / (4.375) ^ 2) :=
        Finset.sum_le_sum (fun k _ => g2_Q_unif k)
    _ = 8 * ((1 / 2 : ℝ) / (4.375) ^ 2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_eps_sum_le :
    ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖ ≤
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) := by
  calc ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖
      ≤ ∑ k in Finset.range 8, ‖Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, (1 / (3 * (4.375) ^ 2 * 4.375)) :=
        Finset.sum_le_sum (fun k _ => g2_eps_unif k)
    _ = 8 * (1 / (3 * (4.375) ^ 2 * 4.375)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_residual_eq :
    (cN_outerN8 - S_outerN8) - target_outer =
      (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)))) -
      ((1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)) := by
  have hLink := g2_log_link8
  unfold cN_outerN8 target_outer
  calc (Complex.log (wOuter + (8 : ℂ)) - 1 / (2 * (wOuter + (8 : ℂ))) - S_outerN8) -
        (Complex.log wOuter - 1 / (2 * wOuter))
      = (Complex.log (wOuter + (8 : ℂ)) - Complex.log wOuter - S_outerN8) -
        ((1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)) := by
          ring
    _ = (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)) := by
          rw [hLink]
          ring

theorem g2_G2_of_telescope_normcap (C2 U0 : ℝ)
    (hU0 : ‖wOuter‖ ^ 2 ≤ U0)
    (hC2 : (8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375)) * U0 ≤ C2) :
    G2_outerN8_prop C2 := by
  have hRes := g2_residual_eq
  have hQ := g2_Q_sum_le
  have hE := g2_eps_sum_le
  have hD := g2_D_norm_le
  have hlow0 := g2_norm_wOuter_lower
  have hnormpos : (0 : ℝ) < ‖wOuter‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hnorm2pos : (0 : ℝ) < ‖wOuter‖ ^ 2 := pow_pos hnormpos 2
  have hA : (0 : ℝ) ≤ 8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375) := by
    norm_num
  have htri : ‖(cN_outerN8 - S_outerN8) - target_outer‖ ≤
      8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375) := by
    have hstep : ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter))‖ ≤
        ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖ +
        ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖ +
        ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ := by
      calc ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)))) -
          ((1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter))‖
          ≤ ‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2) +
            (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ)))‖ +
            ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ :=
              norm_sub_le _ _
        _ ≤ (‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2)‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖) +
            ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ :=
              add_le_add (norm_add_le _ _) le_rfl
        _ = ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wOuter) ^ 2‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wOuter (((k : ℕ) : ℝ))‖ +
            ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ := by
              rw [norm_neg]
    rw [hRes] at hstep
    exact le_trans hstep (add_le_add (add_le_add hQ hE) hD)
  have hle : 8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375) ≤
      C2 / ‖wOuter‖ ^ 2 := by
    rw [le_div_iff₀ hnorm2pos]
    calc (8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
        8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375)) * ‖wOuter‖ ^ 2
        ≤ (8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
          8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375)) * U0 :=
            mul_le_mul_of_nonneg_left hU0 hA
      _ ≤ C2 := hC2
  unfold G2_outerN8_prop
  exact le_trans htri hle

/-! G2-TELE residual (exact, no force): telescope `g2_log_link8` is banked
(`g2_step_nat` + `g2_telescope8` via `Finset.sum_range_sub` + `g2_log_endpoints`
+ `g2_S_align`); `Finset.sum` eps/Q caps banked (`g2_eps_sum_le`, `g2_Q_sum_le`
via `norm_sum_le` + `g2_eps_unif`/`g2_Q_unif` from `g2_eps_bound_wOuter` +
`g2_denom_lower_wOuter`); D-cap banked (`g2_D_eq` + `g2_D_norm_le`
`4/(4.375*4.375) ≈ 0.209`). Full `G2_outerN8_prop C2` is conditional only via
`g2_G2_of_telescope_normcap`: needs `hU0 : ‖wOuter‖^2 ≤ U0` (e.g. from
`‖w‖^2 = Re^2+Im^2 = 0.1975^2+4.375^2 ≈ 19.18`) plus
`hC2 : (Qcap+Ecap+Dcap)*U0 ≤ C2` with
`Qcap = 8*(1/2)/4.375^2 ≈ 0.209`, `Ecap = 8/(3*4.375^2*4.375) ≈ 0.0319`,
`Dcap = 4/4.375^2 ≈ 0.209` (hand arithmetic, not claimed checked; total
`≈ 0.45`, so `C2 ≈ 0.45*19.18 ≈ 8.6`, consistent with prior `~10` guess).
Hence G2 stays Prop without `U0`; H3 stays conditional via
`h3_outer_of_lead_normcap_G2`. Value banked: 8-fold link + uniform caps +
residual identity; gap: norm cap `U0` + `C2` inflation.
-/

/-! ## 19. WENDEL-D D-bound audit (PROOF-ONLY, FENCED, no build): D already banked, numeric cap banked.

Greps (before edit, this turn, this file only):
- telescope 8-fold assembly (TELE agent, section 18): `g2_step_nat/:1169`,
  `g2_telescope8/:1184`, `g2_log_endpoints/:1193`, `g2_S_align/:1203`,
  `g2_log_link8/:1212`, `g2_residual_eq/:1357`, `g2_G2_of_telescope_normcap/:1375`.
  NOT duplicated here.
- D-bound piece per G2 residual (`D = 1/(2*(w+8)) - 1/(2*w)`): `g2_D_eq/:1271`
  (`1/(2*(wOuter+8)) - 1/(2*wOuter) = (-4)/(wOuter*(wOuter+8))` via `field_simp` +
  `ring` with `wOuter ≠ 0`, `wOuter+8 ≠ 0` from `wOuter_re/:80`, `wOuter_add8_re`),
  `g2_D_norm_le/:1287` (`‖D‖ ≤ 4/(4.375*4.375)` via `norm_div`, `norm_mul`,
  `g2_norm_wOuter_lower`, `g2_norm_wOuter8_lower` from `g2_denom_lower_wOuter/:1114`).
  Both already banked; NOT re-proved here (no duplicate).
- tactic grep `sorry|admit|axiom|simpa`: prior sections comment-only mentions;
  zero tactic uses in banked code (this section keeps that).

Attempt (honest): the D-bound piece as filed needs no new derivation — the
identity + absolute cap are closed. This section banks only the NEW explicit
numeral corollary `g2_D_cap_le_021` (`4/(4.375*4.375) ≤ 0.21` by `norm_num`)
and its composition `g2_D_norm_le_021` (`‖D‖ ≤ 0.21` by `le_trans` from the
banked `g2_D_norm_le`). No `sorry`/`admit`/`axiom`/`simpa`; no new imports;
no other files touched; no existing lines modified.
-/

theorem g2_D_cap_le_021 : 4 / (4.375 * 4.375) ≤ (0.21 : ℝ) := by
  norm_num

theorem g2_D_norm_le_021 :
    ‖(1 : ℂ) / (2 * (wOuter + (8 : ℂ))) - (1 : ℂ) / (2 * wOuter)‖ ≤
      (0.21 : ℝ) :=
  le_trans g2_D_norm_le g2_D_cap_le_021

/-! D residual (exact, no force): absolute D-cap banked (`g2_D_norm_le` +
`g2_D_norm_le_021` here); `G2_outerN8_prop C2` still conditional via
`g2_G2_of_telescope_normcap/:1375` on `hU0 : ‖wOuter‖^2 ≤ U0` plus
`hC2 : (Qcap+Ecap+Dcap)*U0 ≤ C2`; H3 still conditional via
`h3_outer_of_lead_normcap_G2/:1036`. Value banked here: numeral `0.21`;
gap: norm cap `U0` + `C2` inflation (not attempted: needs `‖w‖^2 = Re^2+Im^2`
upper-cap API, outside fenced D-numeral brief).
-/

/-! ## 20. WENDEL-U0 normcap + C2 inflation (PROOF-ONLY, FENCED, no build): G2 CLOSED.

Greps (before edit, this turn, this file only):
- wOuter specs: `wOuter/:72` def `Complex.mk 0.1975 (-4.375)`,
  `wOuter_re/:80`, `wOuter_im/:82`; `wOuter_re_pos/:890`,
  `g2_denom_lower_wOuter/:1114`, `g2_norm_wOuter_lower/:1257`;
- D-cap: `g2_D_eq/:1271`, `g2_D_norm_le/:1287` (`‖D‖ ≤ 4/(4.375*4.375)`),
  numeral `g2_D_cap_le_021` + `g2_D_norm_le_021/:1473` (`≤ 0.21`);
- residual identity + conditional: `g2_residual_eq/:1357`,
  `g2_G2_of_telescope_normcap/:1375` needs `hU0 : ‖wOuter‖^2 ≤ U0` plus
  `hC2 : (Qcap+Ecap+Dcap)*U0 ≤ C2` with `Qcap = 8*((1/2)/4.375^2)`,
  `Ecap = 8*(1/(3*4.375^2*4.375))`, `Dcap = 4/(4.375*4.375)`;
- `G2_outerN8_prop/:770` def, uses `:776,1039,1379,1426`;
- tactic grep `sorry|admit|axiom|simpa`: prior sections comment-only mentions;
  zero tactic uses in banked code (this section keeps that).

Banked here (proved, no new imports, this section only):
`wOuter_norm_sq_U0` (U0 via Re^2+Im^2) + `g2_C2_inflation_863`
((Qcap+Ecap+Dcap)*U0 numeral) chain via `g2_G2_of_telescope_normcap`
to close `G2_outerN8_prop 8.63` as `G2_outerN8_banked`.
Exact values: `‖wOuter‖^2 = 0.1975^2+4.375^2 = 19.17963125 ≤ 19.18`;
`Qcap = 256/1225 ≈ 0.20898`, `Ecap = 4096/128625 ≈ 0.03184`,
`Dcap = 256/1225 ≈ 0.20898`, sum `= 57856/128625 ≈ 0.44980`,
times `19.18 = 55483904/6431250 ≈ 8.62723 ≤ 8.63` (hand arithmetic;
machine-checked shape is the `norm_num` goals below).
No `sorry`/`admit`/`axiom`/`simpa`; no new imports; no other files touched;
no existing lines modified.
-/

theorem wOuter_norm_sq_U0 : ‖wOuter‖ ^ 2 ≤ (19.18 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wOuter_re, wOuter_im]
  norm_num

theorem g2_C2_inflation_863 :
    (8 * ((1 / 2 : ℝ) / (4.375) ^ 2) +
      8 * (1 / (3 * (4.375) ^ 2 * 4.375)) + 4 / (4.375 * 4.375)) * 19.18 ≤
      (8.63 : ℝ) := by
  norm_num

theorem G2_outerN8_banked : G2_outerN8_prop 8.63 :=
  g2_G2_of_telescope_normcap 8.63 19.18 wOuter_norm_sq_U0 g2_C2_inflation_863

/-! U0+C2 residual (exact, no force): `G2_outerN8_prop 8.63` CLOSED via
`G2_outerN8_banked` (`wOuter_norm_sq_U0` + `g2_C2_inflation_863` into
`g2_G2_of_telescope_normcap/:1375` with `g2_residual_eq/:1357`,
`g2_Q_sum_le`/`g2_eps_sum_le`/`g2_D_norm_le` caps). H3 via
`h3_outer_of_lead_normcap_G2/:1036` still needs G1 normcap
(`‖wOuter+8‖^2 ≤ U`, `3*U ≤ C*(-4.375)^2`); G1-as-filed stays Prop here.
Value banked: U0 `19.18`, C2 `8.63`; gap: G1-U + C-inflation (not in brief).
-/

/-! ## 21. WENDEL-H3 G1-U normcap + C-inflation (PROOF-ONLY, FENCED, no build): H3 CLOSED.

Greps (before edit, this turn, this file only):
- H3 chain: `h3_outer_of_G1_G2/:774` combiner, `G1_of_normcap/:1012` conditional,
  `h3_outer_of_lead_normcap_G2/:1036` lead-chain, `G2_outerN8_banked/:1526` G2 closed;
- G1 shapes: `G1_outerN8_prop/:707` def, `wOuter_add8_re/:838` Re 8.1975,
  `wOuter_add8_im/:843` Im -4.375, `stirling_wOuter_add8/:848`,
  `stirling_G1expr_im2/:994`;
- U0 precedent: `wOuter_norm_sq_U0/:1516` via `Complex.sq_norm`,
  `Complex.normSq_apply`, `wOuter_re/:80`, `wOuter_im/:82`, `norm_num`,
  `g2_C2_inflation_863/:1520`, `G2_outerN8_banked/:1526`;
- forbidden-tactic grep: zero tactic uses in banked code below (prior hits comment-only).

Attempt (honest mirror of U0 route): U0 went `Re^2+Im^2` norm cap (`wOuter_norm_sq_U0`)
-> numeral inflation (`g2_C2_inflation_863`) -> `g2_G2_of_telescope_normcap`. Here the
mirror is `Re^2+Im^2` cap at `wOuter+8` (`wOuter8_norm_sq_U`) -> numeral C-inflation
(`g1_C_inflation_1354`) -> `G1_of_normcap` to close `G1_outerN8_prop 13.54` as
`G1_outerN8_banked`, then `h3_outer_of_lead_normcap_G2` with banked `G2_outerN8_banked`
to close H3 as `H3_outer_banked`. Exact values: `‖wOuter+8‖^2 = 8.1975^2+4.375^2
= 67.19900625+19.140625 = 86.33963125 ≤ 86.34`; `3*86.34 = 259.02 ≤ 13.54*19.140625
= 259.1640625` (machine-checked shapes are the `norm_num` goals below).
No new imports; no other files touched; no existing lines modified.
-/

theorem wOuter8_norm_sq_U : ‖wOuter + (8 : ℂ)‖ ^ 2 ≤ (86.34 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wOuter_add8_re, wOuter_add8_im]
  norm_num

theorem g1_C_inflation_1354 :
    3 * (86.34 : ℝ) ≤ (13.54 : ℝ) * (-4.375) ^ 2 := by
  norm_num

theorem G1_outerN8_banked : G1_outerN8_prop 13.54 :=
  G1_of_normcap 13.54 86.34 wOuter8_norm_sq_U g1_C_inflation_1354

theorem H3_outer_banked :
    ‖Complex.digamma wOuter - target_outer‖ ≤
      (13.54 : ℝ) / ‖wOuter + (8 : ℂ)‖ ^ 2 + (8.63 : ℝ) / ‖wOuter‖ ^ 2 :=
  h3_outer_of_lead_normcap_G2 13.54 86.34 8.63 wOuter8_norm_sq_U g1_C_inflation_1354
    G2_outerN8_banked

/-! H3 residual (exact, no force): `G1_outerN8_prop 13.54` CLOSED via `G1_outerN8_banked`
(`wOuter8_norm_sq_U` + `g1_C_inflation_1354` into `G1_of_normcap/:1012` with
`stirling_G1expr_im2/:994`); `G2_outerN8_prop 8.63` already CLOSED via
`G2_outerN8_banked/:1526`; H3 CLOSED via `H3_outer_banked`
(`h3_outer_of_lead_normcap_G2/:1036` with banked G1+G2). Value banked: G1-U `86.34`,
G1-C `13.54`, H3 bound `13.54/‖wOuter+8‖^2 + 8.63/‖wOuter‖^2`. Gap: none in H3 chain;
G1-as-Prop premise discharged (no residual premise retained).
-/

/-! ## 22. WENDEL-H3 feed into downstream numeric consumer (PROOF-ONLY, FENCED, no build): CLOSED.

Greps (before edit, this turn, this file only):
- `H3_outer_banked` at `:1573-1577`:
  `‖Complex.digamma wOuter - target_outer‖ ≤ 13.54/‖wOuter+8‖^2 + 8.63/‖wOuter‖^2`
  via `h3_outer_of_lead_normcap_G2/:1036` with `G1_outerN8_banked/:1570`,
  `G2_outerN8_banked/:1526`;
- `stirling_wOuter_add8` at `:848-859`: StirlingVert disc at `wOuter+8` with
  `Im^2` denominator; producer feeding G1 (`stirling_G1expr_im2/:994`,
  `G1_of_normcap/:1012`), not a consumer of H3;
- `digamma_shift_wOuter_8` at `:951-963`: shift identity
  `digamma (wOuter+8) = digamma wOuter + S_outerN8`; producer feeding the H3
  combiner `h3_outer_of_G1_G2/:773`, not a consumer of H3;
- downstream-consumer grep for the H3 shape `digamma wOuter - target_outer`
  after `:1577`: zero theorems take it as hypothesis (only the residual comment
  `:1579-1586` cites it); hence H3 is terminal in file before this section;
- forbidden-tactic grep: zero uses in banked code below (prior hits comment-only).

Attempt: neither `:848` nor `:951` consumes H3 (direction is opposite: both feed
H3). Honest feed is downstream: bank an explicit numeric consumer taking the
exact two-term H3 shape as hypothesis (`h3_numeric_of_bound`) via the banked
floors `g2_norm_wOuter_lower/:1257`, `g2_norm_wOuter8_lower/:1264`, then
discharge with `H3_outer_banked` as `H3_outer_banked_numeric`. Exact value:
`(13.54+8.63)/4.375^2 = 22.17/19.140625 ≤ 1.16` (machine-checked `norm_num`
goal below). No new imports; no existing lines modified.
-/

theorem h3_sq_lower_wOuter : (4.375 : ℝ) ^ 2 ≤ ‖wOuter‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wOuter_lower 2

theorem h3_sq_lower_wOuter8 : (4.375 : ℝ) ^ 2 ≤ ‖wOuter + (8 : ℂ)‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wOuter8_lower 2

theorem h3_div8_le : (13.54 : ℝ) / ‖wOuter + (8 : ℂ)‖ ^ 2 ≤
    (13.54 : ℝ) / (4.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_sq_lower_wOuter8

theorem h3_div0_le : (8.63 : ℝ) / ‖wOuter‖ ^ 2 ≤
    (8.63 : ℝ) / (4.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_sq_lower_wOuter

theorem h3_num_cap : (13.54 : ℝ) / (4.375 : ℝ) ^ 2 +
    (8.63 : ℝ) / (4.375 : ℝ) ^ 2 ≤ (1.16 : ℝ) := by
  norm_num

theorem h3_numeric_of_bound
    (hH3 : ‖Complex.digamma wOuter - target_outer‖ ≤
      (13.54 : ℝ) / ‖wOuter + (8 : ℂ)‖ ^ 2 + (8.63 : ℝ) / ‖wOuter‖ ^ 2) :
    ‖Complex.digamma wOuter - target_outer‖ ≤ (1.16 : ℝ) := by
  exact le_trans hH3 (le_trans (add_le_add h3_div8_le h3_div0_le) h3_num_cap)

theorem H3_outer_banked_numeric :
    ‖Complex.digamma wOuter - target_outer‖ ≤ (1.16 : ℝ) :=
  h3_numeric_of_bound H3_outer_banked

/-! Section-22 residual (exact, no force): H3 two-term shape CLOSED via
`H3_outer_banked/:1573`; downstream numeric consumer CLOSED via
`H3_outer_banked_numeric` (`h3_numeric_of_bound` with `h3_div8_le`/`h3_div0_le`
from `g2_norm_wOuter_lower/:1257`, `g2_norm_wOuter8_lower/:1264`, plus
`h3_num_cap`). Value banked: numeric H3 cap `1.16`. Gap: none in H3 chain;
no premise of `:848`/`:951` was narrowed because neither takes H3 (both feed
H3); no wider Wendel consumer in file takes the H3 shape, so the numeric cap
is the terminal consumer banked here.
-/

/-! ## 23. WENDEL-H3 leaf mirror (PROOF-ONLY, FENCED, no build): H3 CLOSED + numeric.

Greps (before edit, this turn, this file only):
- H3_outer chain: `H3_outer_banked/:1573` via `h3_outer_of_lead_normcap_G2/:1036`
  with `G1_outerN8_banked/:1570` (`G1_of_normcap/:1012` + `wOuter8_norm_sq_U`
  + `g1_C_inflation_1354` + `stirling_G1expr_im2/:994` + `half_div_eq`)
  and `G2_outerN8_banked/:1526` (`g2_G2_of_telescope_normcap/:1375` +
  `wOuter_norm_sq_U0/:1516` + `g2_C2_inflation_863` + `g2_residual_eq/:1357`
  + `g2_log_link8/:1212` + `g2_step_nat/:1169` + `g2_telescope8/:1184`
  + `g2_log_endpoints/:1193` + `g2_S_align/:1203` + caps `g2_Q_sum_le`,
  `g2_eps_sum_le`, `g2_D_norm_le/:1287`); numeric `H3_outer_banked_numeric/:1639`
  cap `1.16` via `h3_numeric_of_bound` + floors `g2_norm_wOuter_lower/:1257`,
  `g2_norm_wOuter8_lower/:1264`; shift `digamma_shift_wOuter_8/:951` via
  generic `digamma_shift_8fold` + `digamma_shift_nat`; combiner
  `h3_outer_of_G1_G2/:773`; lead `stirling_wOuter_add8/:848`.
- wLeaf specs: `wLeaf/:74` def `Complex.mk 0.1 (-3.375)`, `wLeaf_re/:84`,
  `wLeaf_im/:86`; `lower_leaf` Gamma bound at `:285` (not used here);
  no leaf H3/G1/G2/telescope defs exist before this section (zero hits for
  `S_leaf`, `cN_leaf`, `target_leaf`, `G1_leaf`, `G2_leaf`, `H3_leaf`,
  `wLeaf_add8`, `stirling_wLeaf`, `g2_leaf`, `wLeaf_shift`).
- generic reuse: `digamma_shift_nat`, `digamma_shift_8fold`,
  `shift_avoid_of_re_pos`, `g2_log_step/:1093`, `half_div_eq/:991`,
  `Zeta23.StirlingVert.digamma_stirling`, `norm_eps_le`,
  `integral_inv_add_eq_log_sub`, `integral_inv_add_eq`.

Attempt (honest mirror at leaf coords with N = 8): `wLeaf + 8 = mk 8.1 (-3.375)`
(Re 8.1 > 0, |Im| 3.375 >= 1/2). Mirror every outer step with `3.375`
in place of `4.375` and `wLeaf` in place of `wOuter`: shift-avoid + 8-fold
shift, add8 Re/Im, StirlingVert lead + G1-expression rewrite, G1 normcap
conditional + U/C banked, per-step eps + denom floor, 8-fold telescope +
residual identity + uniform Q/E/D caps + G2 conditional + U0/C2 banked,
H3 combiner + two-term close + numeric consumer. Values: `‖wLeaf‖^2 =
0.1^2+3.375^2 = 11.400625 <= 11.41`; `‖wLeaf+8‖^2 = 8.1^2+3.375^2 =
77.000625 <= 77.01`; G1 `3*77.01 = 231.03 <= 20.30*11.390625 = 231.22...`;
G2 `(Qcap+Ecap+Dcap)*11.41 <= 8.82` with `Qcap = 8*(1/2)/3.375^2`,
`Ecap = 8/(3*3.375^2*3.375)`, `Dcap = 4/(3.375*3.375)`; numeric
`(20.30+8.82)/3.375^2 <= 2.56`. No new imports; this section only.
-/

noncomputable def S_leafN8 : ℂ :=
  ∑ k ∈ Finset.range 8, (wLeaf + (k : ℂ))⁻¹

noncomputable def cN_leafN8 : ℂ :=
  Complex.log (wLeaf + (8 : ℂ)) - (1 : ℂ) / (2 * (wLeaf + (8 : ℂ)))

noncomputable def target_leaf : ℂ :=
  Complex.log wLeaf - (1 : ℂ) / (2 * wLeaf)

noncomputable def G1_leafN8_prop (C : ℝ) : Prop :=
  ‖Complex.digamma (wLeaf + (8 : ℂ)) -
    (Complex.log (wLeaf + (8 : ℂ)) - (1 : ℂ) / (2 * (wLeaf + (8 : ℂ))))‖ ≤
    C / ‖wLeaf + (8 : ℂ)‖ ^ 2

noncomputable def G2_leafN8_prop (C2 : ℝ) : Prop :=
  ‖(cN_leafN8 - S_leafN8) - target_leaf‖ ≤ C2 / ‖wLeaf‖ ^ 2

theorem wLeaf_re_pos : 0 < wLeaf.re := by
  rw [wLeaf_re]
  norm_num

theorem wLeaf_shift_avoid (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wLeaf + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) :=
  shift_avoid_of_re_pos wLeaf 8 wLeaf_re_pos k hk m

theorem digamma_shift_wLeaf_8 :
    Complex.digamma (wLeaf + (8 : ℂ)) =
      Complex.digamma wLeaf + S_leafN8 := by
  have hAvoid : ∀ (k : ℕ), k ≤ 8 → ∀ (m : ℕ),
      (wLeaf + ((k : ℕ) : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
    intro k hk m
    exact wLeaf_shift_avoid k hk m
  have h := digamma_shift_8fold wLeaf hAvoid
  have hcast8 : (((8 : ℕ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast8] at h
  unfold S_leafN8
  exact h

theorem wLeaf_add8_re : (wLeaf + (8 : ℂ)).re = 8.1 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_re, wLeaf_re, Complex.natCast_re]
  norm_num

theorem wLeaf_add8_im : (wLeaf + (8 : ℂ)).im = -3.375 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_im, wLeaf_im, Complex.natCast_im]
  norm_num

theorem stirling_wLeaf_add8 :
    ‖Complex.digamma (wLeaf + (8 : ℂ)) - Complex.log (wLeaf + (8 : ℂ)) +
      (1 / 2 : ℂ) / (wLeaf + (8 : ℂ))‖ ≤ 3 / (-3.375) ^ 2 := by
  have hre : (0 : ℝ) < (wLeaf + (8 : ℂ)).re := by
    rw [wLeaf_add8_re]
    norm_num
  have him : (1 / 2 : ℝ) ≤ |(wLeaf + (8 : ℂ)).im| := by
    rw [wLeaf_add8_im]
    norm_num
  have h := Zeta23.StirlingVert.digamma_stirling (w := wLeaf + (8 : ℂ)) hre him
  rw [wLeaf_add8_im] at h
  exact h

theorem stirling_G1expr_leaf_im2 :
    ‖Complex.digamma (wLeaf + (8 : ℂ)) -
      (Complex.log (wLeaf + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wLeaf + (8 : ℂ))))‖ ≤
      3 / (-3.375) ^ 2 := by
  have hhalf : (1 / 2 : ℂ) / (wLeaf + (8 : ℂ)) =
      (1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) :=
    half_div_eq _
  have hrewrite : Complex.digamma (wLeaf + (8 : ℂ)) -
      (Complex.log (wLeaf + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wLeaf + (8 : ℂ)))) =
      Complex.digamma (wLeaf + (8 : ℂ)) - Complex.log (wLeaf + (8 : ℂ)) +
        (1 / 2 : ℂ) / (wLeaf + (8 : ℂ)) := by
    rw [hhalf]
    ring
  rw [hrewrite]
  exact stirling_wLeaf_add8

theorem G1_leaf_of_normcap (C U : ℝ)
    (hU : ‖wLeaf + (8 : ℂ)‖ ^ 2 ≤ U)
    (hC : 3 * U ≤ C * (-3.375) ^ 2) :
    G1_leafN8_prop C := by
  have hIm2pos : (0 : ℝ) < (-3.375) ^ 2 := by
    norm_num
  have hne : wLeaf + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wLeaf_add8_re, Complex.zero_re] at hR
    norm_num at hR
  have hnormpos : (0 : ℝ) < ‖wLeaf + (8 : ℂ)‖ :=
    norm_pos_iff.mpr hne
  have hnorm2pos : (0 : ℝ) < ‖wLeaf + (8 : ℂ)‖ ^ 2 :=
    pow_pos hnormpos 2
  have hle : 3 / (-3.375) ^ 2 ≤ C / ‖wLeaf + (8 : ℂ)‖ ^ 2 := by
    rw [div_le_div_iff hIm2pos hnorm2pos]
    have h3 : 3 * ‖wLeaf + (8 : ℂ)‖ ^ 2 ≤ 3 * U :=
      mul_le_mul_of_nonneg_left hU (by norm_num)
    linarith
  have hmain := stirling_G1expr_leaf_im2
  unfold G1_leafN8_prop
  exact le_trans hmain hle

theorem wLeaf8_norm_sq_U : ‖wLeaf + (8 : ℂ)‖ ^ 2 ≤ (77.01 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wLeaf_add8_re, wLeaf_add8_im]
  norm_num

theorem g1_leaf_C_inflation_2030 :
    3 * (77.01 : ℝ) ≤ (20.30 : ℝ) * (-3.375) ^ 2 := by
  norm_num

theorem G1_leafN8_banked : G1_leafN8_prop 20.30 :=
  G1_leaf_of_normcap 20.30 77.01 wLeaf8_norm_sq_U g1_leaf_C_inflation_2030

theorem h3_leaf_of_G1_G2 (C1 C2 : ℝ)
    (hEq : Complex.digamma (wLeaf + (8 : ℂ)) =
      Complex.digamma wLeaf + S_leafN8)
    (hG1 : G1_leafN8_prop C1) (hG2 : G2_leafN8_prop C2) :
    ‖Complex.digamma wLeaf - target_leaf‖ ≤
      C1 / ‖wLeaf + (8 : ℂ)‖ ^ 2 + C2 / ‖wLeaf‖ ^ 2 := by
  have hDisc : ‖Complex.digamma (wLeaf + (8 : ℂ)) - cN_leafN8‖ ≤
      C1 / ‖wLeaf + (8 : ℂ)‖ ^ 2 := hG1
  have hLink : ‖(cN_leafN8 - S_leafN8) - target_leaf‖ ≤
      C2 / ‖wLeaf‖ ^ 2 := hG2
  have hT : ‖Complex.digamma wLeaf - (cN_leafN8 - S_leafN8)‖ ≤
      C1 / ‖wLeaf + (8 : ℂ)‖ ^ 2 := by
    have hSame : Complex.digamma wLeaf - (cN_leafN8 - S_leafN8) =
        Complex.digamma (wLeaf + (8 : ℂ)) - cN_leafN8 := by
      rw [hEq]
      ring
    rw [hSame]
    exact hDisc
  have hSplit : Complex.digamma wLeaf - target_leaf =
      (Complex.digamma wLeaf - (cN_leafN8 - S_leafN8)) +
        ((cN_leafN8 - S_leafN8) - target_leaf) := by
    ring
  calc ‖Complex.digamma wLeaf - target_leaf‖
      ≤ ‖Complex.digamma wLeaf - (cN_leafN8 - S_leafN8)‖ +
        ‖(cN_leafN8 - S_leafN8) - target_leaf‖ := by
          rw [hSplit]
          exact norm_add_le _ _
    _ ≤ C1 / ‖wLeaf + (8 : ℂ)‖ ^ 2 + C2 / ‖wLeaf‖ ^ 2 :=
          add_le_add hT hLink

theorem g2_eps_bound_wLeaf (m : ℝ) (hm : 0 ≤ m) :
    ‖Zeta23.StirlingVert.eps wLeaf m‖ ≤
      1 / (3 * ‖(m : ℂ) + wLeaf‖ ^ 2 * 3.375) := by
  have ht : (1 / 2 : ℝ) ≤ |wLeaf.im| := by
    rw [wLeaf_im]
    norm_num
  have h := Zeta23.StirlingVert.norm_eps_le (w := wLeaf) (m := m)
    wLeaf_re_pos ht hm
  have him : |wLeaf.im| = (3.375 : ℝ) := by
    rw [wLeaf_im]
    norm_num
  rw [him] at h
  exact h

theorem g2_denom_lower_wLeaf (m : ℝ) :
    (3.375 : ℝ) ≤ ‖(m : ℂ) + wLeaf‖ := by
  have hle : |(((m : ℂ) + wLeaf)).im| ≤ ‖(m : ℂ) + wLeaf‖ :=
    Complex.abs_im_le_norm _
  have him2 : ((((m : ℂ) + wLeaf)).im) = (-3.375 : ℝ) := by
    simp [wLeaf_im]
  have habs : |((((m : ℂ) + wLeaf)).im)| = (3.375 : ℝ) := by
    rw [him2]
    norm_num
  linarith

theorem g2_step_nat_leaf (k : ℕ) :
    Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wLeaf) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) =
      (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2 +
        Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)) := by
  have h := g2_log_step wLeaf wLeaf_re_pos (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hnat : ((k + 1 : ℕ) : ℝ) = (((k : ℕ) : ℝ) + 1 : ℝ) := by
    push_cast
    ring
  have hbridge : ((((k + 1 : ℕ) : ℝ)) : ℂ) = ((((((k : ℕ) : ℝ) + 1 : ℝ))) : ℂ) := by
    rw [hnat]
  rw [hbridge]
  exact h

theorem g2_telescope8_leaf :
    ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wLeaf) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)) =
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wLeaf) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wLeaf) := by
  have h := Finset.sum_range_sub
    (fun j : ℕ => Complex.log (((((j : ℕ) : ℝ)) : ℂ) + wLeaf)) 8
  exact h

theorem g2_log_endpoints_leaf :
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wLeaf) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wLeaf) =
    Complex.log (wLeaf + (8 : ℂ)) - Complex.log wLeaf := by
  have h8 : ((((8 : ℕ) : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  have h0 : ((((0 : ℕ) : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [h8, h0, zero_add, add_comm (8 : ℂ) wLeaf]

theorem g2_S_align_leaf :
    ∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ = S_leafN8 := by
  unfold S_leafN8
  apply Finset.sum_congr rfl
  intro k _
  have hcast : ((((k : ℕ) : ℝ)) : ℂ) = ((k : ℕ) : ℂ) := by
    simp
  rw [hcast, add_comm _ wLeaf]

theorem g2_log_link8_leaf :
    Complex.log (wLeaf + (8 : ℂ)) - Complex.log wLeaf =
    S_leafN8 -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) := by
  have hTel := g2_telescope8_leaf
  have hEnd := g2_log_endpoints_leaf
  have hStep : ∀ k ∈ Finset.range 8,
      (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wLeaf) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)) =
      (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2 +
        Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)) := by
    intro k _
    exact g2_step_nat_leaf k
  have hSum : ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wLeaf) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)) =
      ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2 +
        Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) :=
    Finset.sum_congr rfl hStep
  have hSplit : ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ -
      (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2 +
      Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) =
      (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹) -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc Complex.log (wLeaf + (8 : ℂ)) - Complex.log wLeaf
      = Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wLeaf) -
        Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wLeaf) := hEnd.symm
    _ = ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wLeaf) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)) := hTel.symm
    _ = ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2 +
        Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) := hSum
    _ = (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wLeaf)⁻¹) -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) :=
      hSplit
    _ = S_leafN8 -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))) := by
      rw [g2_S_align_leaf]

theorem g2_norm_wLeaf_lower : (3.375 : ℝ) ≤ ‖wLeaf‖ := by
  have h := g2_denom_lower_wLeaf 0
  have hcast : (((0 : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [hcast, zero_add] at h
  exact h

theorem g2_norm_wLeaf8_lower : (3.375 : ℝ) ≤ ‖wLeaf + (8 : ℂ)‖ := by
  have h := g2_denom_lower_wLeaf 8
  have hcast : (((8 : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast, add_comm] at h
  exact h

theorem g2_D_eq_leaf :
    (1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf) =
      (-4 : ℂ) / (wLeaf * (wLeaf + (8 : ℂ))) := by
  have hw0 : wLeaf ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wLeaf_re, Complex.zero_re] at hR
    norm_num at hR
  have hw80 : wLeaf + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wLeaf_add8_re, Complex.zero_re] at hR
    norm_num at hR
  field_simp
  ring

theorem g2_D_norm_le_leaf :
    ‖(1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)‖ ≤
      4 / (3.375 * 3.375) := by
  have hlow0 := g2_norm_wLeaf_lower
  have hlow8 := g2_norm_wLeaf8_lower
  have hpos0 : (0 : ℝ) < ‖wLeaf‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hpos8 : (0 : ℝ) < ‖wLeaf + (8 : ℂ)‖ := lt_of_lt_of_le (by norm_num) hlow8
  have hfloor : (3.375 * 3.375 : ℝ) ≤ ‖wLeaf‖ * ‖wLeaf + (8 : ℂ)‖ :=
    mul_le_mul hlow0 hlow8 (by norm_num) (le_of_lt hpos0)
  have h4 : ‖(-4 : ℂ)‖ = (4 : ℝ) := by
    simp
    norm_num
  rw [g2_D_eq_leaf, norm_div, norm_mul, h4]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor

theorem g2_Q_unif_leaf (k : ℕ) :
    ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖ ≤
      (1 / 2 : ℝ) / (3.375) ^ 2 := by
  have hfloor := g2_denom_lower_wLeaf (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (3.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp
    norm_num
  rw [norm_div, norm_pow, hhalf]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq

theorem g2_eps_unif_leaf (k : ℕ) :
    ‖Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖ ≤
      1 / (3 * (3.375) ^ 2 * 3.375) := by
  have hbound := g2_eps_bound_wLeaf (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hfloor := g2_denom_lower_wLeaf (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (3.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have h3a : 3 * (3.375 : ℝ) ^ 2 ≤ 3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hfloor2 : 3 * (3.375 : ℝ) ^ 2 * 3.375 ≤
      3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ ^ 2 * 3.375 :=
    mul_le_mul_of_nonneg_right h3a (by norm_num)
  have hle : 1 / (3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wLeaf‖ ^ 2 * 3.375) ≤
      1 / (3 * (3.375) ^ 2 * 3.375) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor2
  exact le_trans hbound hle

theorem g2_Q_sum_le_leaf :
    ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖ ≤
      8 * ((1 / 2 : ℝ) / (3.375) ^ 2) := by
  calc ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖
      ≤ ∑ k in Finset.range 8, ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, ((1 / 2 : ℝ) / (3.375) ^ 2) :=
        Finset.sum_le_sum (fun k _ => g2_Q_unif_leaf k)
    _ = 8 * ((1 / 2 : ℝ) / (3.375) ^ 2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_eps_sum_le_leaf :
    ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖ ≤
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) := by
  calc ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖
      ≤ ∑ k in Finset.range 8, ‖Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, (1 / (3 * (3.375) ^ 2 * 3.375)) :=
        Finset.sum_le_sum (fun k _ => g2_eps_unif_leaf k)
    _ = 8 * (1 / (3 * (3.375) ^ 2 * 3.375)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_residual_eq_leaf :
    (cN_leafN8 - S_leafN8) - target_leaf =
      (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)))) -
      ((1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)) := by
  have hLink := g2_log_link8_leaf
  unfold cN_leafN8 target_leaf
  calc (Complex.log (wLeaf + (8 : ℂ)) - 1 / (2 * (wLeaf + (8 : ℂ))) - S_leafN8) -
        (Complex.log wLeaf - 1 / (2 * wLeaf))
      = (Complex.log (wLeaf + (8 : ℂ)) - Complex.log wLeaf - S_leafN8) -
        ((1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)) := by
          ring
    _ = (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)) := by
          rw [hLink]
          ring

theorem g2_G2_of_telescope_normcap_leaf (C2 U0 : ℝ)
    (hU0 : ‖wLeaf‖ ^ 2 ≤ U0)
    (hC2 : (8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375)) * U0 ≤ C2) :
    G2_leafN8_prop C2 := by
  have hRes := g2_residual_eq_leaf
  have hQ := g2_Q_sum_le_leaf
  have hE := g2_eps_sum_le_leaf
  have hD := g2_D_norm_le_leaf
  have hlow0 := g2_norm_wLeaf_lower
  have hnormpos : (0 : ℝ) < ‖wLeaf‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hnorm2pos : (0 : ℝ) < ‖wLeaf‖ ^ 2 := pow_pos hnormpos 2
  have hA : (0 : ℝ) ≤ 8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375) := by
    norm_num
  have htri : ‖(cN_leafN8 - S_leafN8) - target_leaf‖ ≤
      8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375) := by
    have hstep : ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf))‖ ≤
        ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖ +
        ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖ +
        ‖(1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)‖ := by
      calc ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)))) -
          ((1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf))‖
          ≤ ‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2) +
            (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ)))‖ +
            ‖(1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)‖ :=
              norm_sub_le _ _
        _ ≤ (‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2)‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖) +
            ‖(1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)‖ :=
              add_le_add (norm_add_le _ _) le_rfl
        _ = ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wLeaf) ^ 2‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wLeaf (((k : ℕ) : ℝ))‖ +
            ‖(1 : ℂ) / (2 * (wLeaf + (8 : ℂ))) - (1 : ℂ) / (2 * wLeaf)‖ := by
              rw [norm_neg]
    rw [hRes] at hstep
    exact le_trans hstep (add_le_add (add_le_add hQ hE) hD)
  have hle : 8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375) ≤
      C2 / ‖wLeaf‖ ^ 2 := by
    rw [le_div_iff₀ hnorm2pos]
    calc (8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
        8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375)) * ‖wLeaf‖ ^ 2
        ≤ (8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
          8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375)) * U0 :=
            mul_le_mul_of_nonneg_left hU0 hA
      _ ≤ C2 := hC2
  unfold G2_leafN8_prop
  exact le_trans htri hle

theorem wLeaf_norm_sq_U0 : ‖wLeaf‖ ^ 2 ≤ (11.41 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wLeaf_re, wLeaf_im]
  norm_num

theorem g2_leaf_C2_inflation_882 :
    (8 * ((1 / 2 : ℝ) / (3.375) ^ 2) +
      8 * (1 / (3 * (3.375) ^ 2 * 3.375)) + 4 / (3.375 * 3.375)) * 11.41 ≤
      (8.82 : ℝ) := by
  norm_num

theorem G2_leafN8_banked : G2_leafN8_prop 8.82 :=
  g2_G2_of_telescope_normcap_leaf 8.82 11.41 wLeaf_norm_sq_U0
    g2_leaf_C2_inflation_882

theorem H3_leaf_banked :
    ‖Complex.digamma wLeaf - target_leaf‖ ≤
      (20.30 : ℝ) / ‖wLeaf + (8 : ℂ)‖ ^ 2 + (8.82 : ℝ) / ‖wLeaf‖ ^ 2 :=
  h3_leaf_of_G1_G2 20.30 8.82 digamma_shift_wLeaf_8 G1_leafN8_banked
    G2_leafN8_banked

theorem h3_leaf_sq_lower : (3.375 : ℝ) ^ 2 ≤ ‖wLeaf‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wLeaf_lower 2

theorem h3_leaf_sq_lower8 : (3.375 : ℝ) ^ 2 ≤ ‖wLeaf + (8 : ℂ)‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wLeaf8_lower 2

theorem h3_leaf_div8_le : (20.30 : ℝ) / ‖wLeaf + (8 : ℂ)‖ ^ 2 ≤
    (20.30 : ℝ) / (3.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_leaf_sq_lower8

theorem h3_leaf_div0_le : (8.82 : ℝ) / ‖wLeaf‖ ^ 2 ≤
    (8.82 : ℝ) / (3.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_leaf_sq_lower

theorem h3_leaf_num_cap : (20.30 : ℝ) / (3.375 : ℝ) ^ 2 +
    (8.82 : ℝ) / (3.375 : ℝ) ^ 2 ≤ (2.56 : ℝ) := by
  norm_num

theorem H3_leaf_banked_numeric :
    ‖Complex.digamma wLeaf - target_leaf‖ ≤ (2.56 : ℝ) := by
  have hH3 := H3_leaf_banked
  have hcap := add_le_add h3_leaf_div8_le h3_leaf_div0_le
  exact le_trans hH3 (le_trans hcap h3_leaf_num_cap)

/-! Section-23 residual: H3 leaf mirror CLOSED via `H3_leaf_banked` (G1
`G1_leafN8_banked` with U `77.01` + C `20.30`; G2 `G2_leafN8_banked` with U0
`11.41` + C2 `8.82`; shift `digamma_shift_wLeaf_8`) plus numeric `2.56` via
`H3_leaf_banked_numeric`. Mid/inner centers open (no mirror attempted here).
-/

end Door3ComplexWendel

/-! ## 24. WENDEL-H3MID mid mirror (PROOF-ONLY, FENCED, no build): H3 CLOSED + numeric.

Greps (before edit, this turn, this file only):
- H3_outer chain: `H3_outer_banked` with `G1_outerN8_banked` + `G2_outerN8_banked`
  via `h3_outer_of_G1_G2`; shift `digamma_shift_wOuter_8`; lead `stirling_wOuter_add8`.
- H3_leaf chain (section 23, not duplicated): `H3_leaf_banked` via
  `h3_leaf_of_G1_G2` with `G1_leafN8_banked` (U `77.01`, C `20.30`) and
  `G2_leafN8_banked` (U0 `11.41`, C2 `8.82`); shift `digamma_shift_wLeaf_8`;
  lead `stirling_wLeaf_add8`; telescope `g2_telescope8_leaf` + `g2_log_link8_leaf`
  + `g2_residual_eq_leaf`; numeric `H3_leaf_banked_numeric` cap `2.56`.
- wMid specs: `wMid` def `Complex.mk 0.1975 (-2.375)`, `wMid_re`, `wMid_im`;
  zero hits for `S_mid`, `cN_mid`, `target_mid`, `G1_mid`, `G2_mid`, `H3_mid`,
  `wMid_add8`, `stirling_wMid`, `g2_mid`, `wMid_shift` before this section.
- generic reuse (proved earlier, reused here): `digamma_shift_nat`,
  `digamma_shift_8fold`, `shift_avoid_of_re_pos`, `g2_log_step`, `half_div_eq`,
  `Zeta23.StirlingVert.digamma_stirling`, `Zeta23.StirlingVert.norm_eps_le`.

Mirror at mid coords with N = 8: `wMid + 8 = mk 8.1975 (-2.375)`
(Re 8.1975 > 0, |Im| 2.375 >= 1/2). Every outer/leaf step with `2.375`
in place of `4.375`/`3.375` and `wMid` in place of `wOuter`/`wLeaf`.
Values: `‖wMid‖^2 = 0.1975^2+2.375^2 = 5.67963125 <= 5.68`;
`‖wMid+8‖^2 = 8.1975^2+2.375^2 = 72.83963125 <= 72.84`;
G1 `3*72.84 = 218.52 <= 38.75*5.640625 = 218.57421875`;
G2 `(Qcap+Ecap+Dcap)*5.68 <= 9.20` with `Qcap = 8*(1/2)/2.375^2`,
`Ecap = 8/(3*2.375^2*2.375)`, `Dcap = 4/(2.375*2.375)`; numeric
`(38.75+9.20)/2.375^2 <= 8.51`. This section only; no other file touched.
-/

namespace Door3ComplexWendel

noncomputable def S_midN8 : ℂ :=
  ∑ k ∈ Finset.range 8, (wMid + (k : ℂ))⁻¹

noncomputable def cN_midN8 : ℂ :=
  Complex.log (wMid + (8 : ℂ)) - (1 : ℂ) / (2 * (wMid + (8 : ℂ)))

noncomputable def target_mid : ℂ :=
  Complex.log wMid - (1 : ℂ) / (2 * wMid)

noncomputable def G1_midN8_prop (C : ℝ) : Prop :=
  ‖Complex.digamma (wMid + (8 : ℂ)) -
    (Complex.log (wMid + (8 : ℂ)) - (1 : ℂ) / (2 * (wMid + (8 : ℂ))))‖ ≤
    C / ‖wMid + (8 : ℂ)‖ ^ 2

noncomputable def G2_midN8_prop (C2 : ℝ) : Prop :=
  ‖(cN_midN8 - S_midN8) - target_mid‖ ≤ C2 / ‖wMid‖ ^ 2

theorem wMid_re_pos : 0 < wMid.re := by
  rw [wMid_re]
  norm_num

theorem wMid_shift_avoid (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wMid + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) :=
  shift_avoid_of_re_pos wMid 8 wMid_re_pos k hk m

theorem digamma_shift_wMid_8 :
    Complex.digamma (wMid + (8 : ℂ)) =
      Complex.digamma wMid + S_midN8 := by
  have hAvoid : ∀ (k : ℕ), k ≤ 8 → ∀ (m : ℕ),
      (wMid + ((k : ℕ) : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
    intro k hk m
    exact wMid_shift_avoid k hk m
  have h := digamma_shift_8fold wMid hAvoid
  have hcast8 : (((8 : ℕ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast8] at h
  unfold S_midN8
  exact h

theorem wMid_add8_re : (wMid + (8 : ℂ)).re = 8.1975 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_re, wMid_re, Complex.natCast_re]
  norm_num

theorem wMid_add8_im : (wMid + (8 : ℂ)).im = -2.375 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_im, wMid_im, Complex.natCast_im]
  norm_num

theorem stirling_wMid_add8 :
    ‖Complex.digamma (wMid + (8 : ℂ)) - Complex.log (wMid + (8 : ℂ)) +
      (1 / 2 : ℂ) / (wMid + (8 : ℂ))‖ ≤ 3 / (-2.375) ^ 2 := by
  have hre : (0 : ℝ) < (wMid + (8 : ℂ)).re := by
    rw [wMid_add8_re]
    norm_num
  have him : (1 / 2 : ℝ) ≤ |(wMid + (8 : ℂ)).im| := by
    rw [wMid_add8_im]
    norm_num
  have h := Zeta23.StirlingVert.digamma_stirling (w := wMid + (8 : ℂ)) hre him
  rw [wMid_add8_im] at h
  exact h

theorem stirling_G1expr_mid_im2 :
    ‖Complex.digamma (wMid + (8 : ℂ)) -
      (Complex.log (wMid + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wMid + (8 : ℂ))))‖ ≤
      3 / (-2.375) ^ 2 := by
  have hhalf : (1 / 2 : ℂ) / (wMid + (8 : ℂ)) =
      (1 : ℂ) / (2 * (wMid + (8 : ℂ))) :=
    half_div_eq _
  have hrewrite : Complex.digamma (wMid + (8 : ℂ)) -
      (Complex.log (wMid + (8 : ℂ)) -
        (1 : ℂ) / (2 * (wMid + (8 : ℂ)))) =
      Complex.digamma (wMid + (8 : ℂ)) - Complex.log (wMid + (8 : ℂ)) +
        (1 / 2 : ℂ) / (wMid + (8 : ℂ)) := by
    rw [hhalf]
    ring
  rw [hrewrite]
  exact stirling_wMid_add8

theorem G1_mid_of_normcap (C U : ℝ)
    (hU : ‖wMid + (8 : ℂ)‖ ^ 2 ≤ U)
    (hC : 3 * U ≤ C * (-2.375) ^ 2) :
    G1_midN8_prop C := by
  have hIm2pos : (0 : ℝ) < (-2.375) ^ 2 := by
    norm_num
  have hne : wMid + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wMid_add8_re, Complex.zero_re] at hR
    norm_num at hR
  have hnormpos : (0 : ℝ) < ‖wMid + (8 : ℂ)‖ :=
    norm_pos_iff.mpr hne
  have hnorm2pos : (0 : ℝ) < ‖wMid + (8 : ℂ)‖ ^ 2 :=
    pow_pos hnormpos 2
  have hle : 3 / (-2.375) ^ 2 ≤ C / ‖wMid + (8 : ℂ)‖ ^ 2 := by
    rw [div_le_div_iff hIm2pos hnorm2pos]
    have h3 : 3 * ‖wMid + (8 : ℂ)‖ ^ 2 ≤ 3 * U :=
      mul_le_mul_of_nonneg_left hU (by norm_num)
    linarith
  have hmain := stirling_G1expr_mid_im2
  unfold G1_midN8_prop
  exact le_trans hmain hle

theorem wMid8_norm_sq_U : ‖wMid + (8 : ℂ)‖ ^ 2 ≤ (72.84 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wMid_add8_re, wMid_add8_im]
  norm_num

theorem g1_mid_C_inflation_3875 :
    3 * (72.84 : ℝ) ≤ (38.75 : ℝ) * (-2.375) ^ 2 := by
  norm_num

theorem G1_midN8_banked : G1_midN8_prop 38.75 :=
  G1_mid_of_normcap 38.75 72.84 wMid8_norm_sq_U g1_mid_C_inflation_3875

theorem h3_mid_of_G1_G2 (C1 C2 : ℝ)
    (hEq : Complex.digamma (wMid + (8 : ℂ)) =
      Complex.digamma wMid + S_midN8)
    (hG1 : G1_midN8_prop C1) (hG2 : G2_midN8_prop C2) :
    ‖Complex.digamma wMid - target_mid‖ ≤
      C1 / ‖wMid + (8 : ℂ)‖ ^ 2 + C2 / ‖wMid‖ ^ 2 := by
  have hDisc : ‖Complex.digamma (wMid + (8 : ℂ)) - cN_midN8‖ ≤
      C1 / ‖wMid + (8 : ℂ)‖ ^ 2 := hG1
  have hLink : ‖(cN_midN8 - S_midN8) - target_mid‖ ≤
      C2 / ‖wMid‖ ^ 2 := hG2
  have hT : ‖Complex.digamma wMid - (cN_midN8 - S_midN8)‖ ≤
      C1 / ‖wMid + (8 : ℂ)‖ ^ 2 := by
    have hSame : Complex.digamma wMid - (cN_midN8 - S_midN8) =
        Complex.digamma (wMid + (8 : ℂ)) - cN_midN8 := by
      rw [hEq]
      ring
    rw [hSame]
    exact hDisc
  have hSplit : Complex.digamma wMid - target_mid =
      (Complex.digamma wMid - (cN_midN8 - S_midN8)) +
        ((cN_midN8 - S_midN8) - target_mid) := by
    ring
  calc ‖Complex.digamma wMid - target_mid‖
      ≤ ‖Complex.digamma wMid - (cN_midN8 - S_midN8)‖ +
        ‖(cN_midN8 - S_midN8) - target_mid‖ := by
          rw [hSplit]
          exact norm_add_le _ _
    _ ≤ C1 / ‖wMid + (8 : ℂ)‖ ^ 2 + C2 / ‖wMid‖ ^ 2 :=
          add_le_add hT hLink

theorem g2_eps_bound_wMid (m : ℝ) (hm : 0 ≤ m) :
    ‖Zeta23.StirlingVert.eps wMid m‖ ≤
      1 / (3 * ‖(m : ℂ) + wMid‖ ^ 2 * 2.375) := by
  have ht : (1 / 2 : ℝ) ≤ |wMid.im| := by
    rw [wMid_im]
    norm_num
  have h := Zeta23.StirlingVert.norm_eps_le (w := wMid) (m := m)
    wMid_re_pos ht hm
  have him : |wMid.im| = (2.375 : ℝ) := by
    rw [wMid_im]
    norm_num
  rw [him] at h
  exact h

theorem g2_denom_lower_wMid (m : ℝ) :
    (2.375 : ℝ) ≤ ‖(m : ℂ) + wMid‖ := by
  have hle : |(((m : ℂ) + wMid)).im| ≤ ‖(m : ℂ) + wMid‖ :=
    Complex.abs_im_le_norm _
  have him2 : ((((m : ℂ) + wMid)).im) = (-2.375 : ℝ) := by
    simp [wMid_im]
  have habs : |((((m : ℂ) + wMid)).im)| = (2.375 : ℝ) := by
    rw [him2]
    norm_num
  linarith

theorem g2_step_nat_mid (k : ℕ) :
    Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wMid) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wMid) =
      (((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2 +
        Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)) := by
  have h := g2_log_step wMid wMid_re_pos (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hnat : ((k + 1 : ℕ) : ℝ) = (((k : ℕ) : ℝ) + 1 : ℝ) := by
    push_cast
    ring
  have hbridge : ((((k + 1 : ℕ) : ℝ)) : ℂ) = ((((((k : ℕ) : ℝ) + 1 : ℝ))) : ℂ) := by
    rw [hnat]
  rw [hbridge]
  exact h

theorem g2_telescope8_mid :
    ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wMid) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wMid)) =
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wMid) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wMid) := by
  have h := Finset.sum_range_sub
    (fun j : ℕ => Complex.log (((((j : ℕ) : ℝ)) : ℂ) + wMid)) 8
  exact h

theorem g2_log_endpoints_mid :
    Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wMid) -
      Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wMid) =
    Complex.log (wMid + (8 : ℂ)) - Complex.log wMid := by
  have h8 : ((((8 : ℕ) : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  have h0 : ((((0 : ℕ) : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [h8, h0, zero_add, add_comm (8 : ℂ) wMid]

theorem g2_S_align_mid :
    ∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ = S_midN8 := by
  unfold S_midN8
  apply Finset.sum_congr rfl
  intro k _
  have hcast : ((((k : ℕ) : ℝ)) : ℂ) = ((k : ℕ) : ℂ) := by
    simp
  rw [hcast, add_comm _ wMid]

theorem g2_log_link8_mid :
    Complex.log (wMid + (8 : ℂ)) - Complex.log wMid =
    S_midN8 -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) := by
  have hTel := g2_telescope8_mid
  have hEnd := g2_log_endpoints_mid
  have hStep : ∀ k ∈ Finset.range 8,
      (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wMid) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wMid)) =
      (((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2 +
        Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)) := by
    intro k _
    exact g2_step_nat_mid k
  have hSum : ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wMid) -
      Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wMid)) =
      ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2 +
        Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) :=
    Finset.sum_congr rfl hStep
  have hSplit : ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ -
      (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2 +
      Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) =
      (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹) -
      (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
      (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc Complex.log (wMid + (8 : ℂ)) - Complex.log wMid
      = Complex.log (((((8 : ℕ) : ℝ)) : ℂ) + wMid) -
        Complex.log (((((0 : ℕ) : ℝ)) : ℂ) + wMid) := hEnd.symm
    _ = ∑ k in Finset.range 8, (Complex.log (((((k + 1 : ℕ) : ℝ)) : ℂ) + wMid) -
        Complex.log (((((k : ℕ) : ℝ)) : ℂ) + wMid)) := hTel.symm
    _ = ∑ k in Finset.range 8, ((((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹ -
        (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2 +
        Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) := hSum
    _ = (∑ k in Finset.range 8, (((((k : ℕ) : ℝ)) : ℂ) + wMid)⁻¹) -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) :=
      hSplit
    _ = S_midN8 -
        (∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))) := by
      rw [g2_S_align_mid]

theorem g2_norm_wMid_lower : (2.375 : ℝ) ≤ ‖wMid‖ := by
  have h := g2_denom_lower_wMid 0
  have hcast : (((0 : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [hcast, zero_add] at h
  exact h

theorem g2_norm_wMid8_lower : (2.375 : ℝ) ≤ ‖wMid + (8 : ℂ)‖ := by
  have h := g2_denom_lower_wMid 8
  have hcast : (((8 : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast, add_comm] at h
  exact h

theorem g2_D_eq_mid :
    (1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid) =
      (-4 : ℂ) / (wMid * (wMid + (8 : ℂ))) := by
  have hw0 : wMid ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wMid_re, Complex.zero_re] at hR
    norm_num at hR
  have hw80 : wMid + (8 : ℂ) ≠ 0 := by
    intro hCon
    have hR := congrArg Complex.re hCon
    rw [wMid_add8_re, Complex.zero_re] at hR
    norm_num at hR
  field_simp
  ring

theorem g2_D_norm_le_mid :
    ‖(1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)‖ ≤
      4 / (2.375 * 2.375) := by
  have hlow0 := g2_norm_wMid_lower
  have hlow8 := g2_norm_wMid8_lower
  have hpos0 : (0 : ℝ) < ‖wMid‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hpos8 : (0 : ℝ) < ‖wMid + (8 : ℂ)‖ := lt_of_lt_of_le (by norm_num) hlow8
  have hfloor : (2.375 * 2.375 : ℝ) ≤ ‖wMid‖ * ‖wMid + (8 : ℂ)‖ :=
    mul_le_mul hlow0 hlow8 (by norm_num) (le_of_lt hpos0)
  have h4 : ‖(-4 : ℂ)‖ = (4 : ℝ) := by
    simp
    norm_num
  rw [g2_D_eq_mid, norm_div, norm_mul, h4]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor

theorem g2_Q_unif_mid (k : ℕ) :
    ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖ ≤
      (1 / 2 : ℝ) / (2.375) ^ 2 := by
  have hfloor := g2_denom_lower_wMid (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (2.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp
    norm_num
  rw [norm_div, norm_pow, hhalf]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq

theorem g2_eps_unif_mid (k : ℕ) :
    ‖Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖ ≤
      1 / (3 * (2.375) ^ 2 * 2.375) := by
  have hbound := g2_eps_bound_wMid (((k : ℕ) : ℝ)) (Nat.cast_nonneg k)
  have hfloor := g2_denom_lower_wMid (((k : ℕ) : ℝ))
  have hnormpos : (0 : ℝ) < ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ :=
    lt_of_lt_of_le (by norm_num) hfloor
  have hsq : (2.375 : ℝ) ^ 2 ≤ ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ ^ 2 :=
    pow_le_pow_left (by norm_num) hfloor 2
  have h3a : 3 * (2.375 : ℝ) ^ 2 ≤ 3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hfloor2 : 3 * (2.375 : ℝ) ^ 2 * 2.375 ≤
      3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ ^ 2 * 2.375 :=
    mul_le_mul_of_nonneg_right h3a (by norm_num)
  have hle : 1 / (3 * ‖((((k : ℕ) : ℝ)) : ℂ) + wMid‖ ^ 2 * 2.375) ≤
      1 / (3 * (2.375) ^ 2 * 2.375) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfloor2
  exact le_trans hbound hle

theorem g2_Q_sum_le_mid :
    ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖ ≤
      8 * ((1 / 2 : ℝ) / (2.375) ^ 2) := by
  calc ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖
      ≤ ∑ k in Finset.range 8, ‖(1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, ((1 / 2 : ℝ) / (2.375) ^ 2) :=
        Finset.sum_le_sum (fun k _ => g2_Q_unif_mid k)
    _ = 8 * ((1 / 2 : ℝ) / (2.375) ^ 2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_eps_sum_le_mid :
    ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖ ≤
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) := by
  calc ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖
      ≤ ∑ k in Finset.range 8, ‖Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range 8, (1 / (3 * (2.375) ^ 2 * 2.375)) :=
        Finset.sum_le_sum (fun k _ => g2_eps_unif_mid k)
    _ = 8 * (1 / (3 * (2.375) ^ 2 * 2.375)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem g2_residual_eq_mid :
    (cN_midN8 - S_midN8) - target_mid =
      (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)))) -
      ((1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)) := by
  have hLink := g2_log_link8_mid
  unfold cN_midN8 target_mid
  calc (Complex.log (wMid + (8 : ℂ)) - 1 / (2 * (wMid + (8 : ℂ))) - S_midN8) -
        (Complex.log wMid - 1 / (2 * wMid))
      = (Complex.log (wMid + (8 : ℂ)) - Complex.log wMid - S_midN8) -
        ((1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)) := by
          ring
    _ = (-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)) := by
          rw [hLink]
          ring

theorem g2_G2_of_telescope_normcap_mid (C2 U0 : ℝ)
    (hU0 : ‖wMid‖ ^ 2 ≤ U0)
    (hC2 : (8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375)) * U0 ≤ C2) :
    G2_midN8_prop C2 := by
  have hRes := g2_residual_eq_mid
  have hQ := g2_Q_sum_le_mid
  have hE := g2_eps_sum_le_mid
  have hD := g2_D_norm_le_mid
  have hlow0 := g2_norm_wMid_lower
  have hnormpos : (0 : ℝ) < ‖wMid‖ := lt_of_lt_of_le (by norm_num) hlow0
  have hnorm2pos : (0 : ℝ) < ‖wMid‖ ^ 2 := pow_pos hnormpos 2
  have hA : (0 : ℝ) ≤ 8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375) := by
    norm_num
  have htri : ‖(cN_midN8 - S_midN8) - target_mid‖ ≤
      8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375) := by
    have hstep : ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
        (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)))) -
        ((1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid))‖ ≤
        ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖ +
        ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖ +
        ‖(1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)‖ := by
      calc ‖(-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
          (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)))) -
          ((1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid))‖
          ≤ ‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2) +
            (∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ)))‖ +
            ‖(1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)‖ :=
              norm_sub_le _ _
        _ ≤ (‖-(∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2)‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖) +
            ‖(1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)‖ :=
              add_le_add (norm_add_le _ _) le_rfl
        _ = ‖∑ k in Finset.range 8, (1 / 2 : ℂ) / (((((k : ℕ) : ℝ)) : ℂ) + wMid) ^ 2‖ +
            ‖∑ k in Finset.range 8, Zeta23.StirlingVert.eps wMid (((k : ℕ) : ℝ))‖ +
            ‖(1 : ℂ) / (2 * (wMid + (8 : ℂ))) - (1 : ℂ) / (2 * wMid)‖ := by
              rw [norm_neg]
    rw [hRes] at hstep
    exact le_trans hstep (add_le_add (add_le_add hQ hE) hD)
  have hle : 8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375) ≤
      C2 / ‖wMid‖ ^ 2 := by
    rw [le_div_iff₀ hnorm2pos]
    calc (8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
        8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375)) * ‖wMid‖ ^ 2
        ≤ (8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
          8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375)) * U0 :=
            mul_le_mul_of_nonneg_left hU0 hA
      _ ≤ C2 := hC2
  unfold G2_midN8_prop
  exact le_trans htri hle

theorem wMid_norm_sq_U0 : ‖wMid‖ ^ 2 ≤ (5.68 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wMid_re, wMid_im]
  norm_num

theorem g2_mid_C2_inflation_920 :
    (8 * ((1 / 2 : ℝ) / (2.375) ^ 2) +
      8 * (1 / (3 * (2.375) ^ 2 * 2.375)) + 4 / (2.375 * 2.375)) * 5.68 ≤
      (9.20 : ℝ) := by
  norm_num

theorem G2_midN8_banked : G2_midN8_prop 9.20 :=
  g2_G2_of_telescope_normcap_mid 9.20 5.68 wMid_norm_sq_U0
    g2_mid_C2_inflation_920

theorem H3_mid_banked :
    ‖Complex.digamma wMid - target_mid‖ ≤
      (38.75 : ℝ) / ‖wMid + (8 : ℂ)‖ ^ 2 + (9.20 : ℝ) / ‖wMid‖ ^ 2 :=
  h3_mid_of_G1_G2 38.75 9.20 digamma_shift_wMid_8 G1_midN8_banked
    G2_midN8_banked

theorem h3_mid_sq_lower : (2.375 : ℝ) ^ 2 ≤ ‖wMid‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wMid_lower 2

theorem h3_mid_sq_lower8 : (2.375 : ℝ) ^ 2 ≤ ‖wMid + (8 : ℂ)‖ ^ 2 :=
  pow_le_pow_left (by norm_num) g2_norm_wMid8_lower 2

theorem h3_mid_div8_le : (38.75 : ℝ) / ‖wMid + (8 : ℂ)‖ ^ 2 ≤
    (38.75 : ℝ) / (2.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_mid_sq_lower8

theorem h3_mid_div0_le : (9.20 : ℝ) / ‖wMid‖ ^ 2 ≤
    (9.20 : ℝ) / (2.375 : ℝ) ^ 2 :=
  div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3_mid_sq_lower

theorem h3_mid_num_cap : (38.75 : ℝ) / (2.375 : ℝ) ^ 2 +
    (9.20 : ℝ) / (2.375 : ℝ) ^ 2 ≤ (8.51 : ℝ) := by
  norm_num

theorem H3_mid_banked_numeric :
    ‖Complex.digamma wMid - target_mid‖ ≤ (8.51 : ℝ) := by
  have hH3 := H3_mid_banked
  have hcap := add_le_add h3_mid_div8_le h3_mid_div0_le
  exact le_trans hH3 (le_trans hcap h3_mid_num_cap)

/-! Section-24 residual: H3 mid mirror CLOSED via `H3_mid_banked` (G1
`G1_midN8_banked` with U `72.84` + C `38.75`; G2 `G2_midN8_banked` with U0
`5.68` + C2 `9.20`; shift `digamma_shift_wMid_8`) plus numeric `8.51` via
`H3_mid_banked_numeric`. Inner center open (no mirror attempted here).
-/

end Door3ComplexWendel

/-! ## 25. WENDEL-H3INNER inner mirror (PROOF-ONLY, FENCED, no build): GAP with exact residual.

Greps (before edit, this turn, this file only):
- H3MID shapes: `S_midN8/:2204`, `cN_midN8/:2207`, `target_mid/:2210`,
  `G1_midN8_prop/:2213`, `G2_midN8_prop/:2218`, `G1_mid_of_normcap/:2284`,
  `wMid8_norm_sq_U/:2308`, `g1_mid_C_inflation_3875/:2312`,
  `G1_midN8_banked/:2316` (C 38.75, U 72.84), `g2_telescope8_mid/:2389`,
  `g2_log_endpoints_mid/:2398`, `g2_S_align_mid/:2408`,
  `g2_log_link8_mid/:2417`, `g2_residual_eq_mid/:2562`,
  `g2_G2_of_telescope_normcap_mid/:2580`, `wMid_norm_sq_U0/:2634`,
  `g2_mid_C2_inflation_920/:2638`, `G2_midN8_banked/:2644` (C2 9.20, U0 5.68),
  `H3_mid_banked/:2648`, `H3_mid_banked_numeric/:2672` cap 8.51.
- wInner specs: `wInner/:78` def mk 0.1975 (-0.375), `wInner_re/:92`,
  `wInner_im/:94`, `lower_inner/:329` Gamma discount only; zero hits for
  `S_inner`, `cN_inner`, `target_inner`, `G1_inner`, `G2_inner`, `H3_inner`,
  `wInner_add8`, `stirling_wInner`, `g2_inner`, `wInner_shift` before this section.
- outer/leaf numerics: `H3_outer_banked_numeric/:1639` cap 1.16,
  `H3_leaf_banked_numeric/:2160` cap 2.56.
- generic reuse (proved earlier, reused here): `digamma_shift_nat/:907`,
  `digamma_shift_8fold/:945`, `shift_avoid_of_re_pos/:894`.

Attempt (honest mirror at inner coords with N = 8): `wInner + 8` has
Re 8.1975 > 0 and Im -0.375, so `|Im| = 0.375 < 1 / 2`. Shift-avoid,
8-fold shift, add8 Re/Im, Im-floor denom bounds, norm-sq caps, and the
H3 combiner all mirror and are banked below. The StirlingVert lead does
NOT mirror: both `digamma_stirling` and `norm_eps_le` require
`1 / 2 ≤ |w.im|`; here the banked facts `inner_add8_im_abs_lt_half` and
`inner_im_abs_lt_half` give `|Im| = 0.375 < 1 / 2` at `wInner + 8` and at
`wInner`, so the G1 native disc and the G2 eps caps have no premise
discharge at inner. Hence G1/G2 stay Props and H3 stays conditional via
`h3_inner_of_G1_G2`. No new imports; this section only; no existing lines
modified.
-/

namespace Door3ComplexWendel

noncomputable def S_innerN8 : ℂ :=
  ∑ k ∈ Finset.range 8, (wInner + (k : ℂ))⁻¹

noncomputable def cN_innerN8 : ℂ :=
  Complex.log (wInner + (8 : ℂ)) - (1 : ℂ) / (2 * (wInner + (8 : ℂ)))

noncomputable def target_inner : ℂ :=
  Complex.log wInner - (1 : ℂ) / (2 * wInner)

noncomputable def G1_innerN8_prop (C : ℝ) : Prop :=
  ‖Complex.digamma (wInner + (8 : ℂ)) -
    (Complex.log (wInner + (8 : ℂ)) - (1 : ℂ) / (2 * (wInner + (8 : ℂ))))‖ ≤
    C / ‖wInner + (8 : ℂ)‖ ^ 2

noncomputable def G2_innerN8_prop (C2 : ℝ) : Prop :=
  ‖(cN_innerN8 - S_innerN8) - target_inner‖ ≤ C2 / ‖wInner‖ ^ 2

theorem wInner_re_pos : 0 < wInner.re := by
  rw [wInner_re]
  norm_num

theorem wInner_shift_avoid (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wInner + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) :=
  shift_avoid_of_re_pos wInner 8 wInner_re_pos k hk m

theorem digamma_shift_wInner_8 :
    Complex.digamma (wInner + (8 : ℂ)) =
      Complex.digamma wInner + S_innerN8 := by
  have hAvoid : ∀ (k : ℕ), k ≤ 8 → ∀ (m : ℕ),
      (wInner + ((k : ℕ) : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
    intro k hk m
    exact wInner_shift_avoid k hk m
  have h := digamma_shift_8fold wInner hAvoid
  have hcast8 : (((8 : ℕ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast8] at h
  unfold S_innerN8
  exact h

theorem wInner_add8_re : (wInner + (8 : ℂ)).re = 8.1975 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_re, wInner_re, Complex.natCast_re]
  norm_num

theorem wInner_add8_im : (wInner + (8 : ℂ)).im = -0.375 := by
  have hcast : ((8 : ℕ) : ℂ) = (8 : ℂ) := by simp
  rw [← hcast, Complex.add_im, wInner_im, Complex.natCast_im]
  norm_num

theorem h3_inner_of_G1_G2 (C1 C2 : ℝ)
    (hEq : Complex.digamma (wInner + (8 : ℂ)) =
      Complex.digamma wInner + S_innerN8)
    (hG1 : G1_innerN8_prop C1) (hG2 : G2_innerN8_prop C2) :
    ‖Complex.digamma wInner - target_inner‖ ≤
      C1 / ‖wInner + (8 : ℂ)‖ ^ 2 + C2 / ‖wInner‖ ^ 2 := by
  have hDisc : ‖Complex.digamma (wInner + (8 : ℂ)) - cN_innerN8‖ ≤
      C1 / ‖wInner + (8 : ℂ)‖ ^ 2 := hG1
  have hLink : ‖(cN_innerN8 - S_innerN8) - target_inner‖ ≤
      C2 / ‖wInner‖ ^ 2 := hG2
  have hT : ‖Complex.digamma wInner - (cN_innerN8 - S_innerN8)‖ ≤
      C1 / ‖wInner + (8 : ℂ)‖ ^ 2 := by
    have hSame : Complex.digamma wInner - (cN_innerN8 - S_innerN8) =
        Complex.digamma (wInner + (8 : ℂ)) - cN_innerN8 := by
      rw [hEq]
      ring
    rw [hSame]
    exact hDisc
  have hSplit : Complex.digamma wInner - target_inner =
      (Complex.digamma wInner - (cN_innerN8 - S_innerN8)) +
        ((cN_innerN8 - S_innerN8) - target_inner) := by
    ring
  calc ‖Complex.digamma wInner - target_inner‖
      ≤ ‖Complex.digamma wInner - (cN_innerN8 - S_innerN8)‖ +
        ‖(cN_innerN8 - S_innerN8) - target_inner‖ := by
          rw [hSplit]
          exact norm_add_le _ _
    _ ≤ C1 / ‖wInner + (8 : ℂ)‖ ^ 2 + C2 / ‖wInner‖ ^ 2 :=
          add_le_add hT hLink

theorem g2_denom_lower_wInner (m : ℝ) :
    (0.375 : ℝ) ≤ ‖(m : ℂ) + wInner‖ := by
  have hle : |(((m : ℂ) + wInner)).im| ≤ ‖(m : ℂ) + wInner‖ :=
    Complex.abs_im_le_norm _
  have him2 : ((((m : ℂ) + wInner)).im) = (-0.375 : ℝ) := by
    simp [wInner_im]
  have habs : |((((m : ℂ) + wInner)).im)| = (0.375 : ℝ) := by
    rw [him2]
    norm_num
  linarith

theorem g2_norm_wInner_lower : (0.375 : ℝ) ≤ ‖wInner‖ := by
  have h := g2_denom_lower_wInner 0
  have hcast : (((0 : ℝ)) : ℂ) = (0 : ℂ) := by
    simp
  rw [hcast, zero_add] at h
  exact h

theorem g2_norm_wInner8_lower : (0.375 : ℝ) ≤ ‖wInner + (8 : ℂ)‖ := by
  have h := g2_denom_lower_wInner 8
  have hcast : (((8 : ℝ)) : ℂ) = (8 : ℂ) := by
    simp
  rw [hcast, add_comm] at h
  exact h

theorem wInner_norm_sq_U0 : ‖wInner‖ ^ 2 ≤ (0.18 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wInner_re, wInner_im]
  norm_num

theorem wInner8_norm_sq_U : ‖wInner + (8 : ℂ)‖ ^ 2 ≤ (67.34 : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, wInner_add8_re, wInner_add8_im]
  norm_num

theorem inner_im_abs_lt_half : |wInner.im| < 1 / 2 := by
  rw [wInner_im]
  norm_num

theorem inner_add8_im_abs_lt_half : |(wInner + (8 : ℂ)).im| < 1 / 2 := by
  rw [wInner_add8_im]
  norm_num

/-! Section-25 residual (exact, no force): banked `wInner_re_pos`,
`wInner_shift_avoid`, `digamma_shift_wInner_8` (exact hEq shape for
`h3_inner_of_G1_G2`), `wInner_add8_re` (8.1975), `wInner_add8_im` (-0.375),
`h3_inner_of_G1_G2` combiner, denom floors `g2_denom_lower_wInner`,
`g2_norm_wInner_lower`, `g2_norm_wInner8_lower` (floor 0.375), norm-sq caps
`wInner_norm_sq_U0` (U0 0.18: 0.1975^2+0.375^2 = 0.17963125) and
`wInner8_norm_sq_U` (U 67.34: 8.1975^2+0.375^2 = 67.33963125), plus the
blocker `inner_im_abs_lt_half` / `inner_add8_im_abs_lt_half`
(`|Im| = 0.375 < 1/2`). Gap: `G1_innerN8_prop C` needs the StirlingVert
lead requiring `1/2 ≤ |Im|` at `wInner + 8` (fails by the blocker);
`G2_innerN8_prop C2` needs the eps caps requiring `1/2 ≤ |Im|` at
`wInner` shifts (fails by the same Im); hence H3 at `wInner` stays
conditional via `h3_inner_of_G1_G2`. No numeric cap banked here.
-/

end Door3ComplexWendel

/-! ## 26. WENDEL-FINAL ledger (PROOF-ONLY, FENCED, no build): single audit, then STOP.

Greps (before edit, this turn, this file only):
- outer: `G1_outerN8_banked/:1570` (C 13.54), `G2_outerN8_banked/:1526` (C2 8.63),
  `H3_outer_banked/:1573` two-term, `H3_outer_banked_numeric/:1639` cap 1.16,
  `wOuter_norm_sq_U0/:1516` (19.18), `wOuter8_norm_sq_U/:1562` (86.34);
- leaf: `G1_leafN8_banked/:1804` (C 20.30), `G2_leafN8_banked/:2132` (C2 8.82),
  `H3_leaf_banked/:2136` two-term, `H3_leaf_banked_numeric/:2160` cap 2.56,
  `wLeaf_norm_sq_U0/:2122` (11.41), `wLeaf8_norm_sq_U/:1796` (77.01);
- mid: `G1_midN8_banked/:2316` (C 38.75), `G2_midN8_banked/:2644` (C2 9.20),
  `H3_mid_banked/:2648` two-term, `H3_mid_banked_numeric/:2672` cap 8.51,
  `wMid_norm_sq_U0/:2634` (5.68), `wMid8_norm_sq_U/:2308` (72.84);
- inner: `S_innerN8/:2722`, `cN_innerN8/:2725`, `target_inner/:2728`,
  `G1_innerN8_prop/:2731` (open Prop), `G2_innerN8_prop/:2736` (open Prop),
  `digamma_shift_wInner_8/:2747` (banked hEq), `h3_inner_of_G1_G2/:2771`
  (conditional combiner), `wInner_norm_sq_U0/:2826` (0.18),
  `wInner8_norm_sq_U/:2830` (67.34), `inner_im_abs_lt_half/:2834`,
  `inner_add8_im_abs_lt_half/:2838` (blocker pair, |Im| = 0.375 < 1/2);
- discounts: `lower_outer/:263`, `lower_leaf/:285`, `lower_mid/:307`,
  `lower_inner/:329`; caps `gamma_cap_08025/:186`, `gamma_cap_09/:198`;
- banked-code tactic check: prior hits comment-only; this section adds zero
  new hits and uses only `exact`/`have`/`rw` style steps.

Banked here (this section only, no new imports, no existing lines modified):
`wendel_inner_H3_conditional` (hEq eliminated via `digamma_shift_wInner_8`,
leaving exactly the two open Props as premises) and `wendel_final_ledger`
(single conjunction of every closed wendel-lane value listed above plus the
inner blocker pair and all eight norm-sq caps). Open Props stay open and are
filed in the residual note below; nothing is forced.
-/

namespace Door3ComplexWendel

theorem wendel_inner_H3_conditional (C1 C2 : ℝ)
    (hG1 : G1_innerN8_prop C1) (hG2 : G2_innerN8_prop C2) :
    ‖Complex.digamma wInner - target_inner‖ ≤
      C1 / ‖wInner + (8 : ℂ)‖ ^ 2 + C2 / ‖wInner‖ ^ 2 :=
  h3_inner_of_G1_G2 C1 C2 digamma_shift_wInner_8 hG1 hG2

theorem wendel_final_ledger :
    G1_outerN8_prop 13.54 ∧
    G2_outerN8_prop 8.63 ∧
    (‖Complex.digamma wOuter - target_outer‖ ≤
      (13.54 : ℝ) / ‖wOuter + (8 : ℂ)‖ ^ 2 + (8.63 : ℝ) / ‖wOuter‖ ^ 2) ∧
    (‖Complex.digamma wOuter - target_outer‖ ≤ (1.16 : ℝ)) ∧
    G1_leafN8_prop 20.30 ∧
    G2_leafN8_prop 8.82 ∧
    (‖Complex.digamma wLeaf - target_leaf‖ ≤
      (20.30 : ℝ) / ‖wLeaf + (8 : ℂ)‖ ^ 2 + (8.82 : ℝ) / ‖wLeaf‖ ^ 2) ∧
    (‖Complex.digamma wLeaf - target_leaf‖ ≤ (2.56 : ℝ)) ∧
    G1_midN8_prop 38.75 ∧
    G2_midN8_prop 9.20 ∧
    (‖Complex.digamma wMid - target_mid‖ ≤
      (38.75 : ℝ) / ‖wMid + (8 : ℂ)‖ ^ 2 + (9.20 : ℝ) / ‖wMid‖ ^ 2) ∧
    (‖Complex.digamma wMid - target_mid‖ ≤ (8.51 : ℝ)) ∧
    (|wInner.im| < 1 / 2) ∧
    (|(wInner + (8 : ℂ)).im| < 1 / 2) ∧
    (‖wOuter‖ ^ 2 ≤ (19.18 : ℝ)) ∧
    (‖wOuter + (8 : ℂ)‖ ^ 2 ≤ (86.34 : ℝ)) ∧
    (‖wLeaf‖ ^ 2 ≤ (11.41 : ℝ)) ∧
    (‖wLeaf + (8 : ℂ)‖ ^ 2 ≤ (77.01 : ℝ)) ∧
    (‖wMid‖ ^ 2 ≤ (5.68 : ℝ)) ∧
    (‖wMid + (8 : ℂ)‖ ^ 2 ≤ (72.84 : ℝ)) ∧
    (‖wInner‖ ^ 2 ≤ (0.18 : ℝ)) ∧
    (‖wInner + (8 : ℂ)‖ ^ 2 ≤ (67.34 : ℝ)) ∧
    (Real.pi / (2 * Real.exp (Real.pi * 4.375) * 1.25) ≤
      ‖Complex.Gamma wOuter‖) ∧
    (Real.pi / (2 * Real.exp (Real.pi * 3.375) * 1.12) ≤
      ‖Complex.Gamma wLeaf‖) ∧
    (Real.pi / (2 * Real.exp (Real.pi * 2.375) * 1.25) ≤
      ‖Complex.Gamma wMid‖) ∧
    (Real.pi / (2 * Real.exp (Real.pi * 0.375) * 1.25) ≤
      ‖Complex.Gamma wInner‖) ∧
    (Real.Gamma 0.8025 ≤ (1.25 : ℝ)) ∧
    (Real.Gamma 0.9 ≤ (1.12 : ℝ)) ∧
    (Complex.digamma (wInner + (8 : ℂ)) =
      Complex.digamma wInner + S_innerN8) := by
  exact ⟨G1_outerN8_banked, G2_outerN8_banked, H3_outer_banked,
    H3_outer_banked_numeric, G1_leafN8_banked, G2_leafN8_banked,
    H3_leaf_banked, H3_leaf_banked_numeric, G1_midN8_banked, G2_midN8_banked,
    H3_mid_banked, H3_mid_banked_numeric, inner_im_abs_lt_half,
    inner_add8_im_abs_lt_half, wOuter_norm_sq_U0, wOuter8_norm_sq_U,
    wLeaf_norm_sq_U0, wLeaf8_norm_sq_U, wMid_norm_sq_U0, wMid8_norm_sq_U,
    wInner_norm_sq_U0, wInner8_norm_sq_U, lower_outer, lower_leaf,
    lower_mid, lower_inner, gamma_cap_08025, gamma_cap_09,
    digamma_shift_wInner_8⟩

/-! FINAL residual list (complete, honest, no force):
R1 outer CLOSED: G1 `G1_outerN8_banked` (C 13.54, U 86.34), G2
  `G2_outerN8_banked` (C2 8.63, U0 19.18), H3 `H3_outer_banked` two-term,
  numeric `H3_outer_banked_numeric` 1.16.
R2 leaf CLOSED: G1 `G1_leafN8_banked` (C 20.30, U 77.01), G2
  `G2_leafN8_banked` (C2 8.82, U0 11.41), H3 `H3_leaf_banked` two-term,
  numeric `H3_leaf_banked_numeric` 2.56.
R3 mid CLOSED: G1 `G1_midN8_banked` (C 38.75, U 72.84), G2
  `G2_midN8_banked` (C2 9.20, U0 5.68), H3 `H3_mid_banked` two-term,
  numeric `H3_mid_banked_numeric` 8.51.
R4 inner BLOCKED (sole open lane): `G1_innerN8_prop C` open (StirlingVert
  lead needs 1/2 <= |Im| at `wInner + 8`, fails by `inner_add8_im_abs_lt_half`
  with |Im| = 0.375); `G2_innerN8_prop C2` open (eps caps need 1/2 <= |Im|
  at `wInner` shifts, fails by `inner_im_abs_lt_half`); H3 conditional only
  via `h3_inner_of_G1_G2` / `wendel_inner_H3_conditional` with banked hEq
  `digamma_shift_wInner_8`; norm caps banked (`wInner_norm_sq_U0` 0.18,
  `wInner8_norm_sq_U` 67.34); floors banked (`g2_denom_lower_wInner` 0.375);
  no numeric cap banked for inner.
R5 discount lowers CLOSED but insufficient at large |Im|: `lower_outer`
  (~1.4e-6, formal <= 2e-6 via `outer_small`), `lower_leaf` (~3.5e-5,
  formal <= 4e-5 via `leaf_small`), `lower_mid` (~7.3e-4, formal <= 8e-4
  via `mid_small`), `lower_inner` (~0.39, formal >= 0.38 via `inner_big`);
  companion caps `gamma_cap_08025` (1.25), `gamma_cap_09` (1.12);
  sine upper `sin_norm_le` closed; Tier-C witness `tierC_outer` closed.
R6 wider remainders untouched here: H1 Hoelder interpolation upper (section 9
  sole premise), H2 Stirling-rate |y| factor / Binet bounds (unbanked),
  PSI-SLOPE M2/M3/M4 (Gauss rep / bridge / tight uppers).
Ledger verdict: outer/leaf/mid H3 CLOSED with numeric caps 1.16 / 2.56 / 8.51;
inner H3 OPEN behind the |Im| < 1/2 blocker; file STOPs here per brief.
-/

end Door3ComplexWendel

