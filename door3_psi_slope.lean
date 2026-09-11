import Mathlib
import door3_stirling_gamma
import door3_stirling_rem
import door3_digamma

/-!
# Door-3 psi slope discs via real finite differences (WRITE-ONLY).

No build / lean / lake command run. No commit / push. Exactly one new file.
`door3_psi_slope.lean` was verified absent via glob before writing.
Import DAG checked read-only:
`door3_stirling_gamma.lean:1` imports `Mathlib` only;
`door3_stirling_rem.lean:1-2` imports `Mathlib` + `door3_stirling_gamma` only;
`door3_digamma.lean:1-2` imports `Mathlib` + `door3_stirling_gamma` only.
This file imports `Mathlib` + those three leaves only.

## Recon (read-only, route-determining)

* Sibling REM banks real Wendel two-sided + log form
  `Door3StirlingRem.D3SR_logGamma_wendel` and slope upper
  `Door3StirlingRem.D3SR_logGamma_slope_le`
  (real `x > 0`, `s` in `[0,1]`), plus real Gamma lowers and one
  reflection lower bridge. It stops before psi.
* Sibling DIGAMMA banks the conditional framework with psi-disc premises
  `psiNeed_outer / leaf / mid / inner` at TRUE-scale centers
  `cOuter = mk 1.472 (-1.64)`, `cLeaf = mk 1.213 (-1.689)`,
  `cMid = mk 0.851 (-1.697)`, `cInner = mk (-1.409) (-2.13)`,
  radii `0.5 / 0.5 / 0.5 / 1`, plus `gamNeed_*` TRUE-scale gamma uppers
  `0.002 / 0.008 / 0.04 / 4.5`, generic bridge
  `gammaPrime_le_of_psiDisc`, per-group gamma-prime uppers
  `0.003612 / 0.013608 / 0.06096 / 10.2128`, gross allowances
  `0.000857 / 0.001906 / 0.003621 / 0.037975`, and gap comparisons
  (all four GAP, ratios `4.21 / 7.13 / 16.83 / 268.9`).
  Wire centers `w = s / 2`: outer `mk 0.1975 (-4.375)`,
  leaf `mk 0.1 (-3.375)`, mid `mk 0.1975 (-2.375)`,
  inner `mk 0.1975 (-0.375)` (via `wireOuter / wireLeaf / wireMid / wireInner`).
* The brief idea (symmetric secant
  `[logGamma(w+h) - logGamma(w-h)] / (2h)` squeezing psi via two nested
  Wendel uses) is REAL-ONLY as banked: both `D3SR_logGamma_wendel` and
  `D3SR_logGamma_slope_le` take `(x : Real)` with `0 < x`. There is no
  complex log-Gamma convexity, no Gauss rep for `Complex.digamma`
  (Mathlib TODO), no trigamma bound, and no real-to-complex digamma bridge
  in the banked set. Applying the real slope forms at complex `w` with
  nonzero `Im` is not licensed by their hypotheses.

## Verdict

* CLOSED here: the missing LOWER slope half, the symmetric real squeeze
  `lo <= S <= hi` with `S = (logG(X+h)-logG(X-h))/(2h)`,
  `lo = log(X+h)-1/(X-h)`, `hi = log(X-h)`, plus disc form
  `||S - mid|| <= rad` and radius cap `rad <= 1/(2*(X-h))`,
  all for real `X - h > 0`, `h > 0`, `2*h <= 1`, proved from Wendel upper
  plus one `log(y) <= y-1` use. Per-group real discs at shifted base
  `X = Re(w)+8` (matching DIGAMMA shift `N = 8`) with `h = 0.25` have
  `rad < 0.5`, tighter than the assumed `0.5 / 1.0`.
* NOT closed: complex `psiNeed_*` discharge. The real discs live at real
  `X` near `8.1` with zero imaginary part; `psiNeed_*` live at complex `w`
  with `Im` in `{-4.375, -3.375, -2.375, -0.375}`. No banked lemma moves a
  real log-Gamma secant bound to a `Complex.digamma` disc at complex `w`.
  Hence gamma-prime verdicts stay GAP per the DIGAMMA allowance table.
  Centers `c` are left exactly as DIGAMMA stated (no correction claimed;
  numeric honesty of `log w - 1/(2w)` values is not re-checked here).

All proofs full, explicit binders, small numerals only.
-/

noncomputable section

namespace Door3PsiSlope

open scoped BigOperators

/-! ## 0. Center confirmation (exact DIGAMMA shapes). -/

theorem confirm_wOuter : Door3Digamma.wOuter = Complex.mk 0.1975 (-4.375) := by
  unfold Door3Digamma.wOuter
  exact Door3Digamma.wireOuter

theorem confirm_wLeaf : Door3Digamma.wLeaf = Complex.mk 0.1 (-3.375) := by
  unfold Door3Digamma.wLeaf
  exact Door3Digamma.wireLeaf

theorem confirm_wMid : Door3Digamma.wMid = Complex.mk 0.1975 (-2.375) := by
  unfold Door3Digamma.wMid
  exact Door3Digamma.wireMid

theorem confirm_wInner : Door3Digamma.wInner = Complex.mk 0.1975 (-0.375) := by
  unfold Door3Digamma.wInner
  exact Door3Digamma.wireInner

theorem confirm_cOuter : Door3Digamma.cOuter = Complex.mk 1.472 (-1.64) := rfl

theorem confirm_cLeaf : Door3Digamma.cLeaf = Complex.mk 1.213 (-1.689) := rfl

theorem confirm_cMid : Door3Digamma.cMid = Complex.mk 0.851 (-1.697) := rfl

theorem confirm_cInner : Door3Digamma.cInner = Complex.mk (-1.409) (-2.13) := rfl

/-! ## 1. Real slope objects. -/

noncomputable def slopeS (X : ℝ) (h : ℝ) : ℝ :=
  (Real.log (Real.Gamma (X + h)) - Real.log (Real.Gamma (X - h))) / (2 * h)

noncomputable def loBound (X : ℝ) (h : ℝ) : ℝ :=
  Real.log (X + h) - 1 / (X - h)

noncomputable def hiBound (X : ℝ) (h : ℝ) : ℝ :=
  Real.log (X - h)

noncomputable def midPt (X : ℝ) (h : ℝ) : ℝ :=
  (loBound X h + hiBound X h) / 2

noncomputable def radPt (X : ℝ) (h : ℝ) : ℝ :=
  (hiBound X h - loBound X h) / 2

/-! ## 2. Lower slope half (complement to banked upper). -/

theorem slope_lower (x : ℝ) (s : ℝ) (hx : 0 < x) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.log (x + s) - 1 / x ≤
      (Real.log (Real.Gamma (x + s)) - Real.log (Real.Gamma x)) / s := by
  have hxs : 0 < x + s := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx
  have hxsne : x + s ≠ 0 := ne_of_gt hxs
  have h1s0 : 0 ≤ 1 - s := by linarith
  have h1s1 : 1 - s ≤ 1 := by linarith
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxne : Real.Gamma x ≠ 0 := ne_of_gt hGx
  have hup := Door3StirlingRem.D3SR_logGamma_wendel (x + s) (1 - s) hxs h1s0 h1s1
  have hcomb : (x + s) + (1 - s) = x + 1 := by ring
  rw [hcomb] at hup
  have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hxne
  have hlog1 : Real.log (Real.Gamma (x + 1))
      = Real.log x + Real.log (Real.Gamma x) := by
    rw [hG1, Real.log_mul hxne hGxne]
  rw [hlog1] at hup
  have hnum_le : Real.log x - (1 - s) * Real.log (x + s) ≤
      Real.log (Real.Gamma (x + s)) - Real.log (Real.Gamma x) := by
    linarith
  have hratio_pos : 0 < (x + s) / x := div_pos hxs hx
  have hdiff_le : Real.log (x + s) - Real.log x ≤ s / x := by
    have h1 : Real.log ((x + s) / x) ≤ (x + s) / x - 1 :=
      Real.log_le_sub_one_of_pos hratio_pos
    have h2 : Real.log ((x + s) / x) = Real.log (x + s) - Real.log x :=
      Real.log_div hxsne hxne
    have h3 : (x + s) / x - 1 = s / x := by
      field_simp
      ring
    rw [h2] at h1
    rw [h3] at h1
    exact h1
  rw [le_div_iff₀ hs0]
  have hstep : (Real.log (x + s) - 1 / x) * s ≤
      Real.log x - (1 - s) * Real.log (x + s) := by
    have hexpand : (Real.log (x + s) - 1 / x) * s
        = s * Real.log (x + s) - s / x := by
      ring
    have hexpand2 : Real.log x - (1 - s) * Real.log (x + s)
        = Real.log x - Real.log (x + s) + s * Real.log (x + s) := by
      ring
    rw [hexpand, hexpand2]
    linarith [hdiff_le]
  exact le_trans hstep hnum_le

/-! ## 3. Symmetric real squeeze (two nested Wendel uses). -/

theorem symm_mem (X : ℝ) (h : ℝ) (hXh : 0 < X - h) (hh0 : 0 < h)
    (hh1 : 2 * h ≤ 1) :
    loBound X h ≤ slopeS X h ∧ slopeS X h ≤ hiBound X h := by
  have hx : 0 < X - h := hXh
  have hs0 : 0 < 2 * h := by linarith
  have hs1 : 2 * h ≤ 1 := hh1
  have heq : (X - h) + (2 * h) = X + h := by ring
  have hup := Door3StirlingRem.D3SR_logGamma_slope_le (X - h) (2 * h) hx hs0 hs1
  have hlow := slope_lower (X - h) (2 * h) hx hs0 hs1
  rw [heq] at hup
  rw [heq] at hlow
  unfold loBound hiBound slopeS
  constructor
  · exact hlow
  · exact hup

theorem slope_disc (X : ℝ) (h : ℝ) (hXh : 0 < X - h) (hh0 : 0 < h)
    (hh1 : 2 * h ≤ 1) :
    ‖slopeS X h - midPt X h‖ ≤ radPt X h := by
  have hmem := symm_mem X h hXh hh0 hh1
  have hlo : loBound X h ≤ slopeS X h := hmem.1
  have hhi : slopeS X h ≤ hiBound X h := hmem.2
  have hmid : midPt X h = (loBound X h + hiBound X h) / 2 := rfl
  have hrad : radPt X h = (hiBound X h - loBound X h) / 2 := rfl
  rw [hmid, hrad, Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem rad_le_inv (X : ℝ) (h : ℝ) (hXh : 0 < X - h) (hh0 : 0 < h)
    (hXph : 0 < X + h) :
    radPt X h ≤ 1 / (2 * (X - h)) := by
  have hXhne : (X - h) ≠ 0 := ne_of_gt hXh
  have hXphne : (X + h) ≠ 0 := ne_of_gt hXph
  have hdiv : Real.log ((X + h) / (X - h))
      = Real.log (X + h) - Real.log (X - h) :=
    Real.log_div hXphne hXhne
  have hratio : 1 ≤ (X + h) / (X - h) := by
    rw [le_div_iff₀ hXh]
    linarith
  have hnn : 0 ≤ Real.log ((X + h) / (X - h)) :=
    Real.log_nonneg hratio
  have hrad_eq : radPt X h
      = (1 / (X - h) - Real.log ((X + h) / (X - h))) / 2 := by
    unfold radPt loBound hiBound
    rw [hdiv]
    ring
  have heq2 : 1 / (2 * (X - h)) = (1 / (X - h)) / 2 := by
    ring
  rw [hrad_eq, heq2]
  linarith [hnn]

/-! ## 4. Shift record: real bases are `Re(w) + 8` (DIGAMMA `N = 8`). -/

theorem shift_outer : (8.1975 : ℝ) = Door3Digamma.wOuter.re + 8 := by
  have hw : Door3Digamma.wOuter = Complex.mk 0.1975 (-4.375) := confirm_wOuter
  rw [hw]
  norm_num

theorem shift_leaf : (8.1 : ℝ) = Door3Digamma.wLeaf.re + 8 := by
  have hw : Door3Digamma.wLeaf = Complex.mk 0.1 (-3.375) := confirm_wLeaf
  rw [hw]
  norm_num

theorem shift_mid : (8.1975 : ℝ) = Door3Digamma.wMid.re + 8 := by
  have hw : Door3Digamma.wMid = Complex.mk 0.1975 (-2.375) := confirm_wMid
  rw [hw]
  norm_num

theorem shift_inner : (8.1975 : ℝ) = Door3Digamma.wInner.re + 8 := by
  have hw : Door3Digamma.wInner = Complex.mk 0.1975 (-0.375) := confirm_wInner
  rw [hw]
  norm_num

/-! ## 5. Per-group real slope discs (`h = 0.25`, tighter than `0.5 / 1.0`). -/

theorem psiSlope_outer_mem :
    loBound (8.1975 : ℝ) (0.25 : ℝ) ≤ slopeS (8.1975 : ℝ) (0.25 : ℝ) ∧
      slopeS (8.1975 : ℝ) (0.25 : ℝ) ≤ hiBound (8.1975 : ℝ) (0.25 : ℝ) :=
  symm_mem _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_outer_disc :
    ‖slopeS (8.1975 : ℝ) (0.25 : ℝ) - midPt (8.1975 : ℝ) (0.25 : ℝ)‖ ≤
      radPt (8.1975 : ℝ) (0.25 : ℝ) :=
  slope_disc _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_outer_rad_le :
    radPt (8.1975 : ℝ) (0.25 : ℝ) ≤ 1 / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) :=
  rad_le_inv _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_outer_tight : radPt (8.1975 : ℝ) (0.25 : ℝ) < (0.5 : ℝ) := by
  have hle := psiSlope_outer_rad_le
  have hnum : (1 : ℝ) / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) < 0.5 := by
    norm_num
  exact lt_of_le_of_lt hle hnum

theorem psiSlope_leaf_mem :
    loBound (8.1 : ℝ) (0.25 : ℝ) ≤ slopeS (8.1 : ℝ) (0.25 : ℝ) ∧
      slopeS (8.1 : ℝ) (0.25 : ℝ) ≤ hiBound (8.1 : ℝ) (0.25 : ℝ) :=
  symm_mem _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_leaf_disc :
    ‖slopeS (8.1 : ℝ) (0.25 : ℝ) - midPt (8.1 : ℝ) (0.25 : ℝ)‖ ≤
      radPt (8.1 : ℝ) (0.25 : ℝ) :=
  slope_disc _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_leaf_rad_le :
    radPt (8.1 : ℝ) (0.25 : ℝ) ≤ 1 / (2 * ((8.1 : ℝ) - (0.25 : ℝ))) :=
  rad_le_inv _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_leaf_tight : radPt (8.1 : ℝ) (0.25 : ℝ) < (0.5 : ℝ) := by
  have hle := psiSlope_leaf_rad_le
  have hnum : (1 : ℝ) / (2 * ((8.1 : ℝ) - (0.25 : ℝ))) < 0.5 := by
    norm_num
  exact lt_of_le_of_lt hle hnum

theorem psiSlope_mid_mem :
    loBound (8.1975 : ℝ) (0.25 : ℝ) ≤ slopeS (8.1975 : ℝ) (0.25 : ℝ) ∧
      slopeS (8.1975 : ℝ) (0.25 : ℝ) ≤ hiBound (8.1975 : ℝ) (0.25 : ℝ) :=
  symm_mem _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_mid_disc :
    ‖slopeS (8.1975 : ℝ) (0.25 : ℝ) - midPt (8.1975 : ℝ) (0.25 : ℝ)‖ ≤
      radPt (8.1975 : ℝ) (0.25 : ℝ) :=
  slope_disc _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_mid_rad_le :
    radPt (8.1975 : ℝ) (0.25 : ℝ) ≤ 1 / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) :=
  rad_le_inv _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_mid_tight : radPt (8.1975 : ℝ) (0.25 : ℝ) < (0.5 : ℝ) := by
  have hle := psiSlope_mid_rad_le
  have hnum : (1 : ℝ) / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) < 0.5 := by
    norm_num
  exact lt_of_le_of_lt hle hnum

theorem psiSlope_inner_mem :
    loBound (8.1975 : ℝ) (0.25 : ℝ) ≤ slopeS (8.1975 : ℝ) (0.25 : ℝ) ∧
      slopeS (8.1975 : ℝ) (0.25 : ℝ) ≤ hiBound (8.1975 : ℝ) (0.25 : ℝ) :=
  symm_mem _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_inner_disc :
    ‖slopeS (8.1975 : ℝ) (0.25 : ℝ) - midPt (8.1975 : ℝ) (0.25 : ℝ)‖ ≤
      radPt (8.1975 : ℝ) (0.25 : ℝ) :=
  slope_disc _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_inner_rad_le :
    radPt (8.1975 : ℝ) (0.25 : ℝ) ≤ 1 / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) :=
  rad_le_inv _ _ (by norm_num) (by norm_num) (by norm_num)

theorem psiSlope_inner_tight : radPt (8.1975 : ℝ) (0.25 : ℝ) < (1 : ℝ) := by
  have hle := psiSlope_inner_rad_le
  have hnum : (1 : ℝ) / (2 * ((8.1975 : ℝ) - (0.25 : ℝ))) < 1 := by
    norm_num
  exact lt_of_le_of_lt hle hnum

/-! ## 6. Gamma-prime verdicts vs DIGAMMA allowances (unchanged: GAP).

The real discs above do not discharge `psiNeed_*` (real base `X` near
`8.1` with zero imaginary part vs complex `w` with nonzero `Im`; banked
Wendel is real-only). Hence the conditional gamma-prime chain stays as
banked: uppers exceed gross budgets in all four groups.
-/

theorem gammaVerdict_outer : (0.000857 : ℝ) < (0.003612 : ℝ) :=
  Door3Digamma.gap_outer

theorem gammaVerdict_leaf : (0.001906 : ℝ) < (0.013608 : ℝ) :=
  Door3Digamma.gap_leaf

theorem gammaVerdict_mid : (0.003621 : ℝ) < (0.06096 : ℝ) :=
  Door3Digamma.gap_mid

theorem gammaVerdict_inner : (0.037975 : ℝ) < (10.2128 : ℝ) :=
  Door3Digamma.gap_inner

/-! ## 7. Remainder (discharge record + missing pieces).

* Discharge: NONE of `Door3Digamma.psiNeed_outer / psiNeed_leaf /
  psiNeed_mid / psiNeed_inner` is proved here. The closed discs
  `psiSlope_outer_disc / psiSlope_leaf_disc / psiSlope_mid_disc /
  psiSlope_inner_disc` are REAL log-Gamma secant discs at shifted real
  bases `8.1975 / 8.1 / 8.1975 / 8.1975` with half-step `0.25`; they share
  the DIGAMMA shift `N = 8` on the real axis only. Transfer to complex
  `wOuter / wLeaf / wMid / wInner` needs a complex Wendel / complex
  log-Gamma convexity bound, which is not in the banked set.
* Centers: DIGAMMA `cOuter / cLeaf / cMid / cInner` kept exactly
  (`confirm_cOuter` etc); no correction claimed. Real mid points
  `midPt X h` are distinct objects at large real `X`, not replacements.
* Gamma-prime: per-group verdict GAP (see section 6): outer `0.003612`
  vs allow `0.000857`; leaf `0.013608` vs `0.001906`; mid `0.06096` vs
  `0.003621`; inner `10.2128` vs `0.037975`. Ratios already banked as
  `ratio_outer / ratio_leaf / ratio_mid / ratio_inner`.
* Missing pieces (precise): (M1) complex Wendel two-sided bound for
  `Complex.Gamma` / complex `logGamma` with explicit factors; (M2) Gauss
  integral rep for `Complex.digamma` (Mathlib TODO) or explicit remainder
  `||digamma w - (log w - 1/(2*w))|| <= C/||w||^2`; (M3) real-to-complex
  digamma bridge at the four `w` centers linking `slopeS` to
  `Complex.digamma`; (M4) tight TRUE-scale gamma uppers at
  `Re` in `{0.1, 0.1975}` (banked decay line is at `Re = 0.95`).
-/

end Door3PsiSlope
