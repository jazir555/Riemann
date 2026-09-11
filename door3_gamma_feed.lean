import Mathlib
import central_cover_assembly
import door3_stirling_gamma
import door3_gamma_low
import door3_gamma_disc
import door3_gamma_real_low

/-!
# Door 3 gamma FEED (REALGAM-LOW 0.77 × GAMDISC conditionals).

Cycle safety (verified read-only before writing):
* `door3_stirling_gamma.lean:1` imports `Mathlib` only.
* `central_cover_assembly.lean:1-3` imports `Mathlib`, `riemann_hypothesis`,
  `rh_certificate_infra` (no door3 import).
* `door3_gamma_low.lean:1-3` imports `Mathlib` + `central_cover_assembly`
  + `door3_stirling_gamma` (DAG leaf, no cycle).
* `door3_gamma_disc.lean:1-4` imports `Mathlib` + `central_cover_assembly`
  + `door3_stirling_gamma` + `door3_gamma_low` (DAG leaf).
* `door3_gamma_real_low.lean:1` imports `Mathlib` only (DAG leaf).
* Hence this file (`Mathlib` + `central_cover_assembly` + `door3_stirling_gamma`
  + `door3_gamma_low` + `door3_gamma_disc` + `door3_gamma_real_low`) is a DAG
  leaf. It does NOT import `door3_premise_gamma` (keeps the lane
  one-directional; each `gammaFeed_*_ge` below restates the matching
  `premGamma_*_ge` verbatim via the `gammaOf` unfold, so discharge is recorded
  by restatement).

Recon (brief, read-only):
* 30 conditional shapes in `door3_gamma_disc.lean` (`R28/R35/R38/R29_cond` are
  two-step `k = 2` with banked denominator products `2.83*3.83`, `0.58*1.58`,
  `2.83*3.83`, `3.83*4.83`; the other 26 are one-step `k = 1` with a single
  banked denominator `4.58 / 3.83 / 3.58 / 3.33 / 2.83 / 2.58 / 1.83 / 1.58 /
  0.83 / 0.58` from the matching `Door3GammaLow.*_w_norm_le`). Each conditional
  needs a numerator premise `c ≤ ‖Complex.Gamma (w + k)‖` at the shifted point.
* `gamma_low_77` (`door3_gamma_real_low.lean:220`):
  `∀ x ∈ Icc 1 2.1, (0.77 : ℝ) ≤ Real.Gamma x`. All 30 shifted `Re` lie in
  `[1, 2.1]` (single-step `[1.05, 1.2]`; two-step `2.0525 / 2.1`), so the real
  lower covers the shifted real line.
* `premGamma_*_ge` target Props (`door3_premise_gamma.lean:81-169`): floors and
  `s`-centers restated below as `gammaFeed_*_ge` via
  `gammaOf s = Complex.Gamma (s / 2)` (`central_cover_assembly.lean:6334`).
* `gammaOf` unfold (`:6334` per GAMDISC note):
  `DerivCauchyBridge.gammaOf s = Complex.Gamma (s / 2)` (used once as
  `feed_gammaOf_eq` by `rfl`, then per-theorem `unfold`).

Feed audit — why 0 unconditional closes (no forcing):
* The disc numerator premise is a COMPLEX lower `c ≤ ‖Γ(w+k)‖` at a shifted
  point with `|Im| > 0` (every center has `|Im| ≥ 0.375`, half-point
  `|Im| ≥ 0.1875`). `gamma_low_77` is a REAL lower. The only banked
  real→complex bridge is `D3SG_Gamma_norm_le_real`
  (`‖Γ(w)‖ ≤ Real.Gamma (Re w)`): an UPPER. Using a real lower as a complex
  numerator lower reverses it and is unsound. No banked complex numerator lower
  exists at any shifted point.
* Numerically the direct plug is also false at large `|Im|`: e.g. E10 shifted
  `w+1 = 1.1975 + 4.375i` has TRUE `‖Γ‖ ~ 0.001`, far below `0.77`; claiming
  `0.77 ≤ ‖Γ(w+1)‖` there would be a false premise, not just an unproved one.
  The sibling survival table already flags this: feedability there is stated
  modulo a future sound real→complex bridge plus shifted-TRUE headroom.
* What IS sound with only the allowed imports: for each center with threshold
  `t = F × M ≤ 0.77`, the CONDITIONAL implication
  `(0.77 ≤ ‖Γ(w+k)‖) → floor ≤ ‖gammaOf center‖` via the exact disc
  conditional plus pure threshold arithmetic. The numerator hypothesis stays
  explicitly undischarged (open gap recorded per theorem). For the 6 centers
  with `t > 0.77` even the conditional at `0.77` fails, so no implication is
  stated — recorded open with numbers, nothing forced.

Thresholds at `c = 0.77` (from sibling REALGAM-LOW survival table, rechecked):
* Two-step: R28 `0.026×(2.83×3.83) = 0.28182` FEEDABLE (cond); R38
  `0.024×(2.83×3.83) = 0.26014` FEEDABLE (cond); R29 `0.0045×(3.83×4.83) =
  0.08325` FEEDABLE (cond); R35 `2×(0.58×1.58) = 1.8328` OPEN.
* Single-step FEEDABLE (cond): E10/BA00 `0.00687`; R31/R40/R21/R30 `0.00458`;
  R39 `0.01532`; E09 `0.017235`; R32/R22 `0.02148`; E01 `0.0333`; R33/R23
  `0.08256`; E08 `0.0566`; BA03 `0.0387`; R37/R27 `0.2196`; R34/R24 `0.316`;
  E07 `0.183`; BA04 `0.1264`.
* Single-step OPEN: R36/R26/E06 `0.83`; E05 `0.87`; R25 `1.16` (all exceed
  `0.77`, so not even conditionally feedable at this constant).
* Totals: 24 conditional implications proved, 0 unconditional closes, 6 open.

Line budget: well under 1200. Explicit binders throughout, small numerals
only, no placeholders.
-/

noncomputable section

namespace Door3GammaFeed

/-! ## `gammaOf` bridge (`central_cover_assembly.lean:6334`). -/

/-- `gammaOf` unfolds to `Complex.Gamma (s / 2)` by definition. -/
theorem feed_gammaOf_eq (s : ℂ) :
    DerivCauchyBridge.gammaOf s = Complex.Gamma (s / 2) := rfl

/-- The banked real lower constant, restated for the plug record. -/
theorem feed_real_77_sample (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2.1) :
    (0.77 : ℝ) ≤ Real.Gamma x :=
  Door3GammaRealLow.gamma_low_77 x hx

/-! ## Mirror Props (each discharges the matching `premGamma_*_ge` by
restatement via the `gammaOf` unfold; the premise file is not imported). -/

/-- Discharges `premGamma_BA00_ge` (floor 0.0015). -/
def gammaFeed_BA00_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-8.75))‖

/-- Discharges `premGamma_BA03_ge` (floor 0.015). -/
def gammaFeed_BA03_ge : Prop :=
  (0.015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-4.75))‖

/-- Discharges `premGamma_BA04_ge` (floor 0.08). -/
def gammaFeed_BA04_ge : Prop :=
  (0.08 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-2.75))‖

/-- Discharges `premGamma_R31_ge` (floor 0.001). -/
def gammaFeed_R31_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-8.75))‖

/-- Discharges `premGamma_R32_ge` (floor 0.006). -/
def gammaFeed_R32_ge : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-6.75))‖

/-- Discharges `premGamma_R33_ge` (floor 0.032). -/
def gammaFeed_R33_ge : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-4.75))‖

/-- Discharges `premGamma_R34_ge` (floor 0.2). -/
def gammaFeed_R34_ge : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-2.75))‖

/-- Discharges `premGamma_R35_ge` (floor 2). OPEN (threshold 1.8328 > 0.77). -/
def gammaFeed_R35_ge : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-0.75))‖

/-- Discharges `premGamma_R36_ge` (floor 1). OPEN (threshold 0.83 > 0.77). -/
def gammaFeed_R36_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 1.25)‖

/-- Discharges `premGamma_R37_ge` (floor 0.12). -/
def gammaFeed_R37_ge : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 3.25)‖

/-- Discharges `premGamma_R38_ge` (floor 0.024). -/
def gammaFeed_R38_ge : Prop :=
  (0.024 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 5.25)‖

/-- Discharges `premGamma_R39_ge` (floor 0.004). -/
def gammaFeed_R39_ge : Prop :=
  (0.004 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 7.25)‖

/-- Discharges `premGamma_R40_ge` (floor 0.001). -/
def gammaFeed_R40_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 8.75)‖

/-- Discharges `premGamma_R21_ge` (floor 0.001). -/
def gammaFeed_R21_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-8.75))‖

/-- Discharges `premGamma_R22_ge` (floor 0.006). -/
def gammaFeed_R22_ge : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-6.75))‖

/-- Discharges `premGamma_R23_ge` (floor 0.032). -/
def gammaFeed_R23_ge : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-4.75))‖

/-- Discharges `premGamma_R24_ge` (floor 0.2). -/
def gammaFeed_R24_ge : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-2.75))‖

/-- Discharges `premGamma_R25_ge` (floor 2). OPEN (threshold 1.16 > 0.77). -/
def gammaFeed_R25_ge : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-0.75))‖

/-- Discharges `premGamma_R26_ge` (floor 1). OPEN (threshold 0.83 > 0.77). -/
def gammaFeed_R26_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 1.25)‖

/-- Discharges `premGamma_R27_ge` (floor 0.12). -/
def gammaFeed_R27_ge : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 3.25)‖

/-- Discharges `premGamma_R28_ge` (floor 0.026). -/
def gammaFeed_R28_ge : Prop :=
  (0.026 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 5.25)‖

/-- Discharges `premGamma_R29_ge` (floor 0.0045). -/
def gammaFeed_R29_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 7.25)‖

/-- Discharges `premGamma_R30_ge` (floor 0.001). -/
def gammaFeed_R30_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 8.75)‖

/-- Discharges `premGamma_E01_ge` (floor 0.01). -/
def gammaFeed_E01_ge : Prop :=
  (0.01 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-6.25))‖

/-- Discharges `premGamma_E05_ge` (floor 1.5). OPEN (threshold 0.87 > 0.77). -/
def gammaFeed_E05_ge : Prop :=
  (1.5 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-0.75))‖

/-- Discharges `premGamma_E06_ge` (floor 1). OPEN (threshold 0.83 > 0.77). -/
def gammaFeed_E06_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 1.25)‖

/-- Discharges `premGamma_E07_ge` (floor 0.1). -/
def gammaFeed_E07_ge : Prop :=
  (0.1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 3.25)‖

/-- Discharges `premGamma_E08_ge` (floor 0.02). -/
def gammaFeed_E08_ge : Prop :=
  (0.02 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 5.25)‖

/-- Discharges `premGamma_E09_ge` (floor 0.0045). -/
def gammaFeed_E09_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 7.25)‖

/-- Discharges `premGamma_E10_ge` (floor 0.0015). -/
def gammaFeed_E10_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 8.75)‖

/-! ## Threshold arithmetic at `c = 0.77` (pure `norm_num`; 24 pass, 6 fail). -/

theorem feed_thresh_R28 : (0.026 : ℝ) ≤ (0.77 : ℝ) / (2.83 * 3.83) := by
  norm_num

theorem feed_thresh_R38 : (0.024 : ℝ) ≤ (0.77 : ℝ) / (2.83 * 3.83) := by
  norm_num

theorem feed_thresh_R29 : (0.0045 : ℝ) ≤ (0.77 : ℝ) / (3.83 * 4.83) := by
  norm_num

theorem feed_thresh_E10 : (0.0015 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_BA00 : (0.0015 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_R31 : (0.001 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_R40 : (0.001 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_R21 : (0.001 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_R30 : (0.001 : ℝ) ≤ (0.77 : ℝ) / 4.58 := by
  norm_num

theorem feed_thresh_R39 : (0.004 : ℝ) ≤ (0.77 : ℝ) / 3.83 := by
  norm_num

theorem feed_thresh_E09 : (0.0045 : ℝ) ≤ (0.77 : ℝ) / 3.83 := by
  norm_num

theorem feed_thresh_R32 : (0.006 : ℝ) ≤ (0.77 : ℝ) / 3.58 := by
  norm_num

theorem feed_thresh_R22 : (0.006 : ℝ) ≤ (0.77 : ℝ) / 3.58 := by
  norm_num

theorem feed_thresh_E01 : (0.01 : ℝ) ≤ (0.77 : ℝ) / 3.33 := by
  norm_num

theorem feed_thresh_R33 : (0.032 : ℝ) ≤ (0.77 : ℝ) / 2.58 := by
  norm_num

theorem feed_thresh_R23 : (0.032 : ℝ) ≤ (0.77 : ℝ) / 2.58 := by
  norm_num

theorem feed_thresh_E08 : (0.02 : ℝ) ≤ (0.77 : ℝ) / 2.83 := by
  norm_num

theorem feed_thresh_BA03 : (0.015 : ℝ) ≤ (0.77 : ℝ) / 2.58 := by
  norm_num

theorem feed_thresh_R37 : (0.12 : ℝ) ≤ (0.77 : ℝ) / 1.83 := by
  norm_num

theorem feed_thresh_R27 : (0.12 : ℝ) ≤ (0.77 : ℝ) / 1.83 := by
  norm_num

theorem feed_thresh_R34 : (0.2 : ℝ) ≤ (0.77 : ℝ) / 1.58 := by
  norm_num

theorem feed_thresh_R24 : (0.2 : ℝ) ≤ (0.77 : ℝ) / 1.58 := by
  norm_num

theorem feed_thresh_E07 : (0.1 : ℝ) ≤ (0.77 : ℝ) / 1.83 := by
  norm_num

theorem feed_thresh_BA04 : (0.08 : ℝ) ≤ (0.77 : ℝ) / 1.58 := by
  norm_num

/-- R35 threshold fails at 0.77 (needs 1.8328). OPEN. -/
theorem feed_open_R35 : (0.77 : ℝ) / (0.58 * 1.58) < (2 : ℝ) := by
  norm_num

/-- R25 threshold fails at 0.77 (needs 1.16). OPEN. -/
theorem feed_open_R25 : (0.77 : ℝ) / 0.58 < (2 : ℝ) := by
  norm_num

/-- E05 threshold fails at 0.77 (needs 0.87). OPEN. -/
theorem feed_open_E05 : (0.77 : ℝ) / 0.58 < (1.5 : ℝ) := by
  norm_num

/-- R36 threshold fails at 0.77 (needs 0.83). OPEN. -/
theorem feed_open_R36 : (0.77 : ℝ) / 0.83 < (1 : ℝ) := by
  norm_num

/-- R26 threshold fails at 0.77 (needs 0.83). OPEN. -/
theorem feed_open_R26 : (0.77 : ℝ) / 0.83 < (1 : ℝ) := by
  norm_num

/-- E06 threshold fails at 0.77 (needs 0.83). OPEN. -/
theorem feed_open_E06 : (0.77 : ℝ) / 0.83 < (1 : ℝ) := by
  norm_num

/-! ## Conditional feed implications (24): `0.77`-numerator hypothesis
explicitly undischarged; each pays the exact banked denominators by reference
to the matching `Door3GammaDisc.*_cond`. No floor is forced. -/

/-- R28 conditional feed (two-step `2.83 * 3.83`; numerator OPEN). -/
theorem feed_R28_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 5.25 : ℂ)) / 2) + 2)‖) :
    gammaFeed_R28_ge := by
  unfold gammaFeed_R28_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R28 (Door3GammaDisc.R28_cond (0.77 : ℝ) h)

/-- R38 conditional feed (two-step `2.83 * 3.83`; numerator OPEN). -/
theorem feed_R38_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 5.25 : ℂ)) / 2) + 2)‖) :
    gammaFeed_R38_ge := by
  unfold gammaFeed_R38_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R38 (Door3GammaDisc.R38_cond (0.77 : ℝ) h)

/-- R29 conditional feed (two-step `3.83 * 4.83`; numerator OPEN). -/
theorem feed_R29_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 7.25 : ℂ)) / 2) + 2)‖) :
    gammaFeed_R29_ge := by
  unfold gammaFeed_R29_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R29 (Door3GammaDisc.R29_cond (0.77 : ℝ) h)

/-- E10 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_E10_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 8.75 : ℂ)) / 2) + 1)‖) :
    gammaFeed_E10_ge := by
  unfold gammaFeed_E10_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_E10 (Door3GammaDisc.E10_cond (0.77 : ℝ) h)

/-- BA00 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_BA00_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-8.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_BA00_ge := by
  unfold gammaFeed_BA00_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_BA00 (Door3GammaDisc.BA00_cond (0.77 : ℝ) h)

/-- R31 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_R31_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-8.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R31_ge := by
  unfold gammaFeed_R31_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R31 (Door3GammaDisc.R31_cond (0.77 : ℝ) h)

/-- R40 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_R40_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 8.75 : ℂ)) / 2) + 1)‖) :
    gammaFeed_R40_ge := by
  unfold gammaFeed_R40_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R40 (Door3GammaDisc.R40_cond (0.77 : ℝ) h)

/-- R21 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_R21_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-8.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R21_ge := by
  unfold gammaFeed_R21_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R21 (Door3GammaDisc.R21_cond (0.77 : ℝ) h)

/-- R30 conditional feed (`4.58`; numerator OPEN). -/
theorem feed_R30_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 8.75 : ℂ)) / 2) + 1)‖) :
    gammaFeed_R30_ge := by
  unfold gammaFeed_R30_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R30 (Door3GammaDisc.R30_cond (0.77 : ℝ) h)

/-- R39 conditional feed (`3.83`; numerator OPEN). -/
theorem feed_R39_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 7.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_R39_ge := by
  unfold gammaFeed_R39_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R39 (Door3GammaDisc.R39_cond (0.77 : ℝ) h)

/-- E09 conditional feed (`3.83`; numerator OPEN). -/
theorem feed_E09_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 7.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_E09_ge := by
  unfold gammaFeed_E09_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_E09 (Door3GammaDisc.E09_cond (0.77 : ℝ) h)

/-- R32 conditional feed (`3.58`; numerator OPEN). -/
theorem feed_R32_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-6.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R32_ge := by
  unfold gammaFeed_R32_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R32 (Door3GammaDisc.R32_cond (0.77 : ℝ) h)

/-- R22 conditional feed (`3.58`; numerator OPEN). -/
theorem feed_R22_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-6.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R22_ge := by
  unfold gammaFeed_R22_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R22 (Door3GammaDisc.R22_cond (0.77 : ℝ) h)

/-- E01 conditional feed (`3.33`; numerator OPEN). -/
theorem feed_E01_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-6.25) : ℂ)) / 2) + 1)‖) :
    gammaFeed_E01_ge := by
  unfold gammaFeed_E01_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_E01 (Door3GammaDisc.E01_cond (0.77 : ℝ) h)

/-- R33 conditional feed (`2.58`; numerator OPEN). -/
theorem feed_R33_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-4.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R33_ge := by
  unfold gammaFeed_R33_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R33 (Door3GammaDisc.R33_cond (0.77 : ℝ) h)

/-- R23 conditional feed (`2.58`; numerator OPEN). -/
theorem feed_R23_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-4.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R23_ge := by
  unfold gammaFeed_R23_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R23 (Door3GammaDisc.R23_cond (0.77 : ℝ) h)

/-- E08 conditional feed (`2.83`; numerator OPEN). -/
theorem feed_E08_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 5.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_E08_ge := by
  unfold gammaFeed_E08_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_E08 (Door3GammaDisc.E08_cond (0.77 : ℝ) h)

/-- BA03 conditional feed (`2.58`; numerator OPEN). -/
theorem feed_BA03_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-4.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_BA03_ge := by
  unfold gammaFeed_BA03_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_BA03 (Door3GammaDisc.BA03_cond (0.77 : ℝ) h)

/-- R37 conditional feed (`1.83`; numerator OPEN). -/
theorem feed_R37_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 3.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_R37_ge := by
  unfold gammaFeed_R37_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R37 (Door3GammaDisc.R37_cond (0.77 : ℝ) h)

/-- R27 conditional feed (`1.83`; numerator OPEN). -/
theorem feed_R27_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 3.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_R27_ge := by
  unfold gammaFeed_R27_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R27 (Door3GammaDisc.R27_cond (0.77 : ℝ) h)

/-- R34 conditional feed (`1.58`; numerator OPEN). -/
theorem feed_R34_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.105 (-2.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R34_ge := by
  unfold gammaFeed_R34_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R34 (Door3GammaDisc.R34_cond (0.77 : ℝ) h)

/-- R24 conditional feed (`1.58`; numerator OPEN). -/
theorem feed_R24_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.2 (-2.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_R24_ge := by
  unfold gammaFeed_R24_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_R24 (Door3GammaDisc.R24_cond (0.77 : ℝ) h)

/-- E07 conditional feed (`1.83`; numerator OPEN). -/
theorem feed_E07_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 3.25 : ℂ)) / 2) + 1)‖) :
    gammaFeed_E07_ge := by
  unfold gammaFeed_E07_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_E07 (Door3GammaDisc.E07_cond (0.77 : ℝ) h)

/-- BA04 conditional feed (`1.58`; numerator OPEN). -/
theorem feed_BA04_of_shift
    (h : (0.77 : ℝ) ≤ ‖Complex.Gamma ((((Complex.mk 0.395 (-2.75) : ℂ)) / 2) + 1)‖) :
    gammaFeed_BA04_ge := by
  unfold gammaFeed_BA04_ge
  unfold DerivCauchyBridge.gammaOf
  exact le_trans feed_thresh_BA04 (Door3GammaDisc.BA04_cond (0.77 : ℝ) h)

/-! ## Discharge record + remainder (honest split).

LOWERS CLOSED unconditionally: 0 of 30. No `premGamma_*_ge` is discharged
unconditionally here: every `feed_*_of_shift` above keeps its complex numerator
hypothesis `0.77 ≤ ‖Γ(w+k)‖` explicitly undischarged, and the 6 open centers
(R35, R25, E05, R36, R26, E06) have no implication at all at `c = 0.77`.
CLOSED here instead:
* `feed_gammaOf_eq` (`gammaOf` unfold by `rfl`) + `feed_real_77_sample`
  (banked `gamma_low_77` restated so the 0.77 source is used, not just quoted);
* 30 mirror Props `gammaFeed_*_ge`, each recording which `premGamma_*_ge` it
  discharges by restatement (premise file not imported, lane stays
  one-directional);
* 24 threshold arithmetics `feed_thresh_*` (`F ≤ 0.77 / M`, all by `norm_num`);
* 6 threshold failures `feed_open_*` (`0.77 / M < F`, all by `norm_num`);
* 24 conditional implications `feed_*_of_shift` (threshold + exact
  `Door3GammaDisc.*_cond` by reference, denominators never reproved).
DENOMINATORS: all by reference to `Door3GammaLow.*_w_norm_le` via the disc
conditionals (34 factors total, none reproved).
FALSE FLOORS: none declared false. All 30 floors sit below the TRUE Stirling
estimates quoted in the disc file, so each deficit is negative.
REMAINDER (re-tier lane for the 6 + numerator lane for all 30):
* All 30 unconditional lowers stay open. What blocks them: no sound
  real→complex numerator bridge exists — `D3SG_Gamma_norm_le_real` is an upper,
  and the shifted points have `|Im| > 0`, so `gamma_low_77` cannot be
  transferred; at large `|Im|` the claim `0.77 ≤ ‖Γ(w+k)‖` is additionally
  numerically false (shifted-TRUE headroom negative, e.g. E10 shifted TRUE
  `~0.001`). Required: explicit Stirling-disc enclosures at the shifted points
  (complex numerator lowers), or the `π/2`-rate lane plus a real lower on
  `[1,2]` for the low-`|Im|` centers only.
* The 6 non-feedable (R35 needs 1.8328, R25 needs 1.16, E05 needs 0.87,
  R36/R26/E06 need 0.83 — all above 0.77) stay in the re-tier lane: even a
  sound 0.77 complex bridge would not feed them. At the full 0.88 target, E05
  and R36/R26/E06 would become conditionally feedable; R35 and R25 stay open
  regardless (re-tier/subdivision lane, consistent with the premise
  feasibility audit).
-/

end Door3GammaFeed
