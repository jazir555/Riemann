import Mathlib
import central_cover_assembly

/-!
# Door-3 direct tier-M derivative bounds (Leibniz + small-disc Cauchy arithmetic).

Write-only record. Imports are `Mathlib` + `central_cover_assembly` only.
No other file is imported. Every proof below is complete with explicit
binders where binders occur. The `norm_num` tactic is used only on `ℝ` / `ℕ`
goals. No shortcut rewriting tactic is used.

## Recon record (read-only, verified before writing)

* Leaf tiers live in `central_cover_assembly.lean` as `RXX_leaf_obligations`:
  second conjunct `∀ w, RXX.mem w → ‖deriv xiShifted w‖ ≤ M` with
  `M ∈ {0.05, 0.06, 0.07}`. Outer cells use `M = 0.05`
  (`R00 R10 R11 R20 R21 R30 R31 R40`); inner cells use `M = 0.06`
  (`R05 R06 R15 R16 R25 R26 R35 R36`); mid and outer-leaf cells use
  `M = 0.07` (`R01 R02 R03 R04 R07 R08 R09 R12 R13 R14 R17 R18 R19
  R22 R23 R24 R27 R28 R29 R32 R33 R34 R37 R38 R39`).
* Wide Cauchy gives `16800 / 0.25 = 67200` everywhere
  (`door3_premise_tier.lean`: 41 mismatch blocks, each with
  `premDeriv_RXX_of_ball : ball premise → ‖deriv‖ ≤ 67200` resting on
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` with `r = 0.25`).
  Since `0.05 < 67200`, `0.06 < 67200`, `0.07 < 67200`, no tier follows.
* Representative batch cell `R28` (`door3_cells_batchD.lean`, near `R28 =`
  section): `BD_derivTier_R28 : ∀ w, mem w → ‖deriv xiShifted w‖ ≤ 0.07`,
  `BD_ballSup_R28` on `closedBall center (radius + 0.25)`,
  `BD_R28_radius_lt : radius < 1.26`, center `R28.center`, and the four-part
  center floors (poly `11`, pi `1 / 2`, gamma `0.026`, zeta `1`) with
  threshold `0.05 + 0.07 * 1.26 ≤ 11 * (1 / 2) * 0.026 * 1`.
* Four-factor shape (`central_cover_assembly.lean`, `DerivCauchyBridge`):
  `xiShifted z = polyOf s * piOf s * gammaOf s * zeta s` with
  `s = 1 / 2 + I * z` (`xiShifted_eq_parts`, `norm_xiShifted_eq_parts`).

## Method recorded here (direct, honest numbers)

* Leibniz combination: for factor sups `Aa Ab Ac Ad` and factor-deriv sups
  `Da Db Dc Dd`, the product-derivative combination is
  `Da*Ab*Ac*Ad + Aa*Db*Ac*Ad + Aa*Ab*Dc*Ad + Aa*Ab*Ac*Dd`
  (`leibnizComb` below). A tier follows only if that total is `≤ tier`
  (`leibniz_tier_sufficient`). No factor-deriv sups are banked here, so no
  tier is forced through this route in this file.
* Small-disc Cauchy scale: with `ρC = 0.01`, rate `C / ρC` gives
  `1 / 0.01 = 100` (optimistic `C = 1`) and `0.143 / 0.01 = 14.3`
  (R28-center-floor scale `11 * 0.5 * 0.026 * 1 = 0.143`). Both exceed every
  tier `0.05 / 0.06 / 0.07`. True local sups are `O(10)`, giving rates
  near `1000`, even further above.
* Ordering: biggest-margin first. Margin `= tier - 100` is least negative
  for tier `0.07` (`-99.93`), then `0.06` (`-99.94`), then `0.05`
  (`-99.95`). Hence `0.07` cells first, then `0.06`, then `0.05`.

## Verdict recorded here (numbers, not forced closures)

* Tiers closed via direct bounds in this file: 0 of 41.
* Tier gaps proved: 41 of 41 (each tier `< 100` and `< 14.3`).
* Remainder (not this file): per-center factor-deriv enclosures
  (poly exact, pi closed rpow form, gamma log-derivative, zeta strip
  pieces) plus subdivision / re-tier queue per cell.
-/

noncomputable section

namespace Door3TierDirect

open Complex Real Set Topology

/-! ## 1. Shared direct machine (Leibniz combination + small-disc rates). -/

/-- Four-factor Leibniz combination total. -/
def leibnizComb (Da Ab Ac Ad Aa Db Dc Dd : ℝ) : ℝ :=
  Da * Ab * Ac * Ad + Aa * Db * Ac * Ad + Aa * Ab * Dc * Ad + Aa * Ab * Ac * Dd

/-- Leibniz combination is nonneg from nonneg inputs. -/
theorem leibnizComb_nonneg (Da Ab Ac Ad Aa Db Dc Dd : ℝ)
    (hDa : 0 ≤ Da) (hAb : 0 ≤ Ab) (hAc : 0 ≤ Ac) (hAd : 0 ≤ Ad)
    (hAa : 0 ≤ Aa) (hDb : 0 ≤ Db) (hDc : 0 ≤ Dc) (hDd : 0 ≤ Dd) :
    0 ≤ leibnizComb Da Ab Ac Ad Aa Db Dc Dd := by
  unfold leibnizComb
  positivity

/-- Sufficient condition: a Leibniz total under the tier meets the tier. -/
theorem leibniz_tier_sufficient (Da Ab Ac Ad Aa Db Dc Dd tier : ℝ)
    (h : Da * Ab * Ac * Ad + Aa * Db * Ac * Ad + Aa * Ab * Dc * Ad +
      Aa * Ab * Ac * Dd ≤ tier) :
    Da * Ab * Ac * Ad + Aa * Db * Ac * Ad + Aa * Ab * Dc * Ad +
      Aa * Ab * Ac * Dd ≤ tier := by
  exact h

/-- Small-disc Cauchy closed forms (`ρC = 0.01`). -/
theorem direct_rate_opt : (1 : ℝ) / 0.01 = 100 := by
  norm_num

theorem direct_rate_tight : (0.143 : ℝ) / 0.01 = 14.3 := by
  norm_num

/-- R28-scale center-floor product (`11 * 0.5 * 0.026 * 1 = 0.143`). -/
theorem direct_center_floor_R28scale :
    (11 : ℝ) * (1 / 2) * 0.026 * 1 = 0.143 := by
  norm_num

/-- Shared tier gaps against the optimistic direct rate `100`. -/
theorem tier05_lt_100 : (0.05 : ℝ) < 100 := by
  norm_num

theorem tier06_lt_100 : (0.06 : ℝ) < 100 := by
  norm_num

theorem tier07_lt_100 : (0.07 : ℝ) < 100 := by
  norm_num

/-- Shared tier gaps against the tight-scale direct rate `14.3`. -/
theorem tier05_lt_1430 : (0.05 : ℝ) < 14.3 := by
  norm_num

theorem tier06_lt_1430 : (0.06 : ℝ) < 14.3 := by
  norm_num

theorem tier07_lt_1430 : (0.07 : ℝ) < 14.3 := by
  norm_num

/-- Shared negative margins (`tier - 100 < 0`). -/
theorem margin05_neg : (0.05 : ℝ) - 100 < 0 := by
  norm_num

theorem margin06_neg : (0.06 : ℝ) - 100 < 0 := by
  norm_num

theorem margin07_neg : (0.07 : ℝ) - 100 < 0 := by
  norm_num

/-! ## 2. Tier-0.07 cells first (biggest margin, `-99.93`). -/

def tierDirect_R01_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R01.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R01_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R01_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R02_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R02_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R02_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R03_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R03.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R03_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R03_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R04_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R04.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R04_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R04_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R07_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R07.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R07_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R07_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R08_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R08.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R08_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R08_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R09_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R09.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R09_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R09_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R12_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R12.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R12_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R12_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R13_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R13.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R13_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R13_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R14_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R14.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R14_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R14_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R17_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R17.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R17_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R17_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R18_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R18.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R18_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R18_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R19_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R19.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R19_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R19_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R22_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R22.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R22_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R22_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R23_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R23.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R23_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R23_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R24_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R24.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R24_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R24_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R27_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R27.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R27_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R27_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R28_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R28.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R28_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R28_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R29_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R29.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R29_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R29_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R32_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R32.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R32_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R32_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R33_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R33_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R33_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R34_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R34_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R34_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R37_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R37_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R37_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R38_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R38_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R38_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

def tierDirect_R39_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
theorem tierDirect_R39_gap : (0.07 : ℝ) < 100 :=
  tier07_lt_100
theorem tierDirect_R39_gap_tight : (0.07 : ℝ) < 14.3 :=
  tier07_lt_1430

/-! ## 3. Tier-0.06 cells (margin `-99.94`). -/

def tierDirect_R05_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R05.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R05_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R05_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R06_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R06.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R06_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R06_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R15_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R15.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R15_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R15_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R16_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R16.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R16_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R16_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R25_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R25.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R25_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R25_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R26_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R26.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R26_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R26_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R35_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R35_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R35_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

def tierDirect_R36_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
theorem tierDirect_R36_gap : (0.06 : ℝ) < 100 :=
  tier06_lt_100
theorem tierDirect_R36_gap_tight : (0.06 : ℝ) < 14.3 :=
  tier06_lt_1430

/-! ## 4. Tier-0.05 cells (margin `-99.95`). -/

def tierDirect_R00_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R00_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R00_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R10_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R10.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R10_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R10_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R11_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R11.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R11_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R11_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R20_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R20.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R20_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R20_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R21_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R21.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R21_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R21_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R30_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R30.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R30_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R30_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R31_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R31.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R31_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R31_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

def tierDirect_R40_le : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
theorem tierDirect_R40_gap : (0.05 : ℝ) < 100 :=
  tier05_lt_100
theorem tierDirect_R40_gap_tight : (0.05 : ℝ) < 14.3 :=
  tier05_lt_1430

end Door3TierDirect
