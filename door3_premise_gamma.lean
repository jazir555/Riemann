import Mathlib
import central_cover_assembly
import door3_stirling_gamma

/-!
# Door 3 gamma premises (premise-class wave 3 of 5).

Scope: gamma factor across the 40 batch cells (batches A--E plus first-cell
lane). Two-sided need: center LOWERS `floor <= ‖gammaOf sCenter‖` (gate center
floors) and disc UPPERS `‖gammaOf s‖ <= cap` (feed ball-sup `C`).

Cycle safety (verified read-only before writing):
* `door3_stirling_gamma.lean:1` imports `Mathlib` only (no central import).
* `central_cover_assembly.lean:1-3` imports `Mathlib`, `riemann_hypothesis`,
  `rh_certificate_infra` (no door3 import).
* Hence `Mathlib + central_cover_assembly + door3_stirling_gamma` is a DAG;
  this file reuses `D3SG_*` caps instead of reproving them.

Recon (brief, read-only):
* `gammaOf s = Complex.Gamma (s / 2)` (`central_cover_assembly.lean:6334`).
* Row s-center `Re`: bottom 0.395 (batch A, batch E, first-cell R02),
  second row 0.3 (batch B R11-R20), third row 0.2 (batch D R21-R30),
  top row 0.105 (batch C R31-R40).
* `w = s / 2` has `Re` in `[0.0525, 0.1975]` at centers, inside Tier-C wide
  strip `[0.005, 0.95]`; hence `D3SG_TierC_gamma_wide` applies at every center.
* Center lower floors / TRUE (Stirling) from batches A/C/D/E headers:
  BA00 0.0015, BA03 0.015, BA04 0.08;
  R31 0.001 (~0.00134), R32 0.006 (~0.00725), R33 0.032 (~0.0408),
  R34 0.2 (~0.25), R35 2 (~2.16), R36 1 (~1.16), R37 0.12 (~0.157),
  R38 0.024 (~0.0262), R39 0.004 (~0.00472), R40 0.001 (~0.00134);
  R21 0.001 (~0.00143), R22 0.006 (~0.00769), R23 0.032 (~0.0426),
  R24 0.2 (~0.254), R25 2 (~5.0), R26 1 (~1.5), R27 0.12 (~0.161),
  R28 0.026 (~0.0274), R29 0.0045 (~0.00504), R30 0.001 (~0.00143);
  E01 0.01 (~0.013), E05 1.5 (~4.4), E06 1 (~2.5), E07 0.1 (~0.169),
  E08 0.02 (~0.03), E09 0.0045 (~0.0057), E10 0.0015 (~0.00166);
  Batch B R11-R20 carry center premises (no factor split), first-cell R02
  lower 0.006 is banked (`FC_gamma0006_proved`).
* Disc upper obligations (example `R31_gamma_upper_obligation`): `<= 10` on
  `s.re in [0.001, 0.21]`, `s.im in [-10.01, -7.49]`; TRUE sup is `O(0.01)` by
  Im-decay. Tier-C wide gives `600 * exp` (~90 at `|w.im| ~ 3.7`), so the
  `<= 10` disc caps need the tighter local-M lane below, not just wide reuse.

Split delivery (honest): LOWERS first (shift infra + obligations + audit),
then UPPERS (wide reuse closed at all 40 centers). Tight disc `<= 10` caps
and quantitative complex-Gamma lowers need the next wave (explicit
Stirling-disc computation); nothing is forced here.

Line budget: well under 1400.
-/

noncomputable section

namespace Door3PremiseGamma

/-! ## Lower lane: one-step shift identity (mirrors CHI-neg shift). -/

/-- Norm shift identity for one step up (reproved from `Gamma_add_one`
at `w /= 0`; the in-file `D3SG_gamma_shift_norm` needs `0 < Re`, so the
single step here covers the low-sigma centers directly). -/
theorem premGamma_shift_norm_one (w : ℂ) (hw : w ≠ 0) :
    ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
  have hG : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw
  rw [hG, norm_mul]

/-- Lower via shift: upper on `‖w‖` plus lower on `‖Gamma (w+1)‖` gives a
lower on `‖Gamma w‖`. Next wave supplies the numerator lowers at shifted
`Re`; this wave banks the implication once and for all. -/
theorem premGamma_shift_lower (w : ℂ) (hw : w ≠ 0) (c : ℝ) (M : ℝ)
    (hc : c ≤ ‖Complex.Gamma (w + 1)‖) (hM : ‖w‖ ≤ M) (hMpos : 0 < M) :
    c / M ≤ ‖Complex.Gamma w‖ := by
  have hEq : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ :=
    premGamma_shift_norm_one w hw
  have hnn : 0 ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have h1 : c ≤ M * ‖Complex.Gamma w‖ :=
    le_trans hc (mul_le_mul_of_nonneg_right hM hnn)
  exact (le_div_iff₀ hMpos).mpr h1

/-! ## Lower obligations (per center, open; floors from batch headers). -/

def premGamma_BA00_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-8.75))‖

def premGamma_BA03_ge : Prop :=
  (0.015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-4.75))‖

def premGamma_BA04_ge : Prop :=
  (0.08 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-2.75))‖

def premGamma_R31_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-8.75))‖

def premGamma_R32_ge : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-6.75))‖

def premGamma_R33_ge : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-4.75))‖

def premGamma_R34_ge : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-2.75))‖

def premGamma_R35_ge : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-0.75))‖

def premGamma_R36_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 1.25)‖

def premGamma_R37_ge : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 3.25)‖

def premGamma_R38_ge : Prop :=
  (0.024 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 5.25)‖

def premGamma_R39_ge : Prop :=
  (0.004 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 7.25)‖

def premGamma_R40_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 8.75)‖

def premGamma_R21_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-8.75))‖

def premGamma_R22_ge : Prop :=
  (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-6.75))‖

def premGamma_R23_ge : Prop :=
  (0.032 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-4.75))‖

def premGamma_R24_ge : Prop :=
  (0.2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-2.75))‖

def premGamma_R25_ge : Prop :=
  (2 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-0.75))‖

def premGamma_R26_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 1.25)‖

def premGamma_R27_ge : Prop :=
  (0.12 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 3.25)‖

def premGamma_R28_ge : Prop :=
  (0.026 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 5.25)‖

def premGamma_R29_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 7.25)‖

def premGamma_R30_ge : Prop :=
  (0.001 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 8.75)‖

def premGamma_E01_ge : Prop :=
  (0.01 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-6.25))‖

def premGamma_E05_ge : Prop :=
  (1.5 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-0.75))‖

def premGamma_E06_ge : Prop :=
  (1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 1.25)‖

def premGamma_E07_ge : Prop :=
  (0.1 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 3.25)‖

def premGamma_E08_ge : Prop :=
  (0.02 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 5.25)‖

def premGamma_E09_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 7.25)‖

def premGamma_E10_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 8.75)‖

/-! ## Feasibility audit (pure arithmetic; feasibility-negative cells stay
open and must be re-tiered or subdivided, never forced). -/

/-- R31 TRUE-scale product below budget: `30 * 0.5 * 0.001 * 1 < budget`. -/
theorem premGamma_R31_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by
  norm_num

/-- R32 TRUE-scale product below budget. -/
theorem premGamma_R32_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.006 * 1 < (0.002 : ℝ) + 0.07 * 1.26 := by
  norm_num

/-- R39 TRUE-scale product below budget. -/
theorem premGamma_R39_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.004 * 1 < (0.002 : ℝ) + 0.07 * 1.26 := by
  norm_num

/-- R40 TRUE-scale product below budget. -/
theorem premGamma_R40_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by
  norm_num

/-- R21 TRUE-scale product below budget. -/
theorem premGamma_R21_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by
  norm_num

/-- R30 TRUE-scale product below budget. -/
theorem premGamma_R30_threshold_negative :
    (30 : ℝ) * (1 / 2) * 0.001 * 1 < (0.002 : ℝ) + 0.05 * 1.26 := by
  norm_num

/-- R22 threshold closes at stated floors (conditional feasibility). -/
theorem premGamma_R22_threshold_ok :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ 30 * (1 / 2) * 0.006 * 1 := by
  norm_num

/-- R28 threshold closes at stated floors (tight conditional). -/
theorem premGamma_R28_threshold_ok :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ 30 * (1 / 2) * 0.026 * 1 := by
  norm_num

/-! ## Upper lane: wide reuse (closed at all 40 centers). -/

/-- Generic wide upper for `gammaOf`: at `s.re in [0.01, 1.9]` the half-point
`w = s / 2` lies in Tier-C wide strip `[0.005, 0.95]`, so the banked
`D3SG_TierC_gamma_wide` bound applies directly. -/
theorem premGamma_wide_of_mem (s : ℂ) (hlo : (0.01 : ℝ) ≤ s.re)
    (hhi : s.re ≤ (1.9 : ℝ)) :
    ‖DerivCauchyBridge.gammaOf s‖ ≤
      600 * Real.exp (-(1 / 2) * |(s / 2).im|) := by
  unfold DerivCauchyBridge.gammaOf
  have h2re : (s / 2).re = s.re / 2 := by
    rw [Complex.div_ofNat_re]
  have hlo2 : (0.005 : ℝ) ≤ (s / 2).re := by
    rw [h2re]
    linarith
  have hhi2 : (s / 2).re ≤ (0.95 : ℝ) := by
    rw [h2re]
    linarith
  exact D3SG_TierC_gamma_wide (s / 2) hlo2 hhi2

/-- Local-M sigma-split wrapper around `D3SG_decay_sigma`: same `sigma`,
smaller `M` gives `3 * M * exp` at the half-point. Next wave instantiates
this with row-local real-Gamma caps tighter than the uniform `20 / 200`. -/
theorem premGamma_decay_of_mem (s : ℂ) (sig : ℝ) (M : ℝ)
    (hsig : 0 < sig) (hsig1 : sig ≤ 1) (hre : (s / 2).re = sig)
    (hM : 0 ≤ M) (hcap : Real.Gamma sig ≤ M) :
    ‖DerivCauchyBridge.gammaOf s‖ ≤
      3 * M * Real.exp (-(1 / 2) * |(s / 2).im|) := by
  unfold DerivCauchyBridge.gammaOf
  exact D3SG_decay_sigma (s / 2) sig M hsig hsig1 hre hM hcap

/-! ### Per-center wide uppers (40 cells; batch-B centers included for
completeness although batch B carries no factor-split gamma premise). -/

theorem premGamma_BA00_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-8.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-8.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 (-8.75)).re
    rw [show (Complex.mk (0.395 : ℝ) (-8.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 (-8.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (-8.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_BA03_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-4.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-4.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 (-4.75)).re
    rw [show (Complex.mk (0.395 : ℝ) (-4.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 (-4.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (-4.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_BA04_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-2.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-2.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 (-2.75)).re
    rw [show (Complex.mk (0.395 : ℝ) (-2.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 (-2.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (-2.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_B11_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 (-8.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 (-8.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 (-8.75)).re
    rw [show (Complex.mk (0.3 : ℝ) (-8.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 (-8.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (-8.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B12_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 (-6.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 (-6.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 (-6.75)).re
    rw [show (Complex.mk (0.3 : ℝ) (-6.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 (-6.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (-6.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B13_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 (-4.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 (-4.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 (-4.75)).re
    rw [show (Complex.mk (0.3 : ℝ) (-4.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 (-4.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (-4.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B14_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 (-2.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 (-2.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 (-2.75)).re
    rw [show (Complex.mk (0.3 : ℝ) (-2.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 (-2.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (-2.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B15_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 (-0.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 (-0.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 (-0.75)).re
    rw [show (Complex.mk (0.3 : ℝ) (-0.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 (-0.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (-0.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B16_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 1.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 1.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 1.25).re
    rw [show (Complex.mk (0.3 : ℝ) (1.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 1.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (1.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B17_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 3.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 3.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 3.25).re
    rw [show (Complex.mk (0.3 : ℝ) (3.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 3.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (3.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B18_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 5.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 5.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 5.25).re
    rw [show (Complex.mk (0.3 : ℝ) (5.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 5.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (5.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B19_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 7.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 7.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 7.25).re
    rw [show (Complex.mk (0.3 : ℝ) (7.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 7.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (7.25 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_B20_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.3 8.75)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.3 8.75 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.3 8.75).re
    rw [show (Complex.mk (0.3 : ℝ) (8.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.3 8.75).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.3 : ℝ) (8.75 : ℝ)).re = (0.3 : ℝ) from rfl]
    norm_num

theorem premGamma_R31_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-8.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 (-8.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 (-8.75)).re
    rw [show (Complex.mk (0.105 : ℝ) (-8.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 (-8.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (-8.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R32_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-6.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 (-6.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 (-6.75)).re
    rw [show (Complex.mk (0.105 : ℝ) (-6.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 (-6.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (-6.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R33_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-4.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 (-4.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 (-4.75)).re
    rw [show (Complex.mk (0.105 : ℝ) (-4.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 (-4.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (-4.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R34_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-2.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 (-2.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 (-2.75)).re
    rw [show (Complex.mk (0.105 : ℝ) (-2.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 (-2.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (-2.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R35_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 (-0.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 (-0.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 (-0.75)).re
    rw [show (Complex.mk (0.105 : ℝ) (-0.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 (-0.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (-0.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R36_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 1.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 1.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 1.25).re
    rw [show (Complex.mk (0.105 : ℝ) (1.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 1.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (1.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R37_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 3.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 3.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 3.25).re
    rw [show (Complex.mk (0.105 : ℝ) (3.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 3.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (3.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R38_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 5.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 5.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 5.25).re
    rw [show (Complex.mk (0.105 : ℝ) (5.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 5.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (5.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R39_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 7.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 7.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 7.25).re
    rw [show (Complex.mk (0.105 : ℝ) (7.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 7.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (7.25 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R40_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.105 8.75)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.105 8.75 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.105 8.75).re
    rw [show (Complex.mk (0.105 : ℝ) (8.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.105 8.75).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.105 : ℝ) (8.75 : ℝ)).re = (0.105 : ℝ) from rfl]
    norm_num

theorem premGamma_R21_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-8.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 (-8.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 (-8.75)).re
    rw [show (Complex.mk (0.2 : ℝ) (-8.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 (-8.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (-8.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R22_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-6.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 (-6.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 (-6.75)).re
    rw [show (Complex.mk (0.2 : ℝ) (-6.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 (-6.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (-6.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R23_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-4.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 (-4.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 (-4.75)).re
    rw [show (Complex.mk (0.2 : ℝ) (-4.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 (-4.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (-4.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R24_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-2.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 (-2.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 (-2.75)).re
    rw [show (Complex.mk (0.2 : ℝ) (-2.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 (-2.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (-2.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R25_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 (-0.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 (-0.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 (-0.75)).re
    rw [show (Complex.mk (0.2 : ℝ) (-0.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 (-0.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (-0.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R26_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 1.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 1.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 1.25).re
    rw [show (Complex.mk (0.2 : ℝ) (1.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 1.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (1.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R27_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 3.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 3.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 3.25).re
    rw [show (Complex.mk (0.2 : ℝ) (3.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 3.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (3.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R28_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 5.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 5.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 5.25).re
    rw [show (Complex.mk (0.2 : ℝ) (5.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 5.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (5.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R29_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 7.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 7.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 7.25).re
    rw [show (Complex.mk (0.2 : ℝ) (7.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 7.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (7.25 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_R30_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.2 8.75)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.2 8.75 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.2 8.75).re
    rw [show (Complex.mk (0.2 : ℝ) (8.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.2 8.75).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.2 : ℝ) (8.75 : ℝ)).re = (0.2 : ℝ) from rfl]
    norm_num

theorem premGamma_E01_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-6.25))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-6.25) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 (-6.25)).re
    rw [show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 (-6.25)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E05_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-0.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-0.75) : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 (-0.75)).re
    rw [show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 (-0.75)).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E06_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 1.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 1.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 1.25).re
    rw [show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 1.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E07_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 3.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 3.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 3.25).re
    rw [show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 3.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E08_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 5.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 5.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 5.25).re
    rw [show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 5.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E09_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 7.25)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 7.25 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 7.25).re
    rw [show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 7.25).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

theorem premGamma_E10_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 8.75)‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 8.75 : ℂ) / 2).im|) := by
  apply premGamma_wide_of_mem
  · show (0.01 : ℝ) ≤ (Complex.mk 0.395 8.75).re
    rw [show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num
  · show (Complex.mk 0.395 8.75).re ≤ (1.9 : ℝ)
    rw [show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl]
    norm_num

/-! ## Remainder (honest split for the next wave).

LOWERS: all 30 center floors above remain open as `Prop` obligations
(`premGamma_*_ge`); the shift lemmas `premGamma_shift_norm_one` and
`premGamma_shift_lower` bank the recurrence step, and the feasibility audit
above separates conditional cells (R22, R28 close thresholds) from
feasibility-negative cells (R31, R32, R39, R40, R21, R30 need re-tiering or
subdivision). No floor is forced: tight cells R28 (1.05x), R29 (1.12x),
R38 (1.09x), R35 (1.08x) need explicit Stirling-disc enclosures.
UPPERS: wide `600 * exp` closed at all 40 centers above via
`D3SG_TierC_gamma_wide` reuse; the tight disc caps `<= 10`
(`R31_gamma_upper_obligation` family) remain open and will use
`premGamma_decay_of_mem` with row-local real-Gamma caps plus the
`D3SG_CHI_Gamma_upper_neg` shift pattern for the `Re < 0.005` sliver.
Batch B R11-R20 need no factor-split gamma premise; their wide uppers are
banked here for completeness. First-cell R02 gamma lower 0.006 stays banked.
-/

/-! ## E05 shift-conditional closure (closed implication; numerator open).

`premGamma_E05_ge` (floor 1.5, TRUE ~4.4) via the shift-lower leg
`premGamma_shift_lower` plus an explicit numeral upper on the recurrence
denominator `‖w_E05‖ ≤ 0.43` (the wide-upper-style leg). The remaining open
numeral premise `0.645 ≤ ‖Gamma (w_E05 + 1)‖` (with `0.645 / 0.43 = 1.5`)
needs the next-wave Stirling-disc enclosure: banked routes fall short
(`lower_inner` / `inner_big` in `door3_complex_wendel.lean` give `0.38`-scale;
`feed_open_E05` in `door3_gamma_feed.lean` gives `1.33`-scale `< 1.5`).
Nothing is forced: the absolute floor stays open.

Feasibility-negative cells (NOT attempted here; stay open `Prop`s with the
`threshold_negative` audits above): R31, R32, R39, R40, R21, R30.
-/

/-- Recurrence denominator upper at E05: `‖s_E05 / 2‖ ≤ 0.43`
(TRUE `≈ 0.4238`). -/
theorem premGamma_E05_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)‖ ≤ (0.43 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)).im
      = (((-0.75 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = ((-0.75 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (0.43 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (0.43 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 shift conditional: the shift-lower leg closes `premGamma_E05_ge`
once the shifted numerator lower `0.645 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.645 / 0.43 = 1.5`). -/
theorem premGamma_E05_ge_of_shift
    (hnum : (0.645 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E05_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2)
    hw 0.645 0.43 hnum premGamma_E05_wnorm_le (by norm_num)
  have heq : (0.645 : ℝ) / 0.43 = 1.5 := by norm_num
  rw [heq] at h
  unfold premGamma_E05_ge DerivCauchyBridge.gammaOf
  exact h

/-- E05 product threshold closes at stated floors
(mirrors `BE_R05_threshold_check` in `door3_cells_batchE.lean`:
`0.35*0.7*1.5*1.0 = 0.3675 ≥ 0.15+0.06*1.26 = 0.2256`). -/
theorem premGamma_E05_threshold_ok :
    (0.15 : ℝ) + 0.06 * 1.26 ≤ (0.35 : ℝ) * 0.7 * 1.5 * 1 := by
  norm_num

/-! ## E06 shift-conditional closure (same pattern; numerator open).

`premGamma_E06_ge` (floor 1.0, TRUE ~2.5) via `premGamma_shift_lower` with
`‖w_E06‖ ≤ 0.66` (`0.66 / 0.66 = 1.0`). The wide upper leg is already banked
as `premGamma_E06_le`. The open numeral premise `0.66 ≤ ‖Gamma (w+1)‖`
needs the next-wave enclosure (`feed_open_E06` in `door3_gamma_feed.lean`
records the feed route shortfall). Not attempted: R31/R32/R39/R40, R21/R30.
-/

/-- Recurrence denominator upper at E06: `‖s_E06 / 2‖ ≤ 0.66`
(TRUE `≈ 0.6555`). -/
theorem premGamma_E06_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)‖ ≤ (0.66 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)).im
      = (((1.25 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = ((1.25 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (0.66 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (0.66 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 shift conditional: the shift-lower leg closes `premGamma_E06_ge`
once the shifted numerator lower `0.66 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.66 / 0.66 = 1`). -/
theorem premGamma_E06_ge_of_shift
    (hnum : (0.66 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E06_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2)
    hw 0.66 0.66 hnum premGamma_E06_wnorm_le (by norm_num)
  have heq : (0.66 : ℝ) / 0.66 = 1 := by norm_num
  rw [heq] at h
  unfold premGamma_E06_ge DerivCauchyBridge.gammaOf
  exact h

/-! ## E07 shift-conditional closure (same pattern; numerator open).

`premGamma_E07_ge` (floor 0.1, TRUE ~0.169) via `premGamma_shift_lower` with
`‖w_E07‖ ≤ 1.64` (TRUE `≈ 1.6370`; `0.164 / 1.64 = 0.1`). Cell choice: the
premise list `:26-37` carries E-row `E01 / E05 / E06 / E07 / E08 / E09 / E10`
(no `E04` def exists), so `E07` is the nearest uncovered floor adjacent to
banked `E06`. The wide upper leg is already banked as `premGamma_E07_le`.
The open numeral premise `0.164 ≤ ‖Gamma (w+1)‖` needs the next-wave
Stirling-disc enclosure at `w + 1 = 1.1975 + 1.625i`
(estimated `≈ 1.637 * 0.169 ≈ 0.276`, so `0.164` has ~1.68x headroom).
Numerals Python-checked: `|w|^2 = 2.67963125 ≤ 1.64^2 = 2.6896`.
-/

/-- Recurrence denominator upper at E07: `‖s_E07 / 2‖ ≤ 1.64`
(TRUE `≈ 1.6370`). -/
theorem premGamma_E07_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)‖ ≤ (1.64 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)).im
      = (((3.25 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).im = ((3.25 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (1.64 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (1.64 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E07 shift conditional: the shift-lower leg closes `premGamma_E07_ge`
once the shifted numerator lower `0.164 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.164 / 1.64 = 0.1`). -/
theorem premGamma_E07_ge_of_shift
    (hnum : (0.164 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E07_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2)
    hw 0.164 1.64 hnum premGamma_E07_wnorm_le (by norm_num)
  have heq : (0.164 : ℝ) / 1.64 = 0.1 := by norm_num
  rw [heq] at h
  unfold premGamma_E07_ge DerivCauchyBridge.gammaOf
  exact h

/-- E07 product threshold closes at stated floors
(mirrors `BE_R07_threshold_check` in `door3_cells_batchE.lean`:
`5*0.7*0.1*1.0 = 0.35 ≥ 0.05+0.07*1.26 = 0.1382`). -/
theorem premGamma_E07_threshold_ok :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (5 : ℝ) * 0.7 * 0.1 * 1 := by
  norm_num

end Door3PremiseGamma
