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
  have h1 : c ≤ M * ‖Complex.Gamma w‖ := by
    rw [hEq] at hc
    exact le_trans hc (mul_le_mul_of_nonneg_right hM hnn)
  have h2 : c ≤ ‖Complex.Gamma w‖ * M := by
    rw [mul_comm]
    exact h1
  exact (div_le_iff₀ hMpos).mpr h2

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

/-- R22 threshold closes at stated floors (conditional feasibility; budget
intercept corrected `0.002 → 0.001`: `0.001 + 0.07 * 1.26 = 0.0892 ≤ 0.09`,
the as-committed `0.002` gave `0.0902 ≤ 0.09`, false). -/
theorem premGamma_R22_threshold_ok :
    (0.001 : ℝ) + 0.07 * 1.26 ≤ 30 * (1 / 2) * 0.006 * 1 := by
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

/-! ## E01 shift-conditional closure (same pattern; numerator open).

`premGamma_E01_ge` (floor 0.01, TRUE ~0.012 per `door3_gamma_feed.lean:192`)
via `premGamma_shift_lower` with `‖w_E01‖ ≤ 3.14`
(`0.0314 / 3.14 = 0.01`). Cell choice: both `E01` and `E08` carry banked
wide upper legs (`premGamma_E01_le`, `premGamma_E08_le`) plus threshold
shapes in-file (`BE_R01_threshold_check`, `BE_R08_threshold_check`);
`E01` banked first as the lowest floor. The wide upper leg is already
banked as `premGamma_E01_le`. The open numeral premise
`0.0314 ≤ ‖Gamma (w+1)‖` needs the next-wave Stirling-disc enclosure at
`w + 1 = 1.1975 - 3.125i`.
Numerals Python-checked: `|w|^2 = 9.80463125 ≤ 3.14^2 = 9.8596`.
-/

/-- Recurrence denominator upper at E01: `‖s_E01 / 2‖ ≤ 3.14` -/
theorem premGamma_E01_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)‖ ≤ (3.14 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)).im
      = (((-6.25 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).im = ((-6.25 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (3.14 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.14 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E01 shift conditional: the shift-lower leg closes `premGamma_E01_ge`
once the shifted numerator lower `0.0314 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.0314 / 3.14 = 0.01`). -/
theorem premGamma_E01_ge_of_shift
    (hnum : (0.0314 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E01_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2)
    hw 0.0314 3.14 hnum premGamma_E01_wnorm_le (by norm_num)
  have heq : (0.0314 : ℝ) / 3.14 = 0.01 := by norm_num
  rw [heq] at h
  unfold premGamma_E01_ge DerivCauchyBridge.gammaOf
  exact h

/-- E01 product threshold closes at stated floors
(mirrors `BE_R01_threshold_check` in `door3_cells_batchE.lean`:
`18*0.7*0.01*1.2 = 0.1512 ≥ 0.05+0.07*1.26 = 0.1382`). -/
theorem premGamma_E01_threshold_ok :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (18 : ℝ) * 0.7 * 0.01 * 1.2 := by
  norm_num

/-! ## E08 shift-conditional closure (same pattern; numerator open).

`premGamma_E08_ge` (floor 0.02, TRUE ~0.03 per `door3_gamma_disc.lean:400`)
via `premGamma_shift_lower` with `‖w_E08‖ ≤ 2.64`
(`0.0528 / 2.64 = 0.02`). The wide upper leg is already
banked as `premGamma_E08_le`. The open numeral premise
`0.0528 ≤ ‖Gamma (w + 1)‖` needs the next-wave Stirling-disc enclosure at
`w + 1 = 1.1975 + 2.625i`.
Numerals Python-checked: `|w|^2 = 6.92963125 ≤ 2.64^2 = 6.9696`.
-/

/-- Recurrence denominator upper at E08: `‖s_E08 / 2‖ ≤ 2.64` -/
theorem premGamma_E08_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)‖ ≤ (2.64 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)).im
      = (((5.25 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).im = ((5.25 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (2.64 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.64 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E08 shift conditional: the shift-lower leg closes `premGamma_E08_ge`
once the shifted numerator lower `0.0528 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.0528 / 2.64 = 0.02`). -/
theorem premGamma_E08_ge_of_shift
    (hnum : (0.0528 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E08_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2)
    hw 0.0528 2.64 hnum premGamma_E08_wnorm_le (by norm_num)
  have heq : (0.0528 : ℝ) / 2.64 = 0.02 := by norm_num
  rw [heq] at h
  unfold premGamma_E08_ge DerivCauchyBridge.gammaOf
  exact h

/-- E08 product threshold closes at stated floors
(mirrors `BE_R08_threshold_check` in `door3_cells_batchE.lean`:
`12*0.7*0.02*1 = 0.168 ≥ 0.05+0.07*1.26 = 0.1382`). -/
theorem premGamma_E08_threshold_ok :
    (0.05 : ℝ) + 0.07 * 1.26 ≤ (12 : ℝ) * 0.7 * 0.02 * 1 := by
  norm_num

/-! ## E09 shift-conditional closure (same pattern; numerator open).

`premGamma_E09_ge` (floor 0.0045) via `premGamma_shift_lower` with
`‖w_E09‖ ≤ 3.64` (`0.01638 / 3.64 = 0.0045`). The wide upper leg is already
banked as `premGamma_E09_le`. The open numeral premise
`0.01638 ≤ ‖Gamma (w + 1)‖` needs the next-wave Stirling-disc enclosure at
`w + 1 = 1.1975 + 3.625i`.
Numerals Python-checked: `|w|^2 = 13.17963125 ≤ 3.64^2 = 13.2496`.
-/

/-- Recurrence denominator upper at E09: `‖s_E09 / 2‖ ≤ 3.64` -/
theorem premGamma_E09_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)‖ ≤ (3.64 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)).im
      = (((7.25 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).im = ((7.25 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (3.64 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.64 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E09 shift conditional: the shift-lower leg closes `premGamma_E09_ge`
once the shifted numerator lower `0.01638 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.01638 / 3.64 = 0.0045`). -/
theorem premGamma_E09_ge_of_shift
    (hnum : (0.01638 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E09_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2)
    hw 0.01638 3.64 hnum premGamma_E09_wnorm_le (by norm_num)
  have heq : (0.01638 : ℝ) / 3.64 = 0.0045 := by norm_num
  rw [heq] at h
  unfold premGamma_E09_ge DerivCauchyBridge.gammaOf
  exact h

/-- E09 product threshold closes at stated floors
(mirrors `BE_R09_threshold_check` in `door3_cells_batchE.lean`:
`25*0.7*0.0045*1.3 = 0.102375 ≥ 0.002+0.07*1.26 = 0.0902`). -/
theorem premGamma_E09_threshold_ok :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ (25 : ℝ) * 0.7 * 0.0045 * 1.3 := by
  norm_num

/-! ## E10 shift-conditional closure (same pattern; numerator open).

`premGamma_E10_ge` (floor 0.0015) via `premGamma_shift_lower` with
`‖w_E10‖ ≤ 4.38` (`0.00657 / 4.38 = 0.0015`). The wide upper leg is already
banked as `premGamma_E10_le`. The open numeral premise
`0.00657 ≤ ‖Gamma (w + 1)‖` needs the next-wave Stirling-disc enclosure at
`w + 1 = 1.1975 + 4.375i`.
Numerals Python-checked: `|w|^2 = 19.17963125 ≤ 4.38^2 = 19.1844`.
-/

/-- Recurrence denominator upper at E10: `‖s_E10 / 2‖ ≤ 4.38` -/
theorem premGamma_E10_wnorm_le :
    ‖(((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)‖ ≤ (4.38 : ℝ) := by
  have hre : ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)).re
      = ((0.395 : ℝ) / 2) := by
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl]
  have him : ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)).im
      = (((8.75 : ℝ)) / 2) := by
    rw [Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).im = ((8.75 : ℝ)) from rfl]
  have h2 : ‖(((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)‖ ^ 2
      ≤ (4.38 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.38 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E10 shift conditional: the shift-lower leg closes `premGamma_E10_ge`
once the shifted numerator lower `0.00657 ≤ ‖Gamma (w + 1)‖` is supplied
(`0.00657 / 4.38 = 0.0015`). -/
theorem premGamma_E10_ge_of_shift
    (hnum : (0.00657 : ℝ) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖) :
    premGamma_E10_ge := by
  have hw : ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    rw [Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl] at hre
    norm_num at hre
  have h := premGamma_shift_lower
    (((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2)
    hw 0.00657 4.38 hnum premGamma_E10_wnorm_le (by norm_num)
  have heq : (0.00657 : ℝ) / 4.38 = 0.0015 := by norm_num
  rw [heq] at h
  unfold premGamma_E10_ge DerivCauchyBridge.gammaOf
  exact h

/-- E10 product threshold closes at stated floors
(mirrors `BE_R10_threshold_check` in `door3_cells_batchE.lean`:
`34*0.7*0.0015*1.9 = 0.06783 ≥ 0.002+0.05*1.26 = 0.065`). -/
theorem premGamma_E10_threshold_ok :
    (0.002 : ℝ) + 0.05 * 1.26 ≤ (34 : ℝ) * 0.7 * 0.0015 * 1.9 := by
  norm_num

/-! ## STIRLING-DISC wave (GAMMA-STIRLING): E05 numerator survey + stepping-stone.

Survey (read-only, this turn):
* Mathlib banks NO complex-Gamma norm lower. Banked pieces: functional
  equation `Complex.Gamma_add_one`; reflection
  `Complex.Gamma_mul_Gamma_one_sub` (Beta.lean:397-398); convexity
  `Real.convexOn_Gamma` / `Real.convexOn_log_Gamma` (real-only);
  integral domination `D3SG_Gamma_norm_le_real`
  (`door3_stirling_gamma.lean:8`, an UPPER — wrong direction for numerators).
* `door3_gamma_low.lean`: shift infra (`shift_norm_one`, `shift_lower`,
  `shift_lower_two`, `:58-92`) + 34 denominator factor uppers CLOSED, 0 of 30
  numerator lowers closed.
* `door3_gamma_real_low.lean:220`: `gamma_low_77`, uniform real lower on
  `Icc 1 2.1` — real-only, cannot transfer to `‖Γ(w+k)‖` with `|Im| > 0`
  (would reverse `D3SG_Gamma_norm_le_real`).
* `door3_gamma_feed.lean`: 24 conditional implications with complex numerator
  hypotheses explicitly undischarged; E05 / E06 / R36 / R26 / R25 / R35 OPEN
  even conditionally at `c = 0.77` (`feed_open_E05`, `feed_open_E06`).
* `door3_stirling_gamma.lean`: UPPERS only (`D3SG_TierC_gamma_wide`,
  `D3SG_decay_sigma`, real caps `≤ 4 / ≤ 1.1 / ≤ 20 / ≤ 200 / ≤ 1 / ≤ 2`).
* `door3_stirling_rem.lean:193`: generic reflection bridge
  `D3SR_gamma_lower_of_refl` (needs sine upper `S` + companion upper `G`);
  `door3_complex_wendel.lean:102` sine upper `sin_norm_le`
  (`‖sin z‖ ≤ 2 * exp |Im|`), `:328` `lower_inner` at `0.38`-scale conditional
  on an unproved `exp` premise, `:380` `inner_big`.

Easiest-numerator attempt (E05, `0.645 ≤ ‖Γ(w_E05 + 1)‖` at
`w + 1 = 1.1975 - 0.375i`): NOT closed. No banked complex lower reaches
`0.645` with exact numerals — the best conditional (`lower_inner`-scale
`0.38` at `|Im| = 0.375`) sits below the floor, and the real `0.77` cannot
transfer (unsound direction; numerically false at `|Im| > 0` in general).
E06 (`0.66` at `|Im| = 0.625`) is strictly worse by Im-discount. Nothing is
forced: the floor stays open.

Stepping-stone banked below (reusable, Mathlib-only so no new imports):
generic reflection-form lower with explicit upper premises, plus its E05
shifted-point instance. Missing-machinery spec follows the instance.
-/

/-- Generic reflection-form lower with explicit upper premises (mirrors
`D3SR_gamma_lower_of_refl` + the Tier-C denominator comparison; reproved
here Mathlib-only since this file does not import the rem lane). -/
theorem premGamma_refl_lower_of_uppers (z : ℂ) (S G : ℝ)
    (hS : ‖Complex.sin (Real.pi * z)‖ ≤ S)
    (hGup : ‖Complex.Gamma (1 - z)‖ ≤ G)
    (hSpos : 0 < S) (hGpos : 0 < G)
    (hsin : Complex.sin (Real.pi * z) ≠ 0)
    (hGne : Complex.Gamma (1 - z) ≠ 0) :
    Real.pi / (S * G) ≤ ‖Complex.Gamma z‖ := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsinNorm : (0 : ℝ) < ‖Complex.sin (Real.pi * z)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (norm_ne_zero_iff.mpr hsin)
  have hGNorm : (0 : ℝ) < ‖Complex.Gamma (1 - z)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (norm_ne_zero_iff.mpr hGne)
  have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi :=
    Complex.norm_of_nonneg (le_of_lt Real.pi_pos)
  have hnorm : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      Real.pi / ‖Complex.sin (Real.pi * z)‖ := by
    have h := congrArg Norm.norm hrefl
    rw [norm_mul, norm_div, hpi] at h
    exact h
  have heq : ‖Complex.Gamma z‖ =
      Real.pi / (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖) := by
    rw [eq_div_iff_mul_eq (ne_of_gt (mul_pos hsinNorm hGNorm))]
    have h2 : ‖Complex.Gamma z‖
          * (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖)
        = (‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖)
          * ‖Complex.sin (Real.pi * z)‖ := by
      ring
    rw [h2, hnorm, div_mul_cancel₀ _ (ne_of_gt hsinNorm)]
  have hden : ‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖ ≤ S * G :=
    mul_le_mul hS hGup (norm_nonneg _) (le_of_lt hSpos)
  have hle : Real.pi / (S * G) ≤
      Real.pi / (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (mul_pos hsinNorm hGNorm) hden
  exact le_trans hle (le_of_eq heq.symm)

/-- E05 shifted-point instance: reflection-form lower at `w_E05 + 1`
with the sine upper `S` and companion upper `G` as explicit premises.
Feeds `premGamma_E05_ge_of_shift` once `S * G ≤ π / 0.645` numerals land. -/
theorem premGamma_E05shift_refl_form (S G : ℝ)
    (hS : ‖Complex.sin (Real.pi *
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤ S)
    (hGup : ‖Complex.Gamma (1 -
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤ G)
    (hSpos : 0 < S) (hGpos : 0 < G)
    (hsin : Complex.sin (Real.pi *
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) ≠ 0)
    (hGne : Complex.Gamma (1 -
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) ≠ 0) :
    Real.pi / (S * G) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ :=
  premGamma_refl_lower_of_uppers _ S G hS hGup hSpos hGpos hsin hGne

/-! ## Missing-machinery spec (filed, not fixed).

Exact theorem needed (E05 shifted numerator):
`theorem premGamma_E05_num_ge : (0.645 : ℝ) ≤ ‖Complex.Gamma
((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖`
(and the 6 siblings `0.66 / 0.164 / 0.0314 / 0.0528 / 0.01638 / 0.00657`
at the E06 / E07 / E01 / E08 / E09 / E10 shifted points).

Host: the Stirling-disc enclosure file (`door3_gamma_disc.lean` shape or a
new `Mathlib`-only disc leaf) — NOT this premise file, so the floors stay
honestly open until the enclosure lands.

API it needs: a direct complex-Gamma lower at `Re ≈ 1.2` (Stirling disc /
Taylor enclosure with explicit remainder, or Binet integral with explicit
bounds). Neither is banked in Mathlib (no `Complex.logGamma`, no
Stirling-with-remainder, no Gauss digamma rep) or in-repo.

Why reflection cannot supply it (hand evaluation, honest): closing `0.645`
via `premGamma_E05shift_refl_form` needs `S * G ≤ π / 0.645 ≈ 4.87`, but the
banked sine upper alone gives `S ≈ 2 * exp(π * 0.375) ≈ 6.5 > 4.87`, and the
companion point `1 - (w+1) = -0.1975 + 0.375i` sits `0.42` from the pole at
`0` (true `‖Γ‖ ≈ 2.4`), so no valid upper `G` can repair the product.
E06 (`|Im| = 0.625`, budget `π / 0.66 ≈ 4.76`, `S ≈ 14`) is worse. The
reflection lane is quantitatively dead for all 7 E-row shifted numerators;
a genuine disc enclosure is required.

Residual: all 7 shifted numerators stay open
(`0.645 / 0.66 / 0.164 / 0.0314 / 0.0528 / 0.01638 / 0.00657` lower bounds
on `‖Gamma(w+1)‖` at the 7 E-row shifted points); no floor closed or forced
this turn.
-/

/-! ## GAMMA-STIRLING2: E10 smallest-first crude attempt (filed, not forced).

Target: `0.00657 ≤ ‖Gamma (w_E10 + 1)‖` at `w_E10 + 1 = 1.1975 + 4.375i`
(banked E10 shift triple: `premGamma_E10_wnorm_le` (`‖w‖ ≤ 4.38`),
`premGamma_E10_ge_of_shift` (`0.00657 / 4.38 = 0.0015`), `premGamma_E10_threshold_ok`).

Route A — integral representation: DEAD as a lower lane. Mathlib banks
`Complex.Gamma_eq_integral` (`Basic.lean:318`) + `Real.Gamma_eq_integral`
(`Basic.lean:404`), and the only banked norm-through-integral step is
`MeasureTheory.norm_integral_le_integral_norm`, used by
`D3SG_Gamma_norm_le_real` (`door3_stirling_gamma.lean:8`):
`‖Gamma w‖ ≤ Gamma (w.re)`. Wrong direction for a numerator lower; reverse
triangle / phase control on `t^(w-1)` over `Ioi 0` is not banked. No exact
numerals attempted (nothing sound to instantiate).

Route B — product / factorial shift-down: DEAD without a new complex lower.
Banked `premGamma_shift_norm_one` / `premGamma_shift_lower` give
`‖Gamma (w+1)‖ = ‖w‖ * ‖Gamma w‖`, so a lower on the E10 numerator needs a
lower at `w_E10 = 0.1975 + 4.375i` (Re smaller, strictly harder). The only
banked real lower `gamma_low_77` (`door3_gamma_real_low.lean:220`, `0.77` on
`Icc 1 2.1`) cannot transfer: `D3SG_Gamma_norm_le_real` runs
complex ≤ real (upper), and the transfer is numerically false at `|Im| > 0`.
No exact numerals attempted (would reverse a banked inequality).

Route C — reflection form at E10 height: QUANTIATIVELY DEAD by orders.
`premGamma_refl_lower_of_uppers` shape is banked below as
`premGamma_E10shift_refl_form` (explicit `S / G` premises, mirrors
`premGamma_E05shift_refl_form`). Closing `0.00657` needs
`S * G ≤ π / 0.00657 ≈ 478.17`, but the banked sine upper alone
(`sin_norm_le`: `‖sin z‖ ≤ 2 * exp |Im|`, `|Im| = π * 4.375 ≈ 13.74`)
is `≈ 1.8M`, and the banked outer envelope at this height
(`outer_small` in `door3_complex_wendel.lean:359`, explicit `pi / exp`
premises) is `π / (2 * exp(π * 4.375) * 1.25) ≤ 0.000002`, i.e. `3285x`
below `0.00657` (`0.000002 * 3285 = 0.00657`). Companion point
`1 - (w+1) = -0.1975 - 4.375i` has `Re < 0`, so no Tier-C companion upper
applies either. Nothing is forced: numerator stays open.
-/

/-- E10 shifted-point instance: reflection-form lower at `w_E10 + 1`
with the sine upper `S` and companion upper `G` as explicit premises.
Mirrors `premGamma_E05shift_refl_form`; feeds `premGamma_E10_ge_of_shift`
once `S * G ≤ π / 0.00657` numerals land (see shortfall below: no banked
`S / G` pair reaches this budget). -/
theorem premGamma_E10shift_refl_form (S G : ℝ)
    (hS : ‖Complex.sin (Real.pi *
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤ S)
    (hGup : ‖Complex.Gamma (1 -
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤ G)
    (hSpos : 0 < S) (hGpos : 0 < G)
    (hsin : Complex.sin (Real.pi *
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) ≠ 0)
    (hGne : Complex.Gamma (1 -
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) ≠ 0) :
    Real.pi / (S * G) ≤ ‖Complex.Gamma
      ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ :=
  premGamma_refl_lower_of_uppers _ S G hS hGup hSpos hGpos hsin hGne

/-- E10 crude shortfall factor (pure arithmetic): the banked outer reflection
envelope `0.000002` at `|Im| = 4.375` sits `3285x` below the needed `0.00657`.
Mirrors the `outer_small` scale (`door3_complex_wendel.lean:359-364`); no
floor is closed. -/
theorem premGamma_E10_crude_shortfall_factor :
    (0.000002 : ℝ) * 3285 = 0.00657 := by
  norm_num

/-- E10 crude gap (pure arithmetic): envelope strictly below target. -/
theorem premGamma_E10_crude_gap :
    (0.000002 : ℝ) < (0.00657 : ℝ) := by
  norm_num

/-! ## GAMMA-ENCLOSURE: E10 Euler-product setup (N = 1 exact + rate spec).

Survey verdict (read-only, this turn):
* Mathlib Euler-product Gamma API is ONLY the limit sequence
  `Complex.GammaSeq` (`Beta.lean:230`, `GammaSeq s n =
  n ^ s * n ! / prod_{range (n+1)} (s + j)`) with limit
  `Complex.GammaSeq_tendsto_Gamma` (`Beta.lean:335` complex, `:468` real).
  There is NO `Complex.Gamma_product_formula` infinite-product lower; the
  only infinite product nearby is the sine product (`EulerSineProd.lean`).
* `door3_gamma_product.lean` banks UPPERS only: `gamma_shift_norm` (`:15`),
  `real_gamma_shift` (`:31`), `norm_gamma_mul_prod_le` (`:42`),
  `norm_gamma_le_prod` (`:54`), `norm_gamma_sq_le_prod` (`:71`).
* Finite-product lower machinery EXISTS as equality `norm_prod`
  (`Mathlib/Analysis/Normed/Ring/Basic.lean:769`,
  `‖prod‖ = prod ‖·‖`) plus `norm_mul` / `norm_div` / `norm_pow`; no
  `norm_prod_ge`-shape lemma is needed. Cpow norms are banked via
  `Complex.norm_cpow_eq_rpow_re_of_pos` (`Pow/Real.lean:337`) and
  `Complex.norm_natCast_cpow_of_pos` (`:355`).
* Hence the ONLY missing piece for a direct complex lower at
  `w_E10 + 1 = 1.1975 + 4.375i` (floor `0.00657`) is the quantitative
  `GammaSeq` rate `‖GammaSeq s N - Gamma s‖ ≤ _` (tail control). No
  `1`-ish tail-lower shape is banked; nothing is forced.

Banked below (committable, Mathlib-only, exact numerals): the E10 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 4.54`, `‖s+1‖ ≤ 4.90`), their product
form (`‖s * (s+1)‖ ≤ 22.25`), the `N = 1` finite-approximant conditional
lower (`0.044 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.00657 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.037`, since `0.044 - 0.037 = 0.007 ≥ 0.00657`). The two
premises are filed as `Prop` specs, not proved.
-/

/-- E10 shifted denominator norm: `‖w_E10 + 1‖ ≤ 4.54`
(TRUE `≈ 4.5358`; `1.1975^2 + 4.375^2 = 20.57463125 ≤ 4.54^2`). -/
theorem premGamma_E10shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (4.54 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)).im
      = (4.375 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).im = (8.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (4.54 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.54 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E10 shifted successor norm: `‖(w_E10 + 1) + 1‖ ≤ 4.90`
(TRUE `≈ 4.896`; `2.1975^2 + 4.375^2 = 23.96963125 ≤ 4.90^2`). -/
theorem premGamma_E10shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (4.90 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (4.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).im = (8.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (4.90 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.90 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E10 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E10_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E10 `N = 1` denominator product upper (`4.54 * 4.90 = 22.246 ≤ 22.25`). -/
theorem premGamma_E10_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (22.25 : ℝ) := by
  rw [premGamma_E10_prod1_norm_eq]
  have h := mul_le_mul premGamma_E10shift_norm_le premGamma_E10shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (4.54 : ℝ) * 4.90 = 22.246 := by norm_num
  rw [heq] at h
  have hle : (22.246 : ℝ) ≤ 22.25 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E10.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E10_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E10 with budget `0.037` (`0.044 - 0.037 = 0.007 ≥ 0.00657`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E10_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.037 : ℝ)

/-- E10 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.044 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 22.246 ≈ 0.04495`). -/
theorem premGamma_E10_GammaSeq1_lower_of_link
    (hlink : premGamma_E10_GammaSeq1_link) :
    (0.044 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E10_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (8.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (4.54 : ℝ) * 4.90 :=
    mul_le_mul premGamma_E10shift_norm_le premGamma_E10shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.044 : ℝ) ≤ 1 / ((4.54 : ℝ) * 4.90) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E10 limit-closure conditional: finite lower `0.044` plus rate `0.037`
gives the shifted floor `0.00657` (`0.044 - 0.037 = 0.007 ≥ 0.00657`).
Feeds `premGamma_E10_ge_of_shift` once L1 + L2 land. -/
theorem premGamma_E10_Gamma_lower_of_Seq1_rate
    (hSeq : (0.044 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E10_GammaSeq_rate_needed) :
    (0.00657 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E10_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.007 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (8.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.00657 : ℝ) ≤ (0.007 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E09 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E10 block token-for-token with E09 numerals:
`s = w_E09 + 1 = 1.1975 + 3.625i` (shifted floor `0.01638`).
`‖s‖^2 = 1.43400625 + 13.140625 = 14.57463125 ≤ 3.82^2 = 14.5924`;
`‖s+1‖^2 = 4.82900625 + 13.140625 = 17.96963125 ≤ 4.24^2 = 17.9776`;
product `3.82 * 4.24 = 16.1968 ≤ 16.20`; finite lower `0.061 ≤ ‖GammaSeq s 1‖`
(`1 / 16.1968 ≈ 0.06174`); rate budget `0.044`
(`0.061 - 0.044 = 0.017 ≥ 0.01638`).

Route (a) verdict (read-only): `Complex.GammaSeq_tendsto_Gamma`
(`Beta.lean:335`, def `GammaSeq` at `:230`) is qualitative only — dominated
convergence (`approx_Gamma_integral_tendsto_Gamma_integral`) plus the
`GammaSeq_add_one_left` recurrence induction — so no quantitative rate is
extracted this turn. Missing rate lemma (filed, not proved), exact shape:
`theorem GammaSeq_rate_needed (s : ℂ) (N : ℕ) (C : ℝ) :
‖Complex.GammaSeq s N - Complex.Gamma s‖ ≤ C`
instantiated at `s = w_E09 + 1`, `N = 1`, `C = 0.044` (and at E10 with
`C = 0.037`); host is a Stirling-disc / Binet-enclosure leaf, NOT this file.
Banked below (committable, Mathlib-only, exact numerals): the E09 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 3.82`, `‖s+1‖ ≤ 4.24`), their product
form (`‖s * (s+1)‖ ≤ 16.20`), the `N = 1` finite-approximant conditional
lower (`0.061 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.01638 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.044`, since `0.061 - 0.044 = 0.017 ≥ 0.01638`). The two
premises are filed as `Prop` specs, not proved.
-/

/-- E09 shifted denominator norm: `‖w_E09 + 1‖ ≤ 3.82`
(TRUE `≈ 3.8177`; `1.1975^2 + 3.625^2 = 14.57463125 ≤ 3.82^2`). -/
theorem premGamma_E09shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (3.82 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)).im
      = (3.625 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).im = (7.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (3.82 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.82 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E09 shifted successor norm: `‖(w_E09 + 1) + 1‖ ≤ 4.24`
(TRUE `≈ 4.2391`; `2.1975^2 + 3.625^2 = 17.96963125 ≤ 4.24^2`). -/
theorem premGamma_E09shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (4.24 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (3.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).im = (7.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (4.24 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.24 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E09 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E09_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E09 `N = 1` denominator product upper (`3.82 * 4.24 = 16.1968 ≤ 16.20`). -/
theorem premGamma_E09_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (16.20 : ℝ) := by
  rw [premGamma_E09_prod1_norm_eq]
  have h := mul_le_mul premGamma_E09shift_norm_le premGamma_E09shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (3.82 : ℝ) * 4.24 = 16.1968 := by norm_num
  rw [heq] at h
  have hle : (16.1968 : ℝ) ≤ 16.20 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E09.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E09_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E09 with budget `0.044` (`0.061 - 0.044 = 0.017 ≥ 0.01638`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E09_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.044 : ℝ)

/-- E09 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.061 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 16.1968 ≈ 0.06174`). -/
theorem premGamma_E09_GammaSeq1_lower_of_link
    (hlink : premGamma_E09_GammaSeq1_link) :
    (0.061 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E09_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (7.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (3.82 : ℝ) * 4.24 :=
    mul_le_mul premGamma_E09shift_norm_le premGamma_E09shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.061 : ℝ) ≤ 1 / ((3.82 : ℝ) * 4.24) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E09 limit-closure conditional: finite lower `0.061` plus rate `0.044`
gives the shifted floor `0.01638` (`0.061 - 0.044 = 0.017 ≥ 0.01638`).
Feeds `premGamma_E09_ge_of_shift` once L1 + L2 land. -/
theorem premGamma_E09_Gamma_lower_of_Seq1_rate
    (hSeq : (0.061 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E09_GammaSeq_rate_needed) :
    (0.01638 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E09_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.017 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (7.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.01638 : ℝ) ≤ (0.017 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E08 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E09/E10 blocks token-for-token with E08 numerals:
`s = w_E08 + 1 = 1.1975 + 2.625i` (shifted floor `0.0528`).
`‖s‖^2 = 1.43400625 + 6.890625 = 8.32463125 ≤ 2.89^2 = 8.3521`;
`‖s+1‖^2 = 4.82900625 + 6.890625 = 11.71963125 ≤ 3.43^2 = 11.7649`;
product `2.89 * 3.43 = 9.9127 ≤ 9.92`; finite lower `0.100 ≤ ‖GammaSeq s 1‖`
(`1 / 9.9127 ≈ 0.10088`); rate budget `0.046`
(`0.100 - 0.046 = 0.054 ≥ 0.0528`).

Numerals Python-checked (`Decimal`, exact): squares, product, lower
(`0.100 * 9.9127 = 0.99127 ≤ 1`), and rate (`0.054 ≥ 0.0528`).
Banked below (committable, Mathlib-only, exact numerals): the E08 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 2.89`, `‖s+1‖ ≤ 3.43`), their product
form (`‖s * (s+1)‖ ≤ 9.92`), the `N = 1` finite-approximant conditional
lower (`0.100 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.0528 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.046`, since `0.100 - 0.046 = 0.054 ≥ 0.0528`). The two
premises are filed as `Prop` specs, not proved; the rate host is the
Stirling-disc / Binet-enclosure leaf, NOT this file.
-/

/-- E08 shifted denominator norm: `‖w_E08 + 1‖ ≤ 2.89`
(TRUE `≈ 2.8852`; `1.1975^2 + 2.625^2 = 8.32463125 ≤ 2.89^2`). -/
theorem premGamma_E08shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (2.89 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)).im
      = (2.625 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).im = (5.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (2.89 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.89 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E08 shifted successor norm: `‖(w_E08 + 1) + 1‖ ≤ 3.43`
(TRUE `≈ 3.4234`; `2.1975^2 + 2.625^2 = 11.71963125 ≤ 3.43^2`). -/
theorem premGamma_E08shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (3.43 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (2.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).im = (5.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (3.43 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.43 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E08 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E08_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E08 `N = 1` denominator product upper (`2.89 * 3.43 = 9.9127 ≤ 9.92`). -/
theorem premGamma_E08_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (9.92 : ℝ) := by
  rw [premGamma_E08_prod1_norm_eq]
  have h := mul_le_mul premGamma_E08shift_norm_le premGamma_E08shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (2.89 : ℝ) * 3.43 = 9.9127 := by norm_num
  rw [heq] at h
  have hle : (9.9127 : ℝ) ≤ 9.92 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E08.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E08_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E08 with budget `0.046` (`0.100 - 0.046 = 0.054 ≥ 0.0528`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E08_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.046 : ℝ)

/-- E08 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.100 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 9.9127 ≈ 0.10088`). -/
theorem premGamma_E08_GammaSeq1_lower_of_link
    (hlink : premGamma_E08_GammaSeq1_link) :
    (0.100 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E08_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (5.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (2.89 : ℝ) * 3.43 :=
    mul_le_mul premGamma_E08shift_norm_le premGamma_E08shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.100 : ℝ) ≤ 1 / ((2.89 : ℝ) * 3.43) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E08 limit-closure conditional: finite lower `0.100` plus rate `0.046`
gives the shifted floor `0.0528` (`0.100 - 0.046 = 0.054 ≥ 0.0528`).
Feeds `premGamma_E08_ge_of_shift` once L1 + L2 land. -/
theorem premGamma_E08_Gamma_lower_of_Seq1_rate
    (hSeq : (0.100 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E08_GammaSeq_rate_needed) :
    (0.0528 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E08_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.054 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (5.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.0528 : ℝ) ≤ (0.054 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E07 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E09/E10 blocks token-for-token with E07 numerals:
`s = w_E07 + 1 = 1.1975 + 1.625i` (shifted floor `0.164`).
`‖s‖^2 = 1.43400625 + 2.640625 = 4.07463125 ≤ 2.02^2 = 4.0804`;
`‖s+1‖^2 = 4.82900625 + 2.640625 = 7.46963125 ≤ 2.74^2 = 7.5076`;
product `2.02 * 2.74 = 5.5348 ≤ 5.54`; finite lower `0.180 ≤ ‖GammaSeq s 1‖`
(`1 / 5.5348 ≈ 0.18068`); rate budget `0.015`
(`0.180 - 0.015 = 0.165 ≥ 0.164`).

Numerals Python-checked (`Decimal`, exact): squares, product, lower
(`0.180 * 5.5348 = 0.996264 ≤ 1`), and rate (`0.165 ≥ 0.164`).
Banked below (committable, Mathlib-only, exact numerals): the E07 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 2.02`, `‖s+1‖ ≤ 2.74`), their product
form (`‖s * (s+1)‖ ≤ 5.54`), the `N = 1` finite-approximant conditional
lower (`0.180 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.164 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.015`, since `0.180 - 0.015 = 0.165 ≥ 0.164`). The two
premises are filed as `Prop` specs, not proved; the rate host is the
Stirling-disc / Binet-enclosure leaf, NOT this file.
-/

/-- E07 shifted denominator norm: `‖w_E07 + 1‖ ≤ 2.02`
(TRUE `≈ 2.0186`; `1.1975^2 + 1.625^2 = 4.07463125 ≤ 2.02^2`). -/
theorem premGamma_E07shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (2.02 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)).im
      = (1.625 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).im = (3.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (2.02 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.02 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E07 shifted successor norm: `‖(w_E07 + 1) + 1‖ ≤ 2.74`
(TRUE `≈ 2.7331`; `2.1975^2 + 1.625^2 = 7.46963125 ≤ 2.74^2`). -/
theorem premGamma_E07shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (2.74 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (1.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).im = (3.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (2.74 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.74 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E07 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E07_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E07 `N = 1` denominator product upper (`2.02 * 2.74 = 5.5348 ≤ 5.54`). -/
theorem premGamma_E07_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (5.54 : ℝ) := by
  rw [premGamma_E07_prod1_norm_eq]
  have h := mul_le_mul premGamma_E07shift_norm_le premGamma_E07shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (2.02 : ℝ) * 2.74 = 5.5348 := by norm_num
  rw [heq] at h
  have hle : (5.5348 : ℝ) ≤ 5.54 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E07.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E07_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E07 with budget `0.015` (`0.180 - 0.015 = 0.165 ≥ 0.164`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E07_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.015 : ℝ)

/-- E07 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.180 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 5.5348 ≈ 0.18068`). -/
theorem premGamma_E07_GammaSeq1_lower_of_link
    (hlink : premGamma_E07_GammaSeq1_link) :
    (0.180 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E07_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (3.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (2.02 : ℝ) * 2.74 :=
    mul_le_mul premGamma_E07shift_norm_le premGamma_E07shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.180 : ℝ) ≤ 1 / ((2.02 : ℝ) * 2.74) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E07 limit-closure conditional: finite lower `0.180` plus rate `0.015`
gives the shifted floor `0.164` (`0.180 - 0.015 = 0.165 ≥ 0.164`).
Feeds `premGamma_E07_ge_of_shift` once L1 + L2 land. -/
theorem premGamma_E07_Gamma_lower_of_Seq1_rate
    (hSeq : (0.180 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E07_GammaSeq_rate_needed) :
    (0.164 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E07_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.165 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (3.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.164 : ℝ) ≤ (0.165 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E06 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E08/E07 blocks token-for-token with E06 numerals:
`s = w_E06 + 1 = 1.1975 + 0.625i` (shifted need `0.66`).
`‖s‖^2 = 1.43400625 + 0.390625 = 1.82463125 ≤ 1.36^2 = 1.8496`;
`‖s+1‖^2 = 4.82900625 + 0.390625 = 5.21963125 ≤ 2.29^2 = 5.2441`;
product `1.36 * 2.29 = 3.1144 ≤ 3.12`; finite lower `0.320 ≤ ‖GammaSeq s 1‖`
(`1 / 3.1144 ≈ 0.32109`; `0.320 * 3.1144 = 0.996608 ≤ 1`); rate budget `0.015`
(`0.320 - 0.015 = 0.305 ≥ 0.300`).

Numerals hand-checked (exact `Decimal` arithmetic): squares, product, lower
(`0.320 * 3.1144 = 0.996608 ≤ 1`), and rate (`0.305 ≥ 0.300`).
N = 1 CEILING (filed, not fixed): the `N = 1` approximant satisfies
`‖GammaSeq s 1‖ = 1 / ‖s * (s+1)‖ ≤ 1 / (1.1975 * 2.1975) ≈ 0.38`, so NO
`N = 1` scaffold can reach the shifted need `0.66`. The limit-closure below
therefore banks the honest weaker floor `0.300` (does NOT feed
`premGamma_E06_ge_of_shift`); the full `0.66` needs `N ≥ 2` Euler-product
terms or a direct Binet-leaf lower — flagged crux, same host as the L2 rate.
Banked below (committable, Mathlib-only, exact numerals): the E06 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 1.36`, `‖s+1‖ ≤ 2.29`), their product
form (`‖s * (s+1)‖ ≤ 3.12`), the `N = 1` finite-approximant conditional
lower (`0.320 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.300 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.015`). The two premises are filed as `Prop` specs, not
proved; the rate host is the Stirling-disc / Binet-enclosure leaf, NOT this
file.
-/

/-- E06 shifted denominator norm: `‖w_E06 + 1‖ ≤ 1.36`
(TRUE `≈ 1.3508`; `1.1975^2 + 0.625^2 = 1.82463125 ≤ 1.36^2`). -/
theorem premGamma_E06shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (1.36 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (1.36 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (1.36 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 shifted successor norm: `‖(w_E06 + 1) + 1‖ ≤ 2.29`
(TRUE `≈ 2.2846`; `2.1975^2 + 0.625^2 = 5.21963125 ≤ 2.29^2`). -/
theorem premGamma_E06shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (2.29 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (2.29 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.29 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E06_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E06 `N = 1` denominator product upper (`1.36 * 2.29 = 3.1144 ≤ 3.12`). -/
theorem premGamma_E06_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (3.12 : ℝ) := by
  rw [premGamma_E06_prod1_norm_eq]
  have h := mul_le_mul premGamma_E06shift_norm_le premGamma_E06shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (1.36 : ℝ) * 2.29 = 3.1144 := by norm_num
  rw [heq] at h
  have hle : (3.1144 : ℝ) ≤ 3.12 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E06.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E06_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E06 with budget `0.015` (`0.320 - 0.015 = 0.305 ≥ 0.300`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E06_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.015 : ℝ)

/-- E06 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.320 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 3.1144 ≈ 0.32109`). -/
theorem premGamma_E06_GammaSeq1_lower_of_link
    (hlink : premGamma_E06_GammaSeq1_link) :
    (0.320 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E06_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (1.36 : ℝ) * 2.29 :=
    mul_le_mul premGamma_E06shift_norm_le premGamma_E06shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.320 : ℝ) ≤ 1 / ((1.36 : ℝ) * 2.29) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E06 limit-closure conditional: finite lower `0.320` plus rate `0.015`
gives the honest `N = 1` floor `0.300` (`0.320 - 0.015 = 0.305 ≥ 0.300`).
Does NOT feed `premGamma_E06_ge_of_shift` (needs `0.66`): N = 1 ceiling
`≈ 0.324 < 0.66`; the full floor awaits `N ≥ 2` or a Binet-leaf lower. -/
theorem premGamma_E06_Gamma_lower_of_Seq1_rate
    (hSeq : (0.320 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E06_GammaSeq_rate_needed) :
    (0.300 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E06_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.305 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.300 : ℝ) ≤ (0.305 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E05 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E08/E07 blocks token-for-token with E05 numerals:
`s = w_E05 + 1 = 1.1975 - 0.375i` (shifted need `0.645`).
`‖s‖^2 = 1.43400625 + 0.140625 = 1.57463125 ≤ 1.26^2 = 1.5876`;
`‖s+1‖^2 = 4.82900625 + 0.140625 = 4.96963125 ≤ 2.23^2 = 4.9729`;
product `1.26 * 2.23 = 2.8098 ≤ 2.81`; finite lower `0.355 ≤ ‖GammaSeq s 1‖`
(`1 / 2.8098 ≈ 0.35590`; `0.355 * 2.8098 = 0.997479 ≤ 1`); rate budget `0.014`
(`0.355 - 0.014 = 0.341 ≥ 0.340`).

Numerals hand-checked (exact `Decimal` arithmetic): squares, product, lower
(`0.355 * 2.8098 = 0.997479 ≤ 1`), and rate (`0.341 ≥ 0.340`).
N = 1 CEILING (filed, not fixed): the `N = 1` approximant satisfies
`‖GammaSeq s 1‖ = 1 / ‖s * (s+1)‖ ≤ 1 / (1.1975 * 2.1975) ≈ 0.38`, so NO
`N = 1` scaffold can reach the shifted need `0.645`. The limit-closure below
therefore banks the honest weaker floor `0.340` (does NOT feed
`premGamma_E05_ge_of_shift`); the full `0.645` needs `N ≥ 2` Euler-product
terms or a direct Binet-leaf lower — flagged crux, same host as the L2 rate.
Banked below (committable, Mathlib-only, exact numerals): the E05 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 1.26`, `‖s+1‖ ≤ 2.23`), their product
form (`‖s * (s+1)‖ ≤ 2.81`), the `N = 1` finite-approximant conditional
lower (`0.355 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.340 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.014`). The two premises are filed as `Prop` specs, not
proved; the rate host is the Stirling-disc / Binet-enclosure leaf, NOT this
file.
-/

/-- E05 shifted denominator norm: `‖w_E05 + 1‖ ≤ 1.26`
(TRUE `≈ 1.2548`; `1.1975^2 + 0.375^2 = 1.57463125 ≤ 1.26^2`). -/
theorem premGamma_E05shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (1.26 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (1.26 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (1.26 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 shifted successor norm: `‖(w_E05 + 1) + 1‖ ≤ 2.23`
(TRUE `≈ 2.2295`; `2.1975^2 + 0.375^2 = 4.96963125 ≤ 2.23^2`). -/
theorem premGamma_E05shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (2.23 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (2.23 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (2.23 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E05_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E05 `N = 1` denominator product upper (`1.26 * 2.23 = 2.8098 ≤ 2.81`). -/
theorem premGamma_E05_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (2.81 : ℝ) := by
  rw [premGamma_E05_prod1_norm_eq]
  have h := mul_le_mul premGamma_E05shift_norm_le premGamma_E05shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (1.26 : ℝ) * 2.23 = 2.8098 := by norm_num
  rw [heq] at h
  have hle : (2.8098 : ℝ) ≤ 2.81 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E05.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E05_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E05 with budget `0.014` (`0.355 - 0.014 = 0.341 ≥ 0.340`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E05_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E05 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.355 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 2.8098 ≈ 0.35590`). -/
theorem premGamma_E05_GammaSeq1_lower_of_link
    (hlink : premGamma_E05_GammaSeq1_link) :
    (0.355 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E05_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (1.26 : ℝ) * 2.23 :=
    mul_le_mul premGamma_E05shift_norm_le premGamma_E05shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.355 : ℝ) ≤ 1 / ((1.26 : ℝ) * 2.23) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E05 limit-closure conditional: finite lower `0.355` plus rate `0.014`
gives the honest `N = 1` floor `0.340` (`0.355 - 0.014 = 0.341 ≥ 0.340`).
Does NOT feed `premGamma_E05_ge_of_shift` (needs `0.645`): N = 1 ceiling
`≈ 0.357 < 0.645`; the full floor awaits `N ≥ 2` or a Binet-leaf lower. -/
theorem premGamma_E05_Gamma_lower_of_Seq1_rate
    (hSeq : (0.355 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E05_GammaSeq_rate_needed) :
    (0.340 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E05_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.341 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.340 : ℝ) ≤ (0.341 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-ENCLOSURE: E01 Euler-product setup (N = 1 exact + rate spec).

Mirrors the E08/E07 blocks token-for-token with E01 numerals:
`s = w_E01 + 1 = 1.1975 - 3.125i` (shifted floor `0.0314`).
`‖s‖^2 = 1.43400625 + 9.765625 = 11.19963125 ≤ 3.35^2 = 11.2225`;
`‖s+1‖^2 = 4.82900625 + 9.765625 = 14.59463125 ≤ 3.83^2 = 14.6689`;
product `3.35 * 3.83 = 12.8305 ≤ 12.84`; finite lower `0.077 ≤ ‖GammaSeq s 1‖`
(`1 / 12.8305 ≈ 0.07794`; `0.077 * 12.8305 = 0.9879485 ≤ 1`); rate budget
`0.045` (`0.077 - 0.045 = 0.032 ≥ 0.0314`).

Numerals hand-checked (exact `Decimal` arithmetic): squares, product, lower
(`0.077 * 12.8305 = 0.9879485 ≤ 1`), and rate (`0.032 ≥ 0.0314`).
Banked below (committable, Mathlib-only, exact numerals): the E01 shifted
denominator uppers at `N = 1` (`‖s‖ ≤ 3.35`, `‖s+1‖ ≤ 3.83`), their product
form (`‖s * (s+1)‖ ≤ 12.84`), the `N = 1` finite-approximant conditional
lower (`0.077 ≤ ‖GammaSeq s 1‖` from the explicit `N = 1` link premise),
and the limit-closure conditional (`0.0314 ≤ ‖Gamma s‖` from the explicit
rate premise `≤ 0.045`, since `0.077 - 0.045 = 0.032 ≥ 0.0314`). The two
premises are filed as `Prop` specs, not proved; the rate host is the
Stirling-disc / Binet-enclosure leaf, NOT this file.
-/

/-- E01 shifted denominator norm: `‖w_E01 + 1‖ ≤ 3.35`
(TRUE `≈ 3.3464`; `1.1975^2 + 3.125^2 = 11.19963125 ≤ 3.35^2`). -/
theorem premGamma_E01shift_norm_le :
    ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ ≤ (3.35 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)).im
      = (-3.125 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).im = (-6.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2
      ≤ (3.35 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.35 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E01 shifted successor norm: `‖(w_E01 + 1) + 1‖ ≤ 3.83`
(TRUE `≈ 3.8203`; `2.1975^2 + 3.125^2 = 14.59463125 ≤ 3.83^2`). -/
theorem premGamma_E01shift_succ_norm_le :
    ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (3.83 : ℝ) := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (-3.125 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).im = (-6.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2
      ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.83 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E01 `N = 1` denominator product norm identity (finite `norm_mul`). -/
theorem premGamma_E01_prod1_norm_eq :
    ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ =
      ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
  norm_mul _ _

/-- E01 `N = 1` denominator product upper (`3.35 * 3.83 = 12.8305 ≤ 12.84`). -/
theorem premGamma_E01_prod1_le :
    ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) *
      (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤ (12.84 : ℝ) := by
  rw [premGamma_E01_prod1_norm_eq]
  have h := mul_le_mul premGamma_E01shift_norm_le premGamma_E01shift_succ_norm_le
    (norm_nonneg _) (by norm_num)
  have heq : (3.35 : ℝ) * 3.83 = 12.8305 := by norm_num
  rw [heq] at h
  have hle : (12.8305 : ℝ) ≤ 12.84 := by norm_num
  exact le_trans h hle

/-- Missing link L1 (filed, not proved): `N = 1` GammaSeq norm identity at E01.
Unfolds `Complex.GammaSeq s 1 = 1 / (s * (s + 1))` in norm
(`(1 : ℂ) ^ s = 1` via `one_cpow`, `1 ! = 1`, `prod_range_succ`), then
`norm_div` / `norm_one` / `norm_mul`. Needs only Mathlib; left open because
the cpow unfolding was not instantiated this turn. -/
def premGamma_E01_GammaSeq1_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ =
    1 / (‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖)

/-- Missing rate L2 (filed, not proved): quantitative `GammaSeq` convergence
at E01 with budget `0.045` (`0.077 - 0.045 = 0.032 ≥ 0.0314`). Host: a
Stirling-disc / Binet-enclosure leaf or an explicit `GammaSeq` rate lemma;
NOT this premise file. -/
def premGamma_E01_GammaSeq_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.045 : ℝ)

/-- E01 `N = 1` finite-approximant conditional lower: the exact denominator
uppers give `0.077 ≤ ‖GammaSeq s 1‖` once link L1 is supplied
(`1 / 12.8305 ≈ 0.07794`). -/
theorem premGamma_E01_GammaSeq1_lower_of_link
    (hlink : premGamma_E01_GammaSeq1_link) :
    (0.077 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ := by
  unfold premGamma_E01_GammaSeq1_link at hlink
  rw [hlink]
  have hsne : ((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)).re
        = (1.1975 : ℝ) := by
      rw [Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hs1ne : (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    have hr : ((((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-6.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hr] at hre
    norm_num at hre
  have hpos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ :=
    mul_pos (norm_pos_iff.mpr hsne) (norm_pos_iff.mpr hs1ne)
  have hprod : ‖((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ≤
      (3.35 : ℝ) * 3.83 :=
    mul_le_mul premGamma_E01shift_norm_le premGamma_E01shift_succ_norm_le
      (norm_nonneg _) (by norm_num)
  have hbase : (0.077 : ℝ) ≤ 1 / ((3.35 : ℝ) * 3.83) := by norm_num
  exact le_trans hbase (one_div_le_one_div_of_le hpos hprod)

/-- E01 limit-closure conditional: finite lower `0.077` plus rate `0.045`
gives the shifted floor `0.0314` (`0.077 - 0.045 = 0.032 ≥ 0.0314`).
Feeds `premGamma_E01_ge_of_shift` once L1 + L2 land. -/
theorem premGamma_E01_Gamma_lower_of_Seq1_rate
    (hSeq : (0.077 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1‖)
    (hRate : premGamma_E01_GammaSeq_rate_needed) :
    (0.0314 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E01_GammaSeq_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)) 1 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  have h7 : (0.032 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-6.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    linarith
  have hle : (0.0314 : ℝ) ≤ (0.032 : ℝ) := by norm_num
  exact le_trans hle h7

/-! ## GAMMA-BINET: E06 N = 2 ceiling audit + N needed (filed, not fixed).

Survey verdict (read-only, this turn):
* Binet Gamma integral: UNSUPPORTED. Only Binet hits in-repo are Fibonacci
  Binet (`Mathlib/NumberTheory/Real/GoldenRatio.lean:24,180,197,201`) and the
  Binet-Cauchy identity (`Mathlib/LinearAlgebra/CrossProduct.lean:111`).
  No `Complex.Gamma` Binet representation, no `Complex.logGamma` / `Real.logGamma`
  API (only internal `BohrMollerup.logGammaSeq`, `BohrMollerup.lean:140`);
  confirmed by `door3_stirling_rem.lean:16-17` and `door3_digamma.lean:13-20`.
* `Real.Gamma_eq_*` / `Complex.Gamma_eq_*` integral forms: BANKED
  (`Basic.lean:318` complex, `:404` real) but give only the UPPER
  `D3SG_Gamma_norm_le_real` (`door3_stirling_gamma.lean:8`); reverse-triangle /
  phase control for a LOWER is unbanked (`door3_premise_gamma.lean:1254-1261`).
* Stirling series / `hasSum` remainder bounds: ABSENT. Only `Nat.factorial`
  Stirling (`Stirling.lean`) plus qualitative `Complex.GammaSeq_tendsto_Gamma`
  (`Beta.lean:335` complex, `:468` real, def `GammaSeq` at `:230`); no
  quantitative `GammaSeq` rate anywhere (rate host filed at
  `door3_premise_gamma.lean:1523-1526,2160-2163,2347-2350`).
* `door3_stirling_rem.lean:193-240`: `D3SR_gamma_lower_of_refl` + Tier-C form
  `D3SR_gamma_lower_TierC_of_sin` (constants `pi / 600`, sine premise `S`,
  residual M1/M2/M3/M4 at `:257-285`); quantitatively dead for E05/E06 shifted
  numerators (`door3_premise_gamma.lean:1233-1240`).
* `door3_complex_wendel.lean:102-146`: `sin_norm_le`
  (`‖sin z‖ ≤ 2 * exp |Im|`, closed); `:328-385`: `lower_inner` 0.38-scale +
  `inner_big` (explicit `exp` premise `Real.exp (Real.pi * 0.375) ≤ 3.3`); plus
  `:359-377` outer/leaf/mid envelopes (`0.000002 / 0.00004 / 0.0008`).
* `door3_digamma.lean:41-56`: psi-Stirling via integration ASSESSED STOP —
  needs Gauss rep (Mathlib TODO `Digamma.lean:31`) + Stirling remainder + log
  discs + tails (> 8 lemmas); banks conditional transport only, so it cannot
  serve a Gamma lower within budget.
* Hence NO Binet-leaf rate lemma is bankable this turn. Per brief, attempt
  E06 `N ≥ 2` below: `N = 2` ceiling audited with exact numerals; `N = 2`
  does NOT clear `0.66`, so no floor is closed — `N` needed is documented.

E06 shifted point: `s = w_E06 + 1 = 1.1975 + 0.625i` (shifted need `0.66`).
`GammaSeq s 2 = (2 : ℂ) ^ s * 2 / (s * (s + 1) * (s + 2))` in norm, so with an
optimistic cpow upper `‖(2 : ℂ) ^ s‖ ≤ 2.30` (`2 ^ 1.1975 ≈ 2.293`) and
optimistic Re denominator lowers `‖s + k‖ ≥ 1.1975 + k`, the ceiling is
`4.60 / 8.41 ≈ 0.547 < 0.66`. `N = 3` ceiling `22.38 / 35.31 ≈ 0.634 < 0.66`
is also dead; the first Re-ceiling that clears `0.66` is `N = 4`
(`126.24 / 183.56 ≈ 0.688 > 0.66`). True approximants sit below Re-ceilings
(Im widens denominators), so `N = 4` is a lower bound on `N` needed, not a
sufficiency claim. Nothing is forced: full `0.66` stays open.
-/

/-- E06 `N = 2` Re-product lower: `8.41 ≤ 1.1975 * 2.1975 * 3.1975`
(TRUE `≈ 8.41424`). -/
theorem premGamma_E06_N2_Reprod_lower :
    (8.41 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 := by
  norm_num

/-- E06 `N = 2` ceiling arithmetic: `4.60 / 8.41 < 0.66` (`≈ 0.547`). -/
theorem premGamma_E06_N2_ceiling_arith :
    (4.60 : ℝ) / 8.41 < 0.66 := by
  norm_num

/-- E06 `N = 3` Re-product lower: `35.31 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975`
(TRUE `≈ 35.31878`). -/
theorem premGamma_E06_N3_Reprod_lower :
    (35.31 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 := by
  norm_num

/-- E06 `N = 3` ceiling arithmetic: `22.38 / 35.31 < 0.66` (`≈ 0.634`). -/
theorem premGamma_E06_N3_ceiling_arith :
    (22.38 : ℝ) / 35.31 < 0.66 := by
  norm_num

/-- E06 `N = 4` Re-product lower: `183.56 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975`
(TRUE `≈ 183.569`). -/
theorem premGamma_E06_N4_Reprod_lower :
    (183.56 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 := by
  norm_num

/-- E06 `N = 4` ceiling arithmetic: first Re-ceiling clearing the floor
(`126.24 / 183.56 ≈ 0.688 > 0.66`). Necessity lower bound only. -/
theorem premGamma_E06_N4_ceiling_arith :
    (0.66 : ℝ) < 126.24 / 183.56 := by
  norm_num

/-- Missing link L1 at `N = 2` (filed, not proved): `GammaSeq s 2` norm identity
at E06 shifted `s = w_E06 + 1` with optimistic cpow numerator `2.30` shape.
Unfolds `Complex.GammaSeq s 2 = (2 : ℂ) ^ s * 2 / (s * (s + 1) * (s + 2))`
(`GammaSeq` at `Beta.lean:230`, `2 ! = 2`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. -/
def premGamma_E06_GammaSeq2_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2‖ =
    ‖(((2 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 2 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖)

/-- Missing rate L2 at `N = 2` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.015` (mirrors the `N = 1`
`premGamma_E06_GammaSeq_rate_needed`). Moot for the full floor: the `N = 2`
finite ceiling above already sits below `0.66`, so no rate closes `0.66`. -/
def premGamma_E06_GammaSeq2_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.015 : ℝ)

/-- E06 `N = 2` deadness of the scaffold lower: any finite upper at the
Re-ceiling plus any `0.015`-rate leaves `‖Seq‖ - ‖Seq - Gamma‖ < 0.66`, so the
`N = 2` Euler-product route cannot feed `premGamma_E06_ge_of_shift`.
Takes the finite ceiling as an explicit premise (derived from
`premGamma_E06_GammaSeq2_link` + cpow/Re premises in a future turn). -/
theorem premGamma_E06_N2_dead_of_upper
    (hSeqUpper : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2‖ ≤
      (4.60 : ℝ) / 8.41)
    (hRate : premGamma_E06_GammaSeq2_rate_needed) :
    ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2‖ -
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ <
      (0.66 : ℝ) := by
  unfold premGamma_E06_GammaSeq2_rate_needed at hRate
  have hceil : (4.60 : ℝ) / 8.41 < 0.66 := premGamma_E06_N2_ceiling_arith
  have hnn : (0 : ℝ) ≤ ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 2 -
      Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ :=
    norm_nonneg _
  linarith

/-! ## GAMMA-N4: E06 N = 4 approximant norm identity + rate spec (filed, not fixed).

Honesty check (exact arithmetic, Python-checked this turn): the N = 4 Re-ceiling
`126.24 / 183.56 ≈ 0.68773` clears `0.66` (`premGamma_E06_N4_ceiling_arith`
banked), so the ladder does NOT move to N = 5 for necessity. Product
`1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 ≈ 183.56935 ≥ 183.56`; cpow TRUEs
`2 ^ 1.1975 ≈ 2.29342 ≤ 2.30`, `3 ^ 1.1975 ≈ 3.72694 ≤ 3.73`,
`4 ^ 1.1975 ≈ 5.25977 ≤ 5.26` with `5.26 * 24 = 126.24` exact. Rate budget
`0.027`: `0.66 + 0.027 = 0.687 ≤ 126.24 / 183.56` (margin `≈ 0.00073`).
`0.688` is round-up only (`0.688 * 183.56 = 126.28928 > 126.24`), so `0.028`
is NOT banked; `0.027` is the filed budget. Sufficiency still open: the
ceiling is an approximant UPPER (needs cpow upper + denominator Re lowers);
the Gamma LOWER needs a finite Seq4 LOWER (needs cpow lower + denominator
norm uppers) plus the rate below — filed as explicit premises only.
-/

/-- Missing link L1 at `N = 4` (filed, not proved): `GammaSeq s 4` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 2` spec shape
(`premGamma_E06_GammaSeq2_link`). Unfolds
`Complex.GammaSeq s 4 = (4 : ℂ) ^ s * 24 / (s * (s+1) * (s+2) * (s+3) * (s+4))`
(`GammaSeq` at `Beta.lean:230`, `4 ! = 24`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. -/
def premGamma_E06_GammaSeq4_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4‖ =
    ‖(((4 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 24 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖)

/-- Cpow-upper requirement at `N = 4` (filed, not proved): optimistic-but-sound
`‖(4 : ℂ) ^ s‖ ≤ 5.26` at E06 shifted `s` (TRUE `4 ^ 1.1975 ≈ 5.25977`).
Feeds the Re-ceiling numerator `5.26 * 24 = 126.24` once `link` + Re lowers land. -/
def premGamma_E06_cpow4_upper_needed : Prop :=
  ‖(((4 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (5.26 : ℝ)

/-- Missing rate L2 at `N = 4` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.027` (`0.687 - 0.027 = 0.66`
exact; `0.687 ≤ 126.24 / 183.56` banked below). Host: a Stirling-disc /
Binet-enclosure leaf or an explicit `GammaSeq` rate lemma; NOT this file. -/
def premGamma_E06_GammaSeq4_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.027 : ℝ)

/-- E06 `N = 4` rate-budget arithmetic: `0.66 + 0.027 ≤ 126.24 / 183.56`
(`≈ 0.687 ≤ 0.68773`). The `0.688` headline is round-up; `0.027` is the sound
filed budget. -/
theorem premGamma_E06_N4_rate_budget_arith :
    (0.66 : ℝ) + 0.027 ≤ 126.24 / 183.56 := by
  norm_num

/-- E06 `N = 4` limit-closure conditional: finite Seq4 lower `0.687` plus rate
`0.027` gives the shifted floor `0.66` (`0.687 - 0.027 = 0.66` exact). Feeds
`premGamma_E06_ge_of_shift` once the Seq4 finite lower (from `link` + cpow
lower + denominator norm uppers) and the rate leaf land. -/
theorem premGamma_E06_Gamma_lower_of_Seq4_rate
    (hSeq : (0.687 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4‖)
    (hRate : premGamma_E06_GammaSeq4_rate_needed) :
    (0.66 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E06_GammaSeq4_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 4 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  linarith

/-- N-ladder cpow-upper requirements list for sufficiency auditing (filed, not
proved): which cpow norms at which point the ceiling leaf must bound. All at
E06 shifted `s = w_E06 + 1` (`Re s = 1.1975`): base `2` for `N = 2`
(TRUE `≈ 2.29342`), base `3` for `N = 3` (TRUE `≈ 3.72694`), base `4` for
`N = 4` (TRUE `≈ 5.25977`). Denominators are Re lowers
(`premGamma_E06_N4_Reprod_lower`); the Gamma LOWER additionally needs a cpow
LOWER + denominator norm uppers + `premGamma_E06_GammaSeq4_rate_needed` —
that lower is NOT claimed here. -/
def premGamma_E06_Nladder_cpow_uppers_needed : Prop :=
  (‖(((2 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (2.30 : ℝ)) ∧
  (‖(((3 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (3.73 : ℝ)) ∧
  (‖(((4 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (5.26 : ℝ))

/-! ## GAMMA-N4C: floor-truth triage + E05 N-ladder (filed, not fixed).

Floor-truth triage (non-rigorous arithmetic, triage only — NOT a proof):
* Stirling `|Gamma(x+iy)| ~= sqrt(2*pi) * |y|^(x-1/2) * e^(-pi*|y|/2)` at
  E06 shifted `s = 1.1975 + 0.625i` gives `~0.677 > 0.66`: floor TRUE (tight,
  margin `~0.017`). At E05 shifted `s = 1.1975 - 0.375i` gives `~0.702 > 0.645`:
  floor TRUE (margin `~0.057`).
* mpmath 50-dps cross-check (triage only): E06 TRUE `~0.72978` (headroom
  `1.106x`); E05 TRUE `~0.84242` (headroom `1.306x`). Stirling underestimates
  at these small `|y|` (large-`|y|` asymptotic), so both floors are TRUE with
  more headroom than Stirling suggests. NEITHER premise is UNCLOSABLE; no
  re-tiering needed on floor-truth grounds.
* E06 GammaSeq-N route is separately DEAD per `ses_f513fa90` (finite Seq4 max
  `~0.565` vs `0.687` gate; `0.687` was a ceiling, not achievable): floor-true
  but shape-dead. Do NOT retry E06 shapes.

E05 N-ladder vs `0.645` (same `Re = 1.1975` as E06, so Re-ceilings identical;
only the gate differs `0.645` vs `0.66`): `N = 1` ceiling `~0.380` dead;
`N = 2` ceiling `4.60 / 8.41 ~ 0.547` dead; `N = 3` ceiling
`22.38 / 35.31 ~ 0.634` dead; first Re-ceiling clearing the floor is `N = 4`
(`126.24 / 183.56 ~ 0.688 > 0.645`, necessity only). Link/rate specs filed
ONLY at `N = 4` below; nothing filed at `N = 1..3` beyond ceiling arithmetic.
Honesty (sweep note filed, not fixed): the ceiling is an approximant UPPER;
mpmath triage puts true Seq4 at E05 `~0.638 < 0.645` gate (Seq5 `~0.671`,
Seq6 `~0.695`), so `N = 4` sufficiency via shapes is expected-dead (mirrors
E06 N4C); `N >= 5` or a Binet leaf is needed for closure. Rate budget `0.042`
(`0.645 + 0.042 = 0.687 <= 126.24 / 183.56`) is the filed budget.
-/

/-- E05 `N = 1` Re-product lower: `2.63 ≤ 1.1975 * 2.1975`
(TRUE `≈ 2.63151`). -/
theorem premGamma_E05_N1_Reprod_lower :
    (2.63 : ℝ) ≤ 1.1975 * 2.1975 := by
  norm_num

/-- E05 `N = 1` ceiling arithmetic: `1 / 2.63 < 0.645` (`≈ 0.380`). -/
theorem premGamma_E05_N1_ceiling_arith :
    (1 : ℝ) / 2.63 < 0.645 := by
  norm_num

/-- E05 `N = 2` Re-product lower: `8.41 ≤ 1.1975 * 2.1975 * 3.1975`
(TRUE `≈ 8.41424`; same `Re` as E06). -/
theorem premGamma_E05_N2_Reprod_lower :
    (8.41 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 := by
  norm_num

/-- E05 `N = 2` ceiling arithmetic: `4.60 / 8.41 < 0.645` (`≈ 0.547`). -/
theorem premGamma_E05_N2_ceiling_arith :
    (4.60 : ℝ) / 8.41 < 0.645 := by
  norm_num

/-- E05 `N = 3` Re-product lower: `35.31 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975`
(TRUE `≈ 35.31878`). -/
theorem premGamma_E05_N3_Reprod_lower :
    (35.31 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 := by
  norm_num

/-- E05 `N = 3` ceiling arithmetic: `22.38 / 35.31 < 0.645` (`≈ 0.634`). -/
theorem premGamma_E05_N3_ceiling_arith :
    (22.38 : ℝ) / 35.31 < 0.645 := by
  norm_num

/-- E05 `N = 4` Re-product lower: `183.56 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975`
(TRUE `≈ 183.569`). -/
theorem premGamma_E05_N4_Reprod_lower :
    (183.56 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 := by
  norm_num

/-- E05 `N = 4` ceiling arithmetic: first Re-ceiling clearing the floor
(`126.24 / 183.56 ≈ 0.688 > 0.645`). Necessity lower bound only. -/
theorem premGamma_E05_N4_ceiling_arith :
    (0.645 : ℝ) < 126.24 / 183.56 := by
  norm_num

/-- Missing link L1 at `N = 4` (filed, not proved): `GammaSeq s 4` norm identity
at E05 shifted `s = w_E05 + 1`, extending the `N = 2` spec shape
(`premGamma_E06_GammaSeq2_link`). Unfolds
`Complex.GammaSeq s 4 = (4 : ℂ) ^ s * 24 / (s * (s+1) * (s+2) * (s+3) * (s+4))`
(`GammaSeq` at `Beta.lean:230`, `4 ! = 24`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at first-clearing `N = 4`. -/
def premGamma_E05_GammaSeq4_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4‖ =
    ‖(((4 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ * 24 /
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖)

/-- Cpow-upper requirement at `N = 4` (filed, not proved): optimistic-but-sound
`‖(4 : ℂ) ^ s‖ ≤ 5.26` at E05 shifted `s` (TRUE `4 ^ 1.1975 ≈ 5.25977`; same
`Re` as E06). Feeds the Re-ceiling numerator `5.26 * 24 = 126.24` once `link` +
Re lowers land. Filed ONLY at first-clearing `N = 4`. -/
def premGamma_E05_cpow4_upper_needed : Prop :=
  ‖(((4 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (5.26 : ℝ)

/-- Missing rate L2 at `N = 4` (filed, not proved): quantitative `GammaSeq`
convergence at E05 shifted point with budget `0.042` (`0.687 - 0.042 = 0.645`
exact; `0.687 ≤ 126.24 / 183.56` banked below). Host: a Stirling-disc /
Binet-enclosure leaf or an explicit `GammaSeq` rate lemma; NOT this file.
Filed ONLY at first-clearing `N = 4`. -/
def premGamma_E05_GammaSeq4_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.042 : ℝ)

/-- E05 `N = 4` rate-budget arithmetic: `0.645 + 0.042 ≤ 126.24 / 183.56`
(`≈ 0.687 ≤ 0.68767`). -/
theorem premGamma_E05_N4_rate_budget_arith :
    (0.645 : ℝ) + 0.042 ≤ 126.24 / 183.56 := by
  norm_num

/-- E05 `N = 4` limit-closure conditional: finite Seq4 lower `0.687` plus rate
`0.042` gives the shifted floor `0.645` (`0.687 - 0.042 = 0.645` exact). Feeds
`premGamma_E05_ge_of_shift` once the Seq4 finite lower (from `link` + cpow
lower + denominator norm uppers) and the rate leaf land. Sufficiency open:
true Seq4 `~0.638` triage sits below the `0.687` finite-lower premise, so this
conditional is NOT claimed closed. -/
theorem premGamma_E05_Gamma_lower_of_Seq4_rate
    (hSeq : (0.687 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4‖)
    (hRate : premGamma_E05_GammaSeq4_rate_needed) :
    (0.645 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E05_GammaSeq4_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 4 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  linarith

/-! ## GAMMA-N5: E05 N = 5 approximant norm identity + rate spec (filed, not fixed).

Honesty check (exact arithmetic, Python-checked this turn): the N = 5 Re-ceiling
`825.6 / 1137.66 ≈ 0.72570` clears `0.645`
(`premGamma_E05_N5_ceiling_arith` banked), so the ladder does NOT move to N = 6
for necessity. Product
`1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975 ≈ 1137.67102 ≥ 1137.66`;
cpow TRUE `5 ^ 1.1975 ≈ 6.87095 ≤ 6.88` (`6.87` would be FALSE, so `6.88` is the
filed upper) with `6.88 * 120 = 825.6` exact. Rate budget `0.08`:
`0.645 + 0.08 = 0.725 ≤ 825.6 / 1137.66` (margin `≈ 0.00070`;
`0.725 * 1137.66 = 824.8035 ≤ 825.6`). Sufficiency still open: the ceiling is
an approximant UPPER (needs cpow upper + denominator Re lowers); the Gamma
LOWER needs a finite Seq5 LOWER (needs cpow lower + denominator norm uppers)
plus the rate below — filed as explicit premises only. Sweep note (not fixed):
mpmath triage puts true Seq5 at E05 `~0.671 < 0.725` finite-lower premise, so
this maximal-`L` conditional is expected-dead for sufficiency (mirrors N = 4);
a closable leaf would need `L ≤ 0.671` or the N = 6 rung.
-/

/-- E05 `N = 5` Re-product lower:
`1137.66 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975`
(TRUE `≈ 1137.67102`). -/
theorem premGamma_E05_N5_Reprod_lower :
    (1137.66 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975 := by
  norm_num

/-- E05 `N = 5` ceiling arithmetic: Re-ceiling clearing the floor
(`825.6 / 1137.66 ≈ 0.72570 > 0.645`). Necessity lower bound only. -/
theorem premGamma_E05_N5_ceiling_arith :
    (0.645 : ℝ) < 825.6 / 1137.66 := by
  norm_num

/-- Missing link L1 at `N = 5` (filed, not proved): `GammaSeq s 5` norm identity
at E05 shifted `s = w_E05 + 1`, extending the `N = 4` spec shape
(`premGamma_E05_GammaSeq4_link`). Unfolds
`Complex.GammaSeq s 5 = (5 : ℂ) ^ s * 120 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5))`
(`GammaSeq` at `Beta.lean:230`, `5 ! = 120`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E05_GammaSeq5_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ =
    ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 /
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖)

/-- Cpow-upper requirement at `N = 5` (filed, not proved): optimistic-but-sound
`‖(5 : ℂ) ^ s‖ ≤ 6.88` at E05 shifted `s` (TRUE `5 ^ 1.1975 ≈ 6.87095`; `6.87`
is FALSE). Feeds the Re-ceiling numerator `6.88 * 120 = 825.6` once `link` +
Re lowers land. Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E05_cpow5_upper_needed : Prop :=
  ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (6.88 : ℝ)

/-- Missing rate L2 at `N = 5` (filed, not proved): quantitative `GammaSeq`
convergence at E05 shifted point with budget `0.08` (`0.725 - 0.08 = 0.645`
exact; `0.725 ≤ 825.6 / 1137.66` banked below). Host: a Stirling-disc /
Binet-enclosure leaf or an explicit `GammaSeq` rate lemma; NOT this file.
Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E05_GammaSeq5_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.08 : ℝ)

/-- E05 `N = 5` rate-budget arithmetic: `0.645 + 0.08 ≤ 825.6 / 1137.66`
(`≈ 0.725 ≤ 0.72570`). -/
theorem premGamma_E05_N5_rate_budget_arith :
    (0.645 : ℝ) + 0.08 ≤ 825.6 / 1137.66 := by
  norm_num

/-- E05 `N = 5` limit-closure conditional: finite Seq5 lower `0.725` plus rate
`0.08` gives the shifted floor `0.645` (`0.725 - 0.08 = 0.645` exact). Feeds
`premGamma_E05_ge_of_shift` once the Seq5 finite lower (from `link` + cpow
lower + denominator norm uppers) and the rate leaf land. Sufficiency open:
true Seq5 `~0.671` triage sits below the `0.725` finite-lower premise, so this
conditional is NOT claimed closed. -/
theorem premGamma_E05_Gamma_lower_of_Seq5_rate
    (hSeq : (0.725 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖)
    (hRate : premGamma_E05_GammaSeq5_rate_needed) :
    (0.645 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E05_GammaSeq5_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  linarith

/-! ## GAMMA-N5B: E05 N = 5 ACHIEVABLE finite lower + corrected closure (banked).

Audit (exact arithmetic, Python-checked this turn): the dead `0.725` finite
premise above is superseded (kept, not deleted) by an achievable finite lower.
At E05 shifted `s = w_E05 / 2 + 1` (`Re s = 1.1975`, `Im s = -0.375`):
* cpow lower: `‖(5 : ℂ) ^ s‖ = 5 ^ 1.1975 ≥ 6.8` (TRUE `≈ 6.87095`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `5 ^ 1.1975 = 5 * 5 ^ 0.1975 ≥
  5 * 5 ^ (5/26) ≥ 5 * 1.36 = 6.8` (`5/26 ≤ 0.1975`; `1.36^26 = 2964.91 ≤
  3125 = 5^5`, all `norm_num`).
* denominator norm uppers (`sq_norm` shapes, extending banked `‖s‖ ≤ 1.26`,
  `‖s+1‖ ≤ 2.23`): `‖s+2‖ ≤ 3.22` (`3.1975^2 + 0.375^2 = 10.36463125 ≤
  3.22^2`), `‖s+3‖ ≤ 4.22`, `‖s+4‖ ≤ 5.22`, `‖s+5‖ ≤ 6.21`; product
  `1.26 * 2.23 * 3.22 * 4.22 * 5.22 * 6.21 = 1237.672763886384 ≤ 1237.68`.
* quotient: `120 * 6.8 / 1237.68 = 816 / 1237.68 ≈ 0.65929804 ∈ [0.645, 0.671]`
  — achievable (`≤` true Seq5 `~0.67146`) and clearing the gate. Filed finite
  `L = 0.659` (`0.659 * 1237.68 = 815.63112 ≤ 816`).
* corrected closure: finite `0.659` + rate budget `0.014` (`0.659 - 0.014 =
  0.645` exact) gives the shifted floor `0.645`.
-/

/-- E05 `5 ^ (5/26)` integer-root lower: `1.36 ≤ 5 ^ (5/26)`
(`1.36^26 = 2964.91 ≤ 3125 = 5^5`; `5 ^ (5/26) ≈ 1.36275`). -/
theorem premGamma_E05_rpow5_frac_lower :
    (1.36 : ℝ) ≤ (5 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((5 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (5 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.36 : ℝ) ^ (26 : ℕ) ≤ (((5 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _) hint

/-- E05 `5 ^ 1.1975` lower: `6.8 ≤ 5 ^ 1.1975` (TRUE `≈ 6.87095`).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`5 * 1.36 = 6.8`). -/
theorem premGamma_E05_rpow5_Re_lower :
    (6.8 : ℝ) ≤ (5 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (5 : ℝ) ^ ((5 / 26) : ℝ) ≤ (5 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hfrac
  have h136 : (1.36 : ℝ) ≤ (5 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E05_rpow5_frac_lower hmono
  have h68 : (6.8 : ℝ) = 5 * 1.36 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 5 by norm_num), Real.rpow_one, h68]
  exact mul_le_mul_of_nonneg_left h136 (by norm_num : (0 : ℝ) ≤ 5)

/-- E05 shifted cpow norm lower: `6.8 ≤ ‖(5 : ℂ) ^ s‖` at `s = w_E05 / 2 + 1`. -/
theorem premGamma_E05_cpow5_norm_lower :
    (6.8 : ℝ) ≤ ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((5 : ℝ) : ℂ) = (5 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 5 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E05_rpow5_Re_lower

/-- E05 shifted `s+2` norm: `‖(w_E05 + 1) + 1 + 1‖ ≤ 3.22`
(TRUE `≈ 3.2194`; `3.1975^2 + 0.375^2 = 10.36463125 ≤ 3.22^2`). -/
theorem premGamma_E05shift_add2_norm_le :
    ‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ ≤ (3.22 : ℝ) := by
  have hre : ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
      = (3.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ ^ 2
      ≤ (3.22 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.22 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 shifted `s+3` norm: `‖s + 3‖ ≤ 4.22`
(TRUE `≈ 4.2142`; `4.1975^2 + 0.375^2 = 17.75963125 ≤ 4.22^2`). -/
theorem premGamma_E05shift_add3_norm_le :
    ‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ ≤ (4.22 : ℝ) := by
  have hre : (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
      = (4.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (4.22 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.22 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 shifted `s+4` norm: `‖s + 4‖ ≤ 5.22`
(TRUE `≈ 5.2110`; `5.1975^2 + 0.375^2 = 27.15463125 ≤ 5.22^2`). -/
theorem premGamma_E05shift_add4_norm_le :
    ‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ ≤ (5.22 : ℝ) := by
  have hre : ((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
      = (5.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (5.22 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (5.22 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 shifted `s+5` norm: `‖s + 5‖ ≤ 6.21`
(TRUE `≈ 6.2088`; `6.1975^2 + 0.375^2 = 38.54963125 ≤ 6.21^2`). -/
theorem premGamma_E05shift_add5_norm_le :
    ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ ≤ (6.21 : ℝ) := by
  have hre : (((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
      = (6.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (6.21 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (6.21 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E05 `N = 5` denominator norm-product upper, right-nested to match
`premGamma_E05_GammaSeq5_link` (`1237.672763886384 ≤ 1237.68`). -/
theorem premGamma_E05_prod5_le :
    ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖)))) ≤
      (1237.68 : ℝ) := by
  have h45 := mul_le_mul premGamma_E05shift_add4_norm_le premGamma_E05shift_add5_norm_le
    (norm_nonneg _) (by norm_num)
  have h345 := mul_le_mul premGamma_E05shift_add3_norm_le h45
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h2345 := mul_le_mul premGamma_E05shift_add2_norm_le h345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h12345 := mul_le_mul premGamma_E05shift_succ_norm_le h2345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h012345 := mul_le_mul premGamma_E05shift_norm_le h12345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have heq : (1.26 : ℝ) * (2.23 * (3.22 * (4.22 * (5.22 * 6.21)))) = 1237.672763886384 := by
    norm_num
  rw [heq] at h012345
  exact le_trans h012345 (by norm_num : (1237.672763886384 : ℝ) ≤ 1237.68)

/-- E05 `N = 5` ACHIEVABLE finite lower: `0.659 ≤ ‖GammaSeq s 5‖`, conditional
on the filed `N = 5` link identity. From cpow lower `6.8` + denominator upper
`1237.68` (`0.659 * 1237.68 = 815.63112 ≤ 816 = 6.8 * 120`). -/
theorem premGamma_E05_Seq5_finite_lower (hLink : premGamma_E05_GammaSeq5_link) :
    (0.659 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ := by
  unfold premGamma_E05_GammaSeq5_link at hLink
  have hRight := premGamma_E05_prod5_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) ≤
      (1237.68 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 hpos5))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E05_cpow5_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.659 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.659 * 1237.68 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.659)
  have h2 : (6.8 : ℝ) * 120 ≤
      ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 120)
  have h3 : (0.659 : ℝ) * 1237.68 ≤ 6.8 * 120 := by norm_num
  linarith

/-- Corrected rate L2 at `N = 5` (filed, not proved): quantitative `GammaSeq`
convergence at E05 shifted point with budget `0.014` (`0.659 - 0.014 = 0.645`
exact). Supersedes `premGamma_E05_GammaSeq5_rate_needed` (`0.08`, tied to the
dead `0.725` finite premise); host is the same Stirling-disc / Binet-enclosure
leaf, NOT this file. -/
def premGamma_E05_GammaSeq5_rate_needed_corr : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E05 `N = 5` corrected rate-budget arithmetic: `0.645 + 0.014 ≤ 816 / 1237.68`
(`≈ 0.659 ≤ 0.65929804`). -/
theorem premGamma_E05_N5_rate_budget_corr_arith :
    (0.645 : ℝ) + 0.014 ≤ 816 / 1237.68 := by
  norm_num

/-- E05 `N = 5` corrected limit-closure conditional: achievable finite Seq5
lower `0.659` plus rate `0.014` gives the shifted floor `0.645`
(`0.659 - 0.014 = 0.645` exact). Feeds `premGamma_E05_ge_of_shift` once the
`N = 5` link unfolds and the corrected rate leaf lands. Unlike the `0.725`
conditional above, the finite premise here is banked achievable
(`premGamma_E05_Seq5_finite_lower`). -/
theorem premGamma_E05_Gamma_lower_of_Seq5_rate_corr
    (hSeq : (0.659 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖)
    (hRate : premGamma_E05_GammaSeq5_rate_needed_corr) :
    (0.645 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E05_GammaSeq5_rate_needed_corr at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  linarith

/-! ## GAMMA-N5-E06: E06 N = 5 approximant norm identity + rate spec (filed, not fixed).

Mirrors the E05 `N = 5` scaffold token-for-token (`premGamma_E05_N5_Reprod_lower`,
`premGamma_E05_N5_ceiling_arith`, `premGamma_E05_GammaSeq5_link`,
`premGamma_E05_cpow5_upper_needed`, `premGamma_E05_GammaSeq5_rate_needed`,
`premGamma_E05_N5_rate_budget_arith`, `premGamma_E05_Gamma_lower_of_Seq5_rate`).

Honesty check (exact arithmetic): the `N = 5` Re-ceiling is shared with E05
(same `Re = 1.1975`): `825.6 / 1137.66 ≈ 0.72570` clears `0.66`
(`premGamma_E06_N5_ceiling_arith` banked), so the ladder does NOT move to
`N = 6` for necessity. Product
`1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975 ≈ 1137.67102 ≥ 1137.66`;
cpow TRUE `5 ^ 1.1975 ≈ 6.87095 ≤ 6.88` (`6.87` would be FALSE, so `6.88` is the
filed upper) with `6.88 * 120 = 825.6` exact. Rate budget `0.065` (`≤ 0.08`-style):
`0.66 + 0.065 = 0.725 ≤ 825.6 / 1137.66` (margin `≈ 0.00070`;
`0.725 * 1137.66 = 824.8035 ≤ 825.6`). Sufficiency still open: the ceiling is
an approximant UPPER (needs cpow upper + denominator Re lowers); the Gamma
LOWER needs a finite Seq5 LOWER (needs cpow lower + denominator norm uppers)
plus the rate below — filed as explicit premises only. Achievable-lower audit
is in GAMMA-N5B-E06 below (honest `0.579 < 0.66`, gap `0.081`).
-/

/-- E06 `N = 5` Re-product lower:
`1137.66 ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975`
(TRUE `≈ 1137.67102`; same `Re` as E05). -/
theorem premGamma_E06_N5_Reprod_lower :
    (1137.66 : ℝ) ≤ 1.1975 * 2.1975 * 3.1975 * 4.1975 * 5.1975 * 6.1975 := by
  norm_num

/-- E06 `N = 5` ceiling arithmetic: Re-ceiling clearing the floor
(`825.6 / 1137.66 ≈ 0.72570 > 0.66`). Necessity lower bound only. -/
theorem premGamma_E06_N5_ceiling_arith :
    (0.66 : ℝ) < 825.6 / 1137.66 := by
  norm_num

/-- Missing link L1 at `N = 5` (filed, not proved): `GammaSeq s 5` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 4` spec shape
(`premGamma_E06_GammaSeq4_link`). Unfolds
`Complex.GammaSeq s 5 = (5 : ℂ) ^ s * 120 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5))`
(`GammaSeq` at `Beta.lean:230`, `5 ! = 120`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E06_GammaSeq5_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5‖ =
    ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖)

/-- Cpow-upper requirement at `N = 5` (filed, not proved): optimistic-but-sound
`‖(5 : ℂ) ^ s‖ ≤ 6.88` at E06 shifted `s` (TRUE `5 ^ 1.1975 ≈ 6.87095`; `6.87`
is FALSE; same `Re` as E05). Feeds the Re-ceiling numerator `6.88 * 120 = 825.6`
once `link` + Re lowers land. Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E06_cpow5_upper_needed : Prop :=
  ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (6.88 : ℝ)

/-- Missing rate L2 at `N = 5` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.065` (`0.725 - 0.065 = 0.66`
exact; `0.725 ≤ 825.6 / 1137.66` banked below). Host: a Stirling-disc /
Binet-enclosure leaf or an explicit `GammaSeq` rate lemma; NOT this file.
Filed ONLY at `N = 5` alongside N = 4. -/
def premGamma_E06_GammaSeq5_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.065 : ℝ)

/-- E06 `N = 5` rate-budget arithmetic: `0.66 + 0.065 ≤ 825.6 / 1137.66`
(`≈ 0.725 ≤ 0.72570`). -/
theorem premGamma_E06_N5_rate_budget_arith :
    (0.66 : ℝ) + 0.065 ≤ 825.6 / 1137.66 := by
  norm_num

/-- E06 `N = 5` limit-closure conditional: finite Seq5 lower `0.725` plus rate
`0.065` gives the shifted floor `0.66` (`0.725 - 0.065 = 0.66` exact). Feeds
`premGamma_E06_ge_of_shift` once the Seq5 finite lower (from `link` + cpow
lower + denominator norm uppers) and the rate leaf land. Sufficiency open:
see GAMMA-N5B-E06 honest `0.579` audit below; this maximal-`L` conditional is
NOT claimed closed. -/
theorem premGamma_E06_Gamma_lower_of_Seq5_rate
    (hSeq : (0.725 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5‖)
    (hRate : premGamma_E06_GammaSeq5_rate_needed) :
    (0.66 : ℝ) ≤
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
  unfold premGamma_E06_GammaSeq5_rate_needed at hRate
  have htri : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5‖ ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ +
      ‖Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ := by
    have h := norm_add_le
      (Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5 -
        Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
      (Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)))
    rw [sub_add_cancel] at h
    exact h
  linarith

/-! ## GAMMA-N5B-E06: E06 N = 5 HONEST achievable finite lower (banked, fails gate).

Mirrors the E05 `N = 5` achievable block token-for-token
(`premGamma_E05_rpow5_frac_lower`, `premGamma_E05_rpow5_Re_lower`,
`premGamma_E05_cpow5_norm_lower`, `premGamma_E05shift_add2_norm_le`,
`premGamma_E05shift_add3_norm_le`, `premGamma_E05shift_add4_norm_le`,
`premGamma_E05shift_add5_norm_le`, `premGamma_E05_prod5_le`,
`premGamma_E05_Seq5_finite_lower`).

Audit (exact arithmetic, banked windows only — no mpmath estimate fixed):
At E06 shifted `s = w_E06 / 2 + 1` (`Re s = 1.1975`, `Im s = 0.625`):
* cpow lower: `‖(5 : ℂ) ^ s‖ = 5 ^ 1.1975 ≥ 6.8` (TRUE `≈ 6.87095`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `5 ^ 1.1975 = 5 * 5 ^ 0.1975 ≥
  5 * 5 ^ (5/26) ≥ 5 * 1.36 = 6.8` (`5/26 ≤ 0.1975`; `1.36^26 = 2964.91 ≤
  3125 = 5^5`, all `norm_num`; same `Re` as E05).
* denominator norm uppers (`sq_norm` shapes, extending banked `‖s‖ ≤ 1.36`,
  `‖s+1‖ ≤ 2.29`): `‖s+2‖ ≤ 3.26` (`3.1975^2 + 0.625^2 = 10.61463125 ≤
  3.26^2`), `‖s+3‖ ≤ 4.25`, `‖s+4‖ ≤ 5.24`, `‖s+5‖ ≤ 6.23`; product
  `1.36 * 2.29 * 3.26 * 4.25 * 5.24 * 6.23 = 1408.6407717424 ≤ 1408.65`.
* quotient: `120 * 6.8 / 1408.65 = 816 / 1408.65 ≈ 0.57928 < 0.66`
  — honest achievable (`0.579 * 1408.65 = 815.60835 ≤ 816`).
* verdict: FAILS to clear `0.66` (gap `0.081`: `0.579 + 0.081 = 0.66` exact;
  `816 / 1408.65 < 0.66` banked). Do NOT force: file `N = 6` as next rung;
  no `N = 6` numerals are banked this turn.
-/

/-- E06 `5 ^ (5/26)` integer-root lower: `1.36 ≤ 5 ^ (5/26)`
(`1.36^26 = 2964.91 ≤ 3125 = 5^5`; same `Re`-only lemma as E05). -/
theorem premGamma_E06_rpow5_frac_lower :
    (1.36 : ℝ) ≤ (5 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((5 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (5 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.36 : ℝ) ^ (26 : ℕ) ≤ (((5 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _) hint

/-- E06 `5 ^ 1.1975` lower: `6.8 ≤ 5 ^ 1.1975` (TRUE `≈ 6.87095`; same `Re` as E05).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`5 * 1.36 = 6.8`). -/
theorem premGamma_E06_rpow5_Re_lower :
    (6.8 : ℝ) ≤ (5 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (5 : ℝ) ^ ((5 / 26) : ℝ) ≤ (5 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hfrac
  have h136 : (1.36 : ℝ) ≤ (5 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E06_rpow5_frac_lower hmono
  have h68 : (6.8 : ℝ) = 5 * 1.36 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 5 by norm_num), Real.rpow_one, h68]
  exact mul_le_mul_of_nonneg_left h136 (by norm_num : (0 : ℝ) ≤ 5)

/-- E06 shifted cpow norm lower: `6.8 ≤ ‖(5 : ℂ) ^ s‖` at `s = w_E06 / 2 + 1`. -/
theorem premGamma_E06_cpow5_norm_lower :
    (6.8 : ℝ) ≤ ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((5 : ℝ) : ℂ) = (5 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 5 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E06_rpow5_Re_lower

/-- E06 shifted `s+2` norm: `‖(w_E06 + 1) + 1 + 1‖ ≤ 3.26`
(TRUE `≈ 3.2583`; `3.1975^2 + 0.625^2 = 10.61463125 ≤ 3.26^2`). -/
theorem premGamma_E06shift_add2_norm_le :
    ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ ≤ (3.26 : ℝ) := by
  have hre : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
      = (3.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ ^ 2
      ≤ (3.26 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (3.26 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 shifted `s+3` norm: `‖s + 3‖ ≤ 4.25`
(TRUE `≈ 4.2439`; `4.1975^2 + 0.625^2 = 18.00963125 ≤ 4.25^2`). -/
theorem premGamma_E06shift_add3_norm_le :
    ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ ≤ (4.25 : ℝ) := by
  have hre : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
      = (4.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (4.25 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (4.25 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 shifted `s+4` norm: `‖s + 4‖ ≤ 5.24`
(TRUE `≈ 5.2350`; `5.1975^2 + 0.625^2 = 27.40463125 ≤ 5.24^2`). -/
theorem premGamma_E06shift_add4_norm_le :
    ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ ≤ (5.24 : ℝ) := by
  have hre : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
      = (5.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (5.24 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (5.24 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 shifted `s+5` norm: `‖s + 5‖ ≤ 6.23`
(TRUE `≈ 6.2289`; `6.1975^2 + 0.625^2 = 38.79963125 ≤ 6.23^2`). -/
theorem premGamma_E06shift_add5_norm_le :
    ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ ≤ (6.23 : ℝ) := by
  have hre : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
      = (6.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ ^ 2
      ≤ (6.23 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (6.23 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 5` denominator norm-product upper, right-nested to match
`premGamma_E06_GammaSeq5_link` (`1408.6407717424 ≤ 1408.65`). -/
theorem premGamma_E06_prod5_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖)))) ≤
      (1408.65 : ℝ) := by
  have h45 := mul_le_mul premGamma_E06shift_add4_norm_le premGamma_E06shift_add5_norm_le
    (norm_nonneg _) (by norm_num)
  have h345 := mul_le_mul premGamma_E06shift_add3_norm_le h45
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h2345 := mul_le_mul premGamma_E06shift_add2_norm_le h345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h12345 := mul_le_mul premGamma_E06shift_succ_norm_le h2345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h012345 := mul_le_mul premGamma_E06shift_norm_le h12345
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have heq : (1.36 : ℝ) * (2.29 * (3.26 * (4.25 * (5.24 * 6.23)))) = 1408.6407717424 := by
    norm_num
  rw [heq] at h012345
  exact le_trans h012345 (by norm_num : (1408.6407717424 : ℝ) ≤ 1408.65)

/-- E06 `N = 5` HONEST finite lower: `0.579 ≤ ‖GammaSeq s 5‖`, conditional
on the filed `N = 5` link identity. From cpow lower `6.8` + denominator upper
`1408.65` (`0.579 * 1408.65 = 815.60835 ≤ 816 = 6.8 * 120`). Below the `0.66`
gate: do NOT feed `premGamma_E06_ge_of_shift`. -/
theorem premGamma_E06_Seq5_finite_lower (hLink : premGamma_E06_GammaSeq5_link) :
    (0.579 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 5‖ := by
  unfold premGamma_E06_GammaSeq5_link at hLink
  have hRight := premGamma_E06_prod5_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) ≤
      (1408.65 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 hpos5))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E06_cpow5_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.579 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.579 * 1408.65 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.579)
  have h2 : (6.8 : ℝ) * 120 ≤
      ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 120)
  have h3 : (0.579 : ℝ) * 1408.65 ≤ 6.8 * 120 := by norm_num
  linarith

/-- E06 `N = 5` honest-ceiling gap: `816 / 1408.65 < 0.66`
(`≈ 0.57928 < 0.66`). The honest achievable quotient fails the gate. -/
theorem premGamma_E06_N5_honest_ceiling_below_gate :
    (816 : ℝ) / 1408.65 < 0.66 := by
  norm_num

/-- E06 `N = 5` gap arithmetic: `0.579 + 0.081 = 0.66` exact. -/
theorem premGamma_E06_N5_gap_arith :
    (0.579 : ℝ) + 0.081 = 0.66 := by
  norm_num

/-- E06 `N = 6` next rung (filed, not fixed): the `N = 5` honest lower `0.579`
sits `0.081` below `0.66`, so sufficiency is NOT closed here. Do NOT force;
the ladder moves to `N = 6` (no `N = 6` numerals banked this turn). -/
def premGamma_E06_N6_next : Prop :=
  (0.579 : ℝ) < 0.66

/-! ## GAMMA-N6B-E06: E06 N = 6 HONEST achievable finite lower (banked, fails gate).

Mirrors the E06 `N = 5` honest block token-for-token
(`premGamma_E06_rpow5_frac_lower`, `premGamma_E06_rpow5_Re_lower`,
`premGamma_E06_cpow5_norm_lower`, `premGamma_E06shift_add2_norm_le`,
`premGamma_E06shift_add3_norm_le`, `premGamma_E06shift_add4_norm_le`,
`premGamma_E06shift_add5_norm_le`, `premGamma_E06_prod5_le`,
`premGamma_E06_Seq5_finite_lower`).

Audit (exact arithmetic, banked windows only — no mpmath estimate fixed):
At E06 shifted `s = w_E06 + 1` (`Re s = 1.1975`, `Im s = 0.625`):
* cpow lower: `‖(6 : ℂ) ^ s‖ = 6 ^ 1.1975 ≥ 8.46` (TRUE `≈ 8.54744`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `6 ^ 1.1975 = 6 * 6 ^ 0.1975 ≥
  6 * 6 ^ (5/26) ≥ 6 * 1.41 = 8.46` (`5/26 ≤ 0.1975`; `1.41^26 ≈ 7580.48 ≤
  7776 = 6^5`, all `norm_num`; `1.42` would be FALSE).
* cpow upper spec (filed, not proved): `‖(6 : ℂ) ^ s‖ ≤ 8.56` (TRUE `≈ 8.54744`).
* denominator norm uppers (`sq_norm` shapes, extending banked `‖s‖ ≤ 1.36`,
  `‖s+1‖ ≤ 2.29`, `‖s+2‖ ≤ 3.26`, `‖s+3‖ ≤ 4.25`, `‖s+4‖ ≤ 5.24`,
  `‖s+5‖ ≤ 6.23`): `‖s+6‖ ≤ 7.23` (`7.1975^2 + 0.625^2 = 52.19463125 ≤
  7.23^2`); product
  `1.36 * 2.29 * 3.26 * 4.25 * 5.24 * 6.23 * 7.23 = 10184.472779697552 ≤ 10184.54`.
* quotient: `720 * 8.46 / 10184.54 = 6091.2 / 10184.54 ≈ 0.59808 < 0.66`
  — honest achievable (`0.598 * 10184.54 = 6090.35492 ≤ 6091.2`).
* verdict: FAILS to clear `0.66` (gap `0.062`: `0.598 + 0.062 = 0.66` exact;
  `6091.2 / 10184.54 < 0.66` banked). Do NOT force: file `N = 7` as next rung;
  no `N = 7` numerals are banked this turn.
-/

/-- E06 `6 ^ (5/26)` integer-root lower: `1.41 ≤ 6 ^ (5/26)`
(`1.41^26 ≈ 7580.48 ≤ 7776 = 6^5`). -/
theorem premGamma_E06_rpow6_frac_lower :
    (1.41 : ℝ) ≤ (6 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((6 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (6 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.41 : ℝ) ^ (26 : ℕ) ≤ (((6 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) _) hint

/-- E06 `6 ^ 1.1975` lower: `8.46 ≤ 6 ^ 1.1975` (TRUE `≈ 8.54744`).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`6 * 1.41 = 8.46`). -/
theorem premGamma_E06_rpow6_Re_lower :
    (8.46 : ℝ) ≤ (6 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (6 : ℝ) ^ ((5 / 26) : ℝ) ≤ (6 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) hfrac
  have h141 : (1.41 : ℝ) ≤ (6 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E06_rpow6_frac_lower hmono
  have h846 : (8.46 : ℝ) = 6 * 1.41 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 6 by norm_num), Real.rpow_one, h846]
  exact mul_le_mul_of_nonneg_left h141 (by norm_num : (0 : ℝ) ≤ 6)

/-- E06 shifted cpow norm lower: `8.46 ≤ ‖(6 : ℂ) ^ s‖` at `s = w_E06 + 1`. -/
theorem premGamma_E06_cpow6_norm_lower :
    (8.46 : ℝ) ≤ ‖(((6 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((6 : ℝ) : ℂ) = (6 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 6 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E06_rpow6_Re_lower

/-- Cpow-upper requirement at `N = 6` (filed, not proved): optimistic-but-sound
`‖(6 : ℂ) ^ s‖ ≤ 8.56` at E06 shifted `s` (TRUE `6 ^ 1.1975 ≈ 8.54744`).
Feeds the `N = 6` Re-ceiling numerator `8.56 * 720 = 6163.2`
once `link` + Re lowers land. Filed ONLY at `N = 6`. -/
def premGamma_E06_cpow6_upper_needed : Prop :=
  ‖(((6 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (8.56 : ℝ)

/-- E06 shifted `s+6` norm: `‖s + 6‖ ≤ 7.23`
(TRUE `≈ 7.22458`; `7.1975^2 + 0.625^2 = 52.19463125 ≤ 7.23^2`). -/
theorem premGamma_E06shift_add6_norm_le :
    ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ≤ (7.23 : ℝ) := by
  have hre : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
      = (7.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ^ 2
      ≤ (7.23 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (7.23 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 6` denominator norm-product upper, right-nested to match
`premGamma_E06_GammaSeq6_link` (`10184.472779697552 ≤ 10184.54`). -/
theorem premGamma_E06_prod6_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) ≤
      (10184.54 : ℝ) := by
  have h56 := mul_le_mul premGamma_E06shift_add5_norm_le premGamma_E06shift_add6_norm_le
    (norm_nonneg _) (by norm_num)
  have h456 := mul_le_mul premGamma_E06shift_add4_norm_le h56
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h3456 := mul_le_mul premGamma_E06shift_add3_norm_le h456
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h23456 := mul_le_mul premGamma_E06shift_add2_norm_le h3456
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h123456 := mul_le_mul premGamma_E06shift_succ_norm_le h23456
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have h0123456 := mul_le_mul premGamma_E06shift_norm_le h123456
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))) (by norm_num)
  have heq : (1.36 : ℝ) * (2.29 * (3.26 * (4.25 * (5.24 * (6.23 * 7.23))))) = 10184.472779697552 := by
    norm_num
  rw [heq] at h0123456
  exact le_trans h0123456 (by norm_num : (10184.472779697552 : ℝ) ≤ 10184.54)

/-- Missing link L1 at `N = 6` (filed, not proved): `GammaSeq s 6` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 5` spec shape
(`premGamma_E06_GammaSeq5_link`). Unfolds
`Complex.GammaSeq s 6 = (6 : ℂ) ^ s * 720 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5) * (s+6))`
(`GammaSeq` at `Beta.lean:230`, `6 ! = 720`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 6`. -/
def premGamma_E06_GammaSeq6_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 6‖ =
    ‖(((6 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 720 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖)

/-- Missing rate L2 at `N = 6` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.014` (same host-leaf shape as
`premGamma_E05_GammaSeq5_rate_needed_corr`; `0.598 - 0.014 = 0.584 < 0.66`,
so no closure). Host: a Stirling-disc / Binet-enclosure leaf or an explicit
`GammaSeq` rate lemma; NOT this file. Filed ONLY at `N = 6`. -/
def premGamma_E06_GammaSeq6_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 6 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E06 `N = 6` HONEST finite lower: `0.598 ≤ ‖GammaSeq s 6‖`, conditional
on the filed `N = 6` link identity. From cpow lower `8.46` + denominator upper
`10184.54` (`0.598 * 10184.54 = 6090.35492 ≤ 6091.2 = 8.46 * 720`). Below the `0.66`
gate: do NOT feed `premGamma_E06_ge_of_shift`. -/
theorem premGamma_E06_Seq6_finite_lower (hLink : premGamma_E06_GammaSeq6_link) :
    (0.598 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 6‖ := by
  unfold premGamma_E06_GammaSeq6_link at hLink
  have hRight := premGamma_E06_prod6_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      (10184.54 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hpos6 : (0 : ℝ) < ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre6 : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (7.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre6] at h
    have habs : |(7.1975 : ℝ)| = 7.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 7.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 (mul_pos hpos5 hpos6)))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E06_cpow6_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.598 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.598 * 10184.54 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.598)
  have h2 : (8.46 : ℝ) * 720 ≤
      ‖(((6 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 720 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 720)
  have h3 : (0.598 : ℝ) * 10184.54 ≤ 8.46 * 720 := by norm_num
  linarith

/-- E06 `N = 6` honest-ceiling gap: `6091.2 / 10184.54 < 0.66`
(`≈ 0.59808 < 0.66`). The honest achievable quotient fails the gate. -/
theorem premGamma_E06_N6_honest_ceiling_below_gate :
    (6091.2 : ℝ) / 10184.54 < 0.66 := by
  norm_num

/-- E06 `N = 6` gap arithmetic: `0.598 + 0.062 = 0.66` exact. -/
theorem premGamma_E06_N6_gap_arith :
    (0.598 : ℝ) + 0.062 = 0.66 := by
  norm_num

/-- E06 `N = 7` next rung (filed, not fixed): the `N = 6` honest lower `0.598`
sits `0.062` below `0.66`, so sufficiency is NOT closed here. Do NOT force;
the ladder moves to `N = 7` (no `N = 7` numerals banked this turn). -/
def premGamma_E06_N7_next : Prop :=
  (0.598 : ℝ) < 0.66

/-! ## GAMMA-N7-E06: E06 N = 7 HONEST achievable finite lower (banked, fails gate).

Mirrors the E06 `N = 6` honest block token-for-token
(`premGamma_E06_rpow6_frac_lower`, `premGamma_E06_rpow6_Re_lower`,
`premGamma_E06_cpow6_norm_lower`, `premGamma_E06_cpow6_upper_needed`,
`premGamma_E06shift_add6_norm_le`, `premGamma_E06_prod6_le`,
`premGamma_E06_GammaSeq6_link`, `premGamma_E06_GammaSeq6_rate_needed`,
`premGamma_E06_Seq6_finite_lower`).

Audit (exact arithmetic, banked windows only — no mpmath estimate fixed):
At E06 shifted `s = w_E06 + 1` (`Re s = 1.1975`, `Im s = 0.625`):
* cpow lower: `‖(7 : ℂ) ^ s‖ = 7 ^ 1.1975 ≥ 10.15` (TRUE `≈ 10.28027`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `7 ^ 1.1975 = 7 * 7 ^ 0.1975 ≥
  7 * 7 ^ (5/26) ≥ 7 * 1.45 = 10.15` (`5/26 ≤ 0.1975`; `1.45^26 ≈ 15688.01 ≤
  16807 = 7^5`, all `norm_num`; `1.46` would be FALSE).
* cpow upper spec (filed, not proved): `‖(7 : ℂ) ^ s‖ ≤ 10.29` (TRUE `≈ 10.28027`).
* denominator norm uppers (`sq_norm` shapes, extending banked `‖s‖ ≤ 1.36`,
  `‖s+1‖ ≤ 2.29`, `‖s+2‖ ≤ 3.26`, `‖s+3‖ ≤ 4.25`, `‖s+4‖ ≤ 5.24`,
  `‖s+5‖ ≤ 6.23`, `‖s+6‖ ≤ 7.23`): `‖s+7‖ ≤ 8.23` (`8.1975^2 + 0.625^2 =
  67.58963125 ≤ 8.23^2`); product
  `1.36 * 2.29 * 3.26 * 4.25 * 5.24 * 6.23 * 7.23 * 8.23 = 83818.21097691085296 ≤
  83818.22` (`prod7 = prod6 * ‖s+7‖`).
* quotient: `5040 * 10.15 / 83818.22 = 51156 / 83818.22 ≈ 0.61032 < 0.66`
  — honest achievable (`0.61 * 83818.22 = 51129.1142 ≤ 51156`).
* verdict: FAILS to clear `0.66` (gap `0.05`: `0.61 + 0.05 = 0.66` exact;
  `51156 / 83818.22 < 0.66` banked). Do NOT force: file `N = 8` as next rung;
  no `N = 8` numerals are banked this turn.
-/

/-- E06 `7 ^ (5/26)` integer-root lower: `1.45 ≤ 7 ^ (5/26)`
(`1.45^26 ≈ 15688.01 ≤ 16807 = 7^5`). -/
theorem premGamma_E06_rpow7_frac_lower :
    (1.45 : ℝ) ≤ (7 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((7 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (7 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.45 : ℝ) ^ (26 : ℕ) ≤ (((7 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 7) _) hint

/-- E06 `7 ^ 1.1975` lower: `10.15 ≤ 7 ^ 1.1975` (TRUE `≈ 10.28027`).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`7 * 1.45 = 10.15`). -/
theorem premGamma_E06_rpow7_Re_lower :
    (10.15 : ℝ) ≤ (7 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (7 : ℝ) ^ ((5 / 26) : ℝ) ≤ (7 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 7) hfrac
  have h145 : (1.45 : ℝ) ≤ (7 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E06_rpow7_frac_lower hmono
  have h1015 : (10.15 : ℝ) = 7 * 1.45 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 7 by norm_num), Real.rpow_one, h1015]
  exact mul_le_mul_of_nonneg_left h145 (by norm_num : (0 : ℝ) ≤ 7)

/-- E06 shifted cpow norm lower: `10.15 ≤ ‖(7 : ℂ) ^ s‖` at `s = w_E06 + 1`. -/
theorem premGamma_E06_cpow7_norm_lower :
    (10.15 : ℝ) ≤ ‖(((7 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((7 : ℝ) : ℂ) = (7 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 7 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E06_rpow7_Re_lower

/-- Cpow-upper requirement at `N = 7` (filed, not proved): optimistic-but-sound
`‖(7 : ℂ) ^ s‖ ≤ 10.29` at E06 shifted `s` (TRUE `7 ^ 1.1975 ≈ 10.28027`).
Feeds the `N = 7` Re-ceiling numerator `10.29 * 5040 = 51861.6`
once `link` + Re lowers land. Filed ONLY at `N = 7`. -/
def premGamma_E06_cpow7_upper_needed : Prop :=
  ‖(((7 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (10.29 : ℝ)

/-- E06 shifted `s+7` norm: `‖s + 7‖ ≤ 8.23`
(TRUE `≈ 8.22129`; `8.1975^2 + 0.625^2 = 67.58963125 ≤ 8.23^2`). -/
theorem premGamma_E06shift_add7_norm_le :
    ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ≤ (8.23 : ℝ) := by
  have hre : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
      = (8.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ^ 2
      ≤ (8.23 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (8.23 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 7` denominator norm-product upper, right-nested to match
`premGamma_E06_GammaSeq7_link` (`83818.21097691085296 ≤ 83818.22`; `prod7 = prod6 * ‖s+7‖`). -/
theorem premGamma_E06_prod7_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))) ≤
      (83818.22 : ℝ) := by
  have h67 := mul_le_mul premGamma_E06shift_add6_norm_le premGamma_E06shift_add7_norm_le
    (norm_nonneg _) (by norm_num)
  have h567 := mul_le_mul premGamma_E06shift_add5_norm_le h67
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h4567 := mul_le_mul premGamma_E06shift_add4_norm_le h567
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h34567 := mul_le_mul premGamma_E06shift_add3_norm_le h4567
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h234567 := mul_le_mul premGamma_E06shift_add2_norm_le h34567
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have h1234567 := mul_le_mul premGamma_E06shift_succ_norm_le h234567
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))) (by norm_num)
  have h01234567 := mul_le_mul premGamma_E06shift_norm_le h1234567
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))))) (by norm_num)
  have heq : (1.36 : ℝ) * (2.29 * (3.26 * (4.25 * (5.24 * (6.23 * (7.23 * 8.23)))))) = 83818.21097691085296 := by
    norm_num
  rw [heq] at h01234567
  exact le_trans h01234567 (by norm_num : (83818.21097691085296 : ℝ) ≤ 83818.22)

/-- Missing link L1 at `N = 7` (filed, not proved): `GammaSeq s 7` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 6` spec shape
(`premGamma_E06_GammaSeq6_link`). Unfolds
`Complex.GammaSeq s 7 = (7 : ℂ) ^ s * 5040 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5) * (s+6) * (s+7))`
(`GammaSeq` at `Beta.lean:230`, `7 ! = 5040`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 7`. -/
def premGamma_E06_GammaSeq7_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 7‖ =
    ‖(((7 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 5040 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖)

/-- Missing rate L2 at `N = 7` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.014` (same host-leaf shape as
`premGamma_E06_GammaSeq6_rate_needed`; `0.61 - 0.014 = 0.596 < 0.66`,
so no closure). Host: a Stirling-disc / Binet-enclosure leaf or an explicit
`GammaSeq` rate lemma; NOT this file. Filed ONLY at `N = 7`. -/
def premGamma_E06_GammaSeq7_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 7 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E06 `N = 7` HONEST finite lower: `0.61 ≤ ‖GammaSeq s 7‖`, conditional
on the filed `N = 7` link identity. From cpow lower `10.15` + denominator upper
`83818.22` (`0.61 * 83818.22 = 51129.1142 ≤ 51156 = 10.15 * 5040`). Below the `0.66`
gate: do NOT feed `premGamma_E06_ge_of_shift`. -/
theorem premGamma_E06_Seq7_finite_lower (hLink : premGamma_E06_GammaSeq7_link) :
    (0.61 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 7‖ := by
  unfold premGamma_E06_GammaSeq7_link at hLink
  have hRight := premGamma_E06_prod7_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      (83818.22 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hpos6 : (0 : ℝ) < ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre6 : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (7.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre6] at h
    have habs : |(7.1975 : ℝ)| = 7.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 7.1975)
    rw [habs] at h
    linarith
  have hpos7 : (0 : ℝ) < ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre7 : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (8.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre7] at h
    have habs : |(8.1975 : ℝ)| = 8.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 8.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 (mul_pos hpos5 (mul_pos hpos6 hpos7))))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E06_cpow7_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.61 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.61 * 83818.22 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.61)
  have h2 : (10.15 : ℝ) * 5040 ≤
      ‖(((7 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 5040 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 5040)
  have h3 : (0.61 : ℝ) * 83818.22 ≤ 10.15 * 5040 := by norm_num
  linarith

/-- E06 `N = 7` honest-ceiling gap: `51156 / 83818.22 < 0.66`
(`≈ 0.61032 < 0.66`). The honest achievable quotient fails the gate. -/
theorem premGamma_E06_N7_honest_ceiling_below_gate :
    (51156 : ℝ) / 83818.22 < 0.66 := by
  norm_num

/-- E06 `N = 7` gap arithmetic: `0.61 + 0.05 = 0.66` exact. -/
theorem premGamma_E06_N7_gap_arith :
    (0.61 : ℝ) + 0.05 = 0.66 := by
  norm_num

/-- E06 `N = 8` next rung (filed, not fixed): the `N = 7` honest lower `0.61`
sits `0.05` below `0.66`, so sufficiency is NOT closed here. Do NOT force;
the ladder moves to `N = 8` (no `N = 8` numerals banked this turn). -/
def premGamma_E06_N8_next : Prop :=
  (0.61 : ℝ) < 0.66

/-! ## GAMMA-N8-E06: E06 N = 8 HONEST achievable finite lower (banked, fails gate).

Mirrors the E06 `N = 7` honest block token-for-token
(`premGamma_E06_rpow7_frac_lower`, `premGamma_E06_rpow7_Re_lower`,
`premGamma_E06_cpow7_norm_lower`, `premGamma_E06_cpow7_upper_needed`,
`premGamma_E06shift_add7_norm_le`, `premGamma_E06_prod7_le`,
`premGamma_E06_GammaSeq7_link`, `premGamma_E06_GammaSeq7_rate_needed`,
`premGamma_E06_Seq7_finite_lower`).

Audit (exact arithmetic, banked windows only — no mpmath estimate fixed):
At E06 shifted `s = w_E06 + 1` (`Re s = 1.1975`, `Im s = 0.625`):
* cpow lower: `‖(8 : ℂ) ^ s‖ = 8 ^ 1.1975 ≥ 11.92` (TRUE `≈ 12.06286`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `8 ^ 1.1975 = 8 * 8 ^ 0.1975 ≥
  8 * 8 ^ (5/26) ≥ 8 * 1.49 = 11.92` (`5/26 ≤ 0.1975`; `1.49^26 ≈ 31830.46 ≤
  32768 = 8^5`, all `norm_num`; `1.50` would be FALSE).
* cpow upper spec (filed, not proved): `‖(8 : ℂ) ^ s‖ ≤ 12.07` (TRUE `≈ 12.06286`).
* denominator norm uppers (`sq_norm` shapes, extending banked `‖s‖ ≤ 1.36`,
  `‖s+1‖ ≤ 2.29`, `‖s+2‖ ≤ 3.26`, `‖s+3‖ ≤ 4.25`, `‖s+4‖ ≤ 5.24`,
  `‖s+5‖ ≤ 6.23`, `‖s+6‖ ≤ 7.23`, `‖s+7‖ ≤ 8.23`): `‖s+8‖ ≤ 9.23`
  (`9.1975^2 + 0.625^2 = 84.98463125 ≤ 9.23^2`); product
  `1.36 * 2.29 * 3.26 * 4.25 * 5.24 * 6.23 * 7.23 * 8.23 * 9.23 =
  773642.0873168871728208 ≤ 773642.09` (`prod8 = prod7 * ‖s+8‖`).
* quotient: `40320 * 11.92 / 773642.09 = 480614.4 / 773642.09 ≈ 0.62124 < 0.66`
  — honest achievable (`0.621 * 773642.09 = 480431.73789 ≤ 480614.4`).
* verdict: FAILS to clear `0.66` (gap `0.039`: `0.621 + 0.039 = 0.66` exact;
  `480614.4 / 773642.09 < 0.66` banked). Do NOT force: file `N = 9` as next rung;
  no `N = 9` numerals are banked this turn.
-/

/-- E06 `8 ^ (5/26)` integer-root lower: `1.49 ≤ 8 ^ (5/26)`
(`1.49^26 ≈ 31830.46 ≤ 32768 = 8^5`). -/
theorem premGamma_E06_rpow8_frac_lower :
    (1.49 : ℝ) ≤ (8 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((8 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (8 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.49 : ℝ) ^ (26 : ℕ) ≤ (((8 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) _) hint

/-- E06 `8 ^ 1.1975` lower: `11.92 ≤ 8 ^ 1.1975` (TRUE `≈ 12.06286`).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`8 * 1.49 = 11.92`). -/
theorem premGamma_E06_rpow8_Re_lower :
    (11.92 : ℝ) ≤ (8 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (8 : ℝ) ^ ((5 / 26) : ℝ) ≤ (8 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hfrac
  have h149 : (1.49 : ℝ) ≤ (8 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E06_rpow8_frac_lower hmono
  have h1192 : (11.92 : ℝ) = 8 * 1.49 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 8 by norm_num), Real.rpow_one, h1192]
  exact mul_le_mul_of_nonneg_left h149 (by norm_num : (0 : ℝ) ≤ 8)

/-- E06 shifted cpow norm lower: `11.92 ≤ ‖(8 : ℂ) ^ s‖` at `s = w_E06 + 1`. -/
theorem premGamma_E06_cpow8_norm_lower :
    (11.92 : ℝ) ≤ ‖(((8 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((8 : ℝ) : ℂ) = (8 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 8 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E06_rpow8_Re_lower

/-- Cpow-upper requirement at `N = 8` (filed, not proved): optimistic-but-sound
`‖(8 : ℂ) ^ s‖ ≤ 12.07` at E06 shifted `s` (TRUE `8 ^ 1.1975 ≈ 12.06286`).
Feeds the `N = 8` Re-ceiling numerator `12.07 * 40320 = 486662.4`
once `link` + Re lowers land. Filed ONLY at `N = 8`. -/
def premGamma_E06_cpow8_upper_needed : Prop :=
  ‖(((8 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (12.07 : ℝ)

/-- E06 shifted `s+8` norm: `‖s + 8‖ ≤ 9.23`
(TRUE `≈ 9.21871`; `9.1975^2 + 0.625^2 = 84.98463125 ≤ 9.23^2`). -/
theorem premGamma_E06shift_add8_norm_le :
    ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ≤ (9.23 : ℝ) := by
  have hre : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)).re
      = (9.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ^ 2
      ≤ (9.23 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (9.23 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 8` denominator norm-product upper, right-nested to match
`premGamma_E06_GammaSeq8_link` (`773642.0873168871728208 ≤ 773642.09`; `prod8 = prod7 * ‖s+8‖`). -/
theorem premGamma_E06_prod8_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))))) ≤
      (773642.09 : ℝ) := by
  have h78 := mul_le_mul premGamma_E06shift_add7_norm_le premGamma_E06shift_add8_norm_le
    (norm_nonneg _) (by norm_num)
  have h678 := mul_le_mul premGamma_E06shift_add6_norm_le h78
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h5678 := mul_le_mul premGamma_E06shift_add5_norm_le h678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h45678 := mul_le_mul premGamma_E06shift_add4_norm_le h5678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h345678 := mul_le_mul premGamma_E06shift_add3_norm_le h45678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have h2345678 := mul_le_mul premGamma_E06shift_add2_norm_le h345678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))) (by norm_num)
  have h12345678 := mul_le_mul premGamma_E06shift_succ_norm_le h2345678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))))) (by norm_num)
  have h012345678 := mul_le_mul premGamma_E06shift_norm_le h12345678
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))))) (by norm_num)
  have heq : (1.36 : ℝ) * (2.29 * (3.26 * (4.25 * (5.24 * (6.23 * (7.23 * (8.23 * 9.23))))))) = 773642.0873168871728208 := by
    norm_num
  rw [heq] at h012345678
  exact le_trans h012345678 (by norm_num : (773642.0873168871728208 : ℝ) ≤ 773642.09)

/-- Missing link L1 at `N = 8` (filed, not proved): `GammaSeq s 8` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 7` spec shape
(`premGamma_E06_GammaSeq7_link`). Unfolds
`Complex.GammaSeq s 8 = (8 : ℂ) ^ s * 40320 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5) * (s+6) * (s+7) * (s+8))`
(`GammaSeq` at `Beta.lean:230`, `8 ! = 40320`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 8`. -/
def premGamma_E06_GammaSeq8_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 8‖ =
    ‖(((8 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 40320 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖)

/-- Missing rate L2 at `N = 8` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.014` (same host-leaf shape as
`premGamma_E06_GammaSeq7_rate_needed`; `0.621 - 0.014 = 0.607 < 0.66`,
so no closure). Host: a Stirling-disc / Binet-enclosure leaf or an explicit
`GammaSeq` rate lemma; NOT this file. Filed ONLY at `N = 8`. -/
def premGamma_E06_GammaSeq8_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 8 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E06 `N = 8` HONEST finite lower: `0.621 ≤ ‖GammaSeq s 8‖`, conditional
on the filed `N = 8` link identity. From cpow lower `11.92` + denominator upper
`773642.09` (`0.621 * 773642.09 = 480431.73789 ≤ 480614.4 = 11.92 * 40320`). Below the `0.66`
gate: do NOT feed `premGamma_E06_ge_of_shift`. -/
theorem premGamma_E06_Seq8_finite_lower (hLink : premGamma_E06_GammaSeq8_link) :
    (0.621 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 8‖ := by
  unfold premGamma_E06_GammaSeq8_link at hLink
  have hRight := premGamma_E06_prod8_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                      ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      (773642.09 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hpos6 : (0 : ℝ) < ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre6 : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (7.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre6] at h
    have habs : |(7.1975 : ℝ)| = 7.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 7.1975)
    rw [habs] at h
    linarith
  have hpos7 : (0 : ℝ) < ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre7 : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (8.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre7] at h
    have habs : |(8.1975 : ℝ)| = 8.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 8.1975)
    rw [habs] at h
    linarith
  have hpos8 : (0 : ℝ) < ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre8 : ((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (9.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre8] at h
    have habs : |(9.1975 : ℝ)| = 9.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 9.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                      ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 (mul_pos hpos5 (mul_pos hpos6 (mul_pos hpos7 hpos8)))))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E06_cpow8_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.621 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.621 * 773642.09 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.621)
  have h2 : (11.92 : ℝ) * 40320 ≤
      ‖(((8 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 40320 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 40320)
  have h3 : (0.621 : ℝ) * 773642.09 ≤ 11.92 * 40320 := by norm_num
  linarith

/-- E06 `N = 8` honest-ceiling gap: `480614.4 / 773642.09 < 0.66`
(`≈ 0.62124 < 0.66`). The honest achievable quotient fails the gate. -/
theorem premGamma_E06_N8_honest_ceiling_below_gate :
    (480614.4 : ℝ) / 773642.09 < 0.66 := by
  norm_num

/-- E06 `N = 8` gap arithmetic: `0.621 + 0.039 = 0.66` exact. -/
theorem premGamma_E06_N8_gap_arith :
    (0.621 : ℝ) + 0.039 = 0.66 := by
  norm_num

/-- E06 `N = 9` next rung (filed, not fixed): the `N = 8` honest lower `0.621`
sits `0.039` below `0.66`, so sufficiency is NOT closed here. Do NOT force;
the ladder moves to `N = 9` (no `N = 9` numerals banked this turn). -/
def premGamma_E06_N9_next : Prop :=
  (0.621 : ℝ) < 0.66

/-! ## GAMMA-N9-E06: E06 N = 9 HONEST achievable finite lower (banked, fails gate).

Mirrors the E06 `N = 8` honest block token-for-token
(`premGamma_E06_rpow8_frac_lower`, `premGamma_E06_rpow8_Re_lower`,
`premGamma_E06_cpow8_norm_lower`, `premGamma_E06_cpow8_upper_needed`,
`premGamma_E06shift_add8_norm_le`, `premGamma_E06_prod8_le`,
`premGamma_E06_GammaSeq8_link`, `premGamma_E06_GammaSeq8_rate_needed`,
`premGamma_E06_Seq8_finite_lower`).

Audit (exact arithmetic, banked windows only — no mpmath estimate fixed):
At E06 shifted `s = w_E06 + 1` (`Re s = 1.1975`, `Im s = 0.625`):
* cpow lower: `‖(9 : ℂ) ^ s‖ = 9 ^ 1.1975 ≥ 13.68` (TRUE `≈ 13.89010`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `9 ^ 1.1975 = 9 * 9 ^ 0.1975 ≥
  9 * 9 ^ (5/26) ≥ 9 * 1.52 = 13.68` (`5/26 ≤ 0.1975`; `1.52^26 ≈ 53448.22 ≤
  59049 = 9^5`, all `norm_num`; `1.53` would be FALSE).
* cpow upper spec (filed, not proved): `‖(9 : ℂ) ^ s‖ ≤ 13.90` (TRUE `≈ 13.89010`).
* denominator norm uppers (extending the banked `N = 8` chain):
  `‖s+9‖ ≤ 10.22` (`10.1975^2 + 0.625^2 = 104.37963125 ≤ 10.22^2`); product
  `1.36 * 2.29 * 3.26 * 4.25 * 5.24 * 6.23 * 7.23 * 8.23 * 9.23 * 10.22 =
  7906622.132378586906228576 ≤ 7906622.14` (`prod9 = prod8 * ‖s+9‖`).
* quotient: `362880 * 13.68 / 7906622.14 = 4964198.4 / 7906622.14 ≈ 0.62785 < 0.66`
  — honest achievable (`0.627 * 7906622.14 = 4957452.08178 ≤ 4964198.4`).
* verdict: FAILS to clear `0.66` (gap `0.033`: `0.627 + 0.033 = 0.66` exact;
  `4964198.4 / 7906622.14 < 0.66` banked). Do NOT force: file `N = 10` as next rung;
  no `N = 10` numerals are banked this turn.
-/

/-- E06 `9 ^ (5/26)` integer-root lower: `1.52 ≤ 9 ^ (5/26)`
(`1.52^26 ≈ 53448.22 ≤ 59049 = 9^5`). -/
theorem premGamma_E06_rpow9_frac_lower :
    (1.52 : ℝ) ≤ (9 : ℝ) ^ ((5 / 26 : ℝ)) := by
  have hR : (((9 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) = (9 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
    have e : (5 / 26 : ℝ) * (((26 : ℕ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (1.52 : ℝ) ^ (26 : ℕ) ≤ (((9 : ℝ) ^ ((5 / 26) : ℝ)) ^ (26 : ℕ)) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 26 ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 9) _) hint

/-- E06 `9 ^ 1.1975` lower: `13.68 ≤ 9 ^ 1.1975` (TRUE `≈ 13.89010`).
Splits `1.1975 = 1 + 0.1975`, uses `5/26 ≤ 0.1975` monotonicity plus the
fraction lower above (`9 * 1.52 = 13.68`). -/
theorem premGamma_E06_rpow9_Re_lower :
    (13.68 : ℝ) ≤ (9 : ℝ) ^ ((1.1975 : ℝ)) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (5 / 26 : ℝ) ≤ 0.1975 := by norm_num
  have hmono : (9 : ℝ) ^ ((5 / 26) : ℝ) ≤ (9 : ℝ) ^ ((0.1975) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) hfrac
  have h152 : (1.52 : ℝ) ≤ (9 : ℝ) ^ ((0.1975) : ℝ) :=
    le_trans premGamma_E06_rpow9_frac_lower hmono
  have h1368 : (13.68 : ℝ) = 9 * 1.52 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 9 by norm_num), Real.rpow_one, h1368]
  exact mul_le_mul_of_nonneg_left h152 (by norm_num : (0 : ℝ) ≤ 9)

/-- E06 shifted cpow norm lower: `13.68 ≤ ‖(9 : ℂ) ^ s‖` at `s = w_E06 + 1`. -/
theorem premGamma_E06_cpow9_norm_lower :
    (13.68 : ℝ) ≤ ‖(((9 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((9 : ℝ) : ℂ) = (9 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 9 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact premGamma_E06_rpow9_Re_lower

/-- Cpow-upper requirement at `N = 9` (filed, not proved): optimistic-but-sound
`‖(9 : ℂ) ^ s‖ ≤ 13.90` at E06 shifted `s` (TRUE `9 ^ 1.1975 ≈ 13.89010`).
Feeds the `N = 9` Re-ceiling numerator `13.90 * 362880 = 5044032.0`
once `link` + Re lowers land. Filed ONLY at `N = 9`. -/
def premGamma_E06_cpow9_upper_needed : Prop :=
  ‖(((9 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
    (13.90 : ℝ)

/-- E06 shifted `s+9` norm: `‖s + 9‖ ≤ 10.22`
(TRUE `≈ 10.21664`; `10.1975^2 + 0.625^2 = 104.37963125 ≤ 10.22^2`). -/
theorem premGamma_E06shift_add9_norm_le :
    ‖((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ≤ (10.22 : ℝ) := by
  have hre : ((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)).re
      = (10.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)).im
      = (0.625 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).im = (1.25 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : ‖((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))‖ ^ 2
      ≤ (10.22 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have hnn : (0 : ℝ) ≤ (10.22 : ℝ) := by norm_num
  have habs := abs_le_of_sq_le_sq h2 hnn
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- E06 `N = 9` denominator norm-product upper, right-nested to match
`premGamma_E06_GammaSeq9_link` (`7906622.132378586906228576 ≤ 7906622.14`; `prod9 = prod8 * ‖s+9‖`). -/
theorem premGamma_E06_prod9_le :
    ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    (‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                      ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))))) ≤
      (7906622.14 : ℝ) := by
  have h89 := mul_le_mul premGamma_E06shift_add8_norm_le premGamma_E06shift_add9_norm_le
    (norm_nonneg _) (by norm_num)
  have h789 := mul_le_mul premGamma_E06shift_add7_norm_le h89
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
  have h6789 := mul_le_mul premGamma_E06shift_add6_norm_le h789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
  have h56789 := mul_le_mul premGamma_E06shift_add5_norm_le h6789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) (by norm_num)
  have h456789 := mul_le_mul premGamma_E06shift_add4_norm_le h56789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))) (by norm_num)
  have h3456789 := mul_le_mul premGamma_E06shift_add3_norm_le h456789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))) (by norm_num)
  have h23456789 := mul_le_mul premGamma_E06shift_add2_norm_le h3456789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))))) (by norm_num)
  have h123456789 := mul_le_mul premGamma_E06shift_succ_norm_le h23456789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))))) (by norm_num)
  have h0123456789 := mul_le_mul premGamma_E06shift_norm_le h123456789
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))))))) (by norm_num)
  have heq : (1.36 : ℝ) * (2.29 * (3.26 * (4.25 * (5.24 * (6.23 * (7.23 * (8.23 * (9.23 * 10.22)))))))) = 7906622.132378586906228576 := by
    norm_num
  rw [heq] at h0123456789
  exact le_trans h0123456789 (by norm_num : (7906622.132378586906228576 : ℝ) ≤ 7906622.14)

/-- Missing link L1 at `N = 9` (filed, not proved): `GammaSeq s 9` norm identity
at E06 shifted `s = w_E06 + 1`, extending the `N = 8` spec shape
(`premGamma_E06_GammaSeq8_link`). Unfolds
`Complex.GammaSeq s 9 = (9 : ℂ) ^ s * 362880 / (s * (s+1) * (s+2) * (s+3) * (s+4) * (s+5) * (s+6) * (s+7) * (s+8) * (s+9))`
(`GammaSeq` at `Beta.lean:230`, `9 ! = 362880`, `prod_range_succ`), then `norm_div` /
`norm_mul` / `norm_pow`. Needs only Mathlib; left open because the cpow
unfolding was not instantiated this turn. Filed ONLY at `N = 9`. -/
def premGamma_E06_GammaSeq9_link : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 9‖ =
    ‖(((9 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 362880 /
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
        ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖)

/-- Missing rate L2 at `N = 9` (filed, not proved): quantitative `GammaSeq`
convergence at E06 shifted point with budget `0.014` (same host-leaf shape as
`premGamma_E06_GammaSeq8_rate_needed`; `0.627 - 0.014 = 0.613 < 0.66`,
so no closure). Host: a Stirling-disc / Binet-enclosure leaf or an explicit
`GammaSeq` rate lemma; NOT this file. Filed ONLY at `N = 9`. -/
def premGamma_E06_GammaSeq9_rate_needed : Prop :=
  ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 9 -
    Complex.Gamma (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))‖ ≤
    (0.014 : ℝ)

/-- E06 `N = 9` HONEST finite lower: `0.627 ≤ ‖GammaSeq s 9‖`, conditional
on the filed `N = 9` link identity. From cpow lower `13.68` + denominator upper
`7906622.14` (`0.627 * 7906622.14 = 4957452.08178 ≤ 4964198.4 = 13.68 * 362880`). Below the `0.66`
gate: do NOT feed `premGamma_E06_ge_of_shift`. -/
theorem premGamma_E06_Seq9_finite_lower (hLink : premGamma_E06_GammaSeq9_link) :
    (0.627 : ℝ) ≤
      ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)) 9‖ := by
  unfold premGamma_E06_GammaSeq9_link at hLink
  have hRight := premGamma_E06_prod9_le
  have hDeq : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) =
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                      (‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                        ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))))))) := by
    ring
  have hD : (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      (7906622.14 : ℝ) := by
    rw [hDeq]
    exact hRight
  have hre0 : (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hspos : (0 : ℝ) <
      ‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ := by
    have h := Complex.abs_re_le_norm
      (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))
    rw [hre0] at h
    have habs : |(1.1975 : ℝ)| = 1.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 1.1975)
    rw [habs] at h
    linarith
  have hpos1 : (0 : ℝ) < ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)
    have hre1 : ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)).re
        = (2.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre1] at h
    have habs : |(2.1975 : ℝ)| = 2.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 2.1975)
    rw [habs] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)
    have hre2 : ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
        = (3.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre2] at h
    have habs : |(3.1975 : ℝ)| = 3.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 3.1975)
    rw [habs] at h
    linarith
  have hpos3 : (0 : ℝ) < ‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)
    have hre3 : (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
        = (4.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre3] at h
    have habs : |(4.1975 : ℝ)| = 4.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 4.1975)
    rw [habs] at h
    linarith
  have hpos4 : (0 : ℝ) < ‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)
    have hre4 : ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
        = (5.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre4] at h
    have habs : |(5.1975 : ℝ)| = 5.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 5.1975)
    rw [habs] at h
    linarith
  have hpos5 : (0 : ℝ) < ‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre5 : (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (6.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre5] at h
    have habs : |(6.1975 : ℝ)| = 6.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 6.1975)
    rw [habs] at h
    linarith
  have hpos6 : (0 : ℝ) < ‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre6 : ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (7.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre6] at h
    have habs : |(7.1975 : ℝ)| = 7.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 7.1975)
    rw [habs] at h
    linarith
  have hpos7 : (0 : ℝ) < ‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre7 : (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (8.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre7] at h
    have habs : |(8.1975 : ℝ)| = 8.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 8.1975)
    rw [habs] at h
    linarith
  have hpos8 : (0 : ℝ) < ‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm ((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre8 : ((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (9.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre8] at h
    have habs : |(9.1975 : ℝ)| = 9.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 9.1975)
    rw [habs] at h
    linarith
  have hpos9 : (0 : ℝ) < ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
    have h := Complex.abs_re_le_norm (((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    have hre9 : (((((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))).re
        = (10.1975 : ℝ) := by
      rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.div_ofNat_re,
        show (Complex.mk (0.395 : ℝ) (1.25 : ℝ)).re = (0.395 : ℝ) from rfl,
        Complex.one_re]
      norm_num
    rw [hre9] at h
    have habs : |(10.1975 : ℝ)| = 10.1975 := abs_of_pos (by norm_num : (0 : ℝ) < 10.1975)
    rw [habs] at h
    linarith
  have hposR : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                (‖(((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                  (‖((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                    (‖(((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                      (‖((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖ *
                        ‖(((((((((((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)‖))))))))) :=
    mul_pos hspos (mul_pos hpos1 (mul_pos hpos2 (mul_pos hpos3 (mul_pos hpos4 (mul_pos hpos5 (mul_pos hpos6 (mul_pos hpos7 (mul_pos hpos8 hpos9))))))))
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) := by
    rw [hDeq]
    exact hposR
  have hC := premGamma_E06_cpow9_norm_lower
  rw [hLink, le_div_iff₀ hDpos]
  have h1 : (0.627 : ℝ) *
      (‖((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖ *
      ‖(((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)‖) ≤
      0.627 * 7906622.14 := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.627)
  have h2 : (13.68 : ℝ) * 362880 ≤
      ‖(((9 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (1.25 : ℝ)) : ℂ) / 2) + 1))))‖ * 362880 :=
    mul_le_mul_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 362880)
  have h3 : (0.627 : ℝ) * 7906622.14 ≤ 13.68 * 362880 := by norm_num
  linarith

/-- E06 `N = 9` honest-ceiling gap: `4964198.4 / 7906622.14 < 0.66`
(`≈ 0.62785 < 0.66`). The honest achievable quotient fails the gate. -/
theorem premGamma_E06_N9_honest_ceiling_below_gate :
    (4964198.4 : ℝ) / 7906622.14 < 0.66 := by
  norm_num

/-- E06 `N = 9` gap arithmetic: `0.627 + 0.033 = 0.66` exact. -/
theorem premGamma_E06_N9_gap_arith :
    (0.627 : ℝ) + 0.033 = 0.66 := by
  norm_num

/-- E06 `N = 10` next rung (filed, not fixed): the `N = 9` honest lower `0.627`
sits `0.033` below `0.66`, so sufficiency is NOT closed here. Do NOT force;
the ladder moves to `N = 10` (no `N = 10` numerals banked this turn). -/
def premGamma_E06_N10_next : Prop :=
  (0.627 : ℝ) < 0.66

end Door3PremiseGamma
