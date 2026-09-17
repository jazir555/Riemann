import Mathlib
import central_cover_assembly
import door3_premise_tier
import door3_cell_suppliers

/-!
# Door-3 R02 ball-sup advance (one cell Lambda-enclosure chain + tier-M mismatch).

Write-only advance. Imports are resolved via the `RootScratch` lib registration.
No `sorry` / `admit` / `axiom`; explicit `Prop` premises only; explicit binders.
`norm_num` is used only on `ℝ` / `ℕ` goals.

Recon (read-only, verified before writing):
* `door3_premise_tier.lean`: tier-M `0.05/0.06/0.07`, ball premises
  `premBall_RXX : ∀ z ∈ closedBall center (radius + 0.25), ‖xiShiftedEntire z‖ ≤ 16800`,
  conditional `premDeriv_RXX_of_ball : ball → ‖deriv‖ ≤ 67200`, shared
  `cauchy_closedForm : 16800 / 0.25 = 67200`, `ball_budget_check`,
  per-cell mismatches `premTier_RXX_mismatch : M < 67200`.
* `door3_cell_suppliers.lean` §B: `CS_rect := R02`, fat-ball enclosures,
  `CS_fatPrefactor_upper : ‖(z^2+1/4)/2‖ ≤ 35`, wide premise
  `CS_Lambda0_upper_fat : ∀ s in fat s-rect, ‖Λ₀ s‖ ≤ 479`,
  FE discharge `CS_Lambda0_FE_step` with `CS_Lambda0_of_FE_step`,
  assembly `CS_ballSup16800_of_Lambda0 : Λ₀-premise → ball-sup 16800`.
* Since `CS_rect` is definitionally `R02`, the supplier ball-sup is
  definitionally `Door3PremiseTier.premBall_R02`. This file records that
  bridge plus the honest tier-M quantification for R02 (`M = 0.07`).

Verdict recorded here:
* R02 ball-sup closed conditionally on the wide `Λ₀ ≤ 479` premise (proved).
* R02 `‖deriv‖ ≤ 67200` closed conditionally on the same premise (proved).
* Tier `0.07` NOT closed: `0.07 < 67200` with ratio `960000` and gap
  `67199.93` (proved as arithmetic). Direct derivative bounds or
  subdivision plus re-tiering remain patch-phase work.
* Per-cell `Λ₀ ≤ 479` enclosure itself remains an explicit premise
  (true `O(1)–O(10)` vs `479`); FE+Stirling discharge stays patch-phase.
-/

noncomputable section

namespace Door3R02BallAdvance

open Complex Real Set Topology

/-- R02 ball-sup from the wide `Λ₀ ≤ 479` premise (one cell Lambda-enclosure
bridge; `CS_rect` is definitionally `R02` so the supplier assembly applies). -/
theorem R02_premBall_of_Lambda (hL : Door3CellSuppliers.CS_Lambda0_upper_fat) :
    Door3PremiseTier.premBall_R02 := by
  intro z hz
  exact Door3CellSuppliers.CS_ballSup16800_of_Lambda0 hL z hz

/-- R02 ball-sup from the FE+Stirling discharge shape. -/
theorem R02_premBall_of_FE (h : Door3CellSuppliers.CS_Lambda0_FE_step) :
    Door3PremiseTier.premBall_R02 :=
  R02_premBall_of_Lambda (Door3CellSuppliers.CS_Lambda0_of_FE_step h)

/-- R02 Cauchy deriv cap from the wide `Λ₀` premise. -/
theorem R02_deriv67200_of_Lambda
    (hL : Door3CellSuppliers.CS_Lambda0_upper_fat) (w : ℂ)
    (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  Door3PremiseTier.premDeriv_R02_of_ball (R02_premBall_of_Lambda hL) w hw

/-- R02 Cauchy deriv cap from the FE-step premise. -/
theorem R02_deriv67200_of_FE
    (h : Door3CellSuppliers.CS_Lambda0_FE_step) (w : ℂ)
    (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  Door3PremiseTier.premDeriv_R02_of_ball (R02_premBall_of_FE h) w hw

/-- R02 sphere sup from the wide `Λ₀` premise (each `0.25`-sphere). -/
theorem R02_sphere_of_Lambda
    (hL : Door3CellSuppliers.CS_Lambda0_upper_fat) (w : ℂ)
    (hw : CentralCoverAssembly.R02.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  Door3PremiseTier.premSphere_R02_of_ball (R02_premBall_of_Lambda hL) w hw z hz

/-- Cauchy closed form restated for the R02 chain (`r = 0.25`). -/
theorem R02_cauchy_closedForm : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- R02 tier mismatch restated (`M = 0.07` vs Cauchy `67200`). -/
theorem R02_tier07_mismatch : (0.07 : ℝ) < 67200 :=
  Door3PremiseTier.tier07_lt_67200

/-- Honest gap: Cauchy value exceeds the tier by `67199.93`. -/
theorem R02_tier07_gap : (67200 : ℝ) - 0.07 = 67199.93 := by
  norm_num

/-- Honest ratio: Cauchy value is `960000×` the `0.07` tier. -/
theorem R02_tier07_ratio : (67200 : ℝ) / 0.07 = 960000 := by
  norm_num

/-- Companion ratios for the other tiers (shared Cauchy value). -/
theorem R02_cauchy_ratio05 : (67200 : ℝ) / 0.05 = 1344000 := by
  norm_num

theorem R02_cauchy_ratio06 : (67200 : ℝ) / 0.06 = 1120000 := by
  norm_num

/-- R02 ball assembly value: `1/2 + 35 * 479 = 16765.5`. -/
theorem R02_ball_assembly_value : (0.5 : ℝ) + 35 * 479 = 16765.5 := by
  norm_num

/-- R02 ball assembly fits the joint cap with margin `34.5`. -/
theorem R02_ball_assembly_le_cap : (0.5 : ℝ) + 35 * 479 ≤ 16800 := by
  norm_num

theorem R02_ball_margin : (16800 : ℝ) - (0.5 + 35 * 479) = 34.5 := by
  norm_num

/-! ## R02 deriv residual (WAVE2-DERIV patch record).

Unconditional discharge of `CS_Lambda0_upper_fat` (`Λ₀ ≤ 479` on the fat
`s`-rect) via FE + Stirling needs Gamma-cap and right-side-zeta-cap
inputs absent from Mathlib and from this repo, so it stays an explicit
premise. Closed here, unconditionally:
* generic transfer: any ball sup `C` gives `‖deriv‖ ≤ C / 0.25 = 4 * C`
  on `R02` (`R02_deriv_of_ballCap`, `R02_cauchy_scales_4C`; the staged
  `67200` value is the `C = 16800` case);
* generic ball assembly at any Lambda cap `M ≥ 0`
  (`R02_ballSup_of_LambdaCap`; the staged `16765.5` is the `M = 479`
  case), with the conditional true-scale sharpening `M = 10` giving
  ball `350.5` and deriv `1402` — a proved `47×` factor reduction over
  `16765.5 / 67200`, conditional on the `M = 10` Lambda premise
  (true `Λ₀` there is `O(1)`–`O(10)`);
* the wide premise yields the FE-step shape with `M := 479`
  (`R02_FE_step_of_Lambda`), so `CS_Lambda0_FE_step` is the weaker
  residual — discharging it still needs the Gamma / zeta caps;
* blocking inequalities: tier `0.07` at `r = 0.25` needs `C ≤ 0.0175`
  (`R02_tier07_needs_ball00175`), and at `C = 16800` needs
  `R ≥ 240000` (`R02_tier07_needs_radius240000`); both are infeasible at
  true scale (`0.0175 < 10`, `1.51 < 240000`), and even the sharpened
  `1402` stays above `0.07` (`R02_deriv1402_above_tier07`). Direct
  Cauchy tuning alone cannot close the tier; subdivision plus
  re-tiering or direct derivative bounds remain patch-phase work.
-/

/-- Generic R02 ball-to-deriv transfer at any cap `C` (the staged
`premDeriv_R02_of_ball` is the `C = 16800` case). -/
theorem R02_deriv_of_ballCap (C : ℝ)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R02.center
      (CentralCoverAssembly.R02.radius + 0.25) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ C / 0.25 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R02.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => Door3PremiseTier.strip_of_rect_mem CentralCoverAssembly.R02
      CentralCoverAssembly.R02_strip_lo CentralCoverAssembly.R02_strip_hi u hu
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R02 0.25 C (by norm_num) hStrip hBall w hw

/-- Cauchy scaling at `r = 0.25` is multiplication by `4`. -/
theorem R02_cauchy_scales_4C (C : ℝ) : C / (0.25 : ℝ) = 4 * C := by
  ring

/-- Generic R02 ball-sup assembly at any Lambda cap `M ≥ 0` (the staged
`CS_ballSup16800_of_Lambda0` is the `M = 479` case). -/
theorem R02_ballSup_of_LambdaCap (M : ℝ) (hM0 : 0 ≤ M)
    (hL : ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im →
      s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ M)
    (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3CellSuppliers.CS_rect.center
      (Door3CellSuppliers.CS_rect.radius + 0.25)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 0.5 + 35 * M := by
  have hP := Door3CellSuppliers.CS_fatPrefactor_upper z hz
  have hs := Door3CellSuppliers.CS_fat_s_bounds z hz
  have hLam : ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ M :=
    hL _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  unfold CentralCoverAssembly.xiShiftedEntire
  have hprod : ‖(z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ 35 * M := by
    rw [norm_mul]
    exact mul_le_mul hP hLam (norm_nonneg _) (by norm_num)
  have htot := norm_sub_le ((1 / 2 : ℂ))
    ((z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z))
  rw [Door3CellSuppliers.CS_norm_half] at htot
  linarith [htot, hprod, hM0]

/-- The wide premise yields the FE-step shape with `M := 479`: the
FE-step is the weaker residual. -/
theorem R02_FE_step_of_Lambda
    (hL : Door3CellSuppliers.CS_Lambda0_upper_fat) :
    Door3CellSuppliers.CS_Lambda0_FE_step :=
  ⟨479, le_rfl, hL⟩

/-- Assembly value at the true-scale cap `M = 10`. -/
theorem R02_ball_assembly10_value : (0.5 : ℝ) + 35 * 10 = 350.5 := by
  norm_num

/-- Conditional sharpening at true scale `M = 10`: ball `≤ 350.5`. -/
theorem R02_ballSup350_of_Lambda10
    (hL : ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im →
      s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ (10 : ℝ))
    (z : ℂ)
    (hz : z ∈ Metric.closedBall CentralCoverAssembly.R02.center
      (CentralCoverAssembly.R02.radius + 0.25)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 350.5 := by
  have h := R02_ballSup_of_LambdaCap 10 (by norm_num) hL z hz
  have heq : (0.5 : ℝ) + 35 * 10 = 350.5 := by norm_num
  rw [heq] at h
  exact h

/-- `47×` factor witness for the ball sharpening
(`47 * 350.5 ≤ 16765.5`). -/
theorem R02_ball_sharpening_factor47 : (47 : ℝ) * 350.5 ≤ 16765.5 := by
  norm_num

/-- Conditional deriv sharpening: `M = 10` gives `‖deriv‖ ≤ 1402`. -/
theorem R02_deriv1402_of_Lambda10
    (hL : ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im →
      s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ (10 : ℝ))
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 1402 := by
  have hBall := R02_ballSup350_of_Lambda10 hL
  have h := R02_deriv_of_ballCap 350.5 hBall w hw
  have heq : (350.5 : ℝ) / 0.25 = 1402 := by norm_num
  rw [heq] at h
  exact h

/-- `1402 < 67200`: the proved (conditional) factor reduction. -/
theorem R02_deriv1402_lt_67200 : (1402 : ℝ) < 67200 := by
  norm_num

/-- Absolute drop from the Cauchy value to the sharpened value. -/
theorem R02_deriv1402_gap : (67200 : ℝ) - 1402 = 65798 := by
  norm_num

/-- Blocking inequality, radius fixed: tier `0.07` at `r = 0.25` forces
the ball cap `C ≤ 0.0175`. -/
theorem R02_tier07_needs_ball00175 (C : ℝ)
    (h : C / (0.25 : ℝ) ≤ 0.07) : C ≤ 0.0175 := by
  have hr : (0 : ℝ) < 0.25 := by norm_num
  rw [div_le_iff₀ hr] at h
  have heq : (0.07 : ℝ) * 0.25 = 0.0175 := by norm_num
  linarith

/-- Blocking inequality, cap fixed: tier `0.07` at `C = 16800` forces
the Cauchy radius `R ≥ 240000`. -/
theorem R02_tier07_needs_radius240000 (R : ℝ) (hR : 0 < R)
    (h : (16800 : ℝ) / R ≤ 0.07) : 240000 ≤ R := by
  have heq : (16800 : ℝ) / 0.07 = 240000 := by norm_num
  have hpos : (0 : ℝ) < 0.07 := by norm_num
  have h2 : 16800 ≤ 0.07 * R := by
    rw [div_le_iff₀ hR] at h
    exact h
  have h3 : 16800 / 0.07 ≤ R := by
    rw [div_le_iff₀ hpos]
    linarith [h2]
  rw [heq] at h3
  exact h3

/-- Needed `0.0175` sits far below true `O(10)` scale (witness `10`). -/
theorem R02_ballNeed_gap : (0.0175 : ℝ) < 10 := by
  norm_num

/-- Needed radius `240000` dwarfs the fat-ball scale `1.51`. -/
theorem R02_radiusNeed_gap : (1.51 : ℝ) < 240000 := by
  norm_num

/-- Even the sharpened `1402` stays above tier `0.07`. -/
theorem R02_deriv1402_above_tier07 : (0.07 : ℝ) < 1402 := by
  norm_num

/-- Gap of the sharpened value over the tier. -/
theorem R02_deriv1402_tier_gap : (1402 : ℝ) - 0.07 = 1401.93 := by
  norm_num

#print axioms R02_premBall_of_Lambda
#print axioms R02_deriv67200_of_Lambda
#print axioms R02_tier07_ratio
#print axioms R02_ball_assembly_le_cap
#print axioms R02_deriv_of_ballCap
#print axioms R02_ballSup_of_LambdaCap
#print axioms R02_FE_step_of_Lambda
#print axioms R02_deriv1402_of_Lambda10
#print axioms R02_tier07_needs_ball00175
#print axioms R02_tier07_needs_radius240000

end Door3R02BallAdvance
