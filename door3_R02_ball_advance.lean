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

#print axioms R02_premBall_of_Lambda
#print axioms R02_deriv67200_of_Lambda
#print axioms R02_tier07_ratio
#print axioms R02_ball_assembly_le_cap

end Door3R02BallAdvance
