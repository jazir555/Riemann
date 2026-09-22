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

/-! ## R02 subdivision pilot (WAVE3-DERIV): two halves + halved Cauchy radius.

Pilot step for the subdivision lane: `R02 = (-8,-5.5) × (0.01,0.2)` is split
into west/east halves at `xmid = -6.75` (`R02W`, `R02E`; every `R02` point lies
in one half: `R02_covered_by_halves`, with reverse inclusions
`R02W_mem_to_R02` / `R02E_mem_to_R02`). Per-subrect Cauchy is recomputed at
the halved radius `r = 0.125` (`R02W_deriv_of_ballCap125`,
`R02E_deriv_of_ballCap125`: any sub-ball sup `C` gives `‖deriv‖ ≤ C / 0.125
= 8 * C` on that half, via `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`).

Exact numbers (proved):
* staged cap `C = 16800` gives per-half `16800 / 0.125 = 134400`
  (`R02_subdiv_closedForm134400`, conditional closes `R02W/E_deriv134400_of_ball16800`),
  i.e. exactly `2 * 67200` (`R02_subdiv_doubling`): naive radius-halving
  WORSENS the cap by `2×` (`R02_subdiv_halving_worsens`).
* honest gap `134400 - 0.07 = 134399.93` (`R02_subdiv_gap`), ratio `1920000`
  (`R02_subdiv_ratio`).
* blocking shape at halved radius: `C / 0.125 ≤ 0.07` forces `C ≤ 0.00875`
  (`R02_subdiv_tier07_needs_ball000875`), sitting below true `O(10)` scale
  (`R02_subdiv_ballNeed_gap`); the staged `16800` at `r = 0.125` provably
  misses the tier (`R02_subdiv_halved_radius_blocked`, via
  `R02_tier07_needs_radius240000` since `0.125 < 240000`).
* sharpened `C = 350.5` gives per-half `2804` (`R02_subdiv_closedForm2804`,
  conditional closes `R02W/E_deriv2804_of_ball350`), still above `0.07`
  (`R02_subdiv_2804_above_tier07`, gap `2803.93`).

Verdict: subdivision by halving the Cauchy radius alone cannot reach tier
`0.07` either — it doubles the cap. Re-tiering or direct derivative bounds
remain patch-phase work.
-/

/-- West half of `R02`: `(-8,-6.75) × (0.01,0.2)`. -/
def R02W : CellProofEngine.Rect2D :=
  ⟨-8, -6.75, 0.01, 0.2, by norm_num, by norm_num⟩

/-- East half of `R02`: `(-6.75,-5.5) × (0.01,0.2)`. -/
def R02E : CellProofEngine.Rect2D :=
  ⟨-6.75, -5.5, 0.01, 0.2, by norm_num, by norm_num⟩

/-- West half sits inside `R02`. -/
theorem R02W_mem_to_R02 (w : ℂ) (hw : R02W.mem w) :
    CentralCoverAssembly.R02.mem w := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have hx0n : (-8 : ℝ) ≤ w.re := hx0
  have hx1n : w.re ≤ (-6.75 : ℝ) := hx1
  have hy0n : (0.01 : ℝ) ≤ w.im := hy0
  have hy1n : w.im ≤ (0.2 : ℝ) := hy1
  show (-8 : ℝ) ≤ w.re ∧ w.re ≤ -5.5 ∧ (0.01 : ℝ) ≤ w.im ∧ w.im ≤ 0.2
  exact ⟨hx0n, by linarith, hy0n, hy1n⟩

/-- East half sits inside `R02`. -/
theorem R02E_mem_to_R02 (w : ℂ) (hw : R02E.mem w) :
    CentralCoverAssembly.R02.mem w := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have hx0n : (-6.75 : ℝ) ≤ w.re := hx0
  have hx1n : w.re ≤ (-5.5 : ℝ) := hx1
  have hy0n : (0.01 : ℝ) ≤ w.im := hy0
  have hy1n : w.im ≤ (0.2 : ℝ) := hy1
  show (-8 : ℝ) ≤ w.re ∧ w.re ≤ -5.5 ∧ (0.01 : ℝ) ≤ w.im ∧ w.im ≤ 0.2
  exact ⟨by linarith, hx1n, hy0n, hy1n⟩

/-- The two halves cover `R02` (shared edge `-6.75` belongs to both). -/
theorem R02_covered_by_halves (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    R02W.mem w ∨ R02E.mem w := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have hx0n : (-8 : ℝ) ≤ w.re := hx0
  have hx1n : w.re ≤ (-5.5 : ℝ) := hx1
  have hy0n : (0.01 : ℝ) ≤ w.im := hy0
  have hy1n : w.im ≤ (0.2 : ℝ) := hy1
  rcases le_total w.re (-6.75) with h | h
  · left
    show (-8 : ℝ) ≤ w.re ∧ w.re ≤ -6.75 ∧ (0.01 : ℝ) ≤ w.im ∧ w.im ≤ 0.2
    exact ⟨hx0n, h, hy0n, hy1n⟩
  · right
    show (-6.75 : ℝ) ≤ w.re ∧ w.re ≤ -5.5 ∧ (0.01 : ℝ) ≤ w.im ∧ w.im ≤ 0.2
    exact ⟨h, hx1n, hy0n, hy1n⟩

/-- Generic west-half ball-to-deriv transfer at halved radius `r = 0.125`. -/
theorem R02W_deriv_of_ballCap125 (C : ℝ)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02W.center
      (R02W.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (w : ℂ) (hw : R02W.mem w) :
    ‖deriv xiShifted w‖ ≤ C / 0.125 := by
  have hStrip : ∀ (u : ℂ), R02W.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) := by
    intro u hu
    obtain ⟨_, _, hy0, hy1⟩ := hu
    have hy0n : (0.01 : ℝ) ≤ u.im := hy0
    have hy1n : u.im ≤ (0.2 : ℝ) := hy1
    constructor <;> linarith
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    R02W 0.125 C (by norm_num) hStrip hBall w hw

/-- Generic east-half ball-to-deriv transfer at halved radius `r = 0.125`. -/
theorem R02E_deriv_of_ballCap125 (C : ℝ)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02E.center
      (R02E.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (w : ℂ) (hw : R02E.mem w) :
    ‖deriv xiShifted w‖ ≤ C / 0.125 := by
  have hStrip : ∀ (u : ℂ), R02E.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) := by
    intro u hu
    obtain ⟨_, _, hy0, hy1⟩ := hu
    have hy0n : (0.01 : ℝ) ≤ u.im := hy0
    have hy1n : u.im ≤ (0.2 : ℝ) := hy1
    constructor <;> linarith
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    R02E 0.125 C (by norm_num) hStrip hBall w hw

/-- Cauchy scaling at `r = 0.125` is multiplication by `8`. -/
theorem R02_subdiv_cauchy_scales_8C (C : ℝ) : C / (0.125 : ℝ) = 8 * C := by
  ring

/-- Exact per-subrect cap at the staged `C = 16800`, halved radius. -/
theorem R02_subdiv_closedForm134400 : (16800 : ℝ) / 0.125 = 134400 := by
  norm_num

/-- West half closes `134400` conditionally on its own `16800` sub-ball. -/
theorem R02W_deriv134400_of_ball16800
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02W.center
      (R02W.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800)
    (w : ℂ) (hw : R02W.mem w) :
    ‖deriv xiShifted w‖ ≤ 134400 := by
  have h := R02W_deriv_of_ballCap125 16800 hBall w hw
  have heq : (16800 : ℝ) / 0.125 = 134400 := by norm_num
  rw [heq] at h
  exact h

/-- East half closes `134400` conditionally on its own `16800` sub-ball. -/
theorem R02E_deriv134400_of_ball16800
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02E.center
      (R02E.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800)
    (w : ℂ) (hw : R02E.mem w) :
    ‖deriv xiShifted w‖ ≤ 134400 := by
  have h := R02E_deriv_of_ballCap125 16800 hBall w hw
  have heq : (16800 : ℝ) / 0.125 = 134400 := by norm_num
  rw [heq] at h
  exact h

/-- Halving doubles the staged cap: `134400 = 2 * 67200`. -/
theorem R02_subdiv_doubling : (134400 : ℝ) = 2 * 67200 := by
  norm_num

/-- The halved-radius cap is strictly worse than the staged cap. -/
theorem R02_subdiv_halving_worsens : (67200 : ℝ) < 134400 := by
  norm_num

/-- Honest gap of the subdivided cap over tier `0.07`. -/
theorem R02_subdiv_gap : (134400 : ℝ) - 0.07 = 134399.93 := by
  norm_num

/-- Honest ratio of the subdivided cap to tier `0.07`. -/
theorem R02_subdiv_ratio : (134400 : ℝ) / 0.07 = 1920000 := by
  norm_num

/-- Blocking inequality, halved radius fixed: tier `0.07` at `r = 0.125`
forces the ball cap `C ≤ 0.00875`. -/
theorem R02_subdiv_tier07_needs_ball000875 (C : ℝ)
    (h : C / (0.125 : ℝ) ≤ 0.07) : C ≤ 0.00875 := by
  have hr : (0 : ℝ) < 0.125 := by norm_num
  rw [div_le_iff₀ hr] at h
  have heq : (0.07 : ℝ) * 0.125 = 0.00875 := by norm_num
  linarith

/-- Needed `0.00875` sits far below true `O(10)` scale (witness `10`). -/
theorem R02_subdiv_ballNeed_gap : (0.00875 : ℝ) < 10 := by
  norm_num

/-- The halved radius is dwarfed by the needed `240000`. -/
theorem R02_subdiv_radius0125_lt_240000 : (0.125 : ℝ) < 240000 := by
  norm_num

/-- Halved-radius blocking corollary: staged `16800` at `r = 0.125` provably
misses tier `0.07` (via `R02_tier07_needs_radius240000`). -/
theorem R02_subdiv_halved_radius_blocked
    (h : (16800 : ℝ) / 0.125 ≤ 0.07) : False := by
  have hR := R02_tier07_needs_radius240000 0.125 (by norm_num) h
  have hlt : (0.125 : ℝ) < 240000 := by norm_num
  linarith

/-- The subdivided cap stays above tier `0.07`. -/
theorem R02_subdiv_134400_above_tier07 : (0.07 : ℝ) < 134400 := by
  norm_num

/-- Exact per-subrect cap at the sharpened `C = 350.5`, halved radius. -/
theorem R02_subdiv_closedForm2804 : (350.5 : ℝ) / 0.125 = 2804 := by
  norm_num

/-- West half closes `2804` conditionally on its own `350.5` sub-ball. -/
theorem R02W_deriv2804_of_ball350
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02W.center
      (R02W.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 350.5)
    (w : ℂ) (hw : R02W.mem w) :
    ‖deriv xiShifted w‖ ≤ 2804 := by
  have h := R02W_deriv_of_ballCap125 350.5 hBall w hw
  have heq : (350.5 : ℝ) / 0.125 = 2804 := by norm_num
  rw [heq] at h
  exact h

/-- East half closes `2804` conditionally on its own `350.5` sub-ball. -/
theorem R02E_deriv2804_of_ball350
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02E.center
      (R02E.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 350.5)
    (w : ℂ) (hw : R02E.mem w) :
    ‖deriv xiShifted w‖ ≤ 2804 := by
  have h := R02E_deriv_of_ballCap125 350.5 hBall w hw
  have heq : (350.5 : ℝ) / 0.125 = 2804 := by norm_num
  rw [heq] at h
  exact h

/-- Even the subdivided sharpened value stays above tier `0.07`. -/
theorem R02_subdiv_2804_above_tier07 : (0.07 : ℝ) < 2804 := by
  norm_num

/-- Gap of the subdivided sharpened value over the tier. -/
theorem R02_subdiv_2804_gap : (2804 : ℝ) - 0.07 = 2803.93 := by
  norm_num

/-! ## R02 direct-deriv + retier step (WAVE4-DERIV).

Banked here (sorry-free):
* route (a), one factor-deriv cap on R02: the poly-factor prime
  `deriv polyOf s = s - 1 / 2` (local reproof of the `door3_deriv_up`
  shape, no new import) with the generic `|re|+|im|+0.5` upper and the
  R02-disc `s`-rect cap `‖deriv polyOf s‖ ≤ 9.5` (exact sum `9.49`);
* route (b), exact retier thresholds that ARE satisfiable, each with an
  explicit margin companion: staged `67200` (margin `800` at `68000`)
  conditional on the wide `Λ₀ ≤ 479` premise; sharpened `1402`
  (margin `8` at `1410`) conditional on the true-scale `M = 10` Lambda
  premise; subdivided-halves `2804` conditional on the per-half
  `350.5` sub-ball; subdivided staged `134400` conditional on the
  per-half `16800` sub-ball (exact doubled-cap retier).

Honest scope note: these close the deriv bound at retiered tiers only;
tier `0.07` itself stays out of reach (proved gaps above), and the
`Λ₀` / sub-ball premises remain explicit.
-/

/-- Poly-factor prime on R02 (local mirror of the banked `door3_deriv_up`
shape; `polyOf s = s * (s - 1) / 2`). -/
theorem R02_poly_hasDerivAt (s : ℂ) :
    HasDerivAt DerivCauchyBridge.polyOf (s - 1 / 2) s := by
  have hid : HasDerivAt (fun t : ℂ => t) 1 s :=
    hasDerivAt_id' (x := s)
  have hconst : HasDerivAt (fun t : ℂ => (1 : ℂ)) 0 s :=
    hasDerivAt_const (x := s) (c := (1 : ℂ))
  have hsub : HasDerivAt (fun t : ℂ => t - (1 : ℂ)) (1 - 0) s :=
    hid.sub hconst
  have hmul : HasDerivAt (fun t : ℂ => t * (t - (1 : ℂ)))
      (1 * (s - 1) + s * (1 - 0)) s :=
    hid.mul hsub
  have hdiv : HasDerivAt (fun t : ℂ => t * (t - (1 : ℂ)) / 2)
      ((1 * (s - 1) + s * (1 - 0)) / 2) s :=
    hmul.div_const (2 : ℂ)
  have heqF : (fun t : ℂ => t * (t - (1 : ℂ)) / 2) = DerivCauchyBridge.polyOf := by
    unfold DerivCauchyBridge.polyOf
    rfl
  have heqD : (1 * (s - 1) + s * (1 - 0)) / 2 = s - 1 / 2 := by
    ring
  rw [heqF] at hdiv
  rw [heqD] at hdiv
  exact hdiv

/-- Poly-factor deriv equation. -/
theorem R02_poly_deriv_eq (s : ℂ) :
    deriv DerivCauchyBridge.polyOf s = s - 1 / 2 :=
  (R02_poly_hasDerivAt s).deriv

/-- Generic poly-factor deriv upper from coordinate caps. -/
theorem R02_polyDerivUp_of_abs (s : ℂ) (A B : ℝ)
    (hre : |s.re| ≤ A) (him : |s.im| ≤ B) :
    ‖deriv DerivCauchyBridge.polyOf s‖ ≤ A + B + 0.5 := by
  rw [R02_poly_deriv_eq s]
  have h1 : ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le s (1 / 2)
  have h2 : ‖s‖ ≤ |s.re| + |s.im| :=
    Complex.norm_le_abs_re_add_abs_im s
  have h3 : ‖(1 / 2 : ℂ)‖ = (0.5 : ℝ) := by
    have e1 : ((1 / 2 : ℂ)) = (1 : ℂ) / 2 := by norm_num
    rw [e1, norm_div, norm_one, Complex.norm_two]
    norm_num
  have h4 : ‖s - 1 / 2‖ ≤ (|s.re| + |s.im|) + 0.5 := by
    calc ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := h1
      _ ≤ (|s.re| + |s.im|) + 0.5 := by
        rw [h3] at h1 ⊢
        linarith [h2]
  calc ‖s - 1 / 2‖ ≤ (|s.re| + |s.im|) + 0.5 := h4
    _ ≤ (A + B) + 0.5 := by linarith [hre, him]
    _ = A + B + 0.5 := by ring

/-- Exact coordinate sum feeding the R02-disc cap. -/
theorem R02_polyDeriv_sum949 : (0.74 : ℝ) + 8.25 + 0.5 = 9.49 := by
  norm_num

/-- Route (a): poly-factor deriv cap on the R02-disc `s`-rect
(`0.05 ≤ re ≤ 0.74`, `-8.25 ≤ im ≤ -5.25`, same shape as the banked
`poly_upper_R02_disc` value premises). -/
theorem R02_polyDeriv_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖deriv DerivCauchyBridge.polyOf s‖ ≤ 9.5 := by
  have hre : |s.re| ≤ (0.74 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have him : |s.im| ≤ (8.25 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have h := R02_polyDerivUp_of_abs s 0.74 8.25 hre him
  have hsum : (0.74 : ℝ) + 8.25 + 0.5 ≤ 9.5 := by norm_num
  linarith

/-- Pi-factor exponent prime on R02 (local mirror of the banked `door3_deriv_up`
`piExp_hasDerivAt` shape, no new import). -/
theorem R02_piExp_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => -((t : ℂ) / 2)) (-(1 / 2 : ℂ)) s := by
  have hid : HasDerivAt (fun t : ℂ => t) 1 s :=
    hasDerivAt_id' (x := s)
  have hdiv : HasDerivAt (fun t : ℂ => t / 2) (1 / 2) s :=
    hid.div_const (2 : ℂ)
  have hneg : HasDerivAt (-(fun t : ℂ => t / 2)) (-(1 / 2)) s :=
    hdiv.neg
  have heq : (-(fun t : ℂ => t / 2)) = (fun t : ℂ => -(t / 2)) := rfl
  rw [heq] at hneg
  exact hneg

/-- Pi-factor prime on R02 (local mirror of the banked `door3_deriv_up`
`pi_hasDerivAt` shape via `const_cpow`; `piOf s = π ^ (-(s / 2))`). -/
theorem R02_pi_hasDerivAt (s : ℂ) :
    HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) s := by
  have hc0 : ((Real.pi : ℂ) ≠ 0) := by
    exact_mod_cast Real.pi_pos.ne'
  have hf : HasDerivAt (fun t : ℂ => -((t : ℂ) / 2)) (-(1 / 2 : ℂ)) s :=
    R02_piExp_hasDerivAt s
  have h := hf.const_cpow (c := (Real.pi : ℂ)) (Or.inl hc0)
  have heqF : (fun t : ℂ => ((Real.pi : ℂ) ^ (-(t / 2)))) =
      DerivCauchyBridge.piOf := by
    unfold DerivCauchyBridge.piOf
    rfl
  rw [heqF] at h
  exact h

/-- Pi-factor deriv equation. -/
theorem R02_pi_deriv_eq (s : ℂ) :
    deriv DerivCauchyBridge.piOf s =
      DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) :=
  (R02_pi_hasDerivAt s).deriv

/-- Log-pi norm cap (local mirror of the banked `door3_deriv_up`
`logPi_norm_le` shape, no new import). -/
theorem R02_logPi_norm_le : ‖Complex.log (Real.pi : ℂ)‖ ≤ (2.15 : ℝ) := by
  have hlogEq : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  rw [hlogEq, Complex.norm_real, Real.norm_eq_abs]
  have hnn : 0 ≤ Real.log Real.pi := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  rw [abs_of_nonneg hnn]
  have h1 : Real.log Real.pi ≤ Real.pi - 1 :=
    Real.log_le_sub_one_of_pos Real.pi_pos
  have h2 : Real.pi < 3.15 := Real.pi_lt_d2
  have h3 : Real.pi - 1 ≤ (2.15 : ℝ) := by linarith
  linarith

/-- Generic pi-factor deriv upper from a value upper. -/
theorem R02_piDerivUp_of_upper (s : ℂ) (U : ℝ)
    (hU : ‖DerivCauchyBridge.piOf s‖ ≤ U) (hU0 : 0 ≤ U) :
    ‖deriv DerivCauchyBridge.piOf s‖ ≤ U * 2.15 / 2 := by
  have hder : deriv DerivCauchyBridge.piOf s =
      DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) :=
    (R02_pi_hasDerivAt s).deriv
  rw [hder]
  have e1 : ‖DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) *
      (-(1 / 2 : ℂ))‖ =
      ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ *
        ‖(-(1 / 2 : ℂ))‖ := by
    rw [norm_mul, norm_mul]
  rw [e1]
  have hn : ‖(-(1 / 2 : ℂ))‖ = (0.5 : ℝ) := by
    rw [norm_neg]
    have e2 : ((1 / 2 : ℂ)) = (1 : ℂ) / 2 := by norm_num
    rw [e2, norm_div, norm_one, Complex.norm_two]
    norm_num
  rw [hn]
  have hlog := R02_logPi_norm_le
  have hnn2 : 0 ≤ ‖Complex.log (Real.pi : ℂ)‖ := norm_nonneg _
  have step1 : ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ ≤
      U * 2.15 :=
    mul_le_mul hU hlog hnn2 hU0
  have step2 : ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ * 0.5 ≤
      U * 2.15 * 0.5 :=
    mul_le_mul_of_nonneg_right step1 (by norm_num)
  have fin : U * 2.15 * 0.5 = U * 2.15 / 2 := by ring
  rw [fin] at step2
  exact step2

/-- Pi-factor value cap on the R02-disc `s`-rect (banked hypothesis-free
`DerivCauchyBridge.pi_upper_R02_disc`, needs only `0.05 ≤ s.re`). -/
theorem R02_piVal_cap_disc {s : ℂ} (hre_lo : 0.05 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  DerivCauchyBridge.pi_upper_R02_disc hre_lo

/-- Exact product feeding the R02-disc pi-deriv cap. -/
theorem R02_piDeriv_prod1075 : (1 : ℝ) * 2.15 / 2 = 1.075 := by
  norm_num

/-- Pi-factor deriv cap on the R02-disc `s`-rect
(`0.05 ≤ re ≤ 0.74`, `-8.25 ≤ im ≤ -5.25`; value side needs only the
`re` floor, matching the banked `pi_upper_R02_disc` premise). -/
theorem R02_piDeriv_cap_disc {s : ℂ} (hre_lo : 0.05 ≤ s.re) :
    ‖deriv DerivCauchyBridge.piOf s‖ ≤ 1.075 := by
  have hU := R02_piVal_cap_disc hre_lo
  have h := R02_piDerivUp_of_upper s 1 hU (by norm_num)
  have hprod : (1 : ℝ) * 2.15 / 2 ≤ 1.075 := by norm_num
  linarith

/-- Poly-factor value cap on the R02-disc `s`-rect (banked hypothesis-free
`DerivCauchyBridge.poly_upper_R02_disc`; proves the value premise the
Leibniz packaging needs). -/
theorem R02_polyVal_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 42 :=
  DerivCauchyBridge.poly_upper_R02_disc hre_lo hre_hi him_lo him_hi

/-- Exact value product feeding the partial-product value cap. -/
theorem R02_polyPiVal_prod42 : (42 : ℝ) * 1 = 42 := by
  norm_num

/-- Partial-product value cap `‖P * Q‖ ≤ 42` on the R02-disc `s`-rect. -/
theorem R02_polyPiVal_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s‖ ≤ 42 := by
  have hP := R02_polyVal_cap_disc hre_lo hre_hi him_lo him_hi
  have hQ := R02_piVal_cap_disc hre_lo
  rw [norm_mul]
  have h := mul_le_mul hP hQ (norm_nonneg _) (by norm_num)
  have heq : (42 : ℝ) * 1 = 42 := by norm_num
  linarith

/-- Partial-product prime on R02 via the Leibniz rule. -/
theorem R02_polyPi_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => DerivCauchyBridge.polyOf t * DerivCauchyBridge.piOf t)
      ((s - 1 / 2) * DerivCauchyBridge.piOf s +
        DerivCauchyBridge.polyOf s *
          (DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))) s :=
  (R02_poly_hasDerivAt s).mul (R02_pi_hasDerivAt s)

/-- Partial-product deriv equation (Leibniz packaging in `deriv` form). -/
theorem R02_polyPi_deriv_eq (s : ℂ) :
    deriv (fun t : ℂ => DerivCauchyBridge.polyOf t * DerivCauchyBridge.piOf t) s =
      deriv DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s +
        DerivCauchyBridge.polyOf s * deriv DerivCauchyBridge.piOf s := by
  have h := ((R02_poly_hasDerivAt s).mul (R02_pi_hasDerivAt s)).deriv
  rw [R02_poly_deriv_eq s, R02_pi_deriv_eq s]
  exact h

/-- Generic partial-product deriv upper from value + deriv caps. -/
theorem R02_polyPiDerivUp_of_caps (s : ℂ) (VP VQ DP DQ : ℝ)
    (hVP : ‖DerivCauchyBridge.polyOf s‖ ≤ VP)
    (hVQ : ‖DerivCauchyBridge.piOf s‖ ≤ VQ)
    (hDP : ‖deriv DerivCauchyBridge.polyOf s‖ ≤ DP)
    (hDQ : ‖deriv DerivCauchyBridge.piOf s‖ ≤ DQ)
    (hVP0 : 0 ≤ VP) (hVQ0 : 0 ≤ VQ) (hDP0 : 0 ≤ DP) (hDQ0 : 0 ≤ DQ) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t * DerivCauchyBridge.piOf t) s‖ ≤
      DP * VQ + VP * DQ := by
  have e := R02_polyPi_deriv_eq s
  rw [e]
  have n1 : ‖deriv DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s‖ ≤ DP * VQ := by
    rw [norm_mul]
    exact mul_le_mul hDP hVQ (norm_nonneg _) hDP0
  have n2 : ‖DerivCauchyBridge.polyOf s * deriv DerivCauchyBridge.piOf s‖ ≤ VP * DQ := by
    rw [norm_mul]
    exact mul_le_mul hVP hDQ (norm_nonneg _) hVP0
  calc ‖deriv DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s +
        DerivCauchyBridge.polyOf s * deriv DerivCauchyBridge.piOf s‖
      ≤ ‖deriv DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s‖ +
        ‖DerivCauchyBridge.polyOf s * deriv DerivCauchyBridge.piOf s‖ :=
      norm_add_le _ _
    _ ≤ DP * VQ + VP * DQ := add_le_add n1 n2

/-- Exact Leibniz product feeding the R02-disc partial-product deriv cap. -/
theorem R02_polyPiDeriv_prod5465 : (9.5 : ℝ) * 1 + 42 * 1.075 = 54.65 := by
  norm_num

/-- Partial-product deriv cap on the R02-disc `s`-rect:
`‖deriv (P * Q)‖ ≤ 9.5 * 1 + 42 * 1.075 = 54.65`. -/
theorem R02_polyPiDeriv_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t * DerivCauchyBridge.piOf t) s‖ ≤
      54.65 := by
  have hVP := R02_polyVal_cap_disc hre_lo hre_hi him_lo him_hi
  have hVQ := R02_piVal_cap_disc hre_lo
  have hDP := R02_polyDeriv_cap_disc hre_lo hre_hi him_lo him_hi
  have hDQ := R02_piDeriv_cap_disc hre_lo
  have h := R02_polyPiDerivUp_of_caps s 42 1 9.5 1.075
    hVP hVQ hDP hDQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : (9.5 : ℝ) * 1 + 42 * 1.075 = 54.65 := by norm_num
  linarith

/-- Downstream assembly shape: full `PQ * G * Z` Leibniz majorant from the
partial-product caps plus explicit Gamma/Zeta value+deriv caps. The
`fGamma`/`fZeta` majorants (`UG UZ DG DZ`) stay explicit premises (blocked on
missing majorants); this combinator assumes no analyticity, only the
three-term Leibniz expansion norm. -/
theorem R02_fullDerivUp_of_factorCaps (Vpq Dpq UG UZ DG DZ : ℝ)
    (APQ APQ' AG AG' AZ AZ' : ℂ)
    (hVpq : ‖APQ‖ ≤ Vpq) (hDpq : ‖APQ'‖ ≤ Dpq)
    (hVG : ‖AG‖ ≤ UG) (hVZ : ‖AZ‖ ≤ UZ)
    (hDG : ‖AG'‖ ≤ DG) (hDZ : ‖AZ'‖ ≤ DZ)
    (hVpq0 : 0 ≤ Vpq) (hDpq0 : 0 ≤ Dpq)
    (hUG0 : 0 ≤ UG) (hUZ0 : 0 ≤ UZ)
    (hDG0 : 0 ≤ DG) (hDZ0 : 0 ≤ DZ) :
    ‖APQ' * AG * AZ + APQ * AG' * AZ + APQ * AG * AZ'‖ ≤
      Dpq * UG * UZ + Vpq * DG * UZ + Vpq * UG * DZ := by
  have m1 : ‖APQ' * AG‖ ≤ Dpq * UG := by
    rw [norm_mul]
    exact mul_le_mul hDpq hVG (norm_nonneg _) hDpq0
  have t1 : ‖APQ' * AG * AZ‖ ≤ Dpq * UG * UZ := by
    rw [norm_mul]
    exact mul_le_mul m1 hVZ (norm_nonneg _) (mul_nonneg hDpq0 hUG0)
  have m2 : ‖APQ * AG'‖ ≤ Vpq * DG := by
    rw [norm_mul]
    exact mul_le_mul hVpq hDG (norm_nonneg _) hVpq0
  have t2 : ‖APQ * AG' * AZ‖ ≤ Vpq * DG * UZ := by
    rw [norm_mul]
    exact mul_le_mul m2 hVZ (norm_nonneg _) (mul_nonneg hVpq0 hDG0)
  have m3 : ‖APQ * AG‖ ≤ Vpq * UG := by
    rw [norm_mul]
    exact mul_le_mul hVpq hVG (norm_nonneg _) hVpq0
  have t3 : ‖APQ * AG * AZ'‖ ≤ Vpq * UG * DZ := by
    rw [norm_mul]
    exact mul_le_mul m3 hDZ (norm_nonneg _) (mul_nonneg hVpq0 hUG0)
  calc ‖APQ' * AG * AZ + APQ * AG' * AZ + APQ * AG * AZ'‖
      ≤ ‖APQ' * AG * AZ + APQ * AG' * AZ‖ + ‖APQ * AG * AZ'‖ :=
        norm_add_le _ _
    _ ≤ (‖APQ' * AG * AZ‖ + ‖APQ * AG' * AZ‖) + ‖APQ * AG * AZ'‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (Dpq * UG * UZ + Vpq * DG * UZ) + Vpq * UG * DZ :=
        add_le_add (add_le_add t1 t2) t3

/-- Banked-partial instantiation: with `Vpq = 42`, `Dpq = 54.65` the
downstream bound is `54.65 * UG * UZ + 42 * DG * UZ + 42 * UG * DZ`.
On the R02-disc `s`-rect the two hypotheses `‖APQ‖ ≤ 42`,
`‖APQ'‖ ≤ 54.65` are discharged by `R02_polyPiVal_cap_disc` /
`R02_polyPiDeriv_cap_disc`; `UG UZ DG DZ` remain open. -/
theorem R02_fullDerivUp_bankedPQ_shape (UG UZ DG DZ : ℝ)
    (APQ APQ' AG AG' AZ AZ' : ℂ)
    (hVpq : ‖APQ‖ ≤ 42) (hDpq : ‖APQ'‖ ≤ 54.65)
    (hVG : ‖AG‖ ≤ UG) (hVZ : ‖AZ‖ ≤ UZ)
    (hDG : ‖AG'‖ ≤ DG) (hDZ : ‖AZ'‖ ≤ DZ)
    (hUG0 : 0 ≤ UG) (hUZ0 : 0 ≤ UZ)
    (hDG0 : 0 ≤ DG) (hDZ0 : 0 ≤ DZ) :
    ‖APQ' * AG * AZ + APQ * AG' * AZ + APQ * AG * AZ'‖ ≤
      54.65 * UG * UZ + 42 * DG * UZ + 42 * UG * DZ :=
  R02_fullDerivUp_of_factorCaps 42 54.65 UG UZ DG DZ
    APQ APQ' AG AG' AZ AZ' hVpq hDpq hVG hVZ hDG hDZ
    (by norm_num) (by norm_num) hUG0 hUZ0 hDG0 hDZ0

/-- Gamma-factor value cap on the R02-disc `s`-rect (banked hypothesis-free
`DerivCauchyBridge.gamma_upper_R02_disc`, `‖Γ(s/2)‖ ≤ 40`).
Rect check (no mismatch): the banked cap needs only
`0.05 ≤ s.re ≤ 0.74`; the R02-disc `s`-rect
`Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]` supplies those two premises
and its `im` bounds are unused here. -/
theorem R02_gammaVal_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74) :
    ‖DerivCauchyBridge.gammaOf s‖ ≤ 40 :=
  DerivCauchyBridge.gamma_upper_R02_disc hre_lo hre_hi

/-- Exact value product feeding the 3-factor `P * Q * G` value cap. -/
theorem R02_polyPiGammaVal_prod1680 : (42 : ℝ) * 40 = 1680 := by
  norm_num

/-- Generic 3-factor value upper from a banked partial-product cap plus a
Gamma value cap (pure `norm_mul`, no deriv needed). -/
theorem R02_polyPiGammaValUp_of_caps (APQ AG : ℂ) (Vpq UG : ℝ)
    (hVpq : ‖APQ‖ ≤ Vpq) (hVG : ‖AG‖ ≤ UG)
    (hVpq0 : 0 ≤ Vpq) :
    ‖APQ * AG‖ ≤ Vpq * UG := by
  rw [norm_mul]
  exact mul_le_mul hVpq hVG (norm_nonneg _) hVpq0

/-- 3-factor VALUE cap on the R02-disc `s`-rect:
`‖P * Q * G‖ ≤ 42 * 40 = 1680` via `norm_mul` from
`R02_polyPiVal_cap_disc` and `R02_gammaVal_cap_disc` (no deriv needed). -/
theorem R02_polyPiGammaVal_cap_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s *
      DerivCauchyBridge.gammaOf s‖ ≤ 1680 := by
  have hPQ := R02_polyPiVal_cap_disc hre_lo hre_hi him_lo him_hi
  have hG := R02_gammaVal_cap_disc hre_lo hre_hi
  have h := R02_polyPiGammaValUp_of_caps
    (DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s)
    (DerivCauchyBridge.gammaOf s) 42 40 hPQ hG (by norm_num)
  have heq : (42 : ℝ) * 40 = 1680 := by norm_num
  linarith

/-- Generic 4-factor value upper from a banked 3-factor cap plus a zeta
value cap (pure `norm_mul`, no deriv needed; `UZ` stays an explicit
premise). -/
theorem R02_polyPiGammaZetaValUp_of_caps (APQG AZ : ℂ) (VPQG UZ : ℝ)
    (hVPQG : ‖APQG‖ ≤ VPQG) (hVZ : ‖AZ‖ ≤ UZ)
    (hVPQG0 : 0 ≤ VPQG) :
    ‖APQG * AZ‖ ≤ VPQG * UZ := by
  rw [norm_mul]
  exact mul_le_mul hVPQG hVZ (norm_nonneg _) hVPQG0

/-- Banked-1680 4-factor VALUE instance on the R02-disc `s`-rect:
`‖P * Q * G * Z‖ ≤ 1680 * UZ` from `R02_polyPiGammaVal_cap_disc` plus an
explicit zeta cap `‖zeta s‖ ≤ UZ`. Value side is complete modulo `UZ`. -/
theorem R02_polyPiGammaZetaVal_cap_disc_of_zeta (UZ : ℝ) {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25)
    (hZ : ‖zeta s‖ ≤ UZ) :
    ‖DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s *
      DerivCauchyBridge.gammaOf s * zeta s‖ ≤ 1680 * UZ := by
  have hPQG := R02_polyPiGammaVal_cap_disc hre_lo hre_hi him_lo him_hi
  exact R02_polyPiGammaZetaValUp_of_caps
    (DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s *
      DerivCauchyBridge.gammaOf s) (zeta s) 1680 UZ hPQG hZ (by norm_num)

/-- UZ VALUE-cap missing-numeral spec (filed, not fixed): uniform
`‖zeta s‖ ≤ 10` on the R02-disc `s`-rect `Re ∈ [0.05,0.74]`,
`Im ∈ [-8.25,-5.25]` (statement-identical to the zeta-lane
`DerivCauchyBridge.R02_zeta_upper_obligation`,
`central_cover_assembly.lean:6493`, READ-ONLY — owning lane: zeta lane).
Not satisfiable this turn: banked best uppers `≤ 1012`
(`R02Unconditional.R02_zeta_upper_unconditional`,
`riemann_hypothesis_newsection.lean:1055`, not imported here) and `≤ 934`
(`R02_D3_zeta_upper_934`, `zeta_rigorous.lean:32566`, not imported here)
both exceed `10`; `premZeta_*` floors (`door3_premise_zeta.lean`, e.g.
`1.9 ≤ ‖zeta zs_R00‖`) and the `CS_zeta_of_parts` family
(`door3_cell_suppliers.lean:284`, incl. `CS_zeta_of_S2/S2b/S2c/S2d/S2e/S4/S6`)
prove LOWER bounds — wrong direction for a `≤ 10` upper. `UG` is banked
(`R02_gammaVal_cap_disc`, `UG = 40`); the DG deriv premise stays open
(`R02_gammaDeriv_obligation`; Gamma-deriv machinery tasked separately). -/
def R02_zetaVal_missingNumeral_spec : Prop :=
  ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
    ‖zeta s‖ ≤ 10

/-- Full 4-factor DERIV assembly with banked `PQ` caps and banked Gamma value
`UG = 40`: with `Vpq = 42`, `Dpq = 54.65`, `UG = 40` the downstream bound is
`54.65 * 40 * UZ + 42 * DG * UZ + 42 * 40 * DZ`.
Mirrors `R02_fullDerivUp_bankedPQ_shape` (:817) with the banked Gamma value
cap folded in (`hVG : ‖AG‖ ≤ 40`, discharged on-rect by
`R02_gammaVal_cap_disc` below); `UZ DG DZ` stay explicit premises and no
analyticity is assumed — only the three-term Leibniz norm from
`R02_fullDerivUp_of_factorCaps`. Residual owners: `UZ` zeta-upper lane
(`R02_zetaVal_missingNumeral_spec`, unsatisfiable from banked uppers — zeta
lane owns it); `DG` Gamma-deriv machinery (`R02_gammaDeriv_obligation`,
tasked separately); `DZ` zeta-deriv lane (no banked cap in-tree; owner TBD). -/
theorem R02_fullDerivUp_bankedPQG_shape (UZ DG DZ : ℝ)
    (APQ APQ' AG AG' AZ AZ' : ℂ)
    (hVpq : ‖APQ‖ ≤ 42) (hDpq : ‖APQ'‖ ≤ 54.65)
    (hVG : ‖AG‖ ≤ 40) (hVZ : ‖AZ‖ ≤ UZ)
    (hDG : ‖AG'‖ ≤ DG) (hDZ : ‖AZ'‖ ≤ DZ)
    (hUZ0 : 0 ≤ UZ) (hDG0 : 0 ≤ DG) (hDZ0 : 0 ≤ DZ) :
    ‖APQ' * AG * AZ + APQ * AG' * AZ + APQ * AG * AZ'‖ ≤
      54.65 * 40 * UZ + 42 * DG * UZ + 42 * 40 * DZ :=
  R02_fullDerivUp_bankedPQ_shape 40 UZ DG DZ
    APQ APQ' AG AG' AZ AZ' hVpq hDpq hVG hVZ hDG hDZ
    (by norm_num) hUZ0 hDG0 hDZ0

/-- Zeta-deriv gap as a taskable unit (obligation, not a proof): the exact
statement the full 4-factor deriv assembly still needs is
`‖deriv zeta s‖ ≤ DZ` uniformly on the R02-disc `s`-rect.
No zeta-deriv cap is banked in-tree, so `DZ` remains open (owner TBD —
zeta-deriv lane; mirrors `R02_gammaDeriv_obligation`). -/
def R02_zetaDeriv_obligation (DZ : ℝ) : Prop :=
  ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
    ‖deriv zeta s‖ ≤ DZ

/-- Banked-`UZ = 10` instance of the full 4-factor DERIV assembly: the bound
fires as `54.65 * 40 * 10 + 42 * DG * 10 + 42 * 40 * DZ` the day the zeta
lane banks `R02_zetaVal_missingNumeral_spec` (`‖zeta s‖ ≤ 10` on the rect).
Exact firing condition: `hZ10` (zeta-upper obligation) + the four rect
hypotheses + `‖APQ‖ ≤ 42`, `‖APQ'‖ ≤ 54.65`, `‖AG‖ ≤ 40` (discharged
on-rect by `R02_polyPiVal_cap_disc` / `R02_polyPiDeriv_cap_disc` /
`R02_gammaVal_cap_disc`) + explicit `DG` / `DZ` caps with nonnegativity.
Honest status: `hZ10` is NOT satisfiable this turn (banked best uppers
`≤ 1012` / `≤ 934` exceed `10`; see the `R02_zetaVal_missingNumeral_spec`
docstring) and `DG` / `DZ` stay open — so this instance is armed but
unfired. -/
theorem R02_fullDerivUp_bankedUZ10_of_zetaUpper (DG DZ : ℝ) {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25)
    (APQ APQ' AG AG' : ℂ)
    (hVpq : ‖APQ‖ ≤ 42) (hDpq : ‖APQ'‖ ≤ 54.65)
    (hVG : ‖AG‖ ≤ 40)
    (hDG : ‖AG'‖ ≤ DG) (hDZ : ‖deriv zeta s‖ ≤ DZ)
    (hDG0 : 0 ≤ DG) (hDZ0 : 0 ≤ DZ)
    (hZ10 : R02_zetaVal_missingNumeral_spec) :
    ‖APQ' * AG * zeta s + APQ * AG' * zeta s + APQ * AG * deriv zeta s‖ ≤
      54.65 * 40 * 10 + 42 * DG * 10 + 42 * 40 * DZ := by
  have hVZ : ‖zeta s‖ ≤ (10 : ℝ) :=
    hZ10 s hre_lo hre_hi him_lo him_hi
  exact R02_fullDerivUp_bankedPQG_shape 10 DG DZ
    APQ APQ' AG AG' (zeta s) (deriv zeta s)
    hVpq hDpq hVG hVZ hDG hDZ (by norm_num) hDG0 hDZ0

/-- Exact banked product feeding the `UZ = 934` deriv shape. -/
theorem R02_derivUZ934_prod2041724 : (54.65 : ℝ) * 40 * 934 = 2041724 := by
  norm_num

/-- Banked-`UZ = 934` instance of the full 4-factor DERIV assembly: the bound
fires as `54.65 * 40 * 934 + 42 * DG * 934 + 42 * 40 * DZ` (UZ-part closes to
`2041724` by `R02_derivUZ934_prod2041724`, so the bound is finite and closed
modulo the explicit `DG` / `DZ` caps).
Mirrors `R02_fullDerivUp_bankedUZ10_of_zetaUpper` token-for-token with
`UZ := 934`: the `934` premise is re-stated here as the explicit pointwise
hypothesis `hZ934 : ‖zeta s‖ ≤ 934` (same position/shape as `hZ10`, no import
of the bridge file — the bridge file imports this file so this file must NOT
import the bridge). The bridge theorem `R02_zetaVal_934_of_D3`
(`door3_R02_zeta_bridge.lean:22`) discharges `hZ934` separately on the rect.
`‖APQ‖ ≤ 42`, `‖APQ'‖ ≤ 54.65`, `‖AG‖ ≤ 40` are discharged on-rect by
`R02_polyPiVal_cap_disc` / `R02_polyPiDeriv_cap_disc` /
`R02_gammaVal_cap_disc`; `DG` (Gamma-deriv) and `DZ` (zeta-deriv) stay the
open explicit premises with nonnegativity. First finite closed 4-factor
deriv bound modulo `DG` / `DZ`. -/
theorem R02_fullDerivUp_bankedUZ934_of_zeta934 (DG DZ : ℝ) {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25)
    (APQ APQ' AG AG' : ℂ)
    (hVpq : ‖APQ‖ ≤ 42) (hDpq : ‖APQ'‖ ≤ 54.65)
    (hVG : ‖AG‖ ≤ 40)
    (hDG : ‖AG'‖ ≤ DG) (hDZ : ‖deriv zeta s‖ ≤ DZ)
    (hDG0 : 0 ≤ DG) (hDZ0 : 0 ≤ DZ)
    (hZ934 : ‖zeta s‖ ≤ 934) :
    ‖APQ' * AG * zeta s + APQ * AG' * zeta s + APQ * AG * deriv zeta s‖ ≤
      54.65 * 40 * 934 + 42 * DG * 934 + 42 * 40 * DZ := by
  exact R02_fullDerivUp_bankedPQG_shape 934 DG DZ
    APQ APQ' AG AG' (zeta s) (deriv zeta s)
    hVpq hDpq hVG hZ934 hDG hDZ (by norm_num) hDG0 hDZ0

/-- Generic `(PQ) * G` deriv upper from value + deriv caps (two-term Leibniz
norm; `PQ` is treated as one banked factor). -/
theorem R02_pqGammaDerivUp_of_factorCaps (Vpq Dpq UG DG : ℝ)
    (APQ APQ' AG AG' : ℂ)
    (hVpq : ‖APQ‖ ≤ Vpq) (hDpq : ‖APQ'‖ ≤ Dpq)
    (hVG : ‖AG‖ ≤ UG) (hDG : ‖AG'‖ ≤ DG)
    (hVpq0 : 0 ≤ Vpq) (hDpq0 : 0 ≤ Dpq)
    (hUG0 : 0 ≤ UG) (hDG0 : 0 ≤ DG) :
    ‖APQ' * AG + APQ * AG'‖ ≤ Dpq * UG + Vpq * DG := by
  have n1 : ‖APQ' * AG‖ ≤ Dpq * UG := by
    rw [norm_mul]
    exact mul_le_mul hDpq hVG (norm_nonneg _) hDpq0
  have n2 : ‖APQ * AG'‖ ≤ Vpq * DG := by
    rw [norm_mul]
    exact mul_le_mul hVpq hDG (norm_nonneg _) hVpq0
  calc ‖APQ' * AG + APQ * AG'‖
      ≤ ‖APQ' * AG‖ + ‖APQ * AG'‖ := norm_add_le _ _
    _ ≤ Dpq * UG + Vpq * DG := add_le_add n1 n2

/-- Exact banked product feeding the `(PQ) * G` deriv shape. -/
theorem R02_pqGammaDeriv_prod2186 : (54.65 : ℝ) * 40 = 2186 := by
  norm_num

/-- Banked `(PQ) * G` instantiation: with `Vpq = 42`, `Dpq = 54.65`,
`UG = 40` the downstream bound is `54.65 * 40 + 42 * DG = 2186 + 42 * DG`.
On the R02-disc `s`-rect the three hypotheses `‖APQ‖ ≤ 42`,
`‖APQ'‖ ≤ 54.65`, `‖AG‖ ≤ 40` are discharged by
`R02_polyPiVal_cap_disc` / `R02_polyPiDeriv_cap_disc` /
`R02_gammaVal_cap_disc`; `DG` (the Gamma-deriv cap) stays the single open
deriv premise (mirrors `R02_fullDerivUp_bankedPQ_shape`). -/
theorem R02_pqGammaDerivUp_bankedPQG_shape (DG : ℝ)
    (APQ APQ' AG AG' : ℂ)
    (hVpq : ‖APQ‖ ≤ 42) (hDpq : ‖APQ'‖ ≤ 54.65)
    (hVG : ‖AG‖ ≤ 40) (hDG : ‖AG'‖ ≤ DG)
    (hDG0 : 0 ≤ DG) :
    ‖APQ' * AG + APQ * AG'‖ ≤ 54.65 * 40 + 42 * DG :=
  R02_pqGammaDerivUp_of_factorCaps 42 54.65 40 DG
    APQ APQ' AG AG' hVpq hDpq hVG hDG
    (by norm_num) (by norm_num) (by norm_num) hDG0

/-- Gamma-deriv gap as a taskable unit (obligation, not a proof): the exact
statement the `(PQ) * G` deriv assembly still needs is
`‖deriv gammaOf s‖ ≤ DG` uniformly on the R02-disc `s`-rect.
Needs a Mathlib `Complex.Gamma` deriv API at `s / 2` (a `HasDerivAt` /
differentiable lemma for `Complex.Gamma` with `(s / 2).re > 0`),
composed with the `div_const` chain rule for `s ↦ s / 2`, plus a uniform
norm majorant (Stirling / integral bound) to fix a concrete `DG`.
No such Gamma-deriv cap is banked in-tree, so `DG` remains open. -/
def R02_gammaDeriv_obligation (DG : ℝ) : Prop :=
  ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
    ‖deriv DerivCauchyBridge.gammaOf s‖ ≤ DG

/-- Gamma-factor prime on R02 (local mirror of the banked `door3_deriv_up`
`pi_hasDerivAt` shape and of `Door3Digamma.gOf_hasDerivAt`, no new import):
`gammaOf s = Complex.Gamma (s / 2)`, so the chain rule with the inner
`s ↦ s / 2` prime (`div_const`) gives
`HasDerivAt gammaOf (dG * (1 / 2)) s` from any outer
`HasDerivAt Complex.Gamma dG (s / 2)`.
Banked analyticity supplying `hG` (grep record, read-only):
* Mathlib `Complex.differentiableAt_Gamma`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean:65`, needs
  `hs : ∀ m : ℕ, s ≠ -m`; on the R02-disc `s`-rect `(s / 2).re ∈
  [0.025, 0.37]`, so pole-avoidance follows from `re > 0`, exactly as in
  `Zeta23/GammaFacts.lean:70` `gamma_ne_neg_nat`);
* `Zeta23/GammaFacts.lean:76` `analyticAt_digamma` (Gamma and its deriv
  analytic on `0 < re`, hence `HasDerivAt` at every such point);
* `Door3Digamma.gOf_hasDerivAt` (`door3_digamma.lean:287`, same chain for
  the locally-defined `gOf`, definitionally `gammaOf`).
Unlike the pi case (`const_cpow`, unconditional), the outer premise `hG`
stays explicit because `Complex.Gamma` has poles at `-ℕ`. -/
theorem R02_gamma_hasDerivAt (s dG : ℂ)
    (hG : HasDerivAt Complex.Gamma dG (s / 2)) :
    HasDerivAt DerivCauchyBridge.gammaOf (dG * ((1 : ℂ) / 2)) s := by
  have hHalf : HasDerivAt (fun t : ℂ => t / 2) ((1 : ℂ) / 2) s :=
    (hasDerivAt_id' (x := s)).div_const (2 : ℂ)
  have hComp : HasDerivAt (Complex.Gamma ∘ fun t : ℂ => t / 2)
      (dG * ((1 : ℂ) / 2)) s :=
    hG.comp hHalf
  have heqF : (Complex.Gamma ∘ fun t : ℂ => t / 2) =
      DerivCauchyBridge.gammaOf := by
    unfold DerivCauchyBridge.gammaOf
    rfl
  rw [heqF] at hComp
  exact hComp

/-- Generic Gamma-factor deriv upper from an outer Gamma-prime cap
(mirror of `R02_piDerivUp_of_upper` (:641): the pi lemma folds the closed
`log π / 2` factor into `U * 2.15 / 2`; here the outer prime `dG` has no
closed in-tree majorant, so the cap `‖dG‖ ≤ DGhalf` stays an explicit
premise and the chain rule contributes only the `1 / 2` halving).
Honestly flagged: this does NOT close `DG` — it only transports an outer
`Complex.Gamma` prime cap at `s / 2` to a `gammaOf` prime cap at `s`. -/
theorem R02_gammaDerivUp_of_upper (s dG : ℂ) (DGhalf : ℝ)
    (hG : HasDerivAt Complex.Gamma dG (s / 2))
    (hDG : ‖dG‖ ≤ DGhalf) :
    ‖deriv DerivCauchyBridge.gammaOf s‖ ≤ DGhalf / 2 := by
  have hder : deriv DerivCauchyBridge.gammaOf s = dG * ((1 : ℂ) / 2) :=
    (R02_gamma_hasDerivAt s dG hG).deriv
  rw [hder, norm_mul]
  have hhalf : ‖((1 : ℂ) / 2)‖ = (0.5 : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_two]
    norm_num
  rw [hhalf]
  have hle : ‖dG‖ * 0.5 ≤ DGhalf * 0.5 :=
    mul_le_mul_of_nonneg_right hDG (by norm_num)
  have hfin : DGhalf * 0.5 = DGhalf / 2 := by ring
  rw [hfin] at hle
  exact hle

/-- Gamma-deriv numeral missing-spec (filed, not fixed): existence of a
finite uniform `‖deriv gammaOf s‖ ≤ DG` cap on the R02-disc `s`-rect
`Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`, i.e.
`∃ DG, 0 ≤ DG ∧ R02_gammaDeriv_obligation DG`.
Not satisfiable this turn (per-rule-2 no concrete numeral is attempted):
grep record — no uniform Gamma-prime majorant is banked in-tree:
* `DerivCauchyBridge` (`central_cover_assembly.lean:6325-6520`) banks only
  VALUE uppers (`poly_upper_R02_disc`, `pi_upper_R02_disc`,
  `gamma_upper_R02_disc ≤ 40`); no `HasDerivAt` / `deriv` majorant for
  `gammaOf` there;
* `door3_deriv_up.lean:524` `gammaDerivUp_of_sup` is conditional Cauchy
  (needs `DiffContOnCl` + sphere sup, no numeral);
* `door3_digamma.lean:295` `gammaPrime_le_of_psiDisc` is conditional on a
  digamma-disc premise + Gamma-value cap (no closed numeral);
* `Zeta23/GammaFacts.lean:76` gives analyticity only (no norm cap).
`R02_gamma_hasDerivAt` (above) closes the analyticity link; the numeral is
the remaining Gamma-deriv-lane item. -/
def R02_gammaDeriv_missingNumeral_spec : Prop :=
  ∃ DG : ℝ, 0 ≤ DG ∧ R02_gammaDeriv_obligation DG

/-- Zeta-factor prime on R02 (local mirror of `R02_gamma_hasDerivAt` (:1084),
no new import): `zeta = riemannZeta` definitionally
(`riemann_hypothesis.lean:16`), so any outer `HasDerivAt riemannZeta dZ s`
transports by defeq to `HasDerivAt zeta dZ s`.
Banked analyticity supplying `hZ` (grep record, read-only):
* Mathlib `differentiableAt_riemannZeta`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:139`, needs `hs : s ≠ 1`;
  on the R02-disc `s`-rect `Re ∈ [0.05,0.74]`, pole-avoidance follows from
  `re < 1`);
* `Zeta23.FromPNTPlus.ZetaBounds.lean:156` `analyticAt_riemannZeta`
  (same `s ≠ 1` premise; `.deriv.differentiableAt` at `:161-163`);
* `Zeta23.WeilEF.XiLogDeriv.lean:61` `analyticAt_riemannZeta` and
  `Zeta23.XiPrime.Hardy.Basic.lean:156` `analyticAt_riemannZeta` (same shape).
In-tree USE (not a new bank): `zeta_rigorous.lean:712`
  `(differentiableAt_riemannZeta hs)` and `central_cover_assembly.lean:771`
  (notes `differentiableAt_riemannZeta` only away from `1`);
  `DerivCauchyBridge` (`central_cover_assembly.lean:6178-6565`) banks only
  VALUE uppers (`R02_zeta_upper_obligation :6493`), no zeta `HasDerivAt` /
  `deriv` majorant there.
Unlike the Gamma case (poles at `-ℕ`, composition with `s / 2`), there is no
inner chain: `zeta` is the alias itself, so the transport is `rfl`-defeq.
The outer premise `hZ` stays explicit because `riemannZeta` has a pole at `1`.
Honestly flagged: this closes the ANALYTICITY link only; it does NOT close
`DZ` (no uniform `‖deriv zeta s‖` majorant is banked in-tree; per rule 2 no
numeral is attempted here). -/
theorem R02_zeta_hasDerivAt (s dZ : ℂ)
    (hZ : HasDerivAt riemannZeta dZ s) :
    HasDerivAt zeta dZ s := by
  unfold zeta
  exact hZ

/-- The banked partial-product deriv cap stays above tier `0.07`. -/
theorem R02_polyPi_5465_above_tier07 : (0.07 : ℝ) < 54.65 := by
  norm_num

/-- Honest gap of the partial-product cap over tier `0.07`. -/
theorem R02_polyPi_gap : (54.65 : ℝ) - 0.07 = 54.58 := by
  norm_num

/-- Route (b): staged retier — any `M ≥ 67200` closes R02 deriv
conditional on the wide `Λ₀` premise. -/
theorem R02_retier67200_of_Lambda (M : ℝ) (hM : 67200 ≤ M)
    (hL : Door3CellSuppliers.CS_Lambda0_upper_fat)
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02_deriv67200_of_Lambda hL w hw) hM

/-- Staged retier with margin `800` at `68000`. -/
theorem R02_retier68000_of_Lambda
    (hL : Door3CellSuppliers.CS_Lambda0_upper_fat)
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 68000 :=
  R02_retier67200_of_Lambda 68000 (by norm_num) hL w hw

/-- Staged margin witness. -/
theorem R02_retier68000_margin : (68000 : ℝ) - 67200 = 800 := by
  norm_num

/-- Route (b): sharpened retier — any `M ≥ 1402` closes R02 deriv
conditional on the true-scale `M = 10` Lambda premise. -/
theorem R02_retier1402_of_Lambda10 (M : ℝ) (hM : 1402 ≤ M)
    (hL : ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im →
      s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ (10 : ℝ))
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02_deriv1402_of_Lambda10 hL w hw) hM

/-- Sharpened retier with margin `8` at `1410`. -/
theorem R02_retier1410_of_Lambda10
    (hL : ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im →
      s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ (10 : ℝ))
    (w : ℂ) (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 1410 :=
  R02_retier1402_of_Lambda10 1410 (by norm_num) hL w hw

/-- Sharpened margin witness. -/
theorem R02_retier1410_margin : (1410 : ℝ) - 1402 = 8 := by
  norm_num

/-- Route (b): subdivided retier, west half — any `M ≥ 2804` closes
conditional on the west `350.5` sub-ball. -/
theorem R02_retier2804W_of_ball350 (M : ℝ) (hM : 2804 ≤ M)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02W.center
      (R02W.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 350.5)
    (w : ℂ) (hw : R02W.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02W_deriv2804_of_ball350 hBall w hw) hM

/-- Route (b): subdivided retier, east half — any `M ≥ 2804` closes
conditional on the east `350.5` sub-ball. -/
theorem R02_retier2804E_of_ball350 (M : ℝ) (hM : 2804 ≤ M)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02E.center
      (R02E.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 350.5)
    (w : ℂ) (hw : R02E.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02E_deriv2804_of_ball350 hBall w hw) hM

/-- Route (b): subdivided staged retier, west half — any `M ≥ 134400`
closes conditional on the west `16800` sub-ball (documents the exact
doubled-cap retier; honest scope as with the other retier tiers). -/
theorem R02_retier134400W_of_ball16800 (M : ℝ) (hM : 134400 ≤ M)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02W.center
      (R02W.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800)
    (w : ℂ) (hw : R02W.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02W_deriv134400_of_ball16800 hBall w hw) hM

/-- Route (b): subdivided staged retier, east half — any `M ≥ 134400`
closes conditional on the east `16800` sub-ball. -/
theorem R02_retier134400E_of_ball16800 (M : ℝ) (hM : 134400 ≤ M)
    (hBall : ∀ (z : ℂ), z ∈ Metric.closedBall R02E.center
      (R02E.radius + 0.125) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800)
    (w : ℂ) (hw : R02E.mem w) :
    ‖deriv xiShifted w‖ ≤ M :=
  le_trans (R02E_deriv134400_of_ball16800 hBall w hw) hM

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
#print axioms R02W_deriv_of_ballCap125
#print axioms R02E_deriv_of_ballCap125
#print axioms R02_covered_by_halves
#print axioms R02_subdiv_closedForm134400
#print axioms R02_subdiv_doubling
#print axioms R02_subdiv_tier07_needs_ball000875
#print axioms R02_subdiv_halved_radius_blocked
#print axioms R02W_deriv2804_of_ball350
#print axioms R02E_deriv2804_of_ball350
#print axioms R02_poly_hasDerivAt
#print axioms R02_poly_deriv_eq
#print axioms R02_polyDerivUp_of_abs
#print axioms R02_polyDeriv_cap_disc
#print axioms R02_piExp_hasDerivAt
#print axioms R02_pi_hasDerivAt
#print axioms R02_pi_deriv_eq
#print axioms R02_logPi_norm_le
#print axioms R02_piDerivUp_of_upper
#print axioms R02_piVal_cap_disc
#print axioms R02_piDeriv_prod1075
#print axioms R02_piDeriv_cap_disc
#print axioms R02_polyVal_cap_disc
#print axioms R02_polyPiVal_prod42
#print axioms R02_polyPiVal_cap_disc
#print axioms R02_polyPi_hasDerivAt
#print axioms R02_polyPi_deriv_eq
#print axioms R02_polyPiDerivUp_of_caps
#print axioms R02_polyPiDeriv_prod5465
#print axioms R02_polyPiDeriv_cap_disc
#print axioms R02_fullDerivUp_of_factorCaps
#print axioms R02_fullDerivUp_bankedPQ_shape
#print axioms R02_gammaVal_cap_disc
#print axioms R02_polyPiGammaVal_prod1680
#print axioms R02_polyPiGammaValUp_of_caps
#print axioms R02_polyPiGammaVal_cap_disc
#print axioms R02_polyPiGammaZetaValUp_of_caps
#print axioms R02_polyPiGammaZetaVal_cap_disc_of_zeta
#print axioms R02_fullDerivUp_bankedPQG_shape
#print axioms R02_fullDerivUp_bankedUZ10_of_zetaUpper
#print axioms R02_pqGammaDerivUp_of_factorCaps
#print axioms R02_pqGammaDeriv_prod2186
#print axioms R02_pqGammaDerivUp_bankedPQG_shape
#print axioms R02_polyPi_5465_above_tier07
#print axioms R02_polyPi_gap
#print axioms R02_retier67200_of_Lambda
#print axioms R02_retier68000_of_Lambda
#print axioms R02_retier1402_of_Lambda10
#print axioms R02_retier1410_of_Lambda10
#print axioms R02_retier2804W_of_ball350
#print axioms R02_retier2804E_of_ball350
#print axioms R02_retier134400W_of_ball16800
#print axioms R02_retier134400E_of_ball16800

end Door3R02BallAdvance
