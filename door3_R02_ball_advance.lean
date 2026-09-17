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
    rw [e1, norm_div, Complex.norm_one, Complex.norm_two]
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
#print axioms R02_retier67200_of_Lambda
#print axioms R02_retier68000_of_Lambda
#print axioms R02_retier1402_of_Lambda10
#print axioms R02_retier1410_of_Lambda10
#print axioms R02_retier2804W_of_ball350
#print axioms R02_retier2804E_of_ball350
#print axioms R02_retier134400W_of_ball16800
#print axioms R02_retier134400E_of_ball16800

end Door3R02BallAdvance
