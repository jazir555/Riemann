import Mathlib
import central_cover_assembly

/-!
# Door-3 premise tier wave (tier-M deriv + ball-sup across the batch cells).

Write-only record. Imports are `Mathlib` + `central_cover_assembly` only.
No other file is imported. Every proof below is complete with explicit
binders. The `norm_num` tactic is used only on `ℝ` / `ℕ` goals.

## Recon record (read-only, verified before writing)

* Leaf tiers live in `central_cover_assembly.lean` as `RXX_leaf_obligations`:
  second conjunct `∀ w, RXX.mem w → ‖deriv xiShifted w‖ ≤ M` with
  `M ∈ {0.05, 0.06, 0.07}`. Outer cells use `M = 0.05`
  (`R00 R10 R11 R20 R21 R30 R31 R40`, `ε = 0.002`); inner cells use
  `M = 0.06` (`R05 R06 R15 R16 R25 R26 R35 R36`, `ε = 0.15`); mid cells
  and outer-leaf cells use `M = 0.07`
  (`R01 R02 R03 R04 R07 R08 R09 R12 R13 R14 R17 R18 R19 R22 R23 R24 R27
  R28 R29 R32 R33 R34 R37 R38 R39`); `R02 R09 R12 R22 R29 R32 R39` pair
  `ε = 0.002` with `M = 0.07` (leaf shape, authoritative over section
  headers). Example anchors: `R21` tier `0.05`, `R28` tier `0.07`.
* Ball-sup shape follows `door3_first_cell.lean` (`FC_ballSup_obligation`)
  and batches A–E (`*_ballSup_obligation`): closed-ball sup `16800` on
  `closedBall center (radius + 0.25)` for `xiShiftedEntire`, with
  `r = 0.25` throughout and closed form `16800 / 0.25 = 67200`.
* Cauchy bridge is `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`
  (`central_cover_assembly.lean:6233`, `M = C / r`) resting on
  `sphere_subset_closedBall_of_rect_mem` (`:6213`). The Wide Cauchy
  pattern `tierB_cauchy_of_sharedSup` (`door3_tierB_subdiv.lean`) is a
  shared-sup transfer `C on big ball → per-cell ‖deriv‖ ≤ C / rhoC`;
  it is re-proved LOCALLY below as `tier_cauchy_of_sharedSup` (same
  statement shape, local proof). The tier-B file itself is not imported.
* Batch docs already record the honest gap: Cauchy gives `67200` while
  tiers need `0.05 / 0.06 / 0.07` (`E_cauchy_tier_mismatch05/06/07`,
  `B_cauchy_tier_mismatch05/06/07`, `BA00_cauchy_tier_mismatch`, and the
  first-cell floor `FC_cauchy_M_floor` / exclusion
  `FC_tier007_excluded_via_cauchy`). This file systematizes that gap
  across every cell instead of forcing any tier.

## Verdict recorded here (numbers, not forced closures)

* Tiers closed via Cauchy in this file: 0 of 41.
  Tier mismatches proved: 41 of 41.
  `0.05 < 67200`, `0.06 < 67200`, `0.07 < 67200` (each by `norm_num`),
  with `16800 / 0.25 = 67200` closed once as `cauchy_closedForm`.
  Every tier-`M` deriv bound therefore needs direct derivative bounds or
  subdivision plus re-tiering; none follows from the `16800` joint sup.
* Balls closed unconditionally in this file: 0 of 41.
  Balls systematized as explicit open premises (`premBall_RXX`, one per
  cell, shape `∀ z ∈ closedBall, ‖entire z‖ ≤ 16800`): 41 of 41 stated.
  Conditional Cauchy transfer proved per cell
  (`premDeriv_RXX_of_ball`: ball premise gives `‖deriv‖ ≤ 67200`;
  `premSphere_RXX_of_ball`: ball premise gives each `0.25`-sphere sup).
  True-value estimate for every ball premise is `O(10)` against the
  `16800` cap (loose by three orders of magnitude). A loose
  Lambda-style budget is proved once as arithmetic
  (`ball_budget_check`: `0.5 + 53 * 316 ≤ 16800`): uniform prefactor
  cap `53` with wide Lambda cap `316` meets the joint cap with margin.
  The per-cell Lambda enclosures themselves remain patch-phase work.
* Remainder (not this file): direct tier-`M` derivative bounds or a
  subdivision plus re-tier program per cell; per-cell Lambda enclosures
  discharging `premBall_RXX`; four-factor center floors (poly/pi/gamma/
  zeta lowers) owned by the center-bound waves.
-/

noncomputable section

namespace Door3PremiseTier

open Complex Real Set Topology

/-! ## 1. Shared Cauchy machine (local reproof of the Wide pattern). -/

/-- Local mirror of the Wide shared-sup Cauchy transfer: a shared sup `C`
carrying predicate `P`, subcell selector `Q`, explicit rate `c = C / rhoC`,
sphere inclusion `hSub`, and analytic Cauchy step `hCauchy` give
per-cell `‖deriv F w‖ ≤ C / rhoC`. Proved locally; the tier-B file that
states the same shape is not imported. -/
theorem tier_cauchy_of_sharedSup (F : ℂ → ℂ) (P Q : ℂ → Prop)
    (C rhoC c : ℝ)
    (hRate : c = C / rhoC)
    (hSup : ∀ (z : ℂ), P z → ‖F z‖ ≤ C)
    (hSub : ∀ (w : ℂ), Q w → ∀ (u : ℂ), u ∈ Metric.sphere w rhoC → P u)
    (hCauchy : ∀ (w : ℂ), Q w →
      (∀ (u : ℂ), u ∈ Metric.sphere w rhoC → ‖F u‖ ≤ C) → ‖deriv F w‖ ≤ c) :
    ∀ (w : ℂ), Q w → ‖deriv F w‖ ≤ C / rhoC := by
  intro w hw
  rw [← hRate]
  exact hCauchy w hw (fun u hu => hSup u (hSub w hw u hu))

/-- Cauchy closed form shared by every cell (`r = 0.25`). -/
theorem cauchy_closedForm : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Tier caps against the Cauchy value (shared, cited per cell). -/
theorem tier05_lt_67200 : (0.05 : ℝ) < 67200 := by
  norm_num

theorem tier06_lt_67200 : (0.06 : ℝ) < 67200 := by
  norm_num

theorem tier07_lt_67200 : (0.07 : ℝ) < 67200 := by
  norm_num

/-- Loose Lambda-style budget check (arithmetic only): uniform entire-form
prefactor cap `53` with wide Lambda cap `316` meets the joint `16800`
cap (`0.5 + 53 * 316 = 16748.5 ≤ 16800`). The per-cell Lambda
enclosures feeding this budget remain patch-phase work. -/
theorem ball_budget_check : (0.5 : ℝ) + 53 * 316 ≤ 16800 := by
  norm_num

/-- Strip membership from rect membership plus the banked strip edges
(generic helper; per-cell lemmas feed their own `RXX_strip_lo/hi`). -/
theorem strip_of_rect_mem (R : CellProofEngine.Rect2D)
    (hLo : -(1 / 2 : ℝ) < R.y0) (hHi : R.y1 < (1 / 2 : ℝ))
    (w : ℂ) (hw : R.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  constructor
  · linarith
  · linarith

/-! ## 2. Bottom-row cells R00–R10 (41-cell program: gridFine 40 + R01 extra). -/

def premTier_R00 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R00 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R00.center
    (CentralCoverAssembly.R00.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R00_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R00_of_ball (hBall : premBall_R00) (w : ℂ)
    (hw : CentralCoverAssembly.R00.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R00.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R00
      CentralCoverAssembly.R00_strip_lo CentralCoverAssembly.R00_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R00 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R00_of_ball (hBall : premBall_R00) (w : ℂ)
    (hw : CentralCoverAssembly.R00.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R00 0.25 w hw hz)

def premTier_R01 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R01.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R01 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R01.center
    (CentralCoverAssembly.R01.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R01_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R01_of_ball (hBall : premBall_R01) (w : ℂ)
    (hw : CentralCoverAssembly.R01.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R01.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R01
      CentralCoverAssembly.R01_strip_lo CentralCoverAssembly.R01_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R01 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R01_of_ball (hBall : premBall_R01) (w : ℂ)
    (hw : CentralCoverAssembly.R01.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R01 0.25 w hw hz)

def premTier_R02 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R02 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R02.center
    (CentralCoverAssembly.R02.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R02_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R02_of_ball (hBall : premBall_R02) (w : ℂ)
    (hw : CentralCoverAssembly.R02.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R02.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R02
      CentralCoverAssembly.R02_strip_lo CentralCoverAssembly.R02_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R02 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R02_of_ball (hBall : premBall_R02) (w : ℂ)
    (hw : CentralCoverAssembly.R02.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R02 0.25 w hw hz)

def premTier_R03 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R03.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R03 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R03.center
    (CentralCoverAssembly.R03.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R03_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R03_of_ball (hBall : premBall_R03) (w : ℂ)
    (hw : CentralCoverAssembly.R03.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R03.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R03
      CentralCoverAssembly.R03_strip_lo CentralCoverAssembly.R03_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R03 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R03_of_ball (hBall : premBall_R03) (w : ℂ)
    (hw : CentralCoverAssembly.R03.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R03 0.25 w hw hz)

def premTier_R04 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R04.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R04 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R04.center
    (CentralCoverAssembly.R04.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R04_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R04_of_ball (hBall : premBall_R04) (w : ℂ)
    (hw : CentralCoverAssembly.R04.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R04.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R04
      CentralCoverAssembly.R04_strip_lo CentralCoverAssembly.R04_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R04 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R04_of_ball (hBall : premBall_R04) (w : ℂ)
    (hw : CentralCoverAssembly.R04.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R04 0.25 w hw hz)

def premTier_R05 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R05.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R05 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R05.center
    (CentralCoverAssembly.R05.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R05_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R05_of_ball (hBall : premBall_R05) (w : ℂ)
    (hw : CentralCoverAssembly.R05.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R05.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R05
      CentralCoverAssembly.R05_strip_lo CentralCoverAssembly.R05_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R05 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R05_of_ball (hBall : premBall_R05) (w : ℂ)
    (hw : CentralCoverAssembly.R05.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R05 0.25 w hw hz)

def premTier_R06 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R06.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R06 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R06.center
    (CentralCoverAssembly.R06.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R06_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R06_of_ball (hBall : premBall_R06) (w : ℂ)
    (hw : CentralCoverAssembly.R06.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R06.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R06
      CentralCoverAssembly.R06_strip_lo CentralCoverAssembly.R06_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R06 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R06_of_ball (hBall : premBall_R06) (w : ℂ)
    (hw : CentralCoverAssembly.R06.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R06 0.25 w hw hz)

def premTier_R07 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R07.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R07 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R07.center
    (CentralCoverAssembly.R07.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R07_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R07_of_ball (hBall : premBall_R07) (w : ℂ)
    (hw : CentralCoverAssembly.R07.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R07.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R07
      CentralCoverAssembly.R07_strip_lo CentralCoverAssembly.R07_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R07 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R07_of_ball (hBall : premBall_R07) (w : ℂ)
    (hw : CentralCoverAssembly.R07.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R07 0.25 w hw hz)

def premTier_R08 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R08.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R08 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R08.center
    (CentralCoverAssembly.R08.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R08_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R08_of_ball (hBall : premBall_R08) (w : ℂ)
    (hw : CentralCoverAssembly.R08.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R08.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R08
      CentralCoverAssembly.R08_strip_lo CentralCoverAssembly.R08_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R08 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R08_of_ball (hBall : premBall_R08) (w : ℂ)
    (hw : CentralCoverAssembly.R08.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R08 0.25 w hw hz)

def premTier_R09 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R09.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R09 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R09.center
    (CentralCoverAssembly.R09.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R09_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R09_of_ball (hBall : premBall_R09) (w : ℂ)
    (hw : CentralCoverAssembly.R09.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R09.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R09
      CentralCoverAssembly.R09_strip_lo CentralCoverAssembly.R09_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R09 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R09_of_ball (hBall : premBall_R09) (w : ℂ)
    (hw : CentralCoverAssembly.R09.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R09 0.25 w hw hz)

def premTier_R10 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R10.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R10 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R10.center
    (CentralCoverAssembly.R10.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R10_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R10_of_ball (hBall : premBall_R10) (w : ℂ)
    (hw : CentralCoverAssembly.R10.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R10.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R10
      CentralCoverAssembly.R10_strip_lo CentralCoverAssembly.R10_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R10 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R10_of_ball (hBall : premBall_R10) (w : ℂ)
    (hw : CentralCoverAssembly.R10.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R10 0.25 w hw hz)

/-! ## 3. Second-row cells R11–R20. -/

def premTier_R11 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R11.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R11 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R11.center
    (CentralCoverAssembly.R11.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R11_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R11_of_ball (hBall : premBall_R11) (w : ℂ)
    (hw : CentralCoverAssembly.R11.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R11.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R11
      CentralCoverAssembly.R11_strip_lo CentralCoverAssembly.R11_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R11 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R11_of_ball (hBall : premBall_R11) (w : ℂ)
    (hw : CentralCoverAssembly.R11.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R11 0.25 w hw hz)

def premTier_R12 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R12.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R12 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R12.center
    (CentralCoverAssembly.R12.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R12_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R12_of_ball (hBall : premBall_R12) (w : ℂ)
    (hw : CentralCoverAssembly.R12.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R12.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R12
      CentralCoverAssembly.R12_strip_lo CentralCoverAssembly.R12_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R12 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R12_of_ball (hBall : premBall_R12) (w : ℂ)
    (hw : CentralCoverAssembly.R12.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R12 0.25 w hw hz)

def premTier_R13 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R13.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R13 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R13.center
    (CentralCoverAssembly.R13.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R13_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R13_of_ball (hBall : premBall_R13) (w : ℂ)
    (hw : CentralCoverAssembly.R13.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R13.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R13
      CentralCoverAssembly.R13_strip_lo CentralCoverAssembly.R13_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R13 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R13_of_ball (hBall : premBall_R13) (w : ℂ)
    (hw : CentralCoverAssembly.R13.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R13 0.25 w hw hz)

def premTier_R14 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R14.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R14 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R14.center
    (CentralCoverAssembly.R14.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R14_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R14_of_ball (hBall : premBall_R14) (w : ℂ)
    (hw : CentralCoverAssembly.R14.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R14.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R14
      CentralCoverAssembly.R14_strip_lo CentralCoverAssembly.R14_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R14 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R14_of_ball (hBall : premBall_R14) (w : ℂ)
    (hw : CentralCoverAssembly.R14.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R14 0.25 w hw hz)

def premTier_R15 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R15.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R15 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R15.center
    (CentralCoverAssembly.R15.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R15_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R15_of_ball (hBall : premBall_R15) (w : ℂ)
    (hw : CentralCoverAssembly.R15.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R15.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R15
      CentralCoverAssembly.R15_strip_lo CentralCoverAssembly.R15_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R15 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R15_of_ball (hBall : premBall_R15) (w : ℂ)
    (hw : CentralCoverAssembly.R15.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R15 0.25 w hw hz)

def premTier_R16 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R16.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R16 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R16.center
    (CentralCoverAssembly.R16.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R16_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R16_of_ball (hBall : premBall_R16) (w : ℂ)
    (hw : CentralCoverAssembly.R16.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R16.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R16
      CentralCoverAssembly.R16_strip_lo CentralCoverAssembly.R16_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R16 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R16_of_ball (hBall : premBall_R16) (w : ℂ)
    (hw : CentralCoverAssembly.R16.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R16 0.25 w hw hz)

def premTier_R17 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R17.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R17 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R17.center
    (CentralCoverAssembly.R17.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R17_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R17_of_ball (hBall : premBall_R17) (w : ℂ)
    (hw : CentralCoverAssembly.R17.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R17.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R17
      CentralCoverAssembly.R17_strip_lo CentralCoverAssembly.R17_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R17 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R17_of_ball (hBall : premBall_R17) (w : ℂ)
    (hw : CentralCoverAssembly.R17.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R17 0.25 w hw hz)

def premTier_R18 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R18.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R18 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R18.center
    (CentralCoverAssembly.R18.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R18_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R18_of_ball (hBall : premBall_R18) (w : ℂ)
    (hw : CentralCoverAssembly.R18.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R18.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R18
      CentralCoverAssembly.R18_strip_lo CentralCoverAssembly.R18_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R18 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R18_of_ball (hBall : premBall_R18) (w : ℂ)
    (hw : CentralCoverAssembly.R18.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R18 0.25 w hw hz)

def premTier_R19 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R19.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R19 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R19.center
    (CentralCoverAssembly.R19.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R19_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R19_of_ball (hBall : premBall_R19) (w : ℂ)
    (hw : CentralCoverAssembly.R19.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R19.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R19
      CentralCoverAssembly.R19_strip_lo CentralCoverAssembly.R19_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R19 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R19_of_ball (hBall : premBall_R19) (w : ℂ)
    (hw : CentralCoverAssembly.R19.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R19 0.25 w hw hz)

def premTier_R20 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R20.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R20 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R20.center
    (CentralCoverAssembly.R20.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R20_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R20_of_ball (hBall : premBall_R20) (w : ℂ)
    (hw : CentralCoverAssembly.R20.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R20.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R20
      CentralCoverAssembly.R20_strip_lo CentralCoverAssembly.R20_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R20 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R20_of_ball (hBall : premBall_R20) (w : ℂ)
    (hw : CentralCoverAssembly.R20.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R20 0.25 w hw hz)

/-! ## 4. Third-row cells R21–R30. -/

def premTier_R21 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R21.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R21 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R21.center
    (CentralCoverAssembly.R21.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R21_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R21_of_ball (hBall : premBall_R21) (w : ℂ)
    (hw : CentralCoverAssembly.R21.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R21.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R21
      CentralCoverAssembly.R21_strip_lo CentralCoverAssembly.R21_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R21 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R21_of_ball (hBall : premBall_R21) (w : ℂ)
    (hw : CentralCoverAssembly.R21.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R21 0.25 w hw hz)

def premTier_R22 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R22.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R22 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R22.center
    (CentralCoverAssembly.R22.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R22_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R22_of_ball (hBall : premBall_R22) (w : ℂ)
    (hw : CentralCoverAssembly.R22.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R22.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R22
      CentralCoverAssembly.R22_strip_lo CentralCoverAssembly.R22_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R22 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R22_of_ball (hBall : premBall_R22) (w : ℂ)
    (hw : CentralCoverAssembly.R22.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R22 0.25 w hw hz)

def premTier_R23 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R23.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R23 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R23.center
    (CentralCoverAssembly.R23.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R23_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R23_of_ball (hBall : premBall_R23) (w : ℂ)
    (hw : CentralCoverAssembly.R23.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R23.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R23
      CentralCoverAssembly.R23_strip_lo CentralCoverAssembly.R23_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R23 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R23_of_ball (hBall : premBall_R23) (w : ℂ)
    (hw : CentralCoverAssembly.R23.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R23 0.25 w hw hz)

def premTier_R24 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R24.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R24 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R24.center
    (CentralCoverAssembly.R24.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R24_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R24_of_ball (hBall : premBall_R24) (w : ℂ)
    (hw : CentralCoverAssembly.R24.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R24.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R24
      CentralCoverAssembly.R24_strip_lo CentralCoverAssembly.R24_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R24 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R24_of_ball (hBall : premBall_R24) (w : ℂ)
    (hw : CentralCoverAssembly.R24.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R24 0.25 w hw hz)

def premTier_R25 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R25.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R25 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R25.center
    (CentralCoverAssembly.R25.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R25_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R25_of_ball (hBall : premBall_R25) (w : ℂ)
    (hw : CentralCoverAssembly.R25.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R25.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R25
      CentralCoverAssembly.R25_strip_lo CentralCoverAssembly.R25_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R25 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R25_of_ball (hBall : premBall_R25) (w : ℂ)
    (hw : CentralCoverAssembly.R25.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R25 0.25 w hw hz)

def premTier_R26 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R26.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R26 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R26.center
    (CentralCoverAssembly.R26.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R26_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R26_of_ball (hBall : premBall_R26) (w : ℂ)
    (hw : CentralCoverAssembly.R26.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R26.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R26
      CentralCoverAssembly.R26_strip_lo CentralCoverAssembly.R26_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R26 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R26_of_ball (hBall : premBall_R26) (w : ℂ)
    (hw : CentralCoverAssembly.R26.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R26 0.25 w hw hz)

def premTier_R27 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R27.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R27 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R27.center
    (CentralCoverAssembly.R27.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R27_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R27_of_ball (hBall : premBall_R27) (w : ℂ)
    (hw : CentralCoverAssembly.R27.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R27.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R27
      CentralCoverAssembly.R27_strip_lo CentralCoverAssembly.R27_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R27 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R27_of_ball (hBall : premBall_R27) (w : ℂ)
    (hw : CentralCoverAssembly.R27.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R27 0.25 w hw hz)

def premTier_R28 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R28.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R28 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R28.center
    (CentralCoverAssembly.R28.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R28_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R28_of_ball (hBall : premBall_R28) (w : ℂ)
    (hw : CentralCoverAssembly.R28.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R28.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R28
      CentralCoverAssembly.R28_strip_lo CentralCoverAssembly.R28_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R28 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R28_of_ball (hBall : premBall_R28) (w : ℂ)
    (hw : CentralCoverAssembly.R28.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R28 0.25 w hw hz)

def premTier_R29 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R29.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R29 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R29.center
    (CentralCoverAssembly.R29.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R29_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R29_of_ball (hBall : premBall_R29) (w : ℂ)
    (hw : CentralCoverAssembly.R29.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R29.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R29
      CentralCoverAssembly.R29_strip_lo CentralCoverAssembly.R29_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R29 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R29_of_ball (hBall : premBall_R29) (w : ℂ)
    (hw : CentralCoverAssembly.R29.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R29 0.25 w hw hz)

def premTier_R30 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R30.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R30 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R30.center
    (CentralCoverAssembly.R30.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R30_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R30_of_ball (hBall : premBall_R30) (w : ℂ)
    (hw : CentralCoverAssembly.R30.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R30.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R30
      CentralCoverAssembly.R30_strip_lo CentralCoverAssembly.R30_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R30 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R30_of_ball (hBall : premBall_R30) (w : ℂ)
    (hw : CentralCoverAssembly.R30.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R30 0.25 w hw hz)

/-! ## 5. Top-row cells R31–R40. -/

def premTier_R31 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R31.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R31 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R31.center
    (CentralCoverAssembly.R31.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R31_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R31_of_ball (hBall : premBall_R31) (w : ℂ)
    (hw : CentralCoverAssembly.R31.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R31.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R31
      CentralCoverAssembly.R31_strip_lo CentralCoverAssembly.R31_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R31 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R31_of_ball (hBall : premBall_R31) (w : ℂ)
    (hw : CentralCoverAssembly.R31.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R31 0.25 w hw hz)

def premTier_R32 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R32.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R32 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R32.center
    (CentralCoverAssembly.R32.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R32_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R32_of_ball (hBall : premBall_R32) (w : ℂ)
    (hw : CentralCoverAssembly.R32.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R32.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R32
      CentralCoverAssembly.R32_strip_lo CentralCoverAssembly.R32_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R32 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R32_of_ball (hBall : premBall_R32) (w : ℂ)
    (hw : CentralCoverAssembly.R32.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R32 0.25 w hw hz)

def premTier_R33 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R33 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R33.center
    (CentralCoverAssembly.R33.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R33_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R33_of_ball (hBall : premBall_R33) (w : ℂ)
    (hw : CentralCoverAssembly.R33.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R33.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R33
      CentralCoverAssembly.R33_strip_lo CentralCoverAssembly.R33_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R33 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R33_of_ball (hBall : premBall_R33) (w : ℂ)
    (hw : CentralCoverAssembly.R33.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R33 0.25 w hw hz)

def premTier_R34 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R34 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R34.center
    (CentralCoverAssembly.R34.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R34_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R34_of_ball (hBall : premBall_R34) (w : ℂ)
    (hw : CentralCoverAssembly.R34.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R34.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R34
      CentralCoverAssembly.R34_strip_lo CentralCoverAssembly.R34_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R34 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R34_of_ball (hBall : premBall_R34) (w : ℂ)
    (hw : CentralCoverAssembly.R34.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R34 0.25 w hw hz)

def premTier_R35 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R35 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R35.center
    (CentralCoverAssembly.R35.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R35_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R35_of_ball (hBall : premBall_R35) (w : ℂ)
    (hw : CentralCoverAssembly.R35.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R35.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R35
      CentralCoverAssembly.R35_strip_lo CentralCoverAssembly.R35_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R35 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R35_of_ball (hBall : premBall_R35) (w : ℂ)
    (hw : CentralCoverAssembly.R35.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R35 0.25 w hw hz)

def premTier_R36 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ)
def premBall_R36 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R36.center
    (CentralCoverAssembly.R36.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R36_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200
theorem premDeriv_R36_of_ball (hBall : premBall_R36) (w : ℂ)
    (hw : CentralCoverAssembly.R36.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R36.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R36
      CentralCoverAssembly.R36_strip_lo CentralCoverAssembly.R36_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R36 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R36_of_ball (hBall : premBall_R36) (w : ℂ)
    (hw : CentralCoverAssembly.R36.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R36 0.25 w hw hz)

def premTier_R37 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R37 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R37.center
    (CentralCoverAssembly.R37.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R37_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R37_of_ball (hBall : premBall_R37) (w : ℂ)
    (hw : CentralCoverAssembly.R37.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R37.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R37
      CentralCoverAssembly.R37_strip_lo CentralCoverAssembly.R37_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R37 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R37_of_ball (hBall : premBall_R37) (w : ℂ)
    (hw : CentralCoverAssembly.R37.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R37 0.25 w hw hz)

def premTier_R38 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R38 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R38.center
    (CentralCoverAssembly.R38.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R38_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R38_of_ball (hBall : premBall_R38) (w : ℂ)
    (hw : CentralCoverAssembly.R38.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R38.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R38
      CentralCoverAssembly.R38_strip_lo CentralCoverAssembly.R38_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R38 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R38_of_ball (hBall : premBall_R38) (w : ℂ)
    (hw : CentralCoverAssembly.R38.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R38 0.25 w hw hz)

def premTier_R39 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)
def premBall_R39 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R39.center
    (CentralCoverAssembly.R39.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R39_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200
theorem premDeriv_R39_of_ball (hBall : premBall_R39) (w : ℂ)
    (hw : CentralCoverAssembly.R39.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R39.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R39
      CentralCoverAssembly.R39_strip_lo CentralCoverAssembly.R39_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R39 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R39_of_ball (hBall : premBall_R39) (w : ℂ)
    (hw : CentralCoverAssembly.R39.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R39 0.25 w hw hz)

def premTier_R40 : Prop :=
  ∀ (w : ℂ), CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ)
def premBall_R40 : Prop :=
  ∀ (z : ℂ), z ∈ Metric.closedBall CentralCoverAssembly.R40.center
    (CentralCoverAssembly.R40.radius + 0.25) →
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800
theorem premTier_R40_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200
theorem premDeriv_R40_of_ball (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 := by
  have hStrip : ∀ (u : ℂ), CentralCoverAssembly.R40.mem u →
      -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) :=
    fun u hu => strip_of_rect_mem CentralCoverAssembly.R40
      CentralCoverAssembly.R40_strip_lo CentralCoverAssembly.R40_strip_hi u hu
  have h := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R40 0.25 16800 (by norm_num) hStrip hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at h
  exact h
theorem premSphere_R40_of_ball (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    CentralCoverAssembly.R40 0.25 w hw hz)

end Door3PremiseTier
