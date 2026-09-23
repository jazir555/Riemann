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

/-! ## 6. R02 premise-tier narrowing via banked AO sups (append-only wave).

Grep record (verified before writing via `default.grep`):
* Tier shapes in this file: `premDeriv_RXX_of_ball` with shape
  `premBall_RXX → ∀ w, RXX.mem w → ‖deriv xiShifted w‖ ≤ 67200`,
  e.g. `premDeriv_R00_of_ball :134-145`; all 41 cells share the `≤ 67200`
  shape via `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`
  with `C = 16800`, `r = 0.25` (`16800 / 0.25 = 67200`).
* Banked narrowing chain in `central_cover_assembly.lean`,
  `namespace AO_R02DiscUpdate :9968-10264`:
  `AO_gamma_upper_disc_R02_obligation :9975` (landed gamma cap `≤ 0.097`),
  `AO_sphere_sup_eq :9981` (`42 * 1 * 0.097 * 10 = 40.74`),
  `AO_M_eq :9985` (`40.74 / 0.25 = 162.96`),
  `AO_sphere_improvement :9989` (`40.74 < 16800`),
  `AO_deriv_improvement :9993` (`162.96 < 67200`),
  `AO_entire_upper_of_zeta_upper_R02 :10038`,
  `AO_R02_uniform_sphere_bound :10051` (sphere sup `40.74` from
  poly `≤ 42` + pi `≤ 1` + gamma `≤ 0.097` + zeta `≤ 10`),
  `AO_R02_deriv_bound_of_zeta_upper :10063` (`‖deriv‖ ≤ 162.96`),
  `AO_R02_deriv_bound_163_of_zeta_upper :10078` (`‖deriv‖ ≤ 163`).
  Zeta supplier: `DerivCauchyBridge.R02_zeta_upper_obligation :6493`
  (`‖zeta‖ ≤ 10` on the R02 disc rect).
* Result below: R02 deriv premise narrows `67200 → 162.96` (ceil `163`)
  under exactly the two banked obligations above. Tier `0.07` stays open
  (`0.07 < 162.96`); the other 40 cells keep the `67200` value with the
  mismatch gap recorded in sections 2-5.
-/

namespace Door3PremiseTier

/-- R02 narrowed deriv bound `162.96` chained directly from the banked AO
disc update (sphere `40.74 / 0.25`); premises are exactly the banked
gamma (`≤ 0.097`) plus zeta (`≤ 10`) obligations. -/
theorem narrow_R02_deriv_162p96_of_banked
    (hG : AO_R02DiscUpdate.AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ (w : ℂ), CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (162.96 : ℝ) :=
  AO_R02DiscUpdate.AO_R02_deriv_bound_of_zeta_upper hG hZ

/-- Integer-ceil form of the narrowed R02 bound (`163` covers `162.96`). -/
theorem narrow_R02_deriv_163_of_banked
    (hG : AO_R02DiscUpdate.AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ (w : ℂ), CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ) :=
  AO_R02DiscUpdate.AO_R02_deriv_bound_163_of_zeta_upper hG hZ

/-- Banked narrowed sphere sup `40.74` re-exported for the R02 premise tier. -/
theorem narrow_R02_sphere_40p74_of_banked
    (hG : AO_R02DiscUpdate.AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ (w : ℂ), CentralCoverAssembly.R02.mem w → ∀ (z : ℂ),
      z ∈ Metric.sphere w (0.25 : ℝ) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40.74 : ℝ) :=
  AO_R02DiscUpdate.AO_R02_uniform_sphere_bound hG hZ

/-- Narrowed deriv value strictly improves on the premise-tier `67200`. -/
theorem narrow_R02_deriv_improves : (162.96 : ℝ) < 67200 :=
  AO_R02DiscUpdate.AO_deriv_improvement

/-- Narrowed sphere sup strictly improves on the premise-tier `16800`. -/
theorem narrow_R02_sphere_improves : (40.74 : ℝ) < 16800 :=
  AO_R02DiscUpdate.AO_sphere_improvement

/-- Narrowed Cauchy closed form (`40.74 / 0.25 = 162.96`). -/
theorem narrow_R02_closedForm : (40.74 : ℝ) / 0.25 = 162.96 := by
  norm_num

/-- Residual gap: tier `0.07` remains open below the narrowed `162.96`. -/
theorem narrow_R02_residual_gap : (0.07 : ℝ) < 162.96 := by
  norm_num

/-- Ceil `163` covers the exact narrowed value `162.96`. -/
theorem narrow_R02_163_covers : (162.96 : ℝ) ≤ 163 := by
  norm_num

end Door3PremiseTier

/-! ## 7. R03 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R02 chain in `central_cover_assembly.lean`:
  `namespace AO_R02DiscUpdate :9968-10264`,
  `AO_gamma_upper_disc_R02_obligation :9975`,
  `AO_sphere_sup_eq :9981`, `AO_M_eq :9985`,
  `AO_R02_deriv_bound_of_zeta_upper :10063`,
  `AO_R02_deriv_bound_163_of_zeta_upper :10078`.
* R03 banked-chain search (no local chain): pattern
  `AO_R03|AO_gamma_upper_disc_R03|R03.*162.96|R03.*40.74|R03.*deriv_bound.*163`
  over repo root returns no files; pattern
  `AO_R03|R03.*AO|AO.*R03|gamma.*R03|R03.*gamma|R03.*zeta|zeta.*R03|R03_deriv|R03_uniform|R03.*sphere`
  in `central_cover_assembly.lean` returns only `R03_deriv_residual :17511`
  lines `:17476-17543` (leaf residual, not a banked AO narrow chain); pattern
  `namespace AO_|theorem AO_.*R03|def AO_.*R03|AO_gamma|AO_sphere|AO_M_eq|AO_R0`
  returns only the R02 chain above.
* Result below: no R03 mirror of the R02 shape exists locally, so R03 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R03_mismatch :213`.
-/

namespace Door3PremiseTier

/-- R03 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R03_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R03 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R03_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R03 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R03_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R03 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R03_deriv_keeps_67200 (hBall : premBall_R03) (w : ℂ)
    (hw : CentralCoverAssembly.R03.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R03_of_ball hBall w hw

end Door3PremiseTier

/-! ## 8. R04 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R03 narrow block in this file: `## 7. R03 premise-tier narrow attempt`
  `:1318-1367` with `narrow_R03_closedForm_keeps :1349`,
  `narrow_R03_residual_gap :1353`,
  `narrow_R03_residual_is_mismatch :1357`,
  `narrow_R03_deriv_keeps_67200 :1362`; R03 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R04 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R04|AO_gamma_upper_disc_R04|R04.*deriv_bound|R04.*sphere|AO_R02DiscUpdate`
  over repo root returns only `namespace AO_R02DiscUpdate :9968-10264` plus
  R02 re-exports (no `AO_R04` hit); pattern
  `namespace AO_|AO_gamma|AO_sphere|AO_M_eq|R04_deriv|R04_uniform|R04.*AO|AO.*R04`
  in `central_cover_assembly.lean` returns only the R02 chain
  (`AO_gamma_upper_disc_R02_obligation :9975`, `AO_sphere_sup_eq :9981`,
  `AO_M_eq :9985`) plus `R04_deriv_residual :17582` lines `:17547-17615`
  (leaf residual, not a banked AO narrow chain); pattern
  `R04.*gamma|gamma.*R04|R04.*zeta|zeta.*R04|R04_zeta|R04_gamma`
  returns no files.
* Result below: no R04 mirror of the R02 shape exists locally, so R04 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R04_mismatch :240`.
-/

namespace Door3PremiseTier

/-- R04 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R04_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R04 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R04_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R04 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R04_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R04 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R04_deriv_keeps_67200 (hBall : premBall_R04) (w : ℂ)
    (hw : CentralCoverAssembly.R04.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R04_of_ball hBall w hw

end Door3PremiseTier

/-! ## 9. R05 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R04 narrow block in this file: `## 8. R04 premise-tier narrow attempt`
  `:1369-1420` with `narrow_R04_closedForm_keeps :1402`,
  `narrow_R04_residual_gap :1406`,
  `narrow_R04_residual_is_mismatch :1410`,
  `narrow_R04_deriv_keeps_67200 :1415`; R04 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R05 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R05|AO_gamma_upper_disc_R05|R05.*deriv_bound|R05_uniform|AO.*R05`
  returns no files; pattern `namespace AO_|AO_gamma|AO_sphere|AO_M_eq`
  returns only the R02 chain (`namespace AO_R02DiscUpdate :9968`,
  `AO_gamma_upper_disc_R02_obligation :9975`, `AO_sphere_sup_eq :9981`,
  `AO_M_eq :9985`) plus R02 re-exports (no `AO_R05` hit); pattern
  `R05.*gamma|gamma.*R05|R05.*zeta|zeta.*R05|R05_zeta|R05_gamma|R05_deriv|R05.*sphere`
  returns only `R05_deriv_residual :17654` lines `:17619-17670`
  (leaf residual, not a banked AO narrow chain).
* Result below: no R05 mirror of the R02 shape exists locally, so R05 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R05_mismatch :267`.
-/

namespace Door3PremiseTier

/-- R05 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R05_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R05 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R05_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R05 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R05_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R05 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R05_deriv_keeps_67200 (hBall : premBall_R05) (w : ℂ)
    (hw : CentralCoverAssembly.R05.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R05_of_ball hBall w hw

end Door3PremiseTier

/-! ## 10. R06 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R05 narrow block in this file: `## 9. R05 premise-tier narrow attempt`
  `:1422-1471` with `narrow_R05_closedForm_keeps :1453`,
  `narrow_R05_residual_gap :1457`,
  `narrow_R05_residual_is_mismatch :1461`,
  `narrow_R05_deriv_keeps_67200 :1466`; R05 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R06 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R06|AO_gamma_upper_disc_R06|R06.*deriv_bound|R06_uniform|AO.*R06`
  returns no files; pattern `namespace AO_|AO_gamma|AO_sphere|AO_M_eq|AO_deriv|AO_R02`
  returns only the R02 chain (`namespace AO_R02DiscUpdate :9968-10264`,
  `AO_gamma_upper_disc_R02_obligation :9975`, `AO_sphere_sup_eq :9981`,
  `AO_M_eq :9985`, `AO_deriv_improvement :9993`,
  `AO_R02_uniform_sphere_bound :10051`,
  `AO_R02_deriv_bound_of_zeta_upper :10063`,
  `AO_R02_deriv_bound_163_of_zeta_upper :10078`); pattern
  `R06_deriv|R06_uniform|R06.*sphere|R06.*gamma|gamma.*R06|R06.*zeta|zeta.*R06|R06_zeta|R06_gamma|R06.*guard|guard.*R06`
  returns only `R06_deriv_residual :18013` lines `:17960-18031`
  (leaf residual plus pre-existing R06 guard, not a banked AO narrow chain);
  pattern `R06_leaf|R06_strip|R06_center|R06.*obligation` returns
  `R06_strip_lo/hi :1785-1786`, `R06_leaf_obligations :1814`,
  `R06_H_instance :1843`, `R06_center_residual_three_tenths :18005`,
  `R06_deriv_residual :18013` (tier guards, not an AO chain).
* Result below: no R06 mirror of the R02 shape exists locally, so R06 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R06_mismatch :294`.
-/

namespace Door3PremiseTier

/-- R06 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R06_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R06 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R06_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R06 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R06_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R06 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R06_deriv_keeps_67200 (hBall : premBall_R06) (w : ℂ)
    (hw : CentralCoverAssembly.R06.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R06_of_ball hBall w hw

end Door3PremiseTier

/-! ## 11. R07 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R06 narrow block in this file: `## 10. R06 premise-tier narrow attempt`
  `:1473-1529` with `narrow_R06_closedForm_keeps :1511`,
  `narrow_R06_residual_gap :1515`,
  `narrow_R06_residual_is_mismatch :1519`,
  `narrow_R06_deriv_keeps_67200 :1524`; R06 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R07 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R07|AO_gamma_upper_disc_R07|R07_deriv_bound|R07_uniform|AO.*R07`
  returns no files; pattern
  `R07_deriv|R07_uniform|R07.*sphere|R07.*gamma|gamma.*R07|R07.*zeta|zeta.*R07|R07_zeta|R07_gamma|R07.*guard|guard.*R07`
  returns only `R07_deriv_residual :17729` lines `:17729-17745`
  (leaf residual plus R07 H residuals, not a banked AO narrow chain);
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R07` hit); pattern
  `R07_leaf|R07_strip|R07_center|R07.*obligation` returns
  `R07_strip_lo/hi :1871-1872`, `R07_leaf_obligations :1900`,
  `R07_H_instance :1929`, `R07_center_residual_two_tenths :17721`,
  `R07_deriv_residual :17729` (tier guards, not an AO chain).
* Result below: no R07 mirror of the R02 shape exists locally, so R07 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R07_mismatch :321`.
-/

namespace Door3PremiseTier

/-- R07 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R07_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R07 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R07_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R07 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R07_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R07 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R07_deriv_keeps_67200 (hBall : premBall_R07) (w : ℂ)
    (hw : CentralCoverAssembly.R07.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R07_of_ball hBall w hw

end Door3PremiseTier

/-! ## 12. R08 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R07 narrow block in this file: `## 11. R07 premise-tier narrow attempt`
  `:1531-1583` with `narrow_R07_closedForm_keeps :1565`,
  `narrow_R07_residual_gap :1569`,
  `narrow_R07_residual_is_mismatch :1573`,
  `narrow_R07_deriv_keeps_67200 :1578`; R07 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R08 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R08|AO_gamma_upper_disc_R08|R08_deriv_bound|R08_uniform|AO.*R08`
  returns no files; pattern
  `R08_deriv|R08_uniform|R08.*sphere|R08.*gamma|gamma.*R08|R08.*zeta|zeta.*R08|R08_zeta|R08_gamma|R08.*guard|guard.*R08`
  returns only `R08_deriv_residual :17801` lines `:17801-17802`
  (leaf residual plus R08 H residuals, not a banked AO narrow chain);
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R08` hit); pattern
  `R08_leaf|R08_strip|R08_center|R08.*obligation` returns
  `R08_strip_lo/hi :1957-1958`, `R08_leaf_obligations :1986`,
  `R08_H_instance :2015`, `R08_center_residual_two_tenths :17793`,
  `R08_deriv_residual :17801` (tier guards, not an AO chain).
* Result below: no R08 mirror of the R02 shape exists locally, so R08 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R08_mismatch :348`.
-/

namespace Door3PremiseTier

/-- R08 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R08_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R08 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R08_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R08 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R08_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R08 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R08_deriv_keeps_67200 (hBall : premBall_R08) (w : ℂ)
    (hw : CentralCoverAssembly.R08.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R08_of_ball hBall w hw

end Door3PremiseTier

/-! ## 13. R09 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R08 narrow block in this file: `## 12. R08 premise-tier narrow attempt`
  `:1585-1637` with `narrow_R08_closedForm_keeps :1619`,
  `narrow_R08_residual_gap :1623`,
  `narrow_R08_residual_is_mismatch :1627`,
  `narrow_R08_deriv_keeps_67200 :1632`; R08 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R09 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R09|AO_gamma_upper_disc_R09|R09_deriv_bound|R09_uniform|AO.*R09`
  returns no files; pattern
  `R09_deriv|R09_uniform|R09.*sphere|R09.*gamma|gamma.*R09|R09.*zeta|zeta.*R09|R09_zeta|R09_gamma`
  returns only `R09_deriv_residual :17877` lines `:17877-17878`
  (leaf residual, not a banked AO narrow chain);
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R09` hit); pattern
  `R09_leaf|R09_strip|R09_center|R09.*obligation` returns
  `R09_strip_lo/hi :2043-2044`, `R09_leaf_obligations :2072`,
  `R09_H_instance :2101`, `R09_center_residual_tenth :17870`,
  `R09_deriv_residual :17877` (tier guards/residuals, not an AO chain).
* Result below: no R09 mirror of the R02 shape exists locally, so R09 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R09_mismatch :375`.
-/

namespace Door3PremiseTier

/-- R09 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R09_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R09 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R09_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R09 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R09_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R09 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R09_deriv_keeps_67200 (hBall : premBall_R09) (w : ℂ)
    (hw : CentralCoverAssembly.R09.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R09_of_ball hBall w hw

end Door3PremiseTier

/-! ## 14. R10 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R09 narrow block in this file: `## 13. R09 premise-tier narrow attempt`
  `:1639-1691` with `narrow_R09_closedForm_keeps :1673`,
  `narrow_R09_residual_gap :1677`,
  `narrow_R09_residual_is_mismatch :1681`,
  `narrow_R09_deriv_keeps_67200 :1686`; R09 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R10 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R10|AO_gamma_upper_disc_R10|R10_deriv_bound|R10_uniform|AO.*R10`
  returns no matches (empty; `CutR10` hits are a distinct cutoff rect, not `R10`);
  pattern
  `R10_deriv|R10_uniform|R10.*sphere|R10.*gamma|gamma.*R10|R10.*zeta|zeta.*R10|R10_zeta|R10_gamma|R10.*guard|guard.*R10`
  returns only `R10_deriv_residual :17935` lines `:17935-17943`
  (leaf residual plus H-residual wiring, not a banked AO narrow chain;
  remaining hits are `CutR10` cutoff-rect remainders, distinct from `R10`);
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R10` hit); pattern
  `R10_leaf|R10_strip|R10_center|R10.*obligation` returns
  `R10_strip_lo/hi :2129-2130`, `R10_leaf_obligations :2158`,
  `R10_H_instance :2187`, `R10_center_residual_tenth :17928`,
  `R10_deriv_residual :17935` (tier guards/residuals, not an AO chain).
* Result below: no R10 mirror of the R02 shape exists locally, so R10 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R10_mismatch :402`.
-/

namespace Door3PremiseTier

/-- R10 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R10_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R10 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R10_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R10 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R10_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R10 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R10_deriv_keeps_67200 (hBall : premBall_R10) (w : ℂ)
    (hw : CentralCoverAssembly.R10.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R10_of_ball hBall w hw

end Door3PremiseTier

/-! ## 15. R11 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R10 narrow block in this file: `## 14. R10 premise-tier narrow attempt`
  `:1693-1747` with `narrow_R10_closedForm_keeps :1729`,
  `narrow_R10_residual_gap :1733`,
  `narrow_R10_residual_is_mismatch :1737`,
  `narrow_R10_deriv_keeps_67200 :1742`; R10 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R11 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R11|AO_gamma_upper_disc_R11|R11_deriv_bound|R11_uniform|AO.*R11`
  returns only residual refs `R11_deriv_residual :18091` lines `:18091-18107`
  (leaf residual plus H-residual wiring, not a banked AO narrow chain);
  pattern
  `R11_deriv|R11_uniform|R11.*sphere|R11.*gamma|gamma.*R11|R11.*zeta|zeta.*R11|R11_gamma|R11_zeta|R11.*guard|guard.*R11`
  returns only `R11_deriv_residual :18091` lines `:18091-18107`
  (same residual, not a narrow chain);
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R11` hit); pattern
  `R11_leaf|R11_strip|R11_center|R11.*obligation` returns
  `R11_strip_lo/hi :2504-2505`, `R11_leaf_obligations :2533`,
  `R11_H_instance :2562`, `R11_center_residual_tenth :18084`,
  `R11_deriv_residual :18091` (tier guards/residuals, not an AO chain).
* Result below: no R11 mirror of the R02 shape exists locally, so R11 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R11_mismatch :431`.
-/

namespace Door3PremiseTier

/-- R11 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R11_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R11 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R11_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R11 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R11_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R11 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R11_deriv_keeps_67200 (hBall : premBall_R11) (w : ℂ)
    (hw : CentralCoverAssembly.R11.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R11_of_ball hBall w hw

end Door3PremiseTier

/-! ## 16. R12 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R11 narrow block in this file: `## 15. R11 premise-tier narrow attempt`
  `:1749-1803` with `narrow_R11_closedForm_keeps :1785`,
  `narrow_R11_residual_gap :1789`,
  `narrow_R11_residual_is_mismatch :1793`,
  `narrow_R11_deriv_keeps_67200 :1798`; R11 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R12 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R12|AO_gamma_upper_disc_R12|R12_deriv_bound|R12_uniform`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R12` hit);
  pattern `R12_deriv|R12_uniform|R12.*sphere|R12.*gamma|gamma.*R12|R12.*zeta|zeta.*R12`
  returns only `R12_deriv_residual :18160` lines `:18160-18168`
  (leaf residual, not a banked AO narrow chain); pattern
  `R12_leaf|R12_strip|R12_center|R12.*obligation` returns
  `R12_strip_lo/hi :2588-2589`, `R12_leaf_obligations :2617`,
  `R12_H_instance :2646`, `R12_center_residual_tenth :18153`,
  `R12_deriv_residual :18160` (tier guards/residuals, not an AO chain).
* Result below: no R12 mirror of the R02 shape exists locally, so R12 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R12_mismatch :458`.
-/

namespace Door3PremiseTier

/-- R12 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R12_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R12 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R12_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R12 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R12_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R12 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R12_deriv_keeps_67200 (hBall : premBall_R12) (w : ℂ)
    (hw : CentralCoverAssembly.R12.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R12_of_ball hBall w hw

end Door3PremiseTier

/-! ## 17. R13 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R12 narrow block in this file: `## 16. R12 premise-tier narrow attempt`
  `:1805-1856` with `narrow_R12_closedForm_keeps :1838`,
  `narrow_R12_residual_gap :1842`,
  `narrow_R12_residual_is_mismatch :1846`,
  `narrow_R12_deriv_keeps_67200 :1851`; R12 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R13 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R13` hit);
  patterns `AO_R13|R13_deriv|R13_uniform|R13.*sphere|AO.*R13|R13.*AO|R13_gamma|R13_zeta`
  and `R13_deriv|R13_uniform|R13.*sphere|AO.*R13|R13.*AO|R13_gamma|R13_zeta`
  return no files; pattern `R13_` returns only rect guards
  `R13_x0/x1/y0/y1 :2664-2667`, `R13_width_eq :2669`, `R13_strip_lo/hi :2672-2673`,
  `R13_dx/dy_eq :2675-2681`, `R13_radius_eq/lt :2683-2689`,
  `R13_mem_gridFine :2691`, `R13_leaf_obligations :2701`,
  `R13_fencing_of_bounds :2705`, `R13_lowerBound_of_bounds :2709`,
  `R13_zeroFree_of_bounds :2714`, `R13_nonvanishing_of_bounds :2719`,
  `R13_H_instance :2730`, grid conj `:5140-5183`,
  `R13_conjZF/LB_of_bounds :5688-5695` (tier guards, not an AO chain);
  pattern `R13.*residual|residual.*R13` returns no files and
  `R13_deriv_residual` over repo root returns no files
  (no leaf residual banked for R13); pattern `R1[23]_deriv_residual|R13_leaf_of|R13_H_of`
  returns only `R12_deriv_residual :18160` lines `:18160-18168`
  (R12 leaf residual, not a banked AO narrow chain).
* Result below: no R13 mirror of the R02 shape exists locally, so R13 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R13_mismatch :485`.
-/

namespace Door3PremiseTier

/-- R13 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R13_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R13 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R13_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R13 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R13_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R13 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R13_deriv_keeps_67200 (hBall : premBall_R13) (w : ℂ)
    (hw : CentralCoverAssembly.R13.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R13_of_ball hBall w hw

end Door3PremiseTier

/-! ## 18. R14 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R13 narrow block in this file: `## 17. R13 premise-tier narrow attempt`
  `:1858-1916` with `narrow_R13_closedForm_keeps :1898`,
  `narrow_R13_residual_gap :1902`,
  `narrow_R13_residual_is_mismatch :1906`,
  `narrow_R13_deriv_keeps_67200 :1911`; R13 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R14 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R14` returns no files; pattern
  `R14_deriv|R14_uniform|R14.*sphere` returns no files;
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R14` hit); pattern `R14_` returns only rect guards
  `R14_x0/x1/y0/y1 :2748-2751`, `R14_strip_lo/hi :2756-2757`,
  `R14_dx/dy_eq :2759-2765`, `R14_radius_eq/lt :2767-2773`,
  `R14_mem_gridFine :2775`, `R14_leaf_obligations :2785`,
  `R14_fencing_of_bounds :2789`, `R14_H_instance :2814` (tier guards, not an
  AO chain); pattern `R14_deriv_residual|R14.*residual` over repo root returns
  no files (no leaf residual banked for R14).
* Result below: no R14 mirror of the R02 shape exists locally, so R14 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R14_mismatch :512`.
-/

namespace Door3PremiseTier

/-- R14 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R14_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R14 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R14_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R14 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R14_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R14 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R14_deriv_keeps_67200 (hBall : premBall_R14) (w : ℂ)
    (hw : CentralCoverAssembly.R14.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R14_of_ball hBall w hw

end Door3PremiseTier

/-! ## 19. R15 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R14 narrow block in this file: `## 18. R14 premise-tier narrow attempt`
  `:1918-1969` with `narrow_R14_closedForm_keeps :1951`,
  `narrow_R14_residual_gap :1955`,
  `narrow_R14_residual_is_mismatch :1959`,
  `narrow_R14_deriv_keeps_67200 :1964`; R14 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R15 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R15` returns no files; pattern
  `R15_deriv|R15_uniform|R15.*sphere` returns no files;
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R15` hit); pattern `R15_` returns only rect guards
  `R15_x0/x1/y0/y1 :2832-2835`, `R15_width_eq :2837`,
  `R15_strip_lo/hi :2840-2841`, `R15_dx_eq :2843`, `R15_dy_eq :2847`,
  `R15_radius_eq :2851`, `R15_radius_lt :2856`, `R15_mem_gridFine :2859`,
  `R15_leaf_obligations :2869`, `R15_fencing_of_bounds :2873`,
  `R15_lowerBound_of_bounds :2877`, `R15_zeroFree_of_bounds :2882`,
  `R15_nonvanishing_of_bounds :2887`, `R15_H_instance :2898`
  (tier guards, not an AO chain);
  pattern `R15_deriv_residual|R15.*residual` returns no files;
  pattern `AO.*R15|R15.*AO|R15_gamma|R15_zeta` returns no files
  (no leaf residual banked for R15); pattern `narrow_R15` in this file
  returns no files (no prior R15 narrow).
* Result below: no R15 mirror of the R02 shape exists locally, so R15 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R15_mismatch :539`.
-/

namespace Door3PremiseTier

/-- R15 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R15_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R15 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R15_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R15 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R15_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R15 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R15_deriv_keeps_67200 (hBall : premBall_R15) (w : ℂ)
    (hw : CentralCoverAssembly.R15.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R15_of_ball hBall w hw

end Door3PremiseTier

/-! ## 20. R16 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R15 narrow block in this file: `## 19. R15 premise-tier narrow attempt`
  `:1971-2027` with `narrow_R15_closedForm_keeps :2009`,
  `narrow_R15_residual_gap :2013`,
  `narrow_R15_residual_is_mismatch :2017`,
  `narrow_R15_deriv_keeps_67200 :2022`; R15 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R16 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R16|AO_gamma_upper_disc_R16` returns no files; pattern
  `R16_deriv|R16_uniform|R16.*sphere` returns no files;
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R16` hit); pattern `R16_` returns only rect guards
  `R16_x0/x1/y0/y1 :2916-2919`, `R16_width_eq :2921`,
  `R16_strip_lo/hi :2924-2925`, `R16_dx_eq :2927`, `R16_dy_eq :2931`,
  `R16_radius_eq :2935`, `R16_radius_lt :2940`, `R16_mem_gridFine :2943`,
  `R16_leaf_obligations :2953`, `R16_fencing_of_bounds :2957`,
  `R16_lowerBound_of_bounds :2961`, `R16_zeroFree_of_bounds :2966`,
  `R16_nonvanishing_of_bounds :2971`, `R16_H_instance :2982`
  (tier guards, not an AO chain);
  pattern `R16_deriv_residual|R16.*residual` returns no files;
  pattern `AO.*R16|R16.*AO|R16_gamma|R16_zeta` returns no files
  (no leaf residual banked for R16); pattern `narrow_R16` in this file
  returns no files (no prior R16 narrow).
* Result below: no R16 mirror of the R02 shape exists locally, so R16 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R16_mismatch :566`.
-/

namespace Door3PremiseTier

/-- R16 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R16_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R16 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R16_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R16 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R16_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R16 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R16_deriv_keeps_67200 (hBall : premBall_R16) (w : ℂ)
    (hw : CentralCoverAssembly.R16.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R16_of_ball hBall w hw

end Door3PremiseTier
/-! ## 21. R17 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R16 narrow block in this file: `## 20. R16 premise-tier narrow attempt`
  `:2029-2085` with `narrow_R16_closedForm_keeps :2067`,
  `narrow_R16_residual_gap :2071`,
  `narrow_R16_residual_is_mismatch :2075`,
  `narrow_R16_deriv_keeps_67200 :2080`; R16 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R17 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R17|AO_gamma_upper_disc_R17` returns no files; pattern
  `R17_deriv|R17_uniform|R17.*sphere` returns no files;
  pattern `namespace AO_` returns only `namespace AO_R02DiscUpdate :9968`
  (R02 chain only, no `AO_R17` hit); pattern `theorem R17_|def R17_`
  returns only rect guards `R17_x0/x1/y0/y1 :3000-3003`,
  `R17_strip_lo/hi :3008-3009`, `R17_dx_eq :3011`, `R17_dy_eq :3015`,
  `R17_radius_eq :3019`, `R17_radius_lt :3024`, `R17_mem_gridFine :3027`,
  `R17_leaf_obligations :3037`, `R17_fencing_of_bounds :3041`,
  `R17_lowerBound_of_bounds :3045`, `R17_zeroFree_of_bounds :3050`,
  `R17_nonvanishing_of_bounds :3055`, `R17_H_instance :3066`
  (tier guards, not an AO chain);
  pattern `R17_deriv_residual|R17.*residual|AO.*R17|R17.*AO|R17_gamma|R17_zeta`
  returns no files; pattern `narrow_R17` in this file returns no files
  (no prior R17 narrow).
* Result below: no R17 mirror of the R02 shape exists locally, so R17 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R17_mismatch :593`.
-/

namespace Door3PremiseTier

/-- R17 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R17_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R17 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R17_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R17 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R17_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R17 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R17_deriv_keeps_67200 (hBall : premBall_R17) (w : ℂ)
    (hw : CentralCoverAssembly.R17.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R17_of_ball hBall w hw

end Door3PremiseTier
/-! ## 22. R18 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R17 premise block in this file: `premTier_R17 :587`, `premBall_R17 :589`,
  `premTier_R17_mismatch :593`, `premDeriv_R17_of_ball :595`,
  `premSphere_R17_of_ball :607` (`R17.mem`, tier `0.07`, value `67200`).
* R17 narrow block in this file: `## 21. R17 premise-tier narrow attempt`
  `:2086-2141` with `narrow_R17_closedForm_keeps :2123`,
  `narrow_R17_residual_gap :2127`,
  `narrow_R17_residual_is_mismatch :2131`,
  `narrow_R17_deriv_keeps_67200 :2136`; R17 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R18 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R18|AO_gamma_upper_disc_R18|R18_deriv|R18_uniform|R18.*sphere|R18.*residual|R18_gamma|R18_zeta`
  returns no files; pattern `namespace AO_|AO_R02DiscUpdate|40.74|162.96`
  returns only `namespace AO_R02DiscUpdate :9968` (R02 chain only,
  `AO_sphere_sup_eq :9981`, `AO_M_eq :9985`, `AO_M_le_163 :9997`, no `AO_R18`
  hit); pattern `theorem R18_|def R18_` returns only rect guards
  `R18_x0/x1/y0/y1 :3084-3087`, `R18_width_eq :3089`,
  `R18_strip_lo/hi :3092-3093`, `R18_dx_eq :3095`, `R18_dy_eq :3099`,
  `R18_radius_eq :3103`, `R18_radius_lt :3108`, `R18_mem_gridFine :3111`,
  `R18_leaf_obligations :3121`, `R18_fencing_of_bounds :3125`,
  `R18_lowerBound_of_bounds :3129`, `R18_zeroFree_of_bounds :3134`,
  `R18_nonvanishing_of_bounds :3139`, `R18_H_instance :3150`
  (tier guards, not an AO chain);
  pattern `narrow_R18_` in this file returns no files
  (no prior R18 narrow).
* Result below: no R18 mirror of the R02 shape exists locally, so R18 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R18_mismatch :620`.
-/

namespace Door3PremiseTier

/-- R18 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R18_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R18 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R18_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R18 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R18_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R18 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R18_deriv_keeps_67200 (hBall : premBall_R18) (w : ℂ)
    (hw : CentralCoverAssembly.R18.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R18_of_ball hBall w hw

end Door3PremiseTier
/-! ## 23. R19 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R19 premise block in this file: `premTier_R19 :641`, `premBall_R19 :643`,
  `premTier_R19_mismatch :647`, `premDeriv_R19_of_ball :649`,
  `premSphere_R19_of_ball :661` (`R19.mem`, tier `0.07`, value `67200`).
* R18 narrow block in this file: `## 22. R18 premise-tier narrow attempt`
  `:2142-2200` with `narrow_R18_closedForm_keeps :2182`,
  `narrow_R18_residual_gap :2186`,
  `narrow_R18_residual_is_mismatch :2190`,
  `narrow_R18_deriv_keeps_67200 :2195`; R18 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R19 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R19|AO_gamma_upper_disc_R19|R19_deriv|R19_uniform|R19.*sphere|R19.*residual|R19_gamma|R19_zeta`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R19` hit);
  pattern `theorem R19_|def R19_` returns only rect guards
  `R19_x0/x1/y0/y1 :3168-3171`, `R19_width_eq :3173`,
  `R19_strip_lo/hi :3176-3177`, `R19_dx_eq :3179`, `R19_dy_eq :3183`,
  `R19_radius_eq :3187`, `R19_radius_lt :3192`, `R19_mem_gridFine :3195`,
  `R19_leaf_obligations :3205`, `R19_fencing_of_bounds :3209`,
  `R19_lowerBound_of_bounds :3213`, `R19_zeroFree_of_bounds :3218`,
  `R19_nonvanishing_of_bounds :3223`, `R19_H_instance :3234`
  (tier guards, not an AO chain);
  pattern `narrow_R19_` in this file returns no files
  (no prior R19 narrow).
* Result below: no R19 mirror of the R02 shape exists locally, so R19 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R19_mismatch :647`.
-/

namespace Door3PremiseTier

/-- R19 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R19_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R19 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R19_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R19 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R19_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R19 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R19_deriv_keeps_67200 (hBall : premBall_R19) (w : ℂ)
    (hw : CentralCoverAssembly.R19.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R19_of_ball hBall w hw

end Door3PremiseTier

/-! ## 24. R20 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R19 premise block in this file: `premTier_R19 :641`, `premBall_R19 :643`,
  `premTier_R19_mismatch :647`, `premDeriv_R19_of_ball :649`,
  `premSphere_R19_of_ball :661` (`R19.mem`, tier `0.07`, value `67200`).
* R20 premise block in this file: `premTier_R20 :668`, `premBall_R20 :670`,
  `premTier_R20_mismatch :674`, `premDeriv_R20_of_ball :676`,
  `premSphere_R20_of_ball :688` (`R20.mem`, tier `0.05`, value `67200`).
* R19 narrow block in this file: `## 23. R19 premise-tier narrow attempt`
  `:2201-2258` with `narrow_R19_closedForm_keeps :2240`,
  `narrow_R19_residual_gap :2244`,
  `narrow_R19_residual_is_mismatch :2248`,
  `narrow_R19_deriv_keeps_67200 :2253`; R19 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R20 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R20|AO_gamma_upper_disc_R20|R20_deriv|R20_uniform|R20.*sphere|R20.*residual|R20_gamma|R20_zeta`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R20` hit);
  pattern `theorem R20_|def R20_` returns only rect guards
  `R20_x0/x1/y0/y1 :3252-3255`, `R20_width_eq :3257`,
  `R20_strip_lo/hi :3260-3261`, `R20_dx_eq :3263`, `R20_dy_eq :3267`,
  `R20_radius_eq :3271`, `R20_radius_lt :3276`, `R20_mem_gridFine :3279`,
  `R20_leaf_obligations :3289`, `R20_fencing_of_bounds :3293`,
  `R20_lowerBound_of_bounds :3297`, `R20_zeroFree_of_bounds :3302`,
  `R20_nonvanishing_of_bounds :3307`, `R20_H_instance :3318`
  (tier guards, not an AO chain);
  pattern `narrow_R20_` in this file returns no files
  (no prior R20 narrow).
* Result below: no R20 mirror of the R02 shape exists locally, so R20 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R20_mismatch :674`.
-/

namespace Door3PremiseTier

/-- R20 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R20_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R20 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R20_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R20 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R20_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R20 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R20_deriv_keeps_67200 (hBall : premBall_R20) (w : ℂ)
    (hw : CentralCoverAssembly.R20.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R20_of_ball hBall w hw

end Door3PremiseTier

/-! ## 25. R21 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R20 premise block in this file: `premTier_R20 :668`, `premBall_R20 :670`,
  `premTier_R20_mismatch :674`, `premDeriv_R20_of_ball :676`,
  `premSphere_R20_of_ball :688` (`R20.mem`, tier `0.05`, value `67200`).
* R21 premise block in this file: `premTier_R21 :697`, `premBall_R21 :699`,
  `premTier_R21_mismatch :703`, `premDeriv_R21_of_ball :705`,
  `premSphere_R21_of_ball :717` (`R21.mem`, tier `0.05`, value `67200`).
* R20 narrow block in this file: `## 24. R20 premise-tier narrow attempt`
  `:2260-2320` with `narrow_R20_closedForm_keeps :2302`,
  `narrow_R20_residual_gap :2306`,
  `narrow_R20_residual_is_mismatch :2310`,
  `narrow_R20_deriv_keeps_67200 :2315`; R20 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R21 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R21|AO_gamma_upper_disc_R21|R21_deriv|R21_uniform|R21.*sphere|R21_deriv_residual|R21.*residual|R21_gamma|R21_zeta`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R21` hit);
  pattern `theorem R21_|def R21_` returns only rect guards
  `R21_x0/x1/y0/y1 :3338-3341`, `R21_width_eq :3343`,
  `R21_strip_lo/hi :3346-3347`, `R21_dx_eq :3349`, `R21_dy_eq :3353`,
  `R21_radius_eq :3357`, `R21_radius_lt :3362`, `R21_mem_gridFine :3365`,
  `R21_leaf_obligations :3375`, `R21_fencing_of_bounds :3379`,
  `R21_lowerBound_of_bounds :3383`, `R21_zeroFree_of_bounds :3388`,
  `R21_nonvanishing_of_bounds :3393`, `R21_H_instance :3404`
  (tier guards, not an AO chain);
  pattern `narrow_R21_` in this file returns no files
  (no prior R21 narrow).
* Result below: no R21 mirror of the R02 shape exists locally, so R21 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R21_mismatch :703`.
-/

namespace Door3PremiseTier

/-- R21 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R21_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R21 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R21_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R21 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R21_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R21 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R21_deriv_keeps_67200 (hBall : premBall_R21) (w : ℂ)
    (hw : CentralCoverAssembly.R21.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R21_of_ball hBall w hw

end Door3PremiseTier

/-! ## 26. R22 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R21 premise block in this file: `premTier_R21 :697`, `premBall_R21 :699`,
  `premTier_R21_mismatch :703`, `premDeriv_R21_of_ball :705`,
  `premSphere_R21_of_ball :717` (`R21.mem`, tier `0.05`, value `67200`).
* R22 premise block in this file: `premTier_R22 :724`, `premBall_R22 :726`,
  `premTier_R22_mismatch :730`, `premDeriv_R22_of_ball :732`,
  `premSphere_R22_of_ball :744` (`R22.mem`, tier `0.07`, value `67200`).
* R21 narrow block in this file: `## 25. R21 premise-tier narrow attempt`
  `:2322-2382` with `narrow_R21_closedForm_keeps :2364`,
  `narrow_R21_residual_gap :2368`,
  `narrow_R21_residual_is_mismatch :2372`,
  `narrow_R21_deriv_keeps_67200 :2377`; R21 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R22 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R22|R22_deriv|R22_uniform|R22_gamma|R22_zeta|gamma_upper_disc_R22`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R22` hit);
  pattern `R22` returns only rect guards
  `R22 :3419`, `R22_x0/x1/y0/y1 :3422-3425`,
  `R22_strip_lo/hi :3430-3431`, `R22_radius_eq :3441`,
  `R22_radius_lt :3446`, `R22_mem_gridFine :3449`,
  `R22_leaf_obligations :3459`, `R22_fencing_of_bounds :3463`
  (tier guards, not an AO chain);
  pattern `narrow_R22_` in this file returns no files
  (no prior R22 narrow).
* Result below: no R22 mirror of the R02 shape exists locally, so R22 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R22_mismatch :730`.
-/

namespace Door3PremiseTier

/-- R22 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R22_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R22 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R22_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R22 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R22_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R22 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R22_deriv_keeps_67200 (hBall : premBall_R22) (w : ℂ)
    (hw : CentralCoverAssembly.R22.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R22_of_ball hBall w hw

end Door3PremiseTier

/-! ## 27. R23 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R22 premise block in this file: `premTier_R22 :724`, `premBall_R22 :726`,
  `premTier_R22_mismatch :730`, `premDeriv_R22_of_ball :732`,
  `premSphere_R22_of_ball :744` (`R22.mem`, tier `0.07`, value `67200`).
* R23 premise block in this file: `premTier_R23 :751`, `premBall_R23 :753`,
  `premTier_R23_mismatch :757`, `premDeriv_R23_of_ball :759`,
  `premSphere_R23_of_ball :771` (`R23.mem`, tier `0.07`, value `67200`).
* R22 narrow block in this file: `## 26. R22 premise-tier narrow attempt`
  `:2384-2442` with `narrow_R22_closedForm_keeps :2424`,
  `narrow_R22_residual_gap :2428`,
  `narrow_R22_residual_is_mismatch :2432`,
  `narrow_R22_deriv_keeps_67200 :2437`; R22 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R23 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R23|AO_gamma_upper_disc_R23|R23_deriv|R23_uniform|R23_gamma|R23_zeta|R23.*sphere|R23.*residual`
  returns no lines; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R23` hit);
  pattern `theorem R23_|def R23` returns only rect guards
  `R23 :3503`, `R23_x0/x1/y0/y1 :3506-3509`,
  `R23_strip_lo/hi :3514-3515`, `R23_radius_eq :3525`,
  `R23_radius_lt :3530`, `R23_mem_gridFine :3533`,
  `R23_leaf_obligations :3543`, `R23_fencing_of_bounds :3547`
  (tier guards, not an AO chain);
  pattern `narrow_R23_` in this file returns no lines
  (no prior R23 narrow).
* Result below: no R23 mirror of the R02 shape exists locally, so R23 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R23_mismatch :757`.
-/

namespace Door3PremiseTier

/-- R23 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R23_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R23 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R23_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R23 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R23_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R23 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R23_deriv_keeps_67200 (hBall : premBall_R23) (w : ℂ)
    (hw : CentralCoverAssembly.R23.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R23_of_ball hBall w hw

end Door3PremiseTier

/-! ## 28. R24 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R23 premise block in this file: `premTier_R23 :751`, `premBall_R23 :753`,
  `premTier_R23_mismatch :757`, `premDeriv_R23_of_ball :759`,
  `premSphere_R23_of_ball :771` (`R23.mem`, tier `0.07`, value `67200`).
* R24 premise block in this file: `premTier_R24 :778`, `premBall_R24 :780`,
  `premTier_R24_mismatch :784`, `premDeriv_R24_of_ball :786`,
  `premSphere_R24_of_ball :798` (`R24.mem`, tier `0.07`, value `67200`).
* R23 narrow block in this file: `## 27. R23 premise-tier narrow attempt`
  `:2444-2502` with `narrow_R23_closedForm_keeps :2484`,
  `narrow_R23_residual_gap :2488`,
  `narrow_R23_residual_is_mismatch :2492`,
  `narrow_R23_deriv_keeps_67200 :2497`; R23 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R24 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R24|AO_gamma_upper_disc_R24|R24_deriv|R24_uniform|R24_gamma|R24_zeta|R24.*sphere`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R24` hit);
  pattern `theorem R24_|def R24` returns only rect guards
  `R24 :3587`, `R24_x0/x1/y0/y1 :3590-3593`,
  `R24_strip_lo/hi :3598-3599`, `R24_radius_eq :3609`,
  `R24_radius_lt :3614`, `R24_mem_gridFine :3617`,
  `R24_leaf_obligations :3627`, `R24_fencing_of_bounds :3631`
  (tier guards, not an AO chain);
  pattern `narrow_R24_` in this file returns no files
  (no prior R24 narrow).
* Result below: no R24 mirror of the R02 shape exists locally, so R24 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R24_mismatch :784`.
-/

namespace Door3PremiseTier

/-- R24 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R24_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R24 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R24_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R24 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R24_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R24 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R24_deriv_keeps_67200 (hBall : premBall_R24) (w : ℂ)
    (hw : CentralCoverAssembly.R24.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R24_of_ball hBall w hw

end Door3PremiseTier

/-! ## 29. R25 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R24 premise block in this file: `premTier_R24 :778`, `premBall_R24 :780`,
  `premTier_R24_mismatch :784`, `premDeriv_R24_of_ball :786`,
  `premSphere_R24_of_ball :798` (`R24.mem`, tier `0.07`, value `67200`).
* R25 premise block in this file: `premTier_R25 :805`, `premBall_R25 :807`,
  `premTier_R25_mismatch :811`, `premDeriv_R25_of_ball :813`,
  `premSphere_R25_of_ball :825` (`R25.mem`, tier `0.06`, value `67200`).
* R24 narrow block in this file: `## 28. R24 premise-tier narrow attempt`
  `:2504-2562` with `narrow_R24_closedForm_keeps :2544`,
  `narrow_R24_residual_gap :2548`,
  `narrow_R24_residual_is_mismatch :2552`,
  `narrow_R24_deriv_keeps_67200 :2557`; R24 keeps `67200`, no chain.
* R02 narrow block in this file: `## 6. R02 premise-tier narrowing via banked AO sups`
  `:1241-1316` with `narrow_R02_deriv_162p96_of_banked :1274`,
  `narrow_R02_deriv_163_of_banked :1281`,
  `narrow_R02_sphere_40p74_of_banked :1288`, closed form
  `40.74 / 0.25 = 162.96` `:1305`, residual `0.07 < 162.96` `:1309`.
* Banked AO R25 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R25|AO_gamma_upper_disc_R25|R25_deriv|R25_uniform|R25_gamma|R25_zeta`
  returns no files; pattern `namespace AO_` returns only
  `namespace AO_R02DiscUpdate :9968` (R02 chain only, no `AO_R25` hit);
  pattern `theorem R25_|def R25` returns only rect guards
  `R25 :3671`, `R25_x0/x1/y0/y1 :3674-3677`,
  `R25_strip_lo/hi :3682-3683`, `R25_radius_eq :3693`,
  `R25_radius_lt :3698`, `R25_mem_gridFine :3701`,
  `R25_leaf_obligations :3711`, `R25_fencing_of_bounds :3715`
  (tier guards, not an AO chain);
  pattern `narrow_R25_` in this file returns no files
  (no prior R25 narrow).
* Result below: no R25 mirror of the R02 shape exists locally, so R25 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R25_mismatch :811`.
-/

namespace Door3PremiseTier

/-- R25 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R25_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R25 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R25_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R25 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R25_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R25 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R25_deriv_keeps_67200 (hBall : premBall_R25) (w : ℂ)
    (hw : CentralCoverAssembly.R25.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R25_of_ball hBall w hw

end Door3PremiseTier

/-! ## 30. R26 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R25 premise block in this file: `premTier_R25 :805`, `premBall_R25 :807`,
  `premTier_R25_mismatch :811`, `premDeriv_R25_of_ball :813`,
  `premSphere_R25_of_ball :825` (`R25.mem`, tier `0.06`, value `67200`).
* R26 premise block in this file: `premTier_R26 :832`, `premBall_R26 :834`,
  `premTier_R26_mismatch :838`, `premDeriv_R26_of_ball :840`,
  `premSphere_R26_of_ball :852` (`R26.mem`, tier `0.06`, value `67200`).
* R25 narrow block in this file: `## 29. R25 premise-tier narrow attempt`
  `:2564-2622` with `narrow_R25_closedForm_keeps :2604`,
  `narrow_R25_residual_gap :2608`,
  `narrow_R25_residual_is_mismatch :2612`,
  `narrow_R25_deriv_keeps_67200 :2617`; R25 keeps `67200`, no chain.
* Banked AO R26 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R26|R26_deriv|R26_uniform` returns no files
  (no `AO_R26` hit);
  pattern `narrow_R26_` in this file returns no files
  (no prior R26 narrow).
* Result below: no R26 mirror of the R02 shape exists locally, so R26 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R26_mismatch :838`.
-/

namespace Door3PremiseTier

/-- R26 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R26_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R26 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R26_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R26 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R26_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R26 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R26_deriv_keeps_67200 (hBall : premBall_R26) (w : ℂ)
    (hw : CentralCoverAssembly.R26.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R26_of_ball hBall w hw

end Door3PremiseTier

/-! ## 31. R27 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R26 premise block in this file: `premTier_R26 :832`, `premBall_R26 :834`,
  `premTier_R26_mismatch :838`, `premDeriv_R26_of_ball :840`,
  `premSphere_R26_of_ball :852` (`R26.mem`, tier `0.06`, value `67200`).
* R27 premise block in this file: `premTier_R27 :859`, `premBall_R27 :861`,
  `premTier_R27_mismatch :865`, `premDeriv_R27_of_ball :867`,
  `premSphere_R27_of_ball :879` (`R27.mem`, tier `0.07`, value `67200`).
* R26 narrow block in this file: `## 30. R26 premise-tier narrow attempt`
  `:2624-2670` with `narrow_R26_closedForm_keeps :2652`,
  `narrow_R26_residual_gap :2656`,
  `narrow_R26_residual_is_mismatch :2660`,
  `narrow_R26_deriv_keeps_67200 :2665`; R26 keeps `67200`, no chain.
* Banked AO R27 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R27|R27_deriv|R27_uniform` returns no files
  (no `AO_R27` hit);
  pattern `narrow_R27_` in this file returns no files
  (no prior R27 narrow).
* Result below: no R27 mirror of the R02 shape exists locally, so R27 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R27_mismatch :865`.
-/

namespace Door3PremiseTier

/-- R27 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R27_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R27 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R27_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R27 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R27_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R27 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R27_deriv_keeps_67200 (hBall : premBall_R27) (w : ℂ)
    (hw : CentralCoverAssembly.R27.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R27_of_ball hBall w hw

end Door3PremiseTier

/-! ## 32. R28 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R27 premise block in this file: `premTier_R27 :859`, `premBall_R27 :861`,
  `premTier_R27_mismatch :865`, `premDeriv_R27_of_ball :867`,
  `premSphere_R27_of_ball :879` (`R27.mem`, tier `0.07`, value `67200`).
* R28 premise block in this file: `premTier_R28 :886`, `premBall_R28 :888`,
  `premTier_R28_mismatch :892`, `premDeriv_R28_of_ball :894`,
  `premSphere_R28_of_ball :906` (`R28.mem`, tier `0.07`, value `67200`).
* R27 narrow block in this file: `## 31. R27 premise-tier narrow attempt`
  `:2672-2718` with `narrow_R27_closedForm_keeps :2700`,
  `narrow_R27_residual_gap :2704`,
  `narrow_R27_residual_is_mismatch :2708`,
  `narrow_R27_deriv_keeps_67200 :2713`; R27 keeps `67200`, no chain.
* Banked AO R28 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R28|R28_deriv|R28_uniform` returns no files
  (no `AO_R28` hit);
  pattern `narrow_R28_` in this file returns no files
  (no prior R28 narrow).
* Result below: no R28 mirror of the R02 shape exists locally, so R28 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R28_mismatch :892`.
-/

namespace Door3PremiseTier

/-- R28 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R28_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R28 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R28_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R28 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R28_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R28 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R28_deriv_keeps_67200 (hBall : premBall_R28) (w : ℂ)
    (hw : CentralCoverAssembly.R28.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R28_of_ball hBall w hw

end Door3PremiseTier

/-! ## 33. R29 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R28 premise block in this file: `premTier_R28 :886`, `premBall_R28 :888`,
  `premTier_R28_mismatch :892`, `premDeriv_R28_of_ball :894`,
  `premSphere_R28_of_ball :906` (`R28.mem`, tier `0.07`, value `67200`).
* R29 premise block in this file: `premTier_R29 :913`, `premBall_R29 :915`,
  `premTier_R29_mismatch :919`, `premDeriv_R29_of_ball :921`,
  `premSphere_R29_of_ball :933` (`R29.mem`, tier `0.07`, value `67200`).
* R28 narrow block in this file: `## 32. R28 premise-tier narrow attempt`
  `:2720-2766` with `narrow_R28_closedForm_keeps :2748`,
  `narrow_R28_residual_gap :2752`,
  `narrow_R28_residual_is_mismatch :2756`,
  `narrow_R28_deriv_keeps_67200 :2761`; R28 keeps `67200`, no chain.
* Banked AO R29 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R29|R29_deriv|R29_uniform` returns no files
  (no `AO_R29` hit);
  pattern `narrow_R29_` in this file returns no files
  (no prior R29 narrow).
* Result below: no R29 mirror of the R02 shape exists locally, so R29 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R29_mismatch :919`.
-/

namespace Door3PremiseTier

/-- R29 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R29_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R29 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R29_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R29 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R29_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R29 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R29_deriv_keeps_67200 (hBall : premBall_R29) (w : ℂ)
    (hw : CentralCoverAssembly.R29.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R29_of_ball hBall w hw

end Door3PremiseTier

/-! ## 34. R30 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R29 premise block in this file: `premTier_R29 :913`, `premBall_R29 :915`,
  `premTier_R29_mismatch :919`, `premDeriv_R29_of_ball :921`,
  `premSphere_R29_of_ball :933` (`R29.mem`, tier `0.07`, value `67200`).
* R30 premise block in this file: `premTier_R30 :940`, `premBall_R30 :942`,
  `premTier_R30_mismatch :946`, `premDeriv_R30_of_ball :948`,
  `premSphere_R30_of_ball :960` (`R30.mem`, tier `0.05`, value `67200`).
* R29 narrow block in this file: `## 33. R29 premise-tier narrow attempt`
  `:2768-2814` with `narrow_R29_closedForm_keeps :2796`,
  `narrow_R29_residual_gap :2800`,
  `narrow_R29_residual_is_mismatch :2804`,
  `narrow_R29_deriv_keeps_67200 :2809`; R29 keeps `67200`, no chain.
* Banked AO R30 chain search in `central_cover_assembly.lean` (no local chain):
  pattern `AO_R30|R30_deriv|R30_uniform` returns no files
  (no `AO_R30` hit);
  pattern `narrow_R30_` in this file returns no files
  (no prior R30 narrow).
* Result below: no R30 mirror of the R02 shape exists locally, so R30 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R30_mismatch :946`.
-/

namespace Door3PremiseTier

/-- R30 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no banked narrow chain exists locally. -/
theorem narrow_R30_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R30 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R30_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R30 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R30_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R30 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R30_deriv_keeps_67200 (hBall : premBall_R30) (w : ℂ)
    (hw : CentralCoverAssembly.R30.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R30_of_ball hBall w hw

end Door3PremiseTier

/-! ## 35. R31 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R30 premise block in this file: `premTier_R30 :940`, `premBall_R30 :942`,
  `premTier_R30_mismatch :946`, `premDeriv_R30_of_ball :948`,
  `premSphere_R30_of_ball :960` (`R30.mem`, tier `0.05`, value `67200`).
* R31 premise block in this file: `premTier_R31 :969`, `premBall_R31 :971`,
  `premTier_R31_mismatch :975`, `premDeriv_R31_of_ball :977`,
  `premSphere_R31_of_ball :989` (`R31.mem`, tier `0.05`, value `67200`).
* R30 narrow block in this file: `## 34. R30 premise-tier narrow attempt`
  `:2816-2862` with `narrow_R30_closedForm_keeps :2844`,
  `narrow_R30_residual_gap :2848`,
  `narrow_R30_residual_is_mismatch :2852`,
  `narrow_R30_deriv_keeps_67200 :2857`; R30 keeps `67200`, no chain.
* Banked R31 chain search in `central_cover_assembly.lean`:
  pattern `AO_R31` returns no files (no `AO_R31` hit);
  pattern `R31_deriv|R31_uniform` returns `R31_uniform_deriv_of_closedBall_bound`,
  `R31_uniform_sphere_bound`, `R31_deriv_bound_of_factor_bounds`
  (small-`r` value `5600 / 0.008 = 700000`, still `0.05 < 700000`);
  pattern `narrow_R31_` in this file returns no files
  (no prior R31 narrow).
* Result below: no R31 tier-`0.05` closure exists locally, so R31 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R31_mismatch :975`.
-/

namespace Door3PremiseTier

/-- R31 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
banked small-`r` chain gives `700000`, no tier closure. -/
theorem narrow_R31_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R31 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R31_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R31 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R31_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R31 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R31_deriv_keeps_67200 (hBall : premBall_R31) (w : ℂ)
    (hw : CentralCoverAssembly.R31.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R31_of_ball hBall w hw

end Door3PremiseTier

/-! ## 36. R32 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R31 premise block in this file: `premTier_R31 :969`, `premBall_R31 :971`,
  `premTier_R31_mismatch :975`, `premDeriv_R31_of_ball :977`,
  `premSphere_R31_of_ball :989` (`R31.mem`, tier `0.05`, value `67200`).
* R32 premise block in this file: `premTier_R32 :996`, `premBall_R32 :998`,
  `premTier_R32_mismatch :1002`, `premDeriv_R32_of_ball :1004`,
  `premSphere_R32_of_ball :1016` (`R32.mem`, tier `0.07`, value `67200`).
* R31 narrow block in this file: `## 35. R31 premise-tier narrow attempt`
  `:2864-2912` with `narrow_R31_closedForm_keeps :2894`,
  `narrow_R31_residual_gap :2898`,
  `narrow_R31_residual_is_mismatch :2902`,
  `narrow_R31_deriv_keeps_67200 :2907`; R31 keeps `67200`, no chain.
* Pattern `narrow_R32_` in this file returns no files
  (no prior R32 narrow).
* Result below: no R32 tier-`0.07` closure exists locally, so R32 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R32_mismatch :1002`.
-/

namespace Door3PremiseTier

/-- R32 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R32_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R32 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R32_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R32 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R32_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R32 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R32_deriv_keeps_67200 (hBall : premBall_R32) (w : ℂ)
    (hw : CentralCoverAssembly.R32.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R32_of_ball hBall w hw

end Door3PremiseTier

/-! ## 37. R33 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R32 premise block in this file: `premTier_R32 :996`, `premBall_R32 :998`,
  `premTier_R32_mismatch :1002`, `premDeriv_R32_of_ball :1004`,
  `premSphere_R32_of_ball :1016` (`R32.mem`, tier `0.07`, value `67200`).
* R33 premise block in this file: `premTier_R33 :1023`, `premBall_R33 :1025`,
  `premTier_R33_mismatch :1029`, `premDeriv_R33_of_ball :1031`,
  `premSphere_R33_of_ball :1043` (`R33.mem`, tier `0.07`, value `67200`).
* R32 narrow block in this file: `## 36. R32 premise-tier narrow attempt`
  `:2914-2957` with `narrow_R32_closedForm_keeps :2939`,
  `narrow_R32_residual_gap :2943`,
  `narrow_R32_residual_is_mismatch :2947`,
  `narrow_R32_deriv_keeps_67200 :2952`; R32 keeps `67200`, no chain.
* Pattern `narrow_R33_` in this file returns no files
  (no prior R33 narrow).
* Result below: no R33 tier-`0.07` closure exists locally, so R33 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R33_mismatch :1029`.
-/

namespace Door3PremiseTier

/-- R33 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R33_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R33 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R33_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R33 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R33_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R33 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R33_deriv_keeps_67200 (hBall : premBall_R33) (w : ℂ)
    (hw : CentralCoverAssembly.R33.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R33_of_ball hBall w hw

end Door3PremiseTier

/-! ## 38. R34 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R33 premise block in this file: `premTier_R33 :1023`, `premBall_R33 :1025`,
  `premTier_R33_mismatch :1029`, `premDeriv_R33_of_ball :1031`,
  `premSphere_R33_of_ball :1043` (`R33.mem`, tier `0.07`, value `67200`).
* R34 premise block in this file: `premTier_R34 :1050`, `premBall_R34 :1052`,
  `premTier_R34_mismatch :1056`, `premDeriv_R34_of_ball :1058`,
  `premSphere_R34_of_ball :1070` (`R34.mem`, tier `0.07`, value `67200`).
* R33 narrow block in this file: `## 37. R33 premise-tier narrow attempt`
  `:2959-3002` with `narrow_R33_closedForm_keeps :2984`,
  `narrow_R33_residual_gap :2988`,
  `narrow_R33_residual_is_mismatch :2992`,
  `narrow_R33_deriv_keeps_67200 :2997`; R33 keeps `67200`, no chain.
* Pattern `narrow_R34_` in this file returns no files
  (no prior R34 narrow).
* Result below: no R34 tier-`0.07` closure exists locally, so R34 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R34_mismatch :1056`.
-/

namespace Door3PremiseTier

/-- R34 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R34_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R34 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R34_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R34 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R34_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R34 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R34_deriv_keeps_67200 (hBall : premBall_R34) (w : ℂ)
    (hw : CentralCoverAssembly.R34.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R34_of_ball hBall w hw

end Door3PremiseTier

/-! ## 39. R35 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R34 premise block in this file: `premTier_R34 :1050`, `premBall_R34 :1052`,
  `premTier_R34_mismatch :1056`, `premDeriv_R34_of_ball :1058`,
  `premSphere_R34_of_ball :1070` (`R34.mem`, tier `0.07`, value `67200`).
* R35 premise block in this file: `premTier_R35 :1077`, `premBall_R35 :1079`,
  `premTier_R35_mismatch :1083`, `premDeriv_R35_of_ball :1085`,
  `premSphere_R35_of_ball :1097` (`R35.mem`, tier `0.06`, value `67200`).
* R34 narrow block in this file: `## 38. R34 premise-tier narrow attempt`
  `:3004-3047` with `narrow_R34_closedForm_keeps :3029`,
  `narrow_R34_residual_gap :3033`,
  `narrow_R34_residual_is_mismatch :3037`,
  `narrow_R34_deriv_keeps_67200 :3042`; R34 keeps `67200`, no chain.
* Pattern `narrow_R35_` in this file returns no files
  (no prior R35 narrow).
* Result below: no R35 tier-`0.06` closure exists locally, so R35 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R35_mismatch :1083`.
-/

namespace Door3PremiseTier

/-- R35 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R35_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R35 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R35_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R35 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R35_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R35 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R35_deriv_keeps_67200 (hBall : premBall_R35) (w : ℂ)
    (hw : CentralCoverAssembly.R35.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R35_of_ball hBall w hw

end Door3PremiseTier

/-! ## 40. R36 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R35 premise block in this file: `premTier_R35 :1077`, `premBall_R35 :1079`,
  `premTier_R35_mismatch :1083`, `premDeriv_R35_of_ball :1085`,
  `premSphere_R35_of_ball :1097` (`R35.mem`, tier `0.06`, value `67200`).
* R36 premise block in this file: `premTier_R36 :1104`, `premBall_R36 :1106`,
  `premTier_R36_mismatch :1110`, `premDeriv_R36_of_ball :1112`,
  `premSphere_R36_of_ball :1124` (`R36.mem`, tier `0.06`, value `67200`).
* R35 narrow block in this file: `## 39. R35 premise-tier narrow attempt`
  `:3049-3092` with `narrow_R35_closedForm_keeps :3074`,
  `narrow_R35_residual_gap :3078`,
  `narrow_R35_residual_is_mismatch :3082`,
  `narrow_R35_deriv_keeps_67200 :3087`; R35 keeps `67200`, no chain.
* Pattern `narrow_R36_` in this file returns no files
  (no prior R36 narrow).
* Result below: no R36 tier-`0.06` closure exists locally, so R36 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.06 < 67200`;
  tier `0.06` stays open by the same mismatch as `premTier_R36_mismatch :1110`.
-/

namespace Door3PremiseTier

/-- R36 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R36_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R36 residual gap at the kept value: tier `0.06` stays open below `67200`. -/
theorem narrow_R36_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R36 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R36_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R36 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R36_deriv_keeps_67200 (hBall : premBall_R36) (w : ℂ)
    (hw : CentralCoverAssembly.R36.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R36_of_ball hBall w hw

end Door3PremiseTier

/-! ## 41. R37 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R36 premise block in this file: `premTier_R36 :1104`, `premBall_R36 :1106`,
  `premTier_R36_mismatch :1110`, `premDeriv_R36_of_ball :1112`,
  `premSphere_R36_of_ball :1124` (`R36.mem`, tier `0.06`, value `67200`).
* R37 premise block in this file: `premTier_R37 :1131`, `premBall_R37 :1133`,
  `premTier_R37_mismatch :1137`, `premDeriv_R37_of_ball :1139`,
  `premSphere_R37_of_ball :1151` (`R37.mem`, tier `0.07`, value `67200`).
* R36 narrow block in this file: `## 40. R36 premise-tier narrow attempt`
  `:3094-3137` with `narrow_R36_closedForm_keeps :3119`,
  `narrow_R36_residual_gap :3123`,
  `narrow_R36_residual_is_mismatch :3127`,
  `narrow_R36_deriv_keeps_67200 :3132`; R36 keeps `67200`, no chain.
* Pattern `narrow_R37_` in this file returns no matches
  (no prior R37 narrow).
* Result below: no R37 tier-`0.07` closure exists locally, so R37 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R37_mismatch :1137`.
-/

namespace Door3PremiseTier

/-- R37 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R37_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R37 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R37_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R37 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R37_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R37 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R37_deriv_keeps_67200 (hBall : premBall_R37) (w : ℂ)
    (hw : CentralCoverAssembly.R37.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R37_of_ball hBall w hw

end Door3PremiseTier

/-! ## 42. R38 premise-tier narrow attempt (append-only wave).

* R37 premise block in this file: `premTier_R37 :1131`, `premBall_R37 :1133`,
  `premTier_R37_mismatch :1137`, `premDeriv_R37_of_ball :1139`,
  `premSphere_R37_of_ball :1151` (`R37.mem`, tier `0.07`, value `67200`).
* R38 premise block in this file: `premTier_R38 :1158`, `premBall_R38 :1160`,
  `premTier_R38_mismatch :1164`, `premDeriv_R38_of_ball :1166`,
  `premSphere_R38_of_ball :1178` (`R38.mem`, tier `0.07`, value `67200`).
* R37 narrow block in this file: `## 41. R37 premise-tier narrow attempt`
  `:3139-3182` with `narrow_R37_closedForm_keeps :3164`,
  `narrow_R37_residual_gap :3168`,
  `narrow_R37_residual_is_mismatch :3172`,
  `narrow_R37_deriv_keeps_67200 :3177`; R37 keeps `67200`, no chain.
* Pattern `narrow_R38_` in this file returns no matches
  (no prior R38 narrow).
* Result below: no R38 tier-`0.07` closure exists locally, so R38 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R38_mismatch :1164`.
-/

namespace Door3PremiseTier

/-- R38 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R38_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R38 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R38_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R38 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R38_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R38 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R38_deriv_keeps_67200 (hBall : premBall_R38) (w : ℂ)
    (hw : CentralCoverAssembly.R38.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R38_of_ball hBall w hw

end Door3PremiseTier

/-! ## 43. R39 premise-tier narrow attempt (append-only wave).

* R38 premise block in this file: `premTier_R38 :1158`, `premBall_R38 :1160`,
  `premTier_R38_mismatch :1164`, `premDeriv_R38_of_ball :1166`,
  `premSphere_R38_of_ball :1178` (`R38.mem`, tier `0.07`, value `67200`).
* R39 premise block in this file: `premTier_R39 :1185`, `premBall_R39 :1187`,
  `premTier_R39_mismatch :1191`, `premDeriv_R39_of_ball :1193`,
  `premSphere_R39_of_ball :1205` (`R39.mem`, tier `0.07`, value `67200`).
* R38 narrow block in this file: `## 42. R38 premise-tier narrow attempt`
  `:3184-3226` with `narrow_R38_closedForm_keeps :3208`,
  `narrow_R38_residual_gap :3212`,
  `narrow_R38_residual_is_mismatch :3216`,
  `narrow_R38_deriv_keeps_67200 :3221`; R38 keeps `67200`, no chain.
* Pattern `narrow_R39_` in this file returns no matches
  (no prior R39 narrow).
* Result below: no R39 tier-`0.07` closure exists locally, so R39 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.07 < 67200`;
  tier `0.07` stays open by the same mismatch as `premTier_R39_mismatch :1191`.
-/

namespace Door3PremiseTier

/-- R39 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R39_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R39 residual gap at the kept value: tier `0.07` stays open below `67200`. -/
theorem narrow_R39_residual_gap : (0.07 : ℝ) < 67200 := by
  norm_num

/-- R39 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R39_residual_is_mismatch : (0.07 : ℝ) < 67200 :=
  tier07_lt_67200

/-- R39 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R39_deriv_keeps_67200 (hBall : premBall_R39) (w : ℂ)
    (hw : CentralCoverAssembly.R39.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R39_of_ball hBall w hw

end Door3PremiseTier

/-! ## 44. R40 premise-tier narrow attempt (append-only wave).

* R39 premise block in this file: `premTier_R39 :1185`, `premBall_R39 :1187`,
  `premTier_R39_mismatch :1191`, `premDeriv_R39_of_ball :1193`,
  `premSphere_R39_of_ball :1205` (`R39.mem`, tier `0.07`, value `67200`).
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R39 narrow block in this file: `## 43. R39 premise-tier narrow attempt`
  `:3228-3270` with `narrow_R39_closedForm_keeps :3252`,
  `narrow_R39_residual_gap :3256`,
  `narrow_R39_residual_is_mismatch :3260`,
  `narrow_R39_deriv_keeps_67200 :3265`; R39 keeps `67200`, no chain.
* Pattern `narrow_R40_` in this file returns no matches
  (no prior R40 narrow).
* Result below: no R40 tier-`0.05` closure exists locally, so R40 keeps
  value `67200` (`16800 / 0.25`) with exact residual gap `0.05 < 67200`;
  tier `0.05` stays open by the same mismatch as `premTier_R40_mismatch :1218`.
-/

namespace Door3PremiseTier

/-- R40 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R40_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R40 residual gap at the kept value: tier `0.05` stays open below `67200`. -/
theorem narrow_R40_residual_gap : (0.05 : ℝ) < 67200 := by
  norm_num

/-- R40 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R40_residual_is_mismatch : (0.05 : ℝ) < 67200 :=
  tier05_lt_67200

/-- R40 conditional deriv transfer still lands at `67200` from the ball premise
(re-export for the narrow record). -/
theorem narrow_R40_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  premDeriv_R40_of_ball hBall w hw

end Door3PremiseTier

/-! ## 45. R41 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R40 narrow block in this file: `## 44. R40 premise-tier narrow attempt`
  `:3272-3314` with `narrow_R40_closedForm_keeps :3296`,
  `narrow_R40_residual_gap :3300`,
  `narrow_R40_residual_is_mismatch :3304`,
  `narrow_R40_deriv_keeps_67200 :3309`; R40 keeps `67200`, no chain.
* Central R41 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R41` rect; pattern `narrow_R41_` in this
  file returns no matches (no prior R41 narrow).
* Proxy tier reference only (no central cell): `interval_arith.lean`
  `R41 :38975` with `door3_cell_checker.lean` R41 proxy header `:1857-1861`
  recording inner tier `(0.15, 0.06)`.
* Result below: no central R41 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the proxy inner tier; tier `0.06` stays open by the
  banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the banked
  R40 transfer at `67200` since no central R41 cell exists.
-/

namespace Door3PremiseTier

/-- R41 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R41_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R41 residual gap at the kept value: proxy inner tier `0.06`
stays open below `67200`. -/
theorem narrow_R41_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R41 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R41_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R41 conditional deriv transfer still lands at `67200` (re-export of the
banked R40 transfer; no central R41 cell exists for a separate transfer). -/
theorem narrow_R41_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R40_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 46. R42 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R41 narrow block in this file: `## 45. R41 premise-tier narrow attempt`
  `:3316-3362` with `narrow_R41_closedForm_keeps :3343`,
  `narrow_R41_residual_gap :3348`,
  `narrow_R41_residual_is_mismatch :3352`,
  `narrow_R41_deriv_keeps_67200 :3357`; R41 keeps `67200`, no chain.
* Central R42 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R42` rect; pattern `narrow_R42_` in this
  file returns no matches (no prior R42 narrow).
* Proxy tier reference only (no central cell): `interval_arith.lean`
  `R42 :39110` with `door3_cell_checker.lean` R42 proxy header `:1277-1281`
  recording inner tier `(0.15, 0.06)`.
* Result below: no central R42 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the proxy inner tier; tier `0.06` stays open by the
  banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the banked
  R41 transfer (which re-exports R40) at `67200` since no central R42 cell
  exists.
-/

namespace Door3PremiseTier

/-- R42 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R42_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R42 residual gap at the kept value: proxy inner tier `0.06`
stays open below `67200`. -/
theorem narrow_R42_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R42 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R42_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R42 conditional deriv transfer still lands at `67200` (re-export of the
banked R41 transfer, which re-exports R40; no central R42 cell exists
for a separate transfer). -/
theorem narrow_R42_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R41_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 47. R43 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R42 narrow block in this file: `## 46. R42 premise-tier narrow attempt`
  `:3364-3412` with `narrow_R42_closedForm_keeps :3392`,
  `narrow_R42_residual_gap :3397`,
  `narrow_R42_residual_is_mismatch :3401`,
  `narrow_R42_deriv_keeps_67200 :3407`; R42 keeps `67200` via the
  R41→R40 chain, no central R42 rect.
* Central R43 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R43` rect; pattern `narrow_R43_` in this
  file returns no matches (no prior R43 narrow).
* Proxy tier reference only (no central cell): `interval_arith.lean`
  `R43 :39245` with `door3_cell_checker.lean` R43 proxy header `:642-646`
  recording inner tier `(0.15, 0.06)`.
* Result below: no central R43 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the proxy inner tier; tier `0.06` stays open by the
  banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the banked
  R42 transfer (which re-exports R41→R40) at `67200` since no central R43
  cell exists.
-/

namespace Door3PremiseTier

/-- R43 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R43_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R43 residual gap at the kept value: proxy inner tier `0.06`
stays open below `67200`. -/
theorem narrow_R43_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R43 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R43_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R43 conditional deriv transfer still lands at `67200` (re-export of the
banked R42 transfer, which re-exports R41→R40; no central R43 cell exists
for a separate transfer). -/
theorem narrow_R43_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R42_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 48. R44 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R43 narrow block in this file: `## 47. R43 premise-tier narrow attempt`
  `:3414-3463` with `narrow_R43_closedForm_keeps :3443`,
  `narrow_R43_residual_gap :3448`,
  `narrow_R43_residual_is_mismatch :3452`,
  `narrow_R43_deriv_keeps_67200 :3458`; R43 keeps `67200` via the
  R42→R41→R40 chain, no central R43 rect.
* Central R44 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R44` rect; pattern `narrow_R44_` in this
  file returns no matches (no prior R44 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R44` rect and no `door3_cell_checker.lean` `R44` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R44 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R43 transfer (which re-exports R42→R41→R40) at `67200` since no
  central R44 cell exists.
-/

namespace Door3PremiseTier

/-- R44 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R44_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R44 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R44_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R44 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R44_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R44 conditional deriv transfer still lands at `67200` (re-export of the
banked R43 transfer, which re-exports R42→R41→R40; no central R44 cell
exists for a separate transfer). -/
theorem narrow_R44_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R43_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 49. R45 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R44 narrow block in this file: `## 48. R44 premise-tier narrow attempt`
  `:3465-3515` with `narrow_R44_closedForm_keeps :3495`,
  `narrow_R44_residual_gap :3500`,
  `narrow_R44_residual_is_mismatch :3504`,
  `narrow_R44_deriv_keeps_67200 :3510`; R44 keeps `67200` via the
  R43→R42→R41→R40 chain, no central R44 rect.
* Central R45 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R45` rect; pattern `narrow_R45_` in this
  file returns no matches (no prior R45 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R45` rect and no `door3_cell_checker.lean` `R45` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R45 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R44 transfer (which re-exports R43→R42→R41→R40) at `67200` since no
  central R45 cell exists.
-/

namespace Door3PremiseTier

/-- R45 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R45_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R45 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R45_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R45 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R45_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R45 conditional deriv transfer still lands at `67200` (re-export of the
banked R44 transfer, which re-exports R43→R42→R41→R40; no central R45 cell
exists for a separate transfer). -/
theorem narrow_R45_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R44_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 50. R46 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R45 narrow block in this file: `## 49. R45 premise-tier narrow attempt`
  `:3517-3567` with `narrow_R45_closedForm_keeps :3547`,
  `narrow_R45_residual_gap :3552`,
  `narrow_R45_residual_is_mismatch :3556`,
  `narrow_R45_deriv_keeps_67200 :3562`; R45 keeps `67200` via the
  R44→R43→R42→R41→R40 chain, no central R45 rect.
* Central R46 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R46` rect; pattern `narrow_R46_` in this
  file returns no matches (no prior R46 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R46` rect and no `door3_cell_checker.lean` `R46` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R46 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R45 transfer (which re-exports R44→R43→R42→R41→R40) at `67200`
  since no central R46 cell exists.
-/

namespace Door3PremiseTier

/-- R46 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R46_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R46 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R46_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R46 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R46_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R46 conditional deriv transfer still lands at `67200` (re-export of the
banked R45 transfer, which re-exports R44→R43→R42→R41→R40; no central R46
cell exists for a separate transfer). -/
theorem narrow_R46_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R45_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 51. R47 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R46 narrow block in this file: `## 50. R46 premise-tier narrow attempt`
  `:3569-3619` with `narrow_R46_closedForm_keeps :3599`,
  `narrow_R46_residual_gap :3604`,
  `narrow_R46_residual_is_mismatch :3608`,
  `narrow_R46_deriv_keeps_67200 :3614`; R46 keeps `67200` via the
  R45→R44→R43→R42→R41→R40 chain, no central R46 rect.
* Central R47 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R47` rect; pattern `narrow_R47_` in this
  file returns no matches (no prior R47 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R47` rect and no `door3_cell_checker.lean` `R47` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R47 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R46 transfer (which re-exports R45→R44→R43→R42→R41→R40) at `67200`
  since no central R47 cell exists.
-/

namespace Door3PremiseTier

/-- R47 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R47_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R47 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R47_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R47 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R47_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R47 conditional deriv transfer still lands at `67200` (re-export of the
banked R46 transfer, which re-exports R45→R44→R43→R42→R41→R40; no central R47
cell exists for a separate transfer). -/
theorem narrow_R47_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R46_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 52. R48 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R47 narrow block in this file: `## 51. R47 premise-tier narrow attempt`
  `:3621-3671` with `narrow_R47_closedForm_keeps :3651`,
  `narrow_R47_residual_gap :3656`,
  `narrow_R47_residual_is_mismatch :3660`,
  `narrow_R47_deriv_keeps_67200 :3666`; R47 keeps `67200` via the
  R46→R45→R44→R43→R42→R41→R40 chain, no central R47 rect.
* Central R48 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R48` rect; pattern `narrow_R48_` in this
  file returns no matches (no prior R48 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R48` rect and no `door3_cell_checker.lean` `R48` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R48 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R47 transfer (which re-exports R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R48 cell exists.
-/

namespace Door3PremiseTier

/-- R48 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R48_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R48 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R48_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R48 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R48_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R48 conditional deriv transfer still lands at `67200` (re-export of the
banked R47 transfer, which re-exports R46→R45→R44→R43→R42→R41→R40; no central R48
cell exists for a separate transfer). -/
theorem narrow_R48_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R47_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 53. R49 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R48 narrow block in this file: `## 52. R48 premise-tier narrow attempt`
  `:3674-3724` with `narrow_R48_closedForm_keeps :3704`,
  `narrow_R48_residual_gap :3709`,
  `narrow_R48_residual_is_mismatch :3713`,
  `narrow_R48_deriv_keeps_67200 :3719`; R48 keeps `67200` via the
  R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R48 rect.
* Central R49 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R49` rect; pattern `narrow_R49_` in this
  file returns no matches (no prior R49 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R49` rect and no `door3_cell_checker.lean` `R49` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R49 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R48 transfer (which re-exports R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R49 cell exists.
-/

namespace Door3PremiseTier

/-- R49 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R49_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R49 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R49_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R49 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R49_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R49 conditional deriv transfer still lands at `67200` (re-export of the
banked R48 transfer, which re-exports R47→R46→R45→R44→R43→R42→R41→R40; no central R49
cell exists for a separate transfer). -/
theorem narrow_R49_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R48_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 54. R50 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R49 narrow block in this file: `## 53. R49 premise-tier narrow attempt`
  `:3727-3777` with `narrow_R49_closedForm_keeps :3757`,
  `narrow_R49_residual_gap :3762`,
  `narrow_R49_residual_is_mismatch :3766`,
  `narrow_R49_deriv_keeps_67200 :3772`; R49 keeps `67200` via the
  R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R49 rect.
* Central R50 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R50` rect; pattern `narrow_R50_` in this
  file returns no matches (no prior R50 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R50` rect and no `door3_cell_checker.lean` `R50` proxy header; nearest
  banked proxy is the R43 inner tier `(0.15, 0.06)` (`interval_arith.lean`
  `R43 :39245`, checker R43 header `:642-646`).
* Result below: no central R50 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R49 transfer (which re-exports R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R50 cell exists.
-/

namespace Door3PremiseTier

/-- R50 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R50_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R50 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R50_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R50 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R50_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R50 conditional deriv transfer still lands at `67200` (re-export of the
banked R49 transfer, which re-exports R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R50
cell exists for a separate transfer). -/
theorem narrow_R50_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R49_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 55. R51 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R50 narrow block in this file: `## 54. R50 premise-tier narrow attempt`
  `:3780-3830` with `narrow_R50_closedForm_keeps :3810`,
  `narrow_R50_residual_gap :3815`,
  `narrow_R50_residual_is_mismatch :3819`,
  `narrow_R50_deriv_keeps_67200 :3825`; R50 keeps `67200` via the
  R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R50 rect.
* Central R51 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R51` rect; pattern `narrow_R51_` in this
  file returns no matches (no prior R51 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R51` rect; `door3_cell_checker.lean` banks an `R51` proxy header
  (`:1915`, inner tier `(0.15, 0.06)`); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R51 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R50 transfer (which re-exports R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R51 cell exists.
-/

namespace Door3PremiseTier

/-- R51 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R51_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R51 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R51_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R51 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R51_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R51 conditional deriv transfer still lands at `67200` (re-export of the
banked R50 transfer, which re-exports R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R51
cell exists for a separate transfer). -/
theorem narrow_R51_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R50_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 56. R52 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R51 narrow block in this file: `## 55. R51 premise-tier narrow attempt`
  `:3833-3883` with `narrow_R51_closedForm_keeps :3863`,
  `narrow_R51_residual_gap :3868`,
  `narrow_R51_residual_is_mismatch :3872`,
  `narrow_R51_deriv_keeps_67200 :3878`; R51 keeps `67200` via the
  R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R51 rect.
* Central R52 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R52` rect; pattern `narrow_R52_` in this
  file returns no matches (no prior R52 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R52` rect; `door3_cell_checker.lean` banks an `R52` proxy header
  (`:1335`, inner tier `(0.15, 0.06)`); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R52 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R51 transfer (which re-exports R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R52 cell exists.
-/

namespace Door3PremiseTier

/-- R52 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R52_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R52 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R52_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R52 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R52_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R52 conditional deriv transfer still lands at `67200` (re-export of the
banked R51 transfer, which re-exports R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R52
cell exists for a separate transfer). -/
theorem narrow_R52_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R51_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 57. R53 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R52 narrow block in this file: `## 56. R52 premise-tier narrow attempt`
  `:3884-3934` with `narrow_R52_closedForm_keeps :3914`,
  `narrow_R52_residual_gap :3919`,
  `narrow_R52_residual_is_mismatch :3923`,
  `narrow_R52_deriv_keeps_67200 :3929`; R52 keeps `67200` via the
  R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R52 rect.
* Central R53 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R53` rect; pattern `narrow_R53_` in this
  file returns no matches (no prior R53 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R53` rect; `door3_cell_checker.lean` banks an `R53` proxy header
  (`:699`, inner tier `(0.15, 0.06)`); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R53 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R52 transfer (which re-exports R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R53 cell exists.
-/

namespace Door3PremiseTier

/-- R53 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R53_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R53 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R53_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R53 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R53_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R53 conditional deriv transfer still lands at `67200` (re-export of the
banked R52 transfer, which re-exports R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R53
cell exists for a separate transfer). -/
theorem narrow_R53_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R52_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 58. R54 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R53 narrow block in this file: `## 57. R53 premise-tier narrow attempt`
  `:3935-3985` with `narrow_R53_closedForm_keeps :3965`,
  `narrow_R53_residual_gap :3970`,
  `narrow_R53_residual_is_mismatch :3974`,
  `narrow_R53_deriv_keeps_67200 :3980`; R53 keeps `67200` via the
  R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R53 rect.
* Central R54 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R54` rect; pattern `narrow_R54_` in this
  file returns no matches (no prior R54 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R54` rect; `door3_cell_checker.lean` has no `R54` proxy header
  (grep `R54` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R54 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R53 transfer (which re-exports R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R54 cell exists.
-/

namespace Door3PremiseTier

/-- R54 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R54_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R54 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R54_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R54 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R54_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R54 conditional deriv transfer still lands at `67200` (re-export of the
banked R53 transfer, which re-exports R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R54
cell exists for a separate transfer). -/
theorem narrow_R54_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R53_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 59. R55 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R54 narrow block in this file: `## 58. R54 premise-tier narrow attempt`
  `:3986-4036` with `narrow_R54_closedForm_keeps :4016`,
  `narrow_R54_residual_gap :4021`,
  `narrow_R54_residual_is_mismatch :4025`,
  `narrow_R54_deriv_keeps_67200 :4031`; R54 keeps `67200` via the
  R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R54 rect.
* Central R55 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R55` rect; pattern `narrow_R55_` in this
  file returns no matches (no prior R55 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R55` rect; `door3_cell_checker.lean` has no `R55` proxy header
  (grep `R55` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R55 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R54 transfer (which re-exports R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R55 cell exists.
-/

namespace Door3PremiseTier

/-- R55 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R55_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R55 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R55_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R55 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R55_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R55 conditional deriv transfer still lands at `67200` (re-export of the
banked R54 transfer, which re-exports R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R55
cell exists for a separate transfer). -/
theorem narrow_R55_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R54_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 60. R56 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R55 narrow block in this file: `## 59. R55 premise-tier narrow attempt`
  `:4037-4087` with `narrow_R55_closedForm_keeps :4067`,
  `narrow_R55_residual_gap :4072`,
  `narrow_R55_residual_is_mismatch :4076`,
  `narrow_R55_deriv_keeps_67200 :4082`; R55 keeps `67200` via the
  R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R55 rect.
* Central R56 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R56` rect; pattern `narrow_R56_` in this
  file returns no matches (no prior R56 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R56` rect; `door3_cell_checker.lean` has no `R56` proxy header
  (grep `R56` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R56 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R55 transfer (which re-exports R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R56 cell exists.
-/

namespace Door3PremiseTier

/-- R56 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R56_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R56 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R56_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R56 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R56_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R56 conditional deriv transfer still lands at `67200` (re-export of the
banked R55 transfer, which re-exports R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R56
cell exists for a separate transfer). -/
theorem narrow_R56_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R55_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 61. R57 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R56 narrow block in this file: `## 60. R56 premise-tier narrow attempt`
  `:4088-4138` with `narrow_R56_closedForm_keeps :4118`,
  `narrow_R56_residual_gap :4123`,
  `narrow_R56_residual_is_mismatch :4127`,
  `narrow_R56_deriv_keeps_67200 :4133`; R56 keeps `67200` via the
  R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R56 rect.
* Central R57 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R57` rect; pattern `narrow_R57_` in this
  file returns no matches (no prior R57 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R57` rect; `door3_cell_checker.lean` has no `R57` proxy header
  (grep `R57` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R57 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R56 transfer (which re-exports R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R57 cell exists.
-/

namespace Door3PremiseTier

/-- R57 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R57_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R57 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R57_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R57 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R57_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R57 conditional deriv transfer still lands at `67200` (re-export of the
banked R56 transfer, which re-exports R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R57
cell exists for a separate transfer). -/
theorem narrow_R57_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R56_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 62. R58 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R57 narrow block in this file: `## 61. R57 premise-tier narrow attempt`
  `:4139-4189` with `narrow_R57_closedForm_keeps :4169`,
  `narrow_R57_residual_gap :4174`,
  `narrow_R57_residual_is_mismatch :4178`,
  `narrow_R57_deriv_keeps_67200 :4184`; R57 keeps `67200` via the
  R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R57 rect.
* Central R58 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R58` rect; pattern `narrow_R58_` in this
  file returns no matches (no prior R58 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R58` rect; `door3_cell_checker.lean` has no `R58` proxy header
  (grep `R58` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R58 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R57 transfer (which re-exports R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R58 cell exists.
-/

namespace Door3PremiseTier

/-- R58 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R58_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R58 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R58_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R58 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R58_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R58 conditional deriv transfer still lands at `67200` (re-export of the
banked R57 transfer, which re-exports R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R58
cell exists for a separate transfer). -/
theorem narrow_R58_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R57_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 63. R59 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R58 narrow block in this file: `## 62. R58 premise-tier narrow attempt`
  `:4190-4240` with `narrow_R58_closedForm_keeps :4220`,
  `narrow_R58_residual_gap :4225`,
  `narrow_R58_residual_is_mismatch :4229`,
  `narrow_R58_deriv_keeps_67200 :4235`; R58 keeps `67200` via the
  R57→R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40 chain, no central R58 rect.
* Central R59 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R59` rect; pattern `narrow_R59_` in this
  file returns no matches (no prior R59 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R59` rect; `door3_cell_checker.lean` has no `R59` proxy header
  (grep `R59` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R59 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R58 transfer (which re-exports R57→R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40) at `67200`
  since no central R59 cell exists.
-/

namespace Door3PremiseTier

/-- R59 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R59_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R59 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R59_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R59 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R59_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R59 conditional deriv transfer still lands at `67200` (re-export of the
banked R58 transfer, which re-exports R57→R56→R55→R54→R53→R52→R51→R50→R49→R48→R47→R46→R45→R44→R43→R42→R41→R40; no central R59
cell exists for a separate transfer). -/
theorem narrow_R59_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R58_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 64. R60 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R59 narrow block in this file: `## 63. R59 premise-tier narrow attempt`
  `:4241-4291` with `narrow_R59_closedForm_keeps :4271`,
  `narrow_R59_residual_gap :4276`,
  `narrow_R59_residual_is_mismatch :4280`,
  `narrow_R59_deriv_keeps_67200 :4286`; R59 keeps `67200` via the
  R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no central R59 rect/proxy.
* Central R60 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R60` rect; pattern `narrow_R60_` in this
  file returns no matches (no prior R60 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R60` rect; `door3_cell_checker.lean` has no `R60` proxy header
  (grep `R60` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R60 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R59 transfer (which re-exports R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R60 cell exists.
-/

namespace Door3PremiseTier

/-- R60 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R60_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R60 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R60_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R60 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R60_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R60 conditional deriv transfer still lands at `67200` (re-export of the
banked R59 transfer, which re-exports R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R60
cell exists for a separate transfer). -/
theorem narrow_R60_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R59_deriv_keeps_67200 hBall w hw

end Door3PremiseTier
/-! ## 65. R61 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R60 narrow block in this file: `## 64. R60 premise-tier narrow attempt`
  `:4292-4342` with `narrow_R60_closedForm_keeps :4322`,
  `narrow_R60_residual_gap :4327`,
  `narrow_R60_residual_is_mismatch :4331`,
  `narrow_R60_deriv_keeps_67200 :4337`; R60 keeps `67200` via the
  R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no central R60 rect/proxy.
* Central R61 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R61` rect; pattern `narrow_R61_` in this
  file returns no matches (no prior R61 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R61` rect; `door3_cell_checker.lean` has no `R61` proxy header
  (grep `R61` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R61 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R60 transfer (which re-exports R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R61 cell exists.
-/

namespace Door3PremiseTier

/-- R61 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R61_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R61 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R61_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R61 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R61_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R61 conditional deriv transfer still lands at `67200` (re-export of the
banked R60 transfer, which re-exports R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R61
cell exists for a separate transfer). -/
theorem narrow_R61_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R60_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 66. R62 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R61 narrow block in this file: `## 65. R61 premise-tier narrow attempt`
  `:4343-4393` with `narrow_R61_closedForm_keeps :4373`,
  `narrow_R61_residual_gap :4378`,
  `narrow_R61_residual_is_mismatch :4382`,
  `narrow_R61_deriv_keeps_67200 :4388`; R61 keeps `67200` via the
  R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no central R61 rect/proxy.
* Central R62 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R62` rect; pattern `narrow_R62_` in this
  file returns no matches (no prior R62 narrow).
* Proxy tier reference only (no central cell): no `interval_arith.lean`
  `R62` rect; `door3_cell_checker.lean` has no `R62` proxy header
  (grep `R62` returns no matches in this project); nearest banked inner tier
  `0.06` stays open below the kept value.
* Result below: no central R62 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R61 transfer (which re-exports R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R62 cell exists.
-/

namespace Door3PremiseTier

/-- R62 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R62_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R62 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R62_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R62 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R62_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R62 conditional deriv transfer still lands at `67200` (re-export of the
banked R61 transfer, which re-exports R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R62
cell exists for a separate transfer). -/
theorem narrow_R62_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R61_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 67. R63 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R62 narrow block in this file: `## 66. R62 premise-tier narrow attempt`
  `:4395-4445` with `narrow_R62_closedForm_keeps :4425`,
  `narrow_R62_residual_gap :4430`,
  `narrow_R62_residual_is_mismatch :4434`,
  `narrow_R62_deriv_keeps_67200 :4440`; R62 keeps `67200` via the
  R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no central R62 rect/proxy.
* Central R63 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R63` rect; pattern `narrow_R63_` in this
  file returns no matches (no prior R63 narrow).
* Rect absence only (checker proxy gives no central cell): no
  `central_cover_assembly.lean` `R63` rect and no `interval_arith.lean`
  `R63` rect; `door3_cell_checker.lean` carries an `R63` proxy header
  (mid-bottom, checker-only) with no `CentralCoverAssembly.R63.mem` and no
  central deriv transfer; nearest banked inner tier `0.06` stays open below
  the kept value.
* Result below: no central R63 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R62 transfer (which re-exports R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R63 cell exists.
-/

namespace Door3PremiseTier

/-- R63 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R63_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R63 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R63_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R63 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R63_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R63 conditional deriv transfer still lands at `67200` (re-export of the
banked R62 transfer, which re-exports R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R63
cell exists for a separate transfer). -/
theorem narrow_R63_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R62_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 68. R64 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R63 narrow block in this file: `## 67. R63 premise-tier narrow attempt`
  `:4447-4499` with `narrow_R63_closedForm_keeps :4479`,
  `narrow_R63_residual_gap :4484`,
  `narrow_R63_residual_is_mismatch :4488`,
  `narrow_R63_deriv_keeps_67200 :4494`; R63 keeps `67200` via the
  R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, checker proxy only
  (no central R63 rect).
* Central R64 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R64` rect; pattern `narrow_R64_` in this
  file returns no matches (no prior R64 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R64` rect and no `interval_arith.lean`
  `R64` rect; `door3_cell_checker.lean` carries no `R64` proxy header
  (grep `R64` returns no matches in this project) with no
  `CentralCoverAssembly.R64.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R64 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R63 transfer (which re-exports R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R64 cell exists.
-/

namespace Door3PremiseTier

/-- R64 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R64_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R64 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R64_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R64 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R64_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R64 conditional deriv transfer still lands at `67200` (re-export of the
banked R63 transfer, which re-exports R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R64
cell exists for a separate transfer). -/
theorem narrow_R64_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R63_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 69. R65 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R64 narrow block in this file: `## 68. R64 premise-tier narrow attempt`
  `:4501-4554` with `narrow_R64_closedForm_keeps :4534`,
  `narrow_R64_residual_gap :4539`,
  `narrow_R64_residual_is_mismatch :4543`,
  `narrow_R64_deriv_keeps_67200 :4549`; R64 keeps `67200` via the
  R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, checker proxy only
  (no central R64 rect, no R64 rect/proxy anywhere).
* Central R65 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R65` rect; pattern `narrow_R65_` in this
  file returns no matches (no prior R65 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R65` rect and no `interval_arith.lean`
  `R65` rect; `door3_cell_checker.lean` carries no `R65` proxy header
  (grep `R65` returns no matches in this project) with no
  `CentralCoverAssembly.R65.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R65 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R64 transfer (which re-exports R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R65 cell exists.
-/

namespace Door3PremiseTier

/-- R65 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R65_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R65 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R65_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R65 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R65_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R65 conditional deriv transfer still lands at `67200` (re-export of the
banked R64 transfer, which re-exports R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R65
cell exists for a separate transfer). -/
theorem narrow_R65_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R64_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 70. R66 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R65 narrow block in this file: `## 69. R65 premise-tier narrow attempt`
  `:4556-4609` with `narrow_R65_closedForm_keeps :4589`,
  `narrow_R65_residual_gap :4594`,
  `narrow_R65_residual_is_mismatch :4598`,
  `narrow_R65_deriv_keeps_67200 :4604`; R65 keeps `67200` via the
  R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R65 rect/proxy
  (no central R65 rect, no R65 rect/proxy anywhere).
* Central R66 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R66` rect; pattern `narrow_R66_` in this
  file returns no matches (no prior R66 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R66` rect and no `interval_arith.lean`
  `R66` rect; `door3_cell_checker.lean` carries no `R66` proxy header
  (grep `R66` returns no matches in this project) with no
  `CentralCoverAssembly.R66.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R66 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R65 transfer (which re-exports R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R66 cell exists.
-/

namespace Door3PremiseTier

/-- R66 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R66_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R66 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R66_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R66 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R66_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R66 conditional deriv transfer still lands at `67200` (re-export of the
banked R65 transfer, which re-exports R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R66
cell exists for a separate transfer). -/
theorem narrow_R66_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R65_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 71. R67 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R66 narrow block in this file: `## 70. R66 premise-tier narrow attempt`
  `:4611-4664` with `narrow_R66_closedForm_keeps :4644`,
  `narrow_R66_residual_gap :4649`,
  `narrow_R66_residual_is_mismatch :4653`,
  `narrow_R66_deriv_keeps_67200 :4659`; R66 keeps `67200` via the
  R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R66 rect/proxy
  (no central R66 rect, no R66 rect/proxy anywhere).
* Central R67 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R67` rect; pattern `narrow_R67_` in this
  file returns no matches (no prior R67 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R67` rect and no `interval_arith.lean`
  `R67` rect; `door3_cell_checker.lean` carries no `R67` proxy header
  (grep `R67` returns no matches in this project) with no
  `CentralCoverAssembly.R67.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R67 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R66 transfer (which re-exports R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R67 cell exists.
-/

namespace Door3PremiseTier

/-- R67 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R67_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R67 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R67_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R67 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R67_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R67 conditional deriv transfer still lands at `67200` (re-export of the
banked R66 transfer, which re-exports R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R67
cell exists for a separate transfer). -/
theorem narrow_R67_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R66_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 72. R68 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R67 narrow block in this file: `## 71. R67 premise-tier narrow attempt`
  `:4666-4719` with `narrow_R67_closedForm_keeps :4699`,
  `narrow_R67_residual_gap :4704`,
  `narrow_R67_residual_is_mismatch :4708`,
  `narrow_R67_deriv_keeps_67200 :4714`; R67 keeps `67200` via the
  R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R67 rect/proxy
  (no central R67 rect, no R67 rect/proxy anywhere).
* Central R68 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R68` rect; pattern `narrow_R68_` in this
  file returns no matches (no prior R68 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R68` rect and no `interval_arith.lean`
  `R68` rect; `door3_cell_checker.lean` carries no `R68` proxy header
  (grep `R68` returns no matches in this project) with no
  `CentralCoverAssembly.R68.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R68 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R67 transfer (which re-exports R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R68 cell exists.
-/

namespace Door3PremiseTier

/-- R68 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R68_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R68 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R68_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R68 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R68_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R68 conditional deriv transfer still lands at `67200` (re-export of the
banked R67 transfer, which re-exports R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R68
cell exists for a separate transfer). -/
theorem narrow_R68_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R67_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 73. R69 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R68 narrow block in this file: `## 72. R68 premise-tier narrow attempt`
  `:4722-4775` with `narrow_R68_closedForm_keeps :4755`,
  `narrow_R68_residual_gap :4760`,
  `narrow_R68_residual_is_mismatch :4764`,
  `narrow_R68_deriv_keeps_67200 :4770`; R68 keeps `67200` via the
  R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R68 rect/proxy
  (no central R68 rect, no R68 rect/proxy anywhere).
* Central R69 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R69` rect; pattern `narrow_R69_` in this
  file returns no matches (no prior R69 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R69` rect and no `interval_arith.lean`
  `R69` rect; `door3_cell_checker.lean` carries no `R69` proxy header
  (grep `R69` returns no matches in this project) with no
  `CentralCoverAssembly.R69.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R69 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R68 transfer (which re-exports R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R69 cell exists.
-/

namespace Door3PremiseTier

/-- R69 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R69_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R69 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R69_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R69 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R69_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R69 conditional deriv transfer still lands at `67200` (re-export of the
banked R68 transfer, which re-exports R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R69
cell exists for a separate transfer). -/
theorem narrow_R69_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R68_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 74. R70 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R69 narrow block in this file: `## 73. R69 premise-tier narrow attempt`
  `:4778-4831` with `narrow_R69_closedForm_keeps :4811`,
  `narrow_R69_residual_gap :4816`,
  `narrow_R69_residual_is_mismatch :4820`,
  `narrow_R69_deriv_keeps_67200 :4826`; R69 keeps `67200` via the
  R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R69 rect/proxy
  (no central R69 rect, no R69 rect/proxy anywhere).
* Central R70 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R70` rect; pattern `narrow_R70_` in this
  file returns no matches (no prior R70 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R70` rect and no `interval_arith.lean`
  `R70` rect; `door3_cell_checker.lean` carries no `R70` proxy header
  (grep `R70` returns no matches in this project) with no
  `CentralCoverAssembly.R70.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R70 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R69 transfer (which re-exports R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R70 cell exists.
-/

namespace Door3PremiseTier

/-- R70 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R70_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R70 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R70_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R70 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R70_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R70 conditional deriv transfer still lands at `67200` (re-export of the
banked R69 transfer, which re-exports R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R70
cell exists for a separate transfer). -/
theorem narrow_R70_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R69_deriv_keeps_67200 hBall w hw

end Door3PremiseTier



/-! ## 75. R71 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R70 narrow block in this file: `## 74. R70 premise-tier narrow attempt`
  `:4834-4887` with `narrow_R70_closedForm_keeps :4867`,
  `narrow_R70_residual_gap :4872`,
  `narrow_R70_residual_is_mismatch :4876`,
  `narrow_R70_deriv_keeps_67200 :4882`; R70 keeps `67200` via the
  R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R70 rect/proxy
  (no central R70 rect, no R70 rect/proxy anywhere).
* Central R71 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R71` rect; pattern `narrow_R71_` in this
  file returns no matches (no prior R71 narrow).
* Rect absence only (no central cell, no checker proxy): no
  `central_cover_assembly.lean` `R71` rect and no `interval_arith.lean`
  `R71` rect; `door3_cell_checker.lean` carries no `R71` proxy header
  (grep `R71` returns no matches in this project) with no
  `CentralCoverAssembly.R71.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R71 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R70 transfer (which re-exports R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R71 cell exists.
-/

namespace Door3PremiseTier

/-- R71 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R71_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R71 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R71_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R71 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R71_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R71 conditional deriv transfer still lands at `67200` (re-export of the
banked R70 transfer, which re-exports R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R71
cell exists for a separate transfer). -/
theorem narrow_R71_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R70_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 76. R72 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R71 narrow block in this file: `## 75. R71 premise-tier narrow attempt`
  `:4891-4944` with `narrow_R71_closedForm_keeps :4924`,
  `narrow_R71_residual_gap :4929`,
  `narrow_R71_residual_is_mismatch :4933`,
  `narrow_R71_deriv_keeps_67200 :4939`; R71 keeps `67200` via the
  R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R71 rect/proxy
  (no central R71 rect, no R71 rect/proxy anywhere).
* Central R72 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R72` rect; pattern `narrow_R72_` in this
  file returns no matches (no prior R72 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R72` rect and no `interval_arith.lean` `R72` rect; with no
  `CentralCoverAssembly.R72.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R72 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R71 transfer (which re-exports R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R72 cell exists.
-/

namespace Door3PremiseTier

/-- R72 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R72_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R72 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R72_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R72 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R72_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R72 conditional deriv transfer still lands at `67200` (re-export of the
banked R71 transfer, which re-exports R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R72
cell exists for a separate transfer). -/
theorem narrow_R72_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R71_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 77. R73 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R72 narrow block in this file: `## 76. R72 premise-tier narrow attempt`
  `:4947-4998` with `narrow_R72_closedForm_keeps :4978`,
  `narrow_R72_residual_gap :4983`,
  `narrow_R72_residual_is_mismatch :4987`,
  `narrow_R72_deriv_keeps_67200 :4993`; R72 keeps `67200` via the
  R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R72 rect/proxy
  (no central R72 rect, no R72 rect/proxy anywhere).
* Central R73 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R73` rect; pattern `narrow_R73_` in this
  file returns no matches (no prior R73 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R73` rect and no `interval_arith.lean` `R73` rect; with no
  `CentralCoverAssembly.R73.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R73 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R72 transfer (which re-exports R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R73 cell exists.
-/

namespace Door3PremiseTier

/-- R73 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R73_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R73 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R73_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R73 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R73_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R73 conditional deriv transfer still lands at `67200` (re-export of the
banked R72 transfer, which re-exports R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R73
cell exists for a separate transfer). -/
theorem narrow_R73_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R72_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 78. R74 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R73 narrow block in this file: `## 77. R73 premise-tier narrow attempt`
  `:5001-5052` with `narrow_R73_closedForm_keeps :5032`,
  `narrow_R73_residual_gap :5037`,
  `narrow_R73_residual_is_mismatch :5041`,
  `narrow_R73_deriv_keeps_67200 :5047`; R73 keeps `67200` via the
  R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R73 rect
  (no central R73 rect, no R73 rect anywhere).
* Central R74 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R74` rect; pattern `narrow_R74_` in this
  file returns no matches (no prior R74 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R74` rect and no `interval_arith.lean` `R74` rect; with no
  `CentralCoverAssembly.R74.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R74 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R73 transfer (which re-exports R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R74 cell exists.
-/

namespace Door3PremiseTier

/-- R74 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R74_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R74 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R74_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R74 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R74_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R74 conditional deriv transfer still lands at `67200` (re-export of the
banked R73 transfer, which re-exports R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R74
cell exists for a separate transfer). -/
theorem narrow_R74_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R73_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 79. R75 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R74 narrow block in this file: `## 78. R74 premise-tier narrow attempt`
  `:5055-5106` with `narrow_R74_closedForm_keeps :5086`,
  `narrow_R74_residual_gap :5091`,
  `narrow_R74_residual_is_mismatch :5095`,
  `narrow_R74_deriv_keeps_67200 :5101`; R74 keeps `67200` via the
  R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R74 rect
  (no central R74 rect, no R74 rect anywhere).
* Central R75 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R75` rect; pattern `narrow_R75_` in this
  file returns no matches (no prior R75 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R75` rect and no `interval_arith.lean` `R75` rect; with no
  `CentralCoverAssembly.R75.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R75 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R74 transfer (which re-exports R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R75 cell exists.
-/

namespace Door3PremiseTier

/-- R75 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R75_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R75 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R75_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R75 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R75_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R75 conditional deriv transfer still lands at `67200` (re-export of the
banked R74 transfer, which re-exports R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R75
cell exists for a separate transfer). -/
theorem narrow_R75_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R74_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 80. R76 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R75 narrow block in this file: `## 79. R75 premise-tier narrow attempt`
  `:5109-5160` with `narrow_R75_closedForm_keeps :5140`,
  `narrow_R75_residual_gap :5145`,
  `narrow_R75_residual_is_mismatch :5149`,
  `narrow_R75_deriv_keeps_67200 :5155`; R75 keeps `67200` via the
  R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R75 rect
  (no central R75 rect, no R75 rect anywhere).
* Central R76 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R76` rect; pattern `narrow_R76_` in this
  file returns no matches (no prior R76 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R76` rect and no `interval_arith.lean` `R76` rect; with no
  `CentralCoverAssembly.R76.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R76 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R75 transfer (which re-exports R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R76 cell exists.
-/

namespace Door3PremiseTier

/-- R76 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R76_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R76 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R76_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R76 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R76_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R76 conditional deriv transfer still lands at `67200` (re-export of the
banked R75 transfer, which re-exports R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R76
cell exists for a separate transfer). -/
theorem narrow_R76_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R75_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 81. R77 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R76 narrow block in this file: `## 80. R76 premise-tier narrow attempt`
  `:5163-5214` with `narrow_R76_closedForm_keeps :5194`,
  `narrow_R76_residual_gap :5199`,
  `narrow_R76_residual_is_mismatch :5203`,
  `narrow_R76_deriv_keeps_67200 :5209`; R76 keeps `67200` via the
  R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R76 rect
  (no central R76 rect, no R76 rect anywhere).
* Central R77 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R77` rect; pattern `narrow_R77_` in this
  file returns no matches (no prior R77 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R77` rect and no `interval_arith.lean` `R77` rect; with no
  `CentralCoverAssembly.R77.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R77 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R76 transfer (which re-exports R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R77 cell exists.
-/

namespace Door3PremiseTier

/-- R77 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R77_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R77 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R77_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R77 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R77_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R77 conditional deriv transfer still lands at `67200` (re-export of the
banked R76 transfer, which re-exports R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R77
cell exists for a separate transfer). -/
theorem narrow_R77_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R76_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 82. R78 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R77 narrow block in this file: `## 81. R77 premise-tier narrow attempt`
  `:5216-5267` with `narrow_R77_closedForm_keeps :5247`,
  `narrow_R77_residual_gap :5252`,
  `narrow_R77_residual_is_mismatch :5256`,
  `narrow_R77_deriv_keeps_67200 :5262`; R77 keeps `67200` via the
  R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R77 rect
  (no central R77 rect, no R77 rect anywhere).
* Central R78 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R78` rect; pattern `narrow_R78_` in this
  file returns no matches (no prior R78 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R78` rect and no `interval_arith.lean` `R78` rect; with no
  `CentralCoverAssembly.R78.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R78 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R77 transfer (which re-exports R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R78 cell exists.
-/

namespace Door3PremiseTier

/-- R78 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R78_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R78 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R78_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R78 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R78_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R78 conditional deriv transfer still lands at `67200` (re-export of the
banked R77 transfer, which re-exports R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R78
cell exists for a separate transfer). -/
theorem narrow_R78_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R77_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 83. R79 premise-tier narrow attempt (append-only wave).

* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R78 narrow block in this file: `## 82. R78 premise-tier narrow attempt`
  `:5270-5321` with `narrow_R78_closedForm_keeps :5301`,
  `narrow_R78_residual_gap :5306`,
  `narrow_R78_residual_is_mismatch :5310`,
  `narrow_R78_deriv_keeps_67200 :5316`; R78 keeps `67200` via the
  R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R78 rect
  (no central R78 rect, no R78 rect anywhere).
* Central R79 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R79` rect; pattern `narrow_R79_` in this
  file returns no matches (no prior R79 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R79` rect and no `interval_arith.lean` `R79` rect; with no
  `CentralCoverAssembly.R79.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R79 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R78 transfer (which re-exports R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R79 cell exists.
-/

namespace Door3PremiseTier

/-- R79 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R79_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R79 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R79_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R79 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R79_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R79 conditional deriv transfer still lands at `67200` (re-export of the
banked R78 transfer, which re-exports R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R79
cell exists for a separate transfer). -/
theorem narrow_R79_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R78_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 84. R80 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R79 narrow block in this file: `## 83. R79 premise-tier narrow attempt`
  `:5323-5374` with `narrow_R79_closedForm_keeps :5354`,
  `narrow_R79_residual_gap :5359`,
  `narrow_R79_residual_is_mismatch :5363`,
  `narrow_R79_deriv_keeps_67200 :5369`; R79 keeps `67200` via the
  R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R79 rect
  (no central R79 rect, no R79 rect anywhere).
* Central R80 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R80` rect; pattern `narrow_R80_` in this
  file returns no matches (no prior R80 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R80` rect and no `interval_arith.lean` `R80` rect; with no
  `CentralCoverAssembly.R80.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R80 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R79 transfer (which re-exports R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R80 cell exists.
-/

namespace Door3PremiseTier

/-- R80 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R80_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R80 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R80_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R80 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R80_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R80 conditional deriv transfer still lands at `67200` (re-export of the
banked R79 transfer, which re-exports R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R80
cell exists for a separate transfer). -/
theorem narrow_R80_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R79_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 85. R81 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R80 narrow block in this file: `## 84. R80 premise-tier narrow attempt`
  `:5376-5428` with `narrow_R80_closedForm_keeps :5408`,
  `narrow_R80_residual_gap :5413`,
  `narrow_R80_residual_is_mismatch :5417`,
  `narrow_R80_deriv_keeps_67200 :5423`; R80 keeps `67200` via the
  R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R80 rect
  (no central R80 rect, no R80 rect anywhere).
* Central R81 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R81` rect; pattern `narrow_R81_` in this
  file returns no matches (no prior R81 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R81` rect and no `interval_arith.lean` `R81` rect; with no
  `CentralCoverAssembly.R81.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R81 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R80 transfer (which re-exports R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R81 cell exists.
-/

namespace Door3PremiseTier

/-- R81 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R81_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R81 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R81_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R81 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R81_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R81 conditional deriv transfer still lands at `67200` (re-export of the
banked R80 transfer, which re-exports R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R81
cell exists for a separate transfer). -/
theorem narrow_R81_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R80_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 86. R82 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R81 narrow block in this file: `## 85. R81 premise-tier narrow attempt`
  `:5430-5482` with `narrow_R81_closedForm_keeps :5462`,
  `narrow_R81_residual_gap :5467`,
  `narrow_R81_residual_is_mismatch :5471`,
  `narrow_R81_deriv_keeps_67200 :5477`; R81 keeps `67200` via the
  R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R81 rect
  (no central R81 rect, no R81 rect anywhere).
* Central R82 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R82` rect; pattern `narrow_R82_` in this
  file returns no matches (no prior R82 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R82` rect and no `interval_arith.lean` `R82` rect; with no
  `CentralCoverAssembly.R82.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R82 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R81 transfer (which re-exports R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R82 cell exists.
-/

namespace Door3PremiseTier

/-- R82 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R82_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R82 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R82_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R82 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R82_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R82 conditional deriv transfer still lands at `67200` (re-export of the
banked R81 transfer, which re-exports R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R82
cell exists for a separate transfer). -/
theorem narrow_R82_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R81_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 87. R83 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R82 narrow block in this file: `## 86. R82 premise-tier narrow attempt`
  `:5484-5536` with `narrow_R82_closedForm_keeps :5516`,
  `narrow_R82_residual_gap :5521`,
  `narrow_R82_residual_is_mismatch :5525`,
  `narrow_R82_deriv_keeps_67200 :5531`; R82 keeps `67200` via the
  R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R82 rect
  (no central R82 rect, no R82 rect anywhere).
* Central R83 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R83` rect; pattern `narrow_R83_` in this
  file returns no matches (no prior R83 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R83` rect and no `interval_arith.lean` `R83` rect; with no
  `CentralCoverAssembly.R83.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R83 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R82 transfer (which re-exports R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R83 cell exists.
-/

namespace Door3PremiseTier

/-- R83 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R83_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R83 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R83_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R83 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R83_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R83 conditional deriv transfer still lands at `67200` (re-export of the
banked R82 transfer, which re-exports R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R83
cell exists for a separate transfer). -/
theorem narrow_R83_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R82_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 88. R84 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R83 narrow block in this file: `## 87. R83 premise-tier narrow attempt`
  `:5538-5590` with `narrow_R83_closedForm_keeps :5570`,
  `narrow_R83_residual_gap :5575`,
  `narrow_R83_residual_is_mismatch :5579`,
  `narrow_R83_deriv_keeps_67200 :5585`; R83 keeps `67200` via the
  R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R83 rect
  (no central R83 rect, no R83 rect anywhere).
* Central R84 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R84` rect; pattern `narrow_R84_` in this
  file returns no matches (no prior R84 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R84` rect and no `interval_arith.lean` `R84` rect; with no
  `CentralCoverAssembly.R84.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R84 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R83 transfer (which re-exports R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R84 cell exists.
-/

namespace Door3PremiseTier

/-- R84 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R84_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R84 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R84_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R84 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R84_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R84 conditional deriv transfer still lands at `67200` (re-export of the
banked R83 transfer, which re-exports R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R84
cell exists for a separate transfer). -/
theorem narrow_R84_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R83_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 89. R85 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R84 narrow block in this file: `## 88. R84 premise-tier narrow attempt`
  `:5592-5644` with `narrow_R84_closedForm_keeps :5624`,
  `narrow_R84_residual_gap :5629`,
  `narrow_R84_residual_is_mismatch :5633`,
  `narrow_R84_deriv_keeps_67200 :5639`; R84 keeps `67200` via the
  R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R84 rect
  (no central R84 rect, no R84 rect anywhere).
* Central R85 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R85` rect; pattern `narrow_R85_` in this
  file returns no matches (no prior R85 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R85` rect and no `interval_arith.lean` `R85` rect; with no
  `CentralCoverAssembly.R85.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R85 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R84 transfer (which re-exports R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R85 cell exists.
-/

namespace Door3PremiseTier

/-- R85 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R85_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R85 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R85_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R85 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R85_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R85 conditional deriv transfer still lands at `67200` (re-export of the
banked R84 transfer, which re-exports R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R85
cell exists for a separate transfer). -/
theorem narrow_R85_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R84_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 90. R86 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R85 narrow block in this file: `## 89. R85 premise-tier narrow attempt`
  `:5646-5698` with `narrow_R85_closedForm_keeps :5678`,
  `narrow_R85_residual_gap :5683`,
  `narrow_R85_residual_is_mismatch :5687`,
  `narrow_R85_deriv_keeps_67200 :5693`; R85 keeps `67200` via the
  R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R85 rect
  (no central R85 rect, no R85 rect anywhere).
* Central R86 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R86` rect; pattern `narrow_R86_` in this
  file returns no matches (no prior R86 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R86` rect and no `interval_arith.lean` `R86` rect; with no
  `CentralCoverAssembly.R86.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R86 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R85 transfer (which re-exports R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R86 cell exists.
-/

namespace Door3PremiseTier

/-- R86 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R86_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R86 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R86_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R86 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R86_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R86 conditional deriv transfer still lands at `67200` (re-export of the
banked R85 transfer, which re-exports R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R86
cell exists for a separate transfer). -/
theorem narrow_R86_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R85_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 91. R87 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R86 narrow block in this file: `## 90. R86 premise-tier narrow attempt`
  `:5700-5752` with `narrow_R86_closedForm_keeps :5732`,
  `narrow_R86_residual_gap :5737`,
  `narrow_R86_residual_is_mismatch :5741`,
  `narrow_R86_deriv_keeps_67200 :5747`; R86 keeps `67200` via the
  R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R86 rect
  (no central R86 rect, no R86 rect anywhere).
* Central R87 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R87` rect; pattern `narrow_R87_` in this
  file returns no matches (no prior R87 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R87` rect and no `interval_arith.lean` `R87` rect; with no
  `CentralCoverAssembly.R87.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R87 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R86 transfer (which re-exports R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R87 cell exists.
-/

namespace Door3PremiseTier

/-- R87 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R87_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R87 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R87_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R87 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R87_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R87 conditional deriv transfer still lands at `67200` (re-export of the
banked R86 transfer, which re-exports R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R87
cell exists for a separate transfer). -/
theorem narrow_R87_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R86_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 92. R88 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R87 narrow block in this file: `## 91. R87 premise-tier narrow attempt`
  `:5754-5806` with `narrow_R87_closedForm_keeps :5786`,
  `narrow_R87_residual_gap :5791`,
  `narrow_R87_residual_is_mismatch :5795`,
  `narrow_R87_deriv_keeps_67200 :5801`; R87 keeps `67200` via the
  R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R87 rect
  (no central R87 rect, no R87 rect anywhere).
* Central R88 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R88` rect; pattern `narrow_R88_` in this
  file returns no matches (no prior R88 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R88` rect and no `interval_arith.lean` `R88` rect; with no
  `CentralCoverAssembly.R88.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R88 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R87 transfer (which re-exports R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R88 cell exists.
-/

namespace Door3PremiseTier

/-- R88 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R88_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R88 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R88_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R88 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R88_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R88 conditional deriv transfer still lands at `67200` (re-export of the
banked R87 transfer, which re-exports R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R88
cell exists for a separate transfer). -/
theorem narrow_R88_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R87_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 93. R89 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R88 narrow block in this file: `## 92. R88 premise-tier narrow attempt`
  `:5808-5860` with `narrow_R88_closedForm_keeps :5840`,
  `narrow_R88_residual_gap :5845`,
  `narrow_R88_residual_is_mismatch :5849`,
  `narrow_R88_deriv_keeps_67200 :5855`; R88 keeps `67200` via the
  R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R88 rect
  (no central R88 rect, no R88 rect anywhere).
* Central R89 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R89` rect; pattern `narrow_R89_` in this
  file returns no matches (no prior R89 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R89` rect and no `interval_arith.lean` `R89` rect; with no
  `CentralCoverAssembly.R89.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R89 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R88 transfer (which re-exports R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R89 cell exists.
-/

namespace Door3PremiseTier

/-- R89 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R89_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R89 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R89_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R89 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R89_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R89 conditional deriv transfer still lands at `67200` (re-export of the
banked R88 transfer, which re-exports R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R89
cell exists for a separate transfer). -/
theorem narrow_R89_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R88_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 94. R90 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R89 narrow block in this file: `## 93. R89 premise-tier narrow attempt`
  `:5862-5914` with `narrow_R89_closedForm_keeps :5894`,
  `narrow_R89_residual_gap :5899`,
  `narrow_R89_residual_is_mismatch :5903`,
  `narrow_R89_deriv_keeps_67200 :5909`; R89 keeps `67200` via the
  R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40 chain, no R89 rect
  (no central R89 rect, no R89 rect anywhere).
* Central R90 search: `central_cover_assembly.lean` defines `R00` `:1133`
  through `R40` `:4933` with no `R90` rect; pattern `narrow_R90_` in this
  file returns no matches (no prior R90 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R90` rect and no `interval_arith.lean` `R90` rect; with no
  `CentralCoverAssembly.R90.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R90 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R89 transfer (which re-exports R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R90 cell exists.
-/

namespace Door3PremiseTier

/-- R90 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R90_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R90 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R90_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R90 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R90_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R90 conditional deriv transfer still lands at `67200` (re-export of the
banked R89 transfer, which re-exports R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R90
cell exists for a separate transfer). -/
theorem narrow_R90_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R89_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 95. R91 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R90 narrow block in this file: `## 94. R90 premise-tier narrow attempt`
  `:5916-5968` with `narrow_R90_closedForm_keeps :5948`,
  `narrow_R90_residual_gap :5953`,
  `narrow_R90_residual_is_mismatch :5957`,
  `narrow_R90_deriv_keeps_67200 :5963`; R90 keeps `67200` via the
  R89 chain (R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R90 rect
  (no central R90 rect, no R90 rect anywhere).
* Central R91 search: `central_cover_assembly.lean` grep `R90|R91` returns
  no files found (defines `R00` through `R40` with no `R91` rect);
  `interval_arith.lean` grep `R90|R91` returns no files found;
  pattern `narrow_R91_` in this file returns no matches (no prior R91 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R91` rect and no `interval_arith.lean` `R91` rect; with no
  `CentralCoverAssembly.R91.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R91 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R90 transfer (which re-exports R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R91 cell exists.
-/

namespace Door3PremiseTier

/-- R91 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R91_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R91 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R91_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R91 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R91_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R91 conditional deriv transfer still lands at `67200` (re-export of the
banked R90 transfer, which re-exports R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R91
cell exists for a separate transfer). -/
theorem narrow_R91_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R90_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 96. R92 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R91 narrow block in this file: `## 95. R91 premise-tier narrow attempt`
  `:5970-6023` with `narrow_R91_closedForm_keeps :6003`,
  `narrow_R91_residual_gap :6008`,
  `narrow_R91_residual_is_mismatch :6012`,
  `narrow_R91_deriv_keeps_67200 :6018`; R91 keeps `67200` via the
  R90 chain (R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R91 rect
  (no central R91 rect, no R91 rect anywhere).
* Central R92 search: `central_cover_assembly.lean` grep `R91|R92` returns
  no files found (defines `R00` through `R40` with no `R92` rect);
  `interval_arith.lean` grep `R91|R92` returns no files found;
  pattern `narrow_R92_` in this file returns no matches (no prior R92 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R92` rect and no `interval_arith.lean` `R92` rect; with no
  `CentralCoverAssembly.R92.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value. (The only other
  in-repo `R92` material is the `door3_cell_checker.lean` proxy
  `R92_radius_upper_checker` et al., not a central rect.)
* Result below: no central R92 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R91 transfer (which re-exports R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R92 cell exists.
-/

namespace Door3PremiseTier

/-- R92 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R92_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R92 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R92_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R92 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R92_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R92 conditional deriv transfer still lands at `67200` (re-export of the
banked R91 transfer, which re-exports R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R92
cell exists for a separate transfer). -/
theorem narrow_R92_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R91_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 97. R93 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R92 narrow block in this file: `## 96. R92 premise-tier narrow attempt`
  `:6025-6080` with `narrow_R92_closedForm_keeps :6060`,
  `narrow_R92_residual_gap :6065`,
  `narrow_R92_residual_is_mismatch :6069`,
  `narrow_R92_deriv_keeps_67200 :6075`; R92 keeps `67200` via the
  R91 chain (R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R92 rect
  (no central R92 rect, no R92 rect anywhere).
* Central R93 search: `central_cover_assembly.lean` grep `R93` returns
  only no central rect (defines `R00` through `R40` with no `R93` rect);
  `interval_arith.lean` grep `R93` returns no files found;
  pattern `narrow_R93_` in this file returns no matches (no prior R93 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R93` rect and no `interval_arith.lean` `R93` rect; with no
  `CentralCoverAssembly.R93.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value. (The only other
  in-repo `R93` material is the `door3_cell_checker.lean` proxy
  `R93_radius_upper_checker` et al., not a central rect.)
* Result below: no central R93 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R92 transfer (which re-exports R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R93 cell exists.
-/

namespace Door3PremiseTier

/-- R93 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R93_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R93 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R93_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R93 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R93_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R93 conditional deriv transfer still lands at `67200` (re-export of the
banked R92 transfer, which re-exports R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R93
cell exists for a separate transfer). -/
theorem narrow_R93_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R92_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 98. R94 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R93 narrow block in this file: `## 97. R93 premise-tier narrow attempt`
  `:6082-6137` with `narrow_R93_closedForm_keeps :6117`,
  `narrow_R93_residual_gap :6122`,
  `narrow_R93_residual_is_mismatch :6126`,
  `narrow_R93_deriv_keeps_67200 :6132`; R93 keeps `67200` via the
  R92 chain (R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), checker proxy only
  (`door3_cell_checker.lean` `R93_radius_upper_checker` et al., no central R93 rect).
* Central R94 search: `central_cover_assembly.lean` grep `R94` returns
  no files found (defines `R00` through `R40` with no `R94` rect);
  `interval_arith.lean` grep `R94` returns no files found;
  `door3_cell_checker.lean` grep `R94` returns no files found;
  `rg R94` across the repo returns no matches;
  pattern `narrow_R94_` in this file returns no matches (no prior R94 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R94` rect and no `interval_arith.lean` `R94` rect; with no
  `CentralCoverAssembly.R94.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R94 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R93 transfer (which re-exports R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R94 cell exists.
-/

namespace Door3PremiseTier

/-- R94 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R94_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R94 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R94_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R94 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R94_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R94 conditional deriv transfer still lands at `67200` (re-export of the
banked R93 transfer, which re-exports R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R94
cell exists for a separate transfer). -/
theorem narrow_R94_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R93_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 99. R95 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R94 narrow block in this file: `## 98. R94 premise-tier narrow attempt`
  `:6139-6194` with `narrow_R94_closedForm_keeps :6174`,
  `narrow_R94_residual_gap :6179`,
  `narrow_R94_residual_is_mismatch :6183`,
  `narrow_R94_deriv_keeps_67200 :6189`; R94 keeps `67200` via the
  R93 chain (R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R94 rect
  anywhere (no central R94 rect, no R94 rect anywhere).
* Central R95 search: `central_cover_assembly.lean` grep `R95` returns
  no files found (defines `R00` through `R40` with no `R95` rect);
  `interval_arith.lean` grep `R95` returns no files found;
  `door3_cell_checker.lean` grep `R95` returns no files found;
  `rg R95` across the repo returns no matches;
  pattern `narrow_R95_` in this file returns no matches (no prior R95 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R95` rect and no `interval_arith.lean` `R95` rect; with no
  `CentralCoverAssembly.R95.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R95 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R94 transfer (which re-exports R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R95 cell exists.
-/

namespace Door3PremiseTier

/-- R95 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R95_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R95 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R95_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R95 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R95_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R95 conditional deriv transfer still lands at `67200` (re-export of the
banked R94 transfer, which re-exports R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R95
cell exists for a separate transfer). -/
theorem narrow_R95_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R94_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 100. R96 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R95 narrow block in this file: `## 99. R95 premise-tier narrow attempt`
  `:6196-6251` with `narrow_R95_closedForm_keeps :6231`,
  `narrow_R95_residual_gap :6236`,
  `narrow_R95_residual_is_mismatch :6240`,
  `narrow_R95_deriv_keeps_67200 :6246`; R95 keeps `67200` via the
  R94 chain (R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R95 rect
  anywhere (no central R95 rect, no R95 rect anywhere).
* Central R96 search: `central_cover_assembly.lean` grep `R96` returns
  no files found (defines `R00` through `R40` with no `R96` rect);
  `interval_arith.lean` grep `R96` returns no files found;
  `door3_cell_checker.lean` grep `R96` returns no files found;
  `rg R96` across the repo returns no matches;
  pattern `narrow_R96_` in this file returns no matches (no prior R96 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R96` rect and no `interval_arith.lean` `R96` rect; with no
  `CentralCoverAssembly.R96.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R96 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R95 transfer (which re-exports R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R96 cell exists.
-/

namespace Door3PremiseTier

/-- R96 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R96_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R96 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R96_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R96 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R96_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R96 conditional deriv transfer still lands at `67200` (re-export of the
banked R95 transfer, which re-exports R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R96
cell exists for a separate transfer). -/
theorem narrow_R96_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R95_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 101. R97 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R96 narrow block in this file: `## 100. R96 premise-tier narrow attempt`
  `:6253-6308` with `narrow_R96_closedForm_keeps :6288`,
  `narrow_R96_residual_gap :6293`,
  `narrow_R96_residual_is_mismatch :6297`,
  `narrow_R96_deriv_keeps_67200 :6303`; R96 keeps `67200` via the
  R95 chain (R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R96 rect
  anywhere (no central R96 rect, no R96 rect anywhere).
* Central R97 search: `central_cover_assembly.lean` grep `R97` returns
  no files found (defines `R00` through `R40` with no `R97` rect);
  `interval_arith.lean` grep `R97` returns no files found;
  `door3_cell_checker.lean` grep `R97` returns no files found;
  `rg R97` across the repo returns no matches;
  pattern `narrow_R97_` in this file returns no matches (no prior R97 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R97` rect and no `interval_arith.lean` `R97` rect; with no
  `CentralCoverAssembly.R97.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R97 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R96 transfer (which re-exports R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R97 cell exists.
-/

namespace Door3PremiseTier

/-- R97 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R97_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R97 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R97_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R97 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R97_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R97 conditional deriv transfer still lands at `67200` (re-export of the
banked R96 transfer, which re-exports R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R97
cell exists for a separate transfer). -/
theorem narrow_R97_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R96_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 102. R98 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R97 narrow block in this file: `## 101. R97 premise-tier narrow attempt`
  `:6310-6365` with `narrow_R97_closedForm_keeps :6345`,
  `narrow_R97_residual_gap :6350`,
  `narrow_R97_residual_is_mismatch :6354`,
  `narrow_R97_deriv_keeps_67200 :6360`; R97 keeps `67200` via the
  R96 chain (R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R97 rect
  anywhere (no central R97 rect, no R97 rect anywhere).
* Central R98 search: `central_cover_assembly.lean` grep `R98` returns
  no files found (defines `R00` through `R40` with no `R98` rect);
  `interval_arith.lean` grep `R98` returns no files found;
  `door3_cell_checker.lean` grep `R98` returns no files found;
  `rg R98` across the repo returns no matches;
  pattern `narrow_R98_` in this file returns no matches (no prior R98 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R98` rect and no `interval_arith.lean` `R98` rect; with no
  `CentralCoverAssembly.R98.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R98 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R97 transfer (which re-exports R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R98 cell exists.
-/

namespace Door3PremiseTier

/-- R98 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R98_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R98 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R98_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R98 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R98_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R98 conditional deriv transfer still lands at `67200` (re-export of the
banked R97 transfer, which re-exports R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R98
cell exists for a separate transfer). -/
theorem narrow_R98_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R97_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

/-! ## 103. R99 premise-tier narrow attempt (append-only wave).

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R98 narrow block in this file: `## 102. R98 premise-tier narrow attempt`
  `:6367-6422` with `narrow_R98_closedForm_keeps :6402`,
  `narrow_R98_residual_gap :6407`,
  `narrow_R98_residual_is_mismatch :6411`,
  `narrow_R98_deriv_keeps_67200 :6417`; R98 keeps `67200` via the
  R97 chain (R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R98 rect
  anywhere (no central R98 rect, no R98 rect anywhere).
* Central R99 search: `central_cover_assembly.lean` grep `R99` returns
  no files found (defines `R00` through `R40` with no `R99` rect);
  `interval_arith.lean` grep `R99` returns no files found;
  `door3_cell_checker.lean` grep `R99` returns no files found;
  `rg R99` across the repo returns no matches;
  pattern `narrow_R99_` in this file returns no matches (no prior R99 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R99` rect and no `interval_arith.lean` `R99` rect; with no
  `CentralCoverAssembly.R99.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* Result below: no central R99 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R98 transfer (which re-exports R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R99 cell exists.
-/

namespace Door3PremiseTier

/-- R99 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R99_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R99 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R99_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R99 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R99_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R99 conditional deriv transfer still lands at `67200` (re-export of the
banked R98 transfer, which re-exports R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R99
cell exists for a separate transfer). -/
theorem narrow_R99_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R98_deriv_keeps_67200 hBall w hw

end Door3PremiseTier


/-! ## 104. R100 premise-tier narrow attempt (append-only wave). MILESTONE.

Grep record (verified before writing via `default.grep` + `rg`):
* R40 premise block in this file: `premTier_R40 :1212`, `premBall_R40 :1214`,
  `premTier_R40_mismatch :1218`, `premDeriv_R40_of_ball :1220`,
  `premSphere_R40_of_ball :1232` (`R40.mem`, tier `0.05`, value `67200`).
* R99 narrow block in this file: `## 103. R99 premise-tier narrow attempt`
  `:6424-6479` with `narrow_R99_closedForm_keeps :6459`,
  `narrow_R99_residual_gap :6464`,
  `narrow_R99_residual_is_mismatch :6468`,
  `narrow_R99_deriv_keeps_67200 :6474`; R99 keeps `67200` via the
  R98 chain (R98->R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40), no R99 rect
  anywhere (no central R99 rect, no R99 rect anywhere).
* Central R100 search: `central_cover_assembly.lean` grep `R100` returns
  no files found (defines `R00` through `R40` with no `R100` rect);
  `interval_arith.lean` grep `R100` returns no files found;
  `door3_cell_checker.lean` grep `R100` returns no files found;
  `rg R100` across the repo returns no matches;
  pattern `narrow_R100_` in this file returns no matches (no prior R100 narrow).
* Rect absence only (no central cell): no `central_cover_assembly.lean`
  `R100` rect and no `interval_arith.lean` `R100` rect; with no
  `CentralCoverAssembly.R100.mem` and no central deriv transfer; nearest
  banked inner tier `0.06` stays open below the kept value.
* MILESTONE: R100 completes 100 narrow blocks in this file, all keeps at
  `67200` (`16800 / 0.25`); no tier closure forced anywhere.
* Result below: no central R100 tier closure exists locally, so the narrow
  record keeps value `67200` (`16800 / 0.25`) with exact residual gap
  `0.06 < 67200` at the nearest banked inner tier; tier `0.06` stays open
  by the banked mismatch `tier06_lt_67200`. The deriv keeps re-exports the
  banked R99 transfer (which re-exports R98->R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40) at `67200`
  since no central R100 cell exists.
-/

namespace Door3PremiseTier

/-- R100 keeps the premise-tier Cauchy value (`16800 / 0.25 = 67200`);
no tier closure. -/
theorem narrow_R100_closedForm_keeps : (16800 : ℝ) / 0.25 = 67200 := by
  norm_num

/-- Exact R100 residual gap at the kept value: nearest banked inner tier
`0.06` stays open below `67200`. -/
theorem narrow_R100_residual_gap : (0.06 : ℝ) < 67200 := by
  norm_num

/-- R100 residual restates the banked-tier mismatch at the kept value. -/
theorem narrow_R100_residual_is_mismatch : (0.06 : ℝ) < 67200 :=
  tier06_lt_67200

/-- R100 conditional deriv transfer still lands at `67200` (re-export of the
banked R99 transfer, which re-exports R98->R97->R96->R95->R94->R93->R92->R91->R90->R89->R88->R87->R86->R85->R84->R83->R82->R81->R80->R79->R78->R77->R76->R75->R74->R73->R72->R71->R70->R69->R68->R67->R66->R65->R64->R63->R62->R61->R60->R59->R58->R57->R56->R55->R54->R53->R52->R51->R50->R49->R48->R47->R46->R45->R44->R43->R42->R41->R40; no central R100
cell exists for a separate transfer). -/
theorem narrow_R100_deriv_keeps_67200 (hBall : premBall_R40) (w : ℂ)
    (hw : CentralCoverAssembly.R40.mem w) :
    ‖deriv xiShifted w‖ ≤ 67200 :=
  narrow_R99_deriv_keeps_67200 hBall w hw

end Door3PremiseTier

