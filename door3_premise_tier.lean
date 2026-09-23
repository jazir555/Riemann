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
