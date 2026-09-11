import Mathlib
import central_cover_assembly
import door3_tierB_subdiv

/-! # Door-3 main-band subdivision + re-tier PLAN (proved arithmetic design).

Status: DESIGN ONLY — no cell closed, no supplier discharged, no cover built.
Every analytic input (shared sup, Cauchy rate, per-subcell center floors,
local Lipschitz constant) stays an explicit Prop premise for the wave lanes.
All proofs below are norm_num / linarith / exact scale over ℝ / ℕ.

## Import check (read-only, verified before writing)
`door3_tierB_subdiv.lean` imports exactly `Mathlib` + `central_cover_assembly`
(lines 1-2); it is an upstream leaf, so importing it here creates no cycle.
This file reuses `tierB_subdiv_count`, `tierB_cauchy_of_sharedSup`,
`tierB_cell_feasible` and does not re-prove them.

## Recon: current geometry (40 cells of gridFine + off-grid R01 extra)
Ball radius r < 1.26 every cell. Half-sides (a, b):
* bottom row y = (0.01, 0.2), dy = 0.095, r = √(1.25²+0.095²) < 1.26
* second row y = (0.1, 0.3), dy = 0.1, r = √(1.25²+0.1²) < 1.26
* third row y = (0.2, 0.4), dy = 0.1, r = √(1.25²+0.1²) < 1.26
* top row y = (0.3, 0.49), dy = 0.095, r = √(1.25²+0.095²) < 1.26

Current tiers (ε, M) per batch files (leaf defs authoritative):
* outer (0.002, 0.05): R00, R10, R11, R20, R21, R30, R31, R40 (8 cells)
* leaf-mismatch (0.002, 0.07): R02 (column sibling; wave 0 must confirm the
  door3_first_cell lane tier), R09, R12, R19, R22, R29, R32, R39 (8 cells)
* mid (0.05, 0.07): R01 (off-grid extra, not in the 40), R03, R04, R07, R08,
  R13, R14, R17, R18, R23, R24, R27, R28, R33, R34, R37, R38 (16 in-grid)
* inner (0.15, 0.06): R05, R06, R15, R16, R25, R26, R35, R36 (8 cells)
Census: 8 + 8 + 16 + 8 = 40 (`plan_census_40`).

Batch premise floors (four-factor products, threshold side):
* outer: BA00/R10 34*0.7*0.0015*1.9 = 0.06783
* leaf: R22 0.096, R29 0.0918, R09 25*0.7*0.0045*1.3 = 0.102375
* mid: BA03 10*0.7*0.015*1.4 = 0.147, R01 18*0.7*0.01*1.2 = 0.1512,
  R07 5.0*0.7*0.1*1.0 = 0.35, R08 12*0.7*0.02*1.0 = 0.168,
  R28 0.143, R33 0.144, R38 0.144
* inner: R05 0.35*0.7*1.5*1.0 = 0.3675, R06 0.8*0.7*1.0*1.0 = 0.56,
  R35 threshold 0.25
Numeric-target centerLower minima (`door3_numeric_targets.lean`):
outer 0.073817, leaf 0.139045, mid 0.259061, inner 0.479595.

## Design inputs: TRUE values (coordinator-measured, taken as given targets)
* R22 deriv 0.0655 (tier 0.07); R28 deriv 0.0678 (tier 0.07)
* R05 deriv 0.0424 (tier 0.06); R00/R21/R31 deriv ~0.049 (tier 0.05)
* |xi| centers 0.07-0.49.

## New tiers (ε', M') with M' ≈ 2× TRUE-deriv, ≥1.5× TRUE headroom
* outer: (0.002, 0.11) — 0.049*3/2 = 0.0735 ≤ 0.11
* leaf: (0.002, 0.15) — 0.0655*3/2 = 0.09825 ≤ 0.15
* mid: (0.05, 0.15) — 0.0678*3/2 = 0.1017 ≤ 0.15
* inner: (0.15, 0.09) — 0.0424*3/2 = 0.0636 ≤ 0.09
Design floors F (below every cited floor in the group):
outer 0.0678, leaf 0.091, mid 0.14, inner 0.25.
Certifiability ratio M' ≤ 3×TRUE (local factor uppers must stay tight;
waves owe the analysis): 0.11 ≤ 0.147, 0.15 ≤ 0.1965, 0.15 ≤ 0.2034,
0.09 ≤ 0.1272.

## Subdivision radii ρ' (rounded DOWN from (F − ε' − margin) / M')
* outer ρ' = 0.5: need 0.057 ≤ 0.0578, margin 0.01, 14 subcells/cell
* leaf ρ' = 0.5: need 0.077 ≤ 0.081, margin 0.014, 14 subcells/cell
* mid ρ' = 0.5: need 0.125 ≤ 0.13, margin 0.015, 14 subcells/cell
* inner ρ' = 0.9: need 0.231 ≤ 0.24, margin 0.019, 8 subcells/cell
TOTAL = 8*14 + 8*14 + 16*14 + 8*8 = 512 (`plan_total_512`).
512 is 2.4% over the nominal ~500 target and far below the 2000
subdivision-depth ceiling; ρ' is the coarsest clean rational keeping
margins ≥ 0.01 everywhere, so no depth tradeoff is triggered.

## Per-subcell premise template (what each wave must prove per subcell)
For a subcell with center c, fencing radius ρ', design triple (ε', M')
and design floor F, the wave owes:
(a) measured center lower m with F + M'*ρ' ≤ m (fencing need;
    `plan_subcell_fencing` + `plan_subcell_center_schema` give the shape);
(b) certified local deriv upper M' on the subcell ball (via the shared-sup
    Cauchy template `plan_cauchy_template`, rate constant explicit);
(c) TRUE-headroom target m ≥ 1.3*F where TRUE allows. Cleared on batch
    floors for R05/R06/R07-class (`plan_ok_R05/R06/R07`); FLAGGED for direct
    per-subcell measurement wherever TRUE dips near subcell edges:
    outer band (`plan_flag_outer`), leaf-tight R09/R29-class
    (`plan_flag_leaf`), mid-tight R08/R28-class (`plan_flag_mid`).
Continuity shortcut allowed only with a certified local Lipschitz constant
L ≤ M' on the subcell ball: values on the ball stay ≥ m − M'*ρ' ≥ F.

## Remainder (not this file)
Wave 0: confirm R02 tier; build the 512-subcell cover (14/cell outer/leaf/
mid at ρ' = 0.5, 8/cell inner at ρ' = 0.9); discharge per-subcell (a)-(c);
land the joint ball sup feeding `tierB_cauchy_of_sharedSup`; register the
cover centrally. No existing file touched.
-/

namespace Door3SubdivPlan

/-! ## 1. TRUE headroom: M' ≥ 1.5 × TRUE-deriv, and M' ≤ 3 × TRUE. -/

theorem plan_headroom_outer : (0.049 * 3 / 2 : ℝ) ≤ 0.11 := by norm_num

theorem plan_headroom_leaf : (0.0655 * 3 / 2 : ℝ) ≤ 0.15 := by norm_num

theorem plan_headroom_mid : (0.0678 * 3 / 2 : ℝ) ≤ 0.15 := by norm_num

theorem plan_headroom_inner : (0.0424 * 3 / 2 : ℝ) ≤ 0.09 := by norm_num

theorem plan_ratio_outer : (0.11 : ℝ) ≤ 3 * 0.049 := by norm_num

theorem plan_ratio_leaf : (0.15 : ℝ) ≤ 3 * 0.0655 := by norm_num

theorem plan_ratio_mid : (0.15 : ℝ) ≤ 3 * 0.0678 := by norm_num

theorem plan_ratio_inner : (0.09 : ℝ) ≤ 3 * 0.0424 := by norm_num

/-! ## 2. Per-group design records (headroom + ratio + feasibility + floor). -/

theorem plan_design_outer :
    (0.049 * 3 / 2 : ℝ) ≤ 0.11 ∧ (0.11 : ℝ) ≤ 3 * 0.049 ∧
    ((0.002 : ℝ) + 0.11 * 0.5 ≤ 0.0678 - 0.01) ∧
    ((0.0678 : ℝ) ≤ 0.06783) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem plan_design_leaf :
    (0.0655 * 3 / 2 : ℝ) ≤ 0.15 ∧ (0.15 : ℝ) ≤ 3 * 0.0655 ∧
    ((0.002 : ℝ) + 0.15 * 0.5 ≤ 0.091 - 0.01) ∧
    ((0.091 : ℝ) ≤ 0.0918) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem plan_design_mid :
    (0.0678 * 3 / 2 : ℝ) ≤ 0.15 ∧ (0.15 : ℝ) ≤ 3 * 0.0678 ∧
    ((0.05 : ℝ) + 0.15 * 0.5 ≤ 0.14 - 0.01) ∧
    ((0.14 : ℝ) ≤ 0.143) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem plan_design_inner :
    (0.0424 * 3 / 2 : ℝ) ≤ 0.09 ∧ (0.09 : ℝ) ≤ 3 * 0.0424 ∧
    ((0.15 : ℝ) + 0.09 * 0.9 ≤ 0.25 - 0.01) ∧
    ((0.25 : ℝ) ≤ 0.25) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 3. Batch floor identities + design-floor chains. -/

theorem plan_floor_outer_BA00 :
    (34 * 0.7 * 0.0015 * 1.9 : ℝ) = 0.06783 := by norm_num

theorem plan_floor_mid_BA03 :
    (10 * 0.7 * 0.015 * 1.4 : ℝ) = 0.147 := by norm_num

theorem plan_floor_mid_R01 :
    (18 * 0.7 * 0.01 * 1.2 : ℝ) = 0.1512 := by norm_num

theorem plan_floor_inner_R05 :
    (0.35 * 0.7 * 1.5 * 1.0 : ℝ) = 0.3675 := by norm_num

theorem plan_floor_inner_R06 :
    (0.8 * 0.7 * 1.0 * 1.0 : ℝ) = 0.56 := by norm_num

theorem plan_floor_mid_R07 :
    (5.0 * 0.7 * 0.1 * 1.0 : ℝ) = 0.35 := by norm_num

theorem plan_floor_mid_R08 :
    (12 * 0.7 * 0.02 * 1.0 : ℝ) = 0.168 := by norm_num

theorem plan_floor_leaf_R09 :
    (25 * 0.7 * 0.0045 * 1.3 : ℝ) = 0.102375 := by norm_num

theorem plan_floorchain_outer :
    (0.0678 : ℝ) ≤ 0.06783 ∧ (0.0678 : ℝ) ≤ 0.073817 := by
  refine ⟨by norm_num, by norm_num⟩

theorem plan_floorchain_leaf :
    (0.091 : ℝ) ≤ 0.0918 ∧ (0.091 : ℝ) ≤ 0.096 ∧
    (0.091 : ℝ) ≤ 0.102375 ∧ (0.091 : ℝ) ≤ 0.139045 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem plan_floorchain_mid :
    (0.14 : ℝ) ≤ 0.143 ∧ (0.14 : ℝ) ≤ 0.144 ∧
    (0.14 : ℝ) ≤ 0.147 ∧ (0.14 : ℝ) ≤ 0.1512 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem plan_floorchain_inner :
    (0.25 : ℝ) ≤ 0.25 ∧ (0.25 : ℝ) ≤ 0.3675 ∧
    (0.25 : ℝ) ≤ 0.479595 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## 4. Standalone feasibility per group: ε' + M'·ρ' ≤ F − margin. -/

theorem plan_feas_outer :
    (0.002 : ℝ) + 0.11 * 0.5 ≤ 0.0678 - 0.01 := by norm_num

theorem plan_feas_leaf :
    (0.002 : ℝ) + 0.15 * 0.5 ≤ 0.091 - 0.01 := by norm_num

theorem plan_feas_mid :
    (0.05 : ℝ) + 0.15 * 0.5 ≤ 0.14 - 0.01 := by norm_num

theorem plan_feas_inner :
    (0.15 : ℝ) + 0.09 * 0.9 ≤ 0.25 - 0.01 := by norm_num

/-! ## 5. Subcell counts via `tierB_subdiv_count`.

Geometry A: bottom/top rows (b = 0.095). Geometry B: second/third rows
(b = 0.1). Outer/leaf/mid use ρ' = 0.5 with a 7 × 2 grid (14 subcells);
inner uses ρ' = 0.9 with a 4 × 2 grid (8 subcells). -/

theorem plan_count_AL (N : ℕ) (hN : N ≤ 7 * 2) :
    (N : ℝ) ≤ (2 * 1.25 / 0.5 + 2) * (2 * 0.095 / 0.5 + 2) :=
  Door3TierBSubdiv.tierB_subdiv_count 1.25 0.095 0.5 7 2 N
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hN

theorem plan_count_BL (N : ℕ) (hN : N ≤ 7 * 2) :
    (N : ℝ) ≤ (2 * 1.25 / 0.5 + 2) * (2 * 0.1 / 0.5 + 2) :=
  Door3TierBSubdiv.tierB_subdiv_count 1.25 0.1 0.5 7 2 N
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hN

theorem plan_count_AI (N : ℕ) (hN : N ≤ 4 * 2) :
    (N : ℝ) ≤ (2 * 1.25 / 0.9 + 2) * (2 * 0.095 / 0.9 + 2) :=
  Door3TierBSubdiv.tierB_subdiv_count 1.25 0.095 0.9 4 2 N
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hN

theorem plan_count_BI (N : ℕ) (hN : N ≤ 4 * 2) :
    (N : ℝ) ≤ (2 * 1.25 / 0.9 + 2) * (2 * 0.1 / 0.9 + 2) :=
  Door3TierBSubdiv.tierB_subdiv_count 1.25 0.1 0.9 4 2 N
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hN

theorem plan_cap_AL :
    ((2 * 1.25 / 0.5 + 2) * (2 * 0.095 / 0.5 + 2) : ℝ) = 16.66 := by
  norm_num

theorem plan_cap_BL :
    ((2 * 1.25 / 0.5 + 2) * (2 * 0.1 / 0.5 + 2) : ℝ) = 16.8 := by
  norm_num

theorem plan_cap_AI :
    ((2 * 1.25 / 0.9 + 2) * (2 * 0.095 / 0.9 + 2) : ℝ) ≤ 10.57 := by
  norm_num

theorem plan_cap_BI :
    ((2 * 1.25 / 0.9 + 2) * (2 * 0.1 / 0.9 + 2) : ℝ) ≤ 10.62 := by
  norm_num

theorem plan_cell14 (N : ℕ) (hN : N ≤ 7 * 2) : (N : ℝ) ≤ 14 := by
  have hN' : (N : ℝ) ≤ ((7 * 2 : ℕ) : ℝ) := by exact_mod_cast hN
  have h72 : ((7 * 2 : ℕ) : ℝ) = 14 := by norm_num
  rw [h72] at hN'
  exact hN'

theorem plan_cell8 (N : ℕ) (hN : N ≤ 4 * 2) : (N : ℝ) ≤ 8 := by
  have hN' : (N : ℝ) ≤ ((4 * 2 : ℕ) : ℝ) := by exact_mod_cast hN
  have h42 : ((4 * 2 : ℕ) : ℝ) = 8 := by norm_num
  rw [h42] at hN'
  exact hN'

theorem plan_census_40 : (8 + 8 + 16 + 8 : ℕ) = 40 := by norm_num

theorem plan_total_512 :
    (8 * 14 + 8 * 14 + 16 * 14 + 8 * 8 : ℕ) = 512 := by norm_num

/-! ## 6. Cauchy + fencing reuse (shared-sup template, CutR10 instance,
general per-subcell schema, center-extension schema). -/

theorem plan_cauchy_template (F : ℂ → ℂ) (P Q : ℂ → Prop) (C rhoC : ℝ)
    (hSup : ∀ z : ℂ, P z → ‖F z‖ ≤ C)
    (hSub : ∀ w : ℂ, Q w → ∀ u : ℂ, u ∈ Metric.sphere w rhoC → P u)
    (hCauchy : ∀ w : ℂ, Q w →
      (∀ u : ℂ, u ∈ Metric.sphere w rhoC → ‖F u‖ ≤ C) →
      ‖deriv F w‖ ≤ C / rhoC) :
    ∀ w : ℂ, Q w → ‖deriv F w‖ ≤ C / rhoC := by
  exact Door3TierBSubdiv.tierB_cauchy_of_sharedSup F P Q C rhoC
    (C / rhoC) rfl hSup hSub hCauchy

theorem plan_cutR10_reuse (cv : ℝ)
    (hNeed : (0.001 : ℝ) + (1 / 2 / 1) * 0.05 ≤ 8421 / 320000)
    (hFloor : (8421 / 320000 : ℝ) ≤ cv) :
    (0.001 : ℝ) + (1 / 2 / 1) * 0.05 ≤ cv :=
  Door3TierBSubdiv.tierB_cell_feasible (1 / 2) 1 (8421 / 320000) cv
    hNeed hFloor

theorem plan_subcell_fencing (eps M rho floor cv : ℝ)
    (hNeed : eps + M * rho ≤ floor) (hFloor : floor ≤ cv) :
    eps + M * rho ≤ cv :=
  le_trans hNeed hFloor

theorem plan_subcell_center_schema (m L rho F : ℝ)
    (h : F ≤ m - L * rho) : F + L * rho ≤ m := by
  linarith

/-! ## 7. Subcell-center TRUE headroom: cleared cases + honest flags.

Cleared: bottom-row R05/R06/R07-class premise floors clear 1.3 × the
design floor. Flags: outer band, leaf-tight and mid-tight classes cannot
reach 1.3 × on cited floors — each of their subcells needs a direct
rigorous center measurement (no continuity shortcut). -/

theorem plan_ok_R05 : (1.3 * 0.25 : ℝ) ≤ 0.3675 := by norm_num

theorem plan_ok_R06 : (1.3 * 0.25 : ℝ) ≤ 0.56 := by norm_num

theorem plan_ok_R07 : (1.3 * 0.14 : ℝ) ≤ 0.35 := by norm_num

theorem plan_flag_outer : ¬ ((1.3 * 0.0678 : ℝ) ≤ 0.06783) := by norm_num

theorem plan_flag_leaf : ¬ ((1.3 * 0.091 : ℝ) ≤ 0.0918) := by norm_num

theorem plan_flag_mid : ¬ ((1.3 * 0.14 : ℝ) ≤ 0.143) := by norm_num

end Door3SubdivPlan
