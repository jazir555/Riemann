import Mathlib
import central_cover_assembly

/-! # Door-3 Tier-B subdivision machine (write-only design record).

Machine status: REUSABLE LEMMAS ONLY — no cell closed, no supplier discharged.
This file proves the Tier-B subdivision *machine* (count + shared-sup Cauchy
transfer + per-cell fencing + numeric instantiation) as full proofs from
Mathlib only. Every analytic input (shared sup, Cauchy rate, per-cell floors)
stays an explicit Prop premise for the supplier lanes.

Gap quantified (banked floor `8421 / 320000 = 0.026315625`, see
`Door3CutR10Retier.center_floor_eq` in `door3_cutR10_retier.lean`):
* Symbolic Tier-B instance `(C, rhoC, rho) = (12.87, 1, 0.05)` needs
  `0.001 + 12.87 * 0.05 = 0.6445`, which EXCEEDS the floor (`0.6445 > 0.0263`,
  recorded as `tierB_1287_005_infeasible`). At `rho = 0.05` the fencing need
  `0.001 + C * 0.05 ≤ 0.0263` forces `C ≤ 0.506` (`tierB_Ccap_of_0263`), i.e.
  the honest `12.87` must shrink by a factor of about `25.4` (to `≤ 0.5`).
  Tier-B viability in general needs `C ≤ 0.025 / rho`
  (`tierB_viability_of_rhoCap`).
* Tier-B target `(C, rho) = (1/2, 0.05)` needs `0.001 + 0.025 = 0.026 ≤ floor`
  and PASSES (`tierB_target_05_005_feasible`).

Consumers (supplier lanes that must land the `C ≤ 0.5` target):
* π/2 integral route (`door3_gamma_pi2.lean` verdict: dyadic tiers cap at
  `c ≈ 0.87`; the full tail-product integral route must supply the true
  `π/2` Gamma rate). The rate constant `c` stays an EXPLICIT hypothesis here
  (`tierB_cauchy_of_sharedSup`); the integral route is NOT attempted.
* Local-M σ-split (replace the uniform cap by the local `Γ ≈ 2.2` cap near
  the ball σ-slice with a tight merge constant).
* Zeta `≤ 2` strip (thin s-rect zeta upper feeding the joint sup).

Recon (read-only, not imported): `door3_cutR10_retier.lean` (Tier-B viability
`C ≤ 0.025/rho`, symbolic instance `(12.87, 0.001)`, floor identity),
`door3_cutR10_ballsup.lean` Wide Cauchy tail (shared-sup → per-cell fencing via
`sphere_subset_closedBall_of_rect_mem` + `uniform_deriv_of_closedBall_bound`,
mirrored locally by `hSub` + `hCauchy` below).
-/

namespace Door3TierBSubdiv

/-! ## 1. Subdivision count (general arithmetic).

For a rect of half-sides `(a, b)` covered by an `nx × ny` grid of subcells of
fencing radius `rho`, the analytic per-axis counts `2 * a / rho + 2` and
`2 * b / rho + 2` bound any grid no coarser than them, hence bound the total
subcell count `N`. -/

theorem tierB_subdiv_count (a b rho : ℝ) (nx ny N : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hrho : 0 < rho)
    (hNx : (nx : ℝ) ≤ 2 * a / rho + 2)
    (hNy : (ny : ℝ) ≤ 2 * b / rho + 2)
    (hN : N ≤ nx * ny) :
    (N : ℝ) ≤ (2 * a / rho + 2) * (2 * b / rho + 2) := by
  have hN' : (N : ℝ) ≤ (nx : ℝ) * (ny : ℝ) := by
    exact_mod_cast hN
  have hXnn : (0 : ℝ) ≤ 2 * a / rho + 2 := by
    have h1 : (0 : ℝ) ≤ 2 * a / rho :=
      div_nonneg (by linarith) (le_of_lt hrho)
    linarith
  have hYnn : (0 : ℝ) ≤ (ny : ℝ) := by
    exact_mod_cast Nat.zero_le ny
  have hmul : (nx : ℝ) * (ny : ℝ) ≤ (2 * a / rho + 2) * (2 * b / rho + 2) :=
    mul_le_mul hNx hNy hYnn hXnn
  exact le_trans hN' hmul

/-! ## 2. Shared-sup Cauchy transfer (local mirror of the Wide Cauchy tail).

`P` is the big-ball region predicate carrying the shared sup `C`; `Q` selects
the subcell centers. `hSub` locally mirrors
`sphere_subset_closedBall_of_rect_mem` (every per-cell sphere sits in the big
ball); `hCauchy` licenses the analytic Cauchy step at the EXPLICIT rate
constant `c` (mirror of `uniform_deriv_of_closedBall_bound`; the integral
route is not attempted — `c` and its equation `c = C / rhoC` are premises). -/

theorem tierB_cauchy_of_sharedSup (F : ℂ → ℂ) (P Q : ℂ → Prop)
    (C rhoC c : ℝ)
    (hRate : c = C / rhoC)
    (hSup : ∀ z : ℂ, P z → ‖F z‖ ≤ C)
    (hSub : ∀ w : ℂ, Q w → ∀ u : ℂ, u ∈ Metric.sphere w rhoC → P u)
    (hCauchy : ∀ w : ℂ, Q w → (∀ u : ℂ, u ∈ Metric.sphere w rhoC → ‖F u‖ ≤ C) →
      ‖deriv F w‖ ≤ c) :
    ∀ w : ℂ, Q w → ‖deriv F w‖ ≤ C / rhoC := by
  intro w hw
  rw [← hRate]
  exact hCauchy w hw (fun u hu => hSup u (hSub w hw u hu))

/-! ## 3. Per-subcell fencing (epsilon / M / rho triple).

From `(eps, M, rho) = (0.001, C / rhoC, 0.05)`: the fencing need closes
transitively once the numeric need meets the per-cell floor. -/

theorem tierB_cell_feasible (C rhoC floorC cv : ℝ)
    (hNeed : (0.001 : ℝ) + (C / rhoC) * 0.05 ≤ floorC)
    (hFloor : floorC ≤ cv) :
    (0.001 : ℝ) + (C / rhoC) * 0.05 ≤ cv :=
  le_trans hNeed hFloor

/-! ## 4. CutR10 instantiation at `(C, rhoC, rho) = (12.87, 1, 0.05)`.

Ball-region dims (recon, `door3_cutR10_ballsup.lean`): `CutR10` spans
`x ∈ [9.75, 10.25]` (half-side `a = 0.25`) by `y ∈ [-0.49, 0.49]`
(half-side `b = 0.49`). At `rho = 0.05` the analytic sides are
`2 * 0.25 / 0.05 + 2 = 12` by `2 * 0.49 / 0.05 + 2 = 21.6`: the interior
`12 × 21` grid holds `252` subcells under the analytic product, and the
provisioned cover with the ragged-edge row is `12 × 22 = 264` subcells. -/

theorem tierB_cutR10_ax : (2 * 0.25 / 0.05 + 2 : ℝ) = 12 := by
  norm_num

theorem tierB_cutR10_by_le : (2 * 0.49 / 0.05 + 2 : ℝ) ≤ 22 := by
  norm_num

theorem tierB_cutR10_cells_264 : (12 : ℝ) * 22 = 264 := by
  norm_num

theorem tierB_cutR10_interior_le (N : ℕ) (hN : N ≤ 12 * 21) :
    (N : ℝ) ≤ (2 * 0.25 / 0.05 + 2) * (2 * 0.49 / 0.05 + 2) :=
  tierB_subdiv_count 0.25 0.49 0.05 12 21 N (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN

theorem tierB_cutR10_N_le_264 (N : ℕ) (hN : (N : ℝ) ≤ (12 : ℝ) * 22) :
    (N : ℝ) ≤ 264 := by
  have heq : (12 : ℝ) * 22 = 264 := by
    norm_num
  rw [heq] at hN
  exact hN

/-! ## 5. Feasibility arithmetic at `(12.87, 0.05)` — RECORDED FAILURE.

Need `0.001 + 12.87 * 0.05 = 0.6445` against the banked floor
`8421 / 320000 = 0.026315625`: fails (`0.6445 > 0.0263`). To meet
`0.001 + C * 0.05 ≤ 0.0263` at `rho = 0.05` one needs `C ≤ 0.506`
(`tierB_Ccap_of_0263`); against the exact floor, `M ≤ 0.507`
(`tierB_Mcap_of_floor`). -/

theorem tierB_floor_eq :
    (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5) = 8421 / 320000 := by
  norm_num

theorem tierB_1287_need_eq : (0.001 : ℝ) + 12.87 * 0.05 = 0.6445 := by
  norm_num

theorem tierB_1287_005_infeasible :
    ¬ ((0.001 : ℝ) + 12.87 * 0.05 ≤ 8421 / 320000) := by
  norm_num

theorem tierB_Ccap_of_0263 (C : ℝ)
    (h : (0.001 : ℝ) + C * 0.05 ≤ 0.0263) :
    C ≤ 0.506 := by
  linarith

theorem tierB_Mcap_of_floor (M : ℝ)
    (h : (0.001 : ℝ) + M * 0.05 ≤ 8421 / 320000) :
    M ≤ 0.507 := by
  linarith

/-! ## 6. Tier-B target and viability cap.

The `(C, rho) = (1/2, 0.05)` target the π/2 + local-M + zstrip program must
hit, and the general viability shape `C ≤ 0.025 / rho` (from
`door3_cutR10_retier.lean`). -/

theorem tierB_target_05_005_feasible :
    (0.001 : ℝ) + (1 / 2) * 0.05 ≤ 8421 / 320000 := by
  norm_num

theorem tierB_viability_of_rhoCap (C rho : ℝ) (hrho : 0 < rho)
    (h : C ≤ 0.025 / rho) :
    C * rho ≤ 0.025 :=
  (le_div_iff₀ hrho).mp h

#print axioms tierB_subdiv_count
#print axioms tierB_cauchy_of_sharedSup
#print axioms tierB_cell_feasible
#print axioms tierB_1287_005_infeasible
#print axioms tierB_target_05_005_feasible

/-! ## Patch remainder (not this file).

* Suppliers still owed: joint ball sup `C ≤ 0.5` (needs π/2 integral rate +
  local-M σ-split + zeta `≤ 2` strip), per-subcell center floors, and the
  `12 × 22` subdivision cover construction with `rho = 0.05` subcells.
* Central registration of this machine happens later; no existing file was
  touched.
-/

end Door3TierBSubdiv
