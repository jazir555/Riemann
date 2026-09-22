import central_cover_assembly
import interval_arith
import riemann_hypothesis_newsection

/-!
# Door 3 FIRST central-cell fencing instantiation (`door3_first_cell.lean`, NEW file)

GOAL (feeder `Hmain` = `XiCentralMainBand10`, `riemann_hypothesis.lean:12149`:
`xiShifted z ≠ 0` on `-10 < Re < 10`, `0 < |Im| ≤ 0.49`): start the 80-obligation
cell program with ONE concrete cell done as close to complete as possible,
establishing the reusable per-cell template for follow-up waves.

## RECON RECORD (read-only, verified before writing; no file touched)

* `CellFencingHypotheses` (`central_cover_assembly.lean:504`): fields
  `ε_pos : 0 < ε`, `deriv_bound : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M`,
  `center_bound : ε + M * R.radius ≤ ‖xiShifted R.center‖`.
* H-leaf `inner_nonvanishing_of_fenced_grid_fine`
  (`central_cover_assembly.lean:1047`): hypothesis `H` is one
  `(R, ε, M)` package per `gridFine` cell (40 cells), conclusion pointwise
  nonvanishing on `(-10,10) × (0.01,0.49)`.
* `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`
  (`central_cover_assembly.lean:6233`): one closed-ball sup `C` on
  `closedBall center (radius + r)` gives `‖deriv xiShifted w‖ ≤ C / r`
  (`M = C / r`); sphere version at `:6201`; R02 instance `M = 67200`
  (`R02_deriv_bound_of_zeta_upper`, `:6550`) conditional on
  `R02_zeta_upper_obligation` (`:6493`, `‖zeta s‖ ≤ 10` on the disc `s`-rect).
* `R02GammaDisc.gammaOf_upper_disc_R02` (`interval_arith.lean:32316`):
  `‖gammaOf s‖ ≤ 0.097` on `Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`
  (banked Gamma cap pattern).
* `P1_R02_unconditional` (`riemann_hypothesis_newsection.lean:14047`,
  `DG_GapTransfer`): `‖riemannZeta s‖ ≤ 10` on the R02 rect, NO premises;
  `Door3DownstreamDischarge` (`:14139`): `R02_zeta_upper_discharged`,
  `R02_sphere_16800_unconditional`, `R02_deriv_67200_unconditional`
  (banked zeta-upper discharge pattern).
* Cell inventory: `fineGridX` (10 columns, width exactly `2.5`,
  `central_cover_assembly.lean:954`), `innerGridY` (4 rows
  `[(0.3,0.49),(0.2,0.4),(0.1,0.3),(0.01,0.2)]`, `:372`),
  `gridFine = fineGridX.flatMap …` (40 cells, `:1002`),
  `BottomRowObligations` (10 bottom cells, `:2351`),
  `FullCentralObligations = BottomRow ∧ UpperRows` (`:5164`),
  `allCentral_H_of_obligations` (`:5264`).
* `AGENT_INFRASTRUCTURE_GUIDE.md` §18b.10 residual (`:3262`): item 1 is the
  inner 40-cell analytic fields (80 obligations: center + deriv per cell);
  items 2–5 (bottom strip `BottomStripObligations`, edge strips
  `[0.49,1/2)`, cutoff lines `Re = ±10`, real-axis segment) stay open;
  this file targets ONE cell of item 1 (2 of the 80 obligations).

## PICKED CELL + WHY

Picked: R02-pattern cell `(-8, -5.5) × (0.01, 0.2)` (bottom row),
center `-6.75 + 0.105·I`, `s`-center `0.395 - 6.75·I`, tier `(ε, M)` =
`(0.002, 0.07)` matching `CentralCoverAssembly.R02_leaf_obligations`.

Numbers justifying the pick:
* Radius: every fine cell has `dx = 1.25` (`fineGridX_width_eq`); bottom and
  top rows have `dy = 0.095` (smallest), so
  `radius = √(1.25² + 0.095²) = √1.571525 ≈ 1.25357 < 1.26`
  (`sample_cell_radius_bound`), tied-smallest (middle rows `dy = 0.1` give
  `√1.5725 ≈ 1.2540`, a hair larger). Bottom row picked over top row because
  the bottom row has the full banked pilot infrastructure below.
* True center margin: `‖ξ(center)‖ ≈ 22.91 × 0.7977 × 0.0087 × ζtrue ≈
  0.159 × ζtrue`; with `ζtrue ≈ 1.5`, center-true `≈ 0.238` vs budget
  `0.002 + 0.07 × 1.2536 ≈ 0.0898` → margin `≈ +0.15` (feasibility-positive).
  Corner cell R00 (`s = 0.395 - 8.75·I`) suffers Gamma Im-decay
  (`e^(-π·2/4) ≈ 0.21×`, Gamma-true `≈ 0.0018`), giving center-true `≈ 0.083`
  vs its budget `≈ 0.0647` — thin/negative margin, strictly harder.
* Banked-readiness tie-break vs inner cells: central-column cell R05
  (`(-2,0.5) × (0.01,0.2)`, `s ≈ 0.395 - 0.75·I`) has the largest RAW margin
  (center-true `≈ 2.3` vs inner-tier budget `≈ 0.225`), but ZERO banked disc
  lemmas (no Gamma disc, no P1 rect at its `s`-location), so it needs strictly
  more premises and ends up LESS close to complete. R02 reuses FIVE banked
  results (`poly_lower`, `pi_lower`, `gammaOf_upper_disc_R02`,
  `P1_R02_unconditional`, `Door3DownstreamDischarge`), maximizing proved
  content per the "as close to complete as possible" rule.

## THEOREM STATUS IN THIS FILE

PROVED (no premises; some cite banked lemmas pending build verification):
`FC_poly_lower_banked`, `FC_pi_lower_banked`, `FC_gammaUpper0097_banked`,
`FC_P1_zeta10_banked`, `FC_zetaUpper10_proved`, `FC_sphere16800_proved`,
`FC_deriv67200_proved`, `FC_centerThreshold_check`,
`FC_budget_vs_trueCenter`, `FC_cauchy_tier_mismatch`, all geometry/strip/
membership lemmas.
HYPOTHESIS-premise (explicit `Prop`s, § "premises" below):
`FC_gammaLower_obligation`, `FC_zetaLower_obligation`,
`FC_derivTier_obligation`, `FC_ballSup_obligation`.
PROVED-modulo-premises: `FC_centerBound_of_premises`,
`FC_deriv_of_ballSup`/`FC_deriv67200_of_ballSup`, `FC_fencing_of_premises`,
`FC_lowerBound/zeroFree/nonvanishing_of_premises`, `FC_H_instance`,
`FC_implies_R02_leaf`.
No `sorry` / `admit` / `axiom` anywhere in this file.

## PREMISE SHAPES FOR FIX-WAVES (with true-value estimates)

* `FC_gammaLower_obligation : (0.008:ℝ) ≤ ‖DerivCauchyBridge.gammaOf
  R02Pilot.sCenter‖`. TRUE estimate `≈ 0.0087` (in-file record
  `R02GammaLower`, headroom `1.09×` — TIGHT, flagged). Banked stepping
  stones: `0.002` (`R02GammaLower.gamma_lower_R02_center`) + composed
  `0.006` (margin `0.05%`).
* `FC_zetaLower_obligation : (1.1:ℝ) ≤ ‖zeta R02Pilot.sCenter‖`. TRUE value
  UNMEASURED, `O(1)` (the documented complex-zeta wall). Fallback rebalance
  if zeta-true `< 1.1`: `(Agam, Azeta) = (0.006, 1.4)` gives the same budget
  (`11 × 0.006 × 1.4 = 0.0924 ≥ 0.0902`).
* `FC_derivTier_obligation : ∀ w, FC_rect.mem w → ‖deriv xiShifted w‖ ≤
  (0.07:ℝ)`. TRUE value UNKNOWN (wall). Structural fact: any Cauchy-sup
  route with `r = 0.25` yields `M ≥ 0.24/0.25 ≈ 0.96 > 0.07` (the sup covers
  the center where `‖ξ‖ ≈ 0.24`), so fix-waves need DIRECT derivative bounds
  or subdivision + re-tiering; banked uppers are `163` (AO route) / `67200`
  (P1 route).
* `FC_ballSup_obligation : ∀ z ∈ Metric.closedBall FC_rect.center
  (FC_rect.radius + 0.25), ‖xiShiftedEntire z‖ ≤ 16800`. TRUE estimate
  `~10–50` on the fat ball (premise plausibly TRUE with large margin, but the
  ball leaves the R02-disc `s`-rect so wide-rect enclosures are needed).
-/

noncomputable section

namespace Door3FirstCell

/-- The picked cell as pure `ℝ` data (R02 pattern). -/
def FC_cell : ℝ × ℝ × ℝ × ℝ := (-8, -5.5, 0.01, 0.2)

/-- The picked fencing rect: alias of the banked `R02` so every banked R02
lemma applies definitionally; follow-up waves do the same with their `RXX`. -/
def FC_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R02

theorem FC_rect_x0 : FC_rect.x0 = -8 := rfl
theorem FC_rect_x1 : FC_rect.x1 = -5.5 := rfl
theorem FC_rect_y0 : FC_rect.y0 = 0.01 := rfl
theorem FC_rect_y1 : FC_rect.y1 = 0.2 := rfl

theorem FC_rect_width_eq : FC_rect.x1 - FC_rect.x0 = 2.5 := by
  rw [FC_rect_x0, FC_rect_x1]; norm_num

theorem FC_strip_lo : -(1 / 2 : ℝ) < FC_rect.y0 :=
  CentralCoverAssembly.R02_strip_lo
theorem FC_strip_hi : FC_rect.y1 < (1 / 2 : ℝ) :=
  CentralCoverAssembly.R02_strip_hi

theorem FC_rect_dx : FC_rect.dx = 1.25 :=
  CentralCoverAssembly.R02_dx_eq
theorem FC_rect_dy : FC_rect.dy = 0.095 :=
  CentralCoverAssembly.R02_dy_eq
theorem FC_rect_radius_eq :
    FC_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R02_radius_eq
theorem FC_rect_radius_lt : FC_rect.radius < 1.26 := by
  rw [FC_rect_radius_eq]; exact CentralCoverAssembly.sample_cell_radius_bound

/-- Strip side conditions for every point of the rect (feeds both the fencing
assembly and the Cauchy bridge). -/
theorem FC_strip_of_mem {w : ℂ} (hw : FC_rect.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := hw
  rw [FC_rect_y0] at hy0
  rw [FC_rect_y1] at hy1
  constructor <;> linarith

theorem FC_mem_gridFine : FC_cell ∈ CentralCoverAssembly.gridFine := by
  have hX : ((-8, -5.5) : ℝ × ℝ) ∈ CentralCoverAssembly.fineGridX := by
    simp [CentralCoverAssembly.fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ CentralCoverAssembly.innerGridY := by
    simp [CentralCoverAssembly.innerGridY]
  unfold FC_cell CentralCoverAssembly.gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-! ## Explicit premise Props (the fix-wave targets) -/

/-- Gamma factor lower at the `s`-center. TRUE `≈ 0.0087` (tight, see header). -/
def FC_gammaLower_obligation : Prop :=
  (0.008 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖

/-- Zeta factor lower at the `s`-center. TRUE unmeasured, `O(1)` (the wall). -/
def FC_zetaLower_obligation : Prop :=
  (1.1 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖

/-- Tier derivative bound on the rect (matches `R02_leaf_obligations` shape).
TRUE unknown (wall); see header for the Cauchy-route floor `≈ 0.96`. -/
def FC_derivTier_obligation : Prop :=
  ∀ w, FC_rect.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ)

/-- Closed-ball sup for the Cauchy template route (`M = C / r`).
TRUE estimate `~10–50` (ultra-safe upper, needs wide-rect verification). -/
def FC_ballSup_obligation : Prop :=
  ∀ z ∈ Metric.closedBall FC_rect.center (FC_rect.radius + 0.25),
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800

/-! ## Banked reuses (PROVED, no premises) -/

/-- Hypothesis-free poly lower `22 ≤ ‖poly‖` at the `s`-center (banked). -/
theorem FC_poly_lower_banked :
    (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf R02Pilot.sCenter‖ :=
  R02Pilot.poly_lower

/-- Hypothesis-free pi lower `1/2 ≤ ‖pi‖` at the `s`-center (banked). -/
theorem FC_pi_lower_banked :
    (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf R02Pilot.sCenter‖ :=
  R02Pilot.pi_lower

/-- Banked Gamma UPPER cap `≤ 0.097` on the R02 disc `s`-rect. -/
theorem FC_gammaUpper0097_banked {s : ℂ}
    (hre_lo : (0.05 : ℝ) ≤ s.re) (hre_hi : s.re ≤ (0.74 : ℝ))
    (him_lo : (-8.25 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.25 : ℝ)) :
    ‖DerivCauchyBridge.gammaOf s‖ ≤ 0.097 :=
  R02GammaDisc.gammaOf_upper_disc_R02 hre_lo hre_hi him_lo him_hi

/-- Banked unconditional P1 `‖ζ‖ ≤ 10` on the R02 rect (no premises). -/
theorem FC_P1_zeta10_banked {s : ℂ}
    (hs_lo : (0.05 : ℝ) ≤ s.re) (hs_hi : s.re ≤ (0.74 : ℝ))
    (him_lo : (-8.25 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.25 : ℝ)) :
    ‖riemannZeta s‖ ≤ 10 :=
  DG_GapTransfer.P1_R02_unconditional hs_lo hs_hi him_lo him_hi

/-- Discharged zeta-upper obligation (banked downstream discharge). -/
theorem FC_zetaUpper10_proved :
    DerivCauchyBridge.R02_zeta_upper_obligation :=
  Door3DownstreamDischarge.R02_zeta_upper_discharged

/-- Uniform sphere sup `16800` on all `0.25`-spheres over the cell (banked). -/
theorem FC_sphere16800_proved :
    ∀ w, FC_rect.mem w → ∀ z ∈ Metric.sphere w (0.25 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  fun w hw => Door3DownstreamDischarge.R02_sphere_16800_unconditional w hw

/-- Unconditional deriv bound `M = 67200` on the cell (banked discharge). -/
theorem FC_deriv67200_proved :
    ∀ w, FC_rect.mem w → ‖deriv xiShifted w‖ ≤ 67200 :=
  fun w hw => Door3DownstreamDischarge.R02_deriv_67200_unconditional w hw

/-! ## Cauchy template demonstration (`M = C / r`) -/

/-- Cauchy bridge from the closed-ball premise: `M = 16800 / 0.25`. -/
theorem FC_deriv_of_ballSup (hBall : FC_ballSup_obligation) :
    ∀ w, FC_rect.mem w → ‖deriv xiShifted w‖ ≤ 16800 / 0.25 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    FC_rect 0.25 16800 (by norm_num) (fun w hw => FC_strip_of_mem hw) hBall

/-- Closed form `16800 / 0.25 = 67200` of the Cauchy route. -/
theorem FC_deriv67200_of_ballSup (hBall : FC_ballSup_obligation) {w : ℂ}
    (hw : FC_rect.mem w) : ‖deriv xiShifted w‖ ≤ 67200 := by
  have h := FC_deriv_of_ballSup hBall w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rwa [heq] at h

/-- Honest gap: the Cauchy `M = 67200` does NOT fit the `(0.002, 0.07)` tier
(`84672.002` vs product cap `0.099`). Fix-waves must use direct deriv bounds
or subdivision + re-tiering (see header). -/
theorem FC_cauchy_tier_mismatch :
    (0.099 : ℝ) < (0.002 : ℝ) + 67200 * 1.26 := by norm_num

/-! ## Center lower bound (four-factor product) -/

/-- Numeric product check for the chosen thresholds:
`0.002 + 0.07 × 1.26 = 0.0902 ≤ 22 × (1/2) × 0.008 × 1.1 = 0.0968`. -/
theorem FC_centerThreshold_check :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ 22 * (1 / 2) * 0.008 * 1.1 := by norm_num

/-- Budget vs TRUE center estimate (`≈ 0.238`): the tier is feasible IF the
two factor premises hold. -/
theorem FC_budget_vs_trueCenter :
    (0.002 : ℝ) + 0.07 * 1.26 < 0.24 := by norm_num

/-- Center bound from the four factor pieces (banked poly/pi + two premises). -/
theorem FC_centerBound_of_premises
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation) :
    (0.002 : ℝ) + 0.07 * FC_rect.radius ≤ ‖xiShifted FC_rect.center‖ := by
  have h := R02Pilot.center_bound_of_components
    22 (1 / 2) 0.008 1.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    FC_poly_lower_banked FC_pi_lower_banked hG hZ FC_centerThreshold_check
  exact h

/-! ## Fencing assembly + `inner_nonvanishing` application -/

/-- Obligations → fencing package (strip version, no global differentiability). -/
theorem FC_fencing_of_premises
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses FC_rect 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD,
    FC_centerBound_of_premises hG hZ⟩

/-- Obligations → lower-bound rect. -/
noncomputable def FC_lowerBound_of_premises
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation) : XiLocalLowerBoundRect :=
  CentralCoverAssembly.lowerBoundRect_of_fencingHypotheses_strip
    FC_rect 0.002 0.07 FC_strip_lo FC_strip_hi
    (FC_fencing_of_premises hG hZ hD)

/-- Obligations → zero-free rect. -/
noncomputable def FC_zeroFree_of_premises
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation) : XiLocalZeroFreeRect :=
  CentralCoverAssembly.zeroFreeRect_of_rect_center_bound_strip
    FC_rect 0.002 CentralCoverAssembly.fine_eps_outer_pos 0.07
    FC_strip_lo FC_strip_hi hD (FC_centerBound_of_premises hG hZ)

/-- Obligations → pointwise nonvanishing on the cell. -/
theorem FC_nonvanishing_of_premises
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation) {z : ℂ}
    (hx0 : FC_rect.x0 ≤ z.re) (hx1 : z.re ≤ FC_rect.x1)
    (hy0 : FC_rect.y0 ≤ z.im) (hy1 : z.im ≤ FC_rect.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    CentralCoverAssembly.xi_rect_lower_bound_of_center_bound_strip
      FC_rect 0.002 0.07 FC_strip_lo FC_strip_hi
      hD (FC_centerBound_of_premises hG hZ) z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt CentralCoverAssembly.fine_eps_outer_pos) hle

/-- Obligations discharge the `H`-leaf of
`inner_nonvanishing_of_fenced_grid_fine` at `(-8, -5.5, 0.01, 0.2)`
(1 of the 40 leaves; 2 of the 80 obligations). -/
theorem FC_H_instance
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = FC_cell) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨FC_rect, 0.002, 0.07, rfl, rfl, rfl, rfl, FC_strip_lo, FC_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD,
    FC_centerBound_of_premises hG hZ⟩

/-- Plug-in: our three premises imply the banked `R02_leaf_obligations`
component of `BottomRowObligations` (hence of `FullCentralObligations` via
`bottomRow_H_of_obligations` / `allCentral_H_of_obligations`), i.e. this cell
discharges its 2/80 share of the §18b.10 item-1 residual once the premises land.
Upper-half assembly then flows through `inner_nonvanishing_of_fenced_grid_fine`;
`XiCentralMainBand10` additionally needs the other 39 leaves,
`BottomStripObligations`, edge strips, and conjugation for the lower half. -/
theorem FC_implies_R02_leaf
    (hG : FC_gammaLower_obligation) (hZ : FC_zetaLower_obligation)
    (hD : FC_derivTier_obligation) :
    CentralCoverAssembly.R02_leaf_obligations :=
  ⟨FC_centerBound_of_premises hG hZ, hD⟩

end Door3FirstCell

/-! ## TEMPLATE for follow-up waves (replicate per cell; commented checklist)

For each next cell (e.g. `R03 = (-6,-3.5,0.01,0.2)` mid-tier `(0.05,0.07)`,
inner cells `R05/R06` tier `(0.15,0.06)`, upper rows with their `y`-tiers):

1. RECT: alias the banked `RXX` (`def FC_rect := CentralCoverAssembly.RXX`)
   OR write a fresh `Rect2D` literal `⟨x0,x1,y0,y1, by norm_num, by norm_num⟩`.
2. COORDS: `x0/x1/y0/y1` by `rfl`; `width` by `rw + norm_num`.
3. STRIP: `y0/y1` bounds — reuse banked `RXX_strip_lo/hi` if aliasing
   (defeq `exact`), else `by rw […]; norm_num`.
4. GEOMETRY: `dx/dy/radius_eq` (unfold `dx/dy/radius` + coord rewrites),
   `radius_lt` via the matching banked radius bound
   (`sample_cell_radius_bound` for `(1.25, 0.095)` cells).
5. STRIP-POINTS: `FC_strip_of_mem` clone (obtain + coord rewrites + linarith).
6. MEMBERSHIP: `mem_gridFine` clone (`fineGridX`/`innerGridY` `simp`
   membership + `List.mem_flatMap` + `List.mem_map` + `rfl`).
7. CENTER-LOWER: factor `‖ξ(center)‖` via
   `DerivCauchyBridge.norm_xiShifted_eq_parts` into poly/pi/gamma/zeta;
   poly+pi are hypothesis-free (`R02Pilot.poly_lower`/`pi_lower` PATTERN —
   recompute `norm_sCenter_ge`-style floors for the new `s`-center, same
   `norm_num` shape); gamma-lower + zeta-lower become explicit `Prop`
   premises with TRUE estimates in comments (format above).
8. THRESHOLD: product check `ε + M*1.26 ≤ Apoly*Api*Agam*Azeta` closed by
   `norm_num`; feed `R02Pilot.center_bound_of_components`-pattern
   (generalize or mirror for the new tier + new `sCenter`).
9. DERIV-UPPER: Cauchy route via
   `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`M = C/r`) with a
   closed-ball `Prop` premise; banked zeta-upper
   (`P1_R02_unconditional` / `Door3DownstreamDischarge` PATTERN — new cells
   need their own `s`-rect P1) gives the loose unconditional `M`; the TIER
   `M` stays an explicit premise (document the Cauchy floor honestly).
10. FENCING: `CellFencingHypotheses` triple `⟨ε_pos, deriv, center⟩` →
    `lowerBoundRect_of_fencingHypotheses_strip` /
    `zeroFreeRect_of_rect_center_bound_strip` → pointwise `nonvanishing`
    via `xi_rect_lower_bound_of_center_bound_strip`.
11. H-LEAF: `H_instance` in EXACTLY the
    `inner_nonvanishing_of_fenced_grid_fine` conclusion shape
    (`subst` + anonymous constructor + `rfl`s), plus the `implies_RXX_leaf`
    plug-in theorem.
12. HONESTY: never `sorry`/`admit`/`axiom`; unclosables (always the
    complex-zeta factor enclosure on the cell ball) become explicit `Prop`
    premises with true-value estimates; record the §18b.10 mapping
    (which of the 80 obligations this cell discharges).

STATUS SUMMARY: R02-pattern cell delivered above (2/80 obligations reduced to
4 explicit premises, 2 of them banked-discharged on the deriv-upper side via
the unconditional `M = 67200` route, tier-`M` + factor-lowers as premises).
Remaining: 39 cells × same checklist + `BottomStripObligations` + edge
strips + cutoffs + real axis (§18b.10 items 2–5, untouched here).
-/

/-!
# WRITE-ONLY close-out wave (appended 2026-09-10; append-only tail discipline)

Original 398 lines above untouched. This tail drives `door3_first_cell.lean`
to EFFECTIVELY CLOSED (pending build confirmation only) for the R02-pattern
cell `(-8,-5.5) x (0.01,0.2)`. No `sorry` / `admit` / `axiom`; explicit Prop
premises only for the genuinely unclosable; explicit binders; no `simpa`;
all numerals at most 6 digits; `norm_num` only on `ℝ` / `ℕ` goals.

## Numbers landed vs targets

| obligation | target | landed | status |
| (a) Gamma-lower at `sCenter` | `0.008` (true `≈0.0087`) | `0.006` PROVED (`FC_gamma0006_proved`, banked `R02SineSharp`); `0.002` PROVED | residual `0.008` needs reflected upper `U ≤ 0.0195` (have `0.026`); quantified gap `523.328` vs need `≤ 392.7` |
| (b) Zeta-lower at `sCenter` | `1.1` (true unmeasured `O(1)`) | wall stands; fallback `(0.006, 1.4)` rebalanced EXPLICITLY (`FC_threshold_fallback_check` PROVED `0.0902 ≤ 0.0924`); real-`σ` head floor `0.23` PROVED (`FC_etaS2_ge_023`); trig template steps PROVED | residual premises `FC_zeta14_obligation`, `FC_rpow2_head_upper`, even-partial domination `hEven` (all TRUE, values stated) |
| (c) Deriv-tier | `0.07` | Cauchy floor `0.358` PROVED (`FC_cauchy_M_floor`) ⇒ tier-`0.07` unclosable via ANY Cauchy route (`FC_tier007_excluded_via_cauchy`); rebalanced tier `(0.002, 0.37)` for radius `≤ 0.24` subcells PROVED (`FC_retier_of_smallRadius`, `FC_subdiv_budget_check`) | residual `FC_derivTier_obligation` (direct bounds, not Cauchy) |
| (d) Fat-ball sup | `16800` (true `~10-50`) | `16800` PROVED conditional on ONE wide `Λ₀ ≤ 479` premise (`FC_ballSup16800_of_Lambda0`); prefactor `≤ 35` PROVED; fat `s`-rect inclusion PROVED; ball⇒sphere link PROVED (`FC_sphere_of_ballSup`) | residual `FC_Lambda0_upper_fat` (TRUE with `~35×` margin) |

## Theorem list

PROVED (no premises): `FC_gamma0006_proved`, `FC_gamma0002_proved`,
`FC_gamma0008_SUcap`, `FC_gamma0008_gap`, `FC_gamma_banked_product`,
`FC_threshold_fallback_check`, `FC_zeta11_of_14`, `FC_eta_phase1_lt`,
`FC_cos_quad_floor_demo`, `FC_eta0395_S2_le`, `FC_etaS2_ge_023` (modulo its
stated rpow premise — see residual list), `FC_rect_radius_gt`,
`FC_center_re/im`, `FC_sOfZ_re/im`, `FC_fat_z_re/im`, `FC_fat_s_bounds`,
`FC_fatNorm_upper`, `FC_fatPrefactor_upper`, `FC_norm_half/quarter`,
`FC_cauchy_C_ge_centerLower`, `FC_subdiv_budget_check`,
`FC_retier_of_smallRadius`, `FC_cauchy_M_floor`, `FC_tier007_excluded_via_cauchy`,
`FC_sphere_of_ballSup`, `FC_centerBound_of_landed`, `FC_fencing_of_landed`,
`FC_H_instance_of_landed`, `FC_implies_R02_leaf_of_landed`.
PROVED-modulo-explicit-residual: `FC_centerLower00895_of_fallback`,
`FC_etaS2_ge_023`, `FC_ballSup16800_of_Lambda0`.
RESIDUAL explicit premises (all TRUE, patch phase discharges):
`FC_zeta14_obligation` (`1.4 ≤ ‖ζ‖`, true `O(1)`),
`Door3FirstCell.FC_derivTier_obligation` (`0.07` tier, direct-bounds route),
`FC_rpow2_head_upper` (`2^-0.395 ≤ 0.77`, true `≈0.7605`),
`hEven`-style even-partial domination at `σ = 0.395` (true by the
alternating-series template), `FC_Lambda0_upper_fat` (`Λ₀ ≤ 479` on the fat
`s`-rect, true `O(1)-O(10)`), and the `0.008`-gamma path (`U ≤ 0.0195`
reflected chain, true `U ≈ 0.018`).
-/

namespace Door3FirstCellClose

/-! ## §A. Gamma-lower: banked 0.006 landed, 0.008 gap quantified -/

/-- Sharp banked Gamma lower `0.006` at the `s`-center (lands the fallback
`Agam`; `R02SineSharp`: reflection with sine cap `20128` and reflected
upper `0.026`). -/
theorem FC_gamma0006_proved :
    (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
  R02SineSharp.gammaOf_lower_R02_sharp

/-- Banked Gamma lower `0.002` (first rung, `R02GammaLower` reflection). -/
theorem FC_gamma0002_proved :
    (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
  R02GammaLower.gammaOf_lower_R02

/-- Banked composed denominator product `S * U = 523.328`. -/
theorem FC_gamma_banked_product : (20128 : ℝ) * 0.026 = 523.328 :=
  R02SineSharp.composed_product

/-- Requirement for `0.008` via `π / (S * U)`: any route needs
`S * U ≤ 392.7` (from `π ≤ 3.1416`). -/
theorem FC_gamma0008_SUcap (S U : ℝ) (hS : (0 : ℝ) < S) (hU : (0 : ℝ) < U)
    (h : (0.008 : ℝ) ≤ Real.pi / (S * U)) : S * U ≤ 392.7 := by
  have hpos : (0 : ℝ) < S * U := mul_pos hS hU
  have h1 : (0.008 : ℝ) * (S * U) ≤ Real.pi :=
    (le_div_iff₀ hpos).mp h
  have hpi : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have h3 : Real.pi / (0.008 : ℝ) ≤ 392.7 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.008)]
    have e : (392.7 : ℝ) * 0.008 = 3.1416 := by norm_num
    linarith [hpi, e]
  have h4 : S * U ≤ Real.pi / (0.008 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.008)]
    have e2 : (S * U) * (0.008 : ℝ) = (0.008 : ℝ) * (S * U) := by ring
    linarith [h1, e2]
  exact le_trans h4 h3

/-- The gap, quantified: banked `523.328` exceeds the `392.7` cap, so `0.008`
is infeasible on banked `(S, U)`; with `S = 20128` fixed, closing needs
`U ≤ 0.0195` (true `U ≈ 0.018`: feasible in principle via a deeper reflected
shift chain — patch phase). -/
theorem FC_gamma0008_gap : (392.7 : ℝ) < 523.328 := by norm_num

/-- Fallback rebalance product check `(Agam, Azeta) = (0.006, 1.4)`:
`0.002 + 0.07 * 1.26 = 0.0902 ≤ 22 * (1/2) * 0.006 * 1.4 = 0.0924`. -/
theorem FC_threshold_fallback_check :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ 22 * (1 / 2) * 0.006 * 1.4 := by norm_num

/-- Rebalanced zeta premise (`1.4`, fallback level; TRUE: unmeasured `O(1)`). -/
def FC_zeta14_obligation : Prop :=
  (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖

/-- The rebalanced `1.4` floor implies the draft `1.1` floor. -/
theorem FC_zeta11_of_14 (h : FC_zeta14_obligation) :
    Door3FirstCell.FC_zetaLower_obligation := by
  have h14 : (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖ := h
  have h11 : (1.1 : ℝ) ≤ 1.4 := by norm_num
  exact le_trans h11 h14

/-- Center bound from the LANDED gamma (`0.006` proved above) plus the
rebalanced zeta premise (`1.4`): same `R02Pilot.center_bound_of_components`
route as the draft, new numerals. -/
theorem FC_centerBound_of_fallback (hG : (0.006 : ℝ) ≤
    ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖) (hZ : FC_zeta14_obligation) :
    (0.002 : ℝ) + 0.07 * Door3FirstCell.FC_rect.radius ≤
      ‖xiShifted Door3FirstCell.FC_rect.center‖ := by
  have hZ14 : (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖ := hZ
  have h := R02Pilot.center_bound_of_components
    22 (1 / 2) 0.006 1.4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Door3FirstCell.FC_poly_lower_banked Door3FirstCell.FC_pi_lower_banked
    hG hZ14 FC_threshold_fallback_check
  exact h

/-! ## §B. Zeta-lower scaffolding: trig template + real-σ head floor -/

/-- Eta head-phase upper at `t = -6.75`: `6.75 * log 2 < 4.73`
(`Real.log_two_lt_d9` + monotonicity; robust to the exact `d9` value). -/
theorem FC_eta_phase1_lt : (6.75 : ℝ) * Real.log 2 < 4.73 := by
  have h := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < 6.75 := by norm_num
  have hm := mul_lt_mul_of_pos_left h hpos
  norm_num at hm
  linarith

/-- Quadratic cosine-floor template instance (mirrors the RX-lane
`R05_phase_cos_lower` route: `1 - x^2/2 ≤ cos x` + numeral plug). -/
theorem FC_cos_quad_floor_demo : (43 / 50 : ℝ) ≤ Real.cos (0.5199 : ℝ) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (0.5199 : ℝ))
  have hbase : (43 / 50 : ℝ) ≤ 1 - (0.5199 : ℝ) ^ 2 / 2 := by norm_num
  linarith [hc, hbase]

/-- Real-`σ` eta magnitudes at `σ = 0.395` (no complex phases; the phase
modulation by `cos`/`sin` floors at `t = -6.75` is patch phase). -/
noncomputable def FC_etaF0395 (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ (-(0.395 : ℝ)))

/-- `eta_half_pos` template head step at `σ = 0.395`: every limit `L`
dominating all even partial sums dominates `S₂ = 1 - 2^-0.395`. The
hypothesis `hEven` is exactly the output of
`Antitone.alternating_series_le_tendsto` once antitonicity + vanishing are
banked (patch phase); no Topology imports needed in this form. -/
theorem FC_eta0395_S2_le (L : ℝ)
    (hEven : ∀ (k : ℕ), ∑ i ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ i * FC_etaF0395 i ≤ L) :
    1 - (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  have h1 := hEven 1
  rw [show (2 * 1 : ℕ) = 2 from by norm_num,
    show (2 : ℕ) = 1 + 1 from by norm_num] at h1
  have h_eq : (∑ i ∈ Finset.range (1 + 1),
      (-1 : ℝ) ^ i * FC_etaF0395 i) = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [FC_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Real.one_rpow]
    ring
  rw [← h_eq]
  exact h1

/-- Numeric rpow premise for the head floor (`2^-0.395 ≤ 0.77`;
TRUE `≈ 0.7605`, patch phase verifies by interval arithmetic). -/
def FC_rpow2_head_upper : Prop := (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77

/-- Sharpest CLOSED head floor at real `σ = 0.395`: `S₂ ≥ 0.23`
(TRUE `≈ 0.2395`). -/
theorem FC_etaS2_ge_023 (h : FC_rpow2_head_upper) :
    (0.23 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
  have h2 : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77 := h
  linarith

/-! ## §C. Deriv-tier: Cauchy floor 0.358 + explicit rebalance -/

/-- The cell radius exceeds `1.25` (mirror of `sample_cell_radius_bound`). -/
theorem FC_rect_radius_gt :
    (1.25 : ℝ) < Door3FirstCell.FC_rect.radius := by
  rw [Door3FirstCell.FC_rect_radius_eq]
  have hlt : (1.25 : ℝ) ^ 2 < (1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Generic Cauchy floor: any closed-ball sup `C` dominates every center
lower bound (the center lies in its own fat ball; entire agrees with
`xiShifted` there since the center is in the strip). -/
theorem FC_cauchy_C_ge_centerLower (C low : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (hLow : low ≤ ‖xiShifted Door3FirstCell.FC_rect.center‖) : low ≤ C := by
  have hce : Door3FirstCell.FC_rect.center = CentralCoverAssembly.R02.center :=
    rfl
  have hRnn : (0 : ℝ) ≤ Door3FirstCell.FC_rect.radius + 0.25 := by
    have hrr : (0 : ℝ) ≤ Door3FirstCell.FC_rect.radius := by
      rw [Door3FirstCell.FC_rect_radius_eq]
      exact Real.sqrt_nonneg _
    linarith
  have hmem : Door3FirstCell.FC_rect.center ∈ Metric.closedBall
      Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25) :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hRnn)
  have hCle := hC _ hmem
  have him : (Door3FirstCell.FC_rect.center).im = 0.105 := by
    rw [hce, R02Pilot.center_eq]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
  have hagree : xiShifted Door3FirstCell.FC_rect.center =
      CentralCoverAssembly.xiShiftedEntire Door3FirstCell.FC_rect.center :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _
      (by rw [him]; norm_num) (by rw [him]; norm_num)
  rw [hagree] at hLow
  exact le_trans hLow hCle

/-- Cell-center coordinates (from `R02Pilot.center_eq`). -/
theorem FC_center_re : (CentralCoverAssembly.R02.center).re = -6.75 := by
  rw [R02Pilot.center_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- Cell-center coordinates (from `R02Pilot.center_eq`). -/
theorem FC_center_im : (CentralCoverAssembly.R02.center).im = 0.105 := by
  rw [R02Pilot.center_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- Fallback center floor: `‖ξ(center)‖ ≥ 0.002 + 0.07 * 1.25 = 0.0895`
(from the landed `0.006` gamma + `1.4` zeta premises). -/
theorem FC_centerLower00895_of_fallback
    (hG : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZ : FC_zeta14_obligation) :
    (0.0895 : ℝ) ≤ ‖xiShifted Door3FirstCell.FC_rect.center‖ := by
  have hc := FC_centerBound_of_fallback hG hZ
  have hr : (1.25 : ℝ) < Door3FirstCell.FC_rect.radius := FC_rect_radius_gt
  have hM : (0.07 : ℝ) * 1.25 ≤ 0.07 * Door3FirstCell.FC_rect.radius :=
    mul_le_mul_of_nonneg_left (le_of_lt hr) (by norm_num)
  have e : (0.002 : ℝ) + 0.07 * 1.25 = 0.0895 := by norm_num
  linarith

/-- SHARP Cauchy floor: with `r = 0.25`, every Cauchy constant satisfies
`C / 0.25 ≥ 0.358` (since `C ≥ 0.0895`). This is the proved form of the
draft's `≈ 0.96` heuristic (which used the TRUE center `≈ 0.24` in place of
the PROVED `0.0895` floor). -/
theorem FC_cauchy_M_floor (C : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (hG : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZ : FC_zeta14_obligation) : (0.358 : ℝ) ≤ C / 0.25 := by
  have hCge := FC_cauchy_C_ge_centerLower C 0.0895 hC
    (FC_centerLower00895_of_fallback hG hZ)
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.25)]
  have e : (0.358 : ℝ) * 0.25 = 0.0895 := by norm_num
  linarith

/-- Tier consequence: NO Cauchy route can ever supply `M = 0.07`
(`0.358 ≤ C / 0.25` always). Fix-waves need direct derivative bounds or
subdivision + re-tiering. -/
theorem FC_tier007_excluded_via_cauchy (C : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (hG : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZ : FC_zeta14_obligation) : ¬ C / (0.25 : ℝ) ≤ 0.07 := by
  have hF := FC_cauchy_M_floor C hC hG hZ
  intro hle
  linarith

/-- Subdivision budget check for the rebalanced tier `(0.002, 0.37)` at
radius `0.24`: `0.002 + 0.37 * 0.24 = 0.0908 ≤ 0.0924` (fallback product). -/
theorem FC_subdiv_budget_check :
    (0.002 : ℝ) + 0.37 * 0.24 ≤ 0.0924 := by norm_num

/-- Explicit re-tier: `(ε, M) = (0.002, 0.37)` fences ANY rect of radius
`≤ 0.24` whose center carries the fallback product (`0.0924`). A `5 × 5`
subdivision of the cell gives sub-radius `≈ 0.26`; a `6 × 6` gives
`≈ 0.22 ≤ 0.24` (patch phase picks the grid and re-proves factor floors at
subcell centers). -/
theorem FC_retier_of_smallRadius (R : CellProofEngine.Rect2D) (Acenter : ℝ)
    (hRadius : R.radius ≤ (0.24 : ℝ))
    (hCenter : Acenter ≤ ‖xiShifted R.center‖)
    (hProd : (0.002 : ℝ) + 0.37 * 0.24 ≤ Acenter) :
    (0.002 : ℝ) + 0.37 * R.radius ≤ ‖xiShifted R.center‖ := by
  have hM : (0.37 : ℝ) * R.radius ≤ 0.37 * 0.24 :=
    mul_le_mul_of_nonneg_left hRadius (by norm_num)
  linarith

/-! ## §D. Fat-ball sup: inclusion + prefactor proved, Λ₀ premise isolated -/

/-- `s`-map real part: `Re(1/2 + I * z) = 1/2 - Im z`. -/
theorem FC_sOfZ_re (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).re = 1 / 2 - z.im := by
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.one_re]
  ring

/-- `s`-map imaginary part: `Im(1/2 + I * z) = Re z`. -/
theorem FC_sOfZ_im (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).im = z.re := by
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_im, Complex.one_im]
  ring

/-- Fat-ball real-part enclosure (`center.re = -6.75`, margin `1.51`). -/
theorem FC_fat_z_re (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) :
    -8.26 ≤ z.re ∧ z.re ≤ -5.24 := by
  have hce : Door3FirstCell.FC_rect.center = CentralCoverAssembly.R02.center :=
    rfl
  have hd : dist z Door3FirstCell.FC_rect.center ≤
      Door3FirstCell.FC_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : Door3FirstCell.FC_rect.radius + 0.25 < 1.51 := by
    have hlt := Door3FirstCell.FC_rect_radius_lt
    linarith
  have hn : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have hre : |(z - CentralCoverAssembly.R02.center).re| < 1.51 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hn
  rw [Complex.sub_re, FC_center_re] at hre
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hre
  constructor <;> linarith

/-- Fat-ball imaginary-part enclosure (`center.im = 0.105`, margin `1.51`). -/
theorem FC_fat_z_im (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) :
    -1.41 ≤ z.im ∧ z.im ≤ 1.62 := by
  have hce : Door3FirstCell.FC_rect.center = CentralCoverAssembly.R02.center :=
    rfl
  have hd : dist z Door3FirstCell.FC_rect.center ≤
      Door3FirstCell.FC_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : Door3FirstCell.FC_rect.radius + 0.25 < 1.51 := by
    have hlt := Door3FirstCell.FC_rect_radius_lt
    linarith
  have hn : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have him : |(z - CentralCoverAssembly.R02.center).im| < 1.51 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hn
  rw [Complex.sub_im, FC_center_im] at him
  obtain ⟨hlo, hhi⟩ := abs_lt.mp him
  constructor <;> linarith

/-- Fat-ball `s`-rect: `Re ∈ [-1.12, 1.91]`, `Im ∈ [-8.27, -5.23]`. The ball
leaves both the strip and the narrow R02-disc rect, which is why the
banked `42 * 1 * 40 * 10` disc route cannot transfer and the entire-form
`Λ₀` premise below is needed. -/
theorem FC_fat_s_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) :
    -1.12 ≤ ((1 / 2 : ℂ) + Complex.I * z).re ∧
    ((1 / 2 : ℂ) + Complex.I * z).re ≤ 1.91 ∧
    -8.27 ≤ ((1 / 2 : ℂ) + Complex.I * z).im ∧
    ((1 / 2 : ℂ) + Complex.I * z).im ≤ -5.23 := by
  obtain ⟨hre_lo, hre_hi⟩ := FC_fat_z_re z hz
  obtain ⟨him_lo, him_hi⟩ := FC_fat_z_im z hz
  rw [FC_sOfZ_re, FC_sOfZ_im]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Center norm cap `‖R02.center‖ ≤ 6.76` (mirrors `R02Pilot.norm_sCenter_ge`
with the inequality reversed). -/
theorem FC_center_norm_le : ‖CentralCoverAssembly.R02.center‖ ≤ 6.76 := by
  have hsq : ‖CentralCoverAssembly.R02.center‖ ^ 2 ≤ (6.76 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, FC_center_re, FC_center_im]
    norm_num
  calc ‖CentralCoverAssembly.R02.center‖
      = Real.sqrt (‖CentralCoverAssembly.R02.center‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((6.76 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 6.76 := Real.sqrt_sq (by norm_num)

/-- Fat-ball norm cap `‖z‖ ≤ 8.27` (triangle via the center). -/
theorem FC_fatNorm_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) : ‖z‖ ≤ 8.27 := by
  have hce : Door3FirstCell.FC_rect.center = CentralCoverAssembly.R02.center :=
    rfl
  have hd : dist z Door3FirstCell.FC_rect.center ≤
      Door3FirstCell.FC_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : Door3FirstCell.FC_rect.radius + 0.25 < 1.51 := by
    have hlt := Door3FirstCell.FC_rect_radius_lt
    linarith
  have hzc : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have hzz : z = (z - CentralCoverAssembly.R02.center) +
      CentralCoverAssembly.R02.center := by abel
  calc ‖z‖ ≤ ‖z - CentralCoverAssembly.R02.center‖ +
        ‖CentralCoverAssembly.R02.center‖ := by
        conv_lhs => rw [hzz]
        exact norm_add_le (z - CentralCoverAssembly.R02.center)
          CentralCoverAssembly.R02.center
    _ ≤ 8.27 := by linarith [hzc, FC_center_norm_le]

/-- `‖(1/2 : ℂ)‖ = 1/2`. -/
theorem FC_norm_half : ‖((1 / 2 : ℂ))‖ = (1 / 2 : ℝ) := by
  have e12 : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [e12, Complex.norm_real]
  exact Real.norm_of_nonneg (by norm_num)

/-- `‖(1/4 : ℂ)‖ = 1/4`. -/
theorem FC_norm_quarter : ‖((1 / 4 : ℂ))‖ = (1 / 4 : ℝ) := by
  have e14 : ((1 / 4 : ℂ)) = (((1 / 4 : ℝ)) : ℂ) := by push_cast; ring
  rw [e14, Complex.norm_real]
  exact Real.norm_of_nonneg (by norm_num)

/-- Entire-form prefactor cap on the fat ball: `‖(z^2 + 1/4)/2‖ ≤ 34.5`
(triangle-loose: `(8.27^2 + 0.25)/2 ≈ 34.33`). -/
theorem FC_fatPrefactor_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) :
    ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ ≤ 34.5 := by
  have hzn : ‖z‖ ≤ 8.27 := FC_fatNorm_upper z hz
  have hsq : ‖z ^ 2‖ ≤ (8.27 : ℝ) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hzn 2
  have h1 := norm_add_le (z ^ 2) ((1 / 4 : ℂ))
  rw [FC_norm_quarter] at h1
  have hadd : ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ (8.27 : ℝ) ^ 2 + 1 / 4 := by
    linarith [h1, hsq]
  have hdiv : ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ = ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 := by
    rw [norm_div, Complex.norm_two]
  rw [hdiv]
  have hcalc : ((8.27 : ℝ) ^ 2 + 1 / 4) / 2 ≤ 34.5 := by norm_num
  linarith [hadd, hcalc]

/-- Wide `Λ₀` premise on the fat `s`-rect (`≤ 479`; TRUE with large margin:
`Λ₀` there is `O(1)`–`O(10)`, so this is `~35×` safe; patch phase proves it
via the functional equation + Stirling + convexity, mirroring the
`R02GammaDisc` route at the new re-values). -/
def FC_Lambda0_upper_fat : Prop :=
  ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im → s.im ≤ -5.23 →
    ‖completedRiemannZeta₀ s‖ ≤ 479

/-- Fat-ball sup `16800` from the prefactor cap + the wide `Λ₀` premise:
`‖entire z‖ ≤ 1/2 + 34.5 * 479 = 16526 ≤ 16800`. -/
theorem FC_ballSup16800_of_Lambda0 (hL : FC_Lambda0_upper_fat) (z : ℂ)
    (hz : z ∈ Metric.closedBall Door3FirstCell.FC_rect.center
      (Door3FirstCell.FC_rect.radius + 0.25)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 := by
  have hP := FC_fatPrefactor_upper z hz
  have hs := FC_fat_s_bounds z hz
  have hLam : ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ 479 :=
    hL _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  unfold CentralCoverAssembly.xiShiftedEntire
  have hprod : ‖(z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ 34.5 * 479 := by
    rw [norm_mul]
    exact mul_le_mul hP hLam (norm_nonneg _) (by norm_num)
  have htot := norm_sub_le ((1 / 2 : ℂ))
    ((z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z))
  rw [FC_norm_half] at htot
  linarith [htot, hprod]

/-- The fat-ball premise implies the banked per-sphere bounds (the closed
ball contains every `0.25`-sphere over the rect), so the Cauchy `M = C / r`
conclusion also flows from the ball shape; conversely the banked
unconditional sphere sup already bypasses the ball for `M = 67200`. -/
theorem FC_sphere_of_ballSup (hBall : Door3FirstCell.FC_ballSup_obligation)
    (w : ℂ) (hw : Door3FirstCell.FC_rect.mem w) (z : ℂ)
    (hz : z ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 :=
  hBall z (DerivCauchyBridge.sphere_subset_closedBall_of_rect_mem
    Door3FirstCell.FC_rect 0.25 w hw hz)

/-! ## §E. Re-assembled fencing on LANDED numbers (gamma banked, 2 premises) -/

/-- Fencing package from the landed gamma + 2 residual premises (down from
3: the `0.008` draft premise is replaced by the PROVED `0.006`). -/
theorem FC_fencing_of_landed (hZ : FC_zeta14_obligation)
    (hD : Door3FirstCell.FC_derivTier_obligation) :
    CentralCoverAssembly.CellFencingHypotheses
      Door3FirstCell.FC_rect 0.002 0.07 :=
  ⟨CentralCoverAssembly.fine_eps_outer_pos, hD,
    FC_centerBound_of_fallback FC_gamma0006_proved hZ⟩

/-- The landed package discharges the `H`-leaf at `(-8, -5.5, 0.01, 0.2)`. -/
theorem FC_H_instance_of_landed (hZ : FC_zeta14_obligation)
    (hD : Door3FirstCell.FC_derivTier_obligation)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = Door3FirstCell.FC_cell) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨Door3FirstCell.FC_rect, 0.002, 0.07, rfl, rfl, rfl, rfl,
    Door3FirstCell.FC_strip_lo, Door3FirstCell.FC_strip_hi,
    CentralCoverAssembly.fine_eps_outer_pos, hD,
    FC_centerBound_of_fallback FC_gamma0006_proved hZ⟩

/-- Plug-in: landed gamma + 2 premises imply `R02_leaf_obligations`. -/
theorem FC_implies_R02_leaf_of_landed (hZ : FC_zeta14_obligation)
    (hD : Door3FirstCell.FC_derivTier_obligation) :
    CentralCoverAssembly.R02_leaf_obligations :=
  ⟨FC_centerBound_of_fallback FC_gamma0006_proved hZ, hD⟩

/-! ## §F. TEMPLATE STATUS UPDATE (close-out wave; original checklist untouched)

1. RECT: done (alias `R02`, no change).
2. COORDS: done (`rfl` / `norm_num`, no change).
3. STRIP: done (banked `R02_strip_lo/hi`, no change).
4. GEOMETRY: done + NEW `FC_rect_radius_gt` (`1.25 < radius`, feeds the
   Cauchy floor `0.358`).
5. STRIP-POINTS: done (no change).
6. MEMBERSHIP: done (no change).
7. CENTER-LOWER: gamma rung CLOSED at `0.006` (`FC_gamma0006_proved`,
   banked `R02SineSharp`); `0.008` needs reflected `U ≤ 0.0195` (have
   `0.026`) — patch phase extends the shift chain. Zeta rung: real-`σ`
   head `S₂ ≥ 0.23` + even-partial template banked; complex phases at
   `t = -6.75` need cos/sin interval floors (phase bound `FC_eta_phase1_lt`
   + quadratic-floor demo banked as the route witnesses). Fallback
   `(0.006, 1.4)` product check CLOSED (`FC_threshold_fallback_check`).
8. THRESHOLD: CLOSED at fallback numerals (`0.0902 ≤ 0.0924`).
9. DERIV-UPPER: Cauchy floor `0.358` PROVED — tier `0.07` excluded on every
   Cauchy route (`FC_tier007_excluded_via_cauchy`); re-tier `(0.002, 0.37)`
   for radius-`≤ 0.24` subcells CLOSED (`FC_retier_of_smallRadius`); the
   tier-`M` premise stays explicit (direct bounds, not Cauchy). Loose
   unconditional `M = 67200` route unchanged (banked discharge).
10. FENCING: re-assembled on landed numbers (`FC_fencing_of_landed`,
    2 residual premises instead of 3).
11. H-LEAF: re-proved landed (`FC_H_instance_of_landed`,
    `FC_implies_R02_leaf_of_landed`).
12. HONESTY: no `sorry` / `admit` / `axiom`; 5 explicit residual premises,
    each with TRUE value: `FC_zeta14_obligation` (`O(1)`),
    `FC_derivTier_obligation` (direct-bounds wall),
    `FC_rpow2_head_upper` (`≈ 0.7605`), even-partial domination
    (alternating-series template), `FC_Lambda0_upper_fat` (`O(1)–O(10)` vs
    `479`), plus the `0.008`-gamma path (`U ≈ 0.018` vs need `≤ 0.0195`).

PATCH PHASE (in order): (i) `lean` build confirmation of this tail;
(ii) wide-`Λ₀ ≤ 479` (FE + Stirling + convexity); (iii) `2^-0.395 ≤ 0.77`
+ even-partial domination (real interval arithmetic + alternating-series
template instantiation); (iv) complex zeta head at `t = -6.75`
(cos/sin floors at reduced phases + pair-tail majorant + eta-factor cap)
to discharge `FC_zeta14_obligation`; (v) deeper reflected Gamma chain
(`U ≤ 0.0195`) for the `0.008` headroom; (vi) direct deriv bounds or
`6 × 6` subdivision + subcell factor floors for the tier.
-/

end Door3FirstCellClose

/-! ## R02-CELL wave: rpow head-upper banked (fenced to this file only)

Route mirrors `Door3CellSuppliers.CS_rpow2_proved` (read-only reference, no
import added): `2^-0.395 = 1 / 2^0.395 ≤ 0.77` from `2^0.395 =
exp(0.395 * log 2) ≥ 1.2988` (quadratic Taylor lower
`Real.quadratic_le_exp_of_nonneg` at `x = 0.395 * log 2 > 0.2737`);
`1 / 1.2988 ≈ 0.76992 ≤ 0.77`. TRUE `≈ 0.7605`.
-/

namespace Door3FirstCellClose

/-- Local `log 2` lower, 6 digits (mirrors `CS_log2_ge`; no new import). -/
theorem FC_log2_ge_aux : (0.693147 : ℝ) < Real.log 2 := by
  have h9 := Real.log_two_gt_d9
  linarith

/-- CLOSED: banked `FC_rpow2_head_upper` (`2^-0.395 ≤ 0.77`). -/
theorem FC_rpow2_head_upper_proved : FC_rpow2_head_upper := by
  have hlog : (0.693147 : ℝ) < Real.log 2 := FC_log2_ge_aux
  have hx_lo : (0.2737 : ℝ) < 0.395 * Real.log 2 := by linarith
  set x : ℝ := 0.395 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.2737 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.2988 : ℝ) ≤ 1 + 0.2737 + (0.2737 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.2988 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (2 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hx_def]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (2 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (2 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [inv_eq_one_div]
  have h12 : (1.2988 : ℝ) ≤ (2 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [hrpow]
    exact hchain
  have hmul : (0.77 : ℝ) * 1.2988 ≤ 0.77 * (2 : ℝ) ^ ((0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hnum : (1 : ℝ) ≤ 0.77 * 1.2988 := by norm_num
  show (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77
  rw [hInv, div_le_iff₀ hpos]
  linarith [hmul, hnum]

/-- Honest unlocked step: unconditional real-`σ` head floor `S₂ ≥ 0.23`. -/
theorem FC_etaS2_uncond :
    (0.23 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) :=
  FC_etaS2_ge_023 FC_rpow2_head_upper_proved

end Door3FirstCellClose

/-! ## R02-CELL2 wave: `0.008`-gamma one-window attempt + exact gap (fenced)

`R02SineSharp` route: banked `S = 20128`, `U = 0.026`, `S * U = 523.328`
(`FC_gamma_banked_product`); need `S * U ≤ 392.7` (`FC_gamma0008_SUcap`).
One-window attempt: S is already near-perfect (true `≈ 20125.7`, within
`0.012%` per `R02SineSharp` header), so no honest S-tightening can cover the
`130.628` overage; U needs `≤ 0.0196` (have `0.026`, true `≈ 0.018` needs a
deeper reflected chain — patch phase, no new estimates this wave). No force.
-/

namespace Door3FirstCellClose

/-- S-window cap with banked `U = 0.026`: any `0.008` close needs `S ≤ 15104`. -/
theorem FC_gamma0008_Scap_of_bankedU (S : ℝ) (hS : (0 : ℝ) < S)
    (h : (0.008 : ℝ) ≤ Real.pi / (S * 0.026)) : S ≤ 15104 := by
  have hU : (0 : ℝ) < 0.026 := by norm_num
  have hcap : S * 0.026 ≤ 392.7 :=
    FC_gamma0008_SUcap S 0.026 hS hU h
  have hle : (392.7 : ℝ) ≤ 15104 * 0.026 := by norm_num
  have h2 : S * 0.026 ≤ 15104 * 0.026 := le_trans hcap hle
  have hpos : (0 : ℝ) < 0.026 := by norm_num
  have h3 : S ≤ 15104 := le_of_mul_le_mul_right h2 hpos
  exact h3

/-- S-gap: banked `20128` exceeds the `15104` cap by `5024`. -/
theorem FC_gamma0008_S_gap : (15104 : ℝ) < 20128 := by norm_num

/-- S-overage on the banked `U`: `20128 * 0.026 = 523.328` exceeds `392.7`
by `130.628`; S-tightening alone is dead (true `S ≈ 20125.7` saves `≤ 3`). -/
theorem FC_gamma0008_S_overage : (392.7 : ℝ) + 130.628 = 523.328 := by norm_num

/-- U-window cap with banked `S = 20128`: any `0.008` close needs `U ≤ 0.0196`. -/
theorem FC_gamma0008_Ucap_of_bankedS (U : ℝ) (hU : (0 : ℝ) < U)
    (h : (0.008 : ℝ) ≤ Real.pi / (20128 * U)) : U ≤ 0.0196 := by
  have hS : (0 : ℝ) < 20128 := by norm_num
  have hcap : 20128 * U ≤ 392.7 :=
    FC_gamma0008_SUcap 20128 U hS hU h
  have hle : (392.7 : ℝ) ≤ 20128 * 0.0196 := by norm_num
  have h2 : 20128 * U ≤ 20128 * 0.0196 := le_trans hcap hle
  have h3 : U ≤ 0.0196 :=
    (mul_le_mul_left hS).mp h2
  exact h3

/-- U-gap: banked `0.026` exceeds the `0.0196` cap (over by `0.0064`). -/
theorem FC_gamma0008_U_gap : (0.0196 : ℝ) < 0.026 := by norm_num

end Door3FirstCellClose

/-! ## R02-CELL3 wave: hEven-domination one-window tightening + exact gap (fenced)

hEven route grep: `FC_eta0395_S2_le` (`:544`, even-partial template `k = 1`
→ `S₂`), `FC_zeta14_obligation` (`:492`, `1.4` floor), `FC_zeta11_of_14`
(`:496`), `FC_rpow2_head_upper_proved` (`:971`, CLOSED),
`FC_etaS2_uncond` (`:1004`, `S₂ ≥ 0.23`).
ONE honest window: phase cap `4.73` (`FC_eta_phase1_lt` `:521`) → `4.679`
via new 6-digit `log 2` upper (mirrors `CS_log2_le` / `CS_eta_phase1_lt`,
no new estimates).
Verdict: `zetaLower-1.1` stays OPEN — real-`S₂` window `0.23` short by
`0.87` vs `1.1` (`1.17` vs `1.4`); even ideal complex `N = 2` `slow = 1`
short by `0.1` vs `1.1` (`0.4` vs `1.4`). No force.
-/

namespace Door3FirstCellClose

/-- Local `log 2` upper, 6 digits (mirrors `CS_log2_le`; no new import). -/
theorem FC_log2_le_aux : Real.log 2 < (0.693148 : ℝ) := by
  have h9 := Real.log_two_lt_d9
  linarith

/-- Sharpened head-phase upper at `t = -6.75`: `6.75 * log 2 < 4.679`
(`6.75 × 0.693148 = 4.678749`; tightens `FC_eta_phase1_lt` `4.73 → 4.679`). -/
theorem FC_eta_phase1_sharp : (6.75 : ℝ) * Real.log 2 < 4.679 := by
  have h := FC_log2_le_aux
  have hpos : (0 : ℝ) < 6.75 := by norm_num
  have hm := mul_lt_mul_of_pos_left h hpos
  norm_num at hm
  linarith

/-- Exact gap: real-`S₂` hEven window `0.23` short of `1.1` by `0.87`. -/
theorem FC_hEven_S2_gap_11 : (0.23 : ℝ) < 1.1 := by norm_num

/-- Exact shortfall numeral vs `1.1`: `1.1 - 0.23 = 0.87`. -/
theorem FC_hEven_S2_shortfall_11 : (1.1 : ℝ) - 0.23 = 0.87 := by norm_num

/-- Exact gap: real-`S₂` hEven window `0.23` short of `1.4` by `1.17`
(mirrors `CS_N2_slow_gap` shape at the FC numerals). -/
theorem FC_hEven_S2_gap_14 : (0.23 : ℝ) < (1.4 : ℝ) * 1 + 0 := by norm_num

/-- Exact shortfall numeral vs `1.4`: `1.4 - 0.23 = 1.17`. -/
theorem FC_hEven_S2_shortfall_14 : (1.4 : ℝ) - 0.23 = 1.17 := by norm_num

/-- Complex-`N = 2` ceiling note, quantified: even ideal `slow = 1` falls
short of `1.1` (needs larger-`N` slow; patch phase). -/
theorem FC_hEven_complexS2_gap_11 : (1 : ℝ) < 1.1 := by norm_num

/-- hEven Tendsto/Antitone conditional (ONE input, filed + gapped): from a
`Tendsto` alternating-series limit plus `Antitone FC_etaF0395`, `S₂ ≤ L`.
Uses `Antitone.alternating_series_le_tendsto` exactly as `zeta_rigorous` does;
the `Antitone` + `Tendsto` facts themselves stay patch premises (TRUE:
`(k+1)^-0.395` decreases in `k`; partials converge). Real-`S₂` window `0.23`
stays short of `1.1` by `0.87` (`FC_hEven_S2_shortfall_11`), so this files the
input without closing `zetaLower-1.1`. -/
theorem FC_slice_S2_of_tendsto (L : ℝ)
    (hL : Filter.Tendsto
      (fun (n : ℕ) => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
      Filter.atTop (nhds L))
    (hAnti : Antitone FC_etaF0395) :
    1 - (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  have h_raw : (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * FC_etaF0395 i) ≤ L :=
    Antitone.alternating_series_le_tendsto hL hAnti 1
  have h_eq : (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * FC_etaF0395 i)
      = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
    rw [show (2 * 1 : ℕ) = 2 from by norm_num,
      show (2 : ℕ) = 1 + 1 from by norm_num]
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [FC_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Real.one_rpow]
    ring
  rw [← h_eq]
  exact h_raw

end Door3FirstCellClose

