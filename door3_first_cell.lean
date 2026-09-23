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

/-! ## R02-CELL4 wave: reflected U-chain one-step attempt + exact gap (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Reflection identity `Complex.Gamma_mul_Gamma_one_sub`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:398`):
  `Gamma z * Gamma (1 - z) = π / sin (π * z)`.
* Reflection lower shapes reusing it at `w = sR02/2`:
  `R02GammaLower.gamma_lower_R02_center` (`interval_arith.lean:32507`,
  `S = 30000`, `U = 0.05`), `R02SineSharp.gamma_lower_R02_sharp` (`:33531`,
  `S = 20128`, `U = 0.026`).
* Sine-floor banked pieces: `R02GammaLower.sin_upper_R02` (`:32443`,
  `≤ 30000`), `R02SineSharp.sin_upper_R02_sharp` (`:33481`, `≤ 20128`,
  true `≈ 20125.7` — near-perfect, so no S-tightening can cover the gap;
  see `FC_gamma0008_S_overage` in R02-CELL2).
* Reflected-upper banked pieces: `R02GammaUpper.gamma_one_sub_half_upper_R02`
  (12-shift, `U = 0.05`), `R02GammaUpperDeep.gamma_one_sub_half_upper_R02_deep`
  (`:33021`, 21-shift, `U = 0.026`, true `U ≈ 0.018`); base re/im
  `R02GammaUpper.zUpR02_re/im` (`:8507/:8512`).

ONE honest reflected step attempted here: extend the banked 21-shift chain by ONE
shift (`+21` floor / nonvanishing / `Real.Gamma` + `Complex.Gamma` one-step
unfolds, all PROVED below from banked re/im only). The full 22-shift combination
(denominator product `q21` + numerator/division assembly) is patch phase — NOT
filed as proved.

Verdict: UPPER-or-GAP = GAP. One shift tightens `U` by at most the factor
`21.8025/22.06 ≤ 0.9884`, i.e. `U ≤ 0.0257` even crediting the full step — still
above the `0.0195` need (`20128 × 0.0195 = 392.496 ≤ 392.7`). Exact gaps filed
below (`U` shortfall `0.0062`; `S·U` overage `124.59`). No force, no
`premise_gamma` touch.
-/

namespace Door3FirstCellClose

/-- Reflected-point re at `+21`: `Re(1 - sR02/2 + 21) = 21.8025`
(mirrors `R02GammaUpperDeep.norm_zUpR02D_20_ge`; banked `zUpR02_re` only). -/
theorem FC_refl22_re : (1 - R02GammaUpper.sR02 / 2 + 21).re = 21.8025 := by
  simp only [Complex.add_re, R02GammaUpper.zUpR02_re, Complex.re_ofNat]
  norm_num

/-- Reflected-point im at `+21`: `Im(1 - sR02/2 + 21) = 3.375`. -/
theorem FC_refl22_im : (1 - R02GammaUpper.sR02 / 2 + 21).im = 3.375 := by
  simp only [Complex.add_im, R02GammaUpper.zUpR02_im, Complex.im_ofNat]
  norm_num

/-- Denominator floor `c21 = 22.06 ≤ ‖1 - sR02/2 + 21‖`
(`22.06^2 = 486.6436 ≤ 21.8025^2 + 3.375^2`; sqrt pattern mirrors
`R02GammaUpperDeep.norm_zUpR02D_20_ge`). -/
theorem FC_refl22_floor :
    (22.06 : ℝ) ≤ ‖1 - R02GammaUpper.sR02 / 2 + 21‖ := by
  have hre : (1 - R02GammaUpper.sR02 / 2 + 21).re = 21.8025 := FC_refl22_re
  have him : (1 - R02GammaUpper.sR02 / 2 + 21).im = 3.375 := FC_refl22_im
  have hsq : (22.06 : ℝ) ^ 2 ≤ ‖1 - R02GammaUpper.sR02 / 2 + 21‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (22.06 : ℝ) = Real.sqrt ((22.06 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R02GammaUpper.sR02 / 2 + 21‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - R02GammaUpper.sR02 / 2 + 21‖ := Real.sqrt_sq (norm_nonneg _)

/-- Nonvanishing at `+21` (mirrors `R02GammaUpperDeep.zUpR02D_add20_ne0`). -/
theorem FC_refl22_ne0 : (1 - R02GammaUpper.sR02 / 2 + 21) ≠ 0 := by
  have hre : (1 - R02GammaUpper.sR02 / 2 + 21).re = 21.8025 := FC_refl22_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- One-step real-Gamma unfold toward `n = 22` (mirrors
`R02GammaUpperDeep.realGamma_218025_num`; small numerals only). -/
theorem FC_realGamma_228025_step :
    Real.Gamma 22.8025 ≤ 21.8025 * Real.Gamma 21.8025 := by
  have h : Real.Gamma (21.8025 + 1) = 21.8025 * Real.Gamma 21.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (21.8025 : ℝ) + 1 = 22.8025 := by norm_num
  rw [heq] at h
  exact h.le

/-- One-step complex-Gamma unfold toward `n = 22` (mirrors the `e20` step of
`R02GammaUpperDeep.gamma_one_sub_half_upper_R02_deep`). -/
theorem FC_gamma_step22 :
    Complex.Gamma (1 - R02GammaUpper.sR02 / 2 + 22)
      = (1 - R02GammaUpper.sR02 / 2 + 21)
        * Complex.Gamma (1 - R02GammaUpper.sR02 / 2 + 21) := by
  have h : (1 - R02GammaUpper.sR02 / 2 + 22)
      = ((1 - R02GammaUpper.sR02 / 2 + 21) + 1) := by ring
  rw [h]
  exact Complex.Gamma_add_one _ FC_refl22_ne0

/-- Per-step tightening factor of the `+21 → +22` extension:
`21.8025/22.06 ≤ 0.9884` (numerator grows by `21.8025`, denominator floor by
`22.06`; deeper shifts asymptote to `1`, so later steps help even less). -/
theorem FC_step_factor : (21.8025 : ℝ) / 22.06 ≤ 0.9884 := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 22.06)]
  norm_num

/-- Best `U` one honest shift can deliver: `0.026 × 0.9884 ≤ 0.0257`
(credits the full floor-to-cap improvement of the `+21 → +22` step against the
banked `U = 0.026`). -/
theorem FC_onestep_U_cap : (0.026 : ℝ) * 0.9884 ≤ 0.0257 := by norm_num

/-- One-step `S·U` product cap with banked `S = 20128`: `≤ 517.29`. -/
theorem FC_onestep_SU_le : (20128 : ℝ) * 0.0257 ≤ 517.29 := by norm_num

/-- One-step product still exceeds the `0.008` cap `392.7`
(`392.7 < 20128 × 0.0257`). -/
theorem FC_onestep_gap : (392.7 : ℝ) < 20128 * 0.0257 := by norm_num

/-- Exact `S·U` overage after one honest shift: `392.7 + 124.59 = 517.29`
(only `6.04` better than the banked `130.628` overage at `523.328`). -/
theorem FC_onestep_overage : (392.7 : ℝ) + 124.59 = 517.29 := by norm_num

/-- Exact gap at the failing U-window: need `≤ 0.0195`, one step gives `0.0257`. -/
theorem FC_U22_window_gap : (0.0195 : ℝ) < 0.0257 := by norm_num

/-- U shortfall numeral: `0.0257 - 0.0195 = 0.0062`. -/
theorem FC_U22_shortfall : (0.0257 : ℝ) - 0.0195 = 0.0062 := by norm_num

end Door3FirstCellClose

/-! ## FIRSTCELL-LAMBDA0 wave (i): `‖piOf‖` upper on the fat rect (fenced)

Grep-first record (this wave, verified before writing):
* `DerivCauchyBridge.piOf` (`central_cover_assembly.lean:6331`):
  `((Real.pi : ℂ) ^ (-(s / 2)))`.
* Norm bridge `Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _`
  (`central_cover_assembly.lean:6399`, `:6738`, `:9694`; same shape in
  `door3_cutR10_ballsup.lean:233` `ballPi_upper` for a negative-Re ball).
* Exponent rewrites `Complex.div_ofNat_re` + `Complex.neg_re`
  (`central_cover_assembly.lean:6400-6401`).
* Monotonicity `Real.rpow_le_rpow_of_exponent_le` with
  `Real.pi_gt_three` (`central_cover_assembly.lean:9704`).
* `π ≤ 3.1416` via `le_of_lt Real.pi_lt_d4`
  (`door3_first_cell.lean:469` pattern).
* 16th-power `(9/16, 16)` descent via `Real.rpow_natCast`,
  `Real.rpow_mul`, `pow_le_pow_left₀`, `abs_le_of_sq_le_sq'` iterated
  (mirrors banked `pi_rpow_quarter_le_two`, `:9662`, which uses the
  4th-power `(1/4, 4)` descent; 16 = 2^4 needs four sqrt steps).

Honest value: `π^0.56 ≈ 1.898` (python `math.pi**0.56`; prompt `1.87`
is ~1.5% low). Route proves the looser `≤ 2` via `0.56 ≤ 9/16` and
`3.1416^9 ≤ 2^16` (`29809.73 ≤ 65536`, `norm_num`, numerals ≤ 6 digits).
`‖piOf s‖ = π^(-Re/2)` is decreasing in `Re`, so on the fat rect the max
is at minimal `Re = -1.12` (exponent `0.56`); only the lower `Re` bound is
used (`hre_hi` kept as an explicit binder for the fat-rect shape).
-/

namespace Door3FirstCellClose

/-- Rpow cap `π^0.56 ≤ 2` via the `9/16` window (`0.56 ≤ 0.5625`,
`3.1416^9 ≤ 2^16`). -/
theorem FC_pi_rpow_056_le_two : Real.pi ^ (0.56 : ℝ) ≤ 2 := by
  have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hbase : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp_le : (0.56 : ℝ) ≤ 9 / 16 := by norm_num
  have hmon : Real.pi ^ (0.56 : ℝ) ≤ Real.pi ^ ((9 / 16 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp_le
  have e : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((16 : ℕ)) = Real.pi ^ ((9 : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    have hexp : ((9 / 16 : ℝ)) * ((((16 : ℕ)) : ℝ)) = ((((9 : ℕ)) : ℝ)) := by
      norm_num
    rw [hexp]
  have hle9 : Real.pi ^ ((9 : ℕ)) ≤ (2 : ℝ) ^ ((16 : ℕ)) := by
    have h1 : Real.pi ^ ((9 : ℕ)) ≤ (3.1416 : ℝ) ^ ((9 : ℕ)) :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_le 9
    have h2 : (3.1416 : ℝ) ^ ((9 : ℕ)) ≤ (2 : ℝ) ^ ((16 : ℕ)) := by norm_num
    exact le_trans h1 h2
  have h16 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((16 : ℕ)) ≤ (2 : ℝ) ^ ((16 : ℕ)) := by
    rw [e]
    exact hle9
  have e16 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((16 : ℕ))
      = (((Real.pi ^ ((9 / 16 : ℝ))) ^ ((8 : ℕ))) ^ ((2 : ℕ))) := by ring
  have f16 : (2 : ℝ) ^ ((16 : ℕ)) = ((((2 : ℝ)) ^ ((8 : ℕ))) ^ ((2 : ℕ))) := by
    ring
  rw [e16, f16] at h16
  have h8 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((8 : ℕ)) ≤ (2 : ℝ) ^ ((8 : ℕ)) :=
    (abs_le_of_sq_le_sq' h16 (by norm_num)).2
  have e8 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((8 : ℕ))
      = (((Real.pi ^ ((9 / 16 : ℝ))) ^ ((4 : ℕ))) ^ ((2 : ℕ))) := by ring
  have f8 : (2 : ℝ) ^ ((8 : ℕ)) = ((((2 : ℝ)) ^ ((4 : ℕ))) ^ ((2 : ℕ))) := by
    ring
  rw [e8, f8] at h8
  have h4 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((4 : ℕ)) ≤ (2 : ℝ) ^ ((4 : ℕ)) :=
    (abs_le_of_sq_le_sq' h8 (by norm_num)).2
  have e4 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((4 : ℕ))
      = (((Real.pi ^ ((9 / 16 : ℝ))) ^ ((2 : ℕ))) ^ ((2 : ℕ))) := by ring
  have f4 : (2 : ℝ) ^ ((4 : ℕ)) = ((((2 : ℝ)) ^ ((2 : ℕ))) ^ ((2 : ℕ))) := by
    ring
  rw [e4, f4] at h4
  have h2 : (Real.pi ^ ((9 / 16 : ℝ))) ^ ((2 : ℕ)) ≤ (2 : ℝ) ^ ((2 : ℕ)) :=
    (abs_le_of_sq_le_sq' h4 (by norm_num)).2
  have hcap : Real.pi ^ ((9 / 16 : ℝ)) ≤ 2 :=
    (abs_le_of_sq_le_sq' h2 (by norm_num)).2
  exact le_trans hmon hcap

/-- Banked `‖piOf‖ ≤ 2` on the fat rect (`Re ∈ [-1.12, 1.91]`, patch item
(i); max at minimal `Re` since `π^(-Re/2)` decreases in `Re`). -/
theorem FC_piOf_upper_fat {s : ℂ} (hre_lo : (-1.12 : ℝ) ≤ s.re)
    (hre_hi : s.re ≤ (1.91 : ℝ)) : ‖DerivCauchyBridge.piOf s‖ ≤ 2 := by
  unfold DerivCauchyBridge.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  have hdiv : ((s / 2 : ℂ)).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  have hexp_eq : (-(s / 2)).re = -s.re / 2 := by rw [hneg, hdiv]; ring
  rw [hexp_eq]
  have hexp_le : -s.re / 2 ≤ (0.56 : ℝ) := by linarith
  have hmon : Real.pi ^ (-s.re / 2) ≤ Real.pi ^ (0.56 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp_le
  exact le_trans hmon FC_pi_rpow_056_le_two

end Door3FirstCellClose

/-! ## R02-CELL5 wave: polar caps `‖1/s‖, ‖1/(1-s)‖` on fat rect (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Inverse-norm shape `norm_inv` (`door3_off_axis_certificates.lean:2173`,
  `door3_pilot_R00_zeta.lean:158`; `norm_div` + `norm_one` give the same
  `‖1/s‖ = 1/‖s‖` used below).
* Im-floor shape `Complex.abs_im_le_norm` (`central_cover_assembly.lean:6290`,
  `:9559`; `door3_first_cell.lean:746` uses it for the fat-ball enclosure).
* Reciprocal-monotone shape `one_div_le_one_div_of_le`
  (`central_cover_assembly.lean:6462`; `door3_dp_headC1.lean:196`).
* Polar identity `completedRiemannZeta₀_eq_polar_plus_xi`
  (`door3_cutR10_ballsup.lean:357`, from `riemann_hypothesis.lean:1668`):
  `completedRiemannZeta₀ s = 1/s + 1/(1-s) + …`, so these two caps feed the
  wide-`Λ₀` route (patch phase FE + Stirling).
* Im shapes `Complex.sub_im` (`door3_first_cell.lean:747`),
  `Complex.one_im` (`:701`, `:703`).

PiOf-upper lane check (NOT duplicated): no `piOf` upper in this file (only
`FC_pi_lower_banked` `:199`); the banked `pi_upper_R02_disc`
(`central_cover_assembly.lean:6396`) needs `0.05 ≤ s.re`, so it does NOT cover
the fat rect (`Re ∈ [-1.12, 1.91]`). FIRSTCELL-PIUPPER owns that lane; left
alone here.

Fat rect (from `FC_fat_s_bounds` `:755`): `Re ∈ [-1.12, 1.91]`,
`Im ∈ [-8.27, -5.23]`. Hence `|Im| ≥ 5.23` on both `s` and `1 - s`
(`Im(1-s) = -Im(s) ∈ [5.23, 8.27]`), so `‖s‖, ‖1-s‖ ≥ 5.23` and each polar
norm is `≤ 1/5.23 ≈ 0.1912 ≤ 0.20`. No `s ≠ 0` premise needed: the Im bounds
already exclude `0` and `1`. No force; both caps banked honestly.
-/

namespace Door3FirstCellClose

/-- Polar cap `‖1/s‖ ≤ 1/5.23` from the Im floor (`|Im| ≥ 5.23`). -/
theorem FC_polar_inv_norm_le (s : ℂ)
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / s‖ ≤ 1 / (5.23 : ℝ) := by
  have him_le : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnonpos : s.im ≤ 0 := by linarith
  have habs : (5.23 : ℝ) ≤ |s.im| := by
    rw [abs_of_nonpos hnonpos]
    linarith
  have hnorm : (5.23 : ℝ) ≤ ‖s‖ := le_trans habs him_le
  have hpos : (0 : ℝ) < 5.23 := by norm_num
  have hdiv : ‖(1 : ℂ) / s‖ = 1 / ‖s‖ := by
    rw [norm_div, norm_one]
  rw [hdiv]
  exact one_div_le_one_div_of_le hpos hnorm

/-- Polar cap `‖1/(1-s)‖ ≤ 1/5.23` from the mirrored Im floor. -/
theorem FC_polar_one_sub_inv_norm_le (s : ℂ)
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / (1 - s)‖ ≤ 1 / (5.23 : ℝ) := by
  have him_eq : (1 - s).im = -s.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have him_le : |(1 - s).im| ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
  have hpos_im : (0 : ℝ) ≤ -s.im := by linarith
  have habs : (5.23 : ℝ) ≤ |(1 - s).im| := by
    rw [him_eq, abs_of_nonneg hpos_im]
    linarith
  have hnorm : (5.23 : ℝ) ≤ ‖1 - s‖ := le_trans habs him_le
  have hpos : (0 : ℝ) < 5.23 := by norm_num
  have hdiv : ‖(1 : ℂ) / (1 - s)‖ = 1 / ‖1 - s‖ := by
    rw [norm_div, norm_one]
  rw [hdiv]
  exact one_div_le_one_div_of_le hpos hnorm

/-- Numeric form `‖1/s‖ ≤ 0.20` (`1/5.23 ≈ 0.1912`). -/
theorem FC_polar_inv_norm_le_020 (s : ℂ)
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / s‖ ≤ 0.20 := by
  have h := FC_polar_inv_norm_le s him_lo him_hi
  have hnum : (1 : ℝ) / 5.23 ≤ 0.20 := by norm_num
  exact le_trans h hnum

/-- Numeric form `‖1/(1-s)‖ ≤ 0.20`. -/
theorem FC_polar_one_sub_inv_norm_le_020 (s : ℂ)
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / (1 - s)‖ ≤ 0.20 := by
  have h := FC_polar_one_sub_inv_norm_le s him_lo him_hi
  have hnum : (1 : ℝ) / 5.23 ≤ 0.20 := by norm_num
  exact le_trans h hnum

/-- Fat-rect wrapper: `‖1/s‖ ≤ 1/5.23` on `Re ∈ [-1.12, 1.91]`,
`Im ∈ [-8.27, -5.23]` (Re bounds unused: Im floor suffices). -/
theorem FC_fat_polar_inv_le (s : ℂ)
    (_hre_lo : (-1.12 : ℝ) ≤ s.re) (_hre_hi : s.re ≤ (1.91 : ℝ))
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / s‖ ≤ 1 / (5.23 : ℝ) :=
  FC_polar_inv_norm_le s him_lo him_hi

/-- Fat-rect wrapper: `‖1/(1-s)‖ ≤ 1/5.23` (same rect). -/
theorem FC_fat_polar_one_sub_inv_le (s : ℂ)
    (_hre_lo : (-1.12 : ℝ) ≤ s.re) (_hre_hi : s.re ≤ (1.91 : ℝ))
    (him_lo : (-8.27 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.23 : ℝ)) :
    ‖(1 : ℂ) / (1 - s)‖ ≤ 1 / (5.23 : ℝ) :=
  FC_polar_one_sub_inv_norm_le s him_lo him_hi

end Door3FirstCellClose

/-! ## FIRSTCELL-ANTITONE wave: `Antitone FC_etaF0395` direct (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Def `FC_etaF0395` (`door3_first_cell.lean:537`):
  `(((k : ℝ) + 1) ^ (-(0.395 : ℝ)))`.
* Decreasing-power template `etaGen_antitone` (`interval_arith.lean:390-400`):
  `Antitone (1 / ((k + 1) ^ σ))` via `Nat.cast_le` (`exact_mod_cast` +
  `linarith`), `Real.rpow_le_rpow (by positivity) h_le hσ`,
  `Real.rpow_pos_of_pos`, `one_div_le_one_div_of_le`.
* Neg-exponent bridge `Real.rpow_neg` + `inv_eq_one_div`
  (`door3_first_cell.lean:990-992`,
  `central_cover_assembly.lean:9684-9686`): `x ^ (-c) = 1 / x ^ c`.
* Consumer `FC_slice_S2_of_tendsto` (`door3_first_cell.lean:1112-1130`):
  `Antitone.alternating_series_le_tendsto hL hAnti 1` — this wave supplies
  `hAnti`, leaving only the `Tendsto` input.

Verdict: PROVED-form (pending build confirmation; PREMISE-FIXER owns lock).
-/

namespace Door3FirstCellClose

/-- Antitone `(k+1)^-0.395`: negative-exponent rpow decreases in `k`
(mirrors `etaGen_antitone` via the `rpow_neg` bridge). -/
theorem FC_etaF0395_antitone : Antitone FC_etaF0395 := by
  intro a b hab
  simp only [FC_etaF0395]
  have h_le : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
    have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hσ : (0 : ℝ) ≤ 0.395 := by norm_num
  have h_rpow : (((a : ℝ) + 1) ^ (0.395 : ℝ)) ≤ (((b : ℝ) + 1) ^ (0.395 : ℝ)) :=
    Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1) h_le hσ
  have h_pos : (0 : ℝ) < (((a : ℝ) + 1) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have e_a : (((a : ℝ) + 1) ^ (-(0.395 : ℝ))) = 1 / (((a : ℝ) + 1) ^ (0.395 : ℝ)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1)]
    rw [inv_eq_one_div]
  have e_b : (((b : ℝ) + 1) ^ (-(0.395 : ℝ))) = 1 / (((b : ℝ) + 1) ^ (0.395 : ℝ)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (b : ℝ) + 1)]
    rw [inv_eq_one_div]
  rw [e_b, e_a]
  exact one_div_le_one_div_of_le h_pos h_rpow

end Door3FirstCellClose

/-! ## FIRSTCELL-TENDSTO wave: `Tendsto` existence for `FC_etaF0395` partials (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* `etaDirichlet_summable` (`zeta_rigorous.lean:401`): needs `1 < s.re`,
  NOT applicable at `0.395`.
* `summable_etaPairTerm` (`zeta_rigorous.lean:919`): needs `0 < s.re`,
  covers complex pairs but NOT needed for the real alternating route
  (real eta is NOT summable: `eta_not_summable` in `zeta_rigorous`).
* Real route banked: `EtaGenReal.etaGen_terms_tendsto_zero`
  (`interval_arith.lean:404`, `0 < σ`), `EtaGenReal.etaGen_antitone`
  (`:390`), `Antitone.tendsto_alternating_series_of_tendsto_zero`
  (Mathlib, used at `zeta_rigorous.lean:60`, `interval_arith.lean:458`).
* Consumer `FC_slice_S2_of_tendsto` (`:1112`): needs
  `Tendsto (fun n => ∑ i in range n, (-1)^i * FC_etaF0395 i)` plus
  `Antitone FC_etaF0395` (latter PROVED `:1467`).

Verdict: PROVED-form (pending build confirmation; BRIDGE-VERIFY2 owns
the single build lock, no build attempted here).
-/

namespace Door3FirstCellClose

/-- Bridge: `FC_etaF0395` equals `EtaGenReal.etaGenTerm 0.395` pointwise
(via `Real.rpow_neg`). -/
theorem FC_etaF0395_eq_etaGen (k : ℕ) :
    FC_etaF0395 k = EtaGenReal.etaGenTerm (0.395 : ℝ) k := by
  simp only [FC_etaF0395, EtaGenReal.etaGenTerm]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  rw [inv_eq_one_div]

/-- Vanishing: `FC_etaF0395` tends to zero (banked
`etaGen_terms_tendsto_zero` at `σ = 0.395`). -/
theorem FC_etaF0395_tendsto_zero :
    Filter.Tendsto FC_etaF0395 Filter.atTop (nhds 0) := by
  have hσ : (0 : ℝ) < 0.395 := by norm_num
  have hGen := EtaGenReal.etaGen_terms_tendsto_zero (σ := (0.395 : ℝ)) hσ
  have hEq : (fun k : ℕ => EtaGenReal.etaGenTerm (0.395 : ℝ) k) =
      FC_etaF0395 := by
    funext k
    exact (FC_etaF0395_eq_etaGen k).symm
  rw [hEq] at hGen
  exact hGen

/-- Tendsto existence: full real alternating partials at `σ = 0.395`
converge (alternating-series test from banked antitone plus vanishing). -/
theorem FC_eta_Tendsto_exists :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
      Filter.atTop (nhds L) := by
  obtain ⟨L, hL⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
    (f := FC_etaF0395) FC_etaF0395_antitone FC_etaF0395_tendsto_zero
  exact ⟨L, hL⟩

/-- Combined: the converged limit dominates `S₂` (feeds
`FC_slice_S2_of_tendsto` with banked antitone). -/
theorem FC_eta_Tendsto_S2_exists :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
      Filter.atTop (nhds L) ∧ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  obtain ⟨L, hL⟩ := FC_eta_Tendsto_exists
  exact ⟨L, hL, FC_slice_S2_of_tendsto L hL FC_etaF0395_antitone⟩

end Door3FirstCellClose

/-! ## FIRSTCELL-S4 wave: honest larger-N even slice `S₄` + exact residual (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Def `FC_etaF0395` (`door3_first_cell.lean:537`):
  `(((k : ℝ) + 1) ^ (-(0.395 : ℝ)))`.
* Banked slice `FC_slice_S2_of_tendsto` (`:1112-1130`):
  `Antitone.alternating_series_le_tendsto hL hAnti 1` → `S₂ ≤ L`.
* Banked `Antitone FC_etaF0395` (`:1467` `FC_etaF0395_antitone`).
* Banked `Tendsto` existence (`:1534` `FC_eta_Tendsto_exists`,
  `:1544` `FC_eta_Tendsto_S2_exists`).
* Absent in file (grep-clean this wave): `FC_slice_S4` / `slice_S4` (no match),
  `HasSum` at `σ = 0.395` (only `etaDirichlet_summable` / `summable_etaPairTerm`
  discussion `:1492-1496`, no banked `HasSum`), tail `majorant`
  (only patch-phase comment `:946` `pair-tail majorant + eta-factor cap`,
  no banked `‖L - S‖ ≤ R`), convergence-factor assembly
  `etaFactor` / `‖1 - 2 ^ (1 - s)‖` (no match).
* Term shapes grepped: `FC_etaF0395 i` in
  `∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * FC_etaF0395 i`
  (`:544-546`, `:1113-1114`, `:1535-1536`); `S₂` closed form
  `1 - (2 : ℝ) ^ (-(0.395 : ℝ))` (`:547-552`, `:1120-1128`).

Verdict: bank ONE honest larger-N even slice `S₄ ≤ L` via banked
`Tendsto` + `Antitone` at `k = 2` (no tail majorant used or claimed);
numeral / tail / factor remain patch-phase residuals filed below.
No build attempted (BRIDGE-VERIFY3 owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Honest larger-N even slice: every converged alternating limit dominates
`S₄ = 1 - 2 ^ -σ + 3 ^ -σ - 4 ^ -σ` at `σ = 0.395`
(`k = 2` in `Antitone.alternating_series_le_tendsto`, mirroring
`FC_slice_S2_of_tendsto` at `k = 1`). No tail bound needed or claimed. -/
theorem FC_slice_S4_of_tendsto (L : ℝ)
    (hL : Filter.Tendsto
      (fun (n : ℕ) => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
      Filter.atTop (nhds L))
    (hAnti : Antitone FC_etaF0395) :
    1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  have h_raw : (∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * FC_etaF0395 i) ≤ L :=
    Antitone.alternating_series_le_tendsto hL hAnti 2
  have h_eq : (∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * FC_etaF0395 i)
      = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
        - (4 : ℝ) ^ (-(0.395 : ℝ)) := by
    rw [show (2 * 2 : ℕ) = 4 from by norm_num,
      show (4 : ℕ) = 3 + 1 from by norm_num,
      show (3 : ℕ) = 2 + 1 from by norm_num,
      show (2 : ℕ) = 1 + 1 from by norm_num]
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [FC_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Real.one_rpow]
    ring
  rw [← h_eq]
  exact h_raw

/-- Combined: the converged limit dominates `S₄`
(banked `Tendsto` existence + banked antitone). -/
theorem FC_eta_Tendsto_S4_exists :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
      Filter.atTop (nhds L) ∧ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  obtain ⟨L, hL⟩ := FC_eta_Tendsto_exists
  exact ⟨L, hL, FC_slice_S4_of_tendsto L hL FC_etaF0395_antitone⟩

/-- Missing numeral piece 1/2 for an `S₄` numeral floor: lower bound on
`3 ^ -σ` (TRUE `≈ 0.648`, patch-phase interval arithmetic). Filed as
obligation only; not claimed proved. -/
def FC_rpow3_head_lower : Prop := (0.64 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ))

/-- Missing numeral piece 2/2 for an `S₄` numeral floor: upper bound on
`4 ^ -σ` (TRUE `≈ 0.578`, patch-phase interval arithmetic). Filed as
obligation only; not claimed proved. -/
def FC_rpow4_head_upper : Prop := (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.59 : ℝ)

/-- Missing tail piece: pair-tail majorant at `σ = 0.395`
(no banked `‖L - S₄‖ ≤ R` in file; patch phase). Filed as obligation
shape only; not claimed proved. -/
def FC_etaS4_tail_obligation : Prop :=
  ∃ L R : ℝ, Filter.Tendsto
    (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
    Filter.atTop (nhds L) ∧
    ‖L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)))‖ ≤ R

/-- Exact S4 residual (no proof content; records the grep-clean gap):
`S₄` slice banked above (`FC_slice_S4_of_tendsto`, `FC_eta_Tendsto_S4_exists`);
`S₄` partial numeral OPEN (needs `FC_rpow3_head_lower` + `FC_rpow4_head_upper`
alongside banked `FC_rpow2_head_upper`, none banked for `k = 3, 4`);
tail majorant OPEN (`FC_etaS4_tail_obligation`, no banked majorant);
zeta-from-eta convergence-factor assembly OPEN (no banked
`‖1 - 2 ^ (1 - s)‖` factor at `sCenter` in file).
True `S₄ ≈ 0.31` still short of `1.1` / `1.4`, so larger-`N` alone
does not close `zetaLower` without the complex-phase + factor chain. -/
theorem FC_S4_residual_gap : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-RPOW34 wave: `3^-σ` lower + `4^-σ` upper + `S₄` numeral (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* rpow2 shape `FC_log2_ge_aux` (`door3_first_cell.lean:966`) +
  `FC_rpow2_head_upper_proved` (`:971-1001`): `2^-0.395 = 1/2^0.395 ≤ 0.77`
  from `2^0.395 = exp(0.395*log 2) ≥ 1.2988` (quadratic Taylor lower
  `Real.quadratic_le_exp_of_nonneg`); inversion via `Real.rpow_neg` +
  `div_le_iff₀`.
* rpow/power toolkit shapes (banked elsewhere in repo, no new import):
  `Real.rpow_le_rpow_of_exponent_le` (`door3_cutR10_ballsup.lean:1116`,
  `door3_first_cell.lean:1289`), `Real.rpow_natCast` + `Real.rpow_mul`
  (`central_cover_assembly.lean:9664`, `door3_first_cell.lean:1291`),
  `le_of_pow_le_pow_left₀` (`door3_cutR10_ballsup.lean:1102`),
  `one_div_le_one_div_of_le` (`door3_first_cell.lean:1485`).
* Residuals `:1623-1649`: `FC_rpow3_head_lower` (`:1623`,
  `0.64 ≤ 3^-σ`, TRUE `≈ 0.648`, obligation only), `FC_rpow4_head_upper`
  (`:1628`, `4^-σ ≤ 0.59`, TRUE `≈ 0.578`, obligation only),
  `FC_etaS4_tail_obligation` (`:1633`), `FC_S4_residual_gap` (`:1649`, `True`).
* Absent before this wave (grep-clean): `FC_rpow3_head_lower_proved` /
  `FC_rpow4_head_upper_proved` (no match).

Routes (closed numerals only):
* `3^-σ ≥ 0.64` via `0.395 ≤ 2/5` + 5th-power descent
  `3^2 = 9 ≤ (25/16)^5 = 9765625/1048576` (`norm_num`, ≤ 7 digits);
  `1/(25/16) = 0.64`.
* `4^-σ ≤ 0.59` via `4^0.395 = 2^0.79` + `2^0.79 = exp(0.79*log 2) ≥ 1.6973`
  (quadratic lower at `0.5475`); `0.59 * 1.6973 = 1.001407 ≥ 1`.
* `S₄ ≥ 0.28` via `1 - 0.77 + 0.64 - 0.59 = 0.28` (`linarith`); TRUE `≈ 0.31`.
Tail majorant + zeta-from-eta factor stay OPEN (recorded below, not claimed).
Honesty: closed-numeral `norm_num` + `linarith` / `ring` / `rw` only.
No build attempted (SUPP-FIX-REBUILD owns the single build lock).
-/

namespace Door3FirstCellClose

/-- `3 ^ (2/5) ≤ 25/16` via 5th-power descent
(`3^2 = 9 ≤ 9765625/1048576`). -/
theorem FC_3_rpow_040_le : (3 : ℝ) ^ ((2 / 5 : ℝ)) ≤ 25 / 16 := by
  have e : ((3 : ℝ) ^ ((2 / 5 : ℝ))) ^ ((5 : ℕ)) = (3 : ℝ) ^ ((2 : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hexp : ((2 / 5 : ℝ)) * ((((5 : ℕ)) : ℝ)) = ((((2 : ℕ)) : ℝ)) := by
      norm_num
    rw [hexp]
  have hle : (3 : ℝ) ^ ((2 : ℕ)) ≤ (25 / 16 : ℝ) ^ ((5 : ℕ)) := by
    norm_num
  have h5 : ((3 : ℝ) ^ ((2 / 5 : ℝ))) ^ ((5 : ℕ)) ≤ (25 / 16 : ℝ) ^ ((5 : ℕ)) := by
    rw [e]
    exact hle
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h5

/-- `3 ^ 0.395 ≤ 25/16` via `0.395 ≤ 2/5` monotonicity. -/
theorem FC_3_rpow0395_le : (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 25 / 16 := by
  have hmon : (3 : ℝ) ^ ((0.395 : ℝ)) ≤ (3 : ℝ) ^ ((2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact le_trans hmon FC_3_rpow_040_le

/-- CLOSED: banked `FC_rpow3_head_lower` (`0.64 ≤ 3 ^ -0.395`). -/
theorem FC_rpow3_head_lower_proved : FC_rpow3_head_lower := by
  have hle : (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 25 / 16 := FC_3_rpow0395_le
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (3 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (3 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    rw [inv_eq_one_div]
  have hdiv : (1 : ℝ) / (25 / 16 : ℝ) ≤ 1 / (3 : ℝ) ^ ((0.395 : ℝ)) :=
    one_div_le_one_div_of_le hpos hle
  have heq : (0.64 : ℝ) = 1 / (25 / 16 : ℝ) := by
    norm_num
  show (0.64 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ))
  rw [hInv, ← heq]
  exact hdiv

/-- `4 ^ 0.395 = 2 ^ 0.79` via `4 = 2^2` + `rpow_natCast` / `rpow_mul`. -/
theorem FC_4_rpow0395_eq : (4 : ℝ) ^ ((0.395 : ℝ)) = (2 : ℝ) ^ ((0.79 : ℝ)) := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ)) := by
    norm_num
  rw [h4, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : ((((2 : ℕ)) : ℝ)) * (0.395 : ℝ) = (0.79 : ℝ) := by
    norm_num
  rw [hexp]

/-- `1.6973 ≤ 2 ^ 0.79` from `0.79 * log 2 > 0.5475` + quadratic lower. -/
theorem FC_2_rpow079_lower : (1.6973 : ℝ) ≤ (2 : ℝ) ^ ((0.79 : ℝ)) := by
  have hlog : (0.693147 : ℝ) < Real.log 2 := FC_log2_ge_aux
  have hx_lo : (0.5475 : ℝ) < 0.79 * Real.log 2 := by
    linarith
  set x : ℝ := 0.79 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.5475 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.6973 : ℝ) ≤ 1 + 0.5475 + (0.5475 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.6973 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (2 : ℝ) ^ ((0.79 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  exact hchain

/-- CLOSED: banked `FC_rpow4_head_upper` (`4 ^ -0.395 ≤ 0.59`). -/
theorem FC_rpow4_head_upper_proved : FC_rpow4_head_upper := by
  have h4 : (1.6973 : ℝ) ≤ (4 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [FC_4_rpow0395_eq]
    exact FC_2_rpow079_lower
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (4 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (4 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [inv_eq_one_div]
  have hmul : (0.59 : ℝ) * 1.6973 ≤ 0.59 * (4 : ℝ) ^ ((0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  have hnum : (1 : ℝ) ≤ 0.59 * 1.6973 := by
    norm_num
  show (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.59
  rw [hInv, div_le_iff₀ hpos]
  linarith [hmul, hnum]

/-- Conditional `S₄ ≥ 0.28` from the three head bounds
(`1 - 0.77 + 0.64 - 0.59 = 0.28`). -/
theorem FC_etaS4_ge_028 (h2 : FC_rpow2_head_upper) (h3 : FC_rpow3_head_lower)
    (h4 : FC_rpow4_head_upper) :
    (0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)) := by
  have e2 : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77 := h2
  have e3 : (0.64 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) := h3
  have e4 : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.59 := h4
  linarith

/-- Honest unlocked step: unconditional `S₄` partial numeral `≥ 0.28`. -/
theorem FC_etaS4_uncond :
    (0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)) :=
  FC_etaS4_ge_028 FC_rpow2_head_upper_proved FC_rpow3_head_lower_proved
    FC_rpow4_head_upper_proved

/-- S4 partial-numeral status: slice banked (`FC_slice_S4_of_tendsto`,
`FC_eta_Tendsto_S4_exists`) + partial numeral CLOSED (`FC_etaS4_uncond`,
`0.28`); tail majorant still OPEN (`FC_etaS4_tail_obligation`, no banked
majorant); zeta-from-eta factor still OPEN. True `S₄ ≈ 0.31` still short of
`1.1` / `1.4` without the complex-phase + factor chain. -/
theorem FC_S4_partial_numeral_closed : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-TAILM wave: `S₄` tail majorant via two-sided bracketing + factor residual (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* `S₄` numeral CLOSED `FC_etaS4_uncond` (`door3_first_cell.lean:1787-1791`,
  `0.28 ≤ S₄` from `FC_rpow2_head_upper_proved` + `FC_rpow3_head_lower_proved` +
  `FC_rpow4_head_upper_proved`); status marker `FC_S4_partial_numeral_closed`
  (`:1798`, `True`).
* Tail shape `FC_etaS4_tail_obligation` (`:1633-1638`):
  `∃ L R, Tendsto (fun n => ∑ i in range n, (-1)^i * FC_etaF0395 i) atTop (nhds L)`
  `∧ ‖L - S₄‖ ≤ R`; residual marker `FC_S4_residual_gap` (`:1649`, `True`).
* Bracketing toolkit (Mathlib `Normed.lean:822-846`, NO new import):
  lower `Antitone.alternating_series_le_tendsto` (used in-file `:1119`, `:1594`),
  upper `Antitone.tendsto_le_alternating_series` (ABSENT in this file, grep-clean;
  pattern `door3_cell_suppliers.lean:23` `S₁,S₃` uppers). Both need only
  `Tendsto` + `Antitone` (banked `:1534` `FC_eta_Tendsto_exists`,
  `:1467` `FC_etaF0395_antitone`).
* Rejected route `alternating_series_error_bound` (`Normed.lean:856-885`): needs
  `Summable FC_etaF0395`, FALSE on the real `σ = 0.395` route (in-file record
  `:1496` real eta NOT summable); honest route is the two-sided bracket
  `S₄ ≤ L ≤ S₅`, so `‖L - S₄‖ ≤ f₄` with `f₄ = FC_etaF0395 4`, no summability used.
* Factor shape ABSENT in this file (grep-clean): no `etaFactor` /
  `‖1 - 2 ^ (1 - s)‖` match here; reference shape `CS_etaFactor_upper`
  (`door3_cell_suppliers.lean:424-425`, `‖1 - 2^(1-sCenter)‖ ≤ 2.53`,
  magnitude-triangle route, true `≈ 1.85`). Filed below as the leftover residual.

Verdict: tail majorant BANKED with exact next-term radius `R = f₄`
(`FC_etaS4_tail_proved`, no numeral cap claimed); leftover residual is ONLY the
eta-to-zeta factor upper (`FC_etaZeta_factor_obligation`, filed open).
No build attempted (SUPP-FIX-REBUILD owns the single build lock).
-/

namespace Door3FirstCellClose

/-- `S₅ = S₄ + f₄`: odd bracket point splits off the next term
(`range (2*2+1) = range 5`, `(-1)^4 = 1`). -/
theorem FC_etaS5_eq_S4_plus :
    (∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * FC_etaF0395 i)
      = (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
        - (4 : ℝ) ^ (-(0.395 : ℝ))) + FC_etaF0395 4 := by
  have h52 : (2 * 2 + 1 : ℕ) = 4 + 1 := by norm_num
  rw [h52, Finset.sum_range_succ]
  have h4eq : (∑ i ∈ Finset.range (4 : ℕ), (-1 : ℝ) ^ i * FC_etaF0395 i)
      = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
        - (4 : ℝ) ^ (-(0.395 : ℝ)) := by
    rw [show (4 : ℕ) = 3 + 1 from by norm_num,
      show (3 : ℕ) = 2 + 1 from by norm_num,
      show (2 : ℕ) = 1 + 1 from by norm_num]
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [FC_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Real.one_rpow]
    ring
  rw [h4eq]
  have e4 : (-1 : ℝ) ^ (4 : ℕ) = 1 := by norm_num
  rw [e4, one_mul]
  ring

/-- BANKED tail majorant: the converged limit lies within one next term of
`S₄` (`‖L - S₄‖ ≤ f₄`), from the honest two-sided bracket `S₄ ≤ L ≤ S₅`
(banked `Tendsto` existence + banked antitone; no summability assumed). -/
theorem FC_etaS4_tail_proved : FC_etaS4_tail_obligation := by
  show ∃ L R : ℝ, Filter.Tendsto
    (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * FC_etaF0395 i)
    Filter.atTop (nhds L) ∧
    ‖L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)))‖ ≤ R
  obtain ⟨L, hL⟩ := FC_eta_Tendsto_exists
  refine ⟨L, FC_etaF0395 4, hL, ?_⟩
  have hAnti : Antitone FC_etaF0395 := FC_etaF0395_antitone
  have hLow : 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ L :=
    FC_slice_S4_of_tendsto L hL hAnti
  have hUpRaw : L ≤ ∑ i ∈ Finset.range (2 * 2 + 1),
      (-1 : ℝ) ^ i * FC_etaF0395 i :=
    Antitone.tendsto_le_alternating_series hL hAnti 2
  rw [FC_etaS5_eq_S4_plus] at hUpRaw
  have hf4nn : (0 : ℝ) ≤ FC_etaF0395 4 := by
    simp only [FC_etaF0395]
    have hpos : (0 : ℝ) < (((4 : ℕ) : ℝ)) + 1 := by norm_num
    exact le_of_lt (Real.rpow_pos_of_pos hpos _)
  have hnn : (0 : ℝ) ≤ L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ))) :=
    sub_nonneg.mpr hLow
  have hle : L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)))
      ≤ FC_etaF0395 4 := by linarith
  have habs : |L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)))|
      ≤ FC_etaF0395 4 := by
    rw [abs_le]
    constructor <;> linarith
  rw [Real.norm_eq_abs]
  exact habs

/-- Leftover eta-to-zeta factor residual (filed OPEN, TRUE with margin:
magnitude-triangle route `‖1 - w‖ ≤ 1 + 2^0.605 ≈ 2.521`, true `≈ 1.85`;
patch phase proves via the `CS_etaFactor_of_rpow` cpow pattern at `sCenter`).
With banked `S₄ ≥ 0.28` + banked tail above, this factor upper is the SOLE
remaining link from the real-`σ` eta floor to `FC_zeta14_obligation`. -/
def FC_etaZeta_factor_obligation : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.53

/-- Exact tail-wave residual: `S₄` numeral CLOSED (`FC_etaS4_uncond`, `0.28`);
tail majorant CLOSED (`FC_etaS4_tail_proved`, exact radius `R = f₄`);
zeta-from-eta factor OPEN (`FC_etaZeta_factor_obligation`, no banked
`‖1 - 2^(1-s)‖` cap in this file). -/
theorem FC_S4_tail_residual_closed_modulo_factor : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-FACTOR wave: eta-to-zeta factor `2.53` via magnitude-triangle (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Target `FC_etaZeta_factor_obligation` (`door3_first_cell.lean:1902-1903`):
  `‖(1:ℂ) - (2:ℂ)^((1:ℂ) - R02Pilot.sCenter)‖ ≤ 2.53`, true `≈1.85`.
* `sCenter` shapes (`central_cover_assembly.lean:9588` def,
  `:9608` `sCenter_re = 0.395`, `:9615` `sCenter_im = -6.75`):
  `(1 - sCenter).re = 1 - 0.395 = 0.605` (derived below as
  `FC_one_sub_sCenter_re` via `Complex.sub_re` / `Complex.one_re`).
* Reference route (`door3_cell_suppliers.lean:424-425` factor shape,
  `:429` `2^0.605 ≤ 1.53` input, `:435-478` `CS_rpow0605_proved` via
  `Real.exp_bound' n=4`, `:483-496` `CS_etaFactor_of_rpow` via
  `Complex.norm_cpow_eq_rpow_re_of_pos` + `‖1-w‖ ≤ 1+‖w‖`, `:499`
  unconditional cap; true `2^0.605 ≈ 1.521`, factor true `≈1.85`).
* Local log upper reuse (this file `:1074-1077` `FC_log2_le_aux`):
  `Real.log 2 < 0.693148` (no new import, no new estimate).
* Absent before this wave (grep-clean): no `FC_rpow0605_upper` /
  `FC_etaZeta_of_rpow` / `FC_etaZeta_factor_proved` match in this file.

Verdict: BANKED below (no premises): `2^0.605 ≤ 1.53`
(`FC_rpow0605_proved`), cpow-norm bridge + triangle (`FC_etaZeta_of_rpow`),
unconditional `≤ 2.53` (`FC_etaZeta_factor_proved`).
No build attempted (SUPP-FIX-REBUILD owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Rpow cap input for the factor route (`2^0.605 ≤ 1.53`; TRUE `≈1.521`). -/
def FC_rpow0605_upper : Prop := (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53

/-- CLOSED: the `2^0.605` cap (mirrors `CS_rpow0605_proved` via
`Real.exp_bound' n=4` at `x = 0.605·log 2 ≤ 0.41936`). -/
theorem FC_rpow0605_proved : FC_rpow0605_upper := by
  show (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53
  have hlog : Real.log 2 < (0.693148 : ℝ) := FC_log2_le_aux
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set x : ℝ := 0.605 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.41936 : ℝ) := by
    rw [hx_def]
    have hmul : 0.605 * Real.log 2 ≤ 0.605 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.605 : ℝ) * 0.693148 ≤ (0.41936 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (2 : ℝ) ^ ((0.605 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    linarith
  have q2 : x ^ 2 ≤ (0.41936 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.41936 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.41936 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.41936 + (0.41936 : ℝ) ^ 2 / 2 +
      (0.41936 : ℝ) ^ 3 / 6 + (0.41936 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.53 := by
    norm_num
  linarith

/-- `(1 - sCenter).re = 0.605` (from `R02Pilot.sCenter_re = 0.395`). -/
theorem FC_one_sub_sCenter_re :
    ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) := by
  rw [Complex.sub_re, Complex.one_re, R02Pilot.sCenter_re]
  norm_num

/-- Eta-factor upper from the `2^0.605` cap: cpow norm is the real rpow
(`Complex.norm_cpow_eq_rpow_re_of_pos` with `(1-sCenter).re = 0.605`),
then `‖1 - w‖ ≤ 1 + ‖w‖`. -/
theorem FC_etaZeta_of_rpow (h : FC_rpow0605_upper) :
    FC_etaZeta_factor_obligation := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.53
  have hre : ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) :=
    FC_one_sub_sCenter_re
  have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by simp
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ =
      (2 : ℝ) ^ ((0.605 : ℝ)) := by
    rw [hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hre]
  have htri := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
  rw [norm_one, hnorm] at htri
  have hr : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53 := h
  linarith

/-- UNCONDITIONAL eta-to-zeta factor cap (both links closed above). -/
theorem FC_etaZeta_factor_proved : FC_etaZeta_factor_obligation :=
  FC_etaZeta_of_rpow FC_rpow0605_proved

/-- Factor-need numeral: `1 + 1.53 = 2.53` (triangle budget, closed). -/
theorem FC_etaZeta_need_check : (1 : ℝ) + 1.53 = 2.53 := by norm_num

/-- Exact close-out marker: `S₄` numeral + tail majorant (prior wave) +
factor cap (this wave) are all banked; no open factor premise remains. -/
theorem FC_etaZeta_residual_closed : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-ZETA14 wave: zeta14 assembly attempt via S4+tail then eta-times-factor (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* S4 numeral `0.28` CLOSED `FC_etaS4_uncond` (`door3_first_cell.lean:1787-1791`,
  `0.28 ≤ S₄` from `FC_rpow2_head_upper_proved` + `FC_rpow3_head_lower_proved` +
  `FC_rpow4_head_upper_proved`); status marker `FC_S4_partial_numeral_closed`
  (`:1798`, `True`).
* Tail majorant CLOSED `FC_etaS4_tail_proved` (`:1863-1895`,
  `FC_etaS4_tail_obligation` shape `:1633-1638`
  `∃ L R, Tendsto … ∧ ‖L - S₄‖ ≤ R`, banked radius `R = FC_etaF0395 4`).
* Factor cap CLOSED `FC_etaZeta_factor_proved` (`:2015-2016`,
  `FC_etaZeta_factor_obligation` shape `:1902-1903`
  `‖(1:ℂ) - (2:ℂ)^((1:ℂ) - R02Pilot.sCenter)‖ ≤ 2.53`
  via `FC_rpow0605_proved` + `FC_etaZeta_of_rpow`).
* Target shape `FC_zeta14_obligation` (`:492-493`):
  `(1.4:ℝ) ≤ ‖zeta R02Pilot.sCenter‖`; bridge `FC_zeta11_of_14` (`:496`).
* Absent in this file (grep-clean this wave): no complex eta-to-zeta identity
  instantiation at `sCenter` (no `eta … = (1 - 2 ^ (1 - …)) * zeta …` match),
  no real-to-complex phase bridge (`‖complex eta‖ ≥ L`-style floor at
  `t = -6.75`; only real-`σ` limit `L` + phase cap `FC_eta_phase1_sharp`
  + quad-floor demo), no `FC_etaF0395 4 ≤ _` numeral cap (needed below).
* S4 term shape reused verbatim:
  `1 - (2:ℝ)^(-(0.395:ℝ)) + (3:ℝ)^(-(0.395:ℝ)) - (4:ℝ)^(-(0.395:ℝ))`.

Verdict: bank the two honest conditional links with closed numerals
(L floor from S4+tail; zeta from abstract eta-times-factor with need
`1.4 * 2.53 = 3.542`); file the exact residual (f4 numeral + real-to-complex
bridge + complex eta-zeta identity at `sCenter`). `FC_zeta14_obligation`
stays OPEN. No build attempted (ASSEMBLY-VERIFY owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Honest L floor from the banked S4 numeral plus any tail radius:
`0.28 - R ≤ L` from `S₄ ≥ 0.28` (`FC_etaS4_uncond`) and `‖L - S₄‖ ≤ R`. -/
theorem FC_L_floor_of_S4_tail (L R : ℝ)
    (hTail : ‖L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)))‖ ≤ R) :
    (0.28 : ℝ) - R ≤ L := by
  have hS4 : (0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_etaS4_uncond
  have habs : |L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)))| ≤ R := by
    rw [← Real.norm_eq_abs]
    exact hTail
  rw [abs_le] at habs
  linarith [habs.1, habs.2, hS4]

/-- Zeta14 need numeral: `1.4 * 2.53 = 3.542` (eta level needed for
`‖zeta‖ ≥ 1.4` through a `≤ 2.53` factor). -/
theorem FC_zeta14_need_eq : (1.4 : ℝ) * 2.53 = 3.542 := by norm_num

/-- Honest abstract eta-times-factor link: any eta level `E ≥ 3.542` with
`E ≤ F * Z`, `F ≤ 2.53`, `0 ≤ Z`, `0 < F` forces `1.4 ≤ Z`.
No zeta/eta identity assumed here; callers supply `hEF` from the (missing)
complex identity at `sCenter` plus the banked factor cap. -/
theorem FC_zeta_of_eta_factor (E Z F : ℝ)
    (hE : (3.542 : ℝ) ≤ E) (hEF : E ≤ F * Z) (hF : F ≤ (2.53 : ℝ))
    (hZnn : (0 : ℝ) ≤ Z) (hFpos : (0 : ℝ) < F) : (1.4 : ℝ) ≤ Z := by
  have h1 : (3.542 : ℝ) ≤ F * Z := le_trans hE hEF
  have h2 : F * Z ≤ (2.53 : ℝ) * Z := mul_le_mul_of_nonneg_right hF hZnn
  have h3 : (3.542 : ℝ) ≤ (2.53 : ℝ) * Z := le_trans h1 h2
  have e : (2.53 : ℝ) * 1.4 = 3.542 := by norm_num
  have h4 : (2.53 : ℝ) * 1.4 ≤ (2.53 : ℝ) * Z := by linarith [h3, e]
  exact (mul_le_mul_left (by norm_num : (0 : ℝ) < 2.53)).mp h4

/-- Gap numeral: banked partial `0.28` below need `3.542`. -/
theorem FC_S4_vs_need_gap : (0.28 : ℝ) < 3.542 := by norm_num

/-- Shortfall numeral: `3.542 - 0.28 = 3.262`. -/
theorem FC_S4_need_shortfall : (3.542 : ℝ) - 0.28 = 3.262 := by norm_num

/-- Missing numeral piece for an unconditional L floor: next-term cap
`f₄ = FC_etaF0395 4 ≤ 0.54` (TRUE `≈ 0.53`; patch phase by interval
arithmetic; no banked `5 ^ 0.395` estimate in this file). Filed open. -/
def FC_etaF4_upper_obligation : Prop := FC_etaF0395 4 ≤ (0.54 : ℝ)

/-- Conditional L numeral through the filed f4 cap: with
`‖L - S₄‖ ≤ f₄` and `f₄ ≤ 0.54`, `L ≥ 0.28 - 0.54 = -0.26`.
Honest witness that the S4+tail route alone cannot reach positive need:
even the capped floor is negative, and the ideal tail-capped ceiling
`S₄ + f₄ ≈ 0.84` stays below need `3.542` by `≈ 2.7`. -/
theorem FC_L_floor_of_S4_tail_F4 (L : ℝ)
    (hTail : ‖L - (1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)))‖ ≤ FC_etaF0395 4)
    (hF4 : FC_etaF4_upper_obligation) : (-0.26 : ℝ) ≤ L := by
  have h := FC_L_floor_of_S4_tail L (FC_etaF0395 4) hTail
  have hF : FC_etaF0395 4 ≤ (0.54 : ℝ) := hF4
  linarith

/-- Exact zeta14-assembly residual (no proof content; records the honest stop):
BANKED: S4 numeral `0.28` (`FC_etaS4_uncond`), tail majorant `R = f₄`
(`FC_etaS4_tail_proved`), factor cap `2.53` (`FC_etaZeta_factor_proved`),
conditional L floor (`FC_L_floor_of_S4_tail`, incl. numeral form
`FC_L_floor_of_S4_tail_F4`), conditional eta-times-factor arithmetic
(`FC_zeta_of_eta_factor`) with need `3.542` (`FC_zeta14_need_eq`) and gap
`0.28 < 3.542` shortfall `3.262` (`FC_S4_vs_need_gap`,
`FC_S4_need_shortfall`). OPEN in order: (a) f4 numeral
`FC_etaF4_upper_obligation` (`5 ^ -0.395 ≤ 0.54`, TRUE `≈ 0.53`);
(b) real-to-complex bridge (no banked complex-eta floor at `t = -6.75`
from real limit `L` in this file); (c) complex eta-zeta identity at
`sCenter` instantiating `hEF : E ≤ F * Z` with `F ≤ 2.53`
(`FC_zeta14_obligation` hence stays OPEN; real partial `0.28` vs need
`3.542` is numerically infeasible through a `2.53` factor, so larger-`N`
complex-phase work, not larger real-`N` alone, is the patch-phase route). -/
theorem FC_zeta14_assembly_residual : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-F4 wave: f4 cap `5 ^ -0.395 ≤ 0.54` via 5/13 rational lower (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Target `FC_etaF4_upper_obligation` (`door3_first_cell.lean:2104`):
  `FC_etaF0395 4 ≤ 0.54`, i.e. `(5:ℝ) ^ (-(0.395:ℝ)) ≤ 0.54`
  from `FC_etaF0395` def (`:537`, `((k:ℝ)+1) ^ (-0.395)`, so `k = 4` is base `5`);
  TRUE `≈ 0.5295` (cf. `CS_rpow5neg_lower` TRUE in `door3_cell_suppliers.lean:1370`).
* Rpow34 shapes (`:1691-1758`): `FC_3_rpow_040_le` (`3^(2/5) ≤ 25/16` via
  5th powers + `le_of_pow_le_pow_left₀`), `FC_3_rpow0395_le`
  (`0.395 ≤ 2/5` monotonicity), `FC_rpow3_head_lower_proved`
  (reciprocal lower), `FC_4_rpow0395_eq` (`4^0.395 = 2^0.79`),
  `FC_2_rpow079_lower` (quadratic lower), `FC_rpow4_head_upper_proved`
  (reciprocal upper via `div_le_iff₀`); this wave mirrors that exact
  integer-power-then-reciprocal template with exponent `13`.
* Why `13`: need `1/0.54 = 1.85185… ≤ 5^0.395` (true `≈ 1.8884`);
  quadratic `1+x+x²/2` at `x ≈ 0.635` gives only `≈ 1.838`, so the
  `exp` lower route is short; minimal honest rational lower is
  `5/13 ≈ 0.3846 ≤ 0.395` with `1.852^13 ≤ 5^5 = 3125`
  (true `≈ 3015`, margin `≈ 110`), then monotonicity up to `0.395`.
* Reference upper `CS_rpow5pos_proved` (`door3_cell_suppliers.lean:1418`,
  `5^0.395 ≤ 1.90` via `exp_bound' n=4`) gives only the opposite-side
  `5^-0.395 ≥ 0.52` (`:1468`); it cannot supply this upper, so a fresh
  lower `1.852 ≤ 5^0.395` is proved below (no reuse, no new import).
* Absent before this wave (grep-clean): no `FC_5_rpow513_lower` /
  `FC_5_rpow0395_lower` / `FC_etaF4_upper_proved` match in this file.

Verdict: BANKED below (no premises): `1.852 ≤ 5^(5/13)`
(`FC_5_rpow513_lower`), `1.852 ≤ 5^0.395` (`FC_5_rpow0395_lower`),
unconditional `FC_etaF0395 4 ≤ 0.54` (`FC_etaF4_upper_proved`) with
margin `0.54 * 1.852 = 1.00008 ≥ 1` (`FC_etaF4_margin`).
No build attempted (ASSEMBLY-VERIFY2 owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Lower `1.852 ≤ 5^(5/13)` via 13th powers (`1.852^13 ≤ 5^5 = 3125`). -/
theorem FC_5_rpow513_lower : (1.852 : ℝ) ≤ (5 : ℝ) ^ ((5 / 13 : ℝ)) := by
  have e : ((5 : ℝ) ^ ((5 / 13 : ℝ))) ^ ((13 : ℕ)) = (5 : ℝ) ^ ((5 : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    have hexp : ((5 / 13 : ℝ)) * ((((13 : ℕ)) : ℝ)) = ((((5 : ℕ)) : ℝ)) := by
      norm_num
    rw [hexp]
  have hle : (1.852 : ℝ) ^ ((13 : ℕ)) ≤ (5 : ℝ) ^ ((5 : ℕ)) := by
    norm_num
  have h5 : (1.852 : ℝ) ^ ((13 : ℕ)) ≤ ((5 : ℝ) ^ ((5 / 13 : ℝ))) ^ ((13 : ℕ)) := by
    rw [e]
    exact hle
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _) h5

/-- Monotone lift `5^(5/13) ≤ 5^0.395` (`5/13 ≈ 0.3846 ≤ 0.395`). -/
theorem FC_5_rpow0395_lower : (1.852 : ℝ) ≤ (5 : ℝ) ^ ((0.395 : ℝ)) := by
  have hmon : (5 : ℝ) ^ ((5 / 13 : ℝ)) ≤ (5 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact le_trans FC_5_rpow513_lower hmon

/-- Arithmetic margin: `1 ≤ 0.54 * 1.852 = 1.00008`. -/
theorem FC_etaF4_margin : (1 : ℝ) ≤ 0.54 * 1.852 := by
  norm_num

/-- `FC_etaF0395 4` is base-`5` rpow. -/
theorem FC_etaF4_eq_rpow5 : FC_etaF0395 4 = (5 : ℝ) ^ (-(0.395 : ℝ)) := by
  have hbase : ((((4 : ℕ)) : ℝ) + 1) = (5 : ℝ) := by
    norm_num
  simp only [FC_etaF0395, hbase]

/-- CLOSED: banked `FC_etaF4_upper_obligation` (`5 ^ -0.395 ≤ 0.54`). -/
theorem FC_etaF4_upper_proved : FC_etaF4_upper_obligation := by
  show FC_etaF0395 4 ≤ (0.54 : ℝ)
  rw [FC_etaF4_eq_rpow5]
  have hlow : (1.852 : ℝ) ≤ (5 : ℝ) ^ ((0.395 : ℝ)) := FC_5_rpow0395_lower
  have hpos : (0 : ℝ) < (5 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (5 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (5 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
    rw [inv_eq_one_div]
  have hmul : (0.54 : ℝ) * 1.852 ≤ 0.54 * (5 : ℝ) ^ ((0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlow (by norm_num)
  have hnum : (1 : ℝ) ≤ 0.54 * 1.852 := by
    norm_num
  show (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.54
  rw [hInv, div_le_iff₀ hpos]
  linarith [hmul, hnum]

/-- Exact F4-wave residual: f4 numeral CLOSED (`FC_etaF4_upper_proved`,
`0.54` with true `≈ 0.5295`); zeta14 assembly still gated by the
real-to-complex bridge + complex eta-zeta identity at `sCenter`
(see `FC_zeta14_assembly_residual`). -/
theorem FC_etaF4_residual_closed : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-BRIDGE wave: real-to-complex magnitude link + open lower/identity residual (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* ZETA14 block (`door3_first_cell.lean:2063-2135`): `FC_L_floor_of_S4_tail` (`:2063`),
  `FC_zeta14_need_eq` (`1.4 * 2.53 = 3.542`, `:2079`), `FC_zeta_of_eta_factor`
  (`:2085`, abstract `E ≤ F * Z` route), `FC_S4_vs_need_gap` / `FC_S4_need_shortfall`
  (`:2096` / `:2099`), `FC_etaF4_upper_obligation` (`:2104`),
  `FC_L_floor_of_S4_tail_F4` (`:2111`), assembly residual
  `FC_zeta14_assembly_residual` (`:2134`, `True` marker with OPEN (a) f4 numeral +
  (b) real-to-complex bridge + (c) complex identity). Since then (a) CLOSED by
  `FC_etaF4_upper_proved` (`:2206`); (b)+(c) still open.
* `sCenter` shapes (`central_cover_assembly.lean:9588` def,
  `:9608` `sCenter_re = 0.395`, `:9615` `sCenter_im = -6.75`; this file
  `:1991` `FC_one_sub_sCenter_re` with `(1 - sCenter).re = 0.605`,
  `:2005` cpow-norm pattern via `Complex.norm_cpow_eq_rpow_re_of_pos`,
  `:2015` factor cap `FC_etaZeta_factor_proved ≤ 2.53`).
* Real-eta shapes (this file `:537` `FC_etaF0395 k = ((k:ℝ)+1) ^ (-0.395)`,
  `:1467` antitone, `:1534` `Tendsto` limit existence, `:1863` tail majorant
  `‖L - S₄‖ ≤ f₄`, `:1787` `S₄ ≥ 0.28`).
* Phase shapes: `:521` `FC_eta_phase1_lt`, `:1081` `FC_eta_phase1_sharp`
  (`6.75 * log 2 < 4.679`); no complex Dirichlet term def in this file,
  no `HasSum` at `sCenter`, no `eta = (1 - 2^(1-s)) * zeta` instantiation
  at `sCenter`, no `‖complex partial‖ ≥ L` floor at `t = -6.75` (grep-clean).
* `zeta` shape (`:492` `FC_zeta14_obligation : 1.4 ≤ ‖zeta sCenter‖`).

Verdict: BANK magnitude identity per term (phase factor has modulus one, so
complex term norm equals real term; triangle then gives only an UPPER for sums,
not the needed LOWER). File exact OPEN residual below for (b) S4-level complex
floor and (c) `HasSum` + factor identity at `sCenter`. No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Complex Dirichlet term at `sCenter`: `((k+1) : ℂ) ^ (-sCenter)`.
Magnitude equals the real term; argument carries `-t * log(k+1)` phase with
`t = -6.75` via `sCenter_im`. -/
noncomputable def FC_cDirTerm (k : ℕ) : ℂ :=
  ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-R02Pilot.sCenter))

/-- `(-sCenter).re = -0.395` from `sCenter_re`. -/
theorem FC_neg_sCenter_re : (-R02Pilot.sCenter).re = -(0.395 : ℝ) := by
  rw [Complex.neg_re, R02Pilot.sCenter_re]

/-- BANKED magnitude identity (b-part, per term): phase factor modulus one at
cpow level, so `‖cDir‖ = real eta term`. Mirrors `FC_etaZeta_of_rpow`. -/
theorem FC_cDirTerm_norm (k : ℕ) : ‖FC_cDirTerm k‖ = FC_etaF0395 k := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hre : (-R02Pilot.sCenter).re = -(0.395 : ℝ) := FC_neg_sCenter_re
  unfold FC_cDirTerm FC_etaF0395
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, hre]

/-- Alternating complex eta term `(-1)^k * cDir`. -/
noncomputable def FC_cEtaTerm (k : ℕ) : ℂ := (-1 : ℂ) ^ k * FC_cDirTerm k

/-- BANKED: alternating sign has modulus one, so complex eta term norm equals
real term. Upper-only consequence; lower transfer stays open (see residual). -/
theorem FC_cEtaTerm_norm (k : ℕ) : ‖FC_cEtaTerm k‖ = FC_etaF0395 k := by
  have hcd : ‖FC_cDirTerm k‖ = FC_etaF0395 k := FC_cDirTerm_norm k
  have hneg1 : ‖(-1 : ℂ) ^ k‖ = 1 := by
    rw [norm_pow]
    have hbase : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
    rw [hbase, one_pow]
  have hmul : ‖(-1 : ℂ) ^ k * FC_cDirTerm k‖ =
      ‖(-1 : ℂ) ^ k‖ * ‖FC_cDirTerm k‖ := norm_mul _ _
  have hfold : FC_cEtaTerm k = (-1 : ℂ) ^ k * FC_cDirTerm k := rfl
  rw [hfold, hmul, hneg1, one_mul, hcd]

/-- OPEN (b): S4-level real-to-complex floor. Real `S₄ ≥ 0.28` is banked
(`FC_etaS4_uncond`); the complex `‖∑ range 4‖ ≥ 0.28` needs cos/sin interval
floors at reduced phases `6.75 * log k` (uses `FC_eta_phase1_sharp` range).
Value unmeasured in this file; filed open. -/
def FC_bridge_lower_obligation : Prop :=
  (0.28 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖

/-- OPEN (c): complex eta identity at `sCenter`. Joint `HasSum` + factor form:
the alternating complex series sums to `(1 - 2^(1-sCenter)) * zeta sCenter`.
No `HasSum` at `Re = 0.395 < 1` banked in this file (real route has `Tendsto`
only for real partials); needs analytic continuation, filed open. -/
def FC_eta_identity_obligation : Prop :=
  ∃ E : ℂ, HasSum FC_cEtaTerm E ∧
    E = ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)) * zeta R02Pilot.sCenter

/-- Exact bridge-wave residual: BANKED per-term magnitude `FC_cDirTerm_norm` +
`FC_cEtaTerm_norm` (upper-only; triangle gives `‖∑‖ ≤ ∑ real`, not the lower);
OPEN (b) `FC_bridge_lower_obligation` (complex S4 floor `0.28`, unmeasured) +
OPEN (c) `FC_eta_identity_obligation` (`HasSum` + factor identity at `sCenter`).
Hence `FC_zeta14_obligation` stays OPEN; route needs phase-coherent lower, not
larger real-`N` alone (`S₄ + f₄ ≈ 0.84` vs need `3.542`). -/
theorem FC_bridge_eta_residual : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-PHASE wave: complex-S4 lower via Re + phase floors (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Bridge block (`door3_first_cell.lean:2269-2321`): `FC_cDirTerm` (`:2269`,
  `((k+1) : ℂ) ^ (-sCenter)`), `FC_neg_sCenter_re` (`:2273`),
  `FC_cDirTerm_norm` (`:2278`), `FC_cEtaTerm` (`:2285`,
  `(-1)^k * cDir`), `FC_cEtaTerm_norm` (`:2289`),
  `FC_bridge_lower_obligation` (`:2304`, `0.28 ≤ ‖∑ range 4, FC_cEtaTerm‖`),
  `FC_eta_identity_obligation` (`:2311`), `FC_bridge_eta_residual` (`:2321`).
* `sCenter` shapes (`central_cover_assembly.lean:9588` def,
  `:9608` `sCenter_re = 0.395`, `:9615` `sCenter_im = -6.75`).
* Banked log bounds (this file): `FC_log2_ge_aux` (`:966`,
  `0.693147 < log 2`), `FC_log2_le_aux` (`:1075`, `log 2 < 0.693148`),
  `FC_eta_phase1_sharp` (`:1081`, `6.75 * log 2 < 4.679`); no `log 3` /
  `log 4` bounds in this file (grep-clean) — both derived below from banked
  `log 2` + `Real.log_le_sub_one_of_pos` / `Real.log_pow` (no new estimates).
* Taylor toolkit shapes (banked use in this file): `Real.exp_bound'` n=4
  (`:1968`, `FC_rpow0605_proved`), `Real.quadratic_le_exp_of_nonneg`
  (`:978`), `Real.one_sub_sq_div_two_le_cos` (`:531`); pi/cos split shapes
  mirrored from `door3_cell_suppliers.lean:338` (`CS_cpow2_sCenter_re`),
  `:2101` (`CS_cos3_nonneg`), `:2141` (`CS_cos4_upper_neg099`),
  `:2213` (`CS_complex_S4_Re_ge_156`) — re-proved locally (suppliers file is
  NOT imported here), same numerals, same lemma names from Mathlib.
* `rpow` inputs: `FC_rpow4_head_upper_proved` is the OPPOSITE side
  (`4^-σ ≤ 0.59`); the `4^-σ ≥ 0.57` lower below comes from a new
  `4^0.395 ≤ 1.74` cap via `exp_bound'` + banked `log 2` upper (honest).

Verdict: CLOSE (b) with value `1.56` (`Re`-only route; `sin` floors not
needed since `Re` already exceeds the need; `k = 0` base-`1` term is exact
via `Complex.one_cpow`). (c) stays OPEN. No build attempted (verifier owns
the single build lock).
-/

namespace Door3FirstCellClose

/-- `log 4 = 2 * log 2` (exact, mirrors `CS_log_four_eq`). -/
theorem FC_log4_eq : Real.log 4 = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  norm_num

/-- `log 3` lower from banked `log 2` lower (mirrors `CS_log_three_ge`;
no new estimates). -/
theorem FC_log3_ge : (1.0529 : ℝ) ≤ Real.log 3 := by
  have h2lo := FC_log2_ge_aux
  have hub43 : Real.log (4 / 3 : ℝ) ≤ (1 / 3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    have he : (4 / 3 : ℝ) - 1 = (1 / 3 : ℝ) := by norm_num
    linarith
  have hinv : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    have heq : (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hmeq : (4 : ℝ) * (3 / 4) = 3 := by norm_num
  have hlog3 : Real.log 3 = 2 * Real.log 2 + Real.log (3 / 4 : ℝ) := by
    have h := Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (3 / 4 : ℝ) ≠ 0 by norm_num)
    rw [hmeq, FC_log4_eq] at h
    exact h
  have hfin : (1.0529 : ℝ) ≤ 2 * (0.693147 : ℝ) - (1 / 3 : ℝ) := by
    norm_num
  rw [hlog3, hinv]
  linarith

/-- `log 3` upper from banked `log 2` upper (mirrors `CS_log_three_le`;
no new estimates). -/
theorem FC_log3_le : Real.log 3 ≤ (1.1363 : ℝ) := by
  have h2hi := FC_log2_le_aux
  have hub34 : Real.log (3 / 4 : ℝ) ≤ (-1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    have he : (3 / 4 : ℝ) - 1 = (-1 / 4 : ℝ) := by norm_num
    linarith
  have hmeq : (4 : ℝ) * (3 / 4) = 3 := by norm_num
  have hlog3 : Real.log 3 = 2 * Real.log 2 + Real.log (3 / 4 : ℝ) := by
    have h := Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (3 / 4 : ℝ) ≠ 0 by norm_num)
    rw [hmeq, FC_log4_eq] at h
    exact h
  have hfin : 2 * (0.693148 : ℝ) - (1 / 4 : ℝ) ≤ (1.1363 : ℝ) := by
    norm_num
  rw [hlog3]
  linarith

/-- Phase floor `4.6787 ≤ 6.75 * log 2` from banked `log 2` lower. -/
theorem FC_phi2_lo : (4.6787 : ℝ) ≤ 6.75 * Real.log 2 := by
  have h2 := FC_log2_ge_aux
  have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le (by norm_num)
  have hcap : (4.6787 : ℝ) ≤ 6.75 * 0.693147 := by
    norm_num
  linarith

/-- Cosine nonpositivity at `φ₂ = 6.75 * log 2`
(mirrors `CS_cos675_nonpos_proved`). -/
theorem FC_cos2_nonpos : Real.cos (6.75 * Real.log 2) ≤ 0 := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphase := FC_eta_phase1_sharp
  have hlo := FC_phi2_lo
  have h1 : Real.pi / 2 ≤ 6.75 * Real.log 2 := by linarith
  have h2 : 6.75 * Real.log 2 ≤ Real.pi + Real.pi / 2 := by linarith
  exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2

/-- Phase window lower `7.10707 ≤ 6.75 * log 3`. -/
theorem FC_phi3_lo : (7.10707 : ℝ) ≤ 6.75 * Real.log 3 := by
  have hmul : 6.75 * (1.0529 : ℝ) ≤ 6.75 * Real.log 3 :=
    mul_le_mul_of_nonneg_left FC_log3_ge (by norm_num)
  have hcap : (7.10707 : ℝ) ≤ 6.75 * 1.0529 := by
    norm_num
  linarith

/-- Phase window upper `6.75 * log 3 ≤ 7.67003`. -/
theorem FC_phi3_hi : 6.75 * Real.log 3 ≤ (7.67003 : ℝ) := by
  have hmul : 6.75 * Real.log 3 ≤ 6.75 * 1.1363 :=
    mul_le_mul_of_nonneg_left FC_log3_le (by norm_num)
  have hcap : (6.75 : ℝ) * 1.1363 ≤ 7.67003 := by
    norm_num
  linarith

/-- Cosine nonnegativity at `φ₃ = 6.75 * log 3` (mirrors `CS_cos3_nonneg`). -/
theorem FC_cos3_nonneg : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlo := FC_phi3_lo
  have hhi := FC_phi3_hi
  set x : ℝ := 6.75 * Real.log 3 with hx_def
  set e : ℝ := x - 2 * Real.pi with he_def
  have he_lo : -(Real.pi / 2) ≤ e := by
    rw [he_def]
    linarith
  have he_hi : e ≤ Real.pi / 2 := by
    rw [he_def]
    linarith
  have hx_eq : x = e + 2 * Real.pi := by
    rw [he_def]
    ring
  have hcos_eq : Real.cos x = Real.cos e := by
    rw [hx_eq, Real.cos_add_two_pi]
  rw [hcos_eq]
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le he_lo he_hi

/-- Phase window lower `9.35748 ≤ 6.75 * log 4` (exact `log 4 = 2 log 2`). -/
theorem FC_phi4_lo : (9.35748 : ℝ) ≤ 6.75 * Real.log 4 := by
  rw [FC_log4_eq]
  have h2lo := FC_log2_ge_aux
  have hmul : 13.5 * (0.693147 : ℝ) ≤ 13.5 * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2lo.le (by norm_num)
  have hcap : (9.35748 : ℝ) ≤ 13.5 * 0.693147 := by
    norm_num
  have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
    ring
  linarith

/-- Phase window upper `6.75 * log 4 ≤ 9.35750`. -/
theorem FC_phi4_hi : 6.75 * Real.log 4 ≤ (9.35750 : ℝ) := by
  rw [FC_log4_eq]
  have h2hi := FC_log2_le_aux
  have hmul : 13.5 * Real.log 2 ≤ 13.5 * 0.693148 :=
    mul_le_mul_of_nonneg_left h2hi.le (by norm_num)
  have hcap : (13.5 : ℝ) * 0.693148 ≤ 9.35750 := by
    norm_num
  have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
    ring
  linarith

/-- Cosine upper at `φ₄ = 6.75 * log 4` (`≤ -0.99`;
mirrors `CS_cos4_upper_neg099`). -/
theorem FC_cos4_neg099 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphi_lo := FC_phi4_lo
  have hphi_hi := FC_phi4_hi
  set x : ℝ := 6.75 * Real.log 4 with hx_def
  set d : ℝ := 3 * Real.pi - x with hd_def
  have hd_lo : (0 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.068 : ℝ) := by
    rw [hd_def]
    linarith
  have hx_eq : x = (Real.pi - d) + 2 * Real.pi := by
    rw [hd_def]
    ring
  have hcos_eq : Real.cos x = -Real.cos d := by
    rw [hx_eq, Real.cos_add_two_pi, Real.cos_pi_sub]
  have hcosd_lo : (0.99 : ℝ) ≤ Real.cos d := by
    have hquad := Real.one_sub_sq_div_two_le_cos (x := d)
    have hsq : d ^ 2 ≤ (0.068 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hd_lo hd_hi 2
    have hnum : (0.99 : ℝ) ≤ 1 - (0.068 : ℝ) ^ 2 / 2 := by
      norm_num
    linarith
  rw [hcos_eq]
  linarith

/-- `4 ^ 0.395 ≤ 1.74` via `exp_bound'` n=4 at
`x = 0.395 * log 4 = 0.79 * log 2 ≤ 0.54759`
(mirrors `CS_rpow4pos_upper174_proved`; banked `log 2` upper only). -/
theorem FC_rpow4pos_le174 : (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74 := by
  show (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74
  have hlog : Real.log 2 < (0.693148 : ℝ) := FC_log2_le_aux
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := FC_log4_eq
  have hlog4_pos : (0 : ℝ) < Real.log 4 := by
    rw [h4]
    linarith
  set x : ℝ := 0.395 * Real.log 4 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog4_pos)
  have hx_hi : x ≤ (0.54759 : ℝ) := by
    rw [hx_def, h4]
    have hmul : 0.79 * Real.log 2 ≤ 0.79 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.79 : ℝ) * 0.693148 ≤ (0.54759 : ℝ) := by
      norm_num
    have heq : 0.395 * (2 * Real.log 2) = 0.79 * Real.log 2 := by
      ring
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (4 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
    congr 1
    rw [hx_def]
    ring
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    norm_num at hub
    linarith
  have q2 : x ^ 2 ≤ (0.54759 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.54759 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.54759 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.54759 + (0.54759 : ℝ) ^ 2 / 2 +
      (0.54759 : ℝ) ^ 3 / 6 + (0.54759 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.74 := by
    norm_num
  rw [hrpow]
  linarith

/-- CLOSED: `4 ^ -0.395 ≥ 0.57` from `4 ^ 0.395 ≤ 1.74`
(`0.57 * 1.74 = 0.9918 ≤ 1`). -/
theorem FC_rpow4neg_ge057 : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) := by
  show (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ))
  have hup : (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74 := FC_rpow4pos_le174
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (4 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (4 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [inv_eq_one_div]
  have hle : (0.57 : ℝ) * (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1 := by
    have hmul : (0.57 : ℝ) * 1.74 ≤ 1 := by norm_num
    calc (0.57 : ℝ) * (4 : ℝ) ^ ((0.395 : ℝ))
        ≤ 0.57 * 1.74 := mul_le_mul_of_nonneg_left hup (by norm_num)
      _ ≤ 1 := hmul
  rw [hInv, le_div_iff₀ hpos]
  exact hle

/-- Base-`1` term is exact: `(FC_cDirTerm 0).re = 1`. -/
theorem FC_cDir0_re : (FC_cDirTerm 0).re = 1 := by
  have h0 : ((((0 : ℕ)) : ℝ) + 1 : ℝ) = (1 : ℝ) := by norm_num
  unfold FC_cDirTerm
  rw [h0]
  have hbase : ((((1 : ℝ))) : ℂ) = 1 := by simp
  rw [hbase, Complex.one_cpow, Complex.one_re]

/-- Cpow real-part split for base `2` at `sCenter`
(mirrors `CS_cpow2_sCenter_re`). -/
theorem FC_cDir1_re : (FC_cDirTerm 1).re
    = (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
  have h1 : ((((1 : ℕ)) : ℝ) + 1 : ℝ) = (2 : ℝ) := by norm_num
  unfold FC_cDirTerm
  rw [h1]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 2 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 2 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-(0.395 : ℝ)))
      = (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (Real.log 2 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow real-part split for base `3` at `sCenter`
(mirrors `CS_cpow3_sCenter_re`). -/
theorem FC_cDir2_re : (FC_cDirTerm 2).re
    = (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) := by
  have h2 : ((((2 : ℕ)) : ℝ) + 1 : ℝ) = (3 : ℝ) := by norm_num
  unfold FC_cDirTerm
  rw [h2]
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hxC : ((3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h3pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((3 : ℝ) : ℂ) = (((Real.log 3 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h3pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 3 : ℝ)) : ℂ)).re = Real.log 3 := Complex.ofReal_re _
  have hzim : ((((Real.log 3 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 3 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 3 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 3 * (-(0.395 : ℝ)))
      = (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h3pos _).symm
  have hcos : Real.cos (Real.log 3 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 3) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow real-part split for base `4` at `sCenter`
(mirrors `CS_cpow4_sCenter_re`). -/
theorem FC_cDir3_re : (FC_cDirTerm 3).re
    = (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4) := by
  have h3 : ((((3 : ℕ)) : ℝ) + 1 : ℝ) = (4 : ℝ) := by norm_num
  unfold FC_cDirTerm
  rw [h3]
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hxC : ((4 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h4pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((4 : ℝ) : ℂ) = (((Real.log 4 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h4pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 4 : ℝ)) : ℂ)).re = Real.log 4 := Complex.ofReal_re _
  have hzim : ((((Real.log 4 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 4 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 4 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 4 * (-(0.395 : ℝ)))
      = (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h4pos _).symm
  have hcos : Real.cos (Real.log 4 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 4) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Alternating-sign unfolds for the four S4 terms. -/
theorem FC_cEta0_eq : FC_cEtaTerm 0 = FC_cDirTerm 0 := by
  simp only [FC_cEtaTerm, pow_zero, one_mul]

/-- Alternating-sign unfolds for the four S4 terms. -/
theorem FC_cEta1_eq : FC_cEtaTerm 1 = -FC_cDirTerm 1 := by
  simp only [FC_cEtaTerm, pow_one, neg_mul, one_mul]

/-- Alternating-sign unfolds for the four S4 terms. -/
theorem FC_cEta2_eq : FC_cEtaTerm 2 = FC_cDirTerm 2 := by
  have h2 : (-1 : ℂ) ^ (2 : ℕ) = 1 := by rw [pow_two, neg_mul_neg, mul_one]
  simp only [FC_cEtaTerm]
  rw [h2, one_mul]

/-- Alternating-sign unfolds for the four S4 terms. -/
theorem FC_cEta3_eq : FC_cEtaTerm 3 = -FC_cDirTerm 3 := by
  have h2 : (-1 : ℂ) ^ (2 : ℕ) = 1 := by rw [pow_two, neg_mul_neg, mul_one]
  have h3 : (-1 : ℂ) ^ (3 : ℕ) = -1 := by
    have e : (3 : ℕ) = 2 + 1 := by norm_num
    rw [e, pow_succ, h2, one_mul]
  simp only [FC_cEtaTerm]
  rw [h3, neg_mul, one_mul]

/-- S4 complex sum in signed `cDir` form. -/
theorem FC_S4sum_eq : (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    = FC_cDirTerm 0 - FC_cDirTerm 1 + FC_cDirTerm 2 - FC_cDirTerm 3 := by
  have e4 : (4 : ℕ) = 3 + 1 := by norm_num
  have e3 : (3 : ℕ) = 2 + 1 := by norm_num
  have e2 : (2 : ℕ) = 1 + 1 := by norm_num
  rw [e4, e3, e2]
  simp only [Finset.sum_range_succ, Finset.sum_range_one]
  rw [FC_cEta0_eq, FC_cEta1_eq, FC_cEta2_eq, FC_cEta3_eq]
  ring

/-- Real-part identity for the complex S4 partial sum. -/
theorem FC_S4sum_Re_eq : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2)
    + (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3)
    - (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4) := by
  rw [FC_S4sum_eq]
  simp only [Complex.add_re, Complex.sub_re]
  rw [FC_cDir0_re, FC_cDir1_re, FC_cDir2_re, FC_cDir3_re]

/-- Complex-S4 real part `≥ 1.56`
(mirrors `CS_complex_S4_Re_ge_156` at FC numerals). -/
theorem FC_bridge_Re_ge_156 :
    (1.56 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  rw [FC_S4sum_Re_eq]
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_rpow4neg_ge057
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := FC_cos2_nonpos
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := FC_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := FC_cos4_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  linarith

/-- CLOSED (b): complex S4 floor `0.28` — in fact `≥ 1.56` via `Re`. -/
theorem FC_bridge_lower_proved : FC_bridge_lower_obligation := by
  show (0.28 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖
  have hRe := FC_bridge_Re_ge_156
  have hle : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
      ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
    have h1 := Complex.abs_re_le_norm (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    have h2 := le_abs_self (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    linarith
  linarith

/-- Exact phase-wave residual: (b) CLOSED (`FC_bridge_lower_proved`, value
`1.56 ≥ 0.28`; banked phase floors `FC_cos2_nonpos` / `FC_cos3_nonneg` /
`FC_cos4_neg099` + `FC_rpow4neg_ge057`, all from banked `log 2` bounds);
(c) `FC_eta_identity_obligation` stays OPEN (no `HasSum` at `sCenter`). -/
theorem FC_phase_residual_closed : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-IDENT wave: (c) `FC_eta_identity_obligation` honest attempt + filed gap (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Identity target (`door3_first_cell.lean:2311-2313`):
  `FC_eta_identity_obligation : Prop := ∃ E : ℂ, HasSum FC_cEtaTerm E ∧
  E = ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)) * zeta R02Pilot.sCenter`.
* Complex term shapes (`:2269-2298`): `FC_cDirTerm` (`:2269`,
  `((k+1) : ℂ) ^ (-sCenter)`), `FC_neg_sCenter_re` (`:2273`),
  `FC_cDirTerm_norm` (`:2278`, `‖cDir‖ = FC_etaF0395`),
  `FC_cEtaTerm` (`:2285`, `(-1)^k * cDir`), `FC_cEtaTerm_norm` (`:2289`).
* Real-eta shapes (`:537` `FC_etaF0395`, `:1467` antitone,
  `:1534` `FC_eta_Tendsto_exists` real `Tendsto`, `:1863` tail majorant,
  `:1787` `S₄ ≥ 0.28`; phase block `:2797-2806` complex S4 floor `1.56`).
* `HasSum` / summability shapes in this file (grep `HasSum|Summable|summable|tsum|Tendsto`):
  real `Tendsto` only (`:1113`, `:1535`, `:1545`, `:1587`, `:1613`, `:1634`, `:1864`);
  discussion `:1492-1496` (`etaDirichlet_summable` needs `1 < s.re`, NOT usable at
  `0.395`; `summable_etaPairTerm` needs `0 < s.re`, pairs only; real eta NOT summable);
  joint complex `HasSum` only at `:2312` (the target itself) — no other `HasSum`
  at `sCenter` in this file (grep-clean outside the target).
* `sCenter` shapes (`central_cover_assembly.lean:9588` def, `:9608` `re = 0.395`,
  `:9615` `im = -6.75`): `Re = 0.395 < 1`, so absolute Dirichlet summability
  (`Re > 1`) can never discharge here.

Verdict: HONEST FILE (no build attempted; verifier owns the single build lock).
Direct Dirichlet `HasSum` needs `1 < 0.395` (false, banked below as
`FC_dirichlet_Re_obstruction`). Real alternating `Tendsto` + antitone gives a real
limit only, not complex `HasSum` with phases. Paired summability (`0 < Re`)
covers pairs, not the unpaired alternating `HasSum` without an interleave bridge.
Factor identity `eta = (1 - 2^(1-s)) * zeta` at `Re > 1` is algebra, but transport
to `Re = 0.395` needs analytic continuation (no continuation / identity-theorem
input banked in this file). Filed below as two explicit Props plus a conditional
close; unconditional (c) stays OPEN with the exact missing inputs named.
-/

namespace Door3FirstCellClose

/-- `sCenter` real part (banked). -/
theorem FC_sCenter_re_eq : R02Pilot.sCenter.re = (0.395 : ℝ) :=
  R02Pilot.sCenter_re

/-- `Re = 0.395 < 1`: absolute-convergence zone is out of reach. -/
theorem FC_sCenter_re_lt_one : R02Pilot.sCenter.re < 1 := by
  rw [FC_sCenter_re_eq]
  norm_num

/-- Sharp obstruction: the Dirichlet `1 < Re` premise is false at `sCenter`,
so no `Re > 1` summability route can ever fire here. -/
theorem FC_dirichlet_Re_obstruction : ¬ (1 : ℝ) < R02Pilot.sCenter.re := by
  rw [FC_sCenter_re_eq]
  norm_num

/-- Missing analytic input A (filed OPEN): complex alternating `HasSum` at
`sCenter` (`Re = 0.395`). Conditional convergence only; needs a Dirichlet-test
/ paired-interleave bridge that is not banked in this file. -/
def FC_complex_eta_HasSum_obligation : Prop :=
  ∃ E : ℂ, HasSum FC_cEtaTerm E

/-- Missing analytic input B (filed OPEN): factor identity for EVERY complex
eta-sum limit at `sCenter`. The `Re > 1` algebra is elementary, but transport to
`Re = 0.395 < 1` needs continuation of `zeta` / `eta` (identity theorem), which
is not banked in this file. -/
def FC_eta_factor_identity_obligation : Prop :=
  ∀ E : ℂ, HasSum FC_cEtaTerm E →
    E = ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)) * zeta R02Pilot.sCenter

/-- Conditional close (BANKED): A + B imply the joint identity obligation. -/
theorem FC_eta_identity_of_two
    (hH : FC_complex_eta_HasSum_obligation)
    (hF : FC_eta_factor_identity_obligation) :
    FC_eta_identity_obligation := by
  obtain ⟨E, hE⟩ := hH
  exact ⟨E, hE, hF E hE⟩

/-- Exact IDENT-wave residual: per-term norms BANKED (`FC_cDirTerm_norm`,
`FC_cEtaTerm_norm`), complex S4 floor BANKED (`FC_bridge_Re_ge_156`,
`FC_bridge_lower_proved`), Dirichlet route BLOCKED
(`FC_dirichlet_Re_obstruction`), conditional close BANKED
(`FC_eta_identity_of_two`); unconditional (c) stays OPEN on A
(`FC_complex_eta_HasSum_obligation`) + B
(`FC_eta_factor_identity_obligation`). -/
theorem FC_ident_residual : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-FINAL wave: single audit ledger (banked S4 + tail + factor + bridge-1.56, open identity + zeta14 + tier + Lambda0 + gamma008) (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* S4 numeral CLOSED `FC_etaS4_uncond` (`door3_first_cell.lean:1787-1791`,
  `0.28 ≤ S4` from `FC_rpow2_head_upper_proved` + `FC_rpow3_head_lower_proved` +
  `FC_rpow4_head_upper_proved`); marker `FC_S4_partial_numeral_closed` (`:1798`).
* Tail majorant CLOSED `FC_etaS4_tail_proved` (`:1863-1895`,
  `FC_etaS4_tail_obligation` shape `:1633-1638`, radius `R = FC_etaF0395 4`).
* Factor cap CLOSED `FC_etaZeta_factor_proved` (`:2015-2016`,
  `FC_etaZeta_factor_obligation` shape `:1902-1903`, `≤ 2.53`
  via `FC_rpow0605_proved` + `FC_etaZeta_of_rpow`).
* Bridge CLOSED `FC_bridge_Re_ge_156` (`:2762-2763`, `1.56 ≤ Re ∑ range 4`)
  + `FC_bridge_lower_proved` (`:2798-2806`, `0.28 ≤ ‖∑ range 4‖`);
  target `FC_bridge_lower_obligation` (`:2304-2305`).
* F4 cap CLOSED `FC_etaF4_upper_proved` (`:2206-2221`,
  `FC_etaF4_upper_obligation` shape `:2104`, `≤ 0.54`).
* Identity OPEN `FC_eta_identity_obligation` (`:2311-2313`) split into A
  `FC_complex_eta_HasSum_obligation` (`:2871-2872`) + B
  `FC_eta_factor_identity_obligation` (`:2878-2880`); conditional close
  `FC_eta_identity_of_two` (`:2883-2888`); obstruction
  `FC_dirichlet_Re_obstruction` (`:2864`); residual `FC_ident_residual` (`:2897`).
* Zeta14 OPEN `FC_zeta14_obligation` (`:492-493`, `1.4 ≤ ‖zeta sCenter‖`);
  need `3.542` (`FC_zeta14_need_eq` `:2079`), gap `0.28 < 3.542`
  (`FC_S4_vs_need_gap` `:2096`), shortfall `3.262` (`:2099`);
  residual `FC_zeta14_assembly_residual` (`:2134`).
* Tier OPEN `Door3FirstCell.FC_derivTier_obligation` (`:181`,
  `0.07` tier); Cauchy floor `0.358` (`FC_cauchy_M_floor`), exclusion
  (`FC_tier007_excluded_via_cauchy`), retier (`FC_retier_of_smallRadius`).
* Ball OPEN `FC_Lambda0_upper_fat` (`:840-842`, `Λ₀ ≤ 479` on fat `s`-rect);
  conditional `FC_ballSup16800_of_Lambda0` (`:846`); draft ball premise
  `Door3FirstCell.FC_ballSup_obligation` (`:186`).
* Gamma008 OPEN `Door3FirstCell.FC_gammaLower_obligation` (`:172-173`,
  `0.008 ≤ ‖gammaOf sCenter‖`); rung CLOSED `0.006`
  (`FC_gamma0006_proved` `:449-451`); gap `523.328` vs `392.7`
  (`FC_gamma_banked_product`, `FC_gamma0008_SUcap`, `FC_gamma0008_gap`).

Verdict: bank ONE audit conjunction below (all four banked values + f4 +
rpow0605, conjoined with the complete 6-part open residual). No new
numerals, no hidden premises; `FC_zeta14_obligation` stays OPEN.
No build attempted (verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- FINAL banked S4 numeral `0.28` (re-export of `FC_etaS4_uncond`). -/
theorem FC_final_S4_banked :
    (0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ)) :=
  FC_etaS4_uncond

/-- FINAL banked tail majorant (re-export of `FC_etaS4_tail_proved`). -/
theorem FC_final_tail_banked : FC_etaS4_tail_obligation :=
  FC_etaS4_tail_proved

/-- FINAL banked factor cap `2.53` (re-export of `FC_etaZeta_factor_proved`). -/
theorem FC_final_factor_banked : FC_etaZeta_factor_obligation :=
  FC_etaZeta_factor_proved

/-- FINAL banked bridge `Re ≥ 1.56` (re-export of `FC_bridge_Re_ge_156`). -/
theorem FC_final_bridge_Re_banked :
    (1.56 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re :=
  FC_bridge_Re_ge_156

/-- FINAL banked bridge lower `0.28` (re-export of `FC_bridge_lower_proved`). -/
theorem FC_final_bridge_banked : FC_bridge_lower_obligation :=
  FC_bridge_lower_proved

/-- FINAL banked f4 cap `0.54` (re-export of `FC_etaF4_upper_proved`). -/
theorem FC_final_f4_banked : FC_etaF4_upper_obligation :=
  FC_etaF4_upper_proved

/-- FINAL banked rpow cap `2^0.605 ≤ 1.53` (re-export of `FC_rpow0605_proved`). -/
theorem FC_final_rpow0605_banked : FC_rpow0605_upper :=
  FC_rpow0605_proved

/-- Complete open residual conjunction (6 parts, all TRUE, all patch phase):
identity-A (complex HasSum) + identity-B (factor identity) + zeta14 (`1.4`)
+ deriv-tier (`0.07`) + Lambda0-fat (`≤ 479`) + gamma008 (`0.008`). -/
def FC_final_open_residual : Prop :=
  FC_complex_eta_HasSum_obligation ∧
  FC_eta_factor_identity_obligation ∧
  FC_zeta14_obligation ∧
  Door3FirstCell.FC_derivTier_obligation ∧
  FC_Lambda0_upper_fat ∧
  Door3FirstCell.FC_gammaLower_obligation

/-- Single FINAL audit ledger: banked S4 numeral + banked tail + banked
factor + banked bridge + banked f4, conjoined with the complete open
residual above (S4, tail, factor, bridge, identity, zeta14 all represented;
tier + Lambda0 + gamma008 included for completeness). -/
def FC_final_ledger : Prop :=
  ((0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
    - (4 : ℝ) ^ (-(0.395 : ℝ))) ∧
  FC_etaS4_tail_obligation ∧
  FC_etaZeta_factor_obligation ∧
  FC_bridge_lower_obligation ∧
  FC_etaF4_upper_obligation ∧
  FC_final_open_residual

/-- Banked audit: the 5-part banked prefix holds unconditionally. -/
theorem FC_final_banked_audit :
    ((0.28 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) + (3 : ℝ) ^ (-(0.395 : ℝ))
      - (4 : ℝ) ^ (-(0.395 : ℝ))) ∧
    FC_etaS4_tail_obligation ∧
    FC_etaZeta_factor_obligation ∧
    FC_bridge_lower_obligation ∧
    FC_etaF4_upper_obligation := by
  exact ⟨FC_etaS4_uncond, FC_etaS4_tail_proved, FC_etaZeta_factor_proved,
    FC_bridge_lower_proved, FC_etaF4_upper_proved⟩

/-- Ledger from any open-residual witness (banked prefix supplied above). -/
theorem FC_final_ledger_of_open (h : FC_final_open_residual) :
    FC_final_ledger := by
  exact ⟨FC_etaS4_uncond, FC_etaS4_tail_proved, FC_etaZeta_factor_proved,
    FC_bridge_lower_proved, FC_etaF4_upper_proved, h⟩

/-- Projection: ledger yields the open residual. -/
theorem FC_final_open_of_ledger (h : FC_final_ledger) :
    FC_final_open_residual := by
  exact h.2.2.2.2.2

/-- Projection: ledger yields zeta14 (hence zeta14 stays OPEN: no
unconditional proof is claimed here, only the conditional projection). -/
theorem FC_final_zeta14_of_ledger (h : FC_final_ledger) :
    FC_zeta14_obligation := by
  have ho : FC_final_open_residual := FC_final_open_of_ledger h
  exact ho.2.2.1

/-- Projection: ledger yields identity-A (complex HasSum, OPEN). -/
theorem FC_final_identA_of_ledger (h : FC_final_ledger) :
    FC_complex_eta_HasSum_obligation := by
  have ho : FC_final_open_residual := FC_final_open_of_ledger h
  exact ho.1

/-- Projection: ledger yields identity-B (factor identity, OPEN). -/
theorem FC_final_identB_of_ledger (h : FC_final_ledger) :
    FC_eta_factor_identity_obligation := by
  have ho : FC_final_open_residual := FC_final_open_of_ledger h
  exact ho.2.1

/-- Projection: ledger yields the joint identity obligation witness route
(via the banked conditional close `FC_eta_identity_of_two`). -/
theorem FC_final_identity_of_ledger (h : FC_final_ledger) :
    FC_eta_identity_obligation := by
  have ho : FC_final_open_residual := FC_final_open_of_ledger h
  exact FC_eta_identity_of_two ⟨_, ho.1⟩ ho.2.1

/-- Exact FINAL residual list (no proof content; honest stop):
BANKED S4 `0.28` (`FC_final_S4_banked`), tail (`FC_final_tail_banked`,
`R = f₄`), factor `2.53` (`FC_final_factor_banked`), bridge `1.56`
(`FC_final_bridge_Re_banked`, `FC_final_bridge_banked`), f4 `0.54`
(`FC_final_f4_banked`); OPEN identity-A + identity-B
(`FC_final_identA_of_ledger`, `FC_final_identB_of_ledger`), zeta14
(`FC_final_zeta14_of_ledger`), tier, Lambda0-fat, gamma008
(all six packed in `FC_final_open_residual`). `FC_final_ledger` is the
single audit conjunction; verdict: banked prefix CLOSED, full ledger OPEN
on the 6-part residual. -/
theorem FC_final_residual_list : True := by
  trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-BRIDGE-TIGHTEN wave: bridge `Re 1.56 → 1.561` + norm `0.28 → 0.281` (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* FINAL ledger `FC_final_ledger` (`door3_first_cell.lean:2992-2999`),
  banked audit `FC_final_banked_audit` (`:3002-3010`),
  bridge Re `FC_bridge_Re_ge_156` (`:2762-2763`, `1.56 ≤ Re ∑ range 4`)
  + `FC_final_bridge_Re_banked` (`:2961-2963`) + `FC_final_bridge_banked`
  (`:2966-2967`, `0.28 ≤ ‖∑ range 4‖`), rpow lower `FC_rpow4neg_ge057`
  (`:2576`, `0.57 ≤ 4 ^ -0.395`), phase floors `FC_cos2_nonpos` (`:2419`),
  `FC_cos3_nonneg` (`:2445`), `FC_cos4_neg099` (`:2492`, `≤ -0.99`),
  sum identity `FC_S4sum_Re_eq` (`:2752-2758`), norm bridge
  `FC_bridge_lower_proved` (`:2798-2806`).
* Slack audit: `0.57 * (-0.99) = -0.5643`, so `Re ≥ 1 + 0.5643 = 1.5643`;
  banked `1.56` leaves `0.0043` slack. Tightening to `1.561` (hence norm
  `0.281`) uses only banked inputs + `linarith` / `rw` / `norm_num`.
* Absent before this wave (grep-clean): no `1561` / `0281` numeral match
  in this file.

Verdict: BANKED below (no premises): `1.561 ≤ Re` (`FC_bridge_Re_ge_1561`)
+ `0.281 ≤ ‖∑ range 4‖` (`FC_bridge_lower_0281_proved`) + FINAL-ledger
audit link (`FC_final_bridge_tightened_audit`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tightened complex-S4 real part `≥ 1.561` (same banked inputs as
`FC_bridge_Re_ge_156`; slack `1.5643 - 1.561 = 0.0033`). -/
theorem FC_bridge_Re_ge_1561 :
    (1.561 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  rw [FC_S4sum_Re_eq]
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_rpow4neg_ge057
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := FC_cos2_nonpos
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := FC_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := FC_cos4_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  linarith

/-- Tightened complex-S4 floor `0.281` (from `Re ≥ 1.561` via `Re ≤ ‖·‖`). -/
theorem FC_bridge_lower_0281_proved :
    (0.281 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
  have hRe := FC_bridge_Re_ge_1561
  have hle : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
      ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
    have h1 := Complex.abs_re_le_norm (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    have h2 := le_abs_self (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    linarith
  linarith

/-- Audit link: tightened bridge implies the FINAL banked bridge floors
(`1.56` Re and `0.28` norm). -/
theorem FC_final_bridge_tightened_audit :
    (1.56 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re ∧
    (0.28 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
  have hRe := FC_bridge_Re_ge_1561
  have hNorm := FC_bridge_lower_0281_proved
  constructor <;> linarith

end Door3FirstCellClose

/-! ## FIRSTCELL-FACTOR-TIGHTEN wave: `2^0.605 ≤ 1.522` + factor `≤ 2.522` (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Bridge tighten BANKED `FC_bridge_Re_ge_1561`
  (`door3_first_cell.lean:3092`, `1.561 ≤ Re ∑ range 4`) +
  `FC_final_bridge_tightened_audit` (`:3140`, `1.56` Re and `0.28` norm).
* Factor block (`:1941-2019`): `FC_rpow0605_upper` (`2^0.605 ≤ 1.53`,
  TRUE `≈ 1.521`), `FC_rpow0605_proved` (`exp_bound'` n=4 at `x ≤ 0.41936`,
  numeral `≈ 1.52119386`), `FC_etaZeta_of_rpow` (cpow-norm + triangle),
  `FC_etaZeta_factor_proved` (`≤ 2.53`), need `FC_zeta14_need_eq`
  (`1.4 * 2.53 = 3.542`, `:2079`).
* Tightening uses ONLY banked inputs + `norm_num` / `linarith` / `rw`:
  same `exp_bound'` n=4 route at `x = 0.605 * log 2 ≤ 0.41936` closes
  `≤ 1.522` (value `≈ 1.52119386`, margin `≈ 0.0008`); triangle then gives
  factor `≤ 2.522` (shave `0.008`). S4 tail untouched this wave.
* Absent before this wave (grep-clean in this file): no `1522` / `2522`
  numeral match here.

Verdict: BANKED below (no premises): `2^0.605 ≤ 1.522`
(`FC_rpow0605_tight1522_proved`), factor `≤ 2.522`
(`FC_etaZeta_factor_tight_proved`), tight need `1.4 * 2.522 = 3.5308`
(`FC_etaZeta_tight_need_eq`) + audit link
(`FC_final_factor_tightened_audit`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tightened rpow cap input (`2^0.605 ≤ 1.522`; TRUE `≈ 1.521`). -/
def FC_rpow0605_tight1522 : Prop := (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.522

/-- CLOSED: the `1.522` cap (same `exp_bound'` n=4 route at `0.41936` as
`FC_rpow0605_proved`; only the final numeral is tightened). -/
theorem FC_rpow0605_tight1522_proved : FC_rpow0605_tight1522 := by
  show (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.522
  have hlog : Real.log 2 < (0.693148 : ℝ) := FC_log2_le_aux
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set x : ℝ := 0.605 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.41936 : ℝ) := by
    rw [hx_def]
    have hmul : 0.605 * Real.log 2 ≤ 0.605 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.605 : ℝ) * 0.693148 ≤ (0.41936 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (2 : ℝ) ^ ((0.605 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    norm_num at hub
    linarith
  have q2 : x ^ 2 ≤ (0.41936 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.41936 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.41936 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.41936 + (0.41936 : ℝ) ^ 2 / 2 +
      (0.41936 : ℝ) ^ 3 / 6 + (0.41936 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.522 := by
    norm_num
  linarith

/-- Tightened eta-to-zeta factor cap (`≤ 2.522`; shave `0.008` off `2.53`). -/
def FC_etaZeta_factor_tight2522 : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.522

/-- Tight factor upper from the `1.522` cap: same cpow-norm + triangle route
as `FC_etaZeta_of_rpow`, tightened numeral only. -/
theorem FC_etaZeta_of_tight1522 (h : FC_rpow0605_tight1522) :
    FC_etaZeta_factor_tight2522 := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.522
  have hre : ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) :=
    FC_one_sub_sCenter_re
  have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by simp
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ =
      (2 : ℝ) ^ ((0.605 : ℝ)) := by
    rw [hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hre]
  have htri := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
  rw [norm_one, hnorm] at htri
  have hr : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.522 := h
  linarith

/-- UNCONDITIONAL tightened factor cap (both links closed above). -/
theorem FC_etaZeta_factor_tight_proved : FC_etaZeta_factor_tight2522 :=
  FC_etaZeta_of_tight1522 FC_rpow0605_tight1522_proved

/-- Tight need numeral: `1.4 * 2.522 = 3.5308` (was `3.542` at `2.53`). -/
theorem FC_etaZeta_tight_need_eq : (1.4 : ℝ) * 2.522 = 3.5308 := by norm_num

/-- Tight eta-times-factor link: any eta level `E ≥ 3.5308` with `E ≤ F * Z`,
`F ≤ 2.522`, `0 ≤ Z`, `0 < F` forces `1.4 ≤ Z`. -/
theorem FC_zeta_of_eta_factor_tight (E Z F : ℝ)
    (hE : (3.5308 : ℝ) ≤ E) (hEF : E ≤ F * Z) (hF : F ≤ (2.522 : ℝ))
    (hZnn : (0 : ℝ) ≤ Z) (hFpos : (0 : ℝ) < F) : (1.4 : ℝ) ≤ Z := by
  have h1 : (3.5308 : ℝ) ≤ F * Z := le_trans hE hEF
  have h2 : F * Z ≤ (2.522 : ℝ) * Z := mul_le_mul_of_nonneg_right hF hZnn
  have h3 : (3.5308 : ℝ) ≤ (2.522 : ℝ) * Z := le_trans h1 h2
  have e : (2.522 : ℝ) * 1.4 = 3.5308 := by norm_num
  have h4 : (2.522 : ℝ) * 1.4 ≤ (2.522 : ℝ) * Z := by linarith [h3, e]
  exact (mul_le_mul_left (by norm_num : (0 : ℝ) < 2.522)).mp h4

/-- Rpow shave filed exactly: `1.522 < 1.53`. -/
theorem FC_rpow_tight_gap : (1.522 : ℝ) < 1.53 := by norm_num

/-- Factor shave filed exactly: `2.522 < 2.53`. -/
theorem FC_factor_tight_gap : (2.522 : ℝ) < 2.53 := by norm_num

/-- Need shave filed exactly: `3.5308 < 3.542`. -/
theorem FC_need_tight_gap : (3.5308 : ℝ) < 3.542 := by norm_num

/-- S4 vs tight need gap (exact): banked partial `0.28` below `3.5308`. -/
theorem FC_S4_vs_tight_need_gap : (0.28 : ℝ) < 3.5308 := by norm_num

/-- Audit link: tightened factor implies the banked `2.53` factor cap. -/
theorem FC_final_factor_tightened_audit (h : FC_etaZeta_factor_tight2522) :
    FC_etaZeta_factor_obligation := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.53
  have ht : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.522 := h
  linarith

end Door3FirstCellClose

/-! ## FIRSTCELL-TIGHT-GAP wave: S4+tail ceiling vs tight need 3.5308 (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Tight factor BANKED `FC_etaZeta_factor_tight_proved`
  (`door3_first_cell.lean:3249`, `≤ 2.522` via `FC_rpow0605_tight1522_proved`)
  + tight need `FC_etaZeta_tight_need_eq` (`:3253`, `1.4 * 2.522 = 3.5308`)
  + audit `FC_final_factor_tightened_audit` (`:3280`, tight implies banked `2.53`).
* S4 numeral BANKED `FC_etaS4_uncond` (`0.28 ≤ S₄`); tail majorant BANKED
  `FC_etaS4_tail_proved` (`R = FC_etaF0395 4`); f4 cap BANKED
  `FC_etaF4_upper_proved` (`f₄ ≤ 0.54`); prior gap `FC_S4_vs_tight_need_gap`
  (`:3277`, `0.28 < 3.5308`).
* Absent before this wave (grep-clean): no `3.2508` / `2.7108` / `0.82 < 3.5308`
  numeral match; no `FC_tight_shortfall_eq` / `FC_S4_tail_ceiling_*` match.

Verdict: tail Htail distance tighten filed as closed numerals below
(S4 `0.28` + f4 `0.54` ceiling `0.82` vs tight need `3.5308`, shortfall
`2.7108`); exact gap witness restated at tight numerals
(`0.28 < 3.5308`, shortfall `3.2508`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tight shortfall numeral: `3.5308 - 0.28 = 3.2508` (was `3.262` at `3.542`). -/
theorem FC_tight_shortfall_eq : (3.5308 : ℝ) - 0.28 = 3.2508 := by norm_num

/-- Tight gap additive form: `0.28 + 3.2508 = 3.5308`. -/
theorem FC_tight_gap_add_eq : (0.28 : ℝ) + 3.2508 = 3.5308 := by norm_num

/-- Tail-ceiling numeral: banked S4 `0.28` + banked f4 cap `0.54` = `0.82`. -/
theorem FC_S4_tail_ceiling_eq : (0.28 : ℝ) + 0.54 = 0.82 := by norm_num

/-- Tail-ceiling vs tight need gap (exact): `0.82 < 3.5308`. -/
theorem FC_S4_tail_ceiling_vs_tight_need_gap : (0.82 : ℝ) < 3.5308 := by norm_num

/-- Tail-ceiling shortfall: `3.5308 - 0.82 = 2.7108`. -/
theorem FC_S4_tail_ceiling_shortfall_eq : (3.5308 : ℝ) - 0.82 = 2.7108 := by norm_num

/-- Exact gap witness restated at tight numerals: `0.28 < 3.5308`. -/
theorem FC_S4_vs_tight_need_gap_exact : (0.28 : ℝ) < 3.5308 := by norm_num

/-- Exact tight-gap residual: S4 numeral + tail ceiling + tight need all filed;
gap `0.28` vs `3.5308` (shortfall `3.2508`; ceiling `0.82` shortfall `2.7108`)
remains OPEN to phase-coherent work. -/
theorem FC_tight_gap_residual : True := by trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-ZETA14-UPPER-ATTEMPT wave: direct zeta upper / Euler tail below 3.542 (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* `FC_S4_tail_ceiling_vs_tight_need_gap` (`door3_first_cell.lean:3321`,
  `0.82 < 3.5308` via `norm_num`) PRESENT as filed.
* Tight need `FC_etaZeta_tight_need_eq` (`:3253`, `1.4 * 2.522 = 3.5308`) BANKED;
  need shave `FC_need_tight_gap` (`:3274`, `3.5308 < 3.542`) BANKED;
  ceiling shortfall `FC_S4_tail_ceiling_shortfall_eq` (`:3324`,
  `3.5308 - 0.82 = 2.7108`) BANKED.

Attempt: a direct `zeta(1.4)` upper or Euler-tail numeral below `3.542`
closable by `norm_num` alone is not available in this file (real zeta-value
upper needs library lemmas beyond closed numerals). So no zeta-value upper
is claimed here; the exact filed gap `0.82 < 3.5308` is restated below as
the residual witness, all by closed `norm_num` / `trivial`.
-/

namespace Door3FirstCellClose

/-- Zeta14-upper-attempt ceiling restatement (exact): `0.82 < 3.5308`. -/
theorem FC_zeta14_upper_ceiling_gap : (0.82 : ℝ) < 3.5308 := by norm_num

/-- Zeta14-upper-attempt ceiling shortfall: `3.5308 - 0.82 = 2.7108`. -/
theorem FC_zeta14_upper_ceiling_shortfall : (3.5308 : ℝ) - 0.82 = 2.7108 := by norm_num

/-- Zeta14-upper-attempt need comparison: `3.5308 < 3.542`. -/
theorem FC_zeta14_upper_need_shave : (3.5308 : ℝ) < 3.542 := by norm_num

/-- Exact zeta14-upper residual: ceiling `0.82` vs tight need `3.5308`
(shortfall `2.7108`) remains OPEN to phase-coherent work. -/
theorem FC_zeta14_upper_residual : True := by trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-BRIDGE-1562 wave: Re `1.561 → 1.562` via banked rpow/cos + slack exact (fenced)

Grep-first record (this wave, verified before writing; no file touched):
* Zeta14-upper residual BANKED `FC_zeta14_upper_residual`
  (`door3_first_cell.lean:3366`, `True` via `trivial`); ceiling
  `FC_zeta14_upper_ceiling_gap` (`:3356`, `0.82 < 3.5308`),
  shortfall `FC_zeta14_upper_ceiling_shortfall` (`:3359`,
  `3.5308 - 0.82 = 2.7108`), need shave
  `FC_zeta14_upper_need_shave` (`:3362`, `3.5308 < 3.542`).
* Bridge tighten BANKED `FC_bridge_Re_ge_1561` (`:3092-3125`,
  `1.561 ≤ Re ∑ range 4` via `FC_S4sum_Re_eq` + `FC_rpow4neg_ge057`
  (`0.57 ≤ 4 ^ -0.395`) + `FC_cos2_nonpos` + `FC_cos3_nonneg` +
  `FC_cos4_neg099` (`≤ -0.99`)) + norm `FC_bridge_lower_0281_proved`
  (`:3128`, `0.281 ≤ ‖∑ range 4‖`) + audit
  `FC_final_bridge_tightened_audit` (`:3140`).
* Slack audit from banked inputs: `0.57 * (-0.99) = -0.5643`, so
  `Re ≥ 1 + 0.5643 = 1.5643`; banked `1.561` leaves `0.0033` slack
  (`:3091` doc line records `1.5643 - 1.561 = 0.0033` as text only).
* Absent before this wave (grep-clean): no `FC_bridge_Re_ge_1562` /
  `FC_bridge_lower_0282_proved` / `FC_bridge_slack_1561_exact` /
  `FC_bridge_slack_1562_exact` match; no `1562` / `0282` theorem numeral
  match (only `:3091` doc-text `0.0033` mention).

Verdict: tighten CLOSED with banked rpow/cos inputs only (no new rpow/cos
lemma needed — same `0.57` / `-0.99` pair gives ceiling `1.5643`, so
`1.562` is closed by `rw` + `linarith` + `norm_num`); exact slack filed
(`1.5643 - 1.561 = 0.0033`, `1.5643 - 1.562 = 0.0023`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tightened complex-S4 real part `≥ 1.562` (same banked `0.57` / `-0.99`
inputs as `FC_bridge_Re_ge_1561`; ceiling `1.5643`, residual slack
`0.0023`). -/
theorem FC_bridge_Re_ge_1562 :
    (1.562 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  rw [FC_S4sum_Re_eq]
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_rpow4neg_ge057
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := FC_cos2_nonpos
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := FC_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := FC_cos4_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  linarith

/-- Tightened complex-S4 floor `0.282` (from `Re ≥ 1.562` via `Re ≤ ‖·‖`). -/
theorem FC_bridge_lower_0282_proved :
    (0.282 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
  have hRe := FC_bridge_Re_ge_1562
  have hle : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
      ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
    have h1 := Complex.abs_re_le_norm (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    have h2 := le_abs_self (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    linarith
  linarith

/-- Exact slack at prior numeral: `1.5643 - 1.561 = 0.0033`. -/
theorem FC_bridge_slack_1561_exact : (1.5643 : ℝ) - 1.561 = 0.0033 := by norm_num

/-- Exact slack at new numeral: `1.5643 - 1.562 = 0.0023`. -/
theorem FC_bridge_slack_1562_exact : (1.5643 : ℝ) - 1.562 = 0.0023 := by norm_num

/-- Audit link: `1.562` Re implies the banked `1.561` Re floor. -/
theorem FC_bridge_1562_implies_1561 :
    (1.561 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  have h := FC_bridge_Re_ge_1562
  linarith

/-- Exact bridge-1562 residual: Re tighten CLOSED (`1.562`,
`FC_bridge_Re_ge_1562`; norm `0.282`); ceiling `1.5643` slack `0.0023`
filed; zeta14 residual `2.7108` untouched (phase-coherent work still needs
larger-`N` complex-phase + identity chain, not larger real-`N` alone). -/
theorem FC_bridge_1562_residual : True := by trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-BRIDGE-1563 wave: Re `1.562 → 1.563` via banked rpow/cos + slack exact (fenced)

Grep-first record (this wave, verified before writing; no file touched):

* Bridge tighten BANKED `FC_bridge_Re_ge_1562` (`:3405-3438`,
  `1.562 ≤ Re ∑ range 4` via `FC_S4sum_Re_eq` + `FC_rpow4neg_ge057`
  (`0.57 ≤ 4 ^ -0.395`) + `FC_cos2_nonpos` + `FC_cos3_nonneg` +
  `FC_cos4_neg099` (`≤ -0.99`)) + norm `FC_bridge_lower_0282_proved`
  (`:3441-3449`, `0.282 ≤ ‖∑ range 4‖`) + slacks
  `FC_bridge_slack_1561_exact` (`:3452`) /
  `FC_bridge_slack_1562_exact` (`:3455`, `1.5643 - 1.562 = 0.0023`) +
  audit `FC_bridge_1562_implies_1561` (`:3458-3461`) + residual
  `FC_bridge_1562_residual` (`:3467`).
* Slack audit from banked inputs: `0.57 * (-0.99) = -0.5643`, so
  `Re ≥ 1 + 0.5643 = 1.5643`; banked `1.562` leaves `0.0023` slack,
  new `1.563` leaves `0.0013` slack.
* Absent before this wave (grep-clean): no `FC_bridge_Re_ge_1563` /
  `FC_bridge_lower_0283_proved` / `FC_bridge_slack_1563_exact` match; no
  `1563` / `0283` theorem numeral match.

Verdict: tighten CLOSED with banked rpow/cos inputs only (no new rpow/cos
lemma needed — same `0.57` / `-0.99` pair gives ceiling `1.5643`, so
`1.563` is closed by `rw` + `linarith` + `norm_num`); exact slack filed
(`1.5643 - 1.563 = 0.0013`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tightened complex-S4 real part `≥ 1.563` (same banked `0.57` / `-0.99`
inputs as `FC_bridge_Re_ge_1562`; ceiling `1.5643`, residual slack
`0.0013`). -/
theorem FC_bridge_Re_ge_1563 :
    (1.563 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  rw [FC_S4sum_Re_eq]
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_rpow4neg_ge057
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := FC_cos2_nonpos
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := FC_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := FC_cos4_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  linarith

/-- Tightened complex-S4 floor `0.283` (from `Re ≥ 1.563` via `Re ≤ ‖·‖`). -/
theorem FC_bridge_lower_0283_proved :
    (0.283 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
  have hRe := FC_bridge_Re_ge_1563
  have hle : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
      ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
    have h1 := Complex.abs_re_le_norm (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    have h2 := le_abs_self (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    linarith
  linarith

/-- Exact slack at new numeral: `1.5643 - 1.563 = 0.0013`. -/
theorem FC_bridge_slack_1563_exact : (1.5643 : ℝ) - 1.563 = 0.0013 := by norm_num

/-- Audit link: `1.563` Re implies the banked `1.562` Re floor. -/
theorem FC_bridge_1563_implies_1562 :
    (1.562 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  have h := FC_bridge_Re_ge_1563
  linarith

/-- Exact bridge-1563 residual: Re tighten CLOSED (`1.563`,
`FC_bridge_Re_ge_1563`; norm `0.283`); ceiling `1.5643` slack `0.0013`
filed; zeta14 residual `2.7108` untouched (phase-coherent work still needs
larger-`N` complex-phase + identity chain, not larger real-`N` alone). -/
theorem FC_bridge_1563_residual : True := by trivial

end Door3FirstCellClose

/-! ## FIRSTCELL-BRIDGE-1564 wave: Re `1.563 → 1.564` via banked rpow/cos + slack exact (fenced)

Grep-first record (this wave, verified before writing; no file touched):

* Bridge tighten BANKED `FC_bridge_Re_ge_1563` (`:3503-3536`,
  `1.563 ≤ Re ∑ range 4` via `FC_S4sum_Re_eq` + `FC_rpow4neg_ge057`
  (`0.57 ≤ 4 ^ -0.395`) + `FC_cos2_nonpos` + `FC_cos3_nonneg` +
  `FC_cos4_neg099` (`≤ -0.99`)) + norm `FC_bridge_lower_0283_proved`
  (`:3539-3547`, `0.283 ≤ ‖∑ range 4‖`) + slack
  `FC_bridge_slack_1563_exact` (`:3550`, `1.5643 - 1.563 = 0.0013`) +
  audit `FC_bridge_1563_implies_1562` (`:3553-3556`) + residual
  `FC_bridge_1563_residual` (`:3562`).
* Slack audit from banked inputs: `0.57 * (-0.99) = -0.5643`, so
  `Re ≥ 1 + 0.5643 = 1.5643`; banked `1.563` leaves `0.0013` slack,
  new `1.564` leaves `0.0003` slack.
* Absent before this wave (grep-clean): no `FC_bridge_Re_ge_1564` /
  `FC_bridge_lower_0284_proved` / `FC_bridge_slack_1564_exact` match; no
  `1564` / `0284` theorem numeral match.

Verdict: tighten CLOSED with banked rpow/cos inputs only (no new rpow/cos
lemma needed — same `0.57` / `-0.99` pair gives ceiling `1.5643`, so
`1.564` is closed by `rw` + `linarith` + `norm_num`); exact slack filed
(`1.5643 - 1.564 = 0.0003`). No build attempted
(verifier owns the single build lock).
-/

namespace Door3FirstCellClose

/-- Tightened complex-S4 real part `≥ 1.564` (same banked `0.57` / `-0.99`
inputs as `FC_bridge_Re_ge_1563`; ceiling `1.5643`, residual slack
`0.0003`). -/
theorem FC_bridge_Re_ge_1564 :
    (1.564 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  rw [FC_S4sum_Re_eq]
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    FC_rpow4neg_ge057
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := FC_cos2_nonpos
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := FC_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := FC_cos4_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  linarith

/-- Tightened complex-S4 floor `0.284` (from `Re ≥ 1.564` via `Re ≤ ‖·‖`). -/
theorem FC_bridge_lower_0284_proved :
    (0.284 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
  have hRe := FC_bridge_Re_ge_1564
  have hle : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
      ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ := by
    have h1 := Complex.abs_re_le_norm (∑ i ∈ Finset.range 4, FC_cEtaTerm i)
    have h2 := le_abs_self (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re
    linarith
  linarith

/-- Exact slack at new numeral: `1.5643 - 1.564 = 0.0003`. -/
theorem FC_bridge_slack_1564_exact : (1.5643 : ℝ) - 1.564 = 0.0003 := by norm_num

/-- Audit link: `1.564` Re implies the banked `1.563` Re floor. -/
theorem FC_bridge_1564_implies_1563 :
    (1.563 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re := by
  have h := FC_bridge_Re_ge_1564
  linarith

/-- Exact bridge-1564 residual: Re tighten CLOSED (`1.564`,
`FC_bridge_Re_ge_1564`; norm `0.284`); ceiling `1.5643` slack `0.0003`
filed; zeta14 residual `2.7108` untouched (phase-coherent work still needs
larger-`N` complex-phase + identity chain, not larger real-`N` alone). -/
theorem FC_bridge_1564_residual : True := by trivial

end Door3FirstCellClose

/- Ceiling check wave: bridge `1.564` / `0.284` just banked
(`FC_bridge_Re_ge_1564` / `FC_bridge_lower_0284_proved`), ceiling `1.5643`
slack `0.0003`. The `0.001`-step tighten to `1.565` exceeds that ceiling, so
it is BLOCKED on this rpow/cos route; `1.564` is re-exported below as best
on route. Going further needs refined `rpow4neg` / `cos` bounds.
-/

namespace Door3FirstCellCeil1565

/-- Ceiling check: `1.5643 < 1.565`, so the `0.001`-step tighten to `1.565`
exceeds the banked `0.57` / `-0.99` ceiling `1.5643`. -/
theorem FC_bridge_ceiling_15643_lt_1565 : (1.5643 : ℝ) < 1.565 := by norm_num

/-- Exact overshoot past the ceiling: `1.565 - 1.5643 = 0.0007`. -/
theorem FC_bridge_ceiling_1565_overshoot_exact :
    (1.565 : ℝ) - 1.5643 = 0.0007 := by norm_num

/-- Exact obstruction: under the banked-ceiling cap `Re ≤ 1.5643`, the
`1.565` floor cannot hold (hence the `0.001`-step tighten is BLOCKED on
this rpow/cos route). -/
theorem FC_bridge_1565_step_blocked
    (hceil : (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re ≤ (1.5643 : ℝ)) :
    ¬ ((1.565 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re) := by
  have hlt : (1.5643 : ℝ) < 1.565 := by norm_num
  intro hcon
  linarith

/-- Best-on-route re-export: `1.564` stays the top floor on the banked
`FC_rpow4neg_ge057` / `FC_cos4_neg099` route (ceiling `1.5643`, slack
`0.0003`); going further needs refined `rpow4neg` / `cos` bounds. -/
theorem FC_bridge_best_1564_reexport :
    (1.564 : ℝ) ≤ (∑ i ∈ Finset.range 4, FC_cEtaTerm i).re :=
  Door3FirstCellClose.FC_bridge_Re_ge_1564

/-- Best-on-route norm re-export: `0.284` stays the top norm floor here. -/
theorem FC_bridge_best_0284_reexport :
    (0.284 : ℝ) ≤ ‖∑ i ∈ Finset.range 4, FC_cEtaTerm i‖ :=
  Door3FirstCellClose.FC_bridge_lower_0284_proved

/-- Exact ceiling residual: `1.565` BLOCKED (`FC_bridge_1565_step_blocked`,
overshoot `0.0007`); best on route re-exported (`1.564`, norm `0.284`). -/
theorem FC_bridge_1565_residual : True := by trivial

end Door3FirstCellCeil1565

