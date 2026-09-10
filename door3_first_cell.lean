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
    FC_rect 0.25 16800 (by norm_num) FC_strip_of_mem hBall

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
