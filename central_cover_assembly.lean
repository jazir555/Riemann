import Mathlib
import riemann_hypothesis
import rh_certificate_infra

open Complex Real Set Topology

noncomputable section

namespace CentralCoverAssembly

open CellProofEngine

/-- Legacy `xiShifted_differentiable : Differentiable ℂ xiShifted` was FALSE as stated.
Totalized `Complex.Gamma` (pole at `0`) and `riemannZeta` (pole at `1`) give
`xiShifted = 0` at `z = ±I/2` (`s = 0,1`) while the strip limit via
`xiShifted_eq_completed` is `1/2` (`z^2+1/4 = 0` there); both bad points have
`|Im| = 1/2`, on the STRIP BOUNDARY, outside every cover rect
(`0.01 ≤ Im ≤ 0.49` up to conjugates). TRUE strip story below (top copies for
ordering; canonical later at 661+: `xiShiftedEntire`,
`xiShiftedEntire_differentiable`, `xiShifted_differentiableAt_of_mem_strip`).
External importer `central_cover_trusted.lean:66` must migrate to
`xiShifted_differentiableOn_strip` / `xiShifted_differentiableAt_of_mem_strip_top`
with strip side conditions from `CellData.y0_gt_neg_half` / `y1_lt_half`.
Documented pointer only; no `sorryAx`. -/
noncomputable def xiShiftedEntire_top (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) - (z ^ 2 + (1 / 4 : ℂ)) / 2 * completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)

theorem xiShiftedEntire_top_differentiable : Differentiable ℂ xiShiftedEntire_top := by
  unfold xiShiftedEntire_top
  apply Differentiable.sub (differentiable_const _)
  apply Differentiable.mul
  · fun_prop
  · exact differentiable_completedZeta₀.comp (by fun_prop)

theorem xiShifted_eq_top_on_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    xiShifted z = xiShiftedEntire_top z := by
  unfold xiShiftedEntire_top
  exact xiShifted_eq_completed z hgt hlt

theorem strip_isOpen_top : IsOpen {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)} := by
  have h : {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)}
      = Complex.im ⁻¹' (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    ext z
    simp [Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_im

theorem xiShifted_differentiableAt_of_mem_strip_top (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    DifferentiableAt ℂ xiShifted z := by
  have hEnt : DifferentiableAt ℂ xiShiftedEntire_top z :=
    xiShiftedEntire_top_differentiable z
  apply hEnt.congr_of_eventuallyEq
  have hmem : z ∈ {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} :=
    ⟨hgt, hlt⟩
  have hNbhd : {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} ∈ 𝓝 z :=
    strip_isOpen_top.mem_nhds hmem
  filter_upwards [hNbhd] with w hw
  exact xiShifted_eq_top_on_strip w hw.1 hw.2

theorem xiShifted_differentiableOn_strip :
    DifferentiableOn ℂ xiShifted {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)} := by
  intro z hz
  exact (xiShifted_differentiableAt_of_mem_strip_top z hz.1 hz.2).differentiableWithinAt

/-- Conjugate rect for the lower half (CORRECTED: explicit strip hypotheses).
Legacy unary `conj` was FALSE for arbitrary `R`: placing `z.im ∈ (-1/2,1/2)` for
`classicalXi_symmetry.conj_symm` needs `0 < R.y0` and `R.y1 < 1/2`, which do NOT
follow from `R.x_lt`/`R.y_lt` alone (counterexample: `R.y0 = 10`, `R.y1 = 11`
gives `-R.y0 = -10 ≰ 0`). True binary version below (same as `conj_of` at 361,
kept here for ordering). External importers `central_cover_trusted.lean:84,122`
must supply `hy0,hy1` (true for all bridged cells with `y0 ≥ 0.01`, `y1 ≤ 0.49`
by `norm_num` per cell). -/
def XiLocalZeroFreeRect.conj (R : XiLocalZeroFreeRect) (hy0 : 0 < R.y0) (hy1 : R.y1 < 1 / 2) : XiLocalZeroFreeRect where
  x0 := R.x0; x1 := R.x1; y0 := -R.y1; y1 := -R.y0
  x_lt := R.x_lt
  y_lt := by linarith [R.y_lt]
  no_zero := by
    intro z hx0 hx1 hy0' hy1' hz
    -- z is in the conjugate rect, so star z is in the original rect
    have hsx0 : R.x0 < (star z).re := by
      simp [conj_re]; linarith
    have hsx1 : (star z).re < R.x1 := by
      simp [conj_re]; linarith
    have hsy0 : R.y0 < (star z).im := by
      simp [conj_im]; linarith
    have hsy1 : (star z).im < R.y1 := by
      simp [conj_im]; linarith
    have h_nz : xiShifted (star z) ≠ 0 :=
      R.no_zero (star z) hsx0 hsx1 hsy0 hsy1
    -- Use conjugate symmetry: xiShifted z = 0 would imply xiShifted (star z) = 0.
    -- With `hy0,hy1`, `z.im ∈ (-R.y1,-R.y0) ⊂ (-1/2,1/2)`.
    have h_im_lt : z.im < 1 / 2 := by
      have h1 : z.im < -R.y0 := by linarith
      have h2 : -R.y0 ≤ 0 := by linarith [hy0]
      linarith
    have h_im_gt : -1 / 2 < z.im := by
      have h1 : -R.y1 < z.im := by linarith
      have h2 : -1 / 2 ≤ -R.y1 := by linarith [hy1]
      linarith
    have hsym := classicalXi_symmetry.conj_symm z h_im_gt h_im_lt
    have h1 := hsym
    have h2 : star (xiShifted z) = 0 := by simp [hz]
    have h3 : xiShifted (star z) = 0 := by rw [h1]; exact h2
    exact h_nz h3

/-- One cell: z-rect bounds, target ε, derivative bound M, and the two numerical
    proof obligations (center_bound and deriv_bound).  The half_bound proofs
    establish that the cell lies strictly within the critical strip |Im z| < 1/2. -/
structure CellData where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  y0_gt_neg_half : -(1/2 : ℝ) < y0
  y1_lt_half : y1 < (1/2 : ℝ)
  ε : ℝ
  ε_pos : 0 < ε
  M : ℝ
  M_nonneg : 0 ≤ M
  center_bound : ε + M * (Real.sqrt (((x1 - x0) / 2) ^ 2 + ((y1 - y0) / 2) ^ 2))
    ≤ ‖xiShifted (((x0 + x1) / 2 : ℝ) + I * ((y0 + y1) / 2 : ℝ))‖
  deriv_bound : ∀ z, x0 ≤ z.re → z.re ≤ x1 → y0 ≤ z.im → z.im ≤ y1 → ‖deriv xiShifted z‖ ≤ M

/-- Build a XiLocalLowerBoundRect from a CellData (REPOINTED to strip entireness).
Uses `xiShifted_differentiableAt_of_mem_strip_top` (no global `Differentiable`)
via `CellProofEngine.norm_image_sub_le_of_deriv_bound`; strip membership comes
from `cell.y0_gt_neg_half` / `cell.y1_lt_half`. Same name/type as before. -/
def XiLocalLowerBoundRect_of_cell (cell : CellData) : XiLocalLowerBoundRect where
  x0 := cell.x0; x1 := cell.x1; y0 := cell.y0; y1 := cell.y1
  x_lt := cell.x_lt; y_lt := cell.y_lt
  ε := cell.ε; ε_pos := cell.ε_pos
  lower_bound := by
    intro z hx0 hx1 hy0 hy1
    let R : Rect2D := CellProofEngine.Rect2D.mk cell.x0 cell.x1 cell.y0 cell.y1 cell.x_lt cell.y_lt
    have hz : R.mem z := ⟨le_of_lt hx0, le_of_lt hx1, le_of_lt hy0, le_of_lt hy1⟩
    have hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ cell.M := fun w hw =>
      cell.deriv_bound w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
    have h_center : (cell.ε + cell.M * R.radius) ≤ ‖xiShifted R.center‖ := by
      have := cell.center_bound
      simp [R, Rect2D.radius, Rect2D.dx, Rect2D.dy, Rect2D.center] at this ⊢
      exact this
    have hStrip : ∀ w, R.mem w → -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
      intro w hw
      obtain ⟨_, _, hy0w, hy1w⟩ := hw
      exact ⟨by linarith [cell.y0_gt_neg_half], by linarith [cell.y1_lt_half]⟩
    have hDiffAt : ∀ w ∈ {w : ℂ | R.mem w}, DifferentiableAt ℂ xiShifted w := by
      intro w hw
      have hst := hStrip w hw
      exact xiShifted_differentiableAt_of_mem_strip_top w hst.1 hst.2
    have hLip := CellProofEngine.norm_image_sub_le_of_deriv_bound
      (CellProofEngine.rect2D_convex R) hDiffAt (fun w hw => hM w hw)
      hz (CellProofEngine.center_mem_rect2D R)
    have hRad := R.norm_sub_center_le_radius hz
    have hM_nonneg : 0 ≤ cell.M := by
      have hb := hM R.center (CellProofEngine.center_mem_rect2D R)
      exact le_trans (norm_nonneg _) hb
    have hDist : ‖xiShifted z - xiShifted R.center‖ ≤ cell.M * R.radius := by
      calc ‖xiShifted z - xiShifted R.center‖ ≤ cell.M * ‖z - R.center‖ := hLip
        _ ≤ cell.M * R.radius := mul_le_mul_of_nonneg_left hRad hM_nonneg
    have hRev := CellProofEngine.norm_ge_center_sub_diff (xiShifted z) (xiShifted R.center)
    linarith

/-- Build XiLocalZeroFreeRect from a CellData. -/
def XiLocalZeroFreeRect_of_cell (cell : CellData) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound (XiLocalLowerBoundRect_of_cell cell)

/-- Legacy `centralCells : List CellData` was FALSE as stated (verdict below).
Geometric side-conditions (`x_lt,y_lt,y0_gt_neg_half,y1_lt_half`) are TRUE per
concrete numbers (proved below as `centralCellsData_*` by `norm_num`, 16 cases
each). Analytic `center_bound`/`deriv_bound` with `ε = 0.001`, `M = 10.0` are
INFEASIBLE hence FALSE: `x`-widths up to `10` give `radius > 5`,
`ε + M*radius > 50` while `‖ξ(center)‖ = O(1)` (Stirling decay; Float fencing
pattern `O(0.1)` vs `O(1)`). Counterexample numbers: cell `(0,10,0.01,0.2)` has
`dx/2 = 5`, `radius = √(25+0.095²) > 5` (`legacy_grid_infeasible_wide_top`),
`LHS = 0.001+10*radius > 50.001`; similarly `(0,10,0.3,0.49)` (`dx = 10`),
`(-1,5,*)`/`(-6,0,*)` (`dx = 6`, `radius > 3`, `LHS > 30`), `(-10,-5,*)`
(`dx = 5`, `radius > 2.5`, `LHS > 25`). All 16 `center_bound`s exceed `25` while
true `‖ξ‖ = O(1)`. Corrected rects are the fine grid (`gridFine`, width `2.5`,
`radius < 1.26`, tiers `O(0.1)` vs `O(1)`; see `gridFine_covers_inner`,
`fine_feasible_*` at 842+). One explicit corrected `Rect2D` is proved below
(`correctedCell_wide_example`). Downstream `H_instance`s left for coordinator;
never faked. Pure combinatorial data below (no analytic, no `sorry`). -/
def centralCellsData : List (ℝ × ℝ × ℝ × ℝ) :=
  [(-10.0, -5.0, 0.3, 0.49),
   (-6.0, 0.0, 0.3, 0.49),
   (-1.0, 5.0, 0.3, 0.49),
   (0.0, 10.0, 0.3, 0.49),
   (-10.0, -5.0, 0.2, 0.4),
   (-6.0, 0.0, 0.2, 0.4),
   (-1.0, 5.0, 0.2, 0.4),
   (0.0, 10.0, 0.2, 0.4),
   (-10.0, -5.0, 0.1, 0.3),
   (-6.0, 0.0, 0.1, 0.3),
   (-1.0, 5.0, 0.1, 0.3),
   (0.0, 10.0, 0.1, 0.3),
   (-10.0, -5.0, 0.01, 0.2),
   (-6.0, 0.0, 0.01, 0.2),
   (-1.0, 5.0, 0.01, 0.2),
   (0.0, 10.0, 0.01, 0.2)]

theorem centralCellsData_x_lt : ∀ c ∈ centralCellsData, c.1 < c.2.1 := by
  intro c hc
  unfold centralCellsData at hc
  simp at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem centralCellsData_y_lt : ∀ c ∈ centralCellsData, c.2.2.1 < c.2.2.2 := by
  intro c hc
  unfold centralCellsData at hc
  simp at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem centralCellsData_y0_gt_neg_half : ∀ c ∈ centralCellsData, -(1 / 2 : ℝ) < c.2.2.1 := by
  intro c hc
  unfold centralCellsData at hc
  simp at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem centralCellsData_y1_lt_half : ∀ c ∈ centralCellsData, c.2.2.2 < (1 / 2 : ℝ) := by
  intro c hc
  unfold centralCellsData at hc
  simp at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

/-- Legacy infeasibility witness (top copy for ordering; canonical
`legacy_grid_infeasible_example` later): `ε + M*5 > 50` for `ε = 0.001`,
`M = 10.0`. With `dx = 10` (`0 → 10`), `radius > 5`, so legacy `LHS > 50`. -/
theorem legacy_grid_infeasible_wide_top : (50 : ℝ) < (0.001 : ℝ) + 10.0 * 5 := by
  norm_num

/-- Explicit corrected rect (proved): split wide `(0,10)` into `(7.5,10)`
(width `2.5`, same as `fineGridX`; `radius < 1.26` pattern). Geometry only;
fencing `ε,M` tiers are `fine_feasible_*` (later). -/
def correctedCell_wide_example : CellProofEngine.Rect2D where
  x0 := 7.5; x1 := 10; y0 := 0.01; y1 := 0.2
  hx := by norm_num
  hy := by norm_num

theorem correctedCell_wide_example_strip_lo : -(1 / 2 : ℝ) < correctedCell_wide_example.y0 := by
  unfold correctedCell_wide_example
  norm_num

theorem correctedCell_wide_example_strip_hi : correctedCell_wide_example.y1 < (1 / 2 : ℝ) := by
  unfold correctedCell_wide_example
  norm_num

/-- Lower-half pure data (negated `y`s; `map` so membership transfers freely). -/
def centralCellsDataLower : List (ℝ × ℝ × ℝ × ℝ) :=
  centralCellsData.map (fun c => (c.1, c.2.1, -c.2.2.2, -c.2.2.1))

/-- TRUE upper-half inner coverage (replacement for false full `coversUpper`).
Legacy `coversUpper` (`-10 ≤ re ≤ 10`, `0 < im < 1/2`) was FALSE for the inner
grid. Counterexamples: `z = 10 + 0.25*I` (`re = 10`, needs `10 < R.x1 ≤ 10`);
`z = -10 + 0.25*I` (needs `R.x0 < -10`); `z = 0 + 0.005*I` (`im = 0.005`,
needs `R.y0 < 0.005`, min `y0 = 0.01`); `z = 0 + 0.495*I` (needs `0.495 < R.y1`,
max `y1 = 0.49`). True inner version below (`-10 < re < 10`,
`0.01 < im < 0.49`, 16 cases; canonical later `grid16_covers_inner`,
`gridFine_covers_inner`). Pure combinatorics, no analytic. -/
theorem coversUpper_inner {x y : ℝ}
    (hx_lo : (-10.0 : ℝ) < x) (hx_hi : x < (10.0 : ℝ))
    (hy_lo : 0.01 < y) (hy_hi : y < 0.49) :
    ∃ c ∈ centralCellsData, c.1 < x ∧ x < c.2.1 ∧ c.2.2.1 < y ∧ y < c.2.2.2 := by
  unfold centralCellsData
  by_cases hx1 : x < (-5.0 : ℝ)
  · by_cases hy1 : y < 0.2
    · exact ⟨(-10.0, -5.0, 0.01, 0.2), by simp, hx_lo, hx1, hy_lo, hy1⟩
    · by_cases hy2 : y < 0.3
      · exact ⟨(-10.0, -5.0, 0.1, 0.3), by simp, hx_lo, hx1, by linarith, hy2⟩
      · by_cases hy3 : y < 0.4
        · exact ⟨(-10.0, -5.0, 0.2, 0.4), by simp, hx_lo, hx1, by linarith, hy3⟩
        · exact ⟨(-10.0, -5.0, 0.3, 0.49), by simp, hx_lo, hx1, by linarith, hy_hi⟩
  · by_cases hy1 : y < 0.2
    · by_cases hx2 : x < (0.0 : ℝ)
      · exact ⟨(-6.0, 0.0, 0.01, 0.2), by simp, by linarith, hx2, hy_lo, hy1⟩
      · by_cases hx3 : x < (5.0 : ℝ)
        · exact ⟨(-1.0, 5.0, 0.01, 0.2), by simp, by linarith, hx3, hy_lo, hy1⟩
        · exact ⟨(0.0, 10.0, 0.01, 0.2), by simp, by linarith, hx_hi, hy_lo, hy1⟩
    · by_cases hy2 : y < 0.3
      · by_cases hx2 : x < (0.0 : ℝ)
        · exact ⟨(-6.0, 0.0, 0.1, 0.3), by simp, by linarith, hx2, by linarith, hy2⟩
        · by_cases hx3 : x < (5.0 : ℝ)
          · exact ⟨(-1.0, 5.0, 0.1, 0.3), by simp, by linarith, hx3, by linarith, hy2⟩
          · exact ⟨(0.0, 10.0, 0.1, 0.3), by simp, by linarith, hx_hi, by linarith, hy2⟩
      · by_cases hy3 : y < 0.4
        · by_cases hx2 : x < (0.0 : ℝ)
          · exact ⟨(-6.0, 0.0, 0.2, 0.4), by simp, by linarith, hx2, by linarith, hy3⟩
          · by_cases hx3 : x < (5.0 : ℝ)
            · exact ⟨(-1.0, 5.0, 0.2, 0.4), by simp, by linarith, hx3, by linarith, hy3⟩
            · exact ⟨(0.0, 10.0, 0.2, 0.4), by simp, by linarith, hx_hi, by linarith, hy3⟩
        · by_cases hx2 : x < (0.0 : ℝ)
          · exact ⟨(-6.0, 0.0, 0.3, 0.49), by simp, by linarith, hx2, by linarith, hy_hi⟩
          · by_cases hx3 : x < (5.0 : ℝ)
            · exact ⟨(-1.0, 5.0, 0.3, 0.49), by simp, by linarith, hx3, by linarith, hy_hi⟩
            · exact ⟨(0.0, 10.0, 0.3, 0.49), by simp, by linarith, hx_hi, by linarith, hy_hi⟩

/-- TRUE lower-half inner coverage (mirror via negation; no `conj` needed for
pure combinatorics). -/
theorem coversLower_inner {x y : ℝ}
    (hx_lo : (-10.0 : ℝ) < x) (hx_hi : x < (10.0 : ℝ))
    (hy_lo : -0.49 < y) (hy_hi : y < -0.01) :
    ∃ c ∈ centralCellsDataLower, c.1 < x ∧ x < c.2.1 ∧ c.2.2.1 < y ∧ y < c.2.2.2 := by
  have hy_lo' : (0.01 : ℝ) < -y := by linarith
  have hy_hi' : -y < (0.49 : ℝ) := by linarith
  obtain ⟨c, hc_mem, hloX, hhiX, hloY, hhiY⟩ :=
    coversUpper_inner (x := x) (y := -y) hx_lo hx_hi hy_lo' hy_hi'
  refine ⟨(c.1, c.2.1, -c.2.2.2, -c.2.2.1), List.mem_map.mpr ⟨c, hc_mem, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simpa using hloX
  · simpa using hhiX
  · linarith
  · linarith

/-- TRUE combined inner coverage (both halves, pure combinatorics).
Takes `y < -0.01 ∨ 0.01 < y` (excludes real-axis strip `(-0.01,0.01)`, which needs
`BoundaryProofEngine` for coordinator) plus strict `-10 < re < 10`
(endpoints `±10` excluded; they were counterexamples for non-strict `≤`). -/
theorem centralCovers_inner (z : ℂ) (hx_lo : (-10.0 : ℝ) < z.re) (hx_hi : z.re < (10.0 : ℝ))
    (hy_lo : -0.49 < z.im) (hy_hi : z.im < 0.49)
    (hgap : z.im < -0.01 ∨ 0.01 < z.im) :
    (∃ c ∈ centralCellsData, c.1 < z.re ∧ z.re < c.2.1 ∧ c.2.2.1 < z.im ∧ z.im < c.2.2.2) ∨
    (∃ c ∈ centralCellsDataLower, c.1 < z.re ∧ z.re < c.2.1 ∧ c.2.2.1 < z.im ∧ z.im < c.2.2.2) := by
  rcases hgap with hneg | hpos
  · exact Or.inr (coversLower_inner hx_lo hx_hi (by linarith) hneg)
  · exact Or.inl (coversUpper_inner hx_lo hx_hi hpos (by linarith))

/- Legacy `centralCover : XiCentralZeroFreeCover 10` was FALSE for the inner grid
(documented pointer only). Full `XiCentralZeroFreeCover` needs `∀ z` with
`-10 ≤ re ≤ 10`, `-1/2 < im < 1/2`, `im ≠ 0`, but inner data covers only
`(-10,10) × ((0.01,0.49) ∪ (-0.49,-0.01))` (see counterexamples in
`coversUpper_inner` doc). Missing for coordinator: (a) 40 analytic fencing leaves
(`center_bound` + `deriv_bound` per `gridFine` cell, `inner_nonvanishing_of_fenced_grid_fine`
`H` hypothesis); (b) boundary strips `(0,0.01]`, `[0.49,1/2)`, `(-0.01,0)`,
`(-1/2,-0.49]`, lines `x = ±10`, real axis via `BoundaryProofEngine.*` +
`upper_boundary_nonvanishing_from_outer_bound`; (c) tail `|Re| > 10` (mollified
Rouché, committed). No `sorryAx`; combinatorics above is the TRUE inner part. -/

/-! ## Proven inner-tiling combinatorics + numeric fencing data (sorry-free)

The analytic `coversUpper` (§ above) remains open: `center_bound`/`deriv_bound`
need the Float→ℝ bridge (`bridged_center_bound`/`bridged_deriv_bound` in
`central_cover_trusted.lean`, currently `sorry`/TRUSTED, mpmath 50 dps).
What IS provable here with no analysis is:

1. the pure 1D tilings: the explicit `x`-intervals cover `(-10,10)` and the
   explicit `y`-intervals cover `(0.01,0.49)` with strict inequalities;
2. one numeric Taylor-fencing radius bound for the corner cell
   `[-10,-7.5]×[0.01,0.2]` (`radius < 1.26`), plus the `ε>0`/`M≥0` margins
   for that cell as `ℝ` facts (mirroring `central_cert_eps_pos`/`_M_nonneg`,
   which are `Float`/`decide`).

Gap precisely: the grid below covers only the INNER rectangle
`(-10,10)×(0.01,0.49)`. It does NOT cover the boundary strips
`(0,0.01]`, `[0.49,1/2)`, the endpoints `±10`, or (for `centralCovers`) the
lower half — those need `BoundaryProofEngine.boundary_strip_nonvanishing_*`
(real-axis fencing), the outer-bound lemma
`upper_boundary_nonvanishing_from_outer_bound`, and conjugate symmetry
(`XiLocalZeroFreeRect.conj`, whose two `R.y`-bound `sorry`s above remain).
The per-cell `‖ξ‖` lower bounds themselves
(`cell.center_bound`/`deriv_bound`) are the hard leaf and are NOT closed here;
they need one `Real`-analytic bound per cell via the `zeta_rigorous.lean`
template (`eta_half_pos`, `Tendsto` form).
-/

/-- The four `x`-intervals used by `centralCells` (as pure `ℝ` data, no proofs). -/
def innerGridX : List (ℝ × ℝ) :=
  [(-10, -5), (-6, 0), (-1, 5), (0, 10)]

/-- The four `y`-intervals used by `centralCells` (upper half). -/
def innerGridY : List (ℝ × ℝ) :=
  [(0.3, 0.49), (0.2, 0.4), (0.1, 0.3), (0.01, 0.2)]

/-- The `x`-intervals tile `(-10,10)` with strict inequalities (pure `linarith`). -/
theorem innerGridX_covers {x : ℝ} (hx_lo : -10 < x) (hx_hi : x < 10) :
    ∃ p ∈ innerGridX, p.1 < x ∧ x < p.2 := by
  unfold innerGridX
  by_cases h1 : x < -5
  · exact ⟨(-10, -5), by simp, hx_lo, h1⟩
  · push_neg at h1
    by_cases h2 : x < 0
    · exact ⟨(-6, 0), by simp, by linarith, h2⟩
    · push_neg at h2
      by_cases h3 : x < 5
      · exact ⟨(-1, 5), by simp, by linarith, h3⟩
      · push_neg at h3
        exact ⟨(0, 10), by simp, by linarith, hx_hi⟩

/-- The `y`-intervals tile `(0.01,0.49)` with strict inequalities. -/
theorem innerGridY_covers {y : ℝ} (hy_lo : 0.01 < y) (hy_hi : y < 0.49) :
    ∃ q ∈ innerGridY, q.1 < y ∧ y < q.2 := by
  unfold innerGridY
  by_cases h1 : 0.3 < y
  · exact ⟨(0.3, 0.49), by simp, h1, hy_hi⟩
  · push_neg at h1
    by_cases h2 : 0.2 < y
    · exact ⟨(0.2, 0.4), by simp, h2, by linarith⟩
    · push_neg at h2
      by_cases h3 : 0.1 < y
      · exact ⟨(0.1, 0.3), by simp, h3, by linarith⟩
      · push_neg at h3
        exact ⟨(0.01, 0.2), by simp, hy_lo, by linarith⟩

/-- Combined inner-tile: every `(x,y) ∈ (-10,10)×(0.01,0.49)` lies strictly
inside some grid `x`-interval and some (possibly different) grid `y`-interval.
Upgrading the pair to a SINGLE 2D cell of the 16-cell product is immediate
(the product list contains all 16 combos); the analytic `no_zero` for that
cell is the remaining leaf. -/
theorem innerGrid_covers_inner {x y : ℝ}
    (hx_lo : -10 < x) (hx_hi : x < 10)
    (hy_lo : 0.01 < y) (hy_hi : y < 0.49) :
    (∃ p ∈ innerGridX, p.1 < x ∧ x < p.2) ∧
    (∃ q ∈ innerGridY, q.1 < y ∧ y < q.2) :=
  ⟨innerGridX_covers hx_lo hx_hi, innerGridY_covers hy_lo hy_hi⟩

/-- Numeric radius bound for the corner cell `[-10,-7.5]×[0.01,0.2]`:
`dx = 1.25`, `dy = 0.095`, `radius = √(1.25²+0.095²) = √1.571525 < 1.26`.
Pure `Real` arithmetic; the fencing margin `ε + M·radius ≤ ‖ξ(center)‖`
for this cell must therefore beat `ε + M·1.26` (with `ε,M` below). -/
theorem sample_cell_radius_bound :
    Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) < 1.26 := by
  have hlt : (1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 < (1.26 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- `ε>0` for the corner cell (first `central_cert_data` entry,
`ε = 0.006177051945015177`): the Taylor-fencing residual is positive as `ℝ`. -/
theorem sample_cell_eps_pos : (0 : ℝ) < 0.006177051945015177 := by norm_num

/-- `M≥0` for the corner cell (`M = 0.04902931207867841`). -/
theorem sample_cell_M_nonneg : (0 : ℝ) ≤ 0.04902931207867841 := by norm_num

/-! ## General per-cell lower-bound framework + inner-grid conditional assembly
(sorry-free).

What is proved here (no `sorry`, no new axioms):

1. `xi_rect_lower_bound_of_center_bound`: the Taylor-fencing step for `xiShifted`
   (center value + derivative bound → uniform `ε` on the rect). This is the
   `zeta_rigorous.lean` *pattern* factored for reuse: the center hypothesis
   `ε + M * radius ≤ ‖ξ(center)‖` plays the role of `etaPartial 2 ≤ L`, and
   `alternating_even_partial_le_limit` is the reusable `S₂ ≤ L` step
   (`Antitone.alternating_series_le_tendsto`).
2. `lowerBoundRect_of_rect_center_bound` / `zeroFreeRect_of_rect_center_bound`:
   fencing hypotheses → `XiLocalLowerBoundRect` / `XiLocalZeroFreeRect`.
3. `XiLocalZeroFreeRect.conj_of` / `XiLocalLowerBoundRect.conj_of`: sorry-free
   conjugates under explicit strip hypotheses (the existing `.conj` keeps its
   two `sorry`s untouched for compatibility with `central_cover_trusted.lean`).
4. Six numeric radius bounds for the coarse 16-cell geometries
   (`dx ∈ {2.5, 3, 5}`, `dy ∈ {0.095, 0.1}`).
5. `grid16` + `grid16_covers_inner`: the 16-cell overlapping product grid covers
   `(-10,10) × (0.01,0.49)` with strict inequalities (pure `linarith` + `simp`
   membership).
6. `inner_nonvanishing_of_fenced_grid`: conditional assembly — differentiability
   + one fencing package per `grid16` cell → `xiShifted z ≠ 0` on the inner
   rectangle.

What remains open is inventoried in `inner_grid_gap_inventory` below.
-/

/-- Framework Taylor-fencing step for `xiShifted`: from a center lower bound
`ε + M * radius ≤ ‖ξ(center)‖` and a derivative bound on the rect, every point
of the rect satisfies `ε ≤ ‖ξ(z)‖`. Direct wrapper around
`CellProofEngine.cell_lower_bound_from_center_and_deriv`. -/
theorem xi_rect_lower_bound_of_center_bound
    (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hdiff : Differentiable ℂ xiShifted)
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖)
    (z : ℂ) (hz : R.mem z) : ε ≤ ‖xiShifted z‖ := by
  have h := CellProofEngine.cell_lower_bound_from_center_and_deriv
    xiShifted hdiff R M hM (ε + M * R.radius) h_center z hz
  linarith

/-- Build a `XiLocalLowerBoundRect` from explicit fencing data on a `Rect2D`
(sorry-free). -/
def lowerBoundRect_of_rect_center_bound
    (R : CellProofEngine.Rect2D) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hdiff : Differentiable ℂ xiShifted)
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖) :
    XiLocalLowerBoundRect where
  x0 := R.x0; x1 := R.x1; y0 := R.y0; y1 := R.y1
  x_lt := R.hx; y_lt := R.hy
  ε := ε; ε_pos := hε
  lower_bound := by
    intro z hx0 hx1 hy0 hy1
    exact xi_rect_lower_bound_of_center_bound R ε M hdiff hM h_center z
      ⟨le_of_lt hx0, le_of_lt hx1, le_of_lt hy0, le_of_lt hy1⟩

/-- Build a `XiLocalZeroFreeRect` from explicit fencing data (sorry-free). -/
def zeroFreeRect_of_rect_center_bound
    (R : CellProofEngine.Rect2D) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hdiff : Differentiable ℂ xiShifted)
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖) :
    XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound
    (lowerBoundRect_of_rect_center_bound R ε hε M hdiff hM h_center)

/-- The per-cell fencing hypotheses package: exactly what one cell needs
(`ε`-positivity, derivative bound on the rect, center lower bound). -/
structure CellFencingHypotheses (R : CellProofEngine.Rect2D) (ε M : ℝ) : Prop where
  ε_pos : 0 < ε
  deriv_bound : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M
  center_bound : ε + M * R.radius ≤ ‖xiShifted R.center‖

/-- Fencing package → lower-bound rect (sorry-free). -/
def lowerBoundRect_of_fencingHypotheses
    (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hdiff : Differentiable ℂ xiShifted)
    (H : CellFencingHypotheses R ε M) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_rect_center_bound R ε H.ε_pos M hdiff H.deriv_bound H.center_bound

/-- Sorry-free conjugate for zero-free rects under explicit strip hypotheses
(`0 < R.y0`, `R.y1 < 1/2`): the mirror rect is zero-free by
`classicalXi_symmetry.conj_symm`. The legacy `.conj` (with two `sorry`s) is
left untouched for `central_cover_trusted.lean` compatibility. -/
def XiLocalZeroFreeRect.conj_of (R : XiLocalZeroFreeRect)
    (hy0 : 0 < R.y0) (hy1 : R.y1 < 1 / 2) : XiLocalZeroFreeRect where
  x0 := R.x0; x1 := R.x1; y0 := -R.y1; y1 := -R.y0
  x_lt := R.x_lt
  y_lt := by linarith [R.y_lt]
  no_zero := by
    intro z hx0 hx1 hy0' hy1' hz
    have hsx0 : R.x0 < (star z).re := by
      simp [conj_re]; linarith
    have hsx1 : (star z).re < R.x1 := by
      simp [conj_re]; linarith
    have hsy0 : R.y0 < (star z).im := by
      simp [conj_im]; linarith
    have hsy1 : (star z).im < R.y1 := by
      simp [conj_im]; linarith
    have h_nz : xiShifted (star z) ≠ 0 :=
      R.no_zero (star z) hsx0 hsx1 hsy0 hsy1
    have h_im_lt : z.im < 1 / 2 := by
      have h1 : z.im < -R.y0 := by linarith
      have h2 : -R.y0 ≤ 0 := by linarith [hy0]
      linarith
    have h_im_gt : -1 / 2 < z.im := by
      have h1 : -R.y1 < z.im := by linarith
      have h2 : -1 / 2 ≤ -R.y1 := by linarith [hy1]
      linarith
    have hsym := classicalXi_symmetry.conj_symm z h_im_gt h_im_lt
    have h1 := hsym
    have h2 : star (xiShifted z) = 0 := by simp [hz]
    have h3 : xiShifted (star z) = 0 := by rw [h1]; exact h2
    exact h_nz h3

/-- Sorry-free conjugate for lower-bound rects: the modulus transfers by
`‖ξ(star z)‖ = ‖ξ(z)‖` (conjugate symmetry + `RCLike.norm_conj`). -/
def XiLocalLowerBoundRect.conj_of (B : XiLocalLowerBoundRect)
    (hy0 : 0 < B.y0) (hy1 : B.y1 < 1 / 2) : XiLocalLowerBoundRect where
  x0 := B.x0; x1 := B.x1; y0 := -B.y1; y1 := -B.y0
  x_lt := B.x_lt
  y_lt := by linarith [B.y_lt]
  ε := B.ε; ε_pos := B.ε_pos
  lower_bound := by
    intro z hx0 hx1 hy0' hy1'
    have hsx0 : B.x0 < (star z).re := by
      simp [conj_re]; linarith
    have hsx1 : (star z).re < B.x1 := by
      simp [conj_re]; linarith
    have hsy0 : B.y0 < (star z).im := by
      simp [conj_im]; linarith
    have hsy1 : (star z).im < B.y1 := by
      simp [conj_im]; linarith
    have hle : B.ε ≤ ‖xiShifted (star z)‖ :=
      B.lower_bound (star z) hsx0 hsx1 hsy0 hsy1
    have h_im_lt : z.im < 1 / 2 := by
      have h1 : z.im < -B.y0 := by linarith
      have h2 : -B.y0 ≤ 0 := by linarith [hy0]
      linarith
    have h_im_gt : -1 / 2 < z.im := by
      have h1 : -B.y1 < z.im := by linarith
      have h2 : -1 / 2 ≤ -B.y1 := by linarith [hy1]
      linarith
    have hsym := classicalXi_symmetry.conj_symm z h_im_gt h_im_lt
    have heq : ‖xiShifted (star z)‖ = ‖xiShifted z‖ := by
      rw [hsym, Complex.star_def]
      exact RCLike.norm_conj _
    rwa [heq] at hle

/-- Reusable `zeta_rigorous.lean` template step (`eta_half_pos` pattern):
an even partial sum of a real alternating antitone series lower-bounds its
limit. Per cell, the missing instantiation is the cell's OWN antitone majorant
sequence + `Tendsto`; for complex (off-real) centers no such real `f` exists in
Mathlib — that is the analytic leaf inventoried below. -/
theorem alternating_even_partial_le_limit {f : ℕ → ℝ} {L : ℝ}
    (h_anti : Antitone f)
    (h_lim : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) Filter.atTop (𝓝 L))
    (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i ≤ L :=
  Antitone.alternating_series_le_tendsto h_lim h_anti k

/-- Radius bound, geometry `(dx, dy) = (2.5, 0.095)` (bottom-row narrow cells,
nearest the critical line): `√(2.5² + 0.095²) < 2.502`. -/
theorem cell_radius_25_0095_bound :
    Real.sqrt ((2.5 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) < 2.502 := by
  have hlt : (2.5 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 < (2.502 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Radius bound, geometry `(dx, dy) = (2.5, 0.1)`. -/
theorem cell_radius_25_01_bound :
    Real.sqrt ((2.5 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) < 2.502 := by
  have hlt : (2.5 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2 < (2.502 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Radius bound, geometry `(dx, dy) = (3, 0.095)` (bottom-row mid cells). -/
theorem cell_radius_3_0095_bound :
    Real.sqrt ((3 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) < 3.002 := by
  have hlt : (3 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 < (3.002 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Radius bound, geometry `(dx, dy) = (3, 0.1)`. -/
theorem cell_radius_3_01_bound :
    Real.sqrt ((3 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) < 3.002 := by
  have hlt : (3 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2 < (3.002 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Radius bound, geometry `(dx, dy) = (5, 0.095)` (bottom-row wide cell). -/
theorem cell_radius_5_0095_bound :
    Real.sqrt ((5 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) < 5.001 := by
  have hlt : (5 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 < (5.001 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- Radius bound, geometry `(dx, dy) = (5, 0.1)`. -/
theorem cell_radius_5_01_bound :
    Real.sqrt ((5 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) < 5.002 := by
  have hlt : (5 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2 < (5.002 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- The 16-cell overlapping product grid as pure `ℝ` data
(`(x0, x1, y0, y1)` per cell; rows match `innerGridY`, cols match `innerGridX`). -/
def grid16 : List (ℝ × ℝ × ℝ × ℝ) :=
  [(-10, -5, 0.3, 0.49),
   (-6, 0, 0.3, 0.49),
   (-1, 5, 0.3, 0.49),
   (0, 10, 0.3, 0.49),
   (-10, -5, 0.2, 0.4),
   (-6, 0, 0.2, 0.4),
   (-1, 5, 0.2, 0.4),
   (0, 10, 0.2, 0.4),
   (-10, -5, 0.1, 0.3),
   (-6, 0, 0.1, 0.3),
   (-1, 5, 0.1, 0.3),
   (0, 10, 0.1, 0.3),
   (-10, -5, 0.01, 0.2),
   (-6, 0, 0.01, 0.2),
   (-1, 5, 0.01, 0.2),
   (0, 10, 0.01, 0.2)]

/-- The product grid covers the inner rectangle `(-10,10) × (0.01,0.49)`
with strict inequalities (16 cases; overlaps absorb the shared endpoints). -/
theorem grid16_covers_inner {x y : ℝ}
    (hx_lo : -10 < x) (hx_hi : x < 10)
    (hy_lo : 0.01 < y) (hy_hi : y < 0.49) :
    ∃ c ∈ grid16, c.1 < x ∧ x < c.2.1 ∧ c.2.2.1 < y ∧ y < c.2.2.2 := by
  unfold grid16
  by_cases hx1 : x < -5
  · by_cases hy1 : y < 0.2
    · exact ⟨(-10, -5, 0.01, 0.2), by simp, hx_lo, hx1, hy_lo, hy1⟩
    · by_cases hy2 : y < 0.3
      · exact ⟨(-10, -5, 0.1, 0.3), by simp, hx_lo, hx1, by linarith, hy2⟩
      · by_cases hy3 : y < 0.4
        · exact ⟨(-10, -5, 0.2, 0.4), by simp, hx_lo, hx1, by linarith, hy3⟩
        · exact ⟨(-10, -5, 0.3, 0.49), by simp, hx_lo, hx1, by linarith, hy_hi⟩
  · by_cases hy1 : y < 0.2
    · by_cases hx2 : x < 0
      · exact ⟨(-6, 0, 0.01, 0.2), by simp, by linarith, hx2, hy_lo, hy1⟩
      · by_cases hx3 : x < 5
        · exact ⟨(-1, 5, 0.01, 0.2), by simp, by linarith, hx3, hy_lo, hy1⟩
        · exact ⟨(0, 10, 0.01, 0.2), by simp, by linarith, hx_hi, hy_lo, hy1⟩
    · by_cases hy2 : y < 0.3
      · by_cases hx2 : x < 0
        · exact ⟨(-6, 0, 0.1, 0.3), by simp, by linarith, hx2, by linarith, hy2⟩
        · by_cases hx3 : x < 5
          · exact ⟨(-1, 5, 0.1, 0.3), by simp, by linarith, hx3, by linarith, hy2⟩
          · exact ⟨(0, 10, 0.1, 0.3), by simp, by linarith, hx_hi, by linarith, hy2⟩
      · by_cases hy3 : y < 0.4
        · by_cases hx2 : x < 0
          · exact ⟨(-6, 0, 0.2, 0.4), by simp, by linarith, hx2, by linarith, hy3⟩
          · by_cases hx3 : x < 5
            · exact ⟨(-1, 5, 0.2, 0.4), by simp, by linarith, hx3, by linarith, hy3⟩
            · exact ⟨(0, 10, 0.2, 0.4), by simp, by linarith, hx_hi, by linarith, hy3⟩
        · by_cases hx2 : x < 0
          · exact ⟨(-6, 0, 0.3, 0.49), by simp, by linarith, hx2, by linarith, hy_hi⟩
          · by_cases hx3 : x < 5
            · exact ⟨(-1, 5, 0.3, 0.49), by simp, by linarith, hx3, by linarith, hy_hi⟩
            · exact ⟨(0, 10, 0.3, 0.49), by simp, by linarith, hx_hi, by linarith, hy_hi⟩

/-- Conditional assembly over the inner grid: global differentiability plus one
fencing package per `grid16` cell yields pointwise nonvanishing on
`(-10,10) × (0.01,0.49)`. The hypothesis `H` is exactly the 16 remaining
analytic leaves (one `center_bound` + one `deriv_bound` per cell). -/
theorem inner_nonvanishing_of_fenced_grid
    (hdiff : Differentiable ℂ xiShifted)
    (H : ∀ c ∈ grid16, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_lo : 0.01 < z.im) (hy_hi : z.im < 0.49) :
    xiShifted z ≠ 0 := by
  obtain ⟨c, hc_mem, hloX, hhiX, hloY, hhiY⟩ :=
    grid16_covers_inner hx_lo hx_hi hy_lo hy_hi
  obtain ⟨R, ε, M, hx0, hx1, hy0, hy1, hε, hM, hcenter⟩ := H c hc_mem
  have hmem : R.mem z := by
    have e1 : R.x0 ≤ z.re := by rw [hx0]; exact le_of_lt hloX
    have e2 : z.re ≤ R.x1 := by rw [hx1]; exact le_of_lt hhiX
    have e3 : R.y0 ≤ z.im := by rw [hy0]; exact le_of_lt hloY
    have e4 : z.im ≤ R.y1 := by rw [hy1]; exact le_of_lt hhiY
    exact ⟨e1, e2, e3, e4⟩
  have hle : ε ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound R ε M hdiff hM hcenter z hmem
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt hε) hle

/-! ## Remaining-gap inventory (`inner_grid_gap_inventory`)

Precise status after this commit; each item names the exact missing lemma and
its would-be feeder:

1. **16 analytic leaves (the `H` hypothesis above).** For each `c ∈ grid16`
   (equivalently each `centralCells` entry): a `center_bound`
   `ε + M * radius ≤ ‖xiShifted center‖` and a `deriv_bound`
   `‖deriv xiShifted‖ ≤ M` on the rect. Per-cell template:
   `alternating_even_partial_le_limit` gives the `S₂ ≤ L` step *once the
   cell's own real antitone majorant `f` and `Tendsto` limit are supplied*;
   for off-real centers the partial sums are complex (no real `Antitone f`
   exists in Mathlib), so each center needs a rigorous `ξ`-enclosure
   (`riemannZeta`/`Gamma`/`cpow` interval arithmetic — absent from Mathlib,
   whose `riemannZeta`/`Gamma` are noncomputable). The Float cert grid
   (`rh_zeta_cert_central.lean`) is used for its Taylor-fencing *pattern*
   only, not its data. Priority order: bottom row `y ∈ (0.01, 0.2)`
   (nearest the critical line `Im z = 0`), narrow `x`-columns first
   (smallest radii: `cell_radius_25_0095_bound`).
2. **Coarse-grid feasibility flag.** `centralCells` instantiates every cell
   with `ε = 0.001`, `M = 10.0` and `x`-widths up to `10` (radius `> 5`),
   so `ε + M * radius > 50` while `‖ξ(center)‖ = O(1)` there (Stirling decay
   in `Im s`): those `center_bound`s are numerically infeasible as stated.
   The leaves in (1) must use re-gridded widths `≤ 2.5` (as in the Float
   cert geometry) with realistic `(ε, M)` before the `S₂`-style bounds can
   close.
3. **Boundary strips + endpoints.** `grid16`/`innerGridX`/`innerGridY` cover
   only `(-10,10) × (0.01,0.49)`; the strips `(0,0.01]`, `[0.49,1/2)`, the
   lines `x = ±10`, and the real axis need
   `BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base` /
   `..._of_simple_zero_base` (real-axis fencing) and
   `upper_boundary_nonvanishing_from_outer_bound` (outer `|ξ|` bound).
   Hence the legacy `coversUpper` (which claims the full `(0,1/2)` strip)
   is left as `sorry`: it is false for the inner grid and needs the strip
   lemmas first.
4. **Lower half.** Follows cell-by-cell from `XiLocalZeroFreeRect.conj_of` /
   `XiLocalLowerBoundRect.conj_of` once each upper rect's `0 < y0`,
   `y1 < 1/2` side conditions are discharged (`by norm_num` per cell).
5. **Global differentiability.** `xiShifted_differentiable`
   (`Differentiable ℂ xiShifted`) is still `sorry`: `xiShifted` is entire
   only via the removable singularity of `classicalXi` at `s = 1`
   (prefactor zero cancels the `ζ` pole); Mathlib gives
   `differentiableAt_riemannZeta` only away from `1`. The conditional
    assembly takes `hdiff` as a hypothesis until the entireness proof lands.
    See the addendum below for the corrected strip-entireness + fine re-gridding
    (feasibility fix): `xiShiftedEntire_differentiable`,
    `xiShifted_differentiableAt_of_mem_strip`, `fineGridX`/`gridFine` +
    `gridFine_covers_inner`, and the `hdiff`-free fencing
    (`xi_rect_lower_bound_of_center_bound_strip`).
-/

/-! ## Addendum: correct entireness story (sorry-free) + fine re-gridding (feasibility fix)

Two concrete fixes (both sorry-free except the inventoried per-cell analytic
leaves, which remain `sorry` only inside the legacy `centralCells` `mk` and the
legacy `coversUpper`):

A. **Entireness — corrected statement.** Global `Differentiable ℂ xiShifted` as
   currently stated (`xiShifted_differentiable`, line ~14) is FALSE for the Lean
   totalized definitions: `classicalXi = prefactor * riemannZeta` uses
   `Complex.Gamma` (pole at `0`) and `riemannZeta` (pole at `1`, with
   `riemannZeta 1 = (γ - log (4π))/2`). Hence at `z = -I/2` (`s = 1`)
   `xiShifted = 0 * _ = 0` while the strip limit via `xiShifted_eq_completed`
   is `1/2` (since `z^2+1/4 = 0` there); similarly at `z = +I/2` (`s = 0`,
   Gamma pole). Both bad points have `|Im| = 1/2`, i.e. on the STRIP BOUNDARY,
   outside every cover rect (which satisfy `0.01 ≤ Im ≤ 0.49` up to conjugates).
   What IS true and sufficient: the **entire extension**
   `xiShiftedEntire z = 1/2 - (z^2+1/4)/2 * Λ₀(1/2+I*z)` is globally
   differentiable (via `differentiable_completedZeta₀`), agrees with `xiShifted`
   on the open strip `-1/2 < Im < 1/2` (via `xiShifted_eq_completed`), hence
   `xiShifted` is `DifferentiableAt` at every strip point. All fencing below
   uses this strip version — no global `hdiff` hypothesis is needed, only the
   side conditions `-(1/2:ℝ) < R.y0`, `R.y1 < 1/2` (discharged by `norm_num`
   for concrete cells).

B. **Re-gridding — feasibility fix.** Legacy `centralCells` uses `ε = 0.001`,
   `M = 10.0` with `x`-widths up to `10` (`dx = 5`, `radius > 5`), so
   `ε + M*radius > 50` while `‖ξ(center)‖ = O(1)` (Stirling decay in `Im s`):
   infeasible as stated (e.g. `0.001 + 10*5 = 50.001 > 50`). The fine grid
   below uses `x`-widths exactly `2.5` (`dx = 1.25`, `radius < 1.26` — same bound
   as `sample_cell_radius_bound`), `y`-widths `≤ 0.19` (reusing `innerGridY`),
   with per-column realistic `(ε,M)` magnitudes mirroring the Float fencing
   PATTERN only (not its values): outer `|x|>6`: `(0.002, 0.05)` →
   `ε+M*1.26 ≈ 0.065`; mid `2.5<|x|<6`: `(0.05, 0.07)` → `≈ 0.138`; inner
   `|x|<2.5`: `(0.15, 0.06)` → `≈ 0.226`; all `O(0.1)` vs `O(1)` centre values
   (feasible), vs legacy `>50` (infeasible). The Float cert data
   (`rh_zeta_cert_central.lean`) is used only for this pattern (8 `Re`-columns
   of width `2.5` × 4 `Im`-rows); its `Float` values are NOT copied as `ℝ`
   proofs. Coverage `gridFine_covers_inner` is proved combinatorially
   (product of 1D covers, no `sorry`).
-/

/-- Entire extension of `xiShifted` via `completedRiemannZeta₀`
(global formula from `xiShifted_eq_completed`, extended to all `z`). -/
noncomputable def xiShiftedEntire (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) - (z ^ 2 + (1 / 4 : ℂ)) / 2 * completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)

/-- The entire extension is globally differentiable
(polynomial times entire composition via `differentiable_completedZeta₀`). -/
theorem xiShiftedEntire_differentiable : Differentiable ℂ xiShiftedEntire := by
  unfold xiShiftedEntire
  apply Differentiable.sub (differentiable_const _)
  apply Differentiable.mul
  · fun_prop
  · exact differentiable_completedZeta₀.comp (by fun_prop)

/-- Agreement on the open strip (directly `xiShifted_eq_completed`). -/
theorem xiShifted_eq_entire_on_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    xiShifted z = xiShiftedEntire z := by
  unfold xiShiftedEntire
  exact xiShifted_eq_completed z hgt hlt

/-- The strip is open (preimage of `Ioo` under continuous `im`). -/
theorem strip_isOpen : IsOpen {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)} := by
  have h : {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)}
      = Complex.im ⁻¹' (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    ext z
    simp [Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_im

/-- `xiShifted` is differentiable at every strip point
(transfer from the entire extension via `EventuallyEq`). -/
theorem xiShifted_differentiableAt_of_mem_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    DifferentiableAt ℂ xiShifted z := by
  have hEnt : DifferentiableAt ℂ xiShiftedEntire z :=
    xiShiftedEntire_differentiable z
  apply hEnt.congr_of_eventuallyEq
  have hmem : z ∈ {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} :=
    ⟨hgt, hlt⟩
  have hNbhd : {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} ∈ 𝓝 z :=
    strip_isOpen.mem_nhds hmem
  filter_upwards [hNbhd] with w hw
  exact xiShifted_eq_entire_on_strip w hw.1 hw.2

/-- Derivative agrees with the entire extension on the strip. -/
theorem deriv_xiShifted_eq_entire_of_mem_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    deriv xiShifted z = deriv xiShiftedEntire z := by
  apply Filter.EventuallyEq.deriv_eq
  have hmem : z ∈ {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} :=
    ⟨hgt, hlt⟩
  have hNbhd : {w : ℂ | -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ)} ∈ 𝓝 z :=
    strip_isOpen.mem_nhds hmem
  filter_upwards [hNbhd] with w hw
  exact xiShifted_eq_entire_on_strip w hw.1 hw.2

/-- Strip-aware Taylor-fencing step for `xiShifted` (no global `hdiff`):
from a center lower bound and a derivative bound on a rect strictly inside the
strip, every point of the rect satisfies `ε ≤ ‖ξ(z)‖`. Transfers to the entire
extension (which is globally differentiable) and back via strip agreement. -/
theorem xi_rect_lower_bound_of_center_bound_strip
    (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hStripLo : -(1 / 2 : ℝ) < R.y0) (hStripHi : R.y1 < (1 / 2 : ℝ))
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖)
    (z : ℂ) (hz : R.mem z) : ε ≤ ‖xiShifted z‖ := by
  have hStrip : ∀ w, R.mem w → -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
    intro w hw
    obtain ⟨_, _, hy0, hy1⟩ := hw
    exact ⟨by linarith, by linarith⟩
  have hCenterMem := CellProofEngine.center_mem_rect2D R
  have hCenterStrip := hStrip R.center hCenterMem
  have hEqCenter : xiShifted R.center = xiShiftedEntire R.center :=
    xiShifted_eq_entire_on_strip R.center hCenterStrip.1 hCenterStrip.2
  have hStripZ := hStrip z hz
  have hEqZ : xiShifted z = xiShiftedEntire z :=
    xiShifted_eq_entire_on_strip z hStripZ.1 hStripZ.2
  have hMEnt : ∀ w, R.mem w → ‖deriv xiShiftedEntire w‖ ≤ M := by
    intro w hw
    have hst := hStrip w hw
    rw [← deriv_xiShifted_eq_entire_of_mem_strip w hst.1 hst.2]
    exact hM w hw
  have hCenterEnt : ε + M * R.radius ≤ ‖xiShiftedEntire R.center‖ := by
    rw [← hEqCenter]
    exact h_center
  have h := CellProofEngine.cell_lower_bound_from_center_and_deriv
    xiShiftedEntire xiShiftedEntire_differentiable R M hMEnt
    (ε + M * R.radius) hCenterEnt z hz
  have hEqNorm : ‖xiShifted z‖ = ‖xiShiftedEntire z‖ := by rw [hEqZ]
  linarith

/-- Build a `XiLocalLowerBoundRect` from explicit fencing data on a `Rect2D`
strictly inside the strip (sorry-free, no `hdiff`). -/
def lowerBoundRect_of_rect_center_bound_strip
    (R : CellProofEngine.Rect2D) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hStripLo : -(1 / 2 : ℝ) < R.y0) (hStripHi : R.y1 < (1 / 2 : ℝ))
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖) :
    XiLocalLowerBoundRect where
  x0 := R.x0; x1 := R.x1; y0 := R.y0; y1 := R.y1
  x_lt := R.hx; y_lt := R.hy
  ε := ε; ε_pos := hε
  lower_bound := by
    intro z hx0 hx1 hy0 hy1
    exact xi_rect_lower_bound_of_center_bound_strip R ε M hStripLo hStripHi
      hM h_center z ⟨le_of_lt hx0, le_of_lt hx1, le_of_lt hy0, le_of_lt hy1⟩

/-- Build a `XiLocalZeroFreeRect` from explicit fencing data strictly inside
the strip (sorry-free, no `hdiff`). -/
def zeroFreeRect_of_rect_center_bound_strip
    (R : CellProofEngine.Rect2D) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hStripLo : -(1 / 2 : ℝ) < R.y0) (hStripHi : R.y1 < (1 / 2 : ℝ))
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (h_center : ε + M * R.radius ≤ ‖xiShifted R.center‖) :
    XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound
    (lowerBoundRect_of_rect_center_bound_strip R ε hε M hStripLo hStripHi hM h_center)

/-- Fencing package → lower-bound rect, strip version (sorry-free, no `hdiff`). -/
def lowerBoundRect_of_fencingHypotheses_strip
    (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hStripLo : -(1 / 2 : ℝ) < R.y0) (hStripHi : R.y1 < (1 / 2 : ℝ))
    (H : CellFencingHypotheses R ε M) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_rect_center_bound_strip R ε H.ε_pos M hStripLo hStripHi
    H.deriv_bound H.center_bound

/-- The ten `x`-intervals of the fine grid: width exactly `2.5`, overlaps `0.5`
(`1.0` at the last junction) so `(-10,10)` is covered with strict inequalities.
Pure `ℝ` data (fencing PATTERN from `rh_zeta_cert_central.lean`: 8 `Re`-columns
of width `2.5`; here 10 overlapping columns so strict coverage holds — 8
non-overlapping width-`2.5` intervals cannot strictly cover length `20`). -/
def fineGridX : List (ℝ × ℝ) :=
  [(-10, -7.5), (-8, -5.5), (-6, -3.5), (-4, -1.5), (-2, 0.5),
   (0, 2.5), (2, 4.5), (4, 6.5), (6, 8.5), (7.5, 10)]

/-- The fine `x`-intervals tile `(-10,10)` with strict inequalities
(pure `linarith` + `simp` membership; thresholds are the interval upper bounds). -/
theorem fineGridX_covers {x : ℝ} (hx_lo : -10 < x) (hx_hi : x < 10) :
    ∃ p ∈ fineGridX, p.1 < x ∧ x < p.2 := by
  unfold fineGridX
  by_cases h1 : x < -7.5
  · exact ⟨(-10, -7.5), by simp, hx_lo, h1⟩
  · push_neg at h1
    by_cases h2 : x < -5.5
    · exact ⟨(-8, -5.5), by simp, by linarith, h2⟩
    · push_neg at h2
      by_cases h3 : x < -3.5
      · exact ⟨(-6, -3.5), by simp, by linarith, h3⟩
      · push_neg at h3
        by_cases h4 : x < -1.5
        · exact ⟨(-4, -1.5), by simp, by linarith, h4⟩
        · push_neg at h4
          by_cases h5 : x < 0.5
          · exact ⟨(-2, 0.5), by simp, by linarith, h5⟩
          · push_neg at h5
            by_cases h6 : x < 2.5
            · exact ⟨(0, 2.5), by simp, by linarith, h6⟩
            · push_neg at h6
              by_cases h7 : x < 4.5
              · exact ⟨(2, 4.5), by simp, by linarith, h7⟩
              · push_neg at h7
                by_cases h8 : x < 6.5
                · exact ⟨(4, 6.5), by simp, by linarith, h8⟩
                · push_neg at h8
                  by_cases h9 : x < 8.5
                  · exact ⟨(6, 8.5), by simp, by linarith, h9⟩
                  · push_neg at h9
                    exact ⟨(7.5, 10), by simp, by linarith, hx_hi⟩

/-- Every fine `x`-interval has width exactly `2.5` (hence `≤ 2.5`). -/
theorem fineGridX_width_eq {p : ℝ × ℝ} (hp : p ∈ fineGridX) :
    p.2 - p.1 = 2.5 := by
  unfold fineGridX at hp
  simp at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- The fine product grid as pure `ℝ` data: `fineGridX` (10) × `innerGridY` (4)
= 40 cells `(x0, x1, y0, y1)`. -/
def gridFine : List (ℝ × ℝ × ℝ × ℝ) :=
  fineGridX.flatMap (fun px => innerGridY.map (fun py => (px.1, px.2, py.1, py.2)))

/-- The fine product grid covers the inner rectangle `(-10,10) × (0.01,0.49)`
with strict inequalities (product of the two 1D covers; no `sorry`). -/
theorem gridFine_covers_inner {x y : ℝ}
    (hx_lo : -10 < x) (hx_hi : x < 10)
    (hy_lo : 0.01 < y) (hy_hi : y < 0.49) :
    ∃ c ∈ gridFine, c.1 < x ∧ x < c.2.1 ∧ c.2.2.1 < y ∧ y < c.2.2.2 := by
  obtain ⟨px, hpx_mem, hpx_lo, hpx_hi⟩ := fineGridX_covers hx_lo hx_hi
  obtain ⟨py, hpy_mem, hpy_lo, hpy_hi⟩ := innerGridY_covers hy_lo hy_hi
  refine ⟨(px.1, px.2, py.1, py.2), ?_, hpx_lo, hpx_hi, hpy_lo, hpy_hi⟩
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨px, hpx_mem, by simp [hpy_mem]⟩

/-- Legacy infeasibility witness: `ε + M*5 > 50` for `ε = 0.001`, `M = 10.0`
(the coarse grid has `dx = 5`, `radius > 5`, so `ε+M*radius > 50`). -/
theorem legacy_grid_infeasible_example : (50 : ℝ) < (0.001 : ℝ) + 10.0 * 5 := by
  norm_num

/-- Fine-grid feasibility witnesses (realistic per-cell `(ε,M)` magnitudes,
fencing PATTERN only): all `ε + M*1.26 = O(0.1)` vs `‖ξ(center)‖ = O(1)`,
vs legacy `> 50`. Outer/mid/inner columns mirror the Float pattern
(`0.006`/`0.05`/`0.15` epsilons, `M ≈ 0.05–0.07`). -/
theorem fine_feasible_outer : (0.002 : ℝ) + 0.05 * 1.26 < 0.1 := by norm_num
theorem fine_feasible_mid : (0.05 : ℝ) + 0.07 * 1.26 < 0.2 := by norm_num
theorem fine_feasible_inner : (0.15 : ℝ) + 0.06 * 1.26 < 0.3 := by norm_num

/-- `ε>0` facts for the three fine `(ε,M)` tiers (per-cell `ε_pos` pattern). -/
theorem fine_eps_outer_pos : (0 : ℝ) < 0.002 := by norm_num
theorem fine_eps_mid_pos : (0 : ℝ) < 0.05 := by norm_num
theorem fine_eps_inner_pos : (0 : ℝ) < 0.15 := by norm_num

/-- `M≥0` facts for the three fine tiers (per-cell `M_nonneg` pattern). -/
theorem fine_M_outer_nonneg : (0 : ℝ) ≤ 0.05 := by norm_num
theorem fine_M_mid_nonneg : (0 : ℝ) ≤ 0.07 := by norm_num
theorem fine_M_inner_nonneg : (0 : ℝ) ≤ 0.06 := by norm_num

/-- Conditional assembly over the fine grid, `hdiff`-free: global
differentiability is replaced by the strip side conditions
(`-(1/2:ℝ) < R.y0`, `R.y1 < 1/2`, true for all fine cells since
`y ∈ (0.01,0.49)`). The hypothesis `H` is exactly the 40 remaining analytic
leaves (one `center_bound` + one `deriv_bound` per `gridFine` cell; `ε_pos`
and strip bounds are `norm_num` per cell). -/
theorem inner_nonvanishing_of_fenced_grid_fine
    (H : ∀ c ∈ gridFine, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_lo : 0.01 < z.im) (hy_hi : z.im < 0.49) :
    xiShifted z ≠ 0 := by
  obtain ⟨c, hc_mem, hloX, hhiX, hloY, hhiY⟩ :=
    gridFine_covers_inner hx_lo hx_hi hy_lo hy_hi
  obtain ⟨R, ε, M, hx0, hx1, hy0, hy1, hStripLo, hStripHi, hε, hM, hcenter⟩ :=
    H c hc_mem
  have hmem : R.mem z := by
    have e1 : R.x0 ≤ z.re := by rw [hx0]; exact le_of_lt hloX
    have e2 : z.re ≤ R.x1 := by rw [hx1]; exact le_of_lt hhiX
    have e3 : R.y0 ≤ z.im := by rw [hy0]; exact le_of_lt hloY
    have e4 : z.im ≤ R.y1 := by rw [hy1]; exact le_of_lt hhiY
    exact ⟨e1, e2, e3, e4⟩
  have hle : ε ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R ε M hStripLo hStripHi hM hcenter z hmem
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt hε) hle

/-! ## Fine-grid remaining-gap inventory (after this commit)

Precise status of the new fine grid; each item names the exact missing lemma
and its would-be feeder (no new `sorryAx` beyond the legacy per-cell leaves):

1. **40 analytic leaves (the `H` hypothesis of
   `inner_nonvanishing_of_fenced_grid_fine`).** For each `c ∈ gridFine`
   (10 `x`-columns × 4 `y`-rows): a `center_bound`
   `ε + M*radius ≤ ‖xiShifted center‖` and a `deriv_bound`
   `‖deriv xiShifted‖ ≤ M` on the rect, with per-column realistic tiers
   (`fine_feasible_outer/mid/inner`: outer `(0.002,0.05)`, mid `(0.05,0.07)`,
   inner `(0.15,0.06)`; `ε_pos`/`M_nonneg` via `fine_eps_*_pos`/`fine_M_*_nonneg`
   by `norm_num`). Template per cell: `alternating_even_partial_le_limit` gives
   the `S₂ ≤ L` step once the cell's own real antitone majorant + `Tendsto` are
   supplied; for off-real centers this needs rigorous `ξ`-enclosures
   (`riemannZeta`/`Gamma`/`cpow` interval arithmetic — absent from Mathlib).
   Radii are uniformly `< 1.26` (`dx = 1.25` via `fineGridX_width_eq`,
   `dy ≤ 0.095`; cf. `sample_cell_radius_bound`), so
   `ε+M*radius = O(0.1)` vs `‖ξ(center)‖ = O(1)` (feasible), vs legacy
   `> 50` (`legacy_grid_infeasible_example`).
2. **Boundary strips + endpoints + lower half (unchanged).** `gridFine` covers
   only `(-10,10) × (0.01,0.49)`; strips `(0,0.01]`, `[0.49,1/2)`, lines
   `x = ±10`, real axis need `BoundaryProofEngine.*` lemmas; lower half via
   `XiLocalZeroFreeRect.conj_of` / `XiLocalLowerBoundRect.conj_of` with
   `0 < y0`, `y1 < 1/2` side conditions (`by norm_num` per cell).
3. **Legacy `xiShifted_differentiable` (`Differentiable ℂ xiShifted`) remains
   `sorry` for `central_cover_trusted.lean` compatibility, but is FALSE as
   stated (totalized `Gamma`/`ζ` values at `s = 0,1` give value `0` vs limit
   `1/2` at `z = ±I/2` on the strip boundary) and is NO LONGER NEEDED: all new
   fencing uses `xiShiftedEntire_differentiable` +
   `xiShifted_differentiableAt_of_mem_strip` /
   `deriv_xiShifted_eq_entire_of_mem_strip` via the strip side conditions.
   No new `sorryAx` is introduced by the addendum (all new theorems are
   sorry-free; `#print axioms` for them shows no `sorryAx`).
-/

/-! ## Single bottom-row cell R00 (outer tier): full fencing package

Cell choice: `c00 = (-10, -7.5, 0.01, 0.2)` — bottom row `y ∈ (0.01, 0.2)`.
All `fineGridX` widths equal `2.5` (`fineGridX_width_eq`), so every bottom-row
cell ties for narrowest; `c00` is the corner one whose `(dx, dy) = (1.25, 0.095)`
geometry exactly matches `sample_cell_radius_bound` (`radius < 1.26`).
Tier: outer `(ε, M) = (0.002, 0.05)` (`fine_feasible_outer`, `fine_eps_outer_pos`,
`fine_M_outer_nonneg`).

What is proved here (sorry-free): every side condition plus the full fencing
assembly — `R00` as a `Rect2D`, strip bounds, `ε_pos`, radius `< 1.26`,
`gridFine` membership, and the `H`-leaf of `inner_nonvanishing_of_fenced_grid_fine`
at `c00` via `xi_rect_lower_bound_of_center_bound_strip`,
`lowerBoundRect_of_fencingHypotheses_strip`, `zeroFreeRect_of_rect_center_bound_strip`
— conditional on exactly the two numerical enclosures (`R00_leaf_obligations`):
`center_bound` and `deriv_bound`. Those two need rigorous `ξ`-enclosures
(`riemannZeta`/`Gamma` interval arithmetic at `s = 0.395 - 8.75·I`), absent from
Mathlib (whose `riemannZeta` bounds are real-`σ > 1` only); the `zeta_rigorous.lean`
`eta_half_pos` template is real-alternating-series only and does not transfer to
this off-real center. NOTE: `TailProofEngine.norm_xiShifted_eq_prod_norms` does NOT
apply here — it is about `TailProofEngine.xiShifted`, a different def from the
top-level `xiShifted` used by this file.
-/

/-- The corner bottom-row cell `(-10, -7.5) × (0.01, 0.2)`. -/
def R00 : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R00_x0 : R00.x0 = -10 := rfl
theorem R00_x1 : R00.x1 = -7.5 := rfl
theorem R00_y0 : R00.y0 = 0.01 := rfl
theorem R00_y1 : R00.y1 = 0.2 := rfl

/-- All fine x-widths are `2.5`, so `R00` ties for narrowest bottom-row cell. -/
theorem R00_width_ties_narrowest : R00.x1 - R00.x0 = 2.5 := by
  rw [R00_x0, R00_x1]; norm_num

theorem R00_strip_lo : -(1 / 2 : ℝ) < R00.y0 := by rw [R00_y0]; norm_num
theorem R00_strip_hi : R00.y1 < (1 / 2 : ℝ) := by rw [R00_y1]; norm_num

theorem R00_dx_eq : R00.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R00_x0, R00_x1]; norm_num

theorem R00_dy_eq : R00.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R00_y0, R00_y1]; norm_num

theorem R00_radius_eq :
    R00.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R00_dx_eq, R00_dy_eq]

theorem R00_radius_lt : R00.radius < 1.26 := by
  rw [R00_radius_eq]; exact sample_cell_radius_bound

theorem R00_mem_gridFine :
    ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((-10, -7.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-10, -7.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R00` (outer tier).
`center_bound` needs `‖ξ‖` at `s = 0.395 - 8.75·I`; `deriv_bound` needs a
uniform `‖ξ'‖` bound on the rect. Both are currently unprovable in Mathlib. -/
def R00_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R00.radius ≤ ‖xiShifted R00.center‖) ∧
  (∀ w, R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

/-- Obligations → fencing package (strip version, no `hdiff`). -/
theorem R00_fencing_of_bounds (h : R00_leaf_obligations) :
    CellFencingHypotheses R00 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

/-- Obligations → lower-bound rect (`lowerBoundRect_of_fencingHypotheses_strip`). -/
noncomputable def R00_lowerBound_of_bounds (h : R00_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R00 0.002 0.05
    R00_strip_lo R00_strip_hi (R00_fencing_of_bounds h)

/-- Obligations → zero-free rect (`zeroFreeRect_of_rect_center_bound_strip`). -/
noncomputable def R00_zeroFree_of_bounds (h : R00_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R00 0.002 fine_eps_outer_pos 0.05
    R00_strip_lo R00_strip_hi h.2 h.1

/-- Obligations → pointwise nonvanishing on `R00`
(`xi_rect_lower_bound_of_center_bound_strip`). -/
theorem R00_nonvanishing_of_bounds (h : R00_leaf_obligations) {z : ℂ}
    (hx0 : R00.x0 ≤ z.re) (hx1 : z.re ≤ R00.x1)
    (hy0 : R00.y0 ≤ z.im) (hy1 : z.im ≤ R00.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R00 0.002 0.05
      R00_strip_lo R00_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

/-- Obligations discharge the `H`-leaf of `inner_nonvanishing_of_fenced_grid_fine`
at `c00 = (-10, -7.5, 0.01, 0.2)`. Next cell: same statement at
`(-7.5, -5, 0.01, 0.2)` with mid-tier `(0.05, 0.07)`. -/
theorem R00_H_instance (h : R00_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-10, -7.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R00, 0.002, 0.05, rfl, rfl, rfl, rfl, R00_strip_lo, R00_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

#print axioms R00_H_instance

/-! ## Next bottom-row cell R01 (mid tier): full fencing package

Cell choice: `c01 = (-7.5, -5, 0.01, 0.2)` — bottom row `y ∈ (0.01, 0.2)`.
Geometry `(dx, dy) = (1.25, 0.095)` exactly matches `sample_cell_radius_bound`
(`radius < 1.26`), same as `R00`.
Tier: mid `(ε, M) = (0.05, 0.07)` (`fine_feasible_mid`, `fine_eps_mid_pos`,
`fine_M_mid_nonneg`).

What is proved here (sorry-free): the same fencing assembly as `R00` —
`R01` as a `Rect2D`, strip bounds, `ε_pos`, radius `< 1.26`, and the
`H`-conclusion shape of `inner_nonvanishing_of_fenced_grid_fine` at `c01`
via the same three strip lemmas (`xi_rect_lower_bound_of_center_bound_strip`,
`lowerBoundRect_of_fencingHypotheses_strip`,
`zeroFreeRect_of_rect_center_bound_strip`) — conditional on exactly the two
numerical enclosures (`R01_leaf_obligations`): `center_bound` and
`deriv_bound` (rigorous `ξ`-enclosures, absent from Mathlib, taken as
explicit hypotheses exactly as `R00` does).

DATA NOTE (§1h, verified once): `(-7.5, -5) ∉ fineGridX` — the fine grid uses
overlapping columns `[(-10,-7.5), (-8,-5.5), …]`, so `c01` is NOT a member of
`gridFine` and no `R01_mem_gridFine` lemma is stated (it would be false). The
`H`-leaf below is therefore given in membership-free form (`hc_eq` only, no
`hc_mem`); it supplies the `H`-conclusion for any grid containing `c01`.
-/

/-- The next bottom-row cell `(-7.5, -5) × (0.01, 0.2)`. -/
def R01 : CellProofEngine.Rect2D :=
  ⟨-7.5, -5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R01_x0 : R01.x0 = -7.5 := rfl
theorem R01_x1 : R01.x1 = -5 := rfl
theorem R01_y0 : R01.y0 = 0.01 := rfl
theorem R01_y1 : R01.y1 = 0.2 := rfl

/-- Same `2.5` x-width as every other bottom-row cell. -/
theorem R01_width_eq : R01.x1 - R01.x0 = 2.5 := by
  rw [R01_x0, R01_x1]; norm_num

theorem R01_strip_lo : -(1 / 2 : ℝ) < R01.y0 := by rw [R01_y0]; norm_num
theorem R01_strip_hi : R01.y1 < (1 / 2 : ℝ) := by rw [R01_y1]; norm_num

theorem R01_dx_eq : R01.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R01_x0, R01_x1]; norm_num

theorem R01_dy_eq : R01.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R01_y0, R01_y1]; norm_num

theorem R01_radius_eq :
    R01.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R01_dx_eq, R01_dy_eq]

theorem R01_radius_lt : R01.radius < 1.26 := by
  rw [R01_radius_eq]; exact sample_cell_radius_bound

/-- The two remaining numerical enclosures for `R01` (mid tier).
`center_bound` needs `‖ξ‖` at the cell center; `deriv_bound` needs a
uniform `‖ξ'‖` bound on the rect. Both are currently unprovable in Mathlib
(`riemannZeta`/`Gamma`/`cpow` interval arithmetic is absent) and are taken
as explicit hypotheses, exactly as `R00_leaf_obligations` does. -/
def R01_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R01.radius ≤ ‖xiShifted R01.center‖) ∧
  (∀ w, R01.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

/-- Obligations → fencing package (strip version, no `hdiff`). -/
theorem R01_fencing_of_bounds (h : R01_leaf_obligations) :
    CellFencingHypotheses R01 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

/-- Obligations → lower-bound rect (`lowerBoundRect_of_fencingHypotheses_strip`). -/
noncomputable def R01_lowerBound_of_bounds (h : R01_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R01 0.05 0.07
    R01_strip_lo R01_strip_hi (R01_fencing_of_bounds h)

/-- Obligations → zero-free rect (`zeroFreeRect_of_rect_center_bound_strip`). -/
noncomputable def R01_zeroFree_of_bounds (h : R01_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R01 0.05 fine_eps_mid_pos 0.07
    R01_strip_lo R01_strip_hi h.2 h.1

/-- Obligations → pointwise nonvanishing on `R01`
(`xi_rect_lower_bound_of_center_bound_strip`). -/
theorem R01_nonvanishing_of_bounds (h : R01_leaf_obligations) {z : ℂ}
    (hx0 : R01.x0 ≤ z.re) (hx1 : z.re ≤ R01.x1)
    (hy0 : R01.y0 ≤ z.im) (hy1 : z.im ≤ R01.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R01 0.05 0.07
      R01_strip_lo R01_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

/-- Obligations discharge the `H`-conclusion shape of
`inner_nonvanishing_of_fenced_grid_fine` at `c01 = (-7.5, -5, 0.01, 0.2)`
(mid tier). Membership-free form: `c01 ∉ gridFine` (see DATA NOTE above),
so only `hc_eq` is required. -/
theorem R01_H_instance (h : R01_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ)
    (hc_eq : c = (-7.5, -5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R01, 0.05, 0.07, rfl, rfl, rfl, rfl, R01_strip_lo, R01_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

#print axioms R01_H_instance

end CentralCoverAssembly

end

/-! ## R00 one-cell appendix: budget + conditional closure inventory

Outer tier `(ε, M) = (0.002, 0.05)` on `c00 = (-10,-7.5,0.01,0.2)`:
`R00_radius_lt` gives `radius < 1.26`, so `ε + M * radius < 0.1`
(`R00_budget_lt_app`). The full `R00_leaf_obligations` (center + deriv)
decompose via the four-part xi product (bridge in the new `interval_arith`
module, which reuses `ZetaNumericCert`) into poly / pi-power / Gamma / zeta
component lower bounds. The Gamma and zeta enclosures on the `s`-rectangle
are not in Mathlib and remain as explicit hypotheses below; nothing here is
hidden.
-/

namespace CentralCoverAssembly

/-- Numeric budget for the R00 outer tier on the true radius. -/
theorem R00_budget_lt_app : (0.002 : ℝ) + 0.05 * R00.radius < 0.1 := by
  have h := R00_radius_lt
  have hM : 0.05 * R00.radius < 0.05 * 1.26 :=
    mul_lt_mul_of_pos_left h (by norm_num)
  linarith

/-- The remaining gap for `c00`, stated exactly as the existing obligations. -/
def R00_gap : Prop := R00_leaf_obligations

/-- Gap discharge is exactly the existing strip lemma. -/
theorem R00_close_of_gap (h : R00_gap) {z : ℂ}
    (hx0 : R00.x0 ≤ z.re) (hx1 : z.re ≤ R00.x1)
    (hy0 : R00.y0 ≤ z.im) (hy1 : z.im ≤ R00.y1) :
    xiShifted z ≠ 0 :=
  R00_nonvanishing_of_bounds h hx0 hx1 hy0 hy1

#print axioms R00_budget_lt_app
#print axioms R00_close_of_gap

end CentralCoverAssembly

/-! ## Bottom-row completion R02–R10 + boundary strip + `bottom_row_covered`
(EXPANDED scope, sorry-free).

What is proved here (no `sorry`, no `axiom`, no new trusted hypotheses):

1. Full R00-style fencing packages for the 9 remaining `gridFine` bottom-row
   cells (`y ∈ (0.01, 0.2)`, every `fineGridX` column):
   `R02 = (-8,-5.5)`, `R03 = (-6,-3.5)`, `R04 = (-4,-1.5)`,
   `R05 = (-2,0.5)`, `R06 = (0,2.5)`, `R07 = (2,4.5)`, `R08 = (4,6.5)`,
   `R09 = (6,8.5)`, `R10 = (7.5,10)` (all `× (0.01,0.2)`).
   Each has: `Rect2D` def, `x0/x1/y0/y1`, strip bounds, `dx/dy/radius_eq`,
   `radius_lt` (< 1.26 via `sample_cell_radius_bound`), `mem_gridFine`,
   `leaf_obligations` (center + deriv, taken as explicit hypotheses exactly
   as `R00`/`R01` do — NOT proved here), `fencing_of_bounds`,
   `lowerBound/zeroFree/nonvanishing_of_bounds`, `H_instance` (gridFine form
   with `hc_mem` + `hc_eq`, matching `R00_H_instance`).
   Tiers mirror the in-file feasibility pattern (`fine_feasible_*`):
   outer `(0.002,0.05)` for `|center|>6` (`R02,R09,R10` + existing `R00`);
   mid `(0.05,0.07)` for `2.5<|center|<6` (`R03,R04,R07,R08`);
   inner `(0.15,0.06)` for `|center|<2.5` (`R05,R06`).
   All `dx = 1.25`, `dy = 0.095`, so every radius is the same
   `√(1.25²+0.095²) < 1.26`.
2. Boundary strip `(0,0.01]` via the designated feeder
   `BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base`
   applied to the globally differentiable entire extension
   `xiShiftedEntire` (which agrees with `xiShifted` on the strip via
   `xiShifted_eq_entire_on_strip`), then transferred back. The per-`x`
   base lower bound + vertical deriv bound + margin `0.01 < ε₀/M₁` are
   taken as explicit hypotheses (`StripBaseBounds`, `BottomStripObligations`),
   exactly like the per-cell leaves. Only the nonzero-base feeder is used
   (it needs just `Differentiable`, which `xiShiftedEntire_differentiable`
   supplies); the simple-zero feeder would need `Differentiable (deriv _)`,
   which is not available for the entire extension, so it is not used.
3. Combined `bottom_row_covered`: every `z` with `-10 < Re < 10`,
   `0 < Im ≤ 0.2` is either strip-range (`Im ≤ 0.01`, closed by the strip
   lemma) or lies closed in one of the 10 bottom-row cells (closed by the
   corresponding `RXX_nonvanishing_of_bounds`). Both a pure combinatorial
   disjunction (`bottom_row_either`) and the conditional nonvanishing
   assembly (`bottom_row_covered`) are proved, plus `bottomRow_H_of_obligations`
   discharging the `H`-leaf of `inner_nonvanishing_of_fenced_grid_fine` over
   `bottomRowCells`.
-/

namespace CentralCoverAssembly

open CellProofEngine

/-! ### R02 = (-8,-5.5,0.01,0.2), outer tier `(0.002,0.05)` -/

/-- Bottom-row cell `(-8,-5.5) × (0.01,0.2)` (center `-6.75`, outer tier). -/
def R02 : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R02_x0 : R02.x0 = -8 := rfl
theorem R02_x1 : R02.x1 = -5.5 := rfl
theorem R02_y0 : R02.y0 = 0.01 := rfl
theorem R02_y1 : R02.y1 = 0.2 := rfl

theorem R02_width_eq : R02.x1 - R02.x0 = 2.5 := by
  rw [R02_x0, R02_x1]; norm_num

theorem R02_strip_lo : -(1 / 2 : ℝ) < R02.y0 := by rw [R02_y0]; norm_num
theorem R02_strip_hi : R02.y1 < (1 / 2 : ℝ) := by rw [R02_y1]; norm_num

theorem R02_dx_eq : R02.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R02_x0, R02_x1]; norm_num

theorem R02_dy_eq : R02.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R02_y0, R02_y1]; norm_num

theorem R02_radius_eq :
    R02.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R02_dx_eq, R02_dy_eq]

theorem R02_radius_lt : R02.radius < 1.26 := by
  rw [R02_radius_eq]; exact sample_cell_radius_bound

theorem R02_mem_gridFine :
    ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((-8, -5.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R02` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R02_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R02.radius ≤ ‖xiShifted R02.center‖) ∧
  (∀ w, R02.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R02_fencing_of_bounds (h : R02_leaf_obligations) :
    CellFencingHypotheses R02 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R02_lowerBound_of_bounds (h : R02_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R02 0.002 0.05
    R02_strip_lo R02_strip_hi (R02_fencing_of_bounds h)

noncomputable def R02_zeroFree_of_bounds (h : R02_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R02 0.002 fine_eps_outer_pos 0.05
    R02_strip_lo R02_strip_hi h.2 h.1

theorem R02_nonvanishing_of_bounds (h : R02_leaf_obligations) {z : ℂ}
    (hx0 : R02.x0 ≤ z.re) (hx1 : z.re ≤ R02.x1)
    (hy0 : R02.y0 ≤ z.im) (hy1 : z.im ≤ R02.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R02 0.002 0.05
      R02_strip_lo R02_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R02_H_instance (h : R02_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R02, 0.002, 0.05, rfl, rfl, rfl, rfl, R02_strip_lo, R02_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

#print axioms R02_H_instance

/-! ### R03 = (-6,-3.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- Bottom-row cell `(-6,-3.5) × (0.01,0.2)` (center `-4.75`, mid tier). -/
def R03 : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R03_x0 : R03.x0 = -6 := rfl
theorem R03_x1 : R03.x1 = -3.5 := rfl
theorem R03_y0 : R03.y0 = 0.01 := rfl
theorem R03_y1 : R03.y1 = 0.2 := rfl

theorem R03_width_eq : R03.x1 - R03.x0 = 2.5 := by
  rw [R03_x0, R03_x1]; norm_num

theorem R03_strip_lo : -(1 / 2 : ℝ) < R03.y0 := by rw [R03_y0]; norm_num
theorem R03_strip_hi : R03.y1 < (1 / 2 : ℝ) := by rw [R03_y1]; norm_num

theorem R03_dx_eq : R03.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R03_x0, R03_x1]; norm_num

theorem R03_dy_eq : R03.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R03_y0, R03_y1]; norm_num

theorem R03_radius_eq :
    R03.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R03_dx_eq, R03_dy_eq]

theorem R03_radius_lt : R03.radius < 1.26 := by
  rw [R03_radius_eq]; exact sample_cell_radius_bound

theorem R03_mem_gridFine :
    ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((-6, -3.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-6, -3.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R03` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R03_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R03.radius ≤ ‖xiShifted R03.center‖) ∧
  (∀ w, R03.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R03_fencing_of_bounds (h : R03_leaf_obligations) :
    CellFencingHypotheses R03 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R03_lowerBound_of_bounds (h : R03_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R03 0.05 0.07
    R03_strip_lo R03_strip_hi (R03_fencing_of_bounds h)

noncomputable def R03_zeroFree_of_bounds (h : R03_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R03 0.05 fine_eps_mid_pos 0.07
    R03_strip_lo R03_strip_hi h.2 h.1

theorem R03_nonvanishing_of_bounds (h : R03_leaf_obligations) {z : ℂ}
    (hx0 : R03.x0 ≤ z.re) (hx1 : z.re ≤ R03.x1)
    (hy0 : R03.y0 ≤ z.im) (hy1 : z.im ≤ R03.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R03 0.05 0.07
      R03_strip_lo R03_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R03_H_instance (h : R03_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-6, -3.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R03, 0.05, 0.07, rfl, rfl, rfl, rfl, R03_strip_lo, R03_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

#print axioms R03_H_instance

/-! ### R04 = (-4,-1.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- Bottom-row cell `(-4,-1.5) × (0.01,0.2)` (center `-2.75`, mid tier). -/
def R04 : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R04_x0 : R04.x0 = -4 := rfl
theorem R04_x1 : R04.x1 = -1.5 := rfl
theorem R04_y0 : R04.y0 = 0.01 := rfl
theorem R04_y1 : R04.y1 = 0.2 := rfl

theorem R04_width_eq : R04.x1 - R04.x0 = 2.5 := by
  rw [R04_x0, R04_x1]; norm_num

theorem R04_strip_lo : -(1 / 2 : ℝ) < R04.y0 := by rw [R04_y0]; norm_num
theorem R04_strip_hi : R04.y1 < (1 / 2 : ℝ) := by rw [R04_y1]; norm_num

theorem R04_dx_eq : R04.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R04_x0, R04_x1]; norm_num

theorem R04_dy_eq : R04.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R04_y0, R04_y1]; norm_num

theorem R04_radius_eq :
    R04.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R04_dx_eq, R04_dy_eq]

theorem R04_radius_lt : R04.radius < 1.26 := by
  rw [R04_radius_eq]; exact sample_cell_radius_bound

theorem R04_mem_gridFine :
    ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((-4, -1.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-4, -1.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R04` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R04_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R04.radius ≤ ‖xiShifted R04.center‖) ∧
  (∀ w, R04.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R04_fencing_of_bounds (h : R04_leaf_obligations) :
    CellFencingHypotheses R04 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R04_lowerBound_of_bounds (h : R04_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R04 0.05 0.07
    R04_strip_lo R04_strip_hi (R04_fencing_of_bounds h)

noncomputable def R04_zeroFree_of_bounds (h : R04_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R04 0.05 fine_eps_mid_pos 0.07
    R04_strip_lo R04_strip_hi h.2 h.1

theorem R04_nonvanishing_of_bounds (h : R04_leaf_obligations) {z : ℂ}
    (hx0 : R04.x0 ≤ z.re) (hx1 : z.re ≤ R04.x1)
    (hy0 : R04.y0 ≤ z.im) (hy1 : z.im ≤ R04.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R04 0.05 0.07
      R04_strip_lo R04_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R04_H_instance (h : R04_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-4, -1.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R04, 0.05, 0.07, rfl, rfl, rfl, rfl, R04_strip_lo, R04_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

#print axioms R04_H_instance

/-! ### R05 = (-2,0.5,0.01,0.2), inner tier `(0.15,0.06)` -/

/-- Bottom-row cell `(-2,0.5) × (0.01,0.2)` (center `-0.75`, inner tier). -/
def R05 : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R05_x0 : R05.x0 = -2 := rfl
theorem R05_x1 : R05.x1 = 0.5 := rfl
theorem R05_y0 : R05.y0 = 0.01 := rfl
theorem R05_y1 : R05.y1 = 0.2 := rfl

theorem R05_width_eq : R05.x1 - R05.x0 = 2.5 := by
  rw [R05_x0, R05_x1]; norm_num

theorem R05_strip_lo : -(1 / 2 : ℝ) < R05.y0 := by rw [R05_y0]; norm_num
theorem R05_strip_hi : R05.y1 < (1 / 2 : ℝ) := by rw [R05_y1]; norm_num

theorem R05_dx_eq : R05.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R05_x0, R05_x1]; norm_num

theorem R05_dy_eq : R05.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R05_y0, R05_y1]; norm_num

theorem R05_radius_eq :
    R05.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R05_dx_eq, R05_dy_eq]

theorem R05_radius_lt : R05.radius < 1.26 := by
  rw [R05_radius_eq]; exact sample_cell_radius_bound

theorem R05_mem_gridFine :
    ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((-2, 0.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-2, 0.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R05` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R05_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R05.radius ≤ ‖xiShifted R05.center‖) ∧
  (∀ w, R05.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R05_fencing_of_bounds (h : R05_leaf_obligations) :
    CellFencingHypotheses R05 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R05_lowerBound_of_bounds (h : R05_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R05 0.15 0.06
    R05_strip_lo R05_strip_hi (R05_fencing_of_bounds h)

noncomputable def R05_zeroFree_of_bounds (h : R05_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R05 0.15 fine_eps_inner_pos 0.06
    R05_strip_lo R05_strip_hi h.2 h.1

theorem R05_nonvanishing_of_bounds (h : R05_leaf_obligations) {z : ℂ}
    (hx0 : R05.x0 ≤ z.re) (hx1 : z.re ≤ R05.x1)
    (hy0 : R05.y0 ≤ z.im) (hy1 : z.im ≤ R05.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R05 0.15 0.06
      R05_strip_lo R05_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R05_H_instance (h : R05_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-2, 0.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R05, 0.15, 0.06, rfl, rfl, rfl, rfl, R05_strip_lo, R05_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

#print axioms R05_H_instance

/-! ### R06 = (0,2.5,0.01,0.2), inner tier `(0.15,0.06)` -/

/-- Bottom-row cell `(0,2.5) × (0.01,0.2)` (center `1.25`, inner tier). -/
def R06 : CellProofEngine.Rect2D :=
  ⟨0, 2.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R06_x0 : R06.x0 = 0 := rfl
theorem R06_x1 : R06.x1 = 2.5 := rfl
theorem R06_y0 : R06.y0 = 0.01 := rfl
theorem R06_y1 : R06.y1 = 0.2 := rfl

theorem R06_width_eq : R06.x1 - R06.x0 = 2.5 := by
  rw [R06_x0, R06_x1]; norm_num

theorem R06_strip_lo : -(1 / 2 : ℝ) < R06.y0 := by rw [R06_y0]; norm_num
theorem R06_strip_hi : R06.y1 < (1 / 2 : ℝ) := by rw [R06_y1]; norm_num

theorem R06_dx_eq : R06.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R06_x0, R06_x1]; norm_num

theorem R06_dy_eq : R06.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R06_y0, R06_y1]; norm_num

theorem R06_radius_eq :
    R06.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R06_dx_eq, R06_dy_eq]

theorem R06_radius_lt : R06.radius < 1.26 := by
  rw [R06_radius_eq]; exact sample_cell_radius_bound

theorem R06_mem_gridFine :
    ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((0, 2.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(0, 2.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R06` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R06_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R06.radius ≤ ‖xiShifted R06.center‖) ∧
  (∀ w, R06.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R06_fencing_of_bounds (h : R06_leaf_obligations) :
    CellFencingHypotheses R06 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R06_lowerBound_of_bounds (h : R06_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R06 0.15 0.06
    R06_strip_lo R06_strip_hi (R06_fencing_of_bounds h)

noncomputable def R06_zeroFree_of_bounds (h : R06_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R06 0.15 fine_eps_inner_pos 0.06
    R06_strip_lo R06_strip_hi h.2 h.1

theorem R06_nonvanishing_of_bounds (h : R06_leaf_obligations) {z : ℂ}
    (hx0 : R06.x0 ≤ z.re) (hx1 : z.re ≤ R06.x1)
    (hy0 : R06.y0 ≤ z.im) (hy1 : z.im ≤ R06.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R06 0.15 0.06
      R06_strip_lo R06_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R06_H_instance (h : R06_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (0, 2.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R06, 0.15, 0.06, rfl, rfl, rfl, rfl, R06_strip_lo, R06_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

#print axioms R06_H_instance

/-! ### R07 = (2,4.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- Bottom-row cell `(2,4.5) × (0.01,0.2)` (center `3.25`, mid tier). -/
def R07 : CellProofEngine.Rect2D :=
  ⟨2, 4.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R07_x0 : R07.x0 = 2 := rfl
theorem R07_x1 : R07.x1 = 4.5 := rfl
theorem R07_y0 : R07.y0 = 0.01 := rfl
theorem R07_y1 : R07.y1 = 0.2 := rfl

theorem R07_width_eq : R07.x1 - R07.x0 = 2.5 := by
  rw [R07_x0, R07_x1]; norm_num

theorem R07_strip_lo : -(1 / 2 : ℝ) < R07.y0 := by rw [R07_y0]; norm_num
theorem R07_strip_hi : R07.y1 < (1 / 2 : ℝ) := by rw [R07_y1]; norm_num

theorem R07_dx_eq : R07.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R07_x0, R07_x1]; norm_num

theorem R07_dy_eq : R07.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R07_y0, R07_y1]; norm_num

theorem R07_radius_eq :
    R07.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R07_dx_eq, R07_dy_eq]

theorem R07_radius_lt : R07.radius < 1.26 := by
  rw [R07_radius_eq]; exact sample_cell_radius_bound

theorem R07_mem_gridFine :
    ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((2, 4.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(2, 4.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R07` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R07_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R07.radius ≤ ‖xiShifted R07.center‖) ∧
  (∀ w, R07.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R07_fencing_of_bounds (h : R07_leaf_obligations) :
    CellFencingHypotheses R07 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R07_lowerBound_of_bounds (h : R07_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R07 0.05 0.07
    R07_strip_lo R07_strip_hi (R07_fencing_of_bounds h)

noncomputable def R07_zeroFree_of_bounds (h : R07_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R07 0.05 fine_eps_mid_pos 0.07
    R07_strip_lo R07_strip_hi h.2 h.1

theorem R07_nonvanishing_of_bounds (h : R07_leaf_obligations) {z : ℂ}
    (hx0 : R07.x0 ≤ z.re) (hx1 : z.re ≤ R07.x1)
    (hy0 : R07.y0 ≤ z.im) (hy1 : z.im ≤ R07.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R07 0.05 0.07
      R07_strip_lo R07_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R07_H_instance (h : R07_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (2, 4.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R07, 0.05, 0.07, rfl, rfl, rfl, rfl, R07_strip_lo, R07_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

#print axioms R07_H_instance

/-! ### R08 = (4,6.5,0.01,0.2), mid tier `(0.05,0.07)` -/

/-- Bottom-row cell `(4,6.5) × (0.01,0.2)` (center `5.25`, mid tier). -/
def R08 : CellProofEngine.Rect2D :=
  ⟨4, 6.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R08_x0 : R08.x0 = 4 := rfl
theorem R08_x1 : R08.x1 = 6.5 := rfl
theorem R08_y0 : R08.y0 = 0.01 := rfl
theorem R08_y1 : R08.y1 = 0.2 := rfl

theorem R08_width_eq : R08.x1 - R08.x0 = 2.5 := by
  rw [R08_x0, R08_x1]; norm_num

theorem R08_strip_lo : -(1 / 2 : ℝ) < R08.y0 := by rw [R08_y0]; norm_num
theorem R08_strip_hi : R08.y1 < (1 / 2 : ℝ) := by rw [R08_y1]; norm_num

theorem R08_dx_eq : R08.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R08_x0, R08_x1]; norm_num

theorem R08_dy_eq : R08.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R08_y0, R08_y1]; norm_num

theorem R08_radius_eq :
    R08.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R08_dx_eq, R08_dy_eq]

theorem R08_radius_lt : R08.radius < 1.26 := by
  rw [R08_radius_eq]; exact sample_cell_radius_bound

theorem R08_mem_gridFine :
    ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((4, 6.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(4, 6.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R08` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R08_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R08.radius ≤ ‖xiShifted R08.center‖) ∧
  (∀ w, R08.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R08_fencing_of_bounds (h : R08_leaf_obligations) :
    CellFencingHypotheses R08 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R08_lowerBound_of_bounds (h : R08_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R08 0.05 0.07
    R08_strip_lo R08_strip_hi (R08_fencing_of_bounds h)

noncomputable def R08_zeroFree_of_bounds (h : R08_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R08 0.05 fine_eps_mid_pos 0.07
    R08_strip_lo R08_strip_hi h.2 h.1

theorem R08_nonvanishing_of_bounds (h : R08_leaf_obligations) {z : ℂ}
    (hx0 : R08.x0 ≤ z.re) (hx1 : z.re ≤ R08.x1)
    (hy0 : R08.y0 ≤ z.im) (hy1 : z.im ≤ R08.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R08 0.05 0.07
      R08_strip_lo R08_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R08_H_instance (h : R08_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (4, 6.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R08, 0.05, 0.07, rfl, rfl, rfl, rfl, R08_strip_lo, R08_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

#print axioms R08_H_instance

/-! ### R09 = (6,8.5,0.01,0.2), outer tier `(0.002,0.05)` -/

/-- Bottom-row cell `(6,8.5) × (0.01,0.2)` (center `7.25`, outer tier). -/
def R09 : CellProofEngine.Rect2D :=
  ⟨6, 8.5, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R09_x0 : R09.x0 = 6 := rfl
theorem R09_x1 : R09.x1 = 8.5 := rfl
theorem R09_y0 : R09.y0 = 0.01 := rfl
theorem R09_y1 : R09.y1 = 0.2 := rfl

theorem R09_width_eq : R09.x1 - R09.x0 = 2.5 := by
  rw [R09_x0, R09_x1]; norm_num

theorem R09_strip_lo : -(1 / 2 : ℝ) < R09.y0 := by rw [R09_y0]; norm_num
theorem R09_strip_hi : R09.y1 < (1 / 2 : ℝ) := by rw [R09_y1]; norm_num

theorem R09_dx_eq : R09.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R09_x0, R09_x1]; norm_num

theorem R09_dy_eq : R09.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R09_y0, R09_y1]; norm_num

theorem R09_radius_eq :
    R09.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R09_dx_eq, R09_dy_eq]

theorem R09_radius_lt : R09.radius < 1.26 := by
  rw [R09_radius_eq]; exact sample_cell_radius_bound

theorem R09_mem_gridFine :
    ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((6, 8.5) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(6, 8.5), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R09` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R09_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R09.radius ≤ ‖xiShifted R09.center‖) ∧
  (∀ w, R09.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R09_fencing_of_bounds (h : R09_leaf_obligations) :
    CellFencingHypotheses R09 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R09_lowerBound_of_bounds (h : R09_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R09 0.002 0.05
    R09_strip_lo R09_strip_hi (R09_fencing_of_bounds h)

noncomputable def R09_zeroFree_of_bounds (h : R09_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R09 0.002 fine_eps_outer_pos 0.05
    R09_strip_lo R09_strip_hi h.2 h.1

theorem R09_nonvanishing_of_bounds (h : R09_leaf_obligations) {z : ℂ}
    (hx0 : R09.x0 ≤ z.re) (hx1 : z.re ≤ R09.x1)
    (hy0 : R09.y0 ≤ z.im) (hy1 : z.im ≤ R09.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R09 0.002 0.05
      R09_strip_lo R09_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R09_H_instance (h : R09_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (6, 8.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R09, 0.002, 0.05, rfl, rfl, rfl, rfl, R09_strip_lo, R09_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

#print axioms R09_H_instance

/-! ### R10 = (7.5,10,0.01,0.2), outer tier `(0.002,0.05)` -/

/-- Bottom-row cell `(7.5,10) × (0.01,0.2)` (center `8.75`, outer tier). -/
def R10 : CellProofEngine.Rect2D :=
  ⟨7.5, 10, 0.01, 0.2, by norm_num, by norm_num⟩

theorem R10_x0 : R10.x0 = 7.5 := rfl
theorem R10_x1 : R10.x1 = 10 := rfl
theorem R10_y0 : R10.y0 = 0.01 := rfl
theorem R10_y1 : R10.y1 = 0.2 := rfl

theorem R10_width_eq : R10.x1 - R10.x0 = 2.5 := by
  rw [R10_x0, R10_x1]; norm_num

theorem R10_strip_lo : -(1 / 2 : ℝ) < R10.y0 := by rw [R10_y0]; norm_num
theorem R10_strip_hi : R10.y1 < (1 / 2 : ℝ) := by rw [R10_y1]; norm_num

theorem R10_dx_eq : R10.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R10_x0, R10_x1]; norm_num

theorem R10_dy_eq : R10.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R10_y0, R10_y1]; norm_num

theorem R10_radius_eq :
    R10.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R10_dx_eq, R10_dy_eq]

theorem R10_radius_lt : R10.radius < 1.26 := by
  rw [R10_radius_eq]; exact sample_cell_radius_bound

theorem R10_mem_gridFine :
    ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : ((7.5, 10) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : ((0.01, 0.2) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(7.5, 10), hX, List.mem_map.mpr ⟨(0.01, 0.2), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R10` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R10_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R10.radius ≤ ‖xiShifted R10.center‖) ∧
  (∀ w, R10.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R10_fencing_of_bounds (h : R10_leaf_obligations) :
    CellFencingHypotheses R10 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R10_lowerBound_of_bounds (h : R10_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R10 0.002 0.05
    R10_strip_lo R10_strip_hi (R10_fencing_of_bounds h)

noncomputable def R10_zeroFree_of_bounds (h : R10_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R10 0.002 fine_eps_outer_pos 0.05
    R10_strip_lo R10_strip_hi h.2 h.1

theorem R10_nonvanishing_of_bounds (h : R10_leaf_obligations) {z : ℂ}
    (hx0 : R10.x0 ≤ z.re) (hx1 : z.re ≤ R10.x1)
    (hy0 : R10.y0 ≤ z.im) (hy1 : z.im ≤ R10.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R10 0.002 0.05
      R10_strip_lo R10_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R10_H_instance (h : R10_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (7.5, 10, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R10, 0.002, 0.05, rfl, rfl, rfl, rfl, R10_strip_lo, R10_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

#print axioms R10_H_instance

/-! ### Boundary strip `(0,0.01]` via the designated nonzero-base feeder -/

/-- Per-`x` strip obligations for the designated feeder
`BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base` applied to
the entire extension: base lower bound at `(x:ℂ)`, vertical deriv bound on
`Icc 0 0.02`, and the margin `0.01 < ε₀/M₁` so the whole `(0,0.01]` is fenced.
Taken as explicit hypotheses, exactly like the per-cell leaves. -/
def StripBaseBounds (x : ℝ) (ε0 M1 : ℝ) : Prop :=
  0 < ε0 ∧ 0 < M1 ∧
  ε0 ≤ ‖xiShiftedEntire (x : ℂ)‖ ∧
  (∀ y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ),
    ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ M1) ∧
  (0.01 : ℝ) < ε0 / M1

/-- Global strip obligations over the whole bottom-row footprint. -/
def BottomStripObligations : Prop :=
  ∀ x : ℝ, -10 < x → x < 10 → ∃ ε0 M1 : ℝ, StripBaseBounds x ε0 M1

/-- Pointwise strip fencing: obligations at `x = z.re` give `xiShifted z ≠ 0`
for `0 < Im ≤ 0.01`, via the nonzero-base feeder on `xiShiftedEntire` plus
strip agreement `xiShifted_eq_entire_on_strip`. -/
theorem strip_nonvanishing_of_base_bounds {x : ℝ} {ε0 M1 : ℝ}
    (hb : StripBaseBounds x ε0 M1)
    {z : ℂ} (hz_re : z.re = x) (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.01) :
    xiShifted z ≠ 0 := by
  obtain ⟨hε0, hM1, hbase, hderiv, hmargin⟩ := hb
  have hy_eta : z.im < (0.02 : ℝ) := by linarith
  have hy_margin : z.im < ε0 / M1 := lt_of_le_of_lt hy_le hmargin
  have hz_eq : z = (x : ℂ) + Complex.I * ((z.im : ℝ) : ℂ) := by
    have h := Complex.re_add_im z
    rw [hz_re] at h
    have hcomm : Complex.I * ((z.im : ℝ) : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
      ring
    rw [hcomm]
    exact h.symm
  have hEnt_base : xiShiftedEntire ((x : ℂ) + Complex.I * ((z.im : ℝ) : ℂ)) ≠ 0 :=
    BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base
      xiShiftedEntire xiShiftedEntire_differentiable x ε0 M1 0.02
      hε0 hM1 (by norm_num) hbase hderiv z.im hy_pos hy_eta hy_margin
  have hEnt_z : xiShiftedEntire z ≠ 0 := by
    rwa [← hz_eq] at hEnt_base
  have hStripLo : -(1 / 2 : ℝ) < z.im := by linarith
  have hStripHi : z.im < (1 / 2 : ℝ) := by linarith
  have hAgree : xiShifted z = xiShiftedEntire z :=
    xiShifted_eq_entire_on_strip z hStripLo hStripHi
  rw [hAgree]
  exact hEnt_z

/-- Strip assembly over `-10 < Re < 10`: obligations supply the per-`x` bounds. -/
theorem bottom_strip_covered (hStrip : BottomStripObligations) {z : ℂ}
    (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.01) :
    xiShifted z ≠ 0 := by
  obtain ⟨ε0, M1, hb⟩ := hStrip z.re hx_lo hx_hi
  exact strip_nonvanishing_of_base_bounds hb rfl hy_pos hy_le

#print axioms bottom_strip_covered

/-! ### Bottom-row list, combinatorial either/or, and combined cover -/

/-- The 10 `gridFine` bottom-row cells `y ∈ (0.01,0.2)`. -/
def bottomRowCells : List (ℝ × ℝ × ℝ × ℝ) :=
  [(-10, -7.5, 0.01, 0.2), (-8, -5.5, 0.01, 0.2), (-6, -3.5, 0.01, 0.2),
   (-4, -1.5, 0.01, 0.2), (-2, 0.5, 0.01, 0.2), (0, 2.5, 0.01, 0.2),
   (2, 4.5, 0.01, 0.2), (4, 6.5, 0.01, 0.2), (6, 8.5, 0.01, 0.2),
   (7.5, 10, 0.01, 0.2)]

/-- Every bottom-row cell lies in `gridFine`. -/
theorem bottomRow_mem_gridFine_of_mem {c : ℝ × ℝ × ℝ × ℝ}
    (hc : c ∈ bottomRowCells) : c ∈ gridFine := by
  unfold bottomRowCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R00_mem_gridFine
  · exact R02_mem_gridFine
  · exact R03_mem_gridFine
  · exact R04_mem_gridFine
  · exact R05_mem_gridFine
  · exact R06_mem_gridFine
  · exact R07_mem_gridFine
  · exact R08_mem_gridFine
  · exact R09_mem_gridFine
  · exact R10_mem_gridFine

/-- Pure combinatorics: every `(x,y)` with `-10 < x < 10`, `0 < y ≤ 0.2` is
either strip-range (`y ≤ 0.01`) or lies closed in some bottom-row cell. The
`x`-branching mirrors `fineGridX_covers` thresholds, so each branch's closed
`x`-bounds follow by `linarith`. -/
theorem bottom_row_either {x y : ℝ}
    (hx_lo : -10 < x) (hx_hi : x < 10)
    (hy_pos : 0 < y) (hy_le : y ≤ 0.2) :
    y ≤ 0.01 ∨
    ∃ c ∈ bottomRowCells,
      c.1 ≤ x ∧ x ≤ c.2.1 ∧ c.2.2.1 ≤ y ∧ y ≤ c.2.2.2 := by
  by_cases h : y ≤ 0.01
  · exact Or.inl h
  · right
    push_neg at h
    have hy0 : (0.01 : ℝ) ≤ y := le_of_lt h
    by_cases h1 : x < -7.5
    · exact ⟨(-10, -7.5, 0.01, 0.2), by simp [bottomRowCells],
        by show (-10 : ℝ) ≤ x; linarith, by show x ≤ (-7.5 : ℝ); exact le_of_lt h1,
        hy0, hy_le⟩
    · push_neg at h1
      by_cases h2 : x < -5.5
      · exact ⟨(-8, -5.5, 0.01, 0.2), by simp [bottomRowCells],
          by show (-8 : ℝ) ≤ x; linarith, by show x ≤ (-5.5 : ℝ); exact le_of_lt h2,
          hy0, hy_le⟩
      · push_neg at h2
        by_cases h3 : x < -3.5
        · exact ⟨(-6, -3.5, 0.01, 0.2), by simp [bottomRowCells],
            by show (-6 : ℝ) ≤ x; linarith, by show x ≤ (-3.5 : ℝ); exact le_of_lt h3,
            hy0, hy_le⟩
        · push_neg at h3
          by_cases h4 : x < -1.5
          · exact ⟨(-4, -1.5, 0.01, 0.2), by simp [bottomRowCells],
              by show (-4 : ℝ) ≤ x; linarith, by show x ≤ (-1.5 : ℝ); exact le_of_lt h4,
              hy0, hy_le⟩
          · push_neg at h4
            by_cases h5 : x < 0.5
            · exact ⟨(-2, 0.5, 0.01, 0.2), by simp [bottomRowCells],
                by show (-2 : ℝ) ≤ x; linarith, by show x ≤ (0.5 : ℝ); exact le_of_lt h5,
                hy0, hy_le⟩
            · push_neg at h5
              by_cases h6 : x < 2.5
              · exact ⟨(0, 2.5, 0.01, 0.2), by simp [bottomRowCells],
                  by show (0 : ℝ) ≤ x; linarith, by show x ≤ (2.5 : ℝ); exact le_of_lt h6,
                  hy0, hy_le⟩
              · push_neg at h6
                by_cases h7 : x < 4.5
                · exact ⟨(2, 4.5, 0.01, 0.2), by simp [bottomRowCells],
                    by show (2 : ℝ) ≤ x; linarith, by show x ≤ (4.5 : ℝ); exact le_of_lt h7,
                    hy0, hy_le⟩
                · push_neg at h7
                  by_cases h8 : x < 6.5
                  · exact ⟨(4, 6.5, 0.01, 0.2), by simp [bottomRowCells],
                      by show (4 : ℝ) ≤ x; linarith, by show x ≤ (6.5 : ℝ); exact le_of_lt h8,
                      hy0, hy_le⟩
                  · push_neg at h8
                    by_cases h9 : x < 8.5
                    · exact ⟨(6, 8.5, 0.01, 0.2), by simp [bottomRowCells],
                        by show (6 : ℝ) ≤ x; linarith, by show x ≤ (8.5 : ℝ); exact le_of_lt h9,
                        hy0, hy_le⟩
                    · push_neg at h9
                      exact ⟨(7.5, 10, 0.01, 0.2), by simp [bottomRowCells],
                        by show (7.5 : ℝ) ≤ x; linarith,
                        by show x ≤ (10 : ℝ); exact le_of_lt hx_hi,
                        hy0, hy_le⟩

/-- Joint per-cell obligations for the 10 `gridFine` bottom-row cells. -/
def BottomRowObligations : Prop :=
  R00_leaf_obligations ∧ R02_leaf_obligations ∧ R03_leaf_obligations ∧
  R04_leaf_obligations ∧ R05_leaf_obligations ∧ R06_leaf_obligations ∧
  R07_leaf_obligations ∧ R08_leaf_obligations ∧ R09_leaf_obligations ∧
  R10_leaf_obligations

/-- The 10 bottom-row `H`-leaves of `inner_nonvanishing_of_fenced_grid_fine`
follow jointly from `BottomRowObligations`. -/
theorem bottomRow_H_of_obligations (hCells : BottomRowObligations) :
    ∀ c ∈ bottomRowCells, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  intro c hc
  unfold bottomRowCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h00, _, _, _, _, _, _, _, _, _⟩ := hCells
    exact R00_H_instance h00 _ R00_mem_gridFine rfl
  · obtain ⟨_, h02, _, _, _, _, _, _, _, _⟩ := hCells
    exact R02_H_instance h02 _ R02_mem_gridFine rfl
  · obtain ⟨_, _, h03, _, _, _, _, _, _, _⟩ := hCells
    exact R03_H_instance h03 _ R03_mem_gridFine rfl
  · obtain ⟨_, _, _, h04, _, _, _, _, _, _⟩ := hCells
    exact R04_H_instance h04 _ R04_mem_gridFine rfl
  · obtain ⟨_, _, _, _, h05, _, _, _, _, _⟩ := hCells
    exact R05_H_instance h05 _ R05_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, h06, _, _, _, _⟩ := hCells
    exact R06_H_instance h06 _ R06_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, h07, _, _, _⟩ := hCells
    exact R07_H_instance h07 _ R07_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, h08, _, _⟩ := hCells
    exact R08_H_instance h08 _ R08_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, h09, _⟩ := hCells
    exact R09_H_instance h09 _ R09_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, h10⟩ := hCells
    exact R10_H_instance h10 _ R10_mem_gridFine rfl

/-- Combined bottom-row cover: every `z` with `-10 < Re < 10`, `0 < Im ≤ 0.2`
is nonvanishing — via the strip lemma at `Im ≤ 0.01`, else via the closed
bottom-row cell containing it. The `either/or` is `bottom_row_either`; each
branch closes by the matching `RXX_nonvanishing_of_bounds`. -/
theorem bottom_row_covered (hCells : BottomRowObligations)
    (hStrip : BottomStripObligations)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.2) :
    xiShifted z ≠ 0 := by
  by_cases hS : z.im ≤ 0.01
  · exact bottom_strip_covered hStrip hx_lo hx_hi hy_pos hS
  · push_neg at hS
    obtain ⟨h00, h02, h03, h04, h05, h06, h07, h08, h09, h10⟩ := hCells
    have hy0 : (0.01 : ℝ) ≤ z.im := le_of_lt hS
    by_cases h1 : z.re < -7.5
    · exact R00_nonvanishing_of_bounds h00
        (by rw [R00_x0]; linarith) (by rw [R00_x1]; exact le_of_lt h1)
        (by rw [R00_y0]; exact hy0) (by rw [R00_y1]; exact hy_le)
    · push_neg at h1
      by_cases h2 : z.re < -5.5
      · exact R02_nonvanishing_of_bounds h02
          (by rw [R02_x0]; linarith) (by rw [R02_x1]; exact le_of_lt h2)
          (by rw [R02_y0]; exact hy0) (by rw [R02_y1]; exact hy_le)
      · push_neg at h2
        by_cases h3 : z.re < -3.5
        · exact R03_nonvanishing_of_bounds h03
            (by rw [R03_x0]; linarith) (by rw [R03_x1]; exact le_of_lt h3)
            (by rw [R03_y0]; exact hy0) (by rw [R03_y1]; exact hy_le)
        · push_neg at h3
          by_cases h4 : z.re < -1.5
          · exact R04_nonvanishing_of_bounds h04
              (by rw [R04_x0]; linarith) (by rw [R04_x1]; exact le_of_lt h4)
              (by rw [R04_y0]; exact hy0) (by rw [R04_y1]; exact hy_le)
          · push_neg at h4
            by_cases h5 : z.re < 0.5
            · exact R05_nonvanishing_of_bounds h05
                (by rw [R05_x0]; linarith) (by rw [R05_x1]; exact le_of_lt h5)
                (by rw [R05_y0]; exact hy0) (by rw [R05_y1]; exact hy_le)
            · push_neg at h5
              by_cases h6 : z.re < 2.5
              · exact R06_nonvanishing_of_bounds h06
                  (by rw [R06_x0]; linarith) (by rw [R06_x1]; exact le_of_lt h6)
                  (by rw [R06_y0]; exact hy0) (by rw [R06_y1]; exact hy_le)
              · push_neg at h6
                by_cases h7 : z.re < 4.5
                · exact R07_nonvanishing_of_bounds h07
                    (by rw [R07_x0]; linarith) (by rw [R07_x1]; exact le_of_lt h7)
                    (by rw [R07_y0]; exact hy0) (by rw [R07_y1]; exact hy_le)
                · push_neg at h7
                  by_cases h8 : z.re < 6.5
                  · exact R08_nonvanishing_of_bounds h08
                      (by rw [R08_x0]; linarith) (by rw [R08_x1]; exact le_of_lt h8)
                      (by rw [R08_y0]; exact hy0) (by rw [R08_y1]; exact hy_le)
                  · push_neg at h8
                    by_cases h9 : z.re < 8.5
                    · exact R09_nonvanishing_of_bounds h09
                        (by rw [R09_x0]; linarith) (by rw [R09_x1]; exact le_of_lt h9)
                        (by rw [R09_y0]; exact hy0) (by rw [R09_y1]; exact hy_le)
                    · push_neg at h9
                      exact R10_nonvanishing_of_bounds h10
                        (by rw [R10_x0]; linarith)
                        (by rw [R10_x1]; exact le_of_lt hx_hi)
                        (by rw [R10_y0]; exact hy0) (by rw [R10_y1]; exact hy_le)

#print axioms bottom_row_either
#print axioms bottom_row_covered
#print axioms bottomRow_H_of_obligations
#print axioms strip_nonvanishing_of_base_bounds

end CentralCoverAssembly

namespace CentralCoverAssembly

open CellProofEngine

/-! ## Upper-row completion R11--R40 + `full_central_covered` (EXPANDED scope)

Prior sessions packaged the 10 bottom-row `gridFine` cells `y \in (0.01,0.2)`
(`R00`, `R02`--`R10`) plus the boundary strip `(0,0.01]` into `bottom_row_covered`.
This block replicates the same `RXX` fencing pattern at scale for ALL upper-row
cells `y \in (0.1,0.49)` (the remaining 30 cells of `gridFine`: 10 `x`-columns
× 3 `y`-rows `(0.1,0.3)`, `(0.2,0.4)`, `(0.3,0.49)`), using the tier bounds
already in-file (`fine_eps_outer/mid/inner_pos`, `fine_M_outer/mid/nonneg`).
The two numerical enclosures per cell (`center_bound`, `deriv_bound`) are taken
as explicit per-cell hypotheses exactly as `R00_leaf_obligations` does (known
gap: needs zeta/Gamma/cpow interval arithmetic absent from Mathlib). No `sorry`,
no `admit`, no `axiom`. Endpoints `±10`, `[0.49,1/2)`, and the real axis are
untouched (separate tasks).
-/

/-- Radius bound for upper-row geometry `(dx, dy) = (1.25, 0.1)`:
`√(1.25²+0.1²) < 1.26`. Pure `Real` arithmetic. -/
theorem sample_cell_radius_01_bound :
    Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) < 1.26 := by
  have hlt : (1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2 < (1.26 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

/-! ### Upper row1 `y = (0.1,0.3)`, `dy = 0.1` (10 cells) -/

/-! ### R11 = (-10, -7.5, 0.1, 0.3), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-10,-7.5) × (0.1,0.3)` (outer tier). -/
def R11 : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R11_x0 : R11.x0 = -10 := rfl
theorem R11_x1 : R11.x1 = -7.5 := rfl
theorem R11_y0 : R11.y0 = 0.1 := rfl
theorem R11_y1 : R11.y1 = 0.3 := rfl

theorem R11_width_eq : R11.x1 - R11.x0 = 2.5 := by
  rw [R11_x0, R11_x1]; norm_num

theorem R11_strip_lo : -(1 / 2 : ℝ) < R11.y0 := by rw [R11_y0]; norm_num
theorem R11_strip_hi : R11.y1 < (1 / 2 : ℝ) := by rw [R11_y1]; norm_num

theorem R11_dx_eq : R11.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R11_x0, R11_x1]; norm_num

theorem R11_dy_eq : R11.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R11_y0, R11_y1]; norm_num

theorem R11_radius_eq :
    R11.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R11_dx_eq, R11_dy_eq]

theorem R11_radius_lt : R11.radius < 1.26 := by
  rw [R11_radius_eq]; exact sample_cell_radius_01_bound

theorem R11_mem_gridFine :
    ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-10, -7.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-10, -7.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R11` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R11_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R11.radius ≤ ‖xiShifted R11.center‖) ∧
  (∀ w, R11.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R11_fencing_of_bounds (h : R11_leaf_obligations) :
    CellFencingHypotheses R11 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R11_lowerBound_of_bounds (h : R11_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R11 0.002 0.05
    R11_strip_lo R11_strip_hi (R11_fencing_of_bounds h)

noncomputable def R11_zeroFree_of_bounds (h : R11_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R11 0.002 fine_eps_outer_pos 0.05
    R11_strip_lo R11_strip_hi h.2 h.1

theorem R11_nonvanishing_of_bounds (h : R11_leaf_obligations) {z : ℂ}
    (hx0 : R11.x0 ≤ z.re) (hx1 : z.re ≤ R11.x1)
    (hy0 : R11.y0 ≤ z.im) (hy1 : z.im ≤ R11.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R11 0.002 0.05
      R11_strip_lo R11_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R11_H_instance (h : R11_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-10, -7.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R11, 0.002, 0.05, rfl, rfl, rfl, rfl, R11_strip_lo, R11_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R12 = (-8, -5.5, 0.1, 0.3), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-8,-5.5) × (0.1,0.3)` (outer tier). -/
def R12 : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R12_x0 : R12.x0 = -8 := rfl
theorem R12_x1 : R12.x1 = -5.5 := rfl
theorem R12_y0 : R12.y0 = 0.1 := rfl
theorem R12_y1 : R12.y1 = 0.3 := rfl

theorem R12_width_eq : R12.x1 - R12.x0 = 2.5 := by
  rw [R12_x0, R12_x1]; norm_num

theorem R12_strip_lo : -(1 / 2 : ℝ) < R12.y0 := by rw [R12_y0]; norm_num
theorem R12_strip_hi : R12.y1 < (1 / 2 : ℝ) := by rw [R12_y1]; norm_num

theorem R12_dx_eq : R12.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R12_x0, R12_x1]; norm_num

theorem R12_dy_eq : R12.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R12_y0, R12_y1]; norm_num

theorem R12_radius_eq :
    R12.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R12_dx_eq, R12_dy_eq]

theorem R12_radius_lt : R12.radius < 1.26 := by
  rw [R12_radius_eq]; exact sample_cell_radius_01_bound

theorem R12_mem_gridFine :
    ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-8, -5.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R12` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R12_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R12.radius ≤ ‖xiShifted R12.center‖) ∧
  (∀ w, R12.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R12_fencing_of_bounds (h : R12_leaf_obligations) :
    CellFencingHypotheses R12 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R12_lowerBound_of_bounds (h : R12_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R12 0.002 0.05
    R12_strip_lo R12_strip_hi (R12_fencing_of_bounds h)

noncomputable def R12_zeroFree_of_bounds (h : R12_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R12 0.002 fine_eps_outer_pos 0.05
    R12_strip_lo R12_strip_hi h.2 h.1

theorem R12_nonvanishing_of_bounds (h : R12_leaf_obligations) {z : ℂ}
    (hx0 : R12.x0 ≤ z.re) (hx1 : z.re ≤ R12.x1)
    (hy0 : R12.y0 ≤ z.im) (hy1 : z.im ≤ R12.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R12 0.002 0.05
      R12_strip_lo R12_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R12_H_instance (h : R12_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-8, -5.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R12, 0.002, 0.05, rfl, rfl, rfl, rfl, R12_strip_lo, R12_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R13 = (-6, -3.5, 0.1, 0.3), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-6,-3.5) × (0.1,0.3)` (mid tier). -/
def R13 : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R13_x0 : R13.x0 = -6 := rfl
theorem R13_x1 : R13.x1 = -3.5 := rfl
theorem R13_y0 : R13.y0 = 0.1 := rfl
theorem R13_y1 : R13.y1 = 0.3 := rfl

theorem R13_width_eq : R13.x1 - R13.x0 = 2.5 := by
  rw [R13_x0, R13_x1]; norm_num

theorem R13_strip_lo : -(1 / 2 : ℝ) < R13.y0 := by rw [R13_y0]; norm_num
theorem R13_strip_hi : R13.y1 < (1 / 2 : ℝ) := by rw [R13_y1]; norm_num

theorem R13_dx_eq : R13.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R13_x0, R13_x1]; norm_num

theorem R13_dy_eq : R13.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R13_y0, R13_y1]; norm_num

theorem R13_radius_eq :
    R13.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R13_dx_eq, R13_dy_eq]

theorem R13_radius_lt : R13.radius < 1.26 := by
  rw [R13_radius_eq]; exact sample_cell_radius_01_bound

theorem R13_mem_gridFine :
    ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-6, -3.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-6, -3.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R13` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R13_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R13.radius ≤ ‖xiShifted R13.center‖) ∧
  (∀ w, R13.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R13_fencing_of_bounds (h : R13_leaf_obligations) :
    CellFencingHypotheses R13 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R13_lowerBound_of_bounds (h : R13_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R13 0.05 0.07
    R13_strip_lo R13_strip_hi (R13_fencing_of_bounds h)

noncomputable def R13_zeroFree_of_bounds (h : R13_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R13 0.05 fine_eps_mid_pos 0.07
    R13_strip_lo R13_strip_hi h.2 h.1

theorem R13_nonvanishing_of_bounds (h : R13_leaf_obligations) {z : ℂ}
    (hx0 : R13.x0 ≤ z.re) (hx1 : z.re ≤ R13.x1)
    (hy0 : R13.y0 ≤ z.im) (hy1 : z.im ≤ R13.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R13 0.05 0.07
      R13_strip_lo R13_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R13_H_instance (h : R13_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-6, -3.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R13, 0.05, 0.07, rfl, rfl, rfl, rfl, R13_strip_lo, R13_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R14 = (-4, -1.5, 0.1, 0.3), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-4,-1.5) × (0.1,0.3)` (mid tier). -/
def R14 : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R14_x0 : R14.x0 = -4 := rfl
theorem R14_x1 : R14.x1 = -1.5 := rfl
theorem R14_y0 : R14.y0 = 0.1 := rfl
theorem R14_y1 : R14.y1 = 0.3 := rfl

theorem R14_width_eq : R14.x1 - R14.x0 = 2.5 := by
  rw [R14_x0, R14_x1]; norm_num

theorem R14_strip_lo : -(1 / 2 : ℝ) < R14.y0 := by rw [R14_y0]; norm_num
theorem R14_strip_hi : R14.y1 < (1 / 2 : ℝ) := by rw [R14_y1]; norm_num

theorem R14_dx_eq : R14.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R14_x0, R14_x1]; norm_num

theorem R14_dy_eq : R14.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R14_y0, R14_y1]; norm_num

theorem R14_radius_eq :
    R14.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R14_dx_eq, R14_dy_eq]

theorem R14_radius_lt : R14.radius < 1.26 := by
  rw [R14_radius_eq]; exact sample_cell_radius_01_bound

theorem R14_mem_gridFine :
    ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-4, -1.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-4, -1.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R14` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R14_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R14.radius ≤ ‖xiShifted R14.center‖) ∧
  (∀ w, R14.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R14_fencing_of_bounds (h : R14_leaf_obligations) :
    CellFencingHypotheses R14 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R14_lowerBound_of_bounds (h : R14_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R14 0.05 0.07
    R14_strip_lo R14_strip_hi (R14_fencing_of_bounds h)

noncomputable def R14_zeroFree_of_bounds (h : R14_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R14 0.05 fine_eps_mid_pos 0.07
    R14_strip_lo R14_strip_hi h.2 h.1

theorem R14_nonvanishing_of_bounds (h : R14_leaf_obligations) {z : ℂ}
    (hx0 : R14.x0 ≤ z.re) (hx1 : z.re ≤ R14.x1)
    (hy0 : R14.y0 ≤ z.im) (hy1 : z.im ≤ R14.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R14 0.05 0.07
      R14_strip_lo R14_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R14_H_instance (h : R14_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-4, -1.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R14, 0.05, 0.07, rfl, rfl, rfl, rfl, R14_strip_lo, R14_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R15 = (-2, 0.5, 0.1, 0.3), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(-2,0.5) × (0.1,0.3)` (inner tier). -/
def R15 : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R15_x0 : R15.x0 = -2 := rfl
theorem R15_x1 : R15.x1 = 0.5 := rfl
theorem R15_y0 : R15.y0 = 0.1 := rfl
theorem R15_y1 : R15.y1 = 0.3 := rfl

theorem R15_width_eq : R15.x1 - R15.x0 = 2.5 := by
  rw [R15_x0, R15_x1]; norm_num

theorem R15_strip_lo : -(1 / 2 : ℝ) < R15.y0 := by rw [R15_y0]; norm_num
theorem R15_strip_hi : R15.y1 < (1 / 2 : ℝ) := by rw [R15_y1]; norm_num

theorem R15_dx_eq : R15.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R15_x0, R15_x1]; norm_num

theorem R15_dy_eq : R15.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R15_y0, R15_y1]; norm_num

theorem R15_radius_eq :
    R15.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R15_dx_eq, R15_dy_eq]

theorem R15_radius_lt : R15.radius < 1.26 := by
  rw [R15_radius_eq]; exact sample_cell_radius_01_bound

theorem R15_mem_gridFine :
    ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-2, 0.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-2, 0.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R15` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R15_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R15.radius ≤ ‖xiShifted R15.center‖) ∧
  (∀ w, R15.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R15_fencing_of_bounds (h : R15_leaf_obligations) :
    CellFencingHypotheses R15 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R15_lowerBound_of_bounds (h : R15_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R15 0.15 0.06
    R15_strip_lo R15_strip_hi (R15_fencing_of_bounds h)

noncomputable def R15_zeroFree_of_bounds (h : R15_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R15 0.15 fine_eps_inner_pos 0.06
    R15_strip_lo R15_strip_hi h.2 h.1

theorem R15_nonvanishing_of_bounds (h : R15_leaf_obligations) {z : ℂ}
    (hx0 : R15.x0 ≤ z.re) (hx1 : z.re ≤ R15.x1)
    (hy0 : R15.y0 ≤ z.im) (hy1 : z.im ≤ R15.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R15 0.15 0.06
      R15_strip_lo R15_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R15_H_instance (h : R15_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-2, 0.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R15, 0.15, 0.06, rfl, rfl, rfl, rfl, R15_strip_lo, R15_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R16 = (0, 2.5, 0.1, 0.3), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(0,2.5) × (0.1,0.3)` (inner tier). -/
def R16 : CellProofEngine.Rect2D :=
  ⟨0, 2.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R16_x0 : R16.x0 = 0 := rfl
theorem R16_x1 : R16.x1 = 2.5 := rfl
theorem R16_y0 : R16.y0 = 0.1 := rfl
theorem R16_y1 : R16.y1 = 0.3 := rfl

theorem R16_width_eq : R16.x1 - R16.x0 = 2.5 := by
  rw [R16_x0, R16_x1]; norm_num

theorem R16_strip_lo : -(1 / 2 : ℝ) < R16.y0 := by rw [R16_y0]; norm_num
theorem R16_strip_hi : R16.y1 < (1 / 2 : ℝ) := by rw [R16_y1]; norm_num

theorem R16_dx_eq : R16.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R16_x0, R16_x1]; norm_num

theorem R16_dy_eq : R16.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R16_y0, R16_y1]; norm_num

theorem R16_radius_eq :
    R16.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R16_dx_eq, R16_dy_eq]

theorem R16_radius_lt : R16.radius < 1.26 := by
  rw [R16_radius_eq]; exact sample_cell_radius_01_bound

theorem R16_mem_gridFine :
    ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((0, 2.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(0, 2.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R16` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R16_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R16.radius ≤ ‖xiShifted R16.center‖) ∧
  (∀ w, R16.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R16_fencing_of_bounds (h : R16_leaf_obligations) :
    CellFencingHypotheses R16 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R16_lowerBound_of_bounds (h : R16_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R16 0.15 0.06
    R16_strip_lo R16_strip_hi (R16_fencing_of_bounds h)

noncomputable def R16_zeroFree_of_bounds (h : R16_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R16 0.15 fine_eps_inner_pos 0.06
    R16_strip_lo R16_strip_hi h.2 h.1

theorem R16_nonvanishing_of_bounds (h : R16_leaf_obligations) {z : ℂ}
    (hx0 : R16.x0 ≤ z.re) (hx1 : z.re ≤ R16.x1)
    (hy0 : R16.y0 ≤ z.im) (hy1 : z.im ≤ R16.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R16 0.15 0.06
      R16_strip_lo R16_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R16_H_instance (h : R16_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (0, 2.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R16, 0.15, 0.06, rfl, rfl, rfl, rfl, R16_strip_lo, R16_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R17 = (2, 4.5, 0.1, 0.3), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(2,4.5) × (0.1,0.3)` (mid tier). -/
def R17 : CellProofEngine.Rect2D :=
  ⟨2, 4.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R17_x0 : R17.x0 = 2 := rfl
theorem R17_x1 : R17.x1 = 4.5 := rfl
theorem R17_y0 : R17.y0 = 0.1 := rfl
theorem R17_y1 : R17.y1 = 0.3 := rfl

theorem R17_width_eq : R17.x1 - R17.x0 = 2.5 := by
  rw [R17_x0, R17_x1]; norm_num

theorem R17_strip_lo : -(1 / 2 : ℝ) < R17.y0 := by rw [R17_y0]; norm_num
theorem R17_strip_hi : R17.y1 < (1 / 2 : ℝ) := by rw [R17_y1]; norm_num

theorem R17_dx_eq : R17.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R17_x0, R17_x1]; norm_num

theorem R17_dy_eq : R17.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R17_y0, R17_y1]; norm_num

theorem R17_radius_eq :
    R17.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R17_dx_eq, R17_dy_eq]

theorem R17_radius_lt : R17.radius < 1.26 := by
  rw [R17_radius_eq]; exact sample_cell_radius_01_bound

theorem R17_mem_gridFine :
    ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((2, 4.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(2, 4.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R17` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R17_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R17.radius ≤ ‖xiShifted R17.center‖) ∧
  (∀ w, R17.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R17_fencing_of_bounds (h : R17_leaf_obligations) :
    CellFencingHypotheses R17 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R17_lowerBound_of_bounds (h : R17_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R17 0.05 0.07
    R17_strip_lo R17_strip_hi (R17_fencing_of_bounds h)

noncomputable def R17_zeroFree_of_bounds (h : R17_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R17 0.05 fine_eps_mid_pos 0.07
    R17_strip_lo R17_strip_hi h.2 h.1

theorem R17_nonvanishing_of_bounds (h : R17_leaf_obligations) {z : ℂ}
    (hx0 : R17.x0 ≤ z.re) (hx1 : z.re ≤ R17.x1)
    (hy0 : R17.y0 ≤ z.im) (hy1 : z.im ≤ R17.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R17 0.05 0.07
      R17_strip_lo R17_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R17_H_instance (h : R17_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (2, 4.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R17, 0.05, 0.07, rfl, rfl, rfl, rfl, R17_strip_lo, R17_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R18 = (4, 6.5, 0.1, 0.3), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(4,6.5) × (0.1,0.3)` (mid tier). -/
def R18 : CellProofEngine.Rect2D :=
  ⟨4, 6.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R18_x0 : R18.x0 = 4 := rfl
theorem R18_x1 : R18.x1 = 6.5 := rfl
theorem R18_y0 : R18.y0 = 0.1 := rfl
theorem R18_y1 : R18.y1 = 0.3 := rfl

theorem R18_width_eq : R18.x1 - R18.x0 = 2.5 := by
  rw [R18_x0, R18_x1]; norm_num

theorem R18_strip_lo : -(1 / 2 : ℝ) < R18.y0 := by rw [R18_y0]; norm_num
theorem R18_strip_hi : R18.y1 < (1 / 2 : ℝ) := by rw [R18_y1]; norm_num

theorem R18_dx_eq : R18.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R18_x0, R18_x1]; norm_num

theorem R18_dy_eq : R18.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R18_y0, R18_y1]; norm_num

theorem R18_radius_eq :
    R18.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R18_dx_eq, R18_dy_eq]

theorem R18_radius_lt : R18.radius < 1.26 := by
  rw [R18_radius_eq]; exact sample_cell_radius_01_bound

theorem R18_mem_gridFine :
    ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((4, 6.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(4, 6.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R18` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R18_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R18.radius ≤ ‖xiShifted R18.center‖) ∧
  (∀ w, R18.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R18_fencing_of_bounds (h : R18_leaf_obligations) :
    CellFencingHypotheses R18 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R18_lowerBound_of_bounds (h : R18_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R18 0.05 0.07
    R18_strip_lo R18_strip_hi (R18_fencing_of_bounds h)

noncomputable def R18_zeroFree_of_bounds (h : R18_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R18 0.05 fine_eps_mid_pos 0.07
    R18_strip_lo R18_strip_hi h.2 h.1

theorem R18_nonvanishing_of_bounds (h : R18_leaf_obligations) {z : ℂ}
    (hx0 : R18.x0 ≤ z.re) (hx1 : z.re ≤ R18.x1)
    (hy0 : R18.y0 ≤ z.im) (hy1 : z.im ≤ R18.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R18 0.05 0.07
      R18_strip_lo R18_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R18_H_instance (h : R18_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (4, 6.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R18, 0.05, 0.07, rfl, rfl, rfl, rfl, R18_strip_lo, R18_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R19 = (6, 8.5, 0.1, 0.3), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(6,8.5) × (0.1,0.3)` (outer tier). -/
def R19 : CellProofEngine.Rect2D :=
  ⟨6, 8.5, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R19_x0 : R19.x0 = 6 := rfl
theorem R19_x1 : R19.x1 = 8.5 := rfl
theorem R19_y0 : R19.y0 = 0.1 := rfl
theorem R19_y1 : R19.y1 = 0.3 := rfl

theorem R19_width_eq : R19.x1 - R19.x0 = 2.5 := by
  rw [R19_x0, R19_x1]; norm_num

theorem R19_strip_lo : -(1 / 2 : ℝ) < R19.y0 := by rw [R19_y0]; norm_num
theorem R19_strip_hi : R19.y1 < (1 / 2 : ℝ) := by rw [R19_y1]; norm_num

theorem R19_dx_eq : R19.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R19_x0, R19_x1]; norm_num

theorem R19_dy_eq : R19.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R19_y0, R19_y1]; norm_num

theorem R19_radius_eq :
    R19.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R19_dx_eq, R19_dy_eq]

theorem R19_radius_lt : R19.radius < 1.26 := by
  rw [R19_radius_eq]; exact sample_cell_radius_01_bound

theorem R19_mem_gridFine :
    ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((6, 8.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(6, 8.5), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R19` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R19_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R19.radius ≤ ‖xiShifted R19.center‖) ∧
  (∀ w, R19.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R19_fencing_of_bounds (h : R19_leaf_obligations) :
    CellFencingHypotheses R19 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R19_lowerBound_of_bounds (h : R19_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R19 0.002 0.05
    R19_strip_lo R19_strip_hi (R19_fencing_of_bounds h)

noncomputable def R19_zeroFree_of_bounds (h : R19_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R19 0.002 fine_eps_outer_pos 0.05
    R19_strip_lo R19_strip_hi h.2 h.1

theorem R19_nonvanishing_of_bounds (h : R19_leaf_obligations) {z : ℂ}
    (hx0 : R19.x0 ≤ z.re) (hx1 : z.re ≤ R19.x1)
    (hy0 : R19.y0 ≤ z.im) (hy1 : z.im ≤ R19.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R19 0.002 0.05
      R19_strip_lo R19_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R19_H_instance (h : R19_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (6, 8.5, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R19, 0.002, 0.05, rfl, rfl, rfl, rfl, R19_strip_lo, R19_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R20 = (7.5, 10, 0.1, 0.3), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(7.5,10) × (0.1,0.3)` (outer tier). -/
def R20 : CellProofEngine.Rect2D :=
  ⟨7.5, 10, 0.1, 0.3, by norm_num, by norm_num⟩

theorem R20_x0 : R20.x0 = 7.5 := rfl
theorem R20_x1 : R20.x1 = 10 := rfl
theorem R20_y0 : R20.y0 = 0.1 := rfl
theorem R20_y1 : R20.y1 = 0.3 := rfl

theorem R20_width_eq : R20.x1 - R20.x0 = 2.5 := by
  rw [R20_x0, R20_x1]; norm_num

theorem R20_strip_lo : -(1 / 2 : ℝ) < R20.y0 := by rw [R20_y0]; norm_num
theorem R20_strip_hi : R20.y1 < (1 / 2 : ℝ) := by rw [R20_y1]; norm_num

theorem R20_dx_eq : R20.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R20_x0, R20_x1]; norm_num

theorem R20_dy_eq : R20.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R20_y0, R20_y1]; norm_num

theorem R20_radius_eq :
    R20.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R20_dx_eq, R20_dy_eq]

theorem R20_radius_lt : R20.radius < 1.26 := by
  rw [R20_radius_eq]; exact sample_cell_radius_01_bound

theorem R20_mem_gridFine :
    ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((7.5, 10)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.1, 0.3)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(7.5, 10), hX, List.mem_map.mpr ⟨(0.1, 0.3), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R20` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R20_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R20.radius ≤ ‖xiShifted R20.center‖) ∧
  (∀ w, R20.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R20_fencing_of_bounds (h : R20_leaf_obligations) :
    CellFencingHypotheses R20 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R20_lowerBound_of_bounds (h : R20_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R20 0.002 0.05
    R20_strip_lo R20_strip_hi (R20_fencing_of_bounds h)

noncomputable def R20_zeroFree_of_bounds (h : R20_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R20 0.002 fine_eps_outer_pos 0.05
    R20_strip_lo R20_strip_hi h.2 h.1

theorem R20_nonvanishing_of_bounds (h : R20_leaf_obligations) {z : ℂ}
    (hx0 : R20.x0 ≤ z.re) (hx1 : z.re ≤ R20.x1)
    (hy0 : R20.y0 ≤ z.im) (hy1 : z.im ≤ R20.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R20 0.002 0.05
      R20_strip_lo R20_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R20_H_instance (h : R20_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (7.5, 10, 0.1, 0.3)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R20, 0.002, 0.05, rfl, rfl, rfl, rfl, R20_strip_lo, R20_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### Upper row2 `y = (0.2,0.4)`, `dy = 0.1` (10 cells) -/

/-! ### R21 = (-10, -7.5, 0.2, 0.4), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-10,-7.5) × (0.2,0.4)` (outer tier). -/
def R21 : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R21_x0 : R21.x0 = -10 := rfl
theorem R21_x1 : R21.x1 = -7.5 := rfl
theorem R21_y0 : R21.y0 = 0.2 := rfl
theorem R21_y1 : R21.y1 = 0.4 := rfl

theorem R21_width_eq : R21.x1 - R21.x0 = 2.5 := by
  rw [R21_x0, R21_x1]; norm_num

theorem R21_strip_lo : -(1 / 2 : ℝ) < R21.y0 := by rw [R21_y0]; norm_num
theorem R21_strip_hi : R21.y1 < (1 / 2 : ℝ) := by rw [R21_y1]; norm_num

theorem R21_dx_eq : R21.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R21_x0, R21_x1]; norm_num

theorem R21_dy_eq : R21.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R21_y0, R21_y1]; norm_num

theorem R21_radius_eq :
    R21.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R21_dx_eq, R21_dy_eq]

theorem R21_radius_lt : R21.radius < 1.26 := by
  rw [R21_radius_eq]; exact sample_cell_radius_01_bound

theorem R21_mem_gridFine :
    ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-10, -7.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-10, -7.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R21` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R21_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R21.radius ≤ ‖xiShifted R21.center‖) ∧
  (∀ w, R21.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R21_fencing_of_bounds (h : R21_leaf_obligations) :
    CellFencingHypotheses R21 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R21_lowerBound_of_bounds (h : R21_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R21 0.002 0.05
    R21_strip_lo R21_strip_hi (R21_fencing_of_bounds h)

noncomputable def R21_zeroFree_of_bounds (h : R21_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R21 0.002 fine_eps_outer_pos 0.05
    R21_strip_lo R21_strip_hi h.2 h.1

theorem R21_nonvanishing_of_bounds (h : R21_leaf_obligations) {z : ℂ}
    (hx0 : R21.x0 ≤ z.re) (hx1 : z.re ≤ R21.x1)
    (hy0 : R21.y0 ≤ z.im) (hy1 : z.im ≤ R21.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R21 0.002 0.05
      R21_strip_lo R21_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R21_H_instance (h : R21_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-10, -7.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R21, 0.002, 0.05, rfl, rfl, rfl, rfl, R21_strip_lo, R21_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R22 = (-8, -5.5, 0.2, 0.4), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-8,-5.5) × (0.2,0.4)` (outer tier). -/
def R22 : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R22_x0 : R22.x0 = -8 := rfl
theorem R22_x1 : R22.x1 = -5.5 := rfl
theorem R22_y0 : R22.y0 = 0.2 := rfl
theorem R22_y1 : R22.y1 = 0.4 := rfl

theorem R22_width_eq : R22.x1 - R22.x0 = 2.5 := by
  rw [R22_x0, R22_x1]; norm_num

theorem R22_strip_lo : -(1 / 2 : ℝ) < R22.y0 := by rw [R22_y0]; norm_num
theorem R22_strip_hi : R22.y1 < (1 / 2 : ℝ) := by rw [R22_y1]; norm_num

theorem R22_dx_eq : R22.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R22_x0, R22_x1]; norm_num

theorem R22_dy_eq : R22.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R22_y0, R22_y1]; norm_num

theorem R22_radius_eq :
    R22.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R22_dx_eq, R22_dy_eq]

theorem R22_radius_lt : R22.radius < 1.26 := by
  rw [R22_radius_eq]; exact sample_cell_radius_01_bound

theorem R22_mem_gridFine :
    ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-8, -5.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R22` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R22_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R22.radius ≤ ‖xiShifted R22.center‖) ∧
  (∀ w, R22.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R22_fencing_of_bounds (h : R22_leaf_obligations) :
    CellFencingHypotheses R22 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R22_lowerBound_of_bounds (h : R22_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R22 0.002 0.05
    R22_strip_lo R22_strip_hi (R22_fencing_of_bounds h)

noncomputable def R22_zeroFree_of_bounds (h : R22_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R22 0.002 fine_eps_outer_pos 0.05
    R22_strip_lo R22_strip_hi h.2 h.1

theorem R22_nonvanishing_of_bounds (h : R22_leaf_obligations) {z : ℂ}
    (hx0 : R22.x0 ≤ z.re) (hx1 : z.re ≤ R22.x1)
    (hy0 : R22.y0 ≤ z.im) (hy1 : z.im ≤ R22.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R22 0.002 0.05
      R22_strip_lo R22_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R22_H_instance (h : R22_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-8, -5.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R22, 0.002, 0.05, rfl, rfl, rfl, rfl, R22_strip_lo, R22_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R23 = (-6, -3.5, 0.2, 0.4), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-6,-3.5) × (0.2,0.4)` (mid tier). -/
def R23 : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R23_x0 : R23.x0 = -6 := rfl
theorem R23_x1 : R23.x1 = -3.5 := rfl
theorem R23_y0 : R23.y0 = 0.2 := rfl
theorem R23_y1 : R23.y1 = 0.4 := rfl

theorem R23_width_eq : R23.x1 - R23.x0 = 2.5 := by
  rw [R23_x0, R23_x1]; norm_num

theorem R23_strip_lo : -(1 / 2 : ℝ) < R23.y0 := by rw [R23_y0]; norm_num
theorem R23_strip_hi : R23.y1 < (1 / 2 : ℝ) := by rw [R23_y1]; norm_num

theorem R23_dx_eq : R23.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R23_x0, R23_x1]; norm_num

theorem R23_dy_eq : R23.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R23_y0, R23_y1]; norm_num

theorem R23_radius_eq :
    R23.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R23_dx_eq, R23_dy_eq]

theorem R23_radius_lt : R23.radius < 1.26 := by
  rw [R23_radius_eq]; exact sample_cell_radius_01_bound

theorem R23_mem_gridFine :
    ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-6, -3.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-6, -3.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R23` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R23_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R23.radius ≤ ‖xiShifted R23.center‖) ∧
  (∀ w, R23.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R23_fencing_of_bounds (h : R23_leaf_obligations) :
    CellFencingHypotheses R23 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R23_lowerBound_of_bounds (h : R23_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R23 0.05 0.07
    R23_strip_lo R23_strip_hi (R23_fencing_of_bounds h)

noncomputable def R23_zeroFree_of_bounds (h : R23_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R23 0.05 fine_eps_mid_pos 0.07
    R23_strip_lo R23_strip_hi h.2 h.1

theorem R23_nonvanishing_of_bounds (h : R23_leaf_obligations) {z : ℂ}
    (hx0 : R23.x0 ≤ z.re) (hx1 : z.re ≤ R23.x1)
    (hy0 : R23.y0 ≤ z.im) (hy1 : z.im ≤ R23.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R23 0.05 0.07
      R23_strip_lo R23_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R23_H_instance (h : R23_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-6, -3.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R23, 0.05, 0.07, rfl, rfl, rfl, rfl, R23_strip_lo, R23_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R24 = (-4, -1.5, 0.2, 0.4), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-4,-1.5) × (0.2,0.4)` (mid tier). -/
def R24 : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R24_x0 : R24.x0 = -4 := rfl
theorem R24_x1 : R24.x1 = -1.5 := rfl
theorem R24_y0 : R24.y0 = 0.2 := rfl
theorem R24_y1 : R24.y1 = 0.4 := rfl

theorem R24_width_eq : R24.x1 - R24.x0 = 2.5 := by
  rw [R24_x0, R24_x1]; norm_num

theorem R24_strip_lo : -(1 / 2 : ℝ) < R24.y0 := by rw [R24_y0]; norm_num
theorem R24_strip_hi : R24.y1 < (1 / 2 : ℝ) := by rw [R24_y1]; norm_num

theorem R24_dx_eq : R24.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R24_x0, R24_x1]; norm_num

theorem R24_dy_eq : R24.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R24_y0, R24_y1]; norm_num

theorem R24_radius_eq :
    R24.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R24_dx_eq, R24_dy_eq]

theorem R24_radius_lt : R24.radius < 1.26 := by
  rw [R24_radius_eq]; exact sample_cell_radius_01_bound

theorem R24_mem_gridFine :
    ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-4, -1.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-4, -1.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R24` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R24_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R24.radius ≤ ‖xiShifted R24.center‖) ∧
  (∀ w, R24.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R24_fencing_of_bounds (h : R24_leaf_obligations) :
    CellFencingHypotheses R24 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R24_lowerBound_of_bounds (h : R24_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R24 0.05 0.07
    R24_strip_lo R24_strip_hi (R24_fencing_of_bounds h)

noncomputable def R24_zeroFree_of_bounds (h : R24_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R24 0.05 fine_eps_mid_pos 0.07
    R24_strip_lo R24_strip_hi h.2 h.1

theorem R24_nonvanishing_of_bounds (h : R24_leaf_obligations) {z : ℂ}
    (hx0 : R24.x0 ≤ z.re) (hx1 : z.re ≤ R24.x1)
    (hy0 : R24.y0 ≤ z.im) (hy1 : z.im ≤ R24.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R24 0.05 0.07
      R24_strip_lo R24_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R24_H_instance (h : R24_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-4, -1.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R24, 0.05, 0.07, rfl, rfl, rfl, rfl, R24_strip_lo, R24_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R25 = (-2, 0.5, 0.2, 0.4), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(-2,0.5) × (0.2,0.4)` (inner tier). -/
def R25 : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R25_x0 : R25.x0 = -2 := rfl
theorem R25_x1 : R25.x1 = 0.5 := rfl
theorem R25_y0 : R25.y0 = 0.2 := rfl
theorem R25_y1 : R25.y1 = 0.4 := rfl

theorem R25_width_eq : R25.x1 - R25.x0 = 2.5 := by
  rw [R25_x0, R25_x1]; norm_num

theorem R25_strip_lo : -(1 / 2 : ℝ) < R25.y0 := by rw [R25_y0]; norm_num
theorem R25_strip_hi : R25.y1 < (1 / 2 : ℝ) := by rw [R25_y1]; norm_num

theorem R25_dx_eq : R25.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R25_x0, R25_x1]; norm_num

theorem R25_dy_eq : R25.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R25_y0, R25_y1]; norm_num

theorem R25_radius_eq :
    R25.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R25_dx_eq, R25_dy_eq]

theorem R25_radius_lt : R25.radius < 1.26 := by
  rw [R25_radius_eq]; exact sample_cell_radius_01_bound

theorem R25_mem_gridFine :
    ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-2, 0.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-2, 0.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R25` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R25_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R25.radius ≤ ‖xiShifted R25.center‖) ∧
  (∀ w, R25.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R25_fencing_of_bounds (h : R25_leaf_obligations) :
    CellFencingHypotheses R25 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R25_lowerBound_of_bounds (h : R25_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R25 0.15 0.06
    R25_strip_lo R25_strip_hi (R25_fencing_of_bounds h)

noncomputable def R25_zeroFree_of_bounds (h : R25_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R25 0.15 fine_eps_inner_pos 0.06
    R25_strip_lo R25_strip_hi h.2 h.1

theorem R25_nonvanishing_of_bounds (h : R25_leaf_obligations) {z : ℂ}
    (hx0 : R25.x0 ≤ z.re) (hx1 : z.re ≤ R25.x1)
    (hy0 : R25.y0 ≤ z.im) (hy1 : z.im ≤ R25.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R25 0.15 0.06
      R25_strip_lo R25_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R25_H_instance (h : R25_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-2, 0.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R25, 0.15, 0.06, rfl, rfl, rfl, rfl, R25_strip_lo, R25_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R26 = (0, 2.5, 0.2, 0.4), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(0,2.5) × (0.2,0.4)` (inner tier). -/
def R26 : CellProofEngine.Rect2D :=
  ⟨0, 2.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R26_x0 : R26.x0 = 0 := rfl
theorem R26_x1 : R26.x1 = 2.5 := rfl
theorem R26_y0 : R26.y0 = 0.2 := rfl
theorem R26_y1 : R26.y1 = 0.4 := rfl

theorem R26_width_eq : R26.x1 - R26.x0 = 2.5 := by
  rw [R26_x0, R26_x1]; norm_num

theorem R26_strip_lo : -(1 / 2 : ℝ) < R26.y0 := by rw [R26_y0]; norm_num
theorem R26_strip_hi : R26.y1 < (1 / 2 : ℝ) := by rw [R26_y1]; norm_num

theorem R26_dx_eq : R26.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R26_x0, R26_x1]; norm_num

theorem R26_dy_eq : R26.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R26_y0, R26_y1]; norm_num

theorem R26_radius_eq :
    R26.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R26_dx_eq, R26_dy_eq]

theorem R26_radius_lt : R26.radius < 1.26 := by
  rw [R26_radius_eq]; exact sample_cell_radius_01_bound

theorem R26_mem_gridFine :
    ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((0, 2.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(0, 2.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R26` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R26_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R26.radius ≤ ‖xiShifted R26.center‖) ∧
  (∀ w, R26.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R26_fencing_of_bounds (h : R26_leaf_obligations) :
    CellFencingHypotheses R26 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R26_lowerBound_of_bounds (h : R26_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R26 0.15 0.06
    R26_strip_lo R26_strip_hi (R26_fencing_of_bounds h)

noncomputable def R26_zeroFree_of_bounds (h : R26_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R26 0.15 fine_eps_inner_pos 0.06
    R26_strip_lo R26_strip_hi h.2 h.1

theorem R26_nonvanishing_of_bounds (h : R26_leaf_obligations) {z : ℂ}
    (hx0 : R26.x0 ≤ z.re) (hx1 : z.re ≤ R26.x1)
    (hy0 : R26.y0 ≤ z.im) (hy1 : z.im ≤ R26.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R26 0.15 0.06
      R26_strip_lo R26_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R26_H_instance (h : R26_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (0, 2.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R26, 0.15, 0.06, rfl, rfl, rfl, rfl, R26_strip_lo, R26_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R27 = (2, 4.5, 0.2, 0.4), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(2,4.5) × (0.2,0.4)` (mid tier). -/
def R27 : CellProofEngine.Rect2D :=
  ⟨2, 4.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R27_x0 : R27.x0 = 2 := rfl
theorem R27_x1 : R27.x1 = 4.5 := rfl
theorem R27_y0 : R27.y0 = 0.2 := rfl
theorem R27_y1 : R27.y1 = 0.4 := rfl

theorem R27_width_eq : R27.x1 - R27.x0 = 2.5 := by
  rw [R27_x0, R27_x1]; norm_num

theorem R27_strip_lo : -(1 / 2 : ℝ) < R27.y0 := by rw [R27_y0]; norm_num
theorem R27_strip_hi : R27.y1 < (1 / 2 : ℝ) := by rw [R27_y1]; norm_num

theorem R27_dx_eq : R27.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R27_x0, R27_x1]; norm_num

theorem R27_dy_eq : R27.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R27_y0, R27_y1]; norm_num

theorem R27_radius_eq :
    R27.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R27_dx_eq, R27_dy_eq]

theorem R27_radius_lt : R27.radius < 1.26 := by
  rw [R27_radius_eq]; exact sample_cell_radius_01_bound

theorem R27_mem_gridFine :
    ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((2, 4.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(2, 4.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R27` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R27_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R27.radius ≤ ‖xiShifted R27.center‖) ∧
  (∀ w, R27.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R27_fencing_of_bounds (h : R27_leaf_obligations) :
    CellFencingHypotheses R27 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R27_lowerBound_of_bounds (h : R27_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R27 0.05 0.07
    R27_strip_lo R27_strip_hi (R27_fencing_of_bounds h)

noncomputable def R27_zeroFree_of_bounds (h : R27_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R27 0.05 fine_eps_mid_pos 0.07
    R27_strip_lo R27_strip_hi h.2 h.1

theorem R27_nonvanishing_of_bounds (h : R27_leaf_obligations) {z : ℂ}
    (hx0 : R27.x0 ≤ z.re) (hx1 : z.re ≤ R27.x1)
    (hy0 : R27.y0 ≤ z.im) (hy1 : z.im ≤ R27.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R27 0.05 0.07
      R27_strip_lo R27_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R27_H_instance (h : R27_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (2, 4.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R27, 0.05, 0.07, rfl, rfl, rfl, rfl, R27_strip_lo, R27_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R28 = (4, 6.5, 0.2, 0.4), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(4,6.5) × (0.2,0.4)` (mid tier). -/
def R28 : CellProofEngine.Rect2D :=
  ⟨4, 6.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R28_x0 : R28.x0 = 4 := rfl
theorem R28_x1 : R28.x1 = 6.5 := rfl
theorem R28_y0 : R28.y0 = 0.2 := rfl
theorem R28_y1 : R28.y1 = 0.4 := rfl

theorem R28_width_eq : R28.x1 - R28.x0 = 2.5 := by
  rw [R28_x0, R28_x1]; norm_num

theorem R28_strip_lo : -(1 / 2 : ℝ) < R28.y0 := by rw [R28_y0]; norm_num
theorem R28_strip_hi : R28.y1 < (1 / 2 : ℝ) := by rw [R28_y1]; norm_num

theorem R28_dx_eq : R28.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R28_x0, R28_x1]; norm_num

theorem R28_dy_eq : R28.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R28_y0, R28_y1]; norm_num

theorem R28_radius_eq :
    R28.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R28_dx_eq, R28_dy_eq]

theorem R28_radius_lt : R28.radius < 1.26 := by
  rw [R28_radius_eq]; exact sample_cell_radius_01_bound

theorem R28_mem_gridFine :
    ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((4, 6.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(4, 6.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R28` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R28_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R28.radius ≤ ‖xiShifted R28.center‖) ∧
  (∀ w, R28.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R28_fencing_of_bounds (h : R28_leaf_obligations) :
    CellFencingHypotheses R28 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R28_lowerBound_of_bounds (h : R28_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R28 0.05 0.07
    R28_strip_lo R28_strip_hi (R28_fencing_of_bounds h)

noncomputable def R28_zeroFree_of_bounds (h : R28_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R28 0.05 fine_eps_mid_pos 0.07
    R28_strip_lo R28_strip_hi h.2 h.1

theorem R28_nonvanishing_of_bounds (h : R28_leaf_obligations) {z : ℂ}
    (hx0 : R28.x0 ≤ z.re) (hx1 : z.re ≤ R28.x1)
    (hy0 : R28.y0 ≤ z.im) (hy1 : z.im ≤ R28.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R28 0.05 0.07
      R28_strip_lo R28_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R28_H_instance (h : R28_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (4, 6.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R28, 0.05, 0.07, rfl, rfl, rfl, rfl, R28_strip_lo, R28_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R29 = (6, 8.5, 0.2, 0.4), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(6,8.5) × (0.2,0.4)` (outer tier). -/
def R29 : CellProofEngine.Rect2D :=
  ⟨6, 8.5, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R29_x0 : R29.x0 = 6 := rfl
theorem R29_x1 : R29.x1 = 8.5 := rfl
theorem R29_y0 : R29.y0 = 0.2 := rfl
theorem R29_y1 : R29.y1 = 0.4 := rfl

theorem R29_width_eq : R29.x1 - R29.x0 = 2.5 := by
  rw [R29_x0, R29_x1]; norm_num

theorem R29_strip_lo : -(1 / 2 : ℝ) < R29.y0 := by rw [R29_y0]; norm_num
theorem R29_strip_hi : R29.y1 < (1 / 2 : ℝ) := by rw [R29_y1]; norm_num

theorem R29_dx_eq : R29.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R29_x0, R29_x1]; norm_num

theorem R29_dy_eq : R29.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R29_y0, R29_y1]; norm_num

theorem R29_radius_eq :
    R29.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R29_dx_eq, R29_dy_eq]

theorem R29_radius_lt : R29.radius < 1.26 := by
  rw [R29_radius_eq]; exact sample_cell_radius_01_bound

theorem R29_mem_gridFine :
    ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((6, 8.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(6, 8.5), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R29` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R29_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R29.radius ≤ ‖xiShifted R29.center‖) ∧
  (∀ w, R29.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R29_fencing_of_bounds (h : R29_leaf_obligations) :
    CellFencingHypotheses R29 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R29_lowerBound_of_bounds (h : R29_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R29 0.002 0.05
    R29_strip_lo R29_strip_hi (R29_fencing_of_bounds h)

noncomputable def R29_zeroFree_of_bounds (h : R29_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R29 0.002 fine_eps_outer_pos 0.05
    R29_strip_lo R29_strip_hi h.2 h.1

theorem R29_nonvanishing_of_bounds (h : R29_leaf_obligations) {z : ℂ}
    (hx0 : R29.x0 ≤ z.re) (hx1 : z.re ≤ R29.x1)
    (hy0 : R29.y0 ≤ z.im) (hy1 : z.im ≤ R29.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R29 0.002 0.05
      R29_strip_lo R29_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R29_H_instance (h : R29_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (6, 8.5, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R29, 0.002, 0.05, rfl, rfl, rfl, rfl, R29_strip_lo, R29_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R30 = (7.5, 10, 0.2, 0.4), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(7.5,10) × (0.2,0.4)` (outer tier). -/
def R30 : CellProofEngine.Rect2D :=
  ⟨7.5, 10, 0.2, 0.4, by norm_num, by norm_num⟩

theorem R30_x0 : R30.x0 = 7.5 := rfl
theorem R30_x1 : R30.x1 = 10 := rfl
theorem R30_y0 : R30.y0 = 0.2 := rfl
theorem R30_y1 : R30.y1 = 0.4 := rfl

theorem R30_width_eq : R30.x1 - R30.x0 = 2.5 := by
  rw [R30_x0, R30_x1]; norm_num

theorem R30_strip_lo : -(1 / 2 : ℝ) < R30.y0 := by rw [R30_y0]; norm_num
theorem R30_strip_hi : R30.y1 < (1 / 2 : ℝ) := by rw [R30_y1]; norm_num

theorem R30_dx_eq : R30.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R30_x0, R30_x1]; norm_num

theorem R30_dy_eq : R30.dy = 0.1 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R30_y0, R30_y1]; norm_num

theorem R30_radius_eq :
    R30.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.1 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R30_dx_eq, R30_dy_eq]

theorem R30_radius_lt : R30.radius < 1.26 := by
  rw [R30_radius_eq]; exact sample_cell_radius_01_bound

theorem R30_mem_gridFine :
    ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((7.5, 10)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.2, 0.4)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(7.5, 10), hX, List.mem_map.mpr ⟨(0.2, 0.4), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R30` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R30_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R30.radius ≤ ‖xiShifted R30.center‖) ∧
  (∀ w, R30.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R30_fencing_of_bounds (h : R30_leaf_obligations) :
    CellFencingHypotheses R30 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R30_lowerBound_of_bounds (h : R30_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R30 0.002 0.05
    R30_strip_lo R30_strip_hi (R30_fencing_of_bounds h)

noncomputable def R30_zeroFree_of_bounds (h : R30_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R30 0.002 fine_eps_outer_pos 0.05
    R30_strip_lo R30_strip_hi h.2 h.1

theorem R30_nonvanishing_of_bounds (h : R30_leaf_obligations) {z : ℂ}
    (hx0 : R30.x0 ≤ z.re) (hx1 : z.re ≤ R30.x1)
    (hy0 : R30.y0 ≤ z.im) (hy1 : z.im ≤ R30.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R30 0.002 0.05
      R30_strip_lo R30_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R30_H_instance (h : R30_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (7.5, 10, 0.2, 0.4)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R30, 0.002, 0.05, rfl, rfl, rfl, rfl, R30_strip_lo, R30_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### Upper top `y = (0.3,0.49)`, `dy = 0.095` (10 cells) -/

/-! ### R31 = (-10, -7.5, 0.3, 0.49), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-10,-7.5) × (0.3,0.49)` (outer tier). -/
def R31 : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R31_x0 : R31.x0 = -10 := rfl
theorem R31_x1 : R31.x1 = -7.5 := rfl
theorem R31_y0 : R31.y0 = 0.3 := rfl
theorem R31_y1 : R31.y1 = 0.49 := rfl

theorem R31_width_eq : R31.x1 - R31.x0 = 2.5 := by
  rw [R31_x0, R31_x1]; norm_num

theorem R31_strip_lo : -(1 / 2 : ℝ) < R31.y0 := by rw [R31_y0]; norm_num
theorem R31_strip_hi : R31.y1 < (1 / 2 : ℝ) := by rw [R31_y1]; norm_num

theorem R31_dx_eq : R31.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R31_x0, R31_x1]; norm_num

theorem R31_dy_eq : R31.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R31_y0, R31_y1]; norm_num

theorem R31_radius_eq :
    R31.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R31_dx_eq, R31_dy_eq]

theorem R31_radius_lt : R31.radius < 1.26 := by
  rw [R31_radius_eq]; exact sample_cell_radius_bound

theorem R31_mem_gridFine :
    ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-10, -7.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-10, -7.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R31` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R31_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R31.radius ≤ ‖xiShifted R31.center‖) ∧
  (∀ w, R31.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R31_fencing_of_bounds (h : R31_leaf_obligations) :
    CellFencingHypotheses R31 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R31_lowerBound_of_bounds (h : R31_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R31 0.002 0.05
    R31_strip_lo R31_strip_hi (R31_fencing_of_bounds h)

noncomputable def R31_zeroFree_of_bounds (h : R31_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R31 0.002 fine_eps_outer_pos 0.05
    R31_strip_lo R31_strip_hi h.2 h.1

theorem R31_nonvanishing_of_bounds (h : R31_leaf_obligations) {z : ℂ}
    (hx0 : R31.x0 ≤ z.re) (hx1 : z.re ≤ R31.x1)
    (hy0 : R31.y0 ≤ z.im) (hy1 : z.im ≤ R31.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R31 0.002 0.05
      R31_strip_lo R31_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R31_H_instance (h : R31_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-10, -7.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R31, 0.002, 0.05, rfl, rfl, rfl, rfl, R31_strip_lo, R31_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R32 = (-8, -5.5, 0.3, 0.49), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(-8,-5.5) × (0.3,0.49)` (outer tier). -/
def R32 : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R32_x0 : R32.x0 = -8 := rfl
theorem R32_x1 : R32.x1 = -5.5 := rfl
theorem R32_y0 : R32.y0 = 0.3 := rfl
theorem R32_y1 : R32.y1 = 0.49 := rfl

theorem R32_width_eq : R32.x1 - R32.x0 = 2.5 := by
  rw [R32_x0, R32_x1]; norm_num

theorem R32_strip_lo : -(1 / 2 : ℝ) < R32.y0 := by rw [R32_y0]; norm_num
theorem R32_strip_hi : R32.y1 < (1 / 2 : ℝ) := by rw [R32_y1]; norm_num

theorem R32_dx_eq : R32.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R32_x0, R32_x1]; norm_num

theorem R32_dy_eq : R32.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R32_y0, R32_y1]; norm_num

theorem R32_radius_eq :
    R32.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R32_dx_eq, R32_dy_eq]

theorem R32_radius_lt : R32.radius < 1.26 := by
  rw [R32_radius_eq]; exact sample_cell_radius_bound

theorem R32_mem_gridFine :
    ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-8, -5.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-8, -5.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R32` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R32_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R32.radius ≤ ‖xiShifted R32.center‖) ∧
  (∀ w, R32.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R32_fencing_of_bounds (h : R32_leaf_obligations) :
    CellFencingHypotheses R32 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R32_lowerBound_of_bounds (h : R32_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R32 0.002 0.05
    R32_strip_lo R32_strip_hi (R32_fencing_of_bounds h)

noncomputable def R32_zeroFree_of_bounds (h : R32_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R32 0.002 fine_eps_outer_pos 0.05
    R32_strip_lo R32_strip_hi h.2 h.1

theorem R32_nonvanishing_of_bounds (h : R32_leaf_obligations) {z : ℂ}
    (hx0 : R32.x0 ≤ z.re) (hx1 : z.re ≤ R32.x1)
    (hy0 : R32.y0 ≤ z.im) (hy1 : z.im ≤ R32.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R32 0.002 0.05
      R32_strip_lo R32_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R32_H_instance (h : R32_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-8, -5.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R32, 0.002, 0.05, rfl, rfl, rfl, rfl, R32_strip_lo, R32_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R33 = (-6, -3.5, 0.3, 0.49), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-6,-3.5) × (0.3,0.49)` (mid tier). -/
def R33 : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R33_x0 : R33.x0 = -6 := rfl
theorem R33_x1 : R33.x1 = -3.5 := rfl
theorem R33_y0 : R33.y0 = 0.3 := rfl
theorem R33_y1 : R33.y1 = 0.49 := rfl

theorem R33_width_eq : R33.x1 - R33.x0 = 2.5 := by
  rw [R33_x0, R33_x1]; norm_num

theorem R33_strip_lo : -(1 / 2 : ℝ) < R33.y0 := by rw [R33_y0]; norm_num
theorem R33_strip_hi : R33.y1 < (1 / 2 : ℝ) := by rw [R33_y1]; norm_num

theorem R33_dx_eq : R33.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R33_x0, R33_x1]; norm_num

theorem R33_dy_eq : R33.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R33_y0, R33_y1]; norm_num

theorem R33_radius_eq :
    R33.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R33_dx_eq, R33_dy_eq]

theorem R33_radius_lt : R33.radius < 1.26 := by
  rw [R33_radius_eq]; exact sample_cell_radius_bound

theorem R33_mem_gridFine :
    ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-6, -3.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-6, -3.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R33` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R33_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R33.radius ≤ ‖xiShifted R33.center‖) ∧
  (∀ w, R33.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R33_fencing_of_bounds (h : R33_leaf_obligations) :
    CellFencingHypotheses R33 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R33_lowerBound_of_bounds (h : R33_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R33 0.05 0.07
    R33_strip_lo R33_strip_hi (R33_fencing_of_bounds h)

noncomputable def R33_zeroFree_of_bounds (h : R33_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R33 0.05 fine_eps_mid_pos 0.07
    R33_strip_lo R33_strip_hi h.2 h.1

theorem R33_nonvanishing_of_bounds (h : R33_leaf_obligations) {z : ℂ}
    (hx0 : R33.x0 ≤ z.re) (hx1 : z.re ≤ R33.x1)
    (hy0 : R33.y0 ≤ z.im) (hy1 : z.im ≤ R33.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R33 0.05 0.07
      R33_strip_lo R33_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R33_H_instance (h : R33_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-6, -3.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R33, 0.05, 0.07, rfl, rfl, rfl, rfl, R33_strip_lo, R33_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R34 = (-4, -1.5, 0.3, 0.49), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(-4,-1.5) × (0.3,0.49)` (mid tier). -/
def R34 : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R34_x0 : R34.x0 = -4 := rfl
theorem R34_x1 : R34.x1 = -1.5 := rfl
theorem R34_y0 : R34.y0 = 0.3 := rfl
theorem R34_y1 : R34.y1 = 0.49 := rfl

theorem R34_width_eq : R34.x1 - R34.x0 = 2.5 := by
  rw [R34_x0, R34_x1]; norm_num

theorem R34_strip_lo : -(1 / 2 : ℝ) < R34.y0 := by rw [R34_y0]; norm_num
theorem R34_strip_hi : R34.y1 < (1 / 2 : ℝ) := by rw [R34_y1]; norm_num

theorem R34_dx_eq : R34.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R34_x0, R34_x1]; norm_num

theorem R34_dy_eq : R34.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R34_y0, R34_y1]; norm_num

theorem R34_radius_eq :
    R34.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R34_dx_eq, R34_dy_eq]

theorem R34_radius_lt : R34.radius < 1.26 := by
  rw [R34_radius_eq]; exact sample_cell_radius_bound

theorem R34_mem_gridFine :
    ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-4, -1.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-4, -1.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R34` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R34_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R34.radius ≤ ‖xiShifted R34.center‖) ∧
  (∀ w, R34.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R34_fencing_of_bounds (h : R34_leaf_obligations) :
    CellFencingHypotheses R34 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R34_lowerBound_of_bounds (h : R34_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R34 0.05 0.07
    R34_strip_lo R34_strip_hi (R34_fencing_of_bounds h)

noncomputable def R34_zeroFree_of_bounds (h : R34_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R34 0.05 fine_eps_mid_pos 0.07
    R34_strip_lo R34_strip_hi h.2 h.1

theorem R34_nonvanishing_of_bounds (h : R34_leaf_obligations) {z : ℂ}
    (hx0 : R34.x0 ≤ z.re) (hx1 : z.re ≤ R34.x1)
    (hy0 : R34.y0 ≤ z.im) (hy1 : z.im ≤ R34.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R34 0.05 0.07
      R34_strip_lo R34_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R34_H_instance (h : R34_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-4, -1.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R34, 0.05, 0.07, rfl, rfl, rfl, rfl, R34_strip_lo, R34_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R35 = (-2, 0.5, 0.3, 0.49), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(-2,0.5) × (0.3,0.49)` (inner tier). -/
def R35 : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R35_x0 : R35.x0 = -2 := rfl
theorem R35_x1 : R35.x1 = 0.5 := rfl
theorem R35_y0 : R35.y0 = 0.3 := rfl
theorem R35_y1 : R35.y1 = 0.49 := rfl

theorem R35_width_eq : R35.x1 - R35.x0 = 2.5 := by
  rw [R35_x0, R35_x1]; norm_num

theorem R35_strip_lo : -(1 / 2 : ℝ) < R35.y0 := by rw [R35_y0]; norm_num
theorem R35_strip_hi : R35.y1 < (1 / 2 : ℝ) := by rw [R35_y1]; norm_num

theorem R35_dx_eq : R35.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R35_x0, R35_x1]; norm_num

theorem R35_dy_eq : R35.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R35_y0, R35_y1]; norm_num

theorem R35_radius_eq :
    R35.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R35_dx_eq, R35_dy_eq]

theorem R35_radius_lt : R35.radius < 1.26 := by
  rw [R35_radius_eq]; exact sample_cell_radius_bound

theorem R35_mem_gridFine :
    ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((-2, 0.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(-2, 0.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R35` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R35_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R35.radius ≤ ‖xiShifted R35.center‖) ∧
  (∀ w, R35.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R35_fencing_of_bounds (h : R35_leaf_obligations) :
    CellFencingHypotheses R35 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R35_lowerBound_of_bounds (h : R35_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R35 0.15 0.06
    R35_strip_lo R35_strip_hi (R35_fencing_of_bounds h)

noncomputable def R35_zeroFree_of_bounds (h : R35_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R35 0.15 fine_eps_inner_pos 0.06
    R35_strip_lo R35_strip_hi h.2 h.1

theorem R35_nonvanishing_of_bounds (h : R35_leaf_obligations) {z : ℂ}
    (hx0 : R35.x0 ≤ z.re) (hx1 : z.re ≤ R35.x1)
    (hy0 : R35.y0 ≤ z.im) (hy1 : z.im ≤ R35.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R35 0.15 0.06
      R35_strip_lo R35_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R35_H_instance (h : R35_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (-2, 0.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R35, 0.15, 0.06, rfl, rfl, rfl, rfl, R35_strip_lo, R35_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R36 = (0, 2.5, 0.3, 0.49), inner tier `(0.15,0.06)` -/

/-- Upper-row cell `(0,2.5) × (0.3,0.49)` (inner tier). -/
def R36 : CellProofEngine.Rect2D :=
  ⟨0, 2.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R36_x0 : R36.x0 = 0 := rfl
theorem R36_x1 : R36.x1 = 2.5 := rfl
theorem R36_y0 : R36.y0 = 0.3 := rfl
theorem R36_y1 : R36.y1 = 0.49 := rfl

theorem R36_width_eq : R36.x1 - R36.x0 = 2.5 := by
  rw [R36_x0, R36_x1]; norm_num

theorem R36_strip_lo : -(1 / 2 : ℝ) < R36.y0 := by rw [R36_y0]; norm_num
theorem R36_strip_hi : R36.y1 < (1 / 2 : ℝ) := by rw [R36_y1]; norm_num

theorem R36_dx_eq : R36.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R36_x0, R36_x1]; norm_num

theorem R36_dy_eq : R36.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R36_y0, R36_y1]; norm_num

theorem R36_radius_eq :
    R36.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R36_dx_eq, R36_dy_eq]

theorem R36_radius_lt : R36.radius < 1.26 := by
  rw [R36_radius_eq]; exact sample_cell_radius_bound

theorem R36_mem_gridFine :
    ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((0, 2.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(0, 2.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R36` (inner tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R36_leaf_obligations : Prop :=
  ((0.15 : ℝ) + 0.06 * R36.radius ≤ ‖xiShifted R36.center‖) ∧
  (∀ w, R36.mem w → ‖deriv xiShifted w‖ ≤ (0.06 : ℝ))

theorem R36_fencing_of_bounds (h : R36_leaf_obligations) :
    CellFencingHypotheses R36 0.15 0.06 :=
  ⟨fine_eps_inner_pos, h.2, h.1⟩

noncomputable def R36_lowerBound_of_bounds (h : R36_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R36 0.15 0.06
    R36_strip_lo R36_strip_hi (R36_fencing_of_bounds h)

noncomputable def R36_zeroFree_of_bounds (h : R36_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R36 0.15 fine_eps_inner_pos 0.06
    R36_strip_lo R36_strip_hi h.2 h.1

theorem R36_nonvanishing_of_bounds (h : R36_leaf_obligations) {z : ℂ}
    (hx0 : R36.x0 ≤ z.re) (hx1 : z.re ≤ R36.x1)
    (hy0 : R36.y0 ≤ z.im) (hy1 : z.im ≤ R36.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.15 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R36 0.15 0.06
      R36_strip_lo R36_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_inner_pos) hle

theorem R36_H_instance (h : R36_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (0, 2.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R36, 0.15, 0.06, rfl, rfl, rfl, rfl, R36_strip_lo, R36_strip_hi,
    fine_eps_inner_pos, h.2, h.1⟩

/-! ### R37 = (2, 4.5, 0.3, 0.49), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(2,4.5) × (0.3,0.49)` (mid tier). -/
def R37 : CellProofEngine.Rect2D :=
  ⟨2, 4.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R37_x0 : R37.x0 = 2 := rfl
theorem R37_x1 : R37.x1 = 4.5 := rfl
theorem R37_y0 : R37.y0 = 0.3 := rfl
theorem R37_y1 : R37.y1 = 0.49 := rfl

theorem R37_width_eq : R37.x1 - R37.x0 = 2.5 := by
  rw [R37_x0, R37_x1]; norm_num

theorem R37_strip_lo : -(1 / 2 : ℝ) < R37.y0 := by rw [R37_y0]; norm_num
theorem R37_strip_hi : R37.y1 < (1 / 2 : ℝ) := by rw [R37_y1]; norm_num

theorem R37_dx_eq : R37.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R37_x0, R37_x1]; norm_num

theorem R37_dy_eq : R37.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R37_y0, R37_y1]; norm_num

theorem R37_radius_eq :
    R37.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R37_dx_eq, R37_dy_eq]

theorem R37_radius_lt : R37.radius < 1.26 := by
  rw [R37_radius_eq]; exact sample_cell_radius_bound

theorem R37_mem_gridFine :
    ((2, 4.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((2, 4.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(2, 4.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R37` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R37_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R37.radius ≤ ‖xiShifted R37.center‖) ∧
  (∀ w, R37.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R37_fencing_of_bounds (h : R37_leaf_obligations) :
    CellFencingHypotheses R37 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R37_lowerBound_of_bounds (h : R37_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R37 0.05 0.07
    R37_strip_lo R37_strip_hi (R37_fencing_of_bounds h)

noncomputable def R37_zeroFree_of_bounds (h : R37_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R37 0.05 fine_eps_mid_pos 0.07
    R37_strip_lo R37_strip_hi h.2 h.1

theorem R37_nonvanishing_of_bounds (h : R37_leaf_obligations) {z : ℂ}
    (hx0 : R37.x0 ≤ z.re) (hx1 : z.re ≤ R37.x1)
    (hy0 : R37.y0 ≤ z.im) (hy1 : z.im ≤ R37.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R37 0.05 0.07
      R37_strip_lo R37_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R37_H_instance (h : R37_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (2, 4.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R37, 0.05, 0.07, rfl, rfl, rfl, rfl, R37_strip_lo, R37_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R38 = (4, 6.5, 0.3, 0.49), mid tier `(0.05,0.07)` -/

/-- Upper-row cell `(4,6.5) × (0.3,0.49)` (mid tier). -/
def R38 : CellProofEngine.Rect2D :=
  ⟨4, 6.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R38_x0 : R38.x0 = 4 := rfl
theorem R38_x1 : R38.x1 = 6.5 := rfl
theorem R38_y0 : R38.y0 = 0.3 := rfl
theorem R38_y1 : R38.y1 = 0.49 := rfl

theorem R38_width_eq : R38.x1 - R38.x0 = 2.5 := by
  rw [R38_x0, R38_x1]; norm_num

theorem R38_strip_lo : -(1 / 2 : ℝ) < R38.y0 := by rw [R38_y0]; norm_num
theorem R38_strip_hi : R38.y1 < (1 / 2 : ℝ) := by rw [R38_y1]; norm_num

theorem R38_dx_eq : R38.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R38_x0, R38_x1]; norm_num

theorem R38_dy_eq : R38.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R38_y0, R38_y1]; norm_num

theorem R38_radius_eq :
    R38.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R38_dx_eq, R38_dy_eq]

theorem R38_radius_lt : R38.radius < 1.26 := by
  rw [R38_radius_eq]; exact sample_cell_radius_bound

theorem R38_mem_gridFine :
    ((4, 6.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((4, 6.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(4, 6.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R38` (mid tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R38_leaf_obligations : Prop :=
  ((0.05 : ℝ) + 0.07 * R38.radius ≤ ‖xiShifted R38.center‖) ∧
  (∀ w, R38.mem w → ‖deriv xiShifted w‖ ≤ (0.07 : ℝ))

theorem R38_fencing_of_bounds (h : R38_leaf_obligations) :
    CellFencingHypotheses R38 0.05 0.07 :=
  ⟨fine_eps_mid_pos, h.2, h.1⟩

noncomputable def R38_lowerBound_of_bounds (h : R38_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R38 0.05 0.07
    R38_strip_lo R38_strip_hi (R38_fencing_of_bounds h)

noncomputable def R38_zeroFree_of_bounds (h : R38_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R38 0.05 fine_eps_mid_pos 0.07
    R38_strip_lo R38_strip_hi h.2 h.1

theorem R38_nonvanishing_of_bounds (h : R38_leaf_obligations) {z : ℂ}
    (hx0 : R38.x0 ≤ z.re) (hx1 : z.re ≤ R38.x1)
    (hy0 : R38.y0 ≤ z.im) (hy1 : z.im ≤ R38.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.05 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R38 0.05 0.07
      R38_strip_lo R38_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_mid_pos) hle

theorem R38_H_instance (h : R38_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (4, 6.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R38, 0.05, 0.07, rfl, rfl, rfl, rfl, R38_strip_lo, R38_strip_hi,
    fine_eps_mid_pos, h.2, h.1⟩

/-! ### R39 = (6, 8.5, 0.3, 0.49), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(6,8.5) × (0.3,0.49)` (outer tier). -/
def R39 : CellProofEngine.Rect2D :=
  ⟨6, 8.5, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R39_x0 : R39.x0 = 6 := rfl
theorem R39_x1 : R39.x1 = 8.5 := rfl
theorem R39_y0 : R39.y0 = 0.3 := rfl
theorem R39_y1 : R39.y1 = 0.49 := rfl

theorem R39_width_eq : R39.x1 - R39.x0 = 2.5 := by
  rw [R39_x0, R39_x1]; norm_num

theorem R39_strip_lo : -(1 / 2 : ℝ) < R39.y0 := by rw [R39_y0]; norm_num
theorem R39_strip_hi : R39.y1 < (1 / 2 : ℝ) := by rw [R39_y1]; norm_num

theorem R39_dx_eq : R39.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R39_x0, R39_x1]; norm_num

theorem R39_dy_eq : R39.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R39_y0, R39_y1]; norm_num

theorem R39_radius_eq :
    R39.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R39_dx_eq, R39_dy_eq]

theorem R39_radius_lt : R39.radius < 1.26 := by
  rw [R39_radius_eq]; exact sample_cell_radius_bound

theorem R39_mem_gridFine :
    ((6, 8.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((6, 8.5)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(6, 8.5), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R39` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R39_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R39.radius ≤ ‖xiShifted R39.center‖) ∧
  (∀ w, R39.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R39_fencing_of_bounds (h : R39_leaf_obligations) :
    CellFencingHypotheses R39 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R39_lowerBound_of_bounds (h : R39_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R39 0.002 0.05
    R39_strip_lo R39_strip_hi (R39_fencing_of_bounds h)

noncomputable def R39_zeroFree_of_bounds (h : R39_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R39 0.002 fine_eps_outer_pos 0.05
    R39_strip_lo R39_strip_hi h.2 h.1

theorem R39_nonvanishing_of_bounds (h : R39_leaf_obligations) {z : ℂ}
    (hx0 : R39.x0 ≤ z.re) (hx1 : z.re ≤ R39.x1)
    (hy0 : R39.y0 ≤ z.im) (hy1 : z.im ≤ R39.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R39 0.002 0.05
      R39_strip_lo R39_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R39_H_instance (h : R39_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (6, 8.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R39, 0.002, 0.05, rfl, rfl, rfl, rfl, R39_strip_lo, R39_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

/-! ### R40 = (7.5, 10, 0.3, 0.49), outer tier `(0.002,0.05)` -/

/-- Upper-row cell `(7.5,10) × (0.3,0.49)` (outer tier). -/
def R40 : CellProofEngine.Rect2D :=
  ⟨7.5, 10, 0.3, 0.49, by norm_num, by norm_num⟩

theorem R40_x0 : R40.x0 = 7.5 := rfl
theorem R40_x1 : R40.x1 = 10 := rfl
theorem R40_y0 : R40.y0 = 0.3 := rfl
theorem R40_y1 : R40.y1 = 0.49 := rfl

theorem R40_width_eq : R40.x1 - R40.x0 = 2.5 := by
  rw [R40_x0, R40_x1]; norm_num

theorem R40_strip_lo : -(1 / 2 : ℝ) < R40.y0 := by rw [R40_y0]; norm_num
theorem R40_strip_hi : R40.y1 < (1 / 2 : ℝ) := by rw [R40_y1]; norm_num

theorem R40_dx_eq : R40.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [R40_x0, R40_x1]; norm_num

theorem R40_dy_eq : R40.dy = 0.095 := by
  unfold CellProofEngine.Rect2D.dy
  rw [R40_y0, R40_y1]; norm_num

theorem R40_radius_eq :
    R40.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [R40_dx_eq, R40_dy_eq]

theorem R40_radius_lt : R40.radius < 1.26 := by
  rw [R40_radius_eq]; exact sample_cell_radius_bound

theorem R40_mem_gridFine :
    ((7.5, 10, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ) ∈ gridFine := by
  have hX : (((7.5, 10)) : ℝ × ℝ) ∈ fineGridX := by simp [fineGridX]
  have hY : (((0.3, 0.49)) : ℝ × ℝ) ∈ innerGridY := by simp [innerGridY]
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨(7.5, 10), hX, List.mem_map.mpr ⟨(0.3, 0.49), hY, rfl⟩⟩

/-- The two remaining numerical enclosures for `R40` (outer tier), as explicit
hypotheses exactly as `R00_leaf_obligations` does. -/
def R40_leaf_obligations : Prop :=
  ((0.002 : ℝ) + 0.05 * R40.radius ≤ ‖xiShifted R40.center‖) ∧
  (∀ w, R40.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))

theorem R40_fencing_of_bounds (h : R40_leaf_obligations) :
    CellFencingHypotheses R40 0.002 0.05 :=
  ⟨fine_eps_outer_pos, h.2, h.1⟩

noncomputable def R40_lowerBound_of_bounds (h : R40_leaf_obligations) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_fencingHypotheses_strip R40 0.002 0.05
    R40_strip_lo R40_strip_hi (R40_fencing_of_bounds h)

noncomputable def R40_zeroFree_of_bounds (h : R40_leaf_obligations) :
    XiLocalZeroFreeRect :=
  zeroFreeRect_of_rect_center_bound_strip R40 0.002 fine_eps_outer_pos 0.05
    R40_strip_lo R40_strip_hi h.2 h.1

theorem R40_nonvanishing_of_bounds (h : R40_leaf_obligations) {z : ℂ}
    (hx0 : R40.x0 ≤ z.re) (hx1 : z.re ≤ R40.x1)
    (hy0 : R40.y0 ≤ z.im) (hy1 : z.im ≤ R40.y1) :
    xiShifted z ≠ 0 := by
  have hle : (0.002 : ℝ) ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R40 0.002 0.05
      R40_strip_lo R40_strip_hi h.2 h.1 z ⟨hx0, hx1, hy0, hy1⟩
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt fine_eps_outer_pos) hle

theorem R40_H_instance (h : R40_leaf_obligations)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ gridFine)
    (hc_eq : c = (7.5, 10, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  subst hc_eq
  exact ⟨R40, 0.002, 0.05, rfl, rfl, rfl, rfl, R40_strip_lo, R40_strip_hi,
    fine_eps_outer_pos, h.2, h.1⟩

end CentralCoverAssembly


namespace CentralCoverAssembly

open CellProofEngine

/-! ## Upper-row lists, joint obligations, and row covers (R11--R40)

`midRow1Cells` (`y=(0.1,0.3)`), `midRow2Cells` (`y=(0.2,0.4)`), `topRowCells`
(`y=(0.3,0.49)`): the 30 upper `gridFine` cells. Joint obligations mirror
`BottomRowObligations`; row covers mirror `bottom_row_covered` via closed
`x`-branching (thresholds from `fineGridX_covers`) plus the row's closed
`y`-bounds. Numerical enclosures remain explicit hypotheses.
-/

/-- The 10 `gridFine` cells with `y in (0.1,0.3)`. -/
def midRow1Cells : List (ℝ × ℝ × ℝ × ℝ) :=
  [
    (-10, -7.5, 0.1, 0.3),
    (-8, -5.5, 0.1, 0.3),
    (-6, -3.5, 0.1, 0.3),
    (-4, -1.5, 0.1, 0.3),
    (-2, 0.5, 0.1, 0.3),
    (0, 2.5, 0.1, 0.3),
    (2, 4.5, 0.1, 0.3),
    (4, 6.5, 0.1, 0.3),
    (6, 8.5, 0.1, 0.3),
    (7.5, 10, 0.1, 0.3)]

/-- The 10 `gridFine` cells with `y in (0.2,0.4)`. -/
def midRow2Cells : List (ℝ × ℝ × ℝ × ℝ) :=
  [
    (-10, -7.5, 0.2, 0.4),
    (-8, -5.5, 0.2, 0.4),
    (-6, -3.5, 0.2, 0.4),
    (-4, -1.5, 0.2, 0.4),
    (-2, 0.5, 0.2, 0.4),
    (0, 2.5, 0.2, 0.4),
    (2, 4.5, 0.2, 0.4),
    (4, 6.5, 0.2, 0.4),
    (6, 8.5, 0.2, 0.4),
    (7.5, 10, 0.2, 0.4)]

/-- The 10 `gridFine` cells with `y in (0.3,0.49)`. -/
def topRowCells : List (ℝ × ℝ × ℝ × ℝ) :=
  [
    (-10, -7.5, 0.3, 0.49),
    (-8, -5.5, 0.3, 0.49),
    (-6, -3.5, 0.3, 0.49),
    (-4, -1.5, 0.3, 0.49),
    (-2, 0.5, 0.3, 0.49),
    (0, 2.5, 0.3, 0.49),
    (2, 4.5, 0.3, 0.49),
    (4, 6.5, 0.3, 0.49),
    (6, 8.5, 0.3, 0.49),
    (7.5, 10, 0.3, 0.49)]

/-- All 40 `gridFine` upper cells (bottom 10 + upper 30). -/
def allCentralCells : List (ℝ × ℝ × ℝ × ℝ) :=
  bottomRowCells ++ midRow1Cells ++ midRow2Cells ++ topRowCells

/-- Every mid-row-1 cell lies in `gridFine`. -/
theorem midRow1_mem_gridFine_of_mem {c : ℝ × ℝ × ℝ × ℝ}
    (hc : c ∈ midRow1Cells) : c ∈ gridFine := by
  unfold midRow1Cells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R11_mem_gridFine
  · exact R12_mem_gridFine
  · exact R13_mem_gridFine
  · exact R14_mem_gridFine
  · exact R15_mem_gridFine
  · exact R16_mem_gridFine
  · exact R17_mem_gridFine
  · exact R18_mem_gridFine
  · exact R19_mem_gridFine
  · exact R20_mem_gridFine

/-- Every mid-row-2 cell lies in `gridFine`. -/
theorem midRow2_mem_gridFine_of_mem {c : ℝ × ℝ × ℝ × ℝ}
    (hc : c ∈ midRow2Cells) : c ∈ gridFine := by
  unfold midRow2Cells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R21_mem_gridFine
  · exact R22_mem_gridFine
  · exact R23_mem_gridFine
  · exact R24_mem_gridFine
  · exact R25_mem_gridFine
  · exact R26_mem_gridFine
  · exact R27_mem_gridFine
  · exact R28_mem_gridFine
  · exact R29_mem_gridFine
  · exact R30_mem_gridFine

/-- Every top-row cell lies in `gridFine`. -/
theorem topRow_mem_gridFine_of_mem {c : ℝ × ℝ × ℝ × ℝ}
    (hc : c ∈ topRowCells) : c ∈ gridFine := by
  unfold topRowCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R31_mem_gridFine
  · exact R32_mem_gridFine
  · exact R33_mem_gridFine
  · exact R34_mem_gridFine
  · exact R35_mem_gridFine
  · exact R36_mem_gridFine
  · exact R37_mem_gridFine
  · exact R38_mem_gridFine
  · exact R39_mem_gridFine
  · exact R40_mem_gridFine

/-- Every cell of `allCentralCells` lies in `gridFine`. -/
theorem allCentral_mem_gridFine_of_mem {c : ℝ × ℝ × ℝ × ℝ}
    (hc : c ∈ allCentralCells) : c ∈ gridFine := by
  unfold allCentralCells at hc
  simp at hc
  rcases hc with h | h | h | h
  · exact bottomRow_mem_gridFine_of_mem h
  · exact midRow1_mem_gridFine_of_mem h
  · exact midRow2_mem_gridFine_of_mem h
  · exact topRow_mem_gridFine_of_mem h

/-- Joint obligations for mid-row 1 (`R11`--`R20`). -/
def MidRow1Obligations : Prop :=
  R11_leaf_obligations ∧ R12_leaf_obligations ∧ R13_leaf_obligations ∧
  R14_leaf_obligations ∧ R15_leaf_obligations ∧ R16_leaf_obligations ∧
  R17_leaf_obligations ∧ R18_leaf_obligations ∧ R19_leaf_obligations ∧
  R20_leaf_obligations

/-- Joint obligations for mid-row 2 (`R21`--`R30`). -/
def MidRow2Obligations : Prop :=
  R21_leaf_obligations ∧ R22_leaf_obligations ∧ R23_leaf_obligations ∧
  R24_leaf_obligations ∧ R25_leaf_obligations ∧ R26_leaf_obligations ∧
  R27_leaf_obligations ∧ R28_leaf_obligations ∧ R29_leaf_obligations ∧
  R30_leaf_obligations

/-- Joint obligations for the top row (`R31`--`R40`). -/
def TopRowObligations : Prop :=
  R31_leaf_obligations ∧ R32_leaf_obligations ∧ R33_leaf_obligations ∧
  R34_leaf_obligations ∧ R35_leaf_obligations ∧ R36_leaf_obligations ∧
  R37_leaf_obligations ∧ R38_leaf_obligations ∧ R39_leaf_obligations ∧
  R40_leaf_obligations

/-- Joint obligations for all 30 upper cells. -/
def UpperRowsObligations : Prop :=
  MidRow1Obligations ∧ MidRow2Obligations ∧ TopRowObligations

/-- Joint obligations for all 40 `gridFine` upper cells (bottom 10 + upper 30). -/
def FullCentralObligations : Prop :=
  BottomRowObligations ∧ UpperRowsObligations

/-- The 10 mid-row-1 `H`-leaves follow jointly from `MidRow1Obligations`. -/
theorem midRow1_H_of_obligations (hMid1 : MidRow1Obligations) :
    ∀ c ∈ midRow1Cells, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  intro c hc
  unfold midRow1Cells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h11, _, _, _, _, _, _, _, _, _⟩ := hMid1
    exact R11_H_instance h11 _ R11_mem_gridFine rfl
  · obtain ⟨_, h12, _, _, _, _, _, _, _, _⟩ := hMid1
    exact R12_H_instance h12 _ R12_mem_gridFine rfl
  · obtain ⟨_, _, h13, _, _, _, _, _, _, _⟩ := hMid1
    exact R13_H_instance h13 _ R13_mem_gridFine rfl
  · obtain ⟨_, _, _, h14, _, _, _, _, _, _⟩ := hMid1
    exact R14_H_instance h14 _ R14_mem_gridFine rfl
  · obtain ⟨_, _, _, _, h15, _, _, _, _, _⟩ := hMid1
    exact R15_H_instance h15 _ R15_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, h16, _, _, _, _⟩ := hMid1
    exact R16_H_instance h16 _ R16_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, h17, _, _, _⟩ := hMid1
    exact R17_H_instance h17 _ R17_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, h18, _, _⟩ := hMid1
    exact R18_H_instance h18 _ R18_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, h19, _⟩ := hMid1
    exact R19_H_instance h19 _ R19_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, h20⟩ := hMid1
    exact R20_H_instance h20 _ R20_mem_gridFine rfl

/-- The 10 mid-row-2 `H`-leaves follow jointly from `MidRow2Obligations`. -/
theorem midRow2_H_of_obligations (hMid2 : MidRow2Obligations) :
    ∀ c ∈ midRow2Cells, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  intro c hc
  unfold midRow2Cells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h21, _, _, _, _, _, _, _, _, _⟩ := hMid2
    exact R21_H_instance h21 _ R21_mem_gridFine rfl
  · obtain ⟨_, h22, _, _, _, _, _, _, _, _⟩ := hMid2
    exact R22_H_instance h22 _ R22_mem_gridFine rfl
  · obtain ⟨_, _, h23, _, _, _, _, _, _, _⟩ := hMid2
    exact R23_H_instance h23 _ R23_mem_gridFine rfl
  · obtain ⟨_, _, _, h24, _, _, _, _, _, _⟩ := hMid2
    exact R24_H_instance h24 _ R24_mem_gridFine rfl
  · obtain ⟨_, _, _, _, h25, _, _, _, _, _⟩ := hMid2
    exact R25_H_instance h25 _ R25_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, h26, _, _, _, _⟩ := hMid2
    exact R26_H_instance h26 _ R26_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, h27, _, _, _⟩ := hMid2
    exact R27_H_instance h27 _ R27_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, h28, _, _⟩ := hMid2
    exact R28_H_instance h28 _ R28_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, h29, _⟩ := hMid2
    exact R29_H_instance h29 _ R29_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, h30⟩ := hMid2
    exact R30_H_instance h30 _ R30_mem_gridFine rfl

/-- The 10 top-row `H`-leaves follow jointly from `TopRowObligations`. -/
theorem topRow_H_of_obligations (hTop : TopRowObligations) :
    ∀ c ∈ topRowCells, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  intro c hc
  unfold topRowCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h31, _, _, _, _, _, _, _, _, _⟩ := hTop
    exact R31_H_instance h31 _ R31_mem_gridFine rfl
  · obtain ⟨_, h32, _, _, _, _, _, _, _, _⟩ := hTop
    exact R32_H_instance h32 _ R32_mem_gridFine rfl
  · obtain ⟨_, _, h33, _, _, _, _, _, _, _⟩ := hTop
    exact R33_H_instance h33 _ R33_mem_gridFine rfl
  · obtain ⟨_, _, _, h34, _, _, _, _, _, _⟩ := hTop
    exact R34_H_instance h34 _ R34_mem_gridFine rfl
  · obtain ⟨_, _, _, _, h35, _, _, _, _, _⟩ := hTop
    exact R35_H_instance h35 _ R35_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, h36, _, _, _, _⟩ := hTop
    exact R36_H_instance h36 _ R36_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, h37, _, _, _⟩ := hTop
    exact R37_H_instance h37 _ R37_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, h38, _, _⟩ := hTop
    exact R38_H_instance h38 _ R38_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, h39, _⟩ := hTop
    exact R39_H_instance h39 _ R39_mem_gridFine rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, h40⟩ := hTop
    exact R40_H_instance h40 _ R40_mem_gridFine rfl

/-- All 40 `H`-leaves follow jointly from `FullCentralObligations`. -/
theorem allCentral_H_of_obligations (hFull : FullCentralObligations) :
    ∀ c ∈ allCentralCells, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  obtain ⟨hBot, hUp⟩ := hFull
  obtain ⟨hMid1, hMid2, hTop⟩ := hUp
  intro c hc
  unfold allCentralCells at hc
  simp at hc
  rcases hc with h | h | h | h
  · exact bottomRow_H_of_obligations hBot c h
  · exact midRow1_H_of_obligations hMid1 c h
  · exact midRow2_H_of_obligations hMid2 c h
  · exact topRow_H_of_obligations hTop c h

end CentralCoverAssembly


namespace CentralCoverAssembly

open CellProofEngine

/-! ## Row covers + combined upper cover (positive side)

Each row cover proves pointwise nonvanishing on its closed `y`-strip via the
row's 10 closed `x`-branches (thresholds from `fineGridX_covers`, mirroring
`bottom_row_covered`). `central_upper_covered` combines `bottom_row_covered`
(`0 < Im ≤ 0.2`, strip included) with the three upper rows to cover
`0 < Im ≤ 0.49`: every such `z` is either strip-handled or lies closed in
some packaged upper/bottom cell.
-/

/-- Row cover `y \in [0.1,0.3]`: every `z` with `-10 < Re < 10`, `0.1 ≤ Im ≤ 0.3` is nonvanishing, via closed `x`-branching. -/
theorem row1_covered (hRow : MidRow1Obligations) {z : ℂ}
    (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_lo : (0.1 : ℝ) ≤ z.im) (hy_hi : z.im ≤ (0.3 : ℝ)) :
    xiShifted z ≠ 0 := by
  obtain ⟨h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩ := hRow
  by_cases h1 : z.re < -7.5
  · exact R11_nonvanishing_of_bounds h11
        (by rw [R11_x0]; linarith) (by rw [R11_x1]; exact le_of_lt h1)
        (by rw [R11_y0]; exact hy_lo) (by rw [R11_y1]; exact hy_hi)
  · push_neg at h1
    by_cases h2 : z.re < -5.5
    · exact R12_nonvanishing_of_bounds h12
          (by rw [R12_x0]; linarith) (by rw [R12_x1]; exact le_of_lt h2)
          (by rw [R12_y0]; exact hy_lo) (by rw [R12_y1]; exact hy_hi)
    · push_neg at h2
      by_cases h3 : z.re < -3.5
      · exact R13_nonvanishing_of_bounds h13
            (by rw [R13_x0]; linarith) (by rw [R13_x1]; exact le_of_lt h3)
            (by rw [R13_y0]; exact hy_lo) (by rw [R13_y1]; exact hy_hi)
      · push_neg at h3
        by_cases h4 : z.re < -1.5
        · exact R14_nonvanishing_of_bounds h14
              (by rw [R14_x0]; linarith) (by rw [R14_x1]; exact le_of_lt h4)
              (by rw [R14_y0]; exact hy_lo) (by rw [R14_y1]; exact hy_hi)
        · push_neg at h4
          by_cases h5 : z.re < 0.5
          · exact R15_nonvanishing_of_bounds h15
                (by rw [R15_x0]; linarith) (by rw [R15_x1]; exact le_of_lt h5)
                (by rw [R15_y0]; exact hy_lo) (by rw [R15_y1]; exact hy_hi)
          · push_neg at h5
            by_cases h6 : z.re < 2.5
            · exact R16_nonvanishing_of_bounds h16
                  (by rw [R16_x0]; linarith) (by rw [R16_x1]; exact le_of_lt h6)
                  (by rw [R16_y0]; exact hy_lo) (by rw [R16_y1]; exact hy_hi)
            · push_neg at h6
              by_cases h7 : z.re < 4.5
              · exact R17_nonvanishing_of_bounds h17
                    (by rw [R17_x0]; linarith) (by rw [R17_x1]; exact le_of_lt h7)
                    (by rw [R17_y0]; exact hy_lo) (by rw [R17_y1]; exact hy_hi)
              · push_neg at h7
                by_cases h8 : z.re < 6.5
                · exact R18_nonvanishing_of_bounds h18
                      (by rw [R18_x0]; linarith) (by rw [R18_x1]; exact le_of_lt h8)
                      (by rw [R18_y0]; exact hy_lo) (by rw [R18_y1]; exact hy_hi)
                · push_neg at h8
                  by_cases h9 : z.re < 8.5
                  · exact R19_nonvanishing_of_bounds h19
                        (by rw [R19_x0]; linarith) (by rw [R19_x1]; exact le_of_lt h9)
                        (by rw [R19_y0]; exact hy_lo) (by rw [R19_y1]; exact hy_hi)
                  · push_neg at h9
                    exact R20_nonvanishing_of_bounds h20
                          (by rw [R20_x0]; linarith)
                          (by rw [R20_x1]; exact le_of_lt hx_hi)
                          (by rw [R20_y0]; exact hy_lo) (by rw [R20_y1]; exact hy_hi)


/-- Row cover `y \in [0.2,0.4]`: every `z` with `-10 < Re < 10`, `0.2 ≤ Im ≤ 0.4` is nonvanishing, via closed `x`-branching. -/
theorem row2_covered (hRow : MidRow2Obligations) {z : ℂ}
    (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_lo : (0.2 : ℝ) ≤ z.im) (hy_hi : z.im ≤ (0.4 : ℝ)) :
    xiShifted z ≠ 0 := by
  obtain ⟨h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩ := hRow
  by_cases h1 : z.re < -7.5
  · exact R21_nonvanishing_of_bounds h21
        (by rw [R21_x0]; linarith) (by rw [R21_x1]; exact le_of_lt h1)
        (by rw [R21_y0]; exact hy_lo) (by rw [R21_y1]; exact hy_hi)
  · push_neg at h1
    by_cases h2 : z.re < -5.5
    · exact R22_nonvanishing_of_bounds h22
          (by rw [R22_x0]; linarith) (by rw [R22_x1]; exact le_of_lt h2)
          (by rw [R22_y0]; exact hy_lo) (by rw [R22_y1]; exact hy_hi)
    · push_neg at h2
      by_cases h3 : z.re < -3.5
      · exact R23_nonvanishing_of_bounds h23
            (by rw [R23_x0]; linarith) (by rw [R23_x1]; exact le_of_lt h3)
            (by rw [R23_y0]; exact hy_lo) (by rw [R23_y1]; exact hy_hi)
      · push_neg at h3
        by_cases h4 : z.re < -1.5
        · exact R24_nonvanishing_of_bounds h24
              (by rw [R24_x0]; linarith) (by rw [R24_x1]; exact le_of_lt h4)
              (by rw [R24_y0]; exact hy_lo) (by rw [R24_y1]; exact hy_hi)
        · push_neg at h4
          by_cases h5 : z.re < 0.5
          · exact R25_nonvanishing_of_bounds h25
                (by rw [R25_x0]; linarith) (by rw [R25_x1]; exact le_of_lt h5)
                (by rw [R25_y0]; exact hy_lo) (by rw [R25_y1]; exact hy_hi)
          · push_neg at h5
            by_cases h6 : z.re < 2.5
            · exact R26_nonvanishing_of_bounds h26
                  (by rw [R26_x0]; linarith) (by rw [R26_x1]; exact le_of_lt h6)
                  (by rw [R26_y0]; exact hy_lo) (by rw [R26_y1]; exact hy_hi)
            · push_neg at h6
              by_cases h7 : z.re < 4.5
              · exact R27_nonvanishing_of_bounds h27
                    (by rw [R27_x0]; linarith) (by rw [R27_x1]; exact le_of_lt h7)
                    (by rw [R27_y0]; exact hy_lo) (by rw [R27_y1]; exact hy_hi)
              · push_neg at h7
                by_cases h8 : z.re < 6.5
                · exact R28_nonvanishing_of_bounds h28
                      (by rw [R28_x0]; linarith) (by rw [R28_x1]; exact le_of_lt h8)
                      (by rw [R28_y0]; exact hy_lo) (by rw [R28_y1]; exact hy_hi)
                · push_neg at h8
                  by_cases h9 : z.re < 8.5
                  · exact R29_nonvanishing_of_bounds h29
                        (by rw [R29_x0]; linarith) (by rw [R29_x1]; exact le_of_lt h9)
                        (by rw [R29_y0]; exact hy_lo) (by rw [R29_y1]; exact hy_hi)
                  · push_neg at h9
                    exact R30_nonvanishing_of_bounds h30
                          (by rw [R30_x0]; linarith)
                          (by rw [R30_x1]; exact le_of_lt hx_hi)
                          (by rw [R30_y0]; exact hy_lo) (by rw [R30_y1]; exact hy_hi)


/-- Row cover `y \in [0.3,0.49]`: every `z` with `-10 < Re < 10`, `0.3 ≤ Im ≤ 0.49` is nonvanishing, via closed `x`-branching. -/
theorem top_covered (hRow : TopRowObligations) {z : ℂ}
    (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_lo : (0.3 : ℝ) ≤ z.im) (hy_hi : z.im ≤ (0.49 : ℝ)) :
    xiShifted z ≠ 0 := by
  obtain ⟨h31,h32,h33,h34,h35,h36,h37,h38,h39,h40⟩ := hRow
  by_cases h1 : z.re < -7.5
  · exact R31_nonvanishing_of_bounds h31
        (by rw [R31_x0]; linarith) (by rw [R31_x1]; exact le_of_lt h1)
        (by rw [R31_y0]; exact hy_lo) (by rw [R31_y1]; exact hy_hi)
  · push_neg at h1
    by_cases h2 : z.re < -5.5
    · exact R32_nonvanishing_of_bounds h32
          (by rw [R32_x0]; linarith) (by rw [R32_x1]; exact le_of_lt h2)
          (by rw [R32_y0]; exact hy_lo) (by rw [R32_y1]; exact hy_hi)
    · push_neg at h2
      by_cases h3 : z.re < -3.5
      · exact R33_nonvanishing_of_bounds h33
            (by rw [R33_x0]; linarith) (by rw [R33_x1]; exact le_of_lt h3)
            (by rw [R33_y0]; exact hy_lo) (by rw [R33_y1]; exact hy_hi)
      · push_neg at h3
        by_cases h4 : z.re < -1.5
        · exact R34_nonvanishing_of_bounds h34
              (by rw [R34_x0]; linarith) (by rw [R34_x1]; exact le_of_lt h4)
              (by rw [R34_y0]; exact hy_lo) (by rw [R34_y1]; exact hy_hi)
        · push_neg at h4
          by_cases h5 : z.re < 0.5
          · exact R35_nonvanishing_of_bounds h35
                (by rw [R35_x0]; linarith) (by rw [R35_x1]; exact le_of_lt h5)
                (by rw [R35_y0]; exact hy_lo) (by rw [R35_y1]; exact hy_hi)
          · push_neg at h5
            by_cases h6 : z.re < 2.5
            · exact R36_nonvanishing_of_bounds h36
                  (by rw [R36_x0]; linarith) (by rw [R36_x1]; exact le_of_lt h6)
                  (by rw [R36_y0]; exact hy_lo) (by rw [R36_y1]; exact hy_hi)
            · push_neg at h6
              by_cases h7 : z.re < 4.5
              · exact R37_nonvanishing_of_bounds h37
                    (by rw [R37_x0]; linarith) (by rw [R37_x1]; exact le_of_lt h7)
                    (by rw [R37_y0]; exact hy_lo) (by rw [R37_y1]; exact hy_hi)
              · push_neg at h7
                by_cases h8 : z.re < 6.5
                · exact R38_nonvanishing_of_bounds h38
                      (by rw [R38_x0]; linarith) (by rw [R38_x1]; exact le_of_lt h8)
                      (by rw [R38_y0]; exact hy_lo) (by rw [R38_y1]; exact hy_hi)
                · push_neg at h8
                  by_cases h9 : z.re < 8.5
                  · exact R39_nonvanishing_of_bounds h39
                        (by rw [R39_x0]; linarith) (by rw [R39_x1]; exact le_of_lt h9)
                        (by rw [R39_y0]; exact hy_lo) (by rw [R39_y1]; exact hy_hi)
                  · push_neg at h9
                    exact R40_nonvanishing_of_bounds h40
                          (by rw [R40_x0]; linarith)
                          (by rw [R40_x1]; exact le_of_lt hx_hi)
                          (by rw [R40_y0]; exact hy_lo) (by rw [R40_y1]; exact hy_hi)


/-- Combined positive-side cover: every `z` with `-10 < Re < 10`,
`0 < Im ≤ 0.49` is nonvanishing — via `bottom_row_covered` at `Im ≤ 0.2`
(strip-or-bottom-cell), else via the closed row cell containing it. -/
theorem central_upper_covered (hFull : FullCentralObligations)
    (hStrip : BottomStripObligations)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.49) :
    xiShifted z ≠ 0 := by
  obtain ⟨hBot, hUp⟩ := hFull
  obtain ⟨hMid1, hMid2, hTop⟩ := hUp
  by_cases hY2 : z.im ≤ 0.2
  · exact bottom_row_covered hBot hStrip hx_lo hx_hi hy_pos hY2
  · push_neg at hY2
    by_cases hY3 : z.im ≤ 0.3
    · have hy_lo1 : (0.1 : ℝ) ≤ z.im := by linarith
      exact row1_covered hMid1 hx_lo hx_hi hy_lo1 hY3
    · push_neg at hY3
      by_cases hY4 : z.im ≤ 0.4
      · have hy_lo2 : (0.2 : ℝ) ≤ z.im := by linarith
        exact row2_covered hMid2 hx_lo hx_hi hy_lo2 hY4
      · push_neg at hY4
        have hy_lo3 : (0.3 : ℝ) ≤ z.im := by linarith
        exact top_covered hTop hx_lo hx_hi hy_lo3 hy_le

/-! ## Lower-half transfers via `conj_of` (all 41 packaged cells)

Every packaged upper cell (bottom 11 incl. off-grid `R01` + upper 30) is
mirrored to the lower half by the committed sorry-free
`XiLocalZeroFreeRect.conj_of` / `XiLocalLowerBoundRect.conj_of` with explicit
`0 < y0` (`by rw [RXX_y0]; norm_num`, since `y0 ≥ 0.01`) and `y1 < 1/2`
(`by rw [RXX_y1]; norm_num`, since `y1 ≤ 0.49`) side conditions. The
mirrored rects are zero-free by conjugate symmetry
(`classicalXi_symmetry.conj_symm`); closed lower nonvanishing below follows via
`star` + `central_upper_covered` (equivalent, covering boundary points that the
strict `no_zero` fields exclude).
-/

noncomputable def R00_conjZF_of_bounds (h : R00_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R00_zeroFree_of_bounds h)
    (by have e : (R00_zeroFree_of_bounds h).y0 = R00.y0 := rfl
        rw [e, R00_y0]; norm_num)
    (by have e : (R00_zeroFree_of_bounds h).y1 = R00.y1 := rfl
        rw [e, R00_y1]; norm_num)

noncomputable def R00_conjLB_of_bounds (h : R00_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R00_lowerBound_of_bounds h)
    (by have e : (R00_lowerBound_of_bounds h).y0 = R00.y0 := rfl
        rw [e, R00_y0]; norm_num)
    (by have e : (R00_lowerBound_of_bounds h).y1 = R00.y1 := rfl
        rw [e, R00_y1]; norm_num)

noncomputable def R01_conjZF_of_bounds (h : R01_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R01_zeroFree_of_bounds h)
    (by have e : (R01_zeroFree_of_bounds h).y0 = R01.y0 := rfl
        rw [e, R01_y0]; norm_num)
    (by have e : (R01_zeroFree_of_bounds h).y1 = R01.y1 := rfl
        rw [e, R01_y1]; norm_num)

noncomputable def R01_conjLB_of_bounds (h : R01_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R01_lowerBound_of_bounds h)
    (by have e : (R01_lowerBound_of_bounds h).y0 = R01.y0 := rfl
        rw [e, R01_y0]; norm_num)
    (by have e : (R01_lowerBound_of_bounds h).y1 = R01.y1 := rfl
        rw [e, R01_y1]; norm_num)

noncomputable def R02_conjZF_of_bounds (h : R02_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R02_zeroFree_of_bounds h)
    (by have e : (R02_zeroFree_of_bounds h).y0 = R02.y0 := rfl
        rw [e, R02_y0]; norm_num)
    (by have e : (R02_zeroFree_of_bounds h).y1 = R02.y1 := rfl
        rw [e, R02_y1]; norm_num)

noncomputable def R02_conjLB_of_bounds (h : R02_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R02_lowerBound_of_bounds h)
    (by have e : (R02_lowerBound_of_bounds h).y0 = R02.y0 := rfl
        rw [e, R02_y0]; norm_num)
    (by have e : (R02_lowerBound_of_bounds h).y1 = R02.y1 := rfl
        rw [e, R02_y1]; norm_num)

noncomputable def R03_conjZF_of_bounds (h : R03_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R03_zeroFree_of_bounds h)
    (by have e : (R03_zeroFree_of_bounds h).y0 = R03.y0 := rfl
        rw [e, R03_y0]; norm_num)
    (by have e : (R03_zeroFree_of_bounds h).y1 = R03.y1 := rfl
        rw [e, R03_y1]; norm_num)

noncomputable def R03_conjLB_of_bounds (h : R03_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R03_lowerBound_of_bounds h)
    (by have e : (R03_lowerBound_of_bounds h).y0 = R03.y0 := rfl
        rw [e, R03_y0]; norm_num)
    (by have e : (R03_lowerBound_of_bounds h).y1 = R03.y1 := rfl
        rw [e, R03_y1]; norm_num)

noncomputable def R04_conjZF_of_bounds (h : R04_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R04_zeroFree_of_bounds h)
    (by have e : (R04_zeroFree_of_bounds h).y0 = R04.y0 := rfl
        rw [e, R04_y0]; norm_num)
    (by have e : (R04_zeroFree_of_bounds h).y1 = R04.y1 := rfl
        rw [e, R04_y1]; norm_num)

noncomputable def R04_conjLB_of_bounds (h : R04_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R04_lowerBound_of_bounds h)
    (by have e : (R04_lowerBound_of_bounds h).y0 = R04.y0 := rfl
        rw [e, R04_y0]; norm_num)
    (by have e : (R04_lowerBound_of_bounds h).y1 = R04.y1 := rfl
        rw [e, R04_y1]; norm_num)

noncomputable def R05_conjZF_of_bounds (h : R05_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R05_zeroFree_of_bounds h)
    (by have e : (R05_zeroFree_of_bounds h).y0 = R05.y0 := rfl
        rw [e, R05_y0]; norm_num)
    (by have e : (R05_zeroFree_of_bounds h).y1 = R05.y1 := rfl
        rw [e, R05_y1]; norm_num)

noncomputable def R05_conjLB_of_bounds (h : R05_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R05_lowerBound_of_bounds h)
    (by have e : (R05_lowerBound_of_bounds h).y0 = R05.y0 := rfl
        rw [e, R05_y0]; norm_num)
    (by have e : (R05_lowerBound_of_bounds h).y1 = R05.y1 := rfl
        rw [e, R05_y1]; norm_num)

noncomputable def R06_conjZF_of_bounds (h : R06_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R06_zeroFree_of_bounds h)
    (by have e : (R06_zeroFree_of_bounds h).y0 = R06.y0 := rfl
        rw [e, R06_y0]; norm_num)
    (by have e : (R06_zeroFree_of_bounds h).y1 = R06.y1 := rfl
        rw [e, R06_y1]; norm_num)

noncomputable def R06_conjLB_of_bounds (h : R06_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R06_lowerBound_of_bounds h)
    (by have e : (R06_lowerBound_of_bounds h).y0 = R06.y0 := rfl
        rw [e, R06_y0]; norm_num)
    (by have e : (R06_lowerBound_of_bounds h).y1 = R06.y1 := rfl
        rw [e, R06_y1]; norm_num)

noncomputable def R07_conjZF_of_bounds (h : R07_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R07_zeroFree_of_bounds h)
    (by have e : (R07_zeroFree_of_bounds h).y0 = R07.y0 := rfl
        rw [e, R07_y0]; norm_num)
    (by have e : (R07_zeroFree_of_bounds h).y1 = R07.y1 := rfl
        rw [e, R07_y1]; norm_num)

noncomputable def R07_conjLB_of_bounds (h : R07_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R07_lowerBound_of_bounds h)
    (by have e : (R07_lowerBound_of_bounds h).y0 = R07.y0 := rfl
        rw [e, R07_y0]; norm_num)
    (by have e : (R07_lowerBound_of_bounds h).y1 = R07.y1 := rfl
        rw [e, R07_y1]; norm_num)

noncomputable def R08_conjZF_of_bounds (h : R08_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R08_zeroFree_of_bounds h)
    (by have e : (R08_zeroFree_of_bounds h).y0 = R08.y0 := rfl
        rw [e, R08_y0]; norm_num)
    (by have e : (R08_zeroFree_of_bounds h).y1 = R08.y1 := rfl
        rw [e, R08_y1]; norm_num)

noncomputable def R08_conjLB_of_bounds (h : R08_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R08_lowerBound_of_bounds h)
    (by have e : (R08_lowerBound_of_bounds h).y0 = R08.y0 := rfl
        rw [e, R08_y0]; norm_num)
    (by have e : (R08_lowerBound_of_bounds h).y1 = R08.y1 := rfl
        rw [e, R08_y1]; norm_num)

noncomputable def R09_conjZF_of_bounds (h : R09_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R09_zeroFree_of_bounds h)
    (by have e : (R09_zeroFree_of_bounds h).y0 = R09.y0 := rfl
        rw [e, R09_y0]; norm_num)
    (by have e : (R09_zeroFree_of_bounds h).y1 = R09.y1 := rfl
        rw [e, R09_y1]; norm_num)

noncomputable def R09_conjLB_of_bounds (h : R09_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R09_lowerBound_of_bounds h)
    (by have e : (R09_lowerBound_of_bounds h).y0 = R09.y0 := rfl
        rw [e, R09_y0]; norm_num)
    (by have e : (R09_lowerBound_of_bounds h).y1 = R09.y1 := rfl
        rw [e, R09_y1]; norm_num)

noncomputable def R10_conjZF_of_bounds (h : R10_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R10_zeroFree_of_bounds h)
    (by have e : (R10_zeroFree_of_bounds h).y0 = R10.y0 := rfl
        rw [e, R10_y0]; norm_num)
    (by have e : (R10_zeroFree_of_bounds h).y1 = R10.y1 := rfl
        rw [e, R10_y1]; norm_num)

noncomputable def R10_conjLB_of_bounds (h : R10_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R10_lowerBound_of_bounds h)
    (by have e : (R10_lowerBound_of_bounds h).y0 = R10.y0 := rfl
        rw [e, R10_y0]; norm_num)
    (by have e : (R10_lowerBound_of_bounds h).y1 = R10.y1 := rfl
        rw [e, R10_y1]; norm_num)

noncomputable def R11_conjZF_of_bounds (h : R11_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R11_zeroFree_of_bounds h)
    (by have e : (R11_zeroFree_of_bounds h).y0 = R11.y0 := rfl
        rw [e, R11_y0]; norm_num)
    (by have e : (R11_zeroFree_of_bounds h).y1 = R11.y1 := rfl
        rw [e, R11_y1]; norm_num)

noncomputable def R11_conjLB_of_bounds (h : R11_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R11_lowerBound_of_bounds h)
    (by have e : (R11_lowerBound_of_bounds h).y0 = R11.y0 := rfl
        rw [e, R11_y0]; norm_num)
    (by have e : (R11_lowerBound_of_bounds h).y1 = R11.y1 := rfl
        rw [e, R11_y1]; norm_num)

noncomputable def R12_conjZF_of_bounds (h : R12_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R12_zeroFree_of_bounds h)
    (by have e : (R12_zeroFree_of_bounds h).y0 = R12.y0 := rfl
        rw [e, R12_y0]; norm_num)
    (by have e : (R12_zeroFree_of_bounds h).y1 = R12.y1 := rfl
        rw [e, R12_y1]; norm_num)

noncomputable def R12_conjLB_of_bounds (h : R12_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R12_lowerBound_of_bounds h)
    (by have e : (R12_lowerBound_of_bounds h).y0 = R12.y0 := rfl
        rw [e, R12_y0]; norm_num)
    (by have e : (R12_lowerBound_of_bounds h).y1 = R12.y1 := rfl
        rw [e, R12_y1]; norm_num)

noncomputable def R13_conjZF_of_bounds (h : R13_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R13_zeroFree_of_bounds h)
    (by have e : (R13_zeroFree_of_bounds h).y0 = R13.y0 := rfl
        rw [e, R13_y0]; norm_num)
    (by have e : (R13_zeroFree_of_bounds h).y1 = R13.y1 := rfl
        rw [e, R13_y1]; norm_num)

noncomputable def R13_conjLB_of_bounds (h : R13_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R13_lowerBound_of_bounds h)
    (by have e : (R13_lowerBound_of_bounds h).y0 = R13.y0 := rfl
        rw [e, R13_y0]; norm_num)
    (by have e : (R13_lowerBound_of_bounds h).y1 = R13.y1 := rfl
        rw [e, R13_y1]; norm_num)

noncomputable def R14_conjZF_of_bounds (h : R14_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R14_zeroFree_of_bounds h)
    (by have e : (R14_zeroFree_of_bounds h).y0 = R14.y0 := rfl
        rw [e, R14_y0]; norm_num)
    (by have e : (R14_zeroFree_of_bounds h).y1 = R14.y1 := rfl
        rw [e, R14_y1]; norm_num)

noncomputable def R14_conjLB_of_bounds (h : R14_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R14_lowerBound_of_bounds h)
    (by have e : (R14_lowerBound_of_bounds h).y0 = R14.y0 := rfl
        rw [e, R14_y0]; norm_num)
    (by have e : (R14_lowerBound_of_bounds h).y1 = R14.y1 := rfl
        rw [e, R14_y1]; norm_num)

noncomputable def R15_conjZF_of_bounds (h : R15_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R15_zeroFree_of_bounds h)
    (by have e : (R15_zeroFree_of_bounds h).y0 = R15.y0 := rfl
        rw [e, R15_y0]; norm_num)
    (by have e : (R15_zeroFree_of_bounds h).y1 = R15.y1 := rfl
        rw [e, R15_y1]; norm_num)

noncomputable def R15_conjLB_of_bounds (h : R15_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R15_lowerBound_of_bounds h)
    (by have e : (R15_lowerBound_of_bounds h).y0 = R15.y0 := rfl
        rw [e, R15_y0]; norm_num)
    (by have e : (R15_lowerBound_of_bounds h).y1 = R15.y1 := rfl
        rw [e, R15_y1]; norm_num)

noncomputable def R16_conjZF_of_bounds (h : R16_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R16_zeroFree_of_bounds h)
    (by have e : (R16_zeroFree_of_bounds h).y0 = R16.y0 := rfl
        rw [e, R16_y0]; norm_num)
    (by have e : (R16_zeroFree_of_bounds h).y1 = R16.y1 := rfl
        rw [e, R16_y1]; norm_num)

noncomputable def R16_conjLB_of_bounds (h : R16_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R16_lowerBound_of_bounds h)
    (by have e : (R16_lowerBound_of_bounds h).y0 = R16.y0 := rfl
        rw [e, R16_y0]; norm_num)
    (by have e : (R16_lowerBound_of_bounds h).y1 = R16.y1 := rfl
        rw [e, R16_y1]; norm_num)

noncomputable def R17_conjZF_of_bounds (h : R17_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R17_zeroFree_of_bounds h)
    (by have e : (R17_zeroFree_of_bounds h).y0 = R17.y0 := rfl
        rw [e, R17_y0]; norm_num)
    (by have e : (R17_zeroFree_of_bounds h).y1 = R17.y1 := rfl
        rw [e, R17_y1]; norm_num)

noncomputable def R17_conjLB_of_bounds (h : R17_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R17_lowerBound_of_bounds h)
    (by have e : (R17_lowerBound_of_bounds h).y0 = R17.y0 := rfl
        rw [e, R17_y0]; norm_num)
    (by have e : (R17_lowerBound_of_bounds h).y1 = R17.y1 := rfl
        rw [e, R17_y1]; norm_num)

noncomputable def R18_conjZF_of_bounds (h : R18_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R18_zeroFree_of_bounds h)
    (by have e : (R18_zeroFree_of_bounds h).y0 = R18.y0 := rfl
        rw [e, R18_y0]; norm_num)
    (by have e : (R18_zeroFree_of_bounds h).y1 = R18.y1 := rfl
        rw [e, R18_y1]; norm_num)

noncomputable def R18_conjLB_of_bounds (h : R18_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R18_lowerBound_of_bounds h)
    (by have e : (R18_lowerBound_of_bounds h).y0 = R18.y0 := rfl
        rw [e, R18_y0]; norm_num)
    (by have e : (R18_lowerBound_of_bounds h).y1 = R18.y1 := rfl
        rw [e, R18_y1]; norm_num)

noncomputable def R19_conjZF_of_bounds (h : R19_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R19_zeroFree_of_bounds h)
    (by have e : (R19_zeroFree_of_bounds h).y0 = R19.y0 := rfl
        rw [e, R19_y0]; norm_num)
    (by have e : (R19_zeroFree_of_bounds h).y1 = R19.y1 := rfl
        rw [e, R19_y1]; norm_num)

noncomputable def R19_conjLB_of_bounds (h : R19_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R19_lowerBound_of_bounds h)
    (by have e : (R19_lowerBound_of_bounds h).y0 = R19.y0 := rfl
        rw [e, R19_y0]; norm_num)
    (by have e : (R19_lowerBound_of_bounds h).y1 = R19.y1 := rfl
        rw [e, R19_y1]; norm_num)

noncomputable def R20_conjZF_of_bounds (h : R20_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R20_zeroFree_of_bounds h)
    (by have e : (R20_zeroFree_of_bounds h).y0 = R20.y0 := rfl
        rw [e, R20_y0]; norm_num)
    (by have e : (R20_zeroFree_of_bounds h).y1 = R20.y1 := rfl
        rw [e, R20_y1]; norm_num)

noncomputable def R20_conjLB_of_bounds (h : R20_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R20_lowerBound_of_bounds h)
    (by have e : (R20_lowerBound_of_bounds h).y0 = R20.y0 := rfl
        rw [e, R20_y0]; norm_num)
    (by have e : (R20_lowerBound_of_bounds h).y1 = R20.y1 := rfl
        rw [e, R20_y1]; norm_num)

noncomputable def R21_conjZF_of_bounds (h : R21_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R21_zeroFree_of_bounds h)
    (by have e : (R21_zeroFree_of_bounds h).y0 = R21.y0 := rfl
        rw [e, R21_y0]; norm_num)
    (by have e : (R21_zeroFree_of_bounds h).y1 = R21.y1 := rfl
        rw [e, R21_y1]; norm_num)

noncomputable def R21_conjLB_of_bounds (h : R21_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R21_lowerBound_of_bounds h)
    (by have e : (R21_lowerBound_of_bounds h).y0 = R21.y0 := rfl
        rw [e, R21_y0]; norm_num)
    (by have e : (R21_lowerBound_of_bounds h).y1 = R21.y1 := rfl
        rw [e, R21_y1]; norm_num)

noncomputable def R22_conjZF_of_bounds (h : R22_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R22_zeroFree_of_bounds h)
    (by have e : (R22_zeroFree_of_bounds h).y0 = R22.y0 := rfl
        rw [e, R22_y0]; norm_num)
    (by have e : (R22_zeroFree_of_bounds h).y1 = R22.y1 := rfl
        rw [e, R22_y1]; norm_num)

noncomputable def R22_conjLB_of_bounds (h : R22_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R22_lowerBound_of_bounds h)
    (by have e : (R22_lowerBound_of_bounds h).y0 = R22.y0 := rfl
        rw [e, R22_y0]; norm_num)
    (by have e : (R22_lowerBound_of_bounds h).y1 = R22.y1 := rfl
        rw [e, R22_y1]; norm_num)

noncomputable def R23_conjZF_of_bounds (h : R23_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R23_zeroFree_of_bounds h)
    (by have e : (R23_zeroFree_of_bounds h).y0 = R23.y0 := rfl
        rw [e, R23_y0]; norm_num)
    (by have e : (R23_zeroFree_of_bounds h).y1 = R23.y1 := rfl
        rw [e, R23_y1]; norm_num)

noncomputable def R23_conjLB_of_bounds (h : R23_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R23_lowerBound_of_bounds h)
    (by have e : (R23_lowerBound_of_bounds h).y0 = R23.y0 := rfl
        rw [e, R23_y0]; norm_num)
    (by have e : (R23_lowerBound_of_bounds h).y1 = R23.y1 := rfl
        rw [e, R23_y1]; norm_num)

noncomputable def R24_conjZF_of_bounds (h : R24_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R24_zeroFree_of_bounds h)
    (by have e : (R24_zeroFree_of_bounds h).y0 = R24.y0 := rfl
        rw [e, R24_y0]; norm_num)
    (by have e : (R24_zeroFree_of_bounds h).y1 = R24.y1 := rfl
        rw [e, R24_y1]; norm_num)

noncomputable def R24_conjLB_of_bounds (h : R24_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R24_lowerBound_of_bounds h)
    (by have e : (R24_lowerBound_of_bounds h).y0 = R24.y0 := rfl
        rw [e, R24_y0]; norm_num)
    (by have e : (R24_lowerBound_of_bounds h).y1 = R24.y1 := rfl
        rw [e, R24_y1]; norm_num)

noncomputable def R25_conjZF_of_bounds (h : R25_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R25_zeroFree_of_bounds h)
    (by have e : (R25_zeroFree_of_bounds h).y0 = R25.y0 := rfl
        rw [e, R25_y0]; norm_num)
    (by have e : (R25_zeroFree_of_bounds h).y1 = R25.y1 := rfl
        rw [e, R25_y1]; norm_num)

noncomputable def R25_conjLB_of_bounds (h : R25_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R25_lowerBound_of_bounds h)
    (by have e : (R25_lowerBound_of_bounds h).y0 = R25.y0 := rfl
        rw [e, R25_y0]; norm_num)
    (by have e : (R25_lowerBound_of_bounds h).y1 = R25.y1 := rfl
        rw [e, R25_y1]; norm_num)

noncomputable def R26_conjZF_of_bounds (h : R26_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R26_zeroFree_of_bounds h)
    (by have e : (R26_zeroFree_of_bounds h).y0 = R26.y0 := rfl
        rw [e, R26_y0]; norm_num)
    (by have e : (R26_zeroFree_of_bounds h).y1 = R26.y1 := rfl
        rw [e, R26_y1]; norm_num)

noncomputable def R26_conjLB_of_bounds (h : R26_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R26_lowerBound_of_bounds h)
    (by have e : (R26_lowerBound_of_bounds h).y0 = R26.y0 := rfl
        rw [e, R26_y0]; norm_num)
    (by have e : (R26_lowerBound_of_bounds h).y1 = R26.y1 := rfl
        rw [e, R26_y1]; norm_num)

noncomputable def R27_conjZF_of_bounds (h : R27_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R27_zeroFree_of_bounds h)
    (by have e : (R27_zeroFree_of_bounds h).y0 = R27.y0 := rfl
        rw [e, R27_y0]; norm_num)
    (by have e : (R27_zeroFree_of_bounds h).y1 = R27.y1 := rfl
        rw [e, R27_y1]; norm_num)

noncomputable def R27_conjLB_of_bounds (h : R27_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R27_lowerBound_of_bounds h)
    (by have e : (R27_lowerBound_of_bounds h).y0 = R27.y0 := rfl
        rw [e, R27_y0]; norm_num)
    (by have e : (R27_lowerBound_of_bounds h).y1 = R27.y1 := rfl
        rw [e, R27_y1]; norm_num)

noncomputable def R28_conjZF_of_bounds (h : R28_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R28_zeroFree_of_bounds h)
    (by have e : (R28_zeroFree_of_bounds h).y0 = R28.y0 := rfl
        rw [e, R28_y0]; norm_num)
    (by have e : (R28_zeroFree_of_bounds h).y1 = R28.y1 := rfl
        rw [e, R28_y1]; norm_num)

noncomputable def R28_conjLB_of_bounds (h : R28_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R28_lowerBound_of_bounds h)
    (by have e : (R28_lowerBound_of_bounds h).y0 = R28.y0 := rfl
        rw [e, R28_y0]; norm_num)
    (by have e : (R28_lowerBound_of_bounds h).y1 = R28.y1 := rfl
        rw [e, R28_y1]; norm_num)

noncomputable def R29_conjZF_of_bounds (h : R29_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R29_zeroFree_of_bounds h)
    (by have e : (R29_zeroFree_of_bounds h).y0 = R29.y0 := rfl
        rw [e, R29_y0]; norm_num)
    (by have e : (R29_zeroFree_of_bounds h).y1 = R29.y1 := rfl
        rw [e, R29_y1]; norm_num)

noncomputable def R29_conjLB_of_bounds (h : R29_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R29_lowerBound_of_bounds h)
    (by have e : (R29_lowerBound_of_bounds h).y0 = R29.y0 := rfl
        rw [e, R29_y0]; norm_num)
    (by have e : (R29_lowerBound_of_bounds h).y1 = R29.y1 := rfl
        rw [e, R29_y1]; norm_num)

noncomputable def R30_conjZF_of_bounds (h : R30_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R30_zeroFree_of_bounds h)
    (by have e : (R30_zeroFree_of_bounds h).y0 = R30.y0 := rfl
        rw [e, R30_y0]; norm_num)
    (by have e : (R30_zeroFree_of_bounds h).y1 = R30.y1 := rfl
        rw [e, R30_y1]; norm_num)

noncomputable def R30_conjLB_of_bounds (h : R30_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R30_lowerBound_of_bounds h)
    (by have e : (R30_lowerBound_of_bounds h).y0 = R30.y0 := rfl
        rw [e, R30_y0]; norm_num)
    (by have e : (R30_lowerBound_of_bounds h).y1 = R30.y1 := rfl
        rw [e, R30_y1]; norm_num)

noncomputable def R31_conjZF_of_bounds (h : R31_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R31_zeroFree_of_bounds h)
    (by have e : (R31_zeroFree_of_bounds h).y0 = R31.y0 := rfl
        rw [e, R31_y0]; norm_num)
    (by have e : (R31_zeroFree_of_bounds h).y1 = R31.y1 := rfl
        rw [e, R31_y1]; norm_num)

noncomputable def R31_conjLB_of_bounds (h : R31_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R31_lowerBound_of_bounds h)
    (by have e : (R31_lowerBound_of_bounds h).y0 = R31.y0 := rfl
        rw [e, R31_y0]; norm_num)
    (by have e : (R31_lowerBound_of_bounds h).y1 = R31.y1 := rfl
        rw [e, R31_y1]; norm_num)

noncomputable def R32_conjZF_of_bounds (h : R32_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R32_zeroFree_of_bounds h)
    (by have e : (R32_zeroFree_of_bounds h).y0 = R32.y0 := rfl
        rw [e, R32_y0]; norm_num)
    (by have e : (R32_zeroFree_of_bounds h).y1 = R32.y1 := rfl
        rw [e, R32_y1]; norm_num)

noncomputable def R32_conjLB_of_bounds (h : R32_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R32_lowerBound_of_bounds h)
    (by have e : (R32_lowerBound_of_bounds h).y0 = R32.y0 := rfl
        rw [e, R32_y0]; norm_num)
    (by have e : (R32_lowerBound_of_bounds h).y1 = R32.y1 := rfl
        rw [e, R32_y1]; norm_num)

noncomputable def R33_conjZF_of_bounds (h : R33_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R33_zeroFree_of_bounds h)
    (by have e : (R33_zeroFree_of_bounds h).y0 = R33.y0 := rfl
        rw [e, R33_y0]; norm_num)
    (by have e : (R33_zeroFree_of_bounds h).y1 = R33.y1 := rfl
        rw [e, R33_y1]; norm_num)

noncomputable def R33_conjLB_of_bounds (h : R33_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R33_lowerBound_of_bounds h)
    (by have e : (R33_lowerBound_of_bounds h).y0 = R33.y0 := rfl
        rw [e, R33_y0]; norm_num)
    (by have e : (R33_lowerBound_of_bounds h).y1 = R33.y1 := rfl
        rw [e, R33_y1]; norm_num)

noncomputable def R34_conjZF_of_bounds (h : R34_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R34_zeroFree_of_bounds h)
    (by have e : (R34_zeroFree_of_bounds h).y0 = R34.y0 := rfl
        rw [e, R34_y0]; norm_num)
    (by have e : (R34_zeroFree_of_bounds h).y1 = R34.y1 := rfl
        rw [e, R34_y1]; norm_num)

noncomputable def R34_conjLB_of_bounds (h : R34_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R34_lowerBound_of_bounds h)
    (by have e : (R34_lowerBound_of_bounds h).y0 = R34.y0 := rfl
        rw [e, R34_y0]; norm_num)
    (by have e : (R34_lowerBound_of_bounds h).y1 = R34.y1 := rfl
        rw [e, R34_y1]; norm_num)

noncomputable def R35_conjZF_of_bounds (h : R35_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R35_zeroFree_of_bounds h)
    (by have e : (R35_zeroFree_of_bounds h).y0 = R35.y0 := rfl
        rw [e, R35_y0]; norm_num)
    (by have e : (R35_zeroFree_of_bounds h).y1 = R35.y1 := rfl
        rw [e, R35_y1]; norm_num)

noncomputable def R35_conjLB_of_bounds (h : R35_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R35_lowerBound_of_bounds h)
    (by have e : (R35_lowerBound_of_bounds h).y0 = R35.y0 := rfl
        rw [e, R35_y0]; norm_num)
    (by have e : (R35_lowerBound_of_bounds h).y1 = R35.y1 := rfl
        rw [e, R35_y1]; norm_num)

noncomputable def R36_conjZF_of_bounds (h : R36_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R36_zeroFree_of_bounds h)
    (by have e : (R36_zeroFree_of_bounds h).y0 = R36.y0 := rfl
        rw [e, R36_y0]; norm_num)
    (by have e : (R36_zeroFree_of_bounds h).y1 = R36.y1 := rfl
        rw [e, R36_y1]; norm_num)

noncomputable def R36_conjLB_of_bounds (h : R36_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R36_lowerBound_of_bounds h)
    (by have e : (R36_lowerBound_of_bounds h).y0 = R36.y0 := rfl
        rw [e, R36_y0]; norm_num)
    (by have e : (R36_lowerBound_of_bounds h).y1 = R36.y1 := rfl
        rw [e, R36_y1]; norm_num)

noncomputable def R37_conjZF_of_bounds (h : R37_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R37_zeroFree_of_bounds h)
    (by have e : (R37_zeroFree_of_bounds h).y0 = R37.y0 := rfl
        rw [e, R37_y0]; norm_num)
    (by have e : (R37_zeroFree_of_bounds h).y1 = R37.y1 := rfl
        rw [e, R37_y1]; norm_num)

noncomputable def R37_conjLB_of_bounds (h : R37_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R37_lowerBound_of_bounds h)
    (by have e : (R37_lowerBound_of_bounds h).y0 = R37.y0 := rfl
        rw [e, R37_y0]; norm_num)
    (by have e : (R37_lowerBound_of_bounds h).y1 = R37.y1 := rfl
        rw [e, R37_y1]; norm_num)

noncomputable def R38_conjZF_of_bounds (h : R38_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R38_zeroFree_of_bounds h)
    (by have e : (R38_zeroFree_of_bounds h).y0 = R38.y0 := rfl
        rw [e, R38_y0]; norm_num)
    (by have e : (R38_zeroFree_of_bounds h).y1 = R38.y1 := rfl
        rw [e, R38_y1]; norm_num)

noncomputable def R38_conjLB_of_bounds (h : R38_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R38_lowerBound_of_bounds h)
    (by have e : (R38_lowerBound_of_bounds h).y0 = R38.y0 := rfl
        rw [e, R38_y0]; norm_num)
    (by have e : (R38_lowerBound_of_bounds h).y1 = R38.y1 := rfl
        rw [e, R38_y1]; norm_num)

noncomputable def R39_conjZF_of_bounds (h : R39_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R39_zeroFree_of_bounds h)
    (by have e : (R39_zeroFree_of_bounds h).y0 = R39.y0 := rfl
        rw [e, R39_y0]; norm_num)
    (by have e : (R39_zeroFree_of_bounds h).y1 = R39.y1 := rfl
        rw [e, R39_y1]; norm_num)

noncomputable def R39_conjLB_of_bounds (h : R39_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R39_lowerBound_of_bounds h)
    (by have e : (R39_lowerBound_of_bounds h).y0 = R39.y0 := rfl
        rw [e, R39_y0]; norm_num)
    (by have e : (R39_lowerBound_of_bounds h).y1 = R39.y1 := rfl
        rw [e, R39_y1]; norm_num)

noncomputable def R40_conjZF_of_bounds (h : R40_leaf_obligations) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect.conj_of (R40_zeroFree_of_bounds h)
    (by have e : (R40_zeroFree_of_bounds h).y0 = R40.y0 := rfl
        rw [e, R40_y0]; norm_num)
    (by have e : (R40_zeroFree_of_bounds h).y1 = R40.y1 := rfl
        rw [e, R40_y1]; norm_num)

noncomputable def R40_conjLB_of_bounds (h : R40_leaf_obligations) : XiLocalLowerBoundRect :=
  XiLocalLowerBoundRect.conj_of (R40_lowerBound_of_bounds h)
    (by have e : (R40_lowerBound_of_bounds h).y0 = R40.y0 := rfl
        rw [e, R40_y0]; norm_num)
    (by have e : (R40_lowerBound_of_bounds h).y1 = R40.y1 := rfl
        rw [e, R40_y1]; norm_num)

/-- Lower-half cover: every `z` with `-10 < Re < 10`, `-0.49 ≤ Im < 0`
is nonvanishing, via `star z` + `central_upper_covered` + conjugate symmetry.
This is the closed lower counterpart of the upper cell/strip either/or:
`star z` lies either in the boundary strip or in a closed packaged upper cell,
hence `z` lies in the conjugated lower cell or the mirrored strip. -/
theorem central_lower_covered (hFull : FullCentralObligations)
    (hStrip : BottomStripObligations)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_ge : -0.49 ≤ z.im) (hy_neg : z.im < 0) :
    xiShifted z ≠ 0 := by
  have hstar_re : (star z).re = z.re := by simp [conj_re]
  have hstar_im : (star z).im = -z.im := by simp [conj_im]
  have hstar_lo : -10 < (star z).re := by rw [hstar_re]; exact hx_lo
  have hstar_hi : (star z).re < 10 := by rw [hstar_re]; exact hx_hi
  have hstar_pos : 0 < (star z).im := by rw [hstar_im]; linarith
  have hstar_le : (star z).im ≤ 0.49 := by rw [hstar_im]; linarith
  have h_nz_star : xiShifted (star z) ≠ 0 :=
    central_upper_covered hFull hStrip hstar_lo hstar_hi hstar_pos hstar_le
  have h_im_lt : z.im < 1 / 2 := by linarith
  have h_im_gt : -1 / 2 < z.im := by linarith
  have hsym := classicalXi_symmetry.conj_symm z h_im_gt h_im_lt
  intro hzero
  have h2 : star (xiShifted z) = 0 := by simp [hzero]
  have h3 : xiShifted (star z) = 0 := by rw [hsym]; exact h2
  exact h_nz_star h3

/-- Combined central cover (both halves): every `z` with `-10 < Re < 10` and
`Im ∈ (0,0.49] ∪ [-0.49,0)` is nonvanishing. Positive side is
strip-or-closed-upper-cell (`central_upper_covered`); negative side is the
conjugated mirror (`central_lower_covered` via `conj_of` transfers).
Endpoints `±10`, `[0.49,1/2)`, and the real axis are excluded (separate tasks). -/
theorem full_central_covered (hFull : FullCentralObligations)
    (hStrip : BottomStripObligations)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy : (0 < z.im ∧ z.im ≤ 0.49) ∨ (-0.49 ≤ z.im ∧ z.im < 0)) :
    xiShifted z ≠ 0 := by
  rcases hy with ⟨hpos, hle⟩ | ⟨hge, hneg⟩
  · exact central_upper_covered hFull hStrip hx_lo hx_hi hpos hle
  · exact central_lower_covered hFull hStrip hx_lo hx_hi hge hneg

#print axioms row1_covered
#print axioms row2_covered
#print axioms top_covered
#print axioms central_upper_covered
#print axioms central_lower_covered
#print axioms full_central_covered

end CentralCoverAssembly

/-! ## Cauchy derivative estimate for `xiShifted` via `xiShiftedEntire` (DERIV-factor bridge)

Goal: unblock the DERIV factor `‖deriv xiShifted w‖ ≤ M` uniformly on each of the
40 `gridFine` rects.

Grep-first record (verified 2026-09-03, repo + Mathlib):
* `rg "xiShiftedEntire"` → only the strip entireness family in this file
  (`xiShiftedEntire`, `xiShiftedEntire_differentiable`, `xiShifted_eq_entire_on_strip`,
  `strip_isOpen`, `xiShifted_differentiableAt_of_mem_strip`,
  `deriv_xiShifted_eq_entire_of_mem_strip`); no Cauchy/uniform-derivative
  infrastructure for `xiShifted` exists anywhere else.
* `rg "circleIntegral"` → only Mathlib (`CauchyIntegral.lean`, `Liouville.lean`,
  `Schwarz.lean`, …) + docs yamls; no repo-level Cauchy material for `xiShifted`.
* `rg "norm_deriv"` → Mathlib Schwarz (`norm_deriv_le_div_of_mapsTo_ball`) +
  Liouville (`norm_deriv_le_of_forall_mem_sphere_norm_le`) + unrelated simple-zero
  facts in `riemann_hypothesis.lean`; no uniform `‖deriv xiShifted‖` bounds.
* `rg "R02Uniform|center_bound_of_component_bounds"` → `interval_arith.lean`
  has the four-factor center bridge (`CellUniform.center_bound_of_component_bounds`)
  + `R02Uniform` template (hypothesis-free poly `22`, pi `1/2`, Gamma `1/1e7`,
  conditional `R02_H_of_components` modulo zeta factor + deriv bound); no deriv
  sup discharge.
* `rg "import.*central_cover|import.*interval_arith"` → `interval_arith` and
  `central_cover_trusted` import this file; this file imports only `Mathlib`,
  `riemann_hypothesis`, `rh_certificate_infra`. Hence NO new imports are added
  below (avoids cycles); all Cauchy material used is already in `Mathlib`.

Consequence: Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
(Liouville.lean:76, via `DiffContOnCl.deriv_eq_smul_circleIntegral`) suffices;
nothing circle-integral-related is re-proved here. What is proved here:
1. Generic pointwise Cauchy lemma for `xiShifted` from a sup bound on
   `xiShiftedEntire` over `Metric.sphere w R` (fully proved, only explicit
   sup-bound hypotheses).
2. Uniform rect versions (per-`w` spheres; single-`closedBall` region via triangle).
3. For `R02 = (-8,-5.5,0.01,0.2)` (outer tier) with radius `r = 0.25`:
   hypothesis-free poly `≤ 42`, pi `≤ 1`, Gamma `≤ 40` on the `0.25`-disc
   (`s`-rect `Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`), conditional entire sup
   `≤ 16800` modulo exactly one named zeta-upper supplier, hence conditional
   uniform `‖deriv xiShifted‖ ≤ 67200` on `R02` (first concrete `M` for any cell,
   albeit too large for fencing — see residual).

Exact supplier shapes (Agents D/E-style):
* `DerivCauchyBridge.R02_zeta_upper_obligation` (below): `∀ s, ... → ‖zeta s‖ ≤ 10`
  on the R02 disc `s`-rect. To be discharged by rigorous complex-`zeta` interval
  arithmetic (Dirichlet-eta + remainder, cf. `R00ZetaEM` in `interval_arith.lean`;
  true `|ζ| = O(1)` there, so `10` is safe). Covers cell R02 only; other 39 cells
  need analogous `s`-rect zeta uppers (same shape, different numeric rects).
* No other hypotheses are used: poly/pi/Gamma uppers are hypothesis-free.
-/

namespace DerivCauchyBridge

/-- Generic pointwise Cauchy estimate for `xiShifted` via the entire extension.
From a sup bound `C` for `xiShiftedEntire` on `sphere w R` (exact shape suppliers
must discharge), `‖deriv xiShifted w‖ ≤ C / R`. Uses strip agreement at `w` only;
the ball itself may leave the strip since the extension is entire. -/
theorem deriv_xiShifted_le_of_entire_sphere_bound
    (w : ℂ) (R C : ℝ) (hR : 0 < R)
    (hw_lo : -(1 / 2 : ℝ) < w.im) (hw_hi : w.im < (1 / 2 : ℝ))
    (hC : ∀ z ∈ Metric.sphere w R, ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ‖deriv xiShifted w‖ ≤ C / R := by
  have hEnt : Differentiable ℂ CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable
  have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire (Metric.ball w R) :=
    hEnt.diffContOnCl
  have hBound : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hDC hC
  have hEq : deriv xiShifted w = deriv CentralCoverAssembly.xiShiftedEntire w :=
    CentralCoverAssembly.deriv_xiShifted_eq_entire_of_mem_strip w hw_lo hw_hi
  rw [hEq]
  exact hBound

/-- Uniform rect version from per-`w` sphere bounds: `M = C / r`. -/
theorem uniform_deriv_of_sphere_bound
    (Rrect : CellProofEngine.Rect2D) (r C : ℝ) (hr : 0 < r)
    (hStrip : ∀ w, Rrect.mem w → -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ))
    (hC : ∀ w, Rrect.mem w → ∀ z ∈ Metric.sphere w r,
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, Rrect.mem w → ‖deriv xiShifted w‖ ≤ C / r := by
  intro w hw
  obtain ⟨hlo, hhi⟩ := hStrip w hw
  exact deriv_xiShifted_le_of_entire_sphere_bound w r C hr hlo hhi (hC w hw)

/-- Spheres over a rect lie in the `closedBall` of the center with radius
`radius + r` (triangle inequality via `Rect2D.norm_sub_center_le_radius`). -/
theorem sphere_subset_closedBall_of_rect_mem
    (Rrect : CellProofEngine.Rect2D) (r : ℝ)
    (w : ℂ) (hw : Rrect.mem w) :
    Metric.sphere w r ⊆ Metric.closedBall Rrect.center (Rrect.radius + r) := by
  intro z hz
  rw [Metric.mem_closedBall]
  have hdist : dist z w = r := Metric.mem_sphere.mp hz
  have hnorm_zw : ‖z - w‖ = r := by rwa [dist_eq_norm] at hdist
  have hnorm_wc : ‖w - Rrect.center‖ ≤ Rrect.radius :=
    CellProofEngine.Rect2D.norm_sub_center_le_radius Rrect hw
  have heq : z - Rrect.center = (z - w) + (w - Rrect.center) := by abel
  have hle : ‖z - Rrect.center‖ ≤ ‖z - w‖ + ‖w - Rrect.center‖ := by
    rw [heq]
    exact norm_add_le _ _
  have hdist_eq : dist z Rrect.center = ‖z - Rrect.center‖ := dist_eq_norm _ _
  rw [hdist_eq]
  linarith

/-- Uniform rect version from a single `closedBall` sup bound (supplier-friendly
shape: one region instead of per-`w` spheres). -/
theorem uniform_deriv_of_closedBall_bound
    (Rrect : CellProofEngine.Rect2D) (r C : ℝ) (hr : 0 < r)
    (hStrip : ∀ w, Rrect.mem w → -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ))
    (hCball : ∀ z ∈ Metric.closedBall Rrect.center (Rrect.radius + r),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, Rrect.mem w → ‖deriv xiShifted w‖ ≤ C / r := by
  apply uniform_deriv_of_sphere_bound Rrect r C hr hStrip
  intro w hw z hz
  exact hCball z (sphere_subset_closedBall_of_rect_mem Rrect r w hw hz)

/-! ### R02 disc geometry (`r = 0.25` stays in the strip) -/

/-- `R02.mem` unpacked to numeric bounds. -/
theorem R02_mem_bounds {w : ℂ} (hw : CentralCoverAssembly.R02.mem w) :
    -8 ≤ w.re ∧ w.re ≤ -5.5 ∧ 0.01 ≤ w.im ∧ w.im ≤ 0.2 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R02.x0 = -8 := CentralCoverAssembly.R02_x0
  have e1 : CentralCoverAssembly.R02.x1 = -5.5 := CentralCoverAssembly.R02_x1
  have e2 : CentralCoverAssembly.R02.y0 = 0.01 := CentralCoverAssembly.R02_y0
  have e3 : CentralCoverAssembly.R02.y1 = 0.2 := CentralCoverAssembly.R02_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every `R02` point lies in the open strip (hence deriv transfer applies). -/
theorem R02_strip_of_mem {w : ℂ} (hw : CentralCoverAssembly.R02.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := R02_mem_bounds hw
  constructor <;> linarith

/-- Real parts on the `0.25`-sphere over `R02`: `[-8.25,-5.25]`. -/
theorem R02_sphere_re_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    -8.25 ≤ u.re ∧ u.re ≤ -5.25 := by
  obtain ⟨hx0, hx1, _, _⟩ := R02_mem_bounds hw
  have hdist : dist u w = (0.25 : ℝ) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.25 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.25 : ℝ) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.25 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.25`-sphere over `R02`: `[-0.24,0.45]`. -/
theorem R02_sphere_im_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    -0.24 ≤ u.im ∧ u.im ≤ 0.45 := by
  obtain ⟨_, _, hy0, hy1⟩ := R02_mem_bounds hw
  have hdist : dist u w = (0.25 : ℝ) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.25 : ℝ) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.25 : ℝ) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.25 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.25`-sphere over `R02` stays strictly inside the strip
(`[-0.24,0.45] ⊂ (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R02_sphere_mem_strip {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := R02_sphere_im_bounds hw hu
  constructor <;> linarith

/-- `s = 1/2 + I*u` coordinates for `u` on the R02 `0.25`-sphere:
`s.re ∈ [0.05,0.74]`, `s.im ∈ [-8.25,-5.25]`. -/
theorem R02_s_of_sphere_re_im {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    0.05 ≤ ((1 / 2 : ℂ) + Complex.I * u).re ∧
    ((1 / 2 : ℂ) + Complex.I * u).re ≤ 0.74 ∧
    -8.25 ≤ ((1 / 2 : ℂ) + Complex.I * u).im ∧
    ((1 / 2 : ℂ) + Complex.I * u).im ≤ -5.25 := by
  obtain ⟨hre_lo, hre_hi⟩ := R02_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R02_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : ℂ) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : ℂ) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, hre_lo, hre_hi⟩

/-! ### Four-factor upper bounds on the R02 disc (poly/pi/Gamma hypothesis-free) -/

/-- Polynomial part `s*(s-1)/2` (equals `1/2*s*(s-1)` by `ring`). -/
noncomputable def polyOf (s : ℂ) : ℂ := s * (s - 1) / 2

/-- Pi-power part `π^(-s/2)`. -/
noncomputable def piOf (s : ℂ) : ℂ := ((Real.pi : ℂ) ^ (-(s / 2)))

/-- Gamma part `Γ(s/2)`. -/
noncomputable def gammaOf (s : ℂ) : ℂ := Complex.Gamma (s / 2)

/-- Top-level `xiShifted` factored via our local parts (mirrors
`R00Enclosure.xiShifted_eq_parts` in `interval_arith.lean`, re-proved here to
avoid an import cycle: that file imports this one). -/
theorem xiShifted_eq_parts (z : ℂ) :
    xiShifted z =
      polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      piOf ((1 / 2 : ℂ) + Complex.I * z) *
      gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) := by
  unfold xiShifted classicalXi XiFromPrefactor classicalXiPrefactor
    polyOf piOf gammaOf
  ring

/-- Norm version of the factorisation. -/
theorem norm_xiShifted_eq_parts (z : ℂ) :
    ‖xiShifted z‖ =
      ‖polyOf ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖piOf ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖gammaOf ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖zeta ((1 / 2 : ℂ) + Complex.I * z)‖ := by
  rw [xiShifted_eq_parts z, norm_mul, norm_mul, norm_mul]

/-- Hypothesis-free poly upper `‖poly‖ ≤ 42` on the R02 disc `s`-rect
(triangle `‖z‖ ≤ |re|+|im|`; `8.99*9.2/2 = 41.354 < 42`). -/
theorem poly_upper_R02_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖polyOf s‖ ≤ 42 := by
  unfold polyOf
  have hs_le : ‖s‖ ≤ 8.99 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.74 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 8.25 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 9.2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 0.95 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 8.25 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 8.99 * 9.2 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 8.99 * 9.2 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (8.99 : ℝ) * 9.2 / 2 ≤ 42 := by norm_num
  linarith

/-- Hypothesis-free pi upper `‖π^(-s/2)‖ ≤ 1` for `0.05 ≤ s.re`
(`‖·‖ = π^(-s.re/2)`, exponent `≤ 0`, base `π ≥ 1`). -/
theorem pi_upper_R02_disc {s : ℂ} (hre_lo : 0.05 ≤ s.re) :
    ‖piOf s‖ ≤ 1 := by
  unfold piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  have hle : (-(s / 2)).re ≤ 0 := by
    rw [hneg, h2]
    linarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact Real.rpow_le_one_of_one_le_of_nonpos hpi1 hle

/-- Integral majorant `‖Γ z‖ ≤ Real.Gamma z.re` for `0 < z.re`
(triangle inequality for the Euler integral; same proof as
`R00GammaLower.norm_Gamma_le_realGamma` in `interval_arith.lean`, re-proved
here to avoid an import cycle). -/
theorem norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have hC := Complex.GammaIntegral_convergent hz
  have hR := Real.GammaIntegral_convergent hz
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
        show ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ = _
        rw [norm_mul]
        have h1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) :=
          Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))
        have h2 : ‖(x : ℂ) ^ (z - 1)‖ = x ^ ((z - 1).re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
        rw [h1, h2]
        have hexp : (z - 1).re = z.re - 1 := by simp [Complex.sub_re]
        rw [hexp]

/-- Real-Gamma upper `Real.Gamma x ≤ 40` for `x ∈ [0.025,0.37]`
(convexity on `[1,2]` gives `Γ(x+1) ≤ 1`, then `Γ(x) = Γ(x+1)/x ≤ 1/0.025`). -/
theorem realGamma_le_40_of_mem {x : ℝ}
    (hx_lo : 0.025 ≤ x) (hx_hi : x ≤ 0.37) : Real.Gamma x ≤ 40 := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hy_mem1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_lo : (1 : ℝ) ≤ x + 1 := by linarith
  have hy_hi : x + 1 ≤ (2 : ℝ) := by linarith
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - (x + 1) := by linarith
  have hb_nn : (0 : ℝ) ≤ (x + 1) - 1 := by linarith
  have hab : (2 - (x + 1)) + ((x + 1) - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (2 - (x + 1)) * 1 + ((x + 1) - 1) * 2 = x + 1 := by ring
  rw [heq] at h
  have hrhs : (2 - (x + 1)) * 1 + ((x + 1) - 1) * 1 = (1 : ℝ) := by ring
  rw [hrhs] at h
  have hne : x ≠ 0 := ne_of_gt hx_pos
  have hadd := Real.Gamma_add_one hne
  rw [hadd] at h
  have hfin : Real.Gamma x ≤ 1 / x := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h
  have hfrac : (1 : ℝ) / x ≤ 40 := by
    have h1 : (1 : ℝ) / x ≤ 1 / 0.025 :=
      one_div_le_one_div_of_le (by norm_num) hx_lo
    have h2 : (1 : ℝ) / 0.025 ≤ 40 := by norm_num
    exact le_trans h1 h2
  exact le_trans hfin hfrac

/-- Hypothesis-free Gamma upper `‖Γ(s/2)‖ ≤ 40` on the R02 disc `s`-rect. -/
theorem gamma_upper_R02_disc {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74) :
    ‖gammaOf s‖ ≤ 40 := by
  unfold gammaOf
  have h2re : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hzpos : (0 : ℝ) < (s / 2).re := by
    rw [h2re]
    linarith
  have hle := norm_Gamma_le_realGamma hzpos
  have hx_lo : (0.025 : ℝ) ≤ (s / 2).re := by
    rw [h2re]
    linarith
  have hx_hi : (s / 2).re ≤ (0.37 : ℝ) := by
    rw [h2re]
    linarith
  have hreal := realGamma_le_40_of_mem hx_lo hx_hi
  linarith

/-! ### Conditional R02 sup + first concrete `M` -/

/-- The single remaining supplier obligation for the R02 Cauchy disc:
uniform `‖zeta s‖ ≤ 10` on the `s`-rect `Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`
(true `|ζ| = O(1)` there; to be discharged by rigorous complex-`zeta` interval
arithmetic via Dirichlet-eta + remainder, cf. `R00ZetaEM` in
`interval_arith.lean`). Covers cell R02 only. -/
def R02_zeta_upper_obligation : Prop :=
  ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
    ‖zeta s‖ ≤ 10

/-- Conditional `xiShifted` upper on an R02 sphere point from the zeta supplier:
`‖ξ‖ ≤ 42*1*40*10 = 16800`. -/
theorem xiShifted_upper_of_zeta_upper_R02 {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ))
    (hZ : R02_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 16800 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ := R02_s_of_sphere_re_im hw hu
  have hpoly := poly_upper_R02_disc hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := pi_upper_R02_disc hsre_lo
  have hgam := gamma_upper_R02_disc hsre_lo hsre_hi
  have hzeta : ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 10 :=
    hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖piOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 * 40 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 * 40 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (42 : ℝ) * 1 * 40 * 10 = 16800 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the sphere (agrees in the strip). -/
theorem entire_upper_of_zeta_upper_R02 {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ))
    (hZ : R02_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 16800 := by
  obtain ⟨hlo, hhi⟩ := R02_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact xiShifted_upper_of_zeta_upper_R02 hw hu hZ

/-- Uniform sup `16800` on all R02 `0.25`-spheres from the zeta supplier. -/
theorem R02_uniform_sphere_bound (hZ : R02_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R02.mem w → ∀ z ∈ Metric.sphere w (0.25 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 := by
  intro w hw z hz
  exact entire_upper_of_zeta_upper_R02 hw hz hZ

/-- R02's first concrete derivative bound: uniform `‖deriv xiShifted‖ ≤ 67200`
(`16800 / 0.25`) modulo exactly `R02_zeta_upper_obligation` (zeta `≤ 10` on the
disc `s`-rect). Poly/pi/Gamma factors are hypothesis-free above. -/
theorem R02_deriv_bound_of_zeta_upper (hZ : R02_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ 67200 := by
  have hM := uniform_deriv_of_sphere_bound CentralCoverAssembly.R02 0.25 16800
    (by norm_num) (fun w hw => R02_strip_of_mem hw) (R02_uniform_sphere_bound hZ)
  intro w hw
  have hle := hM w hw
  have heq : (16800 : ℝ) / 0.25 = 67200 := by norm_num
  rw [heq] at hle
  exact hle

#print axioms deriv_xiShifted_le_of_entire_sphere_bound
#print axioms uniform_deriv_of_sphere_bound
#print axioms uniform_deriv_of_closedBall_bound
#print axioms R02_deriv_bound_of_zeta_upper

end DerivCauchyBridge
/-! ## Edge-strip + cutoff-line residual scaffolding (door-2 capstone `XiCentralEdgeStrips10`, `XiCutoffLines10`)

Grep-first record (verified 2026-09-03, repo + Mathlib, `rg`):
* `rg "XiCentralEdgeStrips10|XiCutoffLines10"` -> only `riemann_hypothesis.lean` door-2 capstone defs + assembly (`xiCentralRect10_of_mainBand_and_edgeStrips`, `xiOffRealPointwiseNonvanishing_of_rect10_tail10_cutoff`, `rh_from_mainBand10_edgeStrips10_tail10_cutoff`) + `AGENT_INFRASTRUCTURE_GUIDE.md` section 18b.10; no proofs, only hypothesis Props + assembly (no `sorry`, assembly proved).
* `rg "upper_boundary_nonvanishing_from_outer_bound"` -> `rh_certificate_infra.lean` Theorem 3 (outer bound, generic `f`, needs `Differentiable`, top value + vertical deriv bound) + mentions in `central_cover_assembly.lean` inventory comments only; no instantiation for strips.
* `rg "boundary_strip_nonvanishing_of_nonzero_base"` -> `rh_certificate_infra.lean` Theorem 1 + `central_cover_assembly.lean` bottom-strip instantiation (`BottomStripObligations`, `bottom_strip_covered` via `xiShiftedEntire`); top edge `[0.49,1/2)` has no instantiation.
* `rg "CellGammaUpper|realGamma_.*_le_one|Gamma_add_one"` -> `interval_arith.lean` 40/40 Gamma upper caps for row re-values `{0.395,0.3,0.2,0.105}` (i.e. `s.re`), plus `DerivCauchyBridge` in this file (`norm_Gamma_le_realGamma`, `realGamma_le_40_of_mem`, `gamma_upper_R02_disc` upper `40`). No strip re-value `(0,0.01]` chain exists anywhere.
* `rg "R02_zeta_upper_obligation|R02_deriv_bound_unconditional"` -> `central_cover_assembly.lean` conditional upper `10` gives `M=67200`; unconditional upper `1012` gives `M=6800640` lives in `riemann_hypothesis_newsection.lean` (`R02ZetaUpper`, `R02DerivBridge`), not here; tail Float certs (`Im` in `[10,12]`) do NOT cover strips or center.
* `rg "fineGridX|gridFine|innerGridY"` -> this file only (`fineGridX` 10 columns width `2.5`, `innerGridY` 4 rows, `gridFine` 40 cells, `gridFine_covers_inner`, `full_central_covered` for `(-10,10)` times `((0,0.49]` union `[-0.49,0))`); strips `[0.49,1/2)` plus lines `Re=±10` uncovered.

Consequence: strips need NEW re-value `s.re=1/2-y` in `(0,0.01]` Gamma chain (below: hypothesis-free poly and pi plus center Gamma upper `400` at new re-value, mirroring `DerivCauchyBridge` one-over-x route, distinct names); cutoffs need thin vertical rects staying strictly inside strip (below: `CutL10` and `CutR10` with `y` in `(-0.49,0.49)`, radius `<0.56`). Full cell closure (center lower plus uniform deriv upper plus `inner_nonvanishing_of_fenced_grid_fine` H-leaf) remains blocked by rigorous complex-`zeta` interval arithmetic (same wall as 40 central cells: `Azeta` lower plus tight upper `10`); no `sorry` or `admit` or `axiom` used, zero cells claimed closed, honest residual inventoried at end.
-/

namespace CentralCoverAssembly

open CellProofEngine

/-- The 10 edge-strip cells `y` in `(0.49,0.5)` over the 10 `fineGridX` columns. -/
def edgeStripCells : List (ℝ × ℝ × ℝ × ℝ) :=
  [(-10, -7.5, 0.49, 0.5),
   (-8, -5.5, 0.49, 0.5),
   (-6, -3.5, 0.49, 0.5),
   (-4, -1.5, 0.49, 0.5),
   (-2, 0.5, 0.49, 0.5),
   (0, 2.5, 0.49, 0.5),
   (2, 4.5, 0.49, 0.5),
   (4, 6.5, 0.49, 0.5),
   (6, 8.5, 0.49, 0.5),
   (7.5, 10, 0.49, 0.5)]

/-- Pure combinatorics: every `(x,y)` with `-10<x<10`, `0.49≤y<0.5` lies closed in some edge-strip cell. -/
theorem edgeStripCells_covers {x y : ℝ}
    (hx_lo : -10 < x) (hx_hi : x < 10)
    (hy_lo : 0.49 ≤ y) (hy_hi : y < 0.5) :
    ∃ c ∈ edgeStripCells,
      c.1 ≤ x ∧ x ≤ c.2.1 ∧ c.2.2.1 ≤ y ∧ y ≤ c.2.2.2 := by
  have hy_le : y ≤ 0.5 := le_of_lt hy_hi
  by_cases h1 : x < -7.5
  · exact ⟨(-10, -7.5, 0.49, 0.5), by simp [edgeStripCells],
      by show (-10 : ℝ) ≤ x; linarith,
      by show x ≤ (-7.5 : ℝ); exact le_of_lt h1,
      hy_lo, hy_le⟩
  · push_neg at h1
    by_cases h2 : x < -5.5
    · exact ⟨(-8, -5.5, 0.49, 0.5), by simp [edgeStripCells],
        by show (-8 : ℝ) ≤ x; linarith,
        by show x ≤ (-5.5 : ℝ); exact le_of_lt h2,
        hy_lo, hy_le⟩
    · push_neg at h2
      by_cases h3 : x < -3.5
      · exact ⟨(-6, -3.5, 0.49, 0.5), by simp [edgeStripCells],
          by show (-6 : ℝ) ≤ x; linarith,
          by show x ≤ (-3.5 : ℝ); exact le_of_lt h3,
          hy_lo, hy_le⟩
      · push_neg at h3
        by_cases h4 : x < -1.5
        · exact ⟨(-4, -1.5, 0.49, 0.5), by simp [edgeStripCells],
            by show (-4 : ℝ) ≤ x; linarith,
            by show x ≤ (-1.5 : ℝ); exact le_of_lt h4,
            hy_lo, hy_le⟩
        · push_neg at h4
          by_cases h5 : x < 0.5
          · exact ⟨(-2, 0.5, 0.49, 0.5), by simp [edgeStripCells],
              by show (-2 : ℝ) ≤ x; linarith,
              by show x ≤ (0.5 : ℝ); exact le_of_lt h5,
              hy_lo, hy_le⟩
          · push_neg at h5
            by_cases h6 : x < 2.5
            · exact ⟨(0, 2.5, 0.49, 0.5), by simp [edgeStripCells],
                by show (0 : ℝ) ≤ x; linarith,
                by show x ≤ (2.5 : ℝ); exact le_of_lt h6,
                hy_lo, hy_le⟩
            · push_neg at h6
              by_cases h7 : x < 4.5
              · exact ⟨(2, 4.5, 0.49, 0.5), by simp [edgeStripCells],
                  by show (2 : ℝ) ≤ x; linarith,
                  by show x ≤ (4.5 : ℝ); exact le_of_lt h7,
                  hy_lo, hy_le⟩
              · push_neg at h7
                by_cases h8 : x < 6.5
                · exact ⟨(4, 6.5, 0.49, 0.5), by simp [edgeStripCells],
                    by show (4 : ℝ) ≤ x; linarith,
                    by show x ≤ (6.5 : ℝ); exact le_of_lt h8,
                    hy_lo, hy_le⟩
                · push_neg at h8
                  by_cases h9 : x < 8.5
                  · exact ⟨(6, 8.5, 0.49, 0.5), by simp [edgeStripCells],
                      by show (6 : ℝ) ≤ x; linarith,
                      by show x ≤ (8.5 : ℝ); exact le_of_lt h9,
                      hy_lo, hy_le⟩
                  · push_neg at h9
                    exact ⟨(7.5, 10, 0.49, 0.5), by simp [edgeStripCells],
                      by show (7.5 : ℝ) ≤ x; linarith,
                      by show x ≤ (10 : ℝ); exact le_of_lt hx_hi,
                      hy_lo, hy_le⟩

/-- The corner edge-strip cell `(-10,-7.5)` times `(0.49,0.5)` (outer tier, new re-value). -/
def EdgeS00 : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS00_x0 : EdgeS00.x0 = -10 := rfl
theorem EdgeS00_x1 : EdgeS00.x1 = -7.5 := rfl
theorem EdgeS00_y0 : EdgeS00.y0 = 0.49 := rfl
theorem EdgeS00_y1 : EdgeS00.y1 = 0.5 := rfl

theorem EdgeS00_dx_eq : EdgeS00.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS00_x0, EdgeS00_x1]; norm_num

theorem EdgeS00_dy_eq : EdgeS00.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS00_y0, EdgeS00_y1]; norm_num

theorem EdgeS00_radius_eq :
    EdgeS00.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS00_dx_eq, EdgeS00_dy_eq]

/-- Radius bound for edge-strip geometry `(dx,dy)=(1.25,0.005)`: still `<1.26`. -/
theorem edgeStrip_radius_bound :
    Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) < 1.26 := by
  have hlt : (1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2 < (1.26 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

theorem EdgeS00_radius_lt : EdgeS00.radius < 1.26 := by
  rw [EdgeS00_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS00_strip_lo : -(1 / 2 : ℝ) < EdgeS00.y0 := by rw [EdgeS00_y0]; norm_num

/-- `EdgeS00` touches the strip boundary (`y1=0.5`), so inner strip fencing (`R.y1<1/2`) does NOT apply; outer-bound tool needed. -/
theorem EdgeS00_touches_top : ¬ EdgeS00.y1 < (1 / 2 : ℝ) := by rw [EdgeS00_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS00` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[-10,-7.5]`). -/
theorem edgeS00_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : -10 ≤ s.im) (him_hi : s.im ≤ -7.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (exponent nonpositive, base `pi≥1`). -/
theorem edgeS00_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 := by
  unfold DerivCauchyBridge.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  have hle : (-(s / 2)).re ≤ 0 := by
    rw [hneg, h2]
    linarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact Real.rpow_le_one_of_one_le_of_nonpos hpi1 hle

/-- `EdgeS00.center = -8.75 + 0.495*I`. -/
theorem EdgeS00_center_eq :
    EdgeS00.center =
      (((-8.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS00_x0, EdgeS00_x1, EdgeS00_y0, EdgeS00_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS00_x0, EdgeS00_x1, EdgeS00_y0, EdgeS00_y1]
    simp
    norm_num

/-- The `EdgeS00` `s`-plane center `s=1/2+I*z` at `z=EdgeS00.center`. -/
noncomputable def edgeS00_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS00.center

/-- `Re edgeS00_sCenter = 0.005` (`1/2-0.495`, the NEW re-value). -/
theorem edgeS00_sCenter_re : edgeS00_sCenter.re = 0.005 := by
  unfold edgeS00_sCenter
  rw [EdgeS00_center_eq]
  simp
  norm_num

/-- `Im edgeS00_sCenter = -8.75`. -/
theorem edgeS00_sCenter_im : edgeS00_sCenter.im = -8.75 := by
  unfold edgeS00_sCenter
  rw [EdgeS00_center_eq]
  simp

/-- Real convexity feeder: `Real.Gamma 1.0025 ≤ 1` (`1.0025=0.9975*1+0.0025*2`). -/
theorem edgeS00_realGamma_10025_le_one : Real.Gamma 1.0025 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.9975 := by norm_num
  have hb : (0 : ℝ) ≤ 0.0025 := by norm_num
  have hab : (0.9975 : ℝ) + 0.0025 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.9975 : ℝ) * 1 + 0.0025 * 2 = 1.0025 := by norm_num
  have hrhs : (0.9975 : ℝ) * 1 + 0.0025 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 0.0025 ≤ 400` (`Gamma(1.0025)/0.0025`, new re-value one-over-x route). -/
theorem edgeS00_realGamma_00025_le : Real.Gamma 0.0025 ≤ 400 := by
  have hx_pos : (0 : ℝ) < 0.0025 := by norm_num
  have hne : (0.0025 : ℝ) ≠ 0 := ne_of_gt hx_pos
  have hadd : Real.Gamma (0.0025 + 1) = 0.0025 * Real.Gamma 0.0025 :=
    Real.Gamma_add_one hne
  have heq : (0.0025 : ℝ) + 1 = 1.0025 := by norm_num
  rw [heq] at hadd
  have h1 : Real.Gamma 1.0025 ≤ 1 := edgeS00_realGamma_10025_le_one
  rw [hadd] at h1
  have hfin : Real.Gamma 0.0025 ≤ 1 / 0.0025 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h1
  have hfrac : (1 : ℝ) / 0.0025 ≤ 400 := by norm_num
  exact le_trans hfin hfrac

/-- Hypothesis-free Gamma upper `400` at the `EdgeS00` center (`s/2` has `Re=0.0025`). -/
theorem edgeS00_gamma_upper_center :
    ‖Complex.Gamma (edgeS00_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS00_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS00_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS00_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS00_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- Left cutoff thin rect centered at `Re=-10`, strictly inside strip (`y` in `(-0.49,0.49)`). -/
def CutL10 : CellProofEngine.Rect2D :=
  ⟨-10.25, -9.75, -0.49, 0.49, by norm_num, by norm_num⟩

/-- Right cutoff thin rect centered at `Re=10`, strictly inside strip. -/
def CutR10 : CellProofEngine.Rect2D :=
  ⟨9.75, 10.25, -0.49, 0.49, by norm_num, by norm_num⟩

theorem CutL10_x0 : CutL10.x0 = -10.25 := rfl
theorem CutL10_x1 : CutL10.x1 = -9.75 := rfl
theorem CutL10_y0 : CutL10.y0 = -0.49 := rfl
theorem CutL10_y1 : CutL10.y1 = 0.49 := rfl

theorem CutR10_x0 : CutR10.x0 = 9.75 := rfl
theorem CutR10_x1 : CutR10.x1 = 10.25 := rfl
theorem CutR10_y0 : CutR10.y0 = -0.49 := rfl
theorem CutR10_y1 : CutR10.y1 = 0.49 := rfl

theorem CutL10_dx_eq : CutL10.dx = 0.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [CutL10_x0, CutL10_x1]; norm_num

theorem CutL10_dy_eq : CutL10.dy = 0.49 := by
  unfold CellProofEngine.Rect2D.dy
  rw [CutL10_y0, CutL10_y1]; norm_num

theorem CutR10_dx_eq : CutR10.dx = 0.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [CutR10_x0, CutR10_x1]; norm_num

theorem CutR10_dy_eq : CutR10.dy = 0.49 := by
  unfold CellProofEngine.Rect2D.dy
  rw [CutR10_y0, CutR10_y1]; norm_num

theorem CutL10_radius_eq :
    CutL10.radius = Real.sqrt ((0.25 : ℝ) ^ 2 + (0.49 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [CutL10_dx_eq, CutL10_dy_eq]

theorem CutR10_radius_eq :
    CutR10.radius = Real.sqrt ((0.25 : ℝ) ^ 2 + (0.49 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [CutR10_dx_eq, CutR10_dy_eq]

/-- Radius bound for cutoff geometry `(dx,dy)=(0.25,0.49)`: `<0.56`. -/
theorem cutoff_radius_bound :
    Real.sqrt ((0.25 : ℝ) ^ 2 + (0.49 : ℝ) ^ 2) < 0.56 := by
  have hlt : (0.25 : ℝ) ^ 2 + (0.49 : ℝ) ^ 2 < (0.56 : ℝ) ^ 2 := by norm_num
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (by norm_num)] at h

theorem CutL10_radius_lt : CutL10.radius < 0.56 := by
  rw [CutL10_radius_eq]; exact cutoff_radius_bound

theorem CutR10_radius_lt : CutR10.radius < 0.56 := by
  rw [CutR10_radius_eq]; exact cutoff_radius_bound

theorem CutL10_strip_lo : -(1 / 2 : ℝ) < CutL10.y0 := by rw [CutL10_y0]; norm_num
theorem CutL10_strip_hi : CutL10.y1 < (1 / 2 : ℝ) := by rw [CutL10_y1]; norm_num
theorem CutR10_strip_lo : -(1 / 2 : ℝ) < CutR10.y0 := by rw [CutR10_y0]; norm_num
theorem CutR10_strip_hi : CutR10.y1 < (1 / 2 : ℝ) := by rw [CutR10_y1]; norm_num

/-- Right line `Re=10` with `|Im|≤0.49` lies closed in `CutR10`. -/
theorem CutR10_mem_of_line {z : ℂ}
    (hx : z.re = 10) (hy_lo : -0.49 ≤ z.im) (hy_hi : z.im ≤ 0.49) :
    CutR10.mem z := by
  have hx0 : CutR10.x0 ≤ z.re := by rw [CutR10_x0, hx]; norm_num
  have hx1 : z.re ≤ CutR10.x1 := by rw [CutR10_x1, hx]; norm_num
  have hy0 : CutR10.y0 ≤ z.im := by rw [CutR10_y0]; exact hy_lo
  have hy1 : z.im ≤ CutR10.y1 := by rw [CutR10_y1]; exact hy_hi
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Left line `Re=-10` with `|Im|≤0.49` lies closed in `CutL10`. -/
theorem CutL10_mem_of_line {z : ℂ}
    (hx : z.re = -10) (hy_lo : -0.49 ≤ z.im) (hy_hi : z.im ≤ 0.49) :
    CutL10.mem z := by
  have hx0 : CutL10.x0 ≤ z.re := by rw [CutL10_x0, hx]; norm_num
  have hx1 : z.re ≤ CutL10.x1 := by rw [CutL10_x1, hx]; norm_num
  have hy0 : CutL10.y0 ≤ z.im := by rw [CutL10_y0]; exact hy_lo
  have hy1 : z.im ≤ CutL10.y1 := by rw [CutL10_y1]; exact hy_hi
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Pure combinatorics: every cutoff point `Re=±10`, `|Im|<1/2` is either in its thin rect (`|Im|≤0.49`) or in edge-strip range (`0.49≤|Im|`). -/
theorem cutoffLines_either {z : ℂ}
    (heq : z.re = 10 ∨ z.re = -10)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < 1 / 2) :
    (CutL10.mem z ∨ CutR10.mem z) ∨ (0.49 ≤ z.im ∨ z.im ≤ -0.49) := by
  rcases heq with hx | hx
  · by_cases h1 : -0.49 ≤ z.im
    · by_cases h2 : z.im ≤ 0.49
      · left
        right
        exact CutR10_mem_of_line hx h1 h2
      · right
        exact Or.inl (le_of_lt (lt_of_not_ge h2))
    · right
      exact Or.inr (le_of_lt (lt_of_not_ge h1))
  · by_cases h1 : -0.49 ≤ z.im
    · by_cases h2 : z.im ≤ 0.49
      · left
        left
        exact CutL10_mem_of_line hx h1 h2
      · right
        exact Or.inl (le_of_lt (lt_of_not_ge h2))
    · right
      exact Or.inr (le_of_lt (lt_of_not_ge h1))

#print axioms edgeStripCells_covers
#print axioms EdgeS00_radius_lt
#print axioms EdgeS00_touches_top
#print axioms edgeS00_poly_upper_rect
#print axioms edgeS00_pi_upper_rect
#print axioms edgeS00_gamma_upper_center
#print axioms CutL10_radius_lt
#print axioms CutR10_radius_lt
#print axioms cutoffLines_either

end CentralCoverAssembly

/-! ## Edge-strip + cutoff residual inventory (honest, no `sorry`)

Closed cells this commit (unconditional end-to-end, no hypotheses): NONE (0).
What IS closed unconditionally (hypothesis-free, green above):
* `edgeStripCells_covers` (pure `linarith` plus `simp` membership, 10 cells `y=(0.49,0.5)` tiling `(-10,10)` times `[0.49,0.5)` closed);
* `EdgeS00` geometry (`dx=1.25`, `dy=0.005`, `radius<1.26` reusing `sample_cell_radius_bound` shape with `0.005`);
* `EdgeS00_touches_top` (`y1=0.5`, so `R.y1<1/2` FAILS: inner strip fencing `xi_rect_lower_bound_of_center_bound_strip` inapplicable, outer-bound `upper_boundary_nonvanishing_from_outer_bound` needed);
* `edgeS00_poly_upper_rect` (`≤56`), `edgeS00_pi_upper_rect` (`≤1`), `edgeS00_gamma_upper_center` (`≤400` at NEW re-value `s.re=0.005` via `Real.convexOn_Gamma` base `Gamma 1.0025≤1` plus `Gamma_add_one` one-over-x, reusing `DerivCauchyBridge.norm_Gamma_le_realGamma`);
* `CutL10` and `CutR10` geometry (`dx=0.25`, `dy=0.49`, `radius<0.56`, strictly inside strip) plus `cutoffLines_either` (thin rects cover `|Im|≤0.49`, strips cover `0.49≤|Im|`).

Residual (each names exact missing lemma, same wall as 40 central cells):
1. Edge strips `y` in `[0.49,1/2)` (10 cells `edgeStripCells`, upper plus `conj_of` lower halves): per cell CENTER lower `ε+M*radius≤‖xiShifted center‖` needs `Azeta` lower `‖zeta s_center‖≥Azeta` at NEW re-value `s.re` in `(0,0.01]` (`s=0.005-8.75*I` for `EdgeS00`, true `|zeta|=O(1)`, needs Dirichlet-eta plus remainder `zetaCell_even_remainder_le` instantiation at `σ=0.005` where `r(M)=C*M^{-σ}/σ` decays too slowly for feasible `M`, plus smarter-bound wall); per cell DERIV upper `‖deriv xiShifted‖≤M` needs tight `‖zeta‖≤10` on disc `s`-rect (true `O(1)`, needs FE plus Stirling plus convexity, crude eta M-test gives `≤1012` hence `M=6800640` too large for `ε+M*1.26` fencing); top-touching `y1=0.5` additionally needs `upper_boundary_nonvanishing_from_outer_bound` outer value `ε_top≤‖xiShiftedEntire (x+0.5*I)‖` plus vertical deriv bound (both need same `zeta` upper).
2. Cutoff lines `Re=±10` (2 thin rects `CutL10`, `CutR10`): per rect CENTER plus DERIV same two `zeta` enclosures on vertical `s`-rects (`Re` in `[0.01,0.99]`, `Im=±10`, true `O(1)`), then `inner_nonvanishing_of_fenced_grid_fine` H-leaf plus `cutoffLines_either` assembly; lines with `0.49≤|Im|<1/2` additionally need strip item 1.
-/
/-! ## Edge-strip upper columns S01-S09 (EdgeS00 template replication, 0-sorry)

Grep-first record (verified 2026-09-03, repo + Mathlib, via grep tool):
* `edgeStripCells|EdgeS00|edgeS00|CutL10|CutR10` -> central_cover_assembly EdgeS00 template + CutL10/R10 + guide 18b.10; no EdgeS01-09 defs (no clash).
* `conj_of|lower mirror|LowerHalf` -> sorry-free `XiLocalZeroFreeRect.conj_of` / `XiLocalLowerBoundRect.conj_of` + 41 lower-half `RXX_conjZF/LB` defs (each needs packaged upper R plus `0 < y0`, `y1 < 1/2`); strips have no packaged R (zeta wall) so conj_of inapplicable yet, no new transfer invented.
* `norm_Gamma_le_realGamma|realGamma_le_40_of_mem|polyOf|piOf` -> `DerivCauchyBridge` helpers + `interval_arith` 40-center machine (READ-ONLY, NOT imported); this file mirrors minimal helpers with distinct `edgeS00_*` names, reused below.
* `XiCentralEdgeStrips10` -> `riemann_hypothesis` capstone def + assembly + guide 18b.10; hypothesis Props only, no proofs.
* `upper_boundary_nonvanishing_from_outer_bound` -> `rh_certificate_infra` Theorem 3 (generic `f`) + inventory mentions; no strip instantiation (outer-bound needed since `y1=0.5`).
* `fineGridX` -> this file `fineGridX` 10 cols width `2.5` + `gridFine` 40 cells + covers; `edgeStripCells` reuses same 10 `x`-intervals with `y=(0.49,0.5)`.

Reuse rationale (read EdgeS00 lines, not assumed):
* All 10 upper strips share `y=(0.49,0.5)` so `dx=1.25`, `dy=0.005`, `radius=sqrt(1.25^2+0.005^2)<1.26` via shared `edgeStrip_radius_bound`.
* All share `y`-center `0.495` so `sCenter.re=0.005`, `s/2.re=0.0025`: Gamma `400` chain reuses center-independent `edgeS00_realGamma_00025_le` (plus `edgeS00_realGamma_10025_le_one` feeder) + `DerivCauchyBridge.norm_Gamma_le_realGamma` directly.
* Poly `56` body reuses `10.01*11/2` numeral-for-numeral; only `him_lo/hi` change per column (`|s.im|<=10` still follows by `linarith` since all `x`-intervals lie in `[-10,10]`).
* Pi `1` lemma `edgeS00_pi_upper_rect` is already generic (`0<=s.re` only): per-column wrappers call it directly.
* Center `x`-centers per `edgeStripCells`: `-6.75,-4.75,-2.75,-0.75,1.25,3.25,5.25,7.25,8.75` (`y`-center `0.495` shared).
* Lower-half mirrors via `conj_of` REQUIRE packaged upper rects plus `0<y0`, `y1<1/2`; strips have neither (no H-leaf zeta wall; plus `y1=0.5` fails `y1<1/2`): no transfer invented, lower mirrors stay residual.

Correctness: tail Float certs do not cover strips; global `xiShifted_differentiable` false-as-stated, strip entireness only; no `sorry`/`admit`/`axiom`; fully-verified factors only, zero cells claimed closed.
-/

namespace CentralCoverAssembly

open CellProofEngine

/-- The edge-strip cell `(-8,-5.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS01 : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS01_x0 : EdgeS01.x0 = -8 := rfl
theorem EdgeS01_x1 : EdgeS01.x1 = -5.5 := rfl
theorem EdgeS01_y0 : EdgeS01.y0 = 0.49 := rfl
theorem EdgeS01_y1 : EdgeS01.y1 = 0.5 := rfl

theorem EdgeS01_dx_eq : EdgeS01.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS01_x0, EdgeS01_x1]; norm_num

theorem EdgeS01_dy_eq : EdgeS01.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS01_y0, EdgeS01_y1]; norm_num

theorem EdgeS01_radius_eq :
    EdgeS01.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS01_dx_eq, EdgeS01_dy_eq]

theorem EdgeS01_radius_lt : EdgeS01.radius < 1.26 := by
  rw [EdgeS01_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS01_strip_lo : -(1 / 2 : ℝ) < EdgeS01.y0 := by rw [EdgeS01_y0]; norm_num

/-- `EdgeS01` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS01_touches_top : ¬ EdgeS01.y1 < (1 / 2 : ℝ) := by rw [EdgeS01_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS01` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[-8,-5.5]`; numerals mirror EdgeS00). -/
theorem edgeS01_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : -8 ≤ s.im) (him_hi : s.im ≤ -5.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS01_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS01.center = -6.75 + 0.495*I`. -/
theorem EdgeS01_center_eq :
    EdgeS01.center =
      (((-6.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS01_x0, EdgeS01_x1, EdgeS01_y0, EdgeS01_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS01_x0, EdgeS01_x1, EdgeS01_y0, EdgeS01_y1]
    simp
    norm_num

/-- The `EdgeS01` `s`-plane center `s=1/2+I*z` at `z=EdgeS01.center`. -/
noncomputable def edgeS01_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS01.center

/-- `Re edgeS01_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS01_sCenter_re : edgeS01_sCenter.re = 0.005 := by
  unfold edgeS01_sCenter
  rw [EdgeS01_center_eq]
  simp
  norm_num

/-- `Im edgeS01_sCenter = -6.75`. -/
theorem edgeS01_sCenter_im : edgeS01_sCenter.im = -6.75 := by
  unfold edgeS01_sCenter
  rw [EdgeS01_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS01` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS01_gamma_upper_center :
    ‖Complex.Gamma (edgeS01_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS01_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS01_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS01_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS01_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(-6,-3.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS02 : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS02_x0 : EdgeS02.x0 = -6 := rfl
theorem EdgeS02_x1 : EdgeS02.x1 = -3.5 := rfl
theorem EdgeS02_y0 : EdgeS02.y0 = 0.49 := rfl
theorem EdgeS02_y1 : EdgeS02.y1 = 0.5 := rfl

theorem EdgeS02_dx_eq : EdgeS02.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS02_x0, EdgeS02_x1]; norm_num

theorem EdgeS02_dy_eq : EdgeS02.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS02_y0, EdgeS02_y1]; norm_num

theorem EdgeS02_radius_eq :
    EdgeS02.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS02_dx_eq, EdgeS02_dy_eq]

theorem EdgeS02_radius_lt : EdgeS02.radius < 1.26 := by
  rw [EdgeS02_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS02_strip_lo : -(1 / 2 : ℝ) < EdgeS02.y0 := by rw [EdgeS02_y0]; norm_num

/-- `EdgeS02` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS02_touches_top : ¬ EdgeS02.y1 < (1 / 2 : ℝ) := by rw [EdgeS02_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS02` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[-6,-3.5]`; numerals mirror EdgeS00). -/
theorem edgeS02_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : -6 ≤ s.im) (him_hi : s.im ≤ -3.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS02_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS02.center = -4.75 + 0.495*I`. -/
theorem EdgeS02_center_eq :
    EdgeS02.center =
      (((-4.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS02_x0, EdgeS02_x1, EdgeS02_y0, EdgeS02_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS02_x0, EdgeS02_x1, EdgeS02_y0, EdgeS02_y1]
    simp
    norm_num

/-- The `EdgeS02` `s`-plane center `s=1/2+I*z` at `z=EdgeS02.center`. -/
noncomputable def edgeS02_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS02.center

/-- `Re edgeS02_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS02_sCenter_re : edgeS02_sCenter.re = 0.005 := by
  unfold edgeS02_sCenter
  rw [EdgeS02_center_eq]
  simp
  norm_num

/-- `Im edgeS02_sCenter = -4.75`. -/
theorem edgeS02_sCenter_im : edgeS02_sCenter.im = -4.75 := by
  unfold edgeS02_sCenter
  rw [EdgeS02_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS02` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS02_gamma_upper_center :
    ‖Complex.Gamma (edgeS02_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS02_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS02_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS02_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS02_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(-4,-1.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS03 : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS03_x0 : EdgeS03.x0 = -4 := rfl
theorem EdgeS03_x1 : EdgeS03.x1 = -1.5 := rfl
theorem EdgeS03_y0 : EdgeS03.y0 = 0.49 := rfl
theorem EdgeS03_y1 : EdgeS03.y1 = 0.5 := rfl

theorem EdgeS03_dx_eq : EdgeS03.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS03_x0, EdgeS03_x1]; norm_num

theorem EdgeS03_dy_eq : EdgeS03.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS03_y0, EdgeS03_y1]; norm_num

theorem EdgeS03_radius_eq :
    EdgeS03.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS03_dx_eq, EdgeS03_dy_eq]

theorem EdgeS03_radius_lt : EdgeS03.radius < 1.26 := by
  rw [EdgeS03_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS03_strip_lo : -(1 / 2 : ℝ) < EdgeS03.y0 := by rw [EdgeS03_y0]; norm_num

/-- `EdgeS03` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS03_touches_top : ¬ EdgeS03.y1 < (1 / 2 : ℝ) := by rw [EdgeS03_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS03` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[-4,-1.5]`; numerals mirror EdgeS00). -/
theorem edgeS03_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : -4 ≤ s.im) (him_hi : s.im ≤ -1.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS03_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS03.center = -2.75 + 0.495*I`. -/
theorem EdgeS03_center_eq :
    EdgeS03.center =
      (((-2.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS03_x0, EdgeS03_x1, EdgeS03_y0, EdgeS03_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS03_x0, EdgeS03_x1, EdgeS03_y0, EdgeS03_y1]
    simp
    norm_num

/-- The `EdgeS03` `s`-plane center `s=1/2+I*z` at `z=EdgeS03.center`. -/
noncomputable def edgeS03_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS03.center

/-- `Re edgeS03_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS03_sCenter_re : edgeS03_sCenter.re = 0.005 := by
  unfold edgeS03_sCenter
  rw [EdgeS03_center_eq]
  simp
  norm_num

/-- `Im edgeS03_sCenter = -2.75`. -/
theorem edgeS03_sCenter_im : edgeS03_sCenter.im = -2.75 := by
  unfold edgeS03_sCenter
  rw [EdgeS03_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS03` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS03_gamma_upper_center :
    ‖Complex.Gamma (edgeS03_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS03_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS03_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS03_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS03_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(-2,0.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS04 : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS04_x0 : EdgeS04.x0 = -2 := rfl
theorem EdgeS04_x1 : EdgeS04.x1 = 0.5 := rfl
theorem EdgeS04_y0 : EdgeS04.y0 = 0.49 := rfl
theorem EdgeS04_y1 : EdgeS04.y1 = 0.5 := rfl

theorem EdgeS04_dx_eq : EdgeS04.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS04_x0, EdgeS04_x1]; norm_num

theorem EdgeS04_dy_eq : EdgeS04.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS04_y0, EdgeS04_y1]; norm_num

theorem EdgeS04_radius_eq :
    EdgeS04.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS04_dx_eq, EdgeS04_dy_eq]

theorem EdgeS04_radius_lt : EdgeS04.radius < 1.26 := by
  rw [EdgeS04_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS04_strip_lo : -(1 / 2 : ℝ) < EdgeS04.y0 := by rw [EdgeS04_y0]; norm_num

/-- `EdgeS04` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS04_touches_top : ¬ EdgeS04.y1 < (1 / 2 : ℝ) := by rw [EdgeS04_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS04` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[-2,0.5]`; numerals mirror EdgeS00). -/
theorem edgeS04_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : -2 ≤ s.im) (him_hi : s.im ≤ 0.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS04_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS04.center = -0.75 + 0.495*I`. -/
theorem EdgeS04_center_eq :
    EdgeS04.center =
      (((-0.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS04_x0, EdgeS04_x1, EdgeS04_y0, EdgeS04_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS04_x0, EdgeS04_x1, EdgeS04_y0, EdgeS04_y1]
    simp
    norm_num

/-- The `EdgeS04` `s`-plane center `s=1/2+I*z` at `z=EdgeS04.center`. -/
noncomputable def edgeS04_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS04.center

/-- `Re edgeS04_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS04_sCenter_re : edgeS04_sCenter.re = 0.005 := by
  unfold edgeS04_sCenter
  rw [EdgeS04_center_eq]
  simp
  norm_num

/-- `Im edgeS04_sCenter = -0.75`. -/
theorem edgeS04_sCenter_im : edgeS04_sCenter.im = -0.75 := by
  unfold edgeS04_sCenter
  rw [EdgeS04_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS04` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS04_gamma_upper_center :
    ‖Complex.Gamma (edgeS04_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS04_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS04_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS04_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS04_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(0,2.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS05 : CellProofEngine.Rect2D :=
  ⟨0, 2.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS05_x0 : EdgeS05.x0 = 0 := rfl
theorem EdgeS05_x1 : EdgeS05.x1 = 2.5 := rfl
theorem EdgeS05_y0 : EdgeS05.y0 = 0.49 := rfl
theorem EdgeS05_y1 : EdgeS05.y1 = 0.5 := rfl

theorem EdgeS05_dx_eq : EdgeS05.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS05_x0, EdgeS05_x1]; norm_num

theorem EdgeS05_dy_eq : EdgeS05.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS05_y0, EdgeS05_y1]; norm_num

theorem EdgeS05_radius_eq :
    EdgeS05.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS05_dx_eq, EdgeS05_dy_eq]

theorem EdgeS05_radius_lt : EdgeS05.radius < 1.26 := by
  rw [EdgeS05_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS05_strip_lo : -(1 / 2 : ℝ) < EdgeS05.y0 := by rw [EdgeS05_y0]; norm_num

/-- `EdgeS05` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS05_touches_top : ¬ EdgeS05.y1 < (1 / 2 : ℝ) := by rw [EdgeS05_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS05` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[0,2.5]`; numerals mirror EdgeS00). -/
theorem edgeS05_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : 0 ≤ s.im) (him_hi : s.im ≤ 2.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS05_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS05.center = 1.25 + 0.495*I`. -/
theorem EdgeS05_center_eq :
    EdgeS05.center =
      (((1.25 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS05_x0, EdgeS05_x1, EdgeS05_y0, EdgeS05_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS05_x0, EdgeS05_x1, EdgeS05_y0, EdgeS05_y1]
    simp
    norm_num

/-- The `EdgeS05` `s`-plane center `s=1/2+I*z` at `z=EdgeS05.center`. -/
noncomputable def edgeS05_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS05.center

/-- `Re edgeS05_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS05_sCenter_re : edgeS05_sCenter.re = 0.005 := by
  unfold edgeS05_sCenter
  rw [EdgeS05_center_eq]
  simp
  norm_num

/-- `Im edgeS05_sCenter = 1.25`. -/
theorem edgeS05_sCenter_im : edgeS05_sCenter.im = 1.25 := by
  unfold edgeS05_sCenter
  rw [EdgeS05_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS05` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS05_gamma_upper_center :
    ‖Complex.Gamma (edgeS05_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS05_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS05_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS05_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS05_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(2,4.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS06 : CellProofEngine.Rect2D :=
  ⟨2, 4.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS06_x0 : EdgeS06.x0 = 2 := rfl
theorem EdgeS06_x1 : EdgeS06.x1 = 4.5 := rfl
theorem EdgeS06_y0 : EdgeS06.y0 = 0.49 := rfl
theorem EdgeS06_y1 : EdgeS06.y1 = 0.5 := rfl

theorem EdgeS06_dx_eq : EdgeS06.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS06_x0, EdgeS06_x1]; norm_num

theorem EdgeS06_dy_eq : EdgeS06.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS06_y0, EdgeS06_y1]; norm_num

theorem EdgeS06_radius_eq :
    EdgeS06.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS06_dx_eq, EdgeS06_dy_eq]

theorem EdgeS06_radius_lt : EdgeS06.radius < 1.26 := by
  rw [EdgeS06_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS06_strip_lo : -(1 / 2 : ℝ) < EdgeS06.y0 := by rw [EdgeS06_y0]; norm_num

/-- `EdgeS06` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS06_touches_top : ¬ EdgeS06.y1 < (1 / 2 : ℝ) := by rw [EdgeS06_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS06` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[2,4.5]`; numerals mirror EdgeS00). -/
theorem edgeS06_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : 2 ≤ s.im) (him_hi : s.im ≤ 4.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS06_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS06.center = 3.25 + 0.495*I`. -/
theorem EdgeS06_center_eq :
    EdgeS06.center =
      (((3.25 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS06_x0, EdgeS06_x1, EdgeS06_y0, EdgeS06_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS06_x0, EdgeS06_x1, EdgeS06_y0, EdgeS06_y1]
    simp
    norm_num

/-- The `EdgeS06` `s`-plane center `s=1/2+I*z` at `z=EdgeS06.center`. -/
noncomputable def edgeS06_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS06.center

/-- `Re edgeS06_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS06_sCenter_re : edgeS06_sCenter.re = 0.005 := by
  unfold edgeS06_sCenter
  rw [EdgeS06_center_eq]
  simp
  norm_num

/-- `Im edgeS06_sCenter = 3.25`. -/
theorem edgeS06_sCenter_im : edgeS06_sCenter.im = 3.25 := by
  unfold edgeS06_sCenter
  rw [EdgeS06_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS06` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS06_gamma_upper_center :
    ‖Complex.Gamma (edgeS06_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS06_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS06_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS06_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS06_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(4,6.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS07 : CellProofEngine.Rect2D :=
  ⟨4, 6.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS07_x0 : EdgeS07.x0 = 4 := rfl
theorem EdgeS07_x1 : EdgeS07.x1 = 6.5 := rfl
theorem EdgeS07_y0 : EdgeS07.y0 = 0.49 := rfl
theorem EdgeS07_y1 : EdgeS07.y1 = 0.5 := rfl

theorem EdgeS07_dx_eq : EdgeS07.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS07_x0, EdgeS07_x1]; norm_num

theorem EdgeS07_dy_eq : EdgeS07.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS07_y0, EdgeS07_y1]; norm_num

theorem EdgeS07_radius_eq :
    EdgeS07.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS07_dx_eq, EdgeS07_dy_eq]

theorem EdgeS07_radius_lt : EdgeS07.radius < 1.26 := by
  rw [EdgeS07_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS07_strip_lo : -(1 / 2 : ℝ) < EdgeS07.y0 := by rw [EdgeS07_y0]; norm_num

/-- `EdgeS07` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS07_touches_top : ¬ EdgeS07.y1 < (1 / 2 : ℝ) := by rw [EdgeS07_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS07` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[4,6.5]`; numerals mirror EdgeS00). -/
theorem edgeS07_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : 4 ≤ s.im) (him_hi : s.im ≤ 6.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS07_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS07.center = 5.25 + 0.495*I`. -/
theorem EdgeS07_center_eq :
    EdgeS07.center =
      (((5.25 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS07_x0, EdgeS07_x1, EdgeS07_y0, EdgeS07_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS07_x0, EdgeS07_x1, EdgeS07_y0, EdgeS07_y1]
    simp
    norm_num

/-- The `EdgeS07` `s`-plane center `s=1/2+I*z` at `z=EdgeS07.center`. -/
noncomputable def edgeS07_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS07.center

/-- `Re edgeS07_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS07_sCenter_re : edgeS07_sCenter.re = 0.005 := by
  unfold edgeS07_sCenter
  rw [EdgeS07_center_eq]
  simp
  norm_num

/-- `Im edgeS07_sCenter = 5.25`. -/
theorem edgeS07_sCenter_im : edgeS07_sCenter.im = 5.25 := by
  unfold edgeS07_sCenter
  rw [EdgeS07_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS07` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS07_gamma_upper_center :
    ‖Complex.Gamma (edgeS07_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS07_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS07_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS07_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS07_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(6,8.5)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS08 : CellProofEngine.Rect2D :=
  ⟨6, 8.5, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS08_x0 : EdgeS08.x0 = 6 := rfl
theorem EdgeS08_x1 : EdgeS08.x1 = 8.5 := rfl
theorem EdgeS08_y0 : EdgeS08.y0 = 0.49 := rfl
theorem EdgeS08_y1 : EdgeS08.y1 = 0.5 := rfl

theorem EdgeS08_dx_eq : EdgeS08.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS08_x0, EdgeS08_x1]; norm_num

theorem EdgeS08_dy_eq : EdgeS08.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS08_y0, EdgeS08_y1]; norm_num

theorem EdgeS08_radius_eq :
    EdgeS08.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS08_dx_eq, EdgeS08_dy_eq]

theorem EdgeS08_radius_lt : EdgeS08.radius < 1.26 := by
  rw [EdgeS08_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS08_strip_lo : -(1 / 2 : ℝ) < EdgeS08.y0 := by rw [EdgeS08_y0]; norm_num

/-- `EdgeS08` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS08_touches_top : ¬ EdgeS08.y1 < (1 / 2 : ℝ) := by rw [EdgeS08_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS08` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[6,8.5]`; numerals mirror EdgeS00). -/
theorem edgeS08_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : 6 ≤ s.im) (him_hi : s.im ≤ 8.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS08_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS08.center = 7.25 + 0.495*I`. -/
theorem EdgeS08_center_eq :
    EdgeS08.center =
      (((7.25 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS08_x0, EdgeS08_x1, EdgeS08_y0, EdgeS08_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS08_x0, EdgeS08_x1, EdgeS08_y0, EdgeS08_y1]
    simp
    norm_num

/-- The `EdgeS08` `s`-plane center `s=1/2+I*z` at `z=EdgeS08.center`. -/
noncomputable def edgeS08_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS08.center

/-- `Re edgeS08_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS08_sCenter_re : edgeS08_sCenter.re = 0.005 := by
  unfold edgeS08_sCenter
  rw [EdgeS08_center_eq]
  simp
  norm_num

/-- `Im edgeS08_sCenter = 7.25`. -/
theorem edgeS08_sCenter_im : edgeS08_sCenter.im = 7.25 := by
  unfold edgeS08_sCenter
  rw [EdgeS08_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS08` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS08_gamma_upper_center :
    ‖Complex.Gamma (edgeS08_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS08_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS08_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS08_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS08_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

/-- The edge-strip cell `(7.5,10)` times `(0.49,0.5)` (EdgeS00 template replica). -/
def EdgeS09 : CellProofEngine.Rect2D :=
  ⟨7.5, 10, 0.49, 0.5, by norm_num, by norm_num⟩

theorem EdgeS09_x0 : EdgeS09.x0 = 7.5 := rfl
theorem EdgeS09_x1 : EdgeS09.x1 = 10 := rfl
theorem EdgeS09_y0 : EdgeS09.y0 = 0.49 := rfl
theorem EdgeS09_y1 : EdgeS09.y1 = 0.5 := rfl

theorem EdgeS09_dx_eq : EdgeS09.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS09_x0, EdgeS09_x1]; norm_num

theorem EdgeS09_dy_eq : EdgeS09.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS09_y0, EdgeS09_y1]; norm_num

theorem EdgeS09_radius_eq :
    EdgeS09.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS09_dx_eq, EdgeS09_dy_eq]

theorem EdgeS09_radius_lt : EdgeS09.radius < 1.26 := by
  rw [EdgeS09_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS09_strip_lo : -(1 / 2 : ℝ) < EdgeS09.y0 := by rw [EdgeS09_y0]; norm_num

/-- `EdgeS09` touches the strip boundary (`y1=0.5`), so inner strip fencing does NOT apply; outer-bound tool needed (same as EdgeS00). -/
theorem EdgeS09_touches_top : ¬ EdgeS09.y1 < (1 / 2 : ℝ) := by rw [EdgeS09_y1]; norm_num

/-- Hypothesis-free poly upper `56` on the `EdgeS09` rect `s`-rect (`Re` in `[0,0.01]`, `Im` in `[7.5,10]`; numerals mirror EdgeS00). -/
theorem edgeS09_poly_upper_rect {s : ℂ}
    (hre_lo : 0 ≤ s.re) (hre_hi : s.re ≤ 0.01)
    (him_lo : 7.5 ≤ s.im) (him_hi : s.im ≤ 10) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 0.01 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 1 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 10.01 * 11 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 10.01 * 11 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (10.01 : ℝ) * 11 / 2 ≤ 56 := by norm_num
  linarith

/-- Hypothesis-free pi upper `1` for `0≤s.re` (EdgeS00 generic reused; per-column wrapper). -/
theorem edgeS09_pi_upper_rect {s : ℂ} (hre_lo : 0 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect hre_lo

/-- `EdgeS09.center = 8.75 + 0.495*I`. -/
theorem EdgeS09_center_eq :
    EdgeS09.center =
      (((8.75 : ℝ))) + Complex.I * ((((0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS09_x0, EdgeS09_x1, EdgeS09_y0, EdgeS09_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS09_x0, EdgeS09_x1, EdgeS09_y0, EdgeS09_y1]
    simp
    norm_num

/-- The `EdgeS09` `s`-plane center `s=1/2+I*z` at `z=EdgeS09.center`. -/
noncomputable def edgeS09_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS09.center

/-- `Re edgeS09_sCenter = 0.005` (`1/2-0.495`, same re-value as EdgeS00). -/
theorem edgeS09_sCenter_re : edgeS09_sCenter.re = 0.005 := by
  unfold edgeS09_sCenter
  rw [EdgeS09_center_eq]
  simp
  norm_num

/-- `Im edgeS09_sCenter = 8.75`. -/
theorem edgeS09_sCenter_im : edgeS09_sCenter.im = 8.75 := by
  unfold edgeS09_sCenter
  rw [EdgeS09_center_eq]
  simp

/-- Hypothesis-free Gamma upper `400` at the `EdgeS09` center (`s/2` has `Re=0.0025`; reuses center-independent `edgeS00_realGamma_00025_le`). -/
theorem edgeS09_gamma_upper_center :
    ‖Complex.Gamma (edgeS09_sCenter / 2)‖ ≤ 400 := by
  have h2re : (edgeS09_sCenter / 2).re = 0.0025 := by
    rw [Complex.div_ofNat_re, edgeS09_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS09_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS09_sCenter / 2).re) ≤ 400 := by
    rw [h2re]
    exact edgeS00_realGamma_00025_le
  linarith

#print axioms EdgeS01_radius_lt
#print axioms edgeS01_poly_upper_rect
#print axioms edgeS01_pi_upper_rect
#print axioms edgeS01_gamma_upper_center
#print axioms EdgeS02_radius_lt
#print axioms edgeS02_poly_upper_rect
#print axioms edgeS02_pi_upper_rect
#print axioms edgeS02_gamma_upper_center
#print axioms EdgeS03_radius_lt
#print axioms edgeS03_poly_upper_rect
#print axioms edgeS03_pi_upper_rect
#print axioms edgeS03_gamma_upper_center
#print axioms EdgeS04_radius_lt
#print axioms edgeS04_poly_upper_rect
#print axioms edgeS04_pi_upper_rect
#print axioms edgeS04_gamma_upper_center
#print axioms EdgeS05_radius_lt
#print axioms edgeS05_poly_upper_rect
#print axioms edgeS05_pi_upper_rect
#print axioms edgeS05_gamma_upper_center
#print axioms EdgeS06_radius_lt
#print axioms edgeS06_poly_upper_rect
#print axioms edgeS06_pi_upper_rect
#print axioms edgeS06_gamma_upper_center
#print axioms EdgeS07_radius_lt
#print axioms edgeS07_poly_upper_rect
#print axioms edgeS07_pi_upper_rect
#print axioms edgeS07_gamma_upper_center
#print axioms EdgeS08_radius_lt
#print axioms edgeS08_poly_upper_rect
#print axioms edgeS08_pi_upper_rect
#print axioms edgeS08_gamma_upper_center
#print axioms EdgeS09_radius_lt
#print axioms edgeS09_poly_upper_rect
#print axioms edgeS09_pi_upper_rect
#print axioms edgeS09_gamma_upper_center

end CentralCoverAssembly

/-! ## Edge-strip S01-S09 packaged + residual inventory (honest, no `sorry`)

Packaged this append (unconditional end-to-end, hypothesis-free factors, green below):
* 9 upper strip columns `EdgeS01`-`EdgeS09` geometry each (`x0/x1/y0/y1` by `rfl`, `dx=1.25`, `dy=0.005`, `radius_eq` + `radius_lt<1.26` via shared `edgeStrip_radius_bound`, `strip_lo`, `touches_top` showing `y1=0.5` so inner fencing inapplicable).
* Per column center (`EdgeSXX_center_eq`: `x_c + 0.495*I` with `x_c` in `-6.75,-4.75,-2.75,-0.75,1.25,3.25,5.25,7.25,8.75`) + `sCenter` (`re=0.005` shared re-value, `im=x_c`).
* Per column `edgeSXX_poly_upper_rect` (`<=56`, same `10.01*11/2` numerals, only `Im` hypotheses per `edgeStripCells` interval) + `edgeSXX_pi_upper_rect` (`<=1`, wrapper over generic `edgeS00_pi_upper_rect`) + `edgeSXX_gamma_upper_center` (`<=400`, reuses center-independent `edgeS00_realGamma_00025_le` + `DerivCauchyBridge.norm_Gamma_le_realGamma`).
* Cell IDs packaged: `EdgeS01 (-8,-5.5)`, `EdgeS02 (-6,-3.5)`, `EdgeS03 (-4,-1.5)`, `EdgeS04 (-2,0.5)`, `EdgeS05 (0,2.5)`, `EdgeS06 (2,4.5)`, `EdgeS07 (4,6.5)`, `EdgeS08 (6,8.5)`, `EdgeS09 (7.5,10)`, all at `y=(0.49,0.5)`; with prior `EdgeS00 (-10,-7.5)` all 10 upper columns now have packaged factors.

Closed cells this append (unconditional end-to-end, no hypotheses): NONE (0). Full cell closure (H-leaf) stays blocked by the zeta wall, NOT claimed.

Residual (each names exact missing lemma):
1. Upper strips `EdgeS01`-`EdgeS09` (9 cells): per cell CENTER lower `eps+M*radius<=||xiShifted center||` needs `Azeta` lower `||zeta s_center||>=Azeta` at shared re-value `s.re=0.005` (`s=0.005+x_c*I`, true `|zeta|=O(1)`, needs Dirichlet-eta plus `zetaCell_even_remainder_le` at `sigma=0.005` where `r(M)=C*M^-sigma/sigma` decays too slowly plus smarter-bound wall); per cell DERIV upper `||deriv xiShifted||<=M` needs tight `||zeta||<=10` on disc `s`-rect (true `O(1)`, needs FE+Stirling+convexity; crude eta M-test gives `<=1012` hence `M=6800640` too large for `eps+M*1.26` fencing); top-touching `y1=0.5` additionally needs `upper_boundary_nonvanishing_from_outer_bound` outer value plus vertical deriv bound (same `zeta` upper). Same wall as `EdgeS00` + 40 central cells.
2. Lower-half mirrors (10 cells `y` in `(-0.5,-0.49)`): NO `conj_of` invented. Existing `XiLocalZeroFreeRect.conj_of` / `XiLocalLowerBoundRect.conj_of` pattern (read from 40-cell `RXX_conjZF/LB` defs) requires a packaged upper rect plus `0<y0`, `y1<1/2` side conditions; upper strips have no packaged rect (item 1 zeta wall) and `y1=0.5` fails `y1<1/2`, so transfer is blocked pending item 1. Lower `s`-centers would also carry a DIFFERENT re-value (`0.995`) needing a new Gamma chain, not the shared `0.005` reuse.
3. Cutoff lines `Re=+-10` (`CutL10`/`CutR10` already packaged geometry): per rect CENTER plus DERIV same two `zeta` enclosures on vertical `s`-rects (`Re` in `[0.01,0.99]`, `Im=+-10`), then H-leaf plus `cutoffLines_either` assembly; lines with `0.49<=|Im|<1/2` additionally need items 1-2.
-/
/-! ## Lower-half edge-strip mirrors: 0.995 Gamma chain + S00 end-to-end + y1 verdict

Grep-first record (verified 2026-09-03, via grep tool, this file only):
* `conj_of` -> `XiLocalZeroFreeRect.conj_of` (line 361, needs `0 < R.y0`, `R.y1 < 1/2`) + `XiLocalLowerBoundRect.conj_of` (line 394, same side conditions) + 41 `RXX_conjZF/LB` defs (R00-R40, each `by rw [RXX_y0/y1]; norm_num` since `y0 >= 0.01`, `y1 <= 0.49`).
* `EdgeS00_touches_top|EdgeS01_touches_top|...` -> all 10 uppers prove `¬ y1 < 1/2` (`y1 = 0.5` by `rfl`); direct `conj_of` side condition `R.y1 < 1/2` FAILS for full strips.
* `edgeS00_realGamma_10025_le_one|edgeS00_realGamma_00025_le` -> upper `0.005` chain (convexity `Gamma 1.0025 <= 1` + `Gamma_add_one` one-over-x `<= 400`); no `0.995|1.995|0.4975|1.4975|edgeLower|EdgeS.*Lower|Shrunk` defs exist (verified `rg`, zero hits except residual comments).
* `EdgeS00-S09|edgeS00-S09_sCenter|CutL10|CutR10` -> 10/10 upper columns packaged (geometry `dx=1.25/dy=0.005/radius<1.26`, `center = x_c + 0.495*I`, `sCenter.re=0.005`, poly `<=56`/pi `<=1`/Gamma `<=400`); `CutL10/R10` thin rects `y in (-0.49,0.49)` radius `<0.56`.
* ANTI-BALK: no lower mirrors packaged, residual matches file inventory lines 7918/6814 (blocked on `conj_of` side conditions + `0.995` chain); proceed with append-only.

Reuse rationale (read EdgeS00 lines 6503-6663 + one RXX_conj pair 5346-5358, not assumed):
* Upper `sCenter.re = 0.005` (`1/2-0.495`), `s/2.re = 0.0025`; lower full-mirror `y_c = -0.495` gives `sCenter.re = 0.995` (`1/2-(-0.495)`), `s/2.re = 0.4975`. Both re-values center-independent (shared `y`-center), so one chain each unlocks all 10 mirrors.
* Task literal `Gamma(1.995)/0.995` is `Real.Gamma sCenter.re` (`0.995`); decomposition actually needs `Real.Gamma (sCenter/2).re` (`0.4975` via `Gamma 1.4975`). Both chains proved below (4 lemmas), distinct `edgeLower_*` names, same convexity + `Gamma_add_one` route as `edgeS00_*`.
* Poly `56` numerals swap roles for lower (`||s|| <= 11`, `||s-1|| <= 10.01`, product `11*10.01/2 <= 56` same value); pi `<=1` reuses generic `edgeS00_pi_upper_rect` (`0 <= s.re` still holds since lower `s.re >= 0.99`).
* `conj_of` transfer: full-strip `y1 = 0.5` fails `y1 < 1/2` (verdict below, reuses `EdgeS00_touches_top` shape); shrunk `y1 = 0.499` satisfies both side conditions at explicit coverage cost (gaps `[0.499,0.5)` + `(-0.5,-0.499)`). Conditional mirror-coordinate lemmas show the `conj_of` shape would give `y0 = -0.499/y1 = -0.49` IF an upper shrunk rect were packaged (zeta wall still blocks actual `RXX_conj` defs).

Correctness: tail Float certs do not cover strips; global `xiShifted_differentiable` false-as-stated, strip entireness only; no `sorry`/`admit`/`axiom`; fully-verified factors only, zero cells claimed closed.
-/

namespace CentralCoverAssembly

open CellProofEngine

/-- Real convexity feeder: `Real.Gamma 1.995 <= 1` (`1.995 = 0.005*1 + 0.995*2`). Mirrors `edgeS00_realGamma_10025_le_one`. -/
theorem edgeLower_realGamma_1995_le_one : Real.Gamma 1.995 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.005 := by norm_num
  have hb : (0 : ℝ) ≤ 0.995 := by norm_num
  have hab : (0.005 : ℝ) + 0.995 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.005 : ℝ) * 1 + 0.995 * 2 = 1.995 := by norm_num
  have hrhs : (0.005 : ℝ) * 1 + 0.995 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 0.995 <= 2` (`Gamma(1.995)/0.995`, literal task route, center-independent). -/
theorem edgeLower_realGamma_0995_le : Real.Gamma 0.995 ≤ 2 := by
  have hx_pos : (0 : ℝ) < 0.995 := by norm_num
  have hne : (0.995 : ℝ) ≠ 0 := ne_of_gt hx_pos
  have hadd : Real.Gamma (0.995 + 1) = 0.995 * Real.Gamma 0.995 :=
    Real.Gamma_add_one hne
  have heq : (0.995 : ℝ) + 1 = 1.995 := by norm_num
  rw [heq] at hadd
  have h1 : Real.Gamma 1.995 ≤ 1 := edgeLower_realGamma_1995_le_one
  rw [hadd] at h1
  have hfin : Real.Gamma 0.995 ≤ 1 / 0.995 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h1
  have hfrac : (1 : ℝ) / 0.995 ≤ 2 := by norm_num
  exact le_trans hfin hfrac

/-- Real convexity feeder for the half-value: `Real.Gamma 1.4975 <= 1` (`1.4975 = 0.5025*1 + 0.4975*2`). -/
theorem edgeLower_realGamma_14975_le_one : Real.Gamma 1.4975 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.5025 := by norm_num
  have hb : (0 : ℝ) ≤ 0.4975 := by norm_num
  have hab : (0.5025 : ℝ) + 0.4975 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.5025 : ℝ) * 1 + 0.4975 * 2 = 1.4975 := by norm_num
  have hrhs : (0.5025 : ℝ) * 1 + 0.4975 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 0.4975 <= 3` (`Gamma(1.4975)/0.4975`, actually-needed `(sCenter/2).re` chain, center-independent). -/
theorem edgeLower_realGamma_04975_le : Real.Gamma 0.4975 ≤ 3 := by
  have hx_pos : (0 : ℝ) < 0.4975 := by norm_num
  have hne : (0.4975 : ℝ) ≠ 0 := ne_of_gt hx_pos
  have hadd : Real.Gamma (0.4975 + 1) = 0.4975 * Real.Gamma 0.4975 :=
    Real.Gamma_add_one hne
  have heq : (0.4975 : ℝ) + 1 = 1.4975 := by norm_num
  rw [heq] at hadd
  have h1 : Real.Gamma 1.4975 ≤ 1 := edgeLower_realGamma_14975_le_one
  rw [hadd] at h1
  have hfin : Real.Gamma 0.4975 ≤ 1 / 0.4975 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h1
  have hfrac : (1 : ℝ) / 0.4975 ≤ 3 := by norm_num
  exact le_trans hfin hfrac

/-- Hypothesis-free generic poly upper `56` for lower strips (`Re in [0.99,1.0]`, `Im in [-10,10]`; numerals swap vs EdgeS00: `11*10.01/2`). Covers all 10 lower columns. -/
theorem edgeLower_poly_upper_generic {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -10 ≤ s.im) (him_hi : s.im ≤ 10) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 := by
  unfold DerivCauchyBridge.polyOf
  have hs_le : ‖s‖ ≤ 11 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_abs : |s.re| ≤ 1.0 := by
      rw [abs_le]
      constructor <;> linarith
    have him_abs : |s.im| ≤ 10 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hs1_le : ‖s - 1‖ ≤ 10.01 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    have him1 : (s - 1).im = s.im := by simp [Complex.sub_im]
    have hre_abs : |(s - 1).re| ≤ 0.01 := by
      rw [hre1, abs_le]
      constructor <;> linarith
    have him_abs : |(s - 1).im| ≤ 10 := by
      rw [him1, abs_le]
      constructor <;> linarith
    linarith
  have hmul : ‖s * (s - 1)‖ ≤ 11 * 10.01 := by
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by norm_num)
  have hnorm : ‖s * (s - 1) / 2‖ ≤ 11 * 10.01 / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith [hmul]
  have hcalc : (11 : ℝ) * 10.01 / 2 ≤ 56 := by norm_num
  linarith

/-- The corner lower-mirror cell `(-10,-7.5)` times `(-0.5,-0.49)` (full mirror of EdgeS00, no shrinkage). -/
def EdgeS00_Lower : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS00_Lower_x0 : EdgeS00_Lower.x0 = -10 := rfl
theorem EdgeS00_Lower_x1 : EdgeS00_Lower.x1 = -7.5 := rfl
theorem EdgeS00_Lower_y0 : EdgeS00_Lower.y0 = -0.5 := rfl
theorem EdgeS00_Lower_y1 : EdgeS00_Lower.y1 = -0.49 := rfl

theorem EdgeS00_Lower_dx_eq : EdgeS00_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS00_Lower_x0, EdgeS00_Lower_x1]; norm_num

theorem EdgeS00_Lower_dy_eq : EdgeS00_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS00_Lower_y0, EdgeS00_Lower_y1]; norm_num

theorem EdgeS00_Lower_radius_eq :
    EdgeS00_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS00_Lower_dx_eq, EdgeS00_Lower_dy_eq]

theorem EdgeS00_Lower_radius_lt : EdgeS00_Lower.radius < 1.26 := by
  rw [EdgeS00_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS00_Lower_strip_hi : EdgeS00_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS00_Lower_y1]; norm_num

/-- `EdgeS00_Lower` touches the bottom boundary (`y0 = -0.5`), mirroring `EdgeS00_touches_top`. -/
theorem EdgeS00_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS00_Lower.y0) := by rw [EdgeS00_Lower_y0]; norm_num

/-- `EdgeS00_Lower.center = -8.75 + (-0.495)*I`. -/
theorem EdgeS00_Lower_center_eq :
    EdgeS00_Lower.center =
      (((-8.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS00_Lower_x0, EdgeS00_Lower_x1, EdgeS00_Lower_y0, EdgeS00_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS00_Lower_x0, EdgeS00_Lower_x1, EdgeS00_Lower_y0, EdgeS00_Lower_y1]
    simp
    norm_num

/-- The `EdgeS00_Lower` `s`-plane center `s = 1/2 + I*z` at `z = EdgeS00_Lower.center`. -/
noncomputable def edgeS00_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS00_Lower.center

/-- `Re edgeS00_Lower_sCenter = 0.995` (`1/2-(-0.495)`, the NEW lower re-value). -/
theorem edgeS00_Lower_sCenter_re : edgeS00_Lower_sCenter.re = 0.995 := by
  unfold edgeS00_Lower_sCenter
  rw [EdgeS00_Lower_center_eq]
  simp
  norm_num

/-- `Im edgeS00_Lower_sCenter = -8.75` (same `x_c` as upper). -/
theorem edgeS00_Lower_sCenter_im : edgeS00_Lower_sCenter.im = -8.75 := by
  unfold edgeS00_Lower_sCenter
  rw [EdgeS00_Lower_center_eq]
  simp

/-- Hypothesis-free poly upper `56` on the `EdgeS00_Lower` `s`-rect (`Re in [0.99,1.0]`, `Im in [-10,-7.5]`). -/
theorem edgeS00_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -10 ≤ s.im) (him_hi : s.im ≤ -7.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

/-- Hypothesis-free pi upper `1` for lower (`0.99 <= s.re` implies `0 <= s.re`; wrapper over generic). -/
theorem edgeS00_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

/-- Hypothesis-free Gamma upper `2` at the lower `s`-center itself (`Re = 0.995`, literal task chain). -/
theorem edgeS00_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS00_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS00_Lower_sCenter.re := by
    rw [edgeS00_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS00_Lower_sCenter.re ≤ 2 := by
    rw [edgeS00_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

/-- Hypothesis-free Gamma upper `3` at `sCenter/2` (`Re = 0.4975`, decomposition chain actually needed). -/
theorem edgeS00_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS00_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS00_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS00_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS00_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS00_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- Y1 VERDICT (full strips): direct `conj_of` inapplicable since `EdgeS00.y1 = 0.5` fails `y1 < 1/2` (reuses `EdgeS00_touches_top` shape). Same numeral holds for EdgeS01-S09. -/
theorem edgeS00_full_strip_conj_blocked : ¬ EdgeS00.y1 < (1 / 2 : ℝ) :=
  EdgeS00_touches_top

/-- Shrunk upper `(-10,-7.5)` times `(0.49,0.499)` (SHRINKAGE EXPLICIT: `y1 = 0.499`, gap `[0.499,0.5)` uncovered). -/
def EdgeS00_ShrunkUpper : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, 0.49, 0.499, by norm_num, by norm_num⟩

theorem EdgeS00_ShrunkUpper_x0 : EdgeS00_ShrunkUpper.x0 = -10 := rfl
theorem EdgeS00_ShrunkUpper_x1 : EdgeS00_ShrunkUpper.x1 = -7.5 := rfl
theorem EdgeS00_ShrunkUpper_y0 : EdgeS00_ShrunkUpper.y0 = 0.49 := rfl
theorem EdgeS00_ShrunkUpper_y1 : EdgeS00_ShrunkUpper.y1 = 0.499 := rfl

/-- Shrunk upper satisfies `0 < y0` (first `conj_of` side condition). -/
theorem EdgeS00_ShrunkUpper_y0_pos : 0 < EdgeS00_ShrunkUpper.y0 := by rw [EdgeS00_ShrunkUpper_y0]; norm_num

/-- Shrunk upper satisfies `y1 < 1/2` (second `conj_of` side condition; full `y1 = 0.5` fails). -/
theorem EdgeS00_ShrunkUpper_y1_lt : EdgeS00_ShrunkUpper.y1 < (1 / 2 : ℝ) := by rw [EdgeS00_ShrunkUpper_y1]; norm_num

/-- Shrunk lower `(-10,-7.5)` times `(-0.499,-0.49)` (mirror of shrunk upper, gap `(-0.5,-0.499)` uncovered). -/
def EdgeS00_ShrunkLower : CellProofEngine.Rect2D :=
  ⟨-10, -7.5, -0.499, -0.49, by norm_num, by norm_num⟩

theorem EdgeS00_ShrunkLower_x0 : EdgeS00_ShrunkLower.x0 = -10 := rfl
theorem EdgeS00_ShrunkLower_x1 : EdgeS00_ShrunkLower.x1 = -7.5 := rfl
theorem EdgeS00_ShrunkLower_y0 : EdgeS00_ShrunkLower.y0 = -0.499 := rfl
theorem EdgeS00_ShrunkLower_y1 : EdgeS00_ShrunkLower.y1 = -0.49 := rfl

theorem EdgeS00_ShrunkLower_strip_lo : -(1 / 2 : ℝ) < EdgeS00_ShrunkLower.y0 := by rw [EdgeS00_ShrunkLower_y0]; norm_num
theorem EdgeS00_ShrunkLower_strip_hi : EdgeS00_ShrunkLower.y1 < (1 / 2 : ℝ) := by rw [EdgeS00_ShrunkLower_y1]; norm_num

/-- Shrunk coordinate mirror: `ShrunkLower.y0 = -ShrunkUpper.y1` (by `rfl` numerals). -/
theorem EdgeS00_shrunk_mirror_y0 : EdgeS00_ShrunkLower.y0 = -EdgeS00_ShrunkUpper.y1 := rfl

/-- Shrunk coordinate mirror: `ShrunkLower.y1 = -ShrunkUpper.y0` (by `rfl` numerals). -/
theorem EdgeS00_shrunk_mirror_y1 : EdgeS00_ShrunkLower.y1 = -EdgeS00_ShrunkUpper.y0 := rfl

/-- Conditional `conj_of` shape for shrunk zero-free rects: IF an upper shrunk rect with `y = (0.49,0.499)` were packaged, `conj_of` would give `y = (-0.499,-0.49)` (mirrors `R00_conjZF_of_bounds` template; actual upper rect blocked by zeta wall). -/
theorem edgeS00_shrunk_conjZF_mirror_coords (R : XiLocalZeroFreeRect)
    (h0 : R.y0 = 0.49) (h1 : R.y1 = 0.499)
    (hy0 : 0 < R.y0) (hy1 : R.y1 < 1 / 2) :
    (XiLocalZeroFreeRect.conj_of R hy0 hy1).y0 = -0.499 ∧
    (XiLocalZeroFreeRect.conj_of R hy0 hy1).y1 = -0.49 := by
  constructor
  · have e : (XiLocalZeroFreeRect.conj_of R hy0 hy1).y0 = -R.y1 := rfl
    rw [e, h1]
  · have e : (XiLocalZeroFreeRect.conj_of R hy0 hy1).y1 = -R.y0 := rfl
    rw [e, h0]

/-- Conditional `conj_of` shape for shrunk lower-bound rects (mirrors `R00_conjLB_of_bounds` template). -/
theorem edgeS00_shrunk_conjLB_mirror_coords (B : XiLocalLowerBoundRect)
    (h0 : B.y0 = 0.49) (h1 : B.y1 = 0.499)
    (hy0 : 0 < B.y0) (hy1 : B.y1 < 1 / 2) :
    (XiLocalLowerBoundRect.conj_of B hy0 hy1).y0 = -0.499 ∧
    (XiLocalLowerBoundRect.conj_of B hy0 hy1).y1 = -0.49 := by
  constructor
  · have e : (XiLocalLowerBoundRect.conj_of B hy0 hy1).y0 = -B.y1 := rfl
    rw [e, h1]
  · have e : (XiLocalLowerBoundRect.conj_of B hy0 hy1).y1 = -B.y0 := rfl
    rw [e, h0]

/-- The lower-mirror cell `(-8,-5.5)` times `(-0.5,-0.49)` (full mirror of EdgeS01). -/
def EdgeS01_Lower : CellProofEngine.Rect2D :=
  ⟨-8, -5.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS01_Lower_x0 : EdgeS01_Lower.x0 = -8 := rfl
theorem EdgeS01_Lower_x1 : EdgeS01_Lower.x1 = -5.5 := rfl
theorem EdgeS01_Lower_y0 : EdgeS01_Lower.y0 = -0.5 := rfl
theorem EdgeS01_Lower_y1 : EdgeS01_Lower.y1 = -0.49 := rfl

theorem EdgeS01_Lower_dx_eq : EdgeS01_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS01_Lower_x0, EdgeS01_Lower_x1]; norm_num

theorem EdgeS01_Lower_dy_eq : EdgeS01_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS01_Lower_y0, EdgeS01_Lower_y1]; norm_num

theorem EdgeS01_Lower_radius_eq :
    EdgeS01_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS01_Lower_dx_eq, EdgeS01_Lower_dy_eq]

theorem EdgeS01_Lower_radius_lt : EdgeS01_Lower.radius < 1.26 := by
  rw [EdgeS01_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS01_Lower_strip_hi : EdgeS01_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS01_Lower_y1]; norm_num
theorem EdgeS01_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS01_Lower.y0) := by rw [EdgeS01_Lower_y0]; norm_num

theorem EdgeS01_Lower_center_eq :
    EdgeS01_Lower.center =
      (((-6.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS01_Lower_x0, EdgeS01_Lower_x1, EdgeS01_Lower_y0, EdgeS01_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS01_Lower_x0, EdgeS01_Lower_x1, EdgeS01_Lower_y0, EdgeS01_Lower_y1]
    simp
    norm_num

noncomputable def edgeS01_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS01_Lower.center

theorem edgeS01_Lower_sCenter_re : edgeS01_Lower_sCenter.re = 0.995 := by
  unfold edgeS01_Lower_sCenter
  rw [EdgeS01_Lower_center_eq]
  simp
  norm_num

theorem edgeS01_Lower_sCenter_im : edgeS01_Lower_sCenter.im = -6.75 := by
  unfold edgeS01_Lower_sCenter
  rw [EdgeS01_Lower_center_eq]
  simp

theorem edgeS01_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -8 ≤ s.im) (him_hi : s.im ≤ -5.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS01_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS01_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS01_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS01_Lower_sCenter.re := by
    rw [edgeS01_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS01_Lower_sCenter.re ≤ 2 := by
    rw [edgeS01_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS01_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS01_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS01_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS01_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS01_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS01_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(-6,-3.5)` times `(-0.5,-0.49)` (full mirror of EdgeS02). -/
def EdgeS02_Lower : CellProofEngine.Rect2D :=
  ⟨-6, -3.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS02_Lower_x0 : EdgeS02_Lower.x0 = -6 := rfl
theorem EdgeS02_Lower_x1 : EdgeS02_Lower.x1 = -3.5 := rfl
theorem EdgeS02_Lower_y0 : EdgeS02_Lower.y0 = -0.5 := rfl
theorem EdgeS02_Lower_y1 : EdgeS02_Lower.y1 = -0.49 := rfl

theorem EdgeS02_Lower_dx_eq : EdgeS02_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS02_Lower_x0, EdgeS02_Lower_x1]; norm_num

theorem EdgeS02_Lower_dy_eq : EdgeS02_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS02_Lower_y0, EdgeS02_Lower_y1]; norm_num

theorem EdgeS02_Lower_radius_eq :
    EdgeS02_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS02_Lower_dx_eq, EdgeS02_Lower_dy_eq]

theorem EdgeS02_Lower_radius_lt : EdgeS02_Lower.radius < 1.26 := by
  rw [EdgeS02_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS02_Lower_strip_hi : EdgeS02_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS02_Lower_y1]; norm_num
theorem EdgeS02_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS02_Lower.y0) := by rw [EdgeS02_Lower_y0]; norm_num

theorem EdgeS02_Lower_center_eq :
    EdgeS02_Lower.center =
      (((-4.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS02_Lower_x0, EdgeS02_Lower_x1, EdgeS02_Lower_y0, EdgeS02_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS02_Lower_x0, EdgeS02_Lower_x1, EdgeS02_Lower_y0, EdgeS02_Lower_y1]
    simp
    norm_num

noncomputable def edgeS02_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS02_Lower.center

theorem edgeS02_Lower_sCenter_re : edgeS02_Lower_sCenter.re = 0.995 := by
  unfold edgeS02_Lower_sCenter
  rw [EdgeS02_Lower_center_eq]
  simp
  norm_num

theorem edgeS02_Lower_sCenter_im : edgeS02_Lower_sCenter.im = -4.75 := by
  unfold edgeS02_Lower_sCenter
  rw [EdgeS02_Lower_center_eq]
  simp

theorem edgeS02_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -6 ≤ s.im) (him_hi : s.im ≤ -3.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS02_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS02_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS02_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS02_Lower_sCenter.re := by
    rw [edgeS02_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS02_Lower_sCenter.re ≤ 2 := by
    rw [edgeS02_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS02_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS02_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS02_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS02_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS02_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS02_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(-4,-1.5)` times `(-0.5,-0.49)` (full mirror of EdgeS03). -/
def EdgeS03_Lower : CellProofEngine.Rect2D :=
  ⟨-4, -1.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS03_Lower_x0 : EdgeS03_Lower.x0 = -4 := rfl
theorem EdgeS03_Lower_x1 : EdgeS03_Lower.x1 = -1.5 := rfl
theorem EdgeS03_Lower_y0 : EdgeS03_Lower.y0 = -0.5 := rfl
theorem EdgeS03_Lower_y1 : EdgeS03_Lower.y1 = -0.49 := rfl

theorem EdgeS03_Lower_dx_eq : EdgeS03_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS03_Lower_x0, EdgeS03_Lower_x1]; norm_num

theorem EdgeS03_Lower_dy_eq : EdgeS03_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS03_Lower_y0, EdgeS03_Lower_y1]; norm_num

theorem EdgeS03_Lower_radius_eq :
    EdgeS03_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS03_Lower_dx_eq, EdgeS03_Lower_dy_eq]

theorem EdgeS03_Lower_radius_lt : EdgeS03_Lower.radius < 1.26 := by
  rw [EdgeS03_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS03_Lower_strip_hi : EdgeS03_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS03_Lower_y1]; norm_num
theorem EdgeS03_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS03_Lower.y0) := by rw [EdgeS03_Lower_y0]; norm_num

theorem EdgeS03_Lower_center_eq :
    EdgeS03_Lower.center =
      (((-2.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS03_Lower_x0, EdgeS03_Lower_x1, EdgeS03_Lower_y0, EdgeS03_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS03_Lower_x0, EdgeS03_Lower_x1, EdgeS03_Lower_y0, EdgeS03_Lower_y1]
    simp
    norm_num

noncomputable def edgeS03_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS03_Lower.center

theorem edgeS03_Lower_sCenter_re : edgeS03_Lower_sCenter.re = 0.995 := by
  unfold edgeS03_Lower_sCenter
  rw [EdgeS03_Lower_center_eq]
  simp
  norm_num

theorem edgeS03_Lower_sCenter_im : edgeS03_Lower_sCenter.im = -2.75 := by
  unfold edgeS03_Lower_sCenter
  rw [EdgeS03_Lower_center_eq]
  simp

theorem edgeS03_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -4 ≤ s.im) (him_hi : s.im ≤ -1.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS03_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS03_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS03_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS03_Lower_sCenter.re := by
    rw [edgeS03_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS03_Lower_sCenter.re ≤ 2 := by
    rw [edgeS03_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS03_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS03_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS03_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS03_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS03_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS03_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(-2,0.5)` times `(-0.5,-0.49)` (full mirror of EdgeS04). -/
def EdgeS04_Lower : CellProofEngine.Rect2D :=
  ⟨-2, 0.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS04_Lower_x0 : EdgeS04_Lower.x0 = -2 := rfl
theorem EdgeS04_Lower_x1 : EdgeS04_Lower.x1 = 0.5 := rfl
theorem EdgeS04_Lower_y0 : EdgeS04_Lower.y0 = -0.5 := rfl
theorem EdgeS04_Lower_y1 : EdgeS04_Lower.y1 = -0.49 := rfl

theorem EdgeS04_Lower_dx_eq : EdgeS04_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS04_Lower_x0, EdgeS04_Lower_x1]; norm_num

theorem EdgeS04_Lower_dy_eq : EdgeS04_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS04_Lower_y0, EdgeS04_Lower_y1]; norm_num

theorem EdgeS04_Lower_radius_eq :
    EdgeS04_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS04_Lower_dx_eq, EdgeS04_Lower_dy_eq]

theorem EdgeS04_Lower_radius_lt : EdgeS04_Lower.radius < 1.26 := by
  rw [EdgeS04_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS04_Lower_strip_hi : EdgeS04_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS04_Lower_y1]; norm_num
theorem EdgeS04_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS04_Lower.y0) := by rw [EdgeS04_Lower_y0]; norm_num

theorem EdgeS04_Lower_center_eq :
    EdgeS04_Lower.center =
      (((-0.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS04_Lower_x0, EdgeS04_Lower_x1, EdgeS04_Lower_y0, EdgeS04_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS04_Lower_x0, EdgeS04_Lower_x1, EdgeS04_Lower_y0, EdgeS04_Lower_y1]
    simp
    norm_num

noncomputable def edgeS04_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS04_Lower.center

theorem edgeS04_Lower_sCenter_re : edgeS04_Lower_sCenter.re = 0.995 := by
  unfold edgeS04_Lower_sCenter
  rw [EdgeS04_Lower_center_eq]
  simp
  norm_num

theorem edgeS04_Lower_sCenter_im : edgeS04_Lower_sCenter.im = -0.75 := by
  unfold edgeS04_Lower_sCenter
  rw [EdgeS04_Lower_center_eq]
  simp

theorem edgeS04_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : -2 ≤ s.im) (him_hi : s.im ≤ 0.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS04_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS04_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS04_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS04_Lower_sCenter.re := by
    rw [edgeS04_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS04_Lower_sCenter.re ≤ 2 := by
    rw [edgeS04_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS04_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS04_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS04_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS04_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS04_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS04_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(0,2.5)` times `(-0.5,-0.49)` (full mirror of EdgeS05). -/
def EdgeS05_Lower : CellProofEngine.Rect2D :=
  ⟨0, 2.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS05_Lower_x0 : EdgeS05_Lower.x0 = 0 := rfl
theorem EdgeS05_Lower_x1 : EdgeS05_Lower.x1 = 2.5 := rfl
theorem EdgeS05_Lower_y0 : EdgeS05_Lower.y0 = -0.5 := rfl
theorem EdgeS05_Lower_y1 : EdgeS05_Lower.y1 = -0.49 := rfl

theorem EdgeS05_Lower_dx_eq : EdgeS05_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS05_Lower_x0, EdgeS05_Lower_x1]; norm_num

theorem EdgeS05_Lower_dy_eq : EdgeS05_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS05_Lower_y0, EdgeS05_Lower_y1]; norm_num

theorem EdgeS05_Lower_radius_eq :
    EdgeS05_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS05_Lower_dx_eq, EdgeS05_Lower_dy_eq]

theorem EdgeS05_Lower_radius_lt : EdgeS05_Lower.radius < 1.26 := by
  rw [EdgeS05_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS05_Lower_strip_hi : EdgeS05_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS05_Lower_y1]; norm_num
theorem EdgeS05_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS05_Lower.y0) := by rw [EdgeS05_Lower_y0]; norm_num

theorem EdgeS05_Lower_center_eq :
    EdgeS05_Lower.center =
      (((1.25 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS05_Lower_x0, EdgeS05_Lower_x1, EdgeS05_Lower_y0, EdgeS05_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS05_Lower_x0, EdgeS05_Lower_x1, EdgeS05_Lower_y0, EdgeS05_Lower_y1]
    simp
    norm_num

noncomputable def edgeS05_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS05_Lower.center

theorem edgeS05_Lower_sCenter_re : edgeS05_Lower_sCenter.re = 0.995 := by
  unfold edgeS05_Lower_sCenter
  rw [EdgeS05_Lower_center_eq]
  simp
  norm_num

theorem edgeS05_Lower_sCenter_im : edgeS05_Lower_sCenter.im = 1.25 := by
  unfold edgeS05_Lower_sCenter
  rw [EdgeS05_Lower_center_eq]
  simp

theorem edgeS05_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : 0 ≤ s.im) (him_hi : s.im ≤ 2.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS05_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS05_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS05_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS05_Lower_sCenter.re := by
    rw [edgeS05_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS05_Lower_sCenter.re ≤ 2 := by
    rw [edgeS05_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS05_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS05_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS05_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS05_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS05_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS05_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(2,4.5)` times `(-0.5,-0.49)` (full mirror of EdgeS06). -/
def EdgeS06_Lower : CellProofEngine.Rect2D :=
  ⟨2, 4.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS06_Lower_x0 : EdgeS06_Lower.x0 = 2 := rfl
theorem EdgeS06_Lower_x1 : EdgeS06_Lower.x1 = 4.5 := rfl
theorem EdgeS06_Lower_y0 : EdgeS06_Lower.y0 = -0.5 := rfl
theorem EdgeS06_Lower_y1 : EdgeS06_Lower.y1 = -0.49 := rfl

theorem EdgeS06_Lower_dx_eq : EdgeS06_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS06_Lower_x0, EdgeS06_Lower_x1]; norm_num

theorem EdgeS06_Lower_dy_eq : EdgeS06_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS06_Lower_y0, EdgeS06_Lower_y1]; norm_num

theorem EdgeS06_Lower_radius_eq :
    EdgeS06_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS06_Lower_dx_eq, EdgeS06_Lower_dy_eq]

theorem EdgeS06_Lower_radius_lt : EdgeS06_Lower.radius < 1.26 := by
  rw [EdgeS06_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS06_Lower_strip_hi : EdgeS06_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS06_Lower_y1]; norm_num
theorem EdgeS06_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS06_Lower.y0) := by rw [EdgeS06_Lower_y0]; norm_num

theorem EdgeS06_Lower_center_eq :
    EdgeS06_Lower.center =
      (((3.25 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS06_Lower_x0, EdgeS06_Lower_x1, EdgeS06_Lower_y0, EdgeS06_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS06_Lower_x0, EdgeS06_Lower_x1, EdgeS06_Lower_y0, EdgeS06_Lower_y1]
    simp
    norm_num

noncomputable def edgeS06_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS06_Lower.center

theorem edgeS06_Lower_sCenter_re : edgeS06_Lower_sCenter.re = 0.995 := by
  unfold edgeS06_Lower_sCenter
  rw [EdgeS06_Lower_center_eq]
  simp
  norm_num

theorem edgeS06_Lower_sCenter_im : edgeS06_Lower_sCenter.im = 3.25 := by
  unfold edgeS06_Lower_sCenter
  rw [EdgeS06_Lower_center_eq]
  simp

theorem edgeS06_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : 2 ≤ s.im) (him_hi : s.im ≤ 4.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS06_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS06_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS06_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS06_Lower_sCenter.re := by
    rw [edgeS06_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS06_Lower_sCenter.re ≤ 2 := by
    rw [edgeS06_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS06_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS06_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS06_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS06_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS06_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS06_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(4,6.5)` times `(-0.5,-0.49)` (full mirror of EdgeS07). -/
def EdgeS07_Lower : CellProofEngine.Rect2D :=
  ⟨4, 6.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS07_Lower_x0 : EdgeS07_Lower.x0 = 4 := rfl
theorem EdgeS07_Lower_x1 : EdgeS07_Lower.x1 = 6.5 := rfl
theorem EdgeS07_Lower_y0 : EdgeS07_Lower.y0 = -0.5 := rfl
theorem EdgeS07_Lower_y1 : EdgeS07_Lower.y1 = -0.49 := rfl

theorem EdgeS07_Lower_dx_eq : EdgeS07_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS07_Lower_x0, EdgeS07_Lower_x1]; norm_num

theorem EdgeS07_Lower_dy_eq : EdgeS07_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS07_Lower_y0, EdgeS07_Lower_y1]; norm_num

theorem EdgeS07_Lower_radius_eq :
    EdgeS07_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS07_Lower_dx_eq, EdgeS07_Lower_dy_eq]

theorem EdgeS07_Lower_radius_lt : EdgeS07_Lower.radius < 1.26 := by
  rw [EdgeS07_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS07_Lower_strip_hi : EdgeS07_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS07_Lower_y1]; norm_num
theorem EdgeS07_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS07_Lower.y0) := by rw [EdgeS07_Lower_y0]; norm_num

theorem EdgeS07_Lower_center_eq :
    EdgeS07_Lower.center =
      (((5.25 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS07_Lower_x0, EdgeS07_Lower_x1, EdgeS07_Lower_y0, EdgeS07_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS07_Lower_x0, EdgeS07_Lower_x1, EdgeS07_Lower_y0, EdgeS07_Lower_y1]
    simp
    norm_num

noncomputable def edgeS07_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS07_Lower.center

theorem edgeS07_Lower_sCenter_re : edgeS07_Lower_sCenter.re = 0.995 := by
  unfold edgeS07_Lower_sCenter
  rw [EdgeS07_Lower_center_eq]
  simp
  norm_num

theorem edgeS07_Lower_sCenter_im : edgeS07_Lower_sCenter.im = 5.25 := by
  unfold edgeS07_Lower_sCenter
  rw [EdgeS07_Lower_center_eq]
  simp

theorem edgeS07_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : 4 ≤ s.im) (him_hi : s.im ≤ 6.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS07_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS07_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS07_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS07_Lower_sCenter.re := by
    rw [edgeS07_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS07_Lower_sCenter.re ≤ 2 := by
    rw [edgeS07_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS07_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS07_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS07_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS07_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS07_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS07_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(6,8.5)` times `(-0.5,-0.49)` (full mirror of EdgeS08). -/
def EdgeS08_Lower : CellProofEngine.Rect2D :=
  ⟨6, 8.5, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS08_Lower_x0 : EdgeS08_Lower.x0 = 6 := rfl
theorem EdgeS08_Lower_x1 : EdgeS08_Lower.x1 = 8.5 := rfl
theorem EdgeS08_Lower_y0 : EdgeS08_Lower.y0 = -0.5 := rfl
theorem EdgeS08_Lower_y1 : EdgeS08_Lower.y1 = -0.49 := rfl

theorem EdgeS08_Lower_dx_eq : EdgeS08_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS08_Lower_x0, EdgeS08_Lower_x1]; norm_num

theorem EdgeS08_Lower_dy_eq : EdgeS08_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS08_Lower_y0, EdgeS08_Lower_y1]; norm_num

theorem EdgeS08_Lower_radius_eq :
    EdgeS08_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS08_Lower_dx_eq, EdgeS08_Lower_dy_eq]

theorem EdgeS08_Lower_radius_lt : EdgeS08_Lower.radius < 1.26 := by
  rw [EdgeS08_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS08_Lower_strip_hi : EdgeS08_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS08_Lower_y1]; norm_num
theorem EdgeS08_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS08_Lower.y0) := by rw [EdgeS08_Lower_y0]; norm_num

theorem EdgeS08_Lower_center_eq :
    EdgeS08_Lower.center =
      (((7.25 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS08_Lower_x0, EdgeS08_Lower_x1, EdgeS08_Lower_y0, EdgeS08_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS08_Lower_x0, EdgeS08_Lower_x1, EdgeS08_Lower_y0, EdgeS08_Lower_y1]
    simp
    norm_num

noncomputable def edgeS08_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS08_Lower.center

theorem edgeS08_Lower_sCenter_re : edgeS08_Lower_sCenter.re = 0.995 := by
  unfold edgeS08_Lower_sCenter
  rw [EdgeS08_Lower_center_eq]
  simp
  norm_num

theorem edgeS08_Lower_sCenter_im : edgeS08_Lower_sCenter.im = 7.25 := by
  unfold edgeS08_Lower_sCenter
  rw [EdgeS08_Lower_center_eq]
  simp

theorem edgeS08_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : 6 ≤ s.im) (him_hi : s.im ≤ 8.5) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS08_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS08_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS08_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS08_Lower_sCenter.re := by
    rw [edgeS08_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS08_Lower_sCenter.re ≤ 2 := by
    rw [edgeS08_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS08_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS08_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS08_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS08_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS08_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS08_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

/-- The lower-mirror cell `(7.5,10)` times `(-0.5,-0.49)` (full mirror of EdgeS09). -/
def EdgeS09_Lower : CellProofEngine.Rect2D :=
  ⟨7.5, 10, -0.5, -0.49, by norm_num, by norm_num⟩

theorem EdgeS09_Lower_x0 : EdgeS09_Lower.x0 = 7.5 := rfl
theorem EdgeS09_Lower_x1 : EdgeS09_Lower.x1 = 10 := rfl
theorem EdgeS09_Lower_y0 : EdgeS09_Lower.y0 = -0.5 := rfl
theorem EdgeS09_Lower_y1 : EdgeS09_Lower.y1 = -0.49 := rfl

theorem EdgeS09_Lower_dx_eq : EdgeS09_Lower.dx = 1.25 := by
  unfold CellProofEngine.Rect2D.dx
  rw [EdgeS09_Lower_x0, EdgeS09_Lower_x1]; norm_num

theorem EdgeS09_Lower_dy_eq : EdgeS09_Lower.dy = 0.005 := by
  unfold CellProofEngine.Rect2D.dy
  rw [EdgeS09_Lower_y0, EdgeS09_Lower_y1]; norm_num

theorem EdgeS09_Lower_radius_eq :
    EdgeS09_Lower.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.005 : ℝ) ^ 2) := by
  unfold CellProofEngine.Rect2D.radius
  rw [EdgeS09_Lower_dx_eq, EdgeS09_Lower_dy_eq]

theorem EdgeS09_Lower_radius_lt : EdgeS09_Lower.radius < 1.26 := by
  rw [EdgeS09_Lower_radius_eq]; exact edgeStrip_radius_bound

theorem EdgeS09_Lower_strip_hi : EdgeS09_Lower.y1 < (1 / 2 : ℝ) := by rw [EdgeS09_Lower_y1]; norm_num
theorem EdgeS09_Lower_touches_bottom : ¬ (-(1 / 2 : ℝ) < EdgeS09_Lower.y0) := by rw [EdgeS09_Lower_y0]; norm_num

theorem EdgeS09_Lower_center_eq :
    EdgeS09_Lower.center =
      (((8.75 : ℝ))) + Complex.I * ((((-0.495 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS09_Lower_x0, EdgeS09_Lower_x1, EdgeS09_Lower_y0, EdgeS09_Lower_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [EdgeS09_Lower_x0, EdgeS09_Lower_x1, EdgeS09_Lower_y0, EdgeS09_Lower_y1]
    simp
    norm_num

noncomputable def edgeS09_Lower_sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * EdgeS09_Lower.center

theorem edgeS09_Lower_sCenter_re : edgeS09_Lower_sCenter.re = 0.995 := by
  unfold edgeS09_Lower_sCenter
  rw [EdgeS09_Lower_center_eq]
  simp
  norm_num

theorem edgeS09_Lower_sCenter_im : edgeS09_Lower_sCenter.im = 8.75 := by
  unfold edgeS09_Lower_sCenter
  rw [EdgeS09_Lower_center_eq]
  simp

theorem edgeS09_Lower_poly_upper_rect {s : ℂ}
    (hre_lo : 0.99 ≤ s.re) (hre_hi : s.re ≤ 1.0)
    (him_lo : 7.5 ≤ s.im) (him_hi : s.im ≤ 10) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ 56 :=
  edgeLower_poly_upper_generic hre_lo hre_hi (by linarith) (by linarith)

theorem edgeS09_Lower_pi_upper_rect {s : ℂ} (hre_lo : 0.99 ≤ s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 :=
  edgeS00_pi_upper_rect (by linarith)

theorem edgeS09_Lower_gamma_upper_sCenter :
    ‖Complex.Gamma edgeS09_Lower_sCenter‖ ≤ 2 := by
  have hzpos : (0 : ℝ) < edgeS09_Lower_sCenter.re := by
    rw [edgeS09_Lower_sCenter_re]; norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma edgeS09_Lower_sCenter.re ≤ 2 := by
    rw [edgeS09_Lower_sCenter_re]
    exact edgeLower_realGamma_0995_le
  linarith

theorem edgeS09_Lower_gamma_upper_center :
    ‖Complex.Gamma (edgeS09_Lower_sCenter / 2)‖ ≤ 3 := by
  have h2re : (edgeS09_Lower_sCenter / 2).re = 0.4975 := by
    rw [Complex.div_ofNat_re, edgeS09_Lower_sCenter_re]
    norm_num
  have hzpos : (0 : ℝ) < (edgeS09_Lower_sCenter / 2).re := by
    rw [h2re]
    norm_num
  have hle := DerivCauchyBridge.norm_Gamma_le_realGamma hzpos
  have hreal : Real.Gamma ((edgeS09_Lower_sCenter / 2).re) ≤ 3 := by
    rw [h2re]
    exact edgeLower_realGamma_04975_le
  linarith

#print axioms edgeLower_realGamma_1995_le_one
#print axioms edgeLower_realGamma_0995_le
#print axioms edgeLower_realGamma_14975_le_one
#print axioms edgeLower_realGamma_04975_le
#print axioms edgeLower_poly_upper_generic
#print axioms EdgeS00_Lower_radius_lt
#print axioms EdgeS00_Lower_touches_bottom
#print axioms edgeS00_Lower_poly_upper_rect
#print axioms edgeS00_Lower_pi_upper_rect
#print axioms edgeS00_Lower_gamma_upper_sCenter
#print axioms edgeS00_Lower_gamma_upper_center
#print axioms EdgeS00_ShrunkUpper_y0_pos
#print axioms EdgeS00_ShrunkUpper_y1_lt
#print axioms edgeS00_shrunk_conjZF_mirror_coords
#print axioms edgeS00_shrunk_conjLB_mirror_coords
#print axioms EdgeS01_Lower_radius_lt
#print axioms edgeS01_Lower_gamma_upper_center
#print axioms EdgeS09_Lower_radius_lt
#print axioms edgeS09_Lower_gamma_upper_center

end CentralCoverAssembly

/-! ## Lower-mirror packaged + residual inventory (honest, no `sorry`)

Packaged this append (unconditional end-to-end, hypothesis-free, green below):
* Center-independent `0.995`-family Gamma chains (4 lemmas, mirror `edgeS00_realGamma_00025_le` one-over-x route, distinct `edgeLower_*` names, `interval_arith` untouched): `edgeLower_realGamma_1995_le_one` (`Gamma 1.995 <= 1` via `Real.convexOn_Gamma` weights `0.005/0.995`) + `edgeLower_realGamma_0995_le` (`Gamma 0.995 <= 2` via `Gamma_add_one` + `1/0.995 <= 2`); plus actually-needed half-value `edgeLower_realGamma_14975_le_one` (`Gamma 1.4975 <= 1` weights `0.5025/0.4975`) + `edgeLower_realGamma_04975_le` (`Gamma 0.4975 <= 3` via `1/0.4975 <= 3`). Task literal `Gamma(1.995)/0.995` is `Gamma sCenter.re`; decomposition needs `Gamma (sCenter/2).re`; both provided, each unlocks all 10 mirrors.
* Generic lower poly `edgeLower_poly_upper_generic` (`<=56` for `Re in [0.99,1.0]`, `Im in [-10,10]`; numerals `11*10.01/2`, roles swapped vs upper `10.01*11/2`).
* ONE lower mirror end-to-end `EdgeS00_Lower (-10,-7.5)` at `y = (-0.5,-0.49)` (no shrinkage): geometry (`x0/x1/y0/y1` by `rfl`, `dx=1.25`, `dy=0.005`, `radius_eq` + `radius_lt<1.26` via shared `edgeStrip_radius_bound`, `strip_hi`, `touches_bottom` mirroring `touches_top`), `center = -8.75 + (-0.495)*I`, `sCenter` (`re=0.995`, `im=-8.75`), factors `poly<=56` (wrapper over generic), `pi<=1` (wrapper over `edgeS00_pi_upper_rect`), `Gamma sCenter<=2` (literal chain) + `Gamma (sCenter/2)<=3` (decomposition chain via `DerivCauchyBridge.norm_Gamma_le_realGamma`).
* Y1 VERDICT (read `conj_of` lines 361/394: needs `0 < R.y0`, `R.y1 < 1/2` strictly): full strips `y1 = 0.5` FAIL (`edgeS00_full_strip_conj_blocked` reuses `EdgeS00_touches_top`; same numeral for S01-S09), so direct `conj_of` inapplicable even if upper H-leaf closed. SHRINKAGE EXPLICIT: `EdgeS00_ShrunkUpper y = (0.49,0.499)` (`y1 = 0.499`, gap `[0.499,0.5)` uncovered) satisfies both side conditions (`y0_pos`, `y1_lt` by `norm_num`); mirror `EdgeS00_ShrunkLower y = (-0.499,-0.49)` (`y0 = -y1`/`y1 = -y0` by `rfl`, strictly inside strip) + conditional `conj_of` coordinate shapes (`edgeS00_shrunk_conjZF/LB_mirror_coords`, mirror `R00_conjZF/LB_of_bounds` template, hypothesis `R.y0=0.49/R.y1=0.499` since no upper shrunk rect packaged yet).
* Remaining 9 mirrors `EdgeS01_Lower`-`EdgeS09_Lower` (full, no shrinkage): each geometry + `center = x_c + (-0.495)*I` (`x_c = -6.75,-4.75,-2.75,-0.75,1.25,3.25,5.25,7.25,8.75`) + `sCenter` (`re=0.995`, `im=x_c`) + `poly<=56` (per-column `Im` hypotheses, wrapper over generic) + `pi<=1` + both Gammas (`<=2`/`<=3` reuse center-independent chains). Same shrunk `y1 = 0.499` variant applies analogously per column (not reduplicated).

Closed cells this append (unconditional end-to-end, no hypotheses): NONE (0). Full H-leaf closure stays zeta-blocked, NOT claimed.

Residual (each names exact missing lemma):
1. Upper strips `EdgeS00-S09`: per cell CENTER lower needs `Azeta` lower at `s.re=0.005` + DERIV upper needs tight `||zeta||<=10` + top-touching outer-bound (`upper_boundary_nonvanishing_from_outer_bound`); same wall as 40 central cells.
2. Lower mirrors `EdgeS00_Lower`-`EdgeS09_Lower` (10 cells): hypothesis-free factors done above; per cell CENTER lower needs `Azeta` at NEW `s.re=0.995` (`s=0.995+x_c*I`, e.g. `0.995-8.75*I` for S00) + DERIV upper needs tight `||zeta||<=10` on disc `s`-rect (`Re in [0.99,1.0]`-plus-disc, `Im = x_c`-plus-disc); bottom-touching `y0=-0.5` additionally needs outer-bound mirror of top (same `zeta` upper); `conj_of` transfer of full `XiLocalZeroFreeRect`/`XiLocalLowerBoundRect` additionally needs upper H-leaf item 1 (even shrunk `y1=0.499` needs upper shrunk H-leaf + slightly different `0.9945/0.49725` Gamma re-values, not packaged).
3. Cutoff lines `Re=+-10` (`CutL10/R10` geometry done): same two `zeta` enclosures on vertical `s`-rects, then H-leaf + `cutoffLines_either`; lines with `0.49<=|Im|<1/2` additionally need items 1-2.

Correctness: tail Float certs do not cover strips; global `xiShifted_differentiable` false-as-stated, strip entireness only.
-/

/-! ## Rouché zero-count stability, Jensen route, disc-only, sorry-free

GREP verdict 2026-09-03, cites verified by reading:
- Mathlib complex Rouché, Hurwitz, winding number, argument principle: ABSENT.
  Mathlib/Analysis/Complex/LocallyUniformLimit.lean:136 gives holomorphic limit only,
  Mathlib/Analysis/Analytic/IsolatedZeros.lean:125 gives isolated zeros only,
  Mathlib/Analysis/Complex/JensenFormula.lean:308,376,390 gives Jensen equality
  plus a zero-count UPPER bound only, no Rouché equality of counts.
  No windingNumber, no argumentPrinciple, no countZeros in Mathlib.
  Docs docs/1000.yaml:1377 and :1503 list Hurwitz and Rouché titles with NO decl.
- Consumer READ-ONLY: JensenTranslation.lean:20295 and :20335,
  guide AGENT_INFRASTRUCTURE_GUIDE.md:1269-1271. This block closes the narrow
  disc-only Jensen-route transfer. No project Jensen imports, Mathlib only.

Proved here, all sorry-free, no axiom:
- log_sub_log_le_of_le, abs_log_sub_log_le_of_lower, log-Lipschitz helpers.
- divisor_eq_zero_of_ne_zero, analytic divisor at nonzero points.
- jensen_gap_of_divisor_pos, Jensen counting gap for divisor at interior point.
- rouche_nonvanishing_of_uniform, sup-norm zero-free preservation.
- hurwitz_zero_transfer, uniform limit with interior divisor forces zeros.
- door1_nonreal_zero_forced, disc avoiding reals forces nonreal zero.
-/

namespace RoucheCount

theorem log_sub_log_le_of_le {t τ : ℝ} (hτ : 0 < τ) (h : τ ≤ t) :
    Real.log t - Real.log τ ≤ (t - τ) / τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ h
  rw [← Real.log_div ht.ne' hτ.ne']
  have hpos : 0 < t / τ := div_pos ht hτ
  have h1 := Real.log_le_sub_one_of_pos hpos
  have hτn : τ ≠ 0 := ne_of_gt hτ
  have e : t / τ - 1 = (t - τ) / τ := by field_simp
  linarith

theorem abs_log_sub_log_le_of_lower {m t τ : ℝ} (hm : 0 < m)
    (ht : m ≤ t) (hτ : m ≤ τ) :
    |Real.log t - Real.log τ| ≤ |t - τ| / m := by
  have ht0 : 0 < t := lt_of_lt_of_le hm ht
  have hτ0 : 0 < τ := lt_of_lt_of_le hm hτ
  have hmin : m ≤ min t τ := le_min ht hτ
  have hlog : |Real.log t - Real.log τ| ≤ |t - τ| / min t τ := by
    rcases le_total τ t with h | h
    · have hlg : Real.log τ ≤ Real.log t := Real.log_le_log hτ0 h
      rw [min_eq_right h, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      exact log_sub_log_le_of_le hτ0 h
    · have hlg : Real.log t ≤ Real.log τ := Real.log_le_log ht0 h
      rw [min_eq_left h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        neg_sub, neg_sub]
      exact log_sub_log_le_of_le ht0 h
  calc |Real.log t - Real.log τ| ≤ |t - τ| / min t τ := hlog
    _ ≤ |t - τ| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hmin

theorem divisor_eq_zero_of_ne_zero {c : ℂ} {R : ℝ} {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    {u : ℂ} (hu : u ∈ Metric.closedBall c R) (hGu : G u ≠ 0) :
    MeromorphicOn.divisor G (Metric.closedBall c R) u = 0 := by
  have hord : analyticOrderAt G u = 0 :=
    (hG u hu).analyticOrderAt_eq_zero.mpr hGu
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hG hu, hord]
  simp

theorem jensen_gap_of_divisor_pos {c : ℂ} {R : ℝ} {G : ℂ → ℂ}
    (hR : 0 < R)
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    (hGc : G c ≠ 0)
    {w : ℂ} (hw : w ∈ Metric.ball c R) (hwc : w ≠ c)
    (hdiv : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w) :
    Real.log ‖G c‖ + Real.log (R / ‖c - w‖) ≤
      Real.circleAverage (fun z => Real.log ‖G z‖) c R := by
  have hRabs : |R| = R := abs_of_pos hR
  have hRne : R ≠ 0 := ne_of_gt hR
  have hGabs : AnalyticOnNhd ℂ G (Metric.closedBall c |R|) := by rwa [hRabs]
  have hdivAbs : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c |R|) w := by
    rwa [hRabs]
  have hJen := AnalyticOnNhd.circleAverage_log_norm hRne hGabs hGc
  have hcw_pos : 0 < ‖c - w‖ :=
    norm_pos_iff.mpr (sub_ne_zero_of_ne (Ne.symm hwc))
  have hcw_lt : ‖c - w‖ < R := by
    have hmem := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hmem
    have hrev : ‖w - c‖ = ‖c - w‖ := norm_sub_rev w c
    linarith
  have hlog_pos : 0 < Real.log (R / ‖c - w‖) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hcw_pos]
    simpa using hcw_lt
  have heq_log : Real.log (R / ‖c - w‖) = Real.log (R * ‖c - w‖⁻¹) := by
    rw [div_eq_mul_inv]
  have hDfin : (MeromorphicOn.divisor G (Metric.closedBall c |R|)).support.Finite :=
    (MeromorphicOn.divisor G (Metric.closedBall c |R|)).finiteSupport
      (isCompact_closedBall c |R|)
  have hsub : Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)) ⊆ ↑(hDfin.toFinset) := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    rw [Function.mem_support] at hu ⊢
    intro hDu
    apply hu
    simp [hDu]
  have hEq : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹))
      = ∑ u ∈ hDfin.toFinset, ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹) :=
    finsum_eq_sum_of_support_subset _ hsub
  have hwSupp : w ∈ (MeromorphicOn.divisor G (Metric.closedBall c |R|)).support := by
    rw [Function.mem_support]
    intro h0
    have hle := hdivAbs
    rw [h0] at hle
    norm_num at hle
  have hwmem : w ∈ hDfin.toFinset := hDfin.mem_toFinset.mpr hwSupp
  have hnn : ∀ u ∈ hDfin.toFinset,
      0 ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    have huSupp : u ∈ (MeromorphicOn.divisor G (Metric.closedBall c |R|)).support :=
      hDfin.mem_toFinset.mp hu
    have huCB : u ∈ Metric.closedBall c |R| :=
      (MeromorphicOn.divisor G (Metric.closedBall c |R|)).supportWithinDomain huSupp
    by_cases huc : u = c
    · have hDu : MeromorphicOn.divisor G (Metric.closedBall c |R|) u = 0 := by
        rw [huc]
        have hcCB : c ∈ Metric.closedBall c |R| := by
          rw [Metric.mem_closedBall, dist_self]
          exact abs_nonneg R
        exact divisor_eq_zero_of_ne_zero hGabs hcCB hGc
      rw [hDu]
      simp
    · have hDnn : (0 : ℝ) ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hGabs u
      have hnorm_pos : 0 < ‖c - u‖ :=
        norm_pos_iff.mpr (sub_ne_zero_of_ne (Ne.symm huc))
      have hnorm_le : ‖c - u‖ ≤ R := by
        have hmem := Metric.mem_closedBall.mp (hRabs ▸ huCB)
        rw [dist_eq_norm] at hmem
        have hrev : ‖u - c‖ = ‖c - u‖ := norm_sub_rev u c
        linarith
      have h1 : (1 : ℝ) ≤ R / ‖c - u‖ := by
        rw [le_div_iff₀ hnorm_pos]
        simpa using hnorm_le
      have hlog : 0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
        have heq : R * ‖c - u‖⁻¹ = R / ‖c - u‖ := by rw [div_eq_mul_inv]
        rw [heq]
        exact Real.log_nonneg h1
      exact mul_nonneg hDnn hlog
  have hwTerm : Real.log (R / ‖c - w‖)
      ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) w : ℤ) : ℝ) *
        Real.log (R * ‖c - w‖⁻¹) := by
    have hD1 : (1 : ℝ) ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) w : ℤ) : ℝ) := by
      exact_mod_cast hdivAbs
    have hlog_nn : 0 ≤ Real.log (R * ‖c - w‖⁻¹) := by
      have heq : R * ‖c - w‖⁻¹ = R / ‖c - w‖ := by rw [div_eq_mul_inv]
      rw [heq]
      exact le_of_lt hlog_pos
    rw [heq_log]
    calc Real.log (R * ‖c - w‖⁻¹) = 1 * Real.log (R * ‖c - w‖⁻¹) := by rw [one_mul]
      _ ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) w : ℤ) : ℝ) *
          Real.log (R * ‖c - w‖⁻¹) :=
        mul_le_mul_of_nonneg_right hD1 hlog_nn
  have hsum_ge : Real.log (R / ‖c - w‖)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
        Real.log (R * ‖c - u‖⁻¹) := by
    rw [hEq]
    calc Real.log (R / ‖c - w‖)
        ≤ ((MeromorphicOn.divisor G (Metric.closedBall c |R|) w : ℤ) : ℝ) *
          Real.log (R * ‖c - w‖⁻¹) := hwTerm
      _ ≤ ∑ u ∈ hDfin.toFinset, ((MeromorphicOn.divisor G (Metric.closedBall c |R|) u : ℤ) : ℝ) *
          Real.log (R * ‖c - u‖⁻¹) := Finset.single_le_sum hnn hwmem
  linarith [hJen, hsum_ge]

theorem rouche_nonvanishing_of_uniform {c : ℂ} {R : ℝ}
    {F G : ℂ → ℂ}
    (_hGne : ∀ z ∈ Metric.closedBall c R, G z ≠ 0)
    (hlt : ∀ z ∈ Metric.closedBall c R, ‖F z - G z‖ < ‖G z‖) :
    ∀ z ∈ Metric.closedBall c R, F z ≠ 0 := by
  intro z hz hFz
  have h1 := hlt z hz
  rw [hFz] at h1
  simp at h1

theorem hurwitz_zero_transfer {c : ℂ} {R : ℝ} (hR : 0 < R)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (Metric.closedBall c R))
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    (hGc : G c ≠ 0)
    (hGsph : ∀ z ∈ Metric.sphere c R, G z ≠ 0)
    {w : ℂ} (hw : w ∈ Metric.ball c R) (hwc : w ≠ c)
    (hdiv : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w)
    (hConv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ Metric.closedBall c R,
      ‖F n z - G z‖ < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ u ∈ Metric.closedBall c R, F n u = 0 := by
  have hRabs : |R| = R := abs_of_pos hR
  have hgap := jensen_gap_of_divisor_pos hR hG hGc hw hwc hdiv
  have hcw_pos : 0 < ‖c - w‖ :=
    norm_pos_iff.mpr (sub_ne_zero_of_ne (Ne.symm hwc))
  have hcw_lt : ‖c - w‖ < R := by
    have hmem := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hmem
    have hrev : ‖w - c‖ = ‖c - w‖ := norm_sub_rev w c
    linarith
  have hgapPos : 0 < Real.log (R / ‖c - w‖) :=
    Real.log_pos (by rw [lt_div_iff₀ hcw_pos]; simpa using hcw_lt)
  have hSphNe : (Metric.sphere c R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hGcontSph : ContinuousOn G (Metric.sphere c R) :=
    (AnalyticOnNhd.continuousOn hG).mono Metric.sphere_subset_closedBall
  have hNormCont : ContinuousOn (fun z => ‖G z‖) (Metric.sphere c R) :=
    continuous_norm.comp_continuousOn hGcontSph
  obtain ⟨m0, hm0mem, hm0min⟩ :=
    (isCompact_sphere c R).exists_isMinOn hSphNe hNormCont
  have hmpos : 0 < ‖G m0‖ :=
    norm_pos_iff.mpr (hGsph m0 hm0mem)
  have hmin : ∀ y ∈ Metric.sphere c R, ‖G m0‖ ≤ ‖G y‖ :=
    fun y hy => hm0min hy
  have hmcpos : 0 < ‖G c‖ := norm_pos_iff.mpr hGc
  have hcCB : c ∈ Metric.closedBall c R :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hR.le)
  set a0 : ℝ := min ‖G m0‖ ‖G c‖ with ha0def
  set g0 : ℝ := min (Real.log (R / ‖c - w‖)) 1 with hg0def
  have ha0pos : 0 < a0 := lt_min hmpos hmcpos
  have hg0pos : 0 < g0 := lt_min hgapPos one_pos
  set eps : ℝ := a0 * g0 / 8 with hepsdef
  have hepspos : 0 < eps := div_pos (mul_pos ha0pos hg0pos) (by norm_num)
  obtain ⟨N, hN⟩ := hConv eps hepspos
  refine ⟨N, fun n hn => ?_⟩
  have hUnif : ∀ z ∈ Metric.closedBall c R, ‖F n z - G z‖ < eps :=
    fun z hz => hN n hn z hz
  have hUnifSph : ∀ z ∈ Metric.sphere c R, ‖F n z - G z‖ < eps :=
    fun z hz => hUnif z (Metric.sphere_subset_closedBall hz)
  have hCen : ‖F n c - G c‖ < eps := hUnif c hcCB
  have ha0m : a0 ≤ ‖G m0‖ := min_le_left _ _
  have ha0mc : a0 ≤ ‖G c‖ := min_le_right _ _
  have hg0g : g0 ≤ Real.log (R / ‖c - w‖) := min_le_left _ _
  have ha0nn : 0 ≤ a0 := le_of_lt ha0pos
  have hg0nn : 0 ≤ g0 := le_of_lt hg0pos
  have heps_le_m : eps ≤ ‖G m0‖ / 2 := by
    have h1 : a0 * g0 ≤ ‖G m0‖ * 1 :=
      mul_le_mul ha0m (min_le_right _ _) hg0nn (le_of_lt hmpos)
    linarith [hepsdef]
  have heps_le_mc : eps ≤ ‖G c‖ / 2 := by
    have h1 : a0 * g0 ≤ ‖G c‖ * 1 :=
      mul_le_mul ha0mc (min_le_right _ _) hg0nn (le_of_lt hmcpos)
    linarith [hepsdef]
  have hB1 : eps / (‖G m0‖ / 2) ≤ Real.log (R / ‖c - w‖) / 4 := by
    have hpos2 : 0 < ‖G m0‖ / 2 := by linarith
    rw [div_le_iff₀ hpos2]
    have hprod : a0 * g0 ≤ ‖G m0‖ * Real.log (R / ‖c - w‖) :=
      mul_le_mul ha0m hg0g hg0nn (le_of_lt hmpos)
    linarith [hprod, hepsdef]
  have hB2 : eps / (‖G c‖ / 2) ≤ Real.log (R / ‖c - w‖) / 4 := by
    have hposC : 0 < ‖G c‖ / 2 := by linarith
    rw [div_le_iff₀ hposC]
    have hprod : a0 * g0 ≤ ‖G c‖ * Real.log (R / ‖c - w‖) :=
      mul_le_mul ha0mc hg0g hg0nn (le_of_lt hmcpos)
    linarith [hprod, hepsdef]
  by_contra hcon
  push_neg at hcon
  have hCBLEq : Metric.closedBall c |R| = Metric.closedBall c R := by rw [hRabs]
  have hFnAbs : AnalyticOnNhd ℂ (F n) (Metric.closedBall c |R|) := by
    rw [hCBLEq]; exact hF n
  have hFnFree : ∀ u ∈ Metric.closedBall c |R|, F n u ≠ 0 := by
    intro u hu
    exact hcon u (hCBLEq ▸ hu)
  have hAvgFn := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hFnAbs hFnFree
  have hSphEq : Metric.sphere c |R| = Metric.sphere c R := by rw [hRabs]
  have hFnSph : AnalyticOnNhd ℂ (F n) (Metric.sphere c |R|) := by
    rw [hSphEq]
    exact AnalyticOnNhd.mono (hF n) Metric.sphere_subset_closedBall
  have hGSph : AnalyticOnNhd ℂ G (Metric.sphere c |R|) := by
    rw [hSphEq]
    exact AnalyticOnNhd.mono hG Metric.sphere_subset_closedBall
  have hIntFn : CircleIntegrable (fun x => Real.log ‖F n x‖) c R :=
    MeromorphicOn.circleIntegrable_log_norm
      (AnalyticOnNhd.meromorphicOn hFnSph)
  have hIntG : CircleIntegrable (fun x => Real.log ‖G x‖) c R :=
    MeromorphicOn.circleIntegrable_log_norm
      (AnalyticOnNhd.meromorphicOn hGSph)
  have hIntH2 : CircleIntegrable (fun z => Real.log ‖G z‖ - Real.log ‖F n z‖) c R :=
    CircleIntegrable.sub hIntG hIntFn
  have hAvgH2 : Real.circleAverage (fun z => Real.log ‖G z‖ - Real.log ‖F n z‖) c R
      = Real.circleAverage (fun z => Real.log ‖G z‖) c R -
        Real.circleAverage (fun z => Real.log ‖F n z‖) c R :=
    Real.circleAverage_fun_sub hIntG hIntFn
  have hAbsSph : ∀ z ∈ Metric.sphere c R,
      |Real.log ‖F n z‖ - Real.log ‖G z‖| ≤ eps / (‖G m0‖ / 2) := by
    intro z hz
    have hGz : ‖G m0‖ / 2 ≤ ‖G z‖ := by linarith [hmin z hz]
    have hFz : ‖G m0‖ / 2 ≤ ‖F n z‖ := by
      have h1 := hUnifSph z hz
      have h2 := hmin z hz
      have h3 : ‖G z‖ - ‖F n z‖ ≤ ‖F n z - G z‖ := by
        calc ‖G z‖ - ‖F n z‖ ≤ ‖G z - F n z‖ := norm_sub_norm_le _ _
          _ = ‖F n z - G z‖ := norm_sub_rev _ _
      linarith [heps_le_m]
    have hpos2 : 0 < ‖G m0‖ / 2 := by linarith
    have hLip := abs_log_sub_log_le_of_lower hpos2 hFz hGz
    have hNorm : |‖F n z‖ - ‖G z‖| ≤ eps := by
      calc |‖F n z‖ - ‖G z‖| ≤ ‖F n z - G z‖ := abs_norm_sub_norm_le _ _
        _ ≤ eps := le_of_lt (hUnifSph z hz)
    calc |Real.log ‖F n z‖ - Real.log ‖G z‖|
        ≤ |‖F n z‖ - ‖G z‖| / (‖G m0‖ / 2) := hLip
      _ ≤ eps / (‖G m0‖ / 2) :=
          div_le_div_of_nonneg_right hNorm (le_of_lt hpos2)
  have hUp2 : Real.circleAverage (fun z => Real.log ‖G z‖ - Real.log ‖F n z‖) c R
      ≤ eps / (‖G m0‖ / 2) := by
    apply Real.circleAverage_mono_on_of_le_circle hIntH2
    intro x hx
    have hxR : x ∈ Metric.sphere c R := hRabs ▸ hx
    have h0 := hAbsSph x hxR
    rw [abs_sub_comm] at h0
    exact le_trans (le_abs_self _) h0
  have hAvgBd2 : Real.circleAverage (fun z => Real.log ‖G z‖) c R -
      Real.circleAverage (fun z => Real.log ‖F n z‖) c R ≤ eps / (‖G m0‖ / 2) := by
    rw [← hAvgH2]; exact hUp2
  have hFc_ge : ‖G c‖ / 2 ≤ ‖F n c‖ := by
    have h3 : ‖G c‖ - ‖F n c‖ ≤ ‖F n c - G c‖ := by
      calc ‖G c‖ - ‖F n c‖ ≤ ‖G c - F n c‖ := norm_sub_norm_le _ _
        _ = ‖F n c - G c‖ := norm_sub_rev _ _
    linarith [heps_le_mc]
  have hGc_ge : ‖G c‖ / 2 ≤ ‖G c‖ := by linarith
  have hposC : 0 < ‖G c‖ / 2 := by linarith
  have hCenAbs : |Real.log ‖F n c‖ - Real.log ‖G c‖| ≤ eps / (‖G c‖ / 2) := by
    have hLip := abs_log_sub_log_le_of_lower hposC hFc_ge hGc_ge
    have hNorm : |‖F n c‖ - ‖G c‖| ≤ eps := by
      calc |‖F n c‖ - ‖G c‖| ≤ ‖F n c - G c‖ := abs_norm_sub_norm_le _ _
        _ ≤ eps := le_of_lt hCen
    calc |Real.log ‖F n c‖ - Real.log ‖G c‖|
        ≤ |‖F n c‖ - ‖G c‖| / (‖G c‖ / 2) := hLip
      _ ≤ eps / (‖G c‖ / 2) :=
          div_le_div_of_nonneg_right hNorm (le_of_lt hposC)
  have hCen1 : Real.log ‖F n c‖ - Real.log ‖G c‖ ≤ eps / (‖G c‖ / 2) :=
    le_trans (le_abs_self _) hCenAbs
  linarith [hgap, hAvgFn, hAvgBd2, hCen1, hB1, hB2, hgapPos]

theorem door1_nonreal_zero_forced {c : ℂ} {R : ℝ} (hR0 : 0 < R)
    (hRim : R < |c.im|)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (Metric.closedBall c R))
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    (hGc : G c ≠ 0)
    (hGsph : ∀ z ∈ Metric.sphere c R, G z ≠ 0)
    {w : ℂ} (hw : w ∈ Metric.ball c R) (hwc : w ≠ c)
    (hdiv : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w)
    (hConv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ Metric.closedBall c R,
      ‖F n z - G z‖ < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ u ∈ Metric.closedBall c R, (F n u = 0 ∧ u.im ≠ 0) := by
  obtain ⟨N, hN⟩ := hurwitz_zero_transfer hR0 hF hG hGc hGsph hw hwc hdiv hConv
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨u, huCB, hFu⟩ := hN n hn
  refine ⟨u, huCB, hFu, ?_⟩
  intro him
  have hdist : dist u c ≤ R := Metric.mem_closedBall.mp huCB
  rw [dist_eq_norm] at hdist
  have him_le : |(u - c).im| ≤ ‖u - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, him] at him_le
  have hzero : |(0 : ℝ) - c.im| = |c.im| := by rw [zero_sub, abs_neg]
  rw [hzero] at him_le
  linarith

end RoucheCount

/-! ## R02 PILOT end-to-end closure — first fully-closed cell template (conditional, honest)

Feasibility verdict (computed from committed constants, see final report):
outer tier budget `0.002 + 0.05 * 1.26 = 0.065` versus center product
`22 * (1/2) * Agam * Azeta` with best committed `Agam = 1/10000000`
gives `1.1e-6 * Azeta`; closing needs `Azeta >= 59090`, while true `|zeta| = O(1)`.
Deriv tier needs `M <= 0.05` versus committed `67200` (conditional on `<=10`)
and `6800640` (unconditional from `<=1012`). Hence unconditional closure is
infeasible with committed constants. What is proved below is the closest
closable statement: the R02 H-leaf conditional on three explicit numeric
premises (`0.006 <= ||gamma||`, `1 <= ||zeta||`, `||deriv|| <= 0.05`) with the
numeric product check discharged by `norm_num`. Poly `22` and pi `1/2` are
closed hypothesis-free in-file (distinct names, no new imports, no cycle).
All results use only `Mathlib` plus `rh_certificate_infra` and this file's
own `DerivCauchyBridge` factorisation; `interval_arith` and
`riemann_hypothesis_newsection` are read-only and never imported.
-/

namespace R02Pilot

/-- R02 s-plane center `s = 1/2 + I * R02.center`. -/
noncomputable def sCenter : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center

/-- R02 center coordinates. -/
theorem center_eq :
    CentralCoverAssembly.R02.center =
      (((-6.75 : ℝ) : ℂ)) + Complex.I * (((0.105 : ℝ) : ℂ)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R02_x0, CentralCoverAssembly.R02_x1,
      CentralCoverAssembly.R02_y0, CentralCoverAssembly.R02_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R02_x0, CentralCoverAssembly.R02_x1,
      CentralCoverAssembly.R02_y0, CentralCoverAssembly.R02_y1]
    simp
    norm_num

/-- `Re sCenter = 0.395`. -/
theorem sCenter_re : sCenter.re = 0.395 := by
  unfold sCenter
  rw [center_eq]
  simp
  norm_num

/-- `Im sCenter = -6.75`. -/
theorem sCenter_im : sCenter.im = -6.75 := by
  unfold sCenter
  rw [center_eq]
  simp

/-- `(sCenter - 1).re = -0.605`. -/
theorem sCenter_sub_one_re : (sCenter - 1).re = -0.605 := by
  simp only [Complex.sub_re, Complex.one_re, sCenter_re]
  norm_num

/-- `(sCenter - 1).im = -6.75`. -/
theorem sCenter_sub_one_im : (sCenter - 1).im = -6.75 := by
  simp only [Complex.sub_im, Complex.one_im, sCenter_im]
  norm_num

/-- `||sCenter|| >= 6.7`. -/
theorem norm_sCenter_ge : (6.7 : ℝ) ≤ ‖sCenter‖ := by
  have hsq : (6.7 : ℝ) ^ 2 ≤ ‖sCenter‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sCenter_re, sCenter_im]
    norm_num
  calc (6.7 : ℝ) = Real.sqrt ((6.7 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sCenter‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖sCenter‖ := Real.sqrt_sq (norm_nonneg _)

/-- `||sCenter - 1|| >= 6.7`. -/
theorem norm_sCenter_sub_one_ge : (6.7 : ℝ) ≤ ‖sCenter - 1‖ := by
  have hsq : (6.7 : ℝ) ^ 2 ≤ ‖sCenter - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sCenter_sub_one_re, sCenter_sub_one_im]
    norm_num
  calc (6.7 : ℝ) = Real.sqrt ((6.7 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sCenter - 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖sCenter - 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Hypothesis-free poly lower `22 <= ||poly||` at R02 s-center. -/
theorem poly_lower : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sCenter‖ := by
  unfold DerivCauchyBridge.polyOf
  have h1 : (6.7 : ℝ) ≤ ‖sCenter‖ := norm_sCenter_ge
  have h2 : (6.7 : ℝ) ≤ ‖sCenter - 1‖ := norm_sCenter_sub_one_ge
  have hprod : (6.7 : ℝ) * 6.7 ≤ ‖sCenter‖ * ‖sCenter - 1‖ :=
    mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  have hnorm : ‖sCenter * (sCenter - 1) / 2‖ = ‖sCenter‖ * ‖sCenter - 1‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_two]
  rw [hnorm]
  have hcalc : (22 : ℝ) ≤ (6.7 : ℝ) * 6.7 / 2 := by norm_num
  linarith

/-- `pi ^ (1/4) <= 2`. -/
theorem pi_rpow_quarter_le_two : Real.pi ^ ((1 / 4 : ℝ)) ≤ 2 := by
  have e : (Real.pi ^ ((1 / 4 : ℝ))) ^ ((4 : ℕ)) = Real.pi := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    have hexp : ((1 / 4 : ℝ)) * ((((4 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [hexp, Real.rpow_one]
  have hle : Real.pi ≤ (2 : ℝ) ^ ((4 : ℕ)) := by
    have h16 : (2 : ℝ) ^ ((4 : ℕ)) = 16 := by norm_num
    rw [h16]
    linarith [Real.pi_le_four]
  have h4 : (Real.pi ^ ((1 / 4 : ℝ))) ^ ((4 : ℕ)) ≤ (2 : ℝ) ^ ((4 : ℕ)) := by
    rw [e]
    exact hle
  have e1 : (Real.pi ^ ((1 / 4 : ℝ))) ^ ((4 : ℕ))
      = ((Real.pi ^ ((1 / 4 : ℝ))) ^ ((2 : ℕ))) ^ ((2 : ℕ)) := by ring
  have e2 : (2 : ℝ) ^ ((4 : ℕ)) = (((2 : ℝ)) ^ ((2 : ℕ))) ^ ((2 : ℕ)) := by ring
  rw [e1, e2] at h4
  have hsq : (Real.pi ^ ((1 / 4 : ℝ))) ^ ((2 : ℕ)) ≤ (2 : ℝ) ^ ((2 : ℕ)) :=
    (abs_le_of_sq_le_sq' h4 (by norm_num)).2
  exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2

/-- `1/2 <= pi ^ (-1/4)`. -/
theorem pi_rpow_neg_quarter_ge_half : (1 / 2 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
  have hrw : Real.pi ^ (-(1 / 4 : ℝ)) = 1 / (Real.pi ^ ((1 / 4 : ℝ))) := by
    rw [Real.rpow_neg (le_of_lt Real.pi_pos)]
    exact (one_div _).symm
  rw [hrw]
  exact one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos Real.pi_pos _) pi_rpow_quarter_le_two

/-- Hypothesis-free pi lower `1/2 <= ||pi||` at R02 s-center. -/
theorem pi_lower : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf sCenter‖ := by
  have hnorm : ‖DerivCauchyBridge.piOf sCenter‖ = Real.pi ^ (-(sCenter.re) / 2) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-(sCenter / 2))
    unfold DerivCauchyBridge.piOf
    rw [h]
    congr 1
    rw [Complex.neg_re, Complex.div_ofNat_re]
    ring
  rw [hnorm, sCenter_re]
  have hexp : (-(1 / 4 : ℝ)) ≤ -(0.395 : ℝ) / 2 := by norm_num
  calc (1 / 2 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := pi_rpow_neg_quarter_ge_half
    _ ≤ Real.pi ^ (-(0.395 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp

/-- Outer-tier budget value. -/
theorem budget_eq : (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

/-- Feasibility gap: committed product with `Agam = 1/1e7`, `Azeta = 1/26`
is far below budget. -/
theorem committed_product_lt :
    22 * (1 / 2) * (1 / 10000000) * (1 / 26) < (0.002 : ℝ) + 0.05 * 1.26 := by
  norm_num

/-- Feasibility threshold: with committed `Agam`, closing needs `Azeta >= 59090`. -/
theorem required_Azeta_of_committed_Gamma {Azeta : ℝ}
    (h : (0.002 : ℝ) + 0.05 * 1.26 ≤ 22 * (1 / 2) * (1 / 10000000) * Azeta) :
    (59090 : ℝ) ≤ Azeta := by
  have hb : (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num
  rw [hb] at h
  have hcoeff : (22 : ℝ) * (1 / 2) * (1 / 10000000) = 11 / 10000000 := by norm_num
  rw [hcoeff] at h
  have hpos : (0 : ℝ) < 11 / 10000000 := by norm_num
  have hcomm : (11 : ℝ) / 10000000 * Azeta = Azeta * (11 / 10000000) := by ring
  have h2 : (0.065 : ℝ) ≤ Azeta * (11 / 10000000) := by
    rw [← hcomm]
    exact h
  have hdiv : (0.065 : ℝ) / (11 / 10000000) ≤ Azeta :=
    (div_le_iff₀ hpos).mpr h2
  have hnum : (59090 : ℝ) ≤ (0.065 : ℝ) / (11 / 10000000) := by
    rw [le_div_iff₀ hpos]
    norm_num
  exact le_trans hnum hdiv

/-- Deriv gap, conditional route: tier `0.05` versus `67200`. -/
theorem deriv_gap_conditional : (0.05 : ℝ) < 67200 := by norm_num

/-- Deriv gap, unconditional route: tier `0.05` versus `6800640`. -/
theorem deriv_gap_unconditional : (0.05 : ℝ) < 6800640 := by norm_num

/-- Generic four-factor center bridge in-file (no new imports). -/
theorem center_bound_of_components (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sCenter‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sCenter‖)
    (hgam : Agam ≤ ‖DerivCauchyBridge.gammaOf sCenter‖)
    (hzeta : Azeta ≤ ‖zeta sCenter‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  have harg2 : (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center = sCenter := rfl
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts CentralCoverAssembly.R02.center
  rw [harg2] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted CentralCoverAssembly.R02.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * CentralCoverAssembly.R02.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt CentralCoverAssembly.R02_radius_lt) (by norm_num)
  linarith

/-- Numeric product check for the chosen conditional thresholds. -/
theorem threshold_check : (0.002 : ℝ) + 0.05 * 1.26 ≤ 22 * (1 / 2) * 0.006 * 1 := by
  norm_num

#print axioms R02Pilot.poly_lower
#print axioms R02Pilot.pi_lower
#print axioms R02Pilot.center_bound_of_components

end R02Pilot

/-- R02 pilot conditional closure: three explicit numeric premises discharge
the H-leaf of `inner_nonvanishing_of_fenced_grid_fine` at R02's grid cell.
This turns all future factor work into plug-and-play: prove the three bounds
and the pilot cell closes. -/
theorem R02_closed_of_factorBounds
    (hGam : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (1 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖)
    (hDeriv : ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hpoly : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf R02Pilot.sCenter‖ :=
    R02Pilot.poly_lower
  have hpi : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf R02Pilot.sCenter‖ :=
    R02Pilot.pi_lower
  have hcenter : (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ :=
    R02Pilot.center_bound_of_components 22 (1 / 2) 0.006 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hpoly hpi hGam hZeta R02Pilot.threshold_check
  have hleaf : CentralCoverAssembly.R02_leaf_obligations := ⟨hcenter, hDeriv⟩
  exact CentralCoverAssembly.R02_H_instance hleaf c hc_mem hc_eq

#print axioms R02_closed_of_factorBounds

/-! ## S2a: zero => divisor >= 1 (finite-order packaging, sorry-free)

GREP-first record (2026-09-03, verified by reading, documented in-file per HARD RULES):
- Mathlib complex Rouche / Hurwitz / winding number / argument principle / count-zeros:
  ABSENT. `Mathlib/Analysis/Complex/LocallyUniformLimit.lean:136` gives holomorphic limit
  only (`TendstoLocallyUniformlyOn.differentiableOn`, reused by others, not needed here);
  `Mathlib/Analysis/Analytic/IsolatedZeros.lean:125` gives isolated zeros only;
  `Mathlib/Analysis/Complex/JensenFormula.lean:308,376,390` gives Jensen equality plus a
  zero-count UPPER bound only, no Rouche equality of counts. No `windingNumber`,
  no `argumentPrinciple`, no `countZeros` anywhere in Mathlib (same verdict as the
  `RoucheCount` header above, which was built from scratch from Jensen + sup-norm).
- Mathlib HAS isolated-zero / finite-order material, REUSED here (not recreated):
  `AnalyticAt.analyticOrderAt_eq_zero/ne_zero` + `analyticOrderAt_eq_zero`
  (`Mathlib/Analysis/Analytic/Order.lean:120,129,133,137`), the clopen/connected
  finiteness transfer `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected`
  (`Order.lean:627`, via `isClopen_setOfPred_analyticOrderAt_eq_top` at :580 and
  `exists_analyticOrderAt_ne_top_iff_forall` at :617), `Metric.isPreconnected_closedBall`
  (`Mathlib/Analysis/Normed/Module/Connected.lean:183`, in `namespace Metric`),
  divisor evaluation `MeromorphicOn.AnalyticOnNhd.divisor_apply`
  (`Mathlib/Analysis/Meromorphic/Divisor.lean:71`, full name with `MeromorphicOn.` prefix
  since it lives in `namespace MeromorphicOn`), `ENat.map` monotonicity
  (`ENat.monotone_map_iff` + `map_natCast_strictMono` at `Data/ENat/Basic.lean:596,607`,
  `map_eq_top_iff` at :590), and `WithTop.untop₀_le_untop₀` / `untop₀_one` / `untop₀_coe`
  (`Algebra/Order/WithTop/Untop0.lean:47,75,112`).

What is proved here (no `sorry`, no `admit`, no `axiom`, Mathlib only + this file's own
`RoucheCount`):
- `RoucheCount.divisor_ge_one_of_zero`: an interior zero of an analytic limit forces
  divisor `>= 1` at that point, provided the limit is nonzero somewhere on the same
  closed ball (here the disc center `c`, exactly `hurwitz_zero_transfer`'s `hGc`).
  Finite-order packaging: `G c ≠ 0` gives `orderAt c = 0 ≠ ⊤`; preconnectedness of the
  closed ball transfers `≠ ⊤` to `w`; `G w = 0` gives `orderAt w ≠ 0`; hence
  `1 ≤ orderAt w` as `ℕ∞`, monotonely mapped to `WithTop ℤ` and pushed through `untop₀`.
  This rules out the `⊤ ↦ 0` divisor collapse (locally-zero case) via the `hGc` witness.
- `RoucheCount.hurwitz_zero_transfer_of_zero` / `door1_nonreal_zero_forced_of_zero`:
  exact-signature wrappers around the existing `hurwitz_zero_transfer` /
  `door1_nonreal_zero_forced`, with the `hdiv : 1 ≤ divisor` hypothesis discharged by
  the lemma above and replaced by the directly usable `hGw : G w = 0`. This is the S2a
  link named in guide §18b.10: S2b (a later agent) can now feed a limit zero straight
  into polynomial-eval packaging + `hyperbolic_zeroFree_off_real` composition in the
  door-1 file, without touching divisor internals.
-/

namespace RoucheCount

theorem divisor_ge_one_of_zero {c : ℂ} {R : ℝ} {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    {w : ℂ} (hw : w ∈ Metric.closedBall c R)
    (hGc : G c ≠ 0) (hc : c ∈ Metric.closedBall c R)
    (hGw : G w = 0) :
    1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w := by
  have hGc_ord : analyticOrderAt G c ≠ ⊤ := by
    have h0 : analyticOrderAt G c = 0 :=
      (hG c hc).analyticOrderAt_eq_zero.mpr hGc
    rw [h0]
    simp
  have hord_top : analyticOrderAt G w ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hG
      Metric.isPreconnected_closedBall hc hw hGc_ord
  have hord_zero : analyticOrderAt G w ≠ 0 :=
    (hG w hw).analyticOrderAt_ne_zero.mpr hGw
  have hdiv_eq := MeromorphicOn.AnalyticOnNhd.divisor_apply hG hw
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hord_top
  have hk0 : k ≠ 0 := by
    intro h0
    apply hord_zero
    rw [← hk, h0]
    simp
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hord_eq : analyticOrderAt G w = (k : ℕ∞) := hk.symm
  have h1le_ord : (1 : ℕ∞) ≤ analyticOrderAt G w := by
    rw [hord_eq]
    exact_mod_cast hk1
  have hmono : Monotone (ENat.map ((↑) : ℕ → ℤ)) := by
    rw [ENat.monotone_map_iff]
    intro a b hab
    exact_mod_cast hab
  have h1le_map : (1 : WithTop ℤ) ≤ (analyticOrderAt G w).map ((↑) : ℕ → ℤ) := by
    have h := hmono h1le_ord
    simpa using h
  have hmap_ne_top : (analyticOrderAt G w).map ((↑) : ℕ → ℤ) ≠ ⊤ :=
    ENat.map_eq_top_iff.ne.mpr hord_top
  calc (1 : ℤ) = (1 : WithTop ℤ).untop₀ := by simp
    _ ≤ ((analyticOrderAt G w).map ((↑) : ℕ → ℤ)).untop₀ :=
        WithTop.untop₀_le_untop₀ hmap_ne_top h1le_map
    _ = MeromorphicOn.divisor G (Metric.closedBall c R) w := hdiv_eq.symm

theorem hurwitz_zero_transfer_of_zero {c : ℂ} {R : ℝ} (hR : 0 < R)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (Metric.closedBall c R))
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    (hGc : G c ≠ 0)
    (hGsph : ∀ z ∈ Metric.sphere c R, G z ≠ 0)
    {w : ℂ} (hw : w ∈ Metric.ball c R) (hwc : w ≠ c)
    (hGw : G w = 0)
    (hConv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ Metric.closedBall c R,
      ‖F n z - G z‖ < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ u ∈ Metric.closedBall c R, F n u = 0 := by
  have hc : c ∈ Metric.closedBall c R :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hR.le)
  have hwCB : w ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hw
  have hdiv : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w :=
    divisor_ge_one_of_zero hG hwCB hGc hc hGw
  exact hurwitz_zero_transfer hR hF hG hGc hGsph hw hwc hdiv hConv

theorem door1_nonreal_zero_forced_of_zero {c : ℂ} {R : ℝ} (hR0 : 0 < R)
    (hRim : R < |c.im|)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (Metric.closedBall c R))
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall c R))
    (hGc : G c ≠ 0)
    (hGsph : ∀ z ∈ Metric.sphere c R, G z ≠ 0)
    {w : ℂ} (hw : w ∈ Metric.ball c R) (hwc : w ≠ c)
    (hGw : G w = 0)
    (hConv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ Metric.closedBall c R,
      ‖F n z - G z‖ < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ u ∈ Metric.closedBall c R, (F n u = 0 ∧ u.im ≠ 0) := by
  have hc : c ∈ Metric.closedBall c R :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hR0.le)
  have hwCB : w ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hw
  have hdiv : 1 ≤ MeromorphicOn.divisor G (Metric.closedBall c R) w :=
    divisor_ge_one_of_zero hG hwCB hGc hc hGw
  exact door1_nonreal_zero_forced hR0 hRim hF hG hGc hGsph hw hwc hdiv hConv

end RoucheCount

#print axioms RoucheCount.divisor_ge_one_of_zero
#print axioms RoucheCount.hurwitz_zero_transfer_of_zero
#print axioms RoucheCount.door1_nonreal_zero_forced_of_zero

/-! ## AO door-3 closer wiring: R02 deriv bound with AH landed Gamma cap (0.097)

TASK (door-3 closer wiring): re-derive the R02 deriv bound with AH's landed cap.
Landed: `R02GammaDisc.gammaOf_upper_disc_R02` in `interval_arith.lean:32316`
(drop-in for `DerivCauchyBridge.gammaOf`; disc factor `40 -> 0.097`,
sphere sup `16800 -> 40.74`, deriv `67200 -> 162.96`, tier `~163`).

Grep-first record (2026-09-03, verified via `default.grep`, exact names):
* `R02_deriv_bound_of_zeta_upper|gammaOf_upper_disc_R02|gamma_upper_R02_disc` ->
  `central_cover_assembly.lean:6308,6347,6390,6403`,
  `interval_arith.lean:31762,32315,32316`,
  `zeta_rigorous.lean:4224`, `riemann_hypothesis_newsection.lean:797,820,854,870`.
* `R02_closed_of_factorBounds|threshold_check|required_Azeta|R02Pilot` ->
  `central_cover_assembly.lean:9425,9556,9605,9618`.
* `poly_upper_R02_disc|pi_upper_R02_disc|R02_s_of_sphere_re_im|norm_xiShifted_eq_parts|uniform_deriv_of_sphere_bound|R02_strip_of_mem|R02_sphere_mem_strip` ->
  `central_cover_assembly.lean:6041,6100,6139,6148,6190,6200,6236`.
* `R02_radius_lt|R02_x0|R02_strip_lo|R02_strip_hi|poly_lower|pi_lower|sCenter|center_eq` ->
  `central_cover_assembly.lean:1273,1281,1282,1297,9428,9432,9489,9532`.
* `gammaOf_upper_disc_R02|gamma_upper_disc_R02` in `interval_arith.lean:32105,32316`
  (4 hyps `re lo/hi + im lo/hi`, concl `<= 0.097`; old
  `DerivCauchyBridge.gamma_upper_R02_disc:6308` has 2 hyps, concl `<= 40`).
* `prod_four_ge_of_ge|TailProofEngine` -> `rh_certificate_infra.lean:157,195`,
  consumed at `central_cover_assembly.lean:9596`, `interval_arith.lean:112,139,1785`.

IMPORT CYCLE NOTE: `interval_arith.lean:4` imports `central_cover_assembly`,
so this file CANNOT import `interval_arith`. AH's landed
`R02GammaDisc.gammaOf_upper_disc_R02` is therefore wired as an EXPLICIT
premise `AO_gamma_upper_disc_R02_obligation` with the IDENTICAL statement
(`∀ s, 0.05 ≤ re → re ≤ 0.74 → -8.25 ≤ im → im ≤ -5.25 → ‖gammaOf s‖ ≤ 0.097`).
Downstream (in `interval_arith` or `riemann_hypothesis_newsection`) discharge
`hG` by `R02GammaDisc.gammaOf_upper_disc_R02`. No `sorry`/`admit`/`axiom`,
no hypothesis stand-ins beyond this named landed-obligation premise plus the
pre-existing `DerivCauchyBridge.R02_zeta_upper_obligation` (`‖ζ‖ ≤ 10`).
-/

namespace AO_R02DiscUpdate

/-- Gamma-upper obligation matching AH's landed
`R02GammaDisc.gammaOf_upper_disc_R02` (`interval_arith.lean:32316`) exactly:
identical hyps (re + im rect) and concl `≤ 0.097`.
Stated here (not imported) to avoid the `interval_arith -> central_cover_assembly`
import cycle; discharged downstream by the landed lemma. -/
def AO_gamma_upper_disc_R02_obligation : Prop :=
  ∀ s : ℂ, (0.05 : ℝ) ≤ s.re → s.re ≤ (0.74 : ℝ) →
    (-8.25 : ℝ) ≤ s.im → s.im ≤ (-5.25 : ℝ) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (0.097 : ℝ)

/-- Disc factor product: `42 * 1 * 0.097 * 10 = 40.74` (was `42*1*40*10=16800`). -/
theorem AO_sphere_sup_eq : (42 : ℝ) * 1 * 0.097 * 10 = 40.74 := by
  norm_num

/-- Cauchy `M`: `40.74 / 0.25 = 162.96` (was `16800/0.25=67200`; tier `~163`). -/
theorem AO_M_eq : (40.74 : ℝ) / 0.25 = 162.96 := by
  norm_num

/-- 412x improvement on the sphere sup (`40.74 < 16800`). -/
theorem AO_sphere_improvement : (40.74 : ℝ) < 16800 := by
  norm_num

/-- 412x improvement on the deriv bound (`162.96 < 67200`). -/
theorem AO_deriv_improvement : (162.96 : ℝ) < 67200 := by
  norm_num

/-- Ceil tier `163` covers the exact `162.96`. -/
theorem AO_M_le_163 : (162.96 : ℝ) ≤ 163 := by
  norm_num

/-- Updated conditional `xiShifted` upper on an R02 sphere point:
`‖ξ‖ ≤ 42*1*0.097*10 = 40.74` (mirrors
`DerivCauchyBridge.xiShifted_upper_of_zeta_upper_R02:6339`, same zeta premise
plus the landed gamma premise). -/
theorem AO_xiShifted_upper_of_zeta_upper_R02 {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ))
    (hG : AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 40.74 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    DerivCauchyBridge.R02_s_of_sphere_re_im hw hu
  have hpoly :=
    DerivCauchyBridge.poly_upper_R02_disc hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := DerivCauchyBridge.pi_upper_R02_disc hsre_lo
  have hgam : ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 0.097 :=
    hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta : ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 10 :=
    hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 * 0.097 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 * 0.097 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (42 : ℝ) * 1 * 0.097 * 10 = 40.74 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the sphere (agrees in the strip). -/
theorem AO_entire_upper_of_zeta_upper_R02 {w u : ℂ}
    (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ))
    (hG : AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 40.74 := by
  obtain ⟨hlo, hhi⟩ := DerivCauchyBridge.R02_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact AO_xiShifted_upper_of_zeta_upper_R02 hw hu hG hZ

/-- Uniform sup `40.74` on all R02 `0.25`-spheres (was `16800`). -/
theorem AO_R02_uniform_sphere_bound
    (hG : AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R02.mem w → ∀ z ∈ Metric.sphere w (0.25 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 40.74 := by
  intro w hw z hz
  exact AO_entire_upper_of_zeta_upper_R02 hw hz hG hZ

/-- R02 updated conditional derivative bound: uniform `‖deriv xiShifted‖ ≤ 162.96`
(`40.74 / 0.25`) modulo exactly `R02_zeta_upper_obligation` (zeta `≤ 10`) plus
the landed gamma obligation (`≤ 0.097`). Mirrors
`DerivCauchyBridge.R02_deriv_bound_of_zeta_upper:6390` (`16800/0.25=67200`). -/
theorem AO_R02_deriv_bound_of_zeta_upper
    (hG : AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (162.96 : ℝ) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R02 0.25 40.74
    (by norm_num) (fun w hw => DerivCauchyBridge.R02_strip_of_mem hw)
    (AO_R02_uniform_sphere_bound hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (40.74 : ℝ) / 0.25 = 162.96 := by norm_num
  rw [heq] at hle
  exact hle

/-- Ceil-tier corollary `M = 163` (integer tier for threshold arithmetic). -/
theorem AO_R02_deriv_bound_163_of_zeta_upper
    (hG : AO_gamma_upper_disc_R02_obligation)
    (hZ : DerivCauchyBridge.R02_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ) := by
  intro w hw
  have hle := AO_R02_deriv_bound_of_zeta_upper hG hZ w hw
  linarith

/-- Updated budget value with `M = 163`: `0.002 + 163 * 1.26 = 205.382`
(was `0.002 + 0.05 * 1.26 = 0.065`). -/
theorem AO_budget_163_eq : (0.002 : ℝ) + 163 * 1.26 = 205.382 := by
  norm_num

/-- Updated product value: `22 * (1/2) * 0.006 * 3112 = 205.392`. -/
theorem AO_product_163_eq : (22 : ℝ) * (1 / 2) * 0.006 * 3112 = 205.392 := by
  norm_num

/-- Updated numeric product check for the `M = 163` conditional thresholds:
`0.002 + 163 * 1.26 ≤ 22 * (1/2) * 0.006 * 3112`
(`205.382 ≤ 205.392`, margin `0.01`; mirrors `R02Pilot.threshold_check:9605`
`0.002+0.05*1.26 ≤ 22*(1/2)*0.006*1`). -/
theorem AO_threshold_check_163 :
    (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.006 * 3112 := by
  norm_num

/-- Updated feasibility threshold with `M = 163`, conditional `Agam = 0.006`:
closing needs `Azeta ≥ 3111` (floor; sufficient integer `3112` by
`AO_threshold_check_163`). Mirrors
`R02Pilot.required_Azeta_of_committed_Gamma:9556` shape with exact numbers. -/
theorem AO_required_Azeta_of_Agam_163 {Azeta : ℝ}
    (h : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.006 * Azeta) :
    (3111 : ℝ) ≤ Azeta := by
  have hb : (0.002 : ℝ) + 163 * 1.26 = 205.382 := by norm_num
  rw [hb] at h
  have hcoeff : (22 : ℝ) * (1 / 2) * 0.006 = 0.066 := by norm_num
  rw [hcoeff] at h
  have hpos : (0 : ℝ) < 0.066 := by norm_num
  have hcomm : (0.066 : ℝ) * Azeta = Azeta * 0.066 := by ring
  have h2 : (205.382 : ℝ) ≤ Azeta * 0.066 := by
    rw [← hcomm]
    exact h
  have hdiv : (205.382 : ℝ) / 0.066 ≤ Azeta :=
    (div_le_iff₀ hpos).mpr h2
  have hnum : (3111 : ℝ) ≤ (205.382 : ℝ) / 0.066 := by
    rw [le_div_iff₀ hpos]
    norm_num
  exact le_trans hnum hdiv

/-- Committed-product gap with `M = 163`: `22*(1/2)*(1/1e7)*(1/26) ≪ 205.382`
(mirrors `R02Pilot.committed_product_lt`). -/
theorem AO_committed_product_lt_163 :
    22 * (1 / 2) * (1 / 10000000) * (1 / 26) < (0.002 : ℝ) + 163 * 1.26 := by
  norm_num

/-- Updated feasibility threshold with `M = 163`, committed `Agam = 1/1e7`:
closing needs `Azeta ≥ 186710909` (floor of `205.382/(11/1e7) = 186710909.09…`;
mirrors `R02Pilot.required_Azeta_of_committed_Gamma` `59090` for `M = 0.05`). -/
theorem AO_required_Azeta_of_committed_Gamma_163 {Azeta : ℝ}
    (h : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * (1 / 10000000) * Azeta) :
    (186710909 : ℝ) ≤ Azeta := by
  have hb : (0.002 : ℝ) + 163 * 1.26 = 205.382 := by norm_num
  rw [hb] at h
  have hcoeff : (22 : ℝ) * (1 / 2) * (1 / 10000000) = 11 / 10000000 := by norm_num
  rw [hcoeff] at h
  have hpos : (0 : ℝ) < 11 / 10000000 := by norm_num
  have hcomm : (11 : ℝ) / 10000000 * Azeta = Azeta * (11 / 10000000) := by ring
  have h2 : (205.382 : ℝ) ≤ Azeta * (11 / 10000000) := by
    rw [← hcomm]
    exact h
  have hdiv : (205.382 : ℝ) / (11 / 10000000) ≤ Azeta :=
    (div_le_iff₀ hpos).mpr h2
  have hnum : (186710909 : ℝ) ≤ (205.382 : ℝ) / (11 / 10000000) := by
    rw [le_div_iff₀ hpos]
    norm_num
  exact le_trans hnum hdiv

/-- Updated center bound with `M = 163`: from `Agam ≥ 0.006`, `Azeta ≥ 3112`
gives `0.002 + 163 * radius ≤ ‖ξ(center)‖` (mirrors
`R02Pilot.center_bound_of_components:9582`, which fixes `M = 0.05`). -/
theorem AO_center_bound_163_of_components
    (hGam : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (3112 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖) :
    (0.002 : ℝ) + 163 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  have hpoly : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf R02Pilot.sCenter‖ :=
    R02Pilot.poly_lower
  have hpi : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf R02Pilot.sCenter‖ :=
    R02Pilot.pi_lower
  have harg2 : (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center =
      R02Pilot.sCenter := rfl
  have hdecomp :=
    DerivCauchyBridge.norm_xiShifted_eq_parts CentralCoverAssembly.R02.center
  rw [harg2] at hdecomp
  have hle : 22 * (1 / 2) * 0.006 * 3112 ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hGam hZeta
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbud : 163 * CentralCoverAssembly.R02.radius ≤ 163 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt CentralCoverAssembly.R02_radius_lt) (by norm_num)
  have hthresh : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.006 * 3112 :=
    AO_threshold_check_163
  linarith

/-- R02 updated conditional closure with `M = 163`: three explicit numeric
premises discharge the H-leaf shape of
`inner_nonvanishing_of_fenced_grid_fine` at R02's grid cell
`(-8,-5.5,0.01,0.2)` with `ε = 0.002`, `M = 163`.
Mirrors `R02_closed_of_factorBounds:9618`
(`Agam ≥ 0.006`, `Azeta ≥ 1`, `M ≤ 0.05`); the new `M` forces
`Azeta ≥ 3112` (sufficient by `AO_threshold_check_163`). -/
theorem AO_R02_closed_of_factorBounds_163
    (hGam : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (3112 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖)
    (hDeriv : ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ))
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hcenter : (0.002 : ℝ) + 163 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ :=
    AO_center_bound_163_of_components hGam hZeta
  subst hc_eq
  exact ⟨CentralCoverAssembly.R02, 0.002, 163, rfl, rfl, rfl, rfl,
    CentralCoverAssembly.R02_strip_lo, CentralCoverAssembly.R02_strip_hi,
    (by norm_num), hDeriv, hcenter⟩

/-! ### AO residual premise inventory (who owns what for the R02 H-leaf)

With the landed Gamma cap (`0.097`, `M = 162.96`, tier `163`):

* DERIV `M` (this agent, AO, CLOSED conditional):
  `AO_R02_deriv_bound_of_zeta_upper` / `AO_R02_deriv_bound_163_of_zeta_upper`:
  `‖deriv xiShifted‖ ≤ 162.96` (`≤ 163` ceil) on R02, conditional on
  (i) `DerivCauchyBridge.R02_zeta_upper_obligation` (`‖ζ‖ ≤ 10` on the disc
  `s`-rect `Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`) and
  (ii) `AO_gamma_upper_disc_R02_obligation` (`‖gammaOf‖ ≤ 0.097`, discharged
  downstream by landed `R02GammaDisc.gammaOf_upper_disc_R02`,
  `interval_arith.lean:32316`; true sup `~0.026`, within `3.7x`).
  Old tier `M = 67200` (`16800/0.25`); unconditional `M = 6800640`
  (`‖ζ‖ ≤ 1012` via identity theorem, `riemann_hypothesis_newsection.lean`)
  untouched.

* ZETA UPPER `‖ζ‖ ≤ 10` (sibling zeta-upper agent OWNS; NOT closed here):
  needs whole-line damped left cap `A ≤ 50.925` (`ZetaUpperR02ThreeLines`,
  `riemann_hypothesis_newsection.lean:1105-1116`); honestly proved crude window
  cap `1.2e9`, gap `~2.4e7x` purely in the cos/exp left-edge majorant.
  Needs Stirling-sharp left edge (true `A = O(10²)`); FE+Stirling+convexity
  material absent from Mathlib/repo. The `≤ 10` obligation (hence the `M ≈ 163`
  tier, NOT the `M ≈ 0.05` fencing tier) needs FE+Stirling+convexity, not the
  eta M-test (`r(M) ≈ 180·M^{-0.05}` needs `M ≥ 10^{31}` terms for `r ≤ 5`).

* AGAM `≥ 0.006` at `R02Pilot.sCenter` (`s = 0.395 - 6.75·I`) (sibling
  Gamma-lower agent OWNS; NOT closed here): committed hypothesis-free lower
  is `1/1e7` (`CellGammaUniform`); gap `60000x` (reflection + `1e-7`
  infeasible in principle, needs `‖sin‖ ≥ 3e9`).

* AZETA `≥ 3112` at `R02Pilot.sCenter` for the `M = 163` closure
  (`≥ 3111` necessary by `AO_required_Azeta_of_Agam_163`; `3112` sufficient by
  `AO_threshold_check_163`; old `M = 0.05` closure needed only `≥ 1` by
  `R02Pilot.threshold_check`). With committed `Agam = 1/1e7` the `M = 163`
  closure needs `≥ 186710909` by
  `AO_required_Azeta_of_committed_Gamma_163` (was `≥ 59090` for `M = 0.05`).
  Sibling zeta-lower agent OWNS: conditional `Azeta1 = 1/39` at `1-s0` from
  `‖S_{2048}‖ ≥ 1/3` (`zeta_S1_lower_of_S2048`, margin `~70%`) ⇒ downstream
  `Azeta = 1/2340000000` (`zeta_S0_lower_of_S1`); `S_{2048}` premise stays
  conditional (KL Tier-1 closed, Tier-2 Abel bridge + Tier-3 van der Corput
  or interval arithmetic still open; tail `r(1) ≥ 16` vs `1/3` proves no
  small-M triangle closure exists).

* THRESHOLD (`M = 163`): `AO_threshold_check_163`
  (`205.382 ≤ 205.392`), `AO_budget_163_eq`, `AO_product_163_eq`,
  `AO_center_bound_163_of_components`,
  `AO_R02_closed_of_factorBounds_163` (`ε = 0.002`, `M = 163`,
  `Apoly = 22`, `Api = 1/2`, `Agam = 0.006`, `Azeta = 3112`,
  `radius < 1.26`). Even with zeta-upper closed, the center product
  `22*0.5*0.006*1 = 0.066` vs budget `205.382` is infeasible at realistic
  `|ζ| = O(1)` — the honest wall stands; no cells claimed closed.
-/

end AO_R02DiscUpdate

#print axioms AO_R02DiscUpdate.AO_sphere_sup_eq
#print axioms AO_R02DiscUpdate.AO_M_eq
#print axioms AO_R02DiscUpdate.AO_xiShifted_upper_of_zeta_upper_R02
#print axioms AO_R02DiscUpdate.AO_entire_upper_of_zeta_upper_R02
#print axioms AO_R02DiscUpdate.AO_R02_uniform_sphere_bound
#print axioms AO_R02DiscUpdate.AO_R02_deriv_bound_of_zeta_upper
#print axioms AO_R02DiscUpdate.AO_R02_deriv_bound_163_of_zeta_upper
#print axioms AO_R02DiscUpdate.AO_threshold_check_163
#print axioms AO_R02DiscUpdate.AO_required_Azeta_of_Agam_163
#print axioms AO_R02DiscUpdate.AO_required_Azeta_of_committed_Gamma_163
#print axioms AO_R02DiscUpdate.AO_center_bound_163_of_components
#print axioms AO_R02DiscUpdate.AO_R02_closed_of_factorBounds_163

/-! ## AU door-3 closer wiring v2: R02 closure threshold in `Agam = 0.002` era (`M = 163`)

TASK (door-3 closer wiring v2): re-derive the R02 closure threshold in the
`Agam = 0.002` era (AN landed `R02GammaLower.gammaOf_lower_R02`;
AO's v1 used `Agam = 0.006` / `M = 163` / required-`Azeta >= 3111`).

Recomputed numbers (honest, exact):
* Budget `M = 163`: `0.002 + 163 * 1.26 = 205.382` (`AU_budget_163_eq`,
  mirrors `AO_R02DiscUpdate.AO_budget_163_eq`).
* Coefficient `Agam = 0.002`: `22 * (1/2) * 0.002 = 0.022`.
* Ratio: `205.382 / 0.022 = 9335.5454...` (so necessary floor `9335`,
  sufficient integer `9336` with product `205.392`, margin `0.01`).
* Product: `22 * (1/2) * 0.002 * 9336 = 205.392` (`AU_product_163_002_eq`,
  mirrors `AO_product_163_eq` `22*(1/2)*0.006*3112 = 205.392`; exactly `3x`
  the `Azeta` since `0.006 / 0.002 = 3`, i.e. `3112 * 3 = 9336`).
* Threshold check: `0.002 + 163 * 1.26 <= 22*(1/2)*0.002*9336`
  (`205.382 <= 205.392`, `AU_threshold_check_163_002`,
  mirrors `AO_threshold_check_163`).
* Necessity: `Azeta >= 9335` (`AU_required_Azeta_of_Agam002_163`,
  mirrors `AO_required_Azeta_of_Agam_163` `>= 3111`).
* Old AN tier at `M = 0.05`: `0.065 / 0.022 = 2.9545...`, necessary `2.95`
  (`R02GammaLower.required_Azeta_of_this_Gamma`), sufficient `3`
  (`0.022 * 3 = 0.066 >= 0.065`). The `M = 163` budget is `3160x` larger
  (`205.382 / 0.065`), so the `Azeta` tier scales from `~3` to `~9336`.

Grep-first record (2026-09-04, verified via `rg -n`, exact names):
* `theorem gammaOf_lower_R02` -> `interval_arith.lean:32566`
  (`(0.002:Real) <= ||DerivCauchyBridge.gammaOf R02Pilot.sCenter||`).
* `def AO_gamma_upper_disc_R02_obligation` -> `central_cover_assembly.lean:9975`
  (`forall s, 0.05 <= re -> re <= 0.74 -> -8.25 <= im -> im <= -5.25 ->`
  `||gammaOf s|| <= 0.097`; landed `R02GammaDisc.gammaOf_upper_disc_R02`
  at `interval_arith.lean:32316`).
* `theorem AO_R02_deriv_bound_163_of_zeta_upper` -> `central_cover_assembly.lean:10078`
  (`M = 163` from `AO_gamma_upper` + `R02_zeta_upper_obligation`).
* `def R02_zeta_upper_obligation` -> `central_cover_assembly.lean:6493`
  (`forall s, ... -> ||zeta s|| <= 10` on the R02 disc `s`-rect).
* `noncomputable def gammaOf` -> `central_cover_assembly.lean:6334`
  (`Complex.Gamma (s / 2)`).
* `noncomputable def sCenter` (`R02Pilot`) -> `central_cover_assembly.lean:9588`
  (`(1/2:Complex) + I * R02.center`).
* `theorem R02_H_instance` -> `central_cover_assembly.lean:1499`
  (consumes `R02_leaf_obligations` at `:1470`).
* `theorem R02_radius_lt` -> `central_cover_assembly.lean:1457`
  (`R02.radius < 1.26`).
* `theorem prod_four_ge_of_ge` -> `rh_certificate_infra.lean:195`
  (four-factor lower bridge, consumed at `:9596` pattern).
* `theorem AO_threshold_check_163` -> `central_cover_assembly.lean:10099`
  (`205.382 <= 205.392` at `Agam = 0.006`).
* `theorem AO_required_Azeta_of_Agam_163` -> `central_cover_assembly.lean:10107`
  (`>= 3111` necessary).
* `theorem AO_center_bound_163_of_components` -> `central_cover_assembly.lean:10157`.
* `theorem AO_R02_closed_of_factorBounds_163` -> `central_cover_assembly.lean:10192`.
* `theorem R02_closed_of_factorBounds` -> `central_cover_assembly.lean:9778`
  (`Agam >= 0.006`, `Azeta >= 1`, `M <= 0.05` v1).
* `theorem required_Azeta_of_this_Gamma` (`R02GammaLower`) -> `interval_arith.lean:32582`
  (`>= 2.95` at `M = 0.05`, `Agam = 0.002`).

IMPORT CYCLE NOTE: `interval_arith.lean:4` imports `central_cover_assembly`,
so this file CANNOT import `interval_arith`. AN's landed
`R02GammaLower.gammaOf_lower_R02` is therefore mirrored as the EXPLICIT
premise `AU_gamma_lower_R02_obligation` with the IDENTICAL statement
(`(0.002:Real) <= ||DerivCauchyBridge.gammaOf R02Pilot.sCenter||`),
exactly like AO's `AO_gamma_upper_disc_R02_obligation` pattern.
Downstream (in `interval_arith` or `riemann_hypothesis_newsection`) discharge
`hGam` by `R02GammaLower.gammaOf_lower_R02`. No `sorry`/`admit`/`axiom`,
no hypothesis stand-ins beyond named landed-obligation premises plus the
pre-existing `DerivCauchyBridge.R02_zeta_upper_obligation` (`||zeta|| <= 10`)
and AO's `AO_gamma_upper_disc_R02_obligation` (for `M <= 163`).
-/

namespace AU_R02_Agam002_M163

/-- Gamma-lower obligation matching AN's landed
`R02GammaLower.gammaOf_lower_R02` (`interval_arith.lean:32566`) exactly:
identical concl `0.002 <= ||gammaOf sCenter||`.
Stated here (not imported) to avoid the `interval_arith -> central_cover_assembly`
import cycle; discharged downstream by the landed lemma. -/
def AU_gamma_lower_R02_obligation : Prop :=
  (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖

/-- Updated budget value with `M = 163`: `0.002 + 163 * 1.26 = 205.382`
(mirrors `AO_R02DiscUpdate.AO_budget_163_eq`; budget is `M`-only, unchanged
by the `Agam = 0.002` era). -/
theorem AU_budget_163_eq : (0.002 : ℝ) + 163 * 1.26 = 205.382 := by
  norm_num

/-- Updated product value at `Agam = 0.002`: `22 * (1/2) * 0.002 * 9336 = 205.392`
(mirrors `AO_product_163_eq` `22*(1/2)*0.006*3112 = 205.392`; `9336 = 3112 * 3`
since `0.006 / 0.002 = 3`). -/
theorem AU_product_163_002_eq : (22 : ℝ) * (1 / 2) * 0.002 * 9336 = 205.392 := by
  norm_num

/-- Updated numeric product check for the `Agam = 0.002`, `M = 163` thresholds:
`0.002 + 163 * 1.26 <= 22 * (1/2) * 0.002 * 9336`
(`205.382 <= 205.392`, margin `0.01`; mirrors `AO_threshold_check_163`
`0.002+163*1.26 <= 22*(1/2)*0.006*3112`). -/
theorem AU_threshold_check_163_002 :
    (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.002 * 9336 := by
  norm_num

/-- Updated feasibility threshold with `M = 163`, `Agam = 0.002` era:
closing needs `Azeta >= 9335` (floor of `205.382 / 0.022 = 9335.5454...`;
sufficient integer `9336` by `AU_threshold_check_163_002`). Mirrors
`AO_required_Azeta_of_Agam_163` (`>= 3111` at `Agam = 0.006`) and
`R02GammaLower.required_Azeta_of_this_Gamma` (`>= 2.95` at `M = 0.05`)
shapes with exact numbers. -/
theorem AU_required_Azeta_of_Agam002_163 {Azeta : ℝ}
    (h : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.002 * Azeta) :
    (9335 : ℝ) ≤ Azeta := by
  have hb : (0.002 : ℝ) + 163 * 1.26 = 205.382 := by norm_num
  rw [hb] at h
  have hcoeff : (22 : ℝ) * (1 / 2) * 0.002 = 0.022 := by norm_num
  rw [hcoeff] at h
  have hpos : (0 : ℝ) < 0.022 := by norm_num
  have hcomm : (0.022 : ℝ) * Azeta = Azeta * 0.022 := by ring
  have h2 : (205.382 : ℝ) ≤ Azeta * 0.022 := by
    rw [← hcomm]
    exact h
  have hdiv : (205.382 : ℝ) / 0.022 ≤ Azeta :=
    (div_le_iff₀ hpos).mpr h2
  have hnum : (9335 : ℝ) ≤ (205.382 : ℝ) / 0.022 := by
    rw [le_div_iff₀ hpos]
    norm_num
  exact le_trans hnum hdiv

/-- Updated center bound with `M = 163`, `Agam = 0.002`: from `Agam >= 0.002`,
`Azeta >= 9336` gives `0.002 + 163 * radius <= ||xi(center)||` (mirrors
`AO_R02DiscUpdate.AO_center_bound_163_of_components`, which fixes
`Agam = 0.006`, `Azeta = 3112`). -/
theorem AU_center_bound_163_002_of_components
    (hGam : (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (9336 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖) :
    (0.002 : ℝ) + 163 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  have hpoly : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf R02Pilot.sCenter‖ :=
    R02Pilot.poly_lower
  have hpi : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf R02Pilot.sCenter‖ :=
    R02Pilot.pi_lower
  have harg2 : (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center =
      R02Pilot.sCenter := rfl
  have hdecomp :=
    DerivCauchyBridge.norm_xiShifted_eq_parts CentralCoverAssembly.R02.center
  rw [harg2] at hdecomp
  have hle : 22 * (1 / 2) * 0.002 * 9336 ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hGam hZeta
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbud : 163 * CentralCoverAssembly.R02.radius ≤ 163 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt CentralCoverAssembly.R02_radius_lt) (by norm_num)
  have hthresh : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.002 * 9336 :=
    AU_threshold_check_163_002
  linarith

/-- R02 conditional closure in the `Agam = 0.002`, `M = 163` era: three explicit
numeric premises discharge the H-leaf shape of
`inner_nonvanishing_of_fenced_grid_fine` at R02's grid cell
`(-8,-5.5,0.01,0.2)` with `eps = 0.002`, `M = 163`.
Mirrors `AO_R02DiscUpdate.AO_R02_closed_of_factorBounds_163`
(`Agam >= 0.006`, `Azeta >= 3112`, `M <= 163`); the weaker `Agam` forces
`Azeta >= 9336` (sufficient by `AU_threshold_check_163_002`). -/
theorem AU_R02_closed_of_factorBounds_163_002
    (hGam : (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (9336 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖)
    (hDeriv : ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ))
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hcenter : (0.002 : ℝ) + 163 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ :=
    AU_center_bound_163_002_of_components hGam hZeta
  subst hc_eq
  exact ⟨CentralCoverAssembly.R02, 0.002, 163, rfl, rfl, rfl, rfl,
    CentralCoverAssembly.R02_strip_lo, CentralCoverAssembly.R02_strip_hi,
    (by norm_num), hDeriv, hcenter⟩

/-- Fully-wired R02 conditional closure in the `Agam = 0.002`, `M = 163` era.

PREMISE / OWNER / STATUS TABLE (each premise, who owns it, landed-vs-open,
exact numeric tier):
* (P1) ZETA-UPPER `DerivCauchyBridge.R02_zeta_upper_obligation`
  (`||zeta s|| <= 10` on the disc `s`-rect `Re in [0.05,0.74]`,
  `Im in [-8.25,-5.25]`) -- sibling zeta-upper agent OWNS -- OPEN
  (needs FE+Stirling+convexity; crude window `1.2e9` vs needed `50.925`).
* (P2) GAMMA-UPPER `AO_R02DiscUpdate.AO_gamma_upper_disc_R02_obligation`
  (`||gammaOf s|| <= 0.097` on the same rect) -- AH OWNS, LANDED
  (`R02GammaDisc.gammaOf_upper_disc_R02`, `interval_arith.lean:32316`;
  true sup `~0.026`, within `3.7x`) -- stays an explicit premise here
  (import cycle `interval_arith -> central_cover_assembly`).
  P1+P2 together give `M <= 163` via
  `AO_R02DiscUpdate.AO_R02_deriv_bound_163_of_zeta_upper`
  (`40.74 / 0.25 = 162.96`, ceil `163`; old `67200`, unconditional `6800640`).
* (P3) GAMMA-LOWER `AU_gamma_lower_R02_obligation`
  (`0.002 <= ||gammaOf R02Pilot.sCenter||` at `s = 0.395 - 6.75*I`) --
  AN OWNS, LANDED (`R02GammaLower.gammaOf_lower_R02`,
  `interval_arith.lean:32566`; `20000x` over uniform `1/1e7`, `3x` short of
  `0.006`; true `~0.0087`, headroom `4.3x`) -- stays an explicit premise here
  (same import cycle; mirrors AO's obligation pattern, never by import).
* (P4) ZETA-LOWER `(9336:Real) <= ||zeta R02Pilot.sCenter||` --
  sibling zeta-lower agent OWNS -- OPEN (true `|zeta| = O(1)` vs need `9336`;
  `>= 9335` necessary by `AU_required_Azeta_of_Agam002_163`, `9336` sufficient
  by `AU_threshold_check_163_002`; old `M = 0.05` tier needed only `>= 2.95`
  necessary / `3` sufficient; AO v1 at `Agam = 0.006` needed `>= 3111` / `3112`;
  committed `Agam = 1/1e7` at `M = 163` would need `>= 186710909`).
* (HYPS) POLY `22 <= ||polyOf sCenter||` (`R02Pilot.poly_lower`) and
  PI `1/2 <= ||piOf sCenter||` (`R02Pilot.pi_lower`) -- CLOSED hypothesis-free
  in-file -- no premise.
* (LEAF) `R02_H_instance` wiring (`CentralCoverAssembly.R02_leaf_obligations`
  at `:1470`, `R02_radius_lt` `< 1.26` at `:1457`, `gridFine` cell
  `(-8,-5.5,0.01,0.2)`) -- CLOSED in-file -- mirrors
  `R02_closed_of_factorBounds` / `AO_R02_closed_of_factorBounds_163` exactly.
* HONEST NET: center product `22*0.5*0.002*9336 = 205.392` vs budget `205.382`
  closes conditionally (margin `0.01`), but at realistic `|zeta| = O(1)` the
  product `22*0.5*0.002*1 = 0.022 << 205.382` is infeasible -- 0 cells claimed
  closed; remaining 39 cells: same shape, different `s`-rects.
-/
theorem AU_R02_closed_wired_163_002
    (hG_up : AO_R02DiscUpdate.AO_gamma_upper_disc_R02_obligation)
    (hZ_up : DerivCauchyBridge.R02_zeta_upper_obligation)
    (hGam : AU_gamma_lower_R02_obligation)
    (hZeta : (9336 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hGam' : (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
    hGam
  have hDeriv : ∀ w, CentralCoverAssembly.R02.mem w →
      ‖deriv xiShifted w‖ ≤ (163 : ℝ) :=
    AO_R02DiscUpdate.AO_R02_deriv_bound_163_of_zeta_upper hG_up hZ_up
  exact AU_R02_closed_of_factorBounds_163_002 hGam' hZeta hDeriv c hc_mem hc_eq

/-! ### AU residual premise inventory (who owns what for the R02 H-leaf, `Agam = 0.002` era)

* DERIV `M = 163` (AO, CLOSED conditional, reused here):
  `AO_R02DiscUpdate.AO_R02_deriv_bound_163_of_zeta_upper`
  (`162.96`, ceil `163`) from `R02_zeta_upper_obligation` (`<= 10`) +
  `AO_gamma_upper_disc_R02_obligation` (`<= 0.097`, landed `32316`).
* ZETA-UPPER `||zeta|| <= 10` (sibling OWNS; OPEN): needs `A <= 50.925`
  damped three-lines left cap; crude `1.2e9` banked, gap `~2.4e7x` in
  cos/exp majorant; needs Stirling-sharp left edge (FE+Stirling+convexity
  absent); eta M-test needs `M >= 1e31` terms (`r(M) ~= 180*M^-0.05`).
* AGAM `>= 0.002` at `R02Pilot.sCenter` (AN OWNS; LANDED `32566` as
  `R02GammaLower.gammaOf_lower_R02`; mirrored here as
  `AU_gamma_lower_R02_obligation` for cycle safety; `20000x` over `1/1e7`,
  `3x` short of `0.006`; true `~0.0087`).
* AZETA `>= 9336` at `R02Pilot.sCenter` for `M = 163` closure
  (`>= 9335` necessary by `AU_required_Azeta_of_Agam002_163`; `9336` sufficient
  by `AU_threshold_check_163_002`; old `M = 0.05` needed `>= 2.95` / `3`;
  AO v1 at `0.006` needed `>= 3111` / `3112`; committed `1/1e7` at `M = 163`
  would need `>= 186710909`). Sibling zeta-lower OWNS (conditional `1/39`
  at `1-s0` from `||S_2048|| >= 1/3` => `1/2340000000` downstream;
  `S_2048` stays conditional; no small-`M` triangle closure exists).
* THRESHOLD (`Agam = 0.002`, `M = 163`): `AU_budget_163_eq` (`205.382`),
  `AU_product_163_002_eq` (`205.392`), `AU_threshold_check_163_002`
  (`205.382 <= 205.392`), `AU_center_bound_163_002_of_components`,
  `AU_R02_closed_of_factorBounds_163_002` + wired
  `AU_R02_closed_wired_163_002` (`eps = 0.002`, `M = 163`, `Apoly = 22`,
  `Api = 1/2`, `Agam = 0.002`, `Azeta = 9336`, `radius < 1.26`).
  Honest net: `0.022 << 205.382` at realistic `|zeta|` -- infeasible in
  practice; 0 cells claimed closed.
-/

end AU_R02_Agam002_M163

#print axioms AU_R02_Agam002_M163.AU_budget_163_eq
#print axioms AU_R02_Agam002_M163.AU_product_163_002_eq
#print axioms AU_R02_Agam002_M163.AU_threshold_check_163_002
#print axioms AU_R02_Agam002_M163.AU_required_Azeta_of_Agam002_163
#print axioms AU_R02_Agam002_M163.AU_center_bound_163_002_of_components
#print axioms AU_R02_Agam002_M163.AU_R02_closed_of_factorBounds_163_002
#print axioms AU_R02_Agam002_M163.AU_R02_closed_wired_163_002

/-! ## AX per-cell parametric closure template (door-wide rollout, R02 v2 generalized)

GREP-first record (2026-09-03/04, verified by scans before writing; exact names):
* `R02_closed_of_factorBounds` -> `central_cover_assembly.lean:9778`
  (`Agam >= 0.006`, `Azeta >= 1`, `M <= 0.05` v1 pilot).
* `AO_R02_deriv_bound_163_of_zeta_upper` -> `:10078` (ceil `M = 163` tier);
  `AO_R02_closed_of_factorBounds_163` -> `:10192`
  (`Agam >= 0.006`, `Azeta >= 3112`, `M = 163`; budget `205.382` vs `205.392`).
* `AU_R02_closed_of_factorBounds_163_002` -> `:10443`
  (`Agam >= 0.002`, `Azeta >= 9336`, `M = 163` v2 era);
  `AU_R02_closed_wired_163_002` -> `:10502` (fully-wired H-leaf + P1-P4 table).
* `DerivCauchyBridge.norm_xiShifted_eq_parts` -> `:6350`;
  `TailProofEngine.prod_four_ge_of_ge` -> `rh_certificate_infra.lean:195`;
  `DerivCauchyBridge.polyOf/piOf/gammaOf` -> `:6328/:6331/:6334`.
* `R02Pilot.sCenter` -> `:9588` (`s = 0.395 - 6.75*I`);
  `R02Pilot.poly_lower` -> `:9649` (`22 <= ||polyOf sCenter||`);
  `R02Pilot.pi_lower` -> `:9692` (`1/2 <= ||piOf sCenter||`);
  `AU_threshold_check_163_002`
  (`0.002+163*1.26 <= 22*(1/2)*0.002*9336`, margin `0.01`) -> `:10475`.
* `CentralCoverAssembly.R02` -> `:1430` (`(-8,-5.5,0.01,0.2)`);
  `R02_radius_lt` (`< 1.26`) -> `:1457`; `R02_mem_gridFine` -> `:1460`;
  `R02_strip_lo/hi` -> `:1441/:1442`; `R02_H_instance` -> `:1499`;
  `gridFine` (40 cells) -> `:1002`;
  `inner_nonvanishing_of_fenced_grid_fine` -> `:1047`.
* `CellUniform.pi_lower_of_re` (`1/2`, any `Re <= 1/2`) -> `interval_arith.lean:1752`;
  `CellUniform.center_bound_of_component_bounds` (generic `R`, `radCap 1.26`
  template over `R00Enclosure` parts) -> `:1772` (shape mirrored here over
  `DerivCauchyBridge` parts to avoid the `interval_arith -> central_cover_assembly`
  import cycle; cf. AO `:9957-9965`, AU `:10336-10346` notes).
* `CellGammaUniform.gamma_lower_wide` (`1/1e7`, `Re in [0.01,0.49]`,
  `|Im| <= 10`, `Im != 0`) -> `interval_arith.lean:1686`;
  `R02GammaLower.gammaOf_lower_R02` (`0.002` at `R02Pilot.sCenter`) -> `:32566`;
  `R02GammaDisc.gammaOf_upper_disc_R02` (`<= 0.097`, `Re in [0.05,0.74]`,
  `Im in [-8.25,-5.25]`) -> `:32316`.
* `R00Numerics.poly_lower_R00` (`30`) -> `interval_arith.lean:304`;
  `R00Numerics.pi_lower_R00` (`1/2`) -> `:322`;
  `R02Uniform.poly_lower_R02` (`22`) -> `:1864`;
  `R02Uniform.pi_lower_R02` (`1/2`) -> `:1872`.
* `RowFE` per-row (`|Im| <= 8.75`): Gamma uppers `3/4/5/10`
  (`RowFE_realGamma_0395/030/020/0105_le` -> `:31047/:31073/:31099/:31125`);
  factor uppers `6e7/8e7/1e8/2e8`
  (`RowFE_factor_upper_0395/030/020/0105` -> `:31548/:31606/:31664/:31722`);
  factor lowers `1e-14` all rows
  (`RowFE_factor_lower_0395/030/020/0105` -> `:31558/:31616/:31674/:31732`);
  cos lowers `0.8/0.88/0.95/0.98`
  (`RowFE_cos_real_lower_0395/030/020/0105` -> `:31378/:31396/:31414/:31432`).
* Central rects/radii/leaf-tiers (`central_cover_assembly.lean`):
  bottom row R00-R10 defs `:1133/:1252/:1430/:1516/:1602/:1688/:1774/:1860`
  `/:1946/:2032/:2118`, leaves `:1175/:1288/:1470/:1556/:1642/:1728/:1814/:1900`
  `/:1986/:2072/:2158` (outer `(0.002,0.05)`, mid `(0.05,0.07)`,
  inner `(0.15,0.06)`); row1 R11-R20 defs
  `:2493/:2577/:2661/:2745/:2829/:2913/:2997/:3081/:3165/:3249`;
  row2 R21-R30 `:3335/:3419/:3503/:3587/:3671/:3755/:3839/:3923/:4007/:4091`;
  row3 R31-R40 `:4177/:4261/:4345/:4429/:4513/:4597/:4681/:4765/:4849/:4933`;
  `RXX_mem_gridFine` for R00 and R02-R40, e.g. `:1164/:1460/:1546/:1632`
  through `:4963` (R01 has none: `(-7.5,-5) ∉ fineGridX`,
  membership-free H-leaf, see `:1244-1248`).
* Strips (`central_cover_assembly.lean`): `edgeStripCells` (10 uppers
  `y=(0.49,0.5)`) -> `:6584`; EdgeS00 geometry/poly-56/Gamma-400
  -> `:6663/:6679/:6699/:6810`; EdgeS01-09 poly-56
  -> `:7013/:7129/:7245/:7361/:7477/:7593/:7709/:7825/:7941`;
  lower mirrors EdgeS00_Lower onward plus generic poly-56 -> `:8203+/:8167`;
  shrunk `(0.49,0.499)` pair -> `:8306/:8321`;
  `CutL10/CutR10` geometry (`dx=0.25/dy=0.49/radius<0.56`)
  -> `:6826/:6830/:6876/:6879`.

IMPORT CYCLE NOTE (as AO/AU): `interval_arith.lean:4` imports
`central_cover_assembly`, so this file CANNOT import `interval_arith`.
All per-cell factor numbers beyond R02 stay EXPLICIT premises below
(nothing unlanded becomes a theorem); R02's `poly_lower`/`pi_lower` are
in-file (`R02Pilot`), its `163` threshold is reused from AU's landed check.
Full proofs only; no hidden obligations beyond named landed-obligation premises.
-/

namespace AX_CellTemplate

/-- Per-cell parametric center bridge (mirrors AU's
`AU_center_bound_163_002_of_components`, generalized over the rect `R`,
its `s`-plane center `sC`, all four factor floors, `M`, and the radius cap
`radCap`): four-factor bridge via
`DerivCauchyBridge.norm_xiShifted_eq_parts` +
`TailProofEngine.prod_four_ge_of_ge`, then `M * radius <= M * radCap`
monotonicity into the budget. -/
theorem center_bound_of_factorBounds
    (R : CellProofEngine.Rect2D)
    (sC : ℂ) (hsC : (1 / 2 : ℂ) + Complex.I * R.center = sC)
    (Apoly Api Agam Azeta ε M radCap : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hM0 : 0 ≤ M)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC‖)
    (hZeta : Azeta ≤ ‖zeta sC‖)
    (hRad : R.radius ≤ radCap)
    (hThresh : ε + M * radCap ≤ Apoly * Api * Agam * Azeta) :
    ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts R.center
  rw [hsC] at hdecomp
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted R.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hGam hZeta hA0 hB0 hC0 hD0
  have hbud : M * R.radius ≤ M * radCap :=
    mul_le_mul_of_nonneg_left hRad hM0
  linarith

/-- Per-cell parametric closure template (generalizes AU's
`AU_R02_closed_of_factorBounds_163_002` to a generic cell): explicit numeric
premises (poly/pi/Gamma/zeta floors, deriv cap `M`, radius cap + budget
inequality) discharge the H-leaf shape of
`inner_nonvanishing_of_fenced_grid_fine` at the cell's `gridFine` tuple.
The `gridFine`-membership and coordinate premises keep the fencing link;
analytic content is entirely in the factor floors + `hThresh`. -/
theorem CellClosed_of_factorBounds
    (R : CellProofEngine.Rect2D)
    (sC : ℂ) (hsC : (1 / 2 : ℂ) + Complex.I * R.center = sC)
    (Apoly Api Agam Azeta ε M radCap : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hM0 : 0 ≤ M)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC‖)
    (hZeta : Azeta ≤ ‖zeta sC‖)
    (hDeriv : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (hRad : R.radius ≤ radCap)
    (hThresh : ε + M * radCap ≤ Apoly * Api * Agam * Azeta)
    (hStripLo : -(1 / 2 : ℝ) < R.y0) (hStripHi : R.y1 < (1 / 2 : ℝ))
    (hEps : 0 < ε)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hx0 : R.x0 = c.1) (hx1 : R.x1 = c.2.1)
    (hy0 : R.y0 = c.2.2.1) (hy1 : R.y1 = c.2.2.2) :
    ∃ (Rw : CellProofEngine.Rect2D) (εw Mw : ℝ),
      Rw.x0 = c.1 ∧ Rw.x1 = c.2.1 ∧ Rw.y0 = c.2.2.1 ∧ Rw.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < Rw.y0 ∧ Rw.y1 < (1 / 2 : ℝ) ∧
      0 < εw ∧ (∀ w, Rw.mem w → ‖deriv xiShifted w‖ ≤ Mw) ∧
      εw + Mw * Rw.radius ≤ ‖xiShifted Rw.center‖ := by
  have hcenter : ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
    center_bound_of_factorBounds R sC hsC Apoly Api Agam Azeta ε M radCap
      hA0 hB0 hC0 hD0 hM0 hpoly hpi hGam hZeta hRad hThresh
  exact ⟨R, ε, M, hx0, hx1, hy0, hy1, hStripLo, hStripHi, hEps, hDeriv, hcenter⟩

/-- R02 corollary: the template recovers AU's v2 numbers exactly
(`Apoly = 22`, `Api = 1/2`, `Agam = 0.002`, `Azeta = 9336`,
`ε = 0.002`, `M = 163`, `radCap = 1.26`; budget `205.382` vs product
`205.392`, margin `0.01`). This proves the template matches the pilot:
same premises as `AU_R02_closed_of_factorBounds_163_002` give the same H-leaf,
with `poly_lower`/`pi_lower` from `R02Pilot` and the threshold from AU. -/
theorem R02_recovers_AU_163_002
    (hGam : (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖)
    (hZeta : (9336 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖)
    (hDeriv : ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ))
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center =
      R02Pilot.sCenter := rfl
  have hpoly : (22 : ℝ) ≤ ‖DerivCauchyBridge.polyOf R02Pilot.sCenter‖ :=
    R02Pilot.poly_lower
  have hpi : (1 / 2 : ℝ) ≤ ‖DerivCauchyBridge.piOf R02Pilot.sCenter‖ :=
    R02Pilot.pi_lower
  have hRad : CentralCoverAssembly.R02.radius ≤ (1.26 : ℝ) :=
    le_of_lt CentralCoverAssembly.R02_radius_lt
  have hThresh : (0.002 : ℝ) + 163 * 1.26 ≤ 22 * (1 / 2) * 0.002 * 9336 :=
    AU_R02_Agam002_M163.AU_threshold_check_163_002
  subst hc_eq
  exact CellClosed_of_factorBounds
    CentralCoverAssembly.R02 R02Pilot.sCenter hsC
    22 (1 / 2) 0.002 9336 0.002 163 1.26
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R02_strip_lo CentralCoverAssembly.R02_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

/-! ### AX rollout premise tiers (proved doc-string; nothing unlanded is a theorem)

How to read each row: instantiate `CellClosed_of_factorBounds` with the
cell's `R` / `sC = 1/2 + I * R.center`, the quoted `Apoly/Api/Agam/Azeta`
floors, the leaf-tier `(eps, M)` of that cell's `RXX_leaf_obligations`,
`radCap` from its `radius_lt`, and `hThresh : eps + M * radCap <= product`.
Required `Azeta` floor in closed form:
`Azeta >= (eps + M * radCap) / (Apoly * Api * Agam)`
(needs `Apoly * Api * Agam > 0`; all quoted floors are positive).
`hDeriv : ||deriv xiShifted|| <= M` on `R.mem` stays a premise everywhere
(discharged downstream per cell by the Cauchy sphere/closed-ball bridge from
a zeta-upper + Gamma-upper on that cell's disc `s`-rect, exactly as
`AO_R02_deriv_bound_163_of_zeta_upper` does for R02).

* GROUP G0 (pilot, CLOSED conditional, theorem above): R02
  `(-8,-5.5,0.01,0.2)` (`R02 :1430`, `R02_mem_gridFine :1460`,
  `R02_leaf_obligations (0.002,0.05) :1470`, `radius < 1.26 :1457`):
  `Apoly = 22` (`R02Pilot.poly_lower :9649`, also `R02Uniform :1864`),
  `Api = 1/2` (`R02Pilot.pi_lower :9692`, uniform `:1752`),
  `Agam = 0.002` (`R02GammaLower.gammaOf_lower_R02 :32566`),
  `Azeta = 9336` (premise; `>= 9335` necessary by
  `AU_required_Azeta_of_Agam002_163`, sufficient by
  `AU_threshold_check_163_002 :10475`); `M = 163` via
  `AO_R02_deriv_bound_163_of_zeta_upper :10078` from zeta-upper `<= 10`
  (`R02_zeta_upper_obligation`, OPEN) + Gamma-upper `<= 0.097`
  (`AO_gamma_upper_disc_R02_obligation`, landed `:32316`).
  Check: budget `0.002 + 163 * 1.26 = 205.382` (`AU_budget_163_eq`),
  product `22 * (1/2) * 0.002 * 9336 = 205.392`
  (`AU_product_163_002_eq`), margin `0.01`.

* GROUP G1 (bottom row `y = (0.01,0.2)`, `ymid = 0.105`, `s.Re = 0.395`,
  `radCap = 1.26`, `radius < 1.26` same shape as `:1457`):
  - G1-outer R00 `(-10,-7.5)` (`:1133`, mem `:1164`, leaf `(0.002,0.05) :1175`),
    R09 `(6,8.5)` (`:2032`, mem `:2062`, leaf `(0.002,0.05) :2072`),
    R10 `(7.5,10)` (`:2118`, mem `:2148`, leaf `(0.002,0.05) :2158`):
    `Apoly` premise per center (R00 landed `30` at `sR00`, `:304`;
    others unlanded, keep symbolic), `Api = 1/2` uniform (`:1752`,
    R00 landed `:322`), `Agam` premise (uniform `1/1e7` via `:1686`;
    R02-tier `0.002` NOT transferable off-center), `Azeta` premise with
    tier `Azeta >= (eps + M * 1.26) / (Apoly * 0.5 * Agam)`;
    at fencing tier `(0.002,0.05)` this is `(0.065)/(Apoly*0.5*Agam)`.
  - G1-mid R03 `(-6,-3.5)` (`:1516`, mem `:1546`, leaf `(0.05,0.07) :1556`),
    R04 `(-4,-1.5)` (`:1602`, mem `:1632`, leaf `:1642`),
    R07 `(2,4.5)` (`:1860`, mem `:1890`, leaf `:1900`),
    R08 `(4,6.5)` (`:1946`, mem `:1976`, leaf `:1986`),
    plus R01 `(-7.5,-5)` (`:1252`, leaf `(0.05,0.07) :1288`,
    MEMBERSHIP-FREE: `(-7.5,-5) ∉ fineGridX`, see `:1244-1248`;
    instantiate the template with its own membership premise adapted,
    coordinates unchanged): tier
    `Azeta >= (0.05 + 0.07 * 1.26) / (Apoly * 0.5 * Agam)`
    `= 0.1382 / (Apoly * 0.5 * Agam)`.
  - G1-inner R05 `(-2,0.5)` (`:1688`, mem `:1718`, leaf `(0.15,0.06) :1728`),
    R06 `(0,2.5)` (`:1774`, mem `:1804`, leaf `:1814`): tier
    `Azeta >= (0.15 + 0.06 * 1.26) / (Apoly * 0.5 * Agam)`
    `= 0.2256 / (Apoly * 0.5 * Agam)`.
  - G1 Gamma-upper (deriv side): R02 disc cap `0.097` (`:32316`,
    `Re in [0.05,0.74]`, `Im in [-8.25,-5.25]`) is R02-only; other G1 discs
    keep per-disc Gamma-upper premises (landed center caps `<= 0.01` group,
    e.g. `R02GammaUpper :8811`, `R03GammaUpper`, `R10GammaUpper :4064`;
    `RowFE` row-`0.395` toolkit: `G = 3` (`:31047`), factor `<= 6e7`
    (`:31548`), factor lower `1e-14` (`:31558`), cos lower `0.8` (`:31378`)).

* GROUP G2 (row1 `y = (0.1,0.3)`, `ymid = 0.2`, `s.Re = 0.3`,
  `radCap = 1.26`, `dx = 1.25/dy = 0.1`): R11 `(-10,-7.5)` (`:2493`,
  mem `:2523`, leaf `(0.002,0.05) :2533`), R12 `(-8,-5.5)` (`:2577`, `:2607`),
  R13 `(-6,-3.5)` mid (`:2661`, `:2691`), R14 `(-4,-1.5)` mid (`:2745`,
  `:2775`), R15 `(-2,0.5)` inner (`:2829`, `:2859`), R16 `(0,2.5)` inner
  (`:2913`, `:2943`), R17 `(2,4.5)` mid (`:2997`, `:3027`), R18 `(4,6.5)`
  mid (`:3081`, `:3111`), R19 `(6,8.5)` outer (`:3165`, `:3195`), R20
  `(7.5,10)` outer (`:3249`, `:3279`). `Apoly` premise per center
  (unlanded; keep symbolic), `Api = 1/2` uniform (`:1752` applies since
  `0.3 <= 1/2`), `Agam` premise (uniform `1/1e7` `:1686`), `Azeta` premise
  with the same three tier formulas as G1 (outer/mid/inner `(eps,M)` are
  identical). `RowFE` row-`0.3` toolkit: `G = 4` (`:31073`), factor
  `<= 8e7` (`:31606`), lower `1e-14` (`:31616`), cos `0.88` (`:31396`).

* GROUP G3 (row2 `y = (0.2,0.4)`, `ymid = 0.3`, `s.Re = 0.2`,
  `radCap = 1.26`): R21 `(-10,-7.5)` (`:3335`, mem `:3365`), R22 `(-8,-5.5)`
  (`:3419`, `:3449`), R23 `(-6,-3.5)` mid (`:3503`, `:3533`), R24 `(-4,-1.5)`
  mid (`:3587`, `:3617`), R25 `(-2,0.5)` inner (`:3671`, `:3701`), R26
  `(0,2.5)` inner (`:3755`, `:3785`), R27 `(2,4.5)` mid (`:3839`, `:3869`),
  R28 `(4,6.5)` mid (`:3923`, `:3953`), R29 `(6,8.5)` outer (`:4007`,
  `:4037`), R30 `(7.5,10)` outer (`:4091`, `:4121`). Same tier formulas;
  `Api = 1/2` uniform (`0.2 <= 1/2`); `RowFE` row-`0.2`: `G = 5`
  (`:31099`), factor `<= 1e8` (`:31664`), lower `1e-14` (`:31674`), cos
  `0.95` (`:31414`).

* GROUP G4 (row3 `y = (0.3,0.49)`, `ymid = 0.395`, `s.Re = 0.105`,
  `radCap = 1.26`): R31 `(-10,-7.5)` (`:4177`, mem `:4207`), R32 `(-8,-5.5)`
  (`:4261`, `:4291`), R33 `(-6,-3.5)` mid (`:4345`, `:4375`), R34 `(-4,-1.5)`
  mid (`:4429`, `:4459`), R35 `(-2,0.5)` inner (`:4513`, `:4543`), R36
  `(0,2.5)` inner (`:4597`, `:4637`), R37 `(2,4.5)` mid (`:4681`, `:4711`),
  R38 `(4,6.5)` mid (`:4765`, `:4795`), R39 `(6,8.5)` outer (`:4849`,
  `:4879`), R40 `(7.5,10)` outer (`:4933`, mem `:4963`). Same tier
  formulas; `Api = 1/2` uniform (`0.105 <= 1/2`); `RowFE` row-`0.105`:
  `G = 10` (`:31125`), factor `<= 2e8` (`:31722`), lower `1e-14`
  (`:31732`), cos `0.98` (`:31432`). DERIV CAVEAT (upper rows): the `0.25`
  sphere exits the strip (`0.49 + 0.25 > 0.5`), so the deriv premise must
  use `r < 0.01` spheres or the closed-ball bridge
  (`uniform_deriv_of_closedBall_bound`); keep `M` a premise with that
  side condition documented, do not reuse the `0.25`-sphere numbers here.

* GROUP G5 (edge strips UPPER, 10 cells, `y = (0.49,0.5)`, `ymid = 0.495`,
  `s.Re = 0.005`, `dx = 1.25/dy = 0.005`, `radius < 1.26`
  e.g. `EdgeS00_radius_lt :6691`): EdgeS00 `(-10,-7.5)` (`:6663`) through
  EdgeS09 `(7.5,10)` (`:7912`); list membership in `edgeStripCells :6584`.
  Landed hypothesis-free factors: poly `<= 56` per column
  (`:6699/:7013/:7129/:7245/:7361/:7477/:7593/:7709/:7825/:7941`),
  pi `<= 1`, Gamma `<= 400` at center (`s/2` has `Re = 0.0025`, `:6810`).
  Center/deriv premises per cell: `Azeta` lower at `s = 0.005 + x_c*I`
  plus the strip `M`; tier formula with `radCap = 1.26` and the strip
  `(eps, M)` (reuse the column's central `(eps, M)` or keep symbolic).
  STRIP CAVEAT: `y1 = 0.5` is NOT `< 1/2` (`EdgeS00_touches_top :6697`
  pattern holds for all 10 uppers), so the H-leaf strip hypothesis must
  use the shrunk pair (`EdgeS00_ShrunkUpper/Lower :8306/:8321`,
  `y1 = 0.499`, explicit gaps `[0.499,0.5)`/`(-0.5,-0.499]`); keep the
  shrunk coordinates as premises.

* GROUP G6 (edge strips LOWER mirrors, 10 cells, `y = (-0.5,-0.49)`,
  `s.Re = 0.995`, same `dx/dy/radius` e.g. `:8219-8224`): EdgeS00_Lower
  (`:8203`) through EdgeS09_Lower (`:9075`). Landed: generic poly `<= 56`
  (`Re in [0.99,1.0]`, `:8167`; per-column e.g. `:8263`), Gamma `<= 2` at
  `re 0.995` + `<= 3` at `0.4975` (center-independent chains). Per-cell
  `Azeta` at `s = 0.995 + x_c*I` (e.g. `0.995 - 8.75*I` for S00) plus `M`
  stay premises with `radCap = 1.26`.

* GROUP G7 (cutoff lines, 2 thin rects): CutL10
  `(-10.25,-9.75,-0.49,0.49)` (`:6826`, `dx = 0.25/dy = 0.49`,
  `radius < 0.56 :6876`, strip `:6882-6883`, line membership `:6898`) and
  CutR10 (`:6830`, `:6879`, `:6884-6885`, `:6888`); covering
  `cutoffLines_either :6911`. Per-rect center + deriv need the same two
  zeta enclosures on vertical `s`-rects (`Re in [0.01,0.99]`, `Im = +-10`,
  true `O(1)`); tier formula with `radCap = 0.56`.
  Lines with `0.49 <= |Im| < 1/2` additionally need the strip cells above.

Residual honesty (unchanged from AU): at realistic `|zeta| = O(1)` every
group's product `Apoly * 0.5 * Agam * 1` is orders of magnitude below its
`eps + M * radCap` once `M` is at wired tier (`163`); 0 cells claimed
closed. Closing any cell = landing its `Azeta` (zeta-lower agent) +
  its zeta-upper/Gamma-upper `M` (zeta-upper agent) and feeding this template.
-/

end AX_CellTemplate

#print axioms AX_CellTemplate.center_bound_of_factorBounds
#print axioms AX_CellTemplate.CellClosed_of_factorBounds
#print axioms AX_CellTemplate.R02_recovers_AU_163_002
/-! ## BB row-3 small-r deriv packaging (door-3 rollout premise, upper rows)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `:6201`
  (`M = C / r` from per-`w` sphere sups);
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`
  (`M = C / r` from one closed-ball sup via
  `sphere_subset_closedBall_of_rect_mem` `:6213` +
  `Rect2D.norm_sub_center_le_radius` `rh_certificate_infra.lean:52`).
* `CentralCoverAssembly.R31` (`(-10,-7.5,0.3,0.49)`) -> `:4177`;
  `R31_x0/x1/y0/y1` -> `:4180-4183`; `R31_strip_lo/hi` -> `:4188-4189`;
  `R31_radius_lt` (`< 1.26`) -> `:4204`; `R31_mem_gridFine` -> `:4207`.
* `AX_CellTemplate.CellClosed_of_factorBounds` (generic per-cell template) ->
  `:10676`; `R02_recovers_AU_163_002` (pilot recovery pattern) -> `:10710`.
* Quoted sup values (obligations only, no import of `interval_arith`, which
  imports this file -- AO/AU pattern, cf. `:9957-9965`):
  poly `56` (edge-strip poly-56 tier, cf. `:6699`);
  pi `1` (`DerivCauchyBridge.pi_upper_R02_disc`, `:6396`);
  Gamma `10` (`RowFE_realGamma_0105_le`, `interval_arith.lean:31125`,
  row-`0.105` family);
  zeta `10` (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).
  `R02GammaDisc.gammaOf_upper_disc_R02` (`interval_arith.lean:32316`,
  `<= 0.097`) is R02-rect-only (`Re in [0.05,0.74]`, `Im in [-8.25,-5.25]`)
  and NOT reused here: the row-3 small-`r` `s`-rect below
  (`Re in [0.001,0.21]`, `Im in [-10.01,-7.49]`) is disjoint from it.

DERIV CAVEAT (upper rows, cf. G4 `:10836-10840`): the `r = 0.25` sphere over
R31 EXITS the strip (`R31.y1 + 0.25 = 0.74 > 0.5`, proved as
`R31_sphere_025_exits` below), so the template's deriv premise cannot use
the `0.25`-sphere bridge there. The binding constraint is
`R31.y1 + r < 0.5`, i.e. `r < 0.01`; we take `r = 0.008`
(`0.49 + 0.008 = 0.498 < 0.5`, `R31_small_radius_admissible`), giving the
clean tier `M = 5600 / 0.008 = 700000` (`R31_M_eq`).
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 882000.002`).
-/

namespace BB_Row3SmallR

/-- R31 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R31_mem_bounds {w : ℂ} (hw : CentralCoverAssembly.R31.mem w) :
    -10 ≤ w.re ∧ w.re ≤ -7.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R31.x0 = -10 := CentralCoverAssembly.R31_x0
  have e1 : CentralCoverAssembly.R31.x1 = -7.5 := CentralCoverAssembly.R31_x1
  have e2 : CentralCoverAssembly.R31.y0 = 0.3 := CentralCoverAssembly.R31_y0
  have e3 : CentralCoverAssembly.R31.y1 = 0.49 := CentralCoverAssembly.R31_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R31 point lies in the open strip (deriv transfer applies). -/
theorem R31_strip_of_mem {w : ℂ} (hw : CentralCoverAssembly.R31.mem w) :
    -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
  obtain ⟨_, _, hy0, hy1⟩ := R31_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R31_small_radius_admissible : (0.49 : ℝ) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R31
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R31_sphere_025_exits : (0.5 : ℝ) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R31: `[-10.008,-7.492]`. -/
theorem R31_small_sphere_re_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ)) :
    -10.008 ≤ u.re ∧ u.re ≤ -7.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R31_mem_bounds hw
  have hdist : dist u w = (0.008 : ℝ) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : ℝ) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R31: `[0.292,0.498]`. -/
theorem R31_small_sphere_im_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R31_mem_bounds hw
  have hdist : dist u w = (0.008 : ℝ) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : ℝ) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : ℝ) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R31 stays strictly inside the strip
(`[0.292,0.498] ⊂ (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R31_small_sphere_mem_strip {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ)) :
    -(1 / 2 : ℝ) < u.im ∧ u.im < (1 / 2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := R31_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 pilot cell R31:
from a single closed-ball sup `C` over
`closedBall R31.center (R31.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R31.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R31_uniform_deriv_of_closedBall_bound (C : ℝ)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R31.center
      (CentralCoverAssembly.R31.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R31.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R31 0.008 C (by norm_num)
    (fun w hw => R31_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R31 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`; true sup `≈ 55.2`). -/
def R31_poly_upper_obligation : Prop :=
  ∀ s : ℂ, (0.001 : ℝ) ≤ s.re → s.re ≤ (0.21 : ℝ) →
    (-10.01 : ℝ) ≤ s.im → s.im ≤ (-7.49 : ℝ) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : ℝ)

/-- Pi-upper obligation (value `1`: `pi_upper_R02_disc` shape, `:6396`;
its proof needs only `0 < s.re`). -/
def R31_pi_upper_obligation : Prop :=
  ∀ s : ℂ, (0.001 : ℝ) ≤ s.re → s.re ≤ (0.21 : ℝ) →
    (-10.01 : ℝ) ≤ s.im → s.im ≤ (-7.49 : ℝ) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : ℝ)

/-- Gamma-upper obligation (value `10`: `RowFE_realGamma_0105_le` value,
`interval_arith.lean:31125`, row-`0.105` family; true sup is `O(0.01)` by
Im-decay since `|s.im| ≥ 7.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R31_gamma_upper_obligation : Prop :=
  ∀ s : ℂ, (0.001 : ℝ) ≤ s.re → s.re ≤ (0.21 : ℝ) →
    (-10.01 : ℝ) ≤ s.im → s.im ≤ (-7.49 : ℝ) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : ℝ)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|ζ| = O(1)` on this rect). -/
def R31_zeta_upper_obligation : Prop :=
  ∀ s : ℂ, (0.001 : ℝ) ≤ s.re → s.re ≤ (0.21 : ℝ) →
    (-10.01 : ℝ) ≤ s.im → s.im ≤ (-7.49 : ℝ) →
    ‖zeta s‖ ≤ (10 : ℝ)

/-- `s = 1/2 + I*u` coordinates for `u` on an R31 `0.008`-sphere:
`s.re ∈ [0.001,0.21]`, `s.im ∈ [-10.01,-7.49]`
(tight rect `[0.002,0.208] × [-10.008,-7.492]`, loosened for clean numerals). -/
theorem R31_s_of_small_sphere_re_im {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ)) :
    0.001 ≤ ((1 / 2 : ℂ) + Complex.I * u).re ∧
    ((1 / 2 : ℂ) + Complex.I * u).re ≤ 0.21 ∧
    -10.01 ≤ ((1 / 2 : ℂ) + Complex.I * u).im ∧
    ((1 / 2 : ℂ) + Complex.I * u).im ≤ -7.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R31_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R31_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : ℂ) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : ℂ) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R31_C_eq : (56 : ℝ) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R31_M_eq : (5600 : ℝ) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R31 small-sphere point:
`‖ξ‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R31_xiShifted_upper_of_factor_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ))
    (hP : R31_poly_upper_obligation) (hPi : R31_pi_upper_obligation)
    (hG : R31_gamma_upper_obligation) (hZ : R31_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R31_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : ℝ) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R31_entire_upper_of_factor_bounds {w u : ℂ}
    (hw : CentralCoverAssembly.R31.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : ℝ))
    (hP : R31_poly_upper_obligation) (hPi : R31_pi_upper_obligation)
    (hG : R31_gamma_upper_obligation) (hZ : R31_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R31_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R31_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R31 `0.008`-spheres from the four obligations. -/
theorem R31_uniform_sphere_bound
    (hP : R31_poly_upper_obligation) (hPi : R31_pi_upper_obligation)
    (hG : R31_gamma_upper_obligation) (hZ : R31_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R31.mem w → ∀ z ∈ Metric.sphere w (0.008 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R31_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 pilot deriv bound: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R31_deriv_bound_of_factor_bounds
    (hP : R31_poly_upper_obligation) (hPi : R31_pi_upper_obligation)
    (hG : R31_gamma_upper_obligation) (hZ : R31_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R31.mem w → ‖deriv xiShifted w‖ ≤ (700000 : ℝ) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R31 0.008 5600
    (by norm_num) (fun w hw => R31_strip_of_mem hw)
    (R31_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : ℝ) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R31 `s`-plane center `s = 1/2 + I * R31.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC31 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R31.center

/-- R31 center coordinates. -/
theorem R31_center_eq :
    CentralCoverAssembly.R31.center =
      (((-8.75 : ℝ) : ℂ)) + Complex.I * (((0.395 : ℝ) : ℂ)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R31_x0, CentralCoverAssembly.R31_x1,
      CentralCoverAssembly.R31_y0, CentralCoverAssembly.R31_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R31_x0, CentralCoverAssembly.R31_x1,
      CentralCoverAssembly.R31_y0, CentralCoverAssembly.R31_y1]
    simp
    norm_num

/-- `Re sC31 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC31_re : sC31.re = 0.105 := by
  unfold sC31
  rw [R31_center_eq]
  simp
  norm_num

/-- `Im sC31 = -8.75`. -/
theorem sC31_im : sC31.im = -8.75 := by
  unfold sC31
  rw [R31_center_eq]
  simp

/-- (3) Row-3 pilot closure: R31 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta ≥ 0.002 + 700000 * 1.26 = 882000.002`). -/
theorem R31_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC31‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC31‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC31‖)
    (hZeta : Azeta ≤ ‖zeta sC31‖)
    (hP : R31_poly_upper_obligation) (hPi : R31_pi_upper_obligation)
    (hG : R31_gamma_upper_obligation) (hZ : R31_zeta_upper_obligation)
    (hThresh : (0.002 : ℝ) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-10, -7.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R31.center =
      sC31 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R31.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : ℝ) :=
    R31_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R31.radius ≤ (1.26 : ℝ) :=
    le_of_lt CentralCoverAssembly.R31_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R31 sC31 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R31_strip_lo CentralCoverAssembly.R31_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BB_Row3SmallR

#print axioms BB_Row3SmallR.R31_uniform_deriv_of_closedBall_bound
#print axioms BB_Row3SmallR.R31_deriv_bound_of_factor_bounds
#print axioms BB_Row3SmallR.R31_closed_of_smallR_factorBounds
/-! ## BD row-3 shared + R32 small-r packaging (door-3 rollout premise, Agent BD tail)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`
  (`M = C / r` from per-`w` sphere sups);
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`
  (`M = C / r` from one closed-ball sup via
  `sphere_subset_closedBall_of_rect_mem` `:6213` +
  `Rect2D.norm_sub_center_le_radius` `rh_certificate_infra.lean:52`).
* `CentralCoverAssembly.R32` (`(-8,-5.5,0.3,0.49)`) -> `:4261`;
  `R32_x0/x1/y0/y1` -> `:4264-4267`; `R32_strip_lo/hi` -> `:4272-4273`;
  `R32_radius_lt` (`< 1.26`) -> `:4288`; `R32_mem_gridFine` -> `:4291`.
* `AX_CellTemplate.CellClosed_of_factorBounds` (generic per-cell template) ->
  `:10676`; `R02_recovers_AU_163_002` (pilot recovery pattern) -> `:10710`.
* Quoted sup values (obligations only, no import of `interval_arith`, which
  imports this file -- AO/AU/BB pattern, cf. `:9957-9965` and BB `:9901-9911`):
  poly `56` (edge-strip poly-56 tier, cf. `:6699`);
  pi `1` (`DerivCauchyBridge.pi_upper_R02_disc`, `:6396`);
  Gamma `10` (`RowFE_realGamma_0105_le`, `interval_arith.lean:31125`,
  row-`0.105` family);
  zeta `10` (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).
  `R02GammaDisc.gammaOf_upper_disc_R02` (`interval_arith.lean:32316`,
  `<= 0.097`) is R02-rect-only (`Re in [0.05,0.74]`, `Im in [-8.25,-5.25]`)
  and NOT reused here: the row-3 small-`r` `s`-rect below
  (`Re in [0.001,0.21]`, `Im in [-8.01,-5.49]` for R32) is disjoint from it.

DERIV CAVEAT (upper rows, cf. G4 `:10836-10840`): the `r = 0.25` sphere over
R32 EXITS the strip (`R32.y1 + 0.25 = 0.74 > 0.5`, proved as
`R32_sphere_025_exits` below), so the template's deriv premise cannot use
the `0.25`-sphere bridge there. The binding constraint is
`R32.y1 + r < 0.5`, i.e. `r < 0.01`; we take `r = 0.008`
(`0.49 + 0.008 = 0.498 < 0.5`, `R32_small_radius_admissible`), giving the
clean tier `M = 5600 / 0.008 = 700000` (`R32_M_eq`), same as R31's
`R31_M_eq` since the row-3 `y`-interval is identical.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.002 + 700000 * 1.26 = 882000.002`).
Shared per-row facts (`pi <= 1`, `Real.Gamma 0.105 <= 10`-shape) live once in
`BD_Row3Shared` below, not copied per cell.
-/

namespace BD_Row3Shared

/-- Shared row-3 pi upper `||piOf s|| <= 1` for `0.001 <= s.re`
(mirrors `DerivCauchyBridge.pi_upper_R02_disc` `:6396` with the row-3
`s`-rect floor `0.001`; proof needs only `0 <= s.re`). -/
theorem pi_upper_row3 {s : Complex} (hre_lo : (0.001 : Real) <= s.re) :
    ‖DerivCauchyBridge.piOf s‖ ≤ 1 := by
  unfold DerivCauchyBridge.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  have hle : (-(s / 2)).re ≤ 0 := by
    rw [hneg, h2]
    linarith
  have hpi1 : (1 : Real) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact Real.rpow_le_one_of_one_le_of_nonpos hpi1 hle

/-- Shared Real-Gamma cap at `0.105`: `Real.Gamma 0.105 <= 10`
(mirrors `RowFE_realGamma_0105_le`, `interval_arith.lean:31125`, row-`0.105`
family; quoted as the `10` in per-cell Gamma obligations, proved once here). -/
theorem realGamma_0105_le_mirror : Real.Gamma (0.105 : Real) ≤ 10 := by
  have hx_pos : (0 : Real) < 0.105 := by norm_num
  have hy_mem1 : (1 : Real) ∈ Set.Ioi (0 : Real) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : Real) ∈ Set.Ioi (0 : Real) := Set.mem_Ioi.mpr (by norm_num)
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : Real) ≤ 2 - ((0.105 : Real) + 1) := by norm_num
  have hb_nn : (0 : Real) ≤ ((0.105 : Real) + 1) - 1 := by norm_num
  have hab : ((2 : Real) - ((0.105 : Real) + 1)) + (((0.105 : Real) + 1) - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : ((2 : Real) - ((0.105 : Real) + 1)) * 1 + (((0.105 : Real) + 1) - 1) * 2 =
      (0.105 : Real) + 1 := by ring
  rw [heq] at h
  have hrhs : ((2 : Real) - ((0.105 : Real) + 1)) * 1 + (((0.105 : Real) + 1) - 1) * 1 =
      (1 : Real) := by ring
  rw [hrhs] at h
  have hne : (0.105 : Real) ≠ 0 := by norm_num
  have hadd := Real.Gamma_add_one hne
  rw [hadd] at h
  have hfin : Real.Gamma (0.105 : Real) ≤ 1 / 0.105 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h
  have hfrac : (1 : Real) / 0.105 ≤ 10 := by norm_num
  exact le_trans hfin hfrac

end BD_Row3Shared

#print axioms BD_Row3Shared.pi_upper_row3
#print axioms BD_Row3Shared.realGamma_0105_le_mirror

namespace BD_R32SmallR

/-- R32 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R32_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R32.mem w) :
    -8 ≤ w.re ∧ w.re ≤ -5.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R32.x0 = -8 := CentralCoverAssembly.R32_x0
  have e1 : CentralCoverAssembly.R32.x1 = -5.5 := CentralCoverAssembly.R32_x1
  have e2 : CentralCoverAssembly.R32.y0 = 0.3 := CentralCoverAssembly.R32_y0
  have e3 : CentralCoverAssembly.R32.y1 = 0.49 := CentralCoverAssembly.R32_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R32 point lies in the open strip (deriv transfer applies). -/
theorem R32_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R32.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R32_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R32_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R32
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R32_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R32: `[-8.008,-5.492]`. -/
theorem R32_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -8.008 ≤ u.re ∧ u.re ≤ -5.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R32_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R32: `[0.292,0.498]`. -/
theorem R32_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R32_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R32 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R32_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R32_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R32:
from a single closed-ball sup `C` over
`closedBall R32.center (R32.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R32.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R32_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R32.center
      (CentralCoverAssembly.R32.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R32.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R32 0.008 C (by norm_num)
    (fun w hw => R32_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R32 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`; true sup is below R31's
since `|s.im| <= 8.01 < 10.01`). -/
def R32_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-8.01 : Real) ≤ s.im → s.im ≤ (-5.49 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: `pi_upper_R02_disc` shape, `:6396`,
shared proof `BD_Row3Shared.pi_upper_row3`;
its proof needs only `0 < s.re`). -/
def R32_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-8.01 : Real) ≤ s.im → s.im ≤ (-5.49 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: `RowFE_realGamma_0105_le` value,
`interval_arith.lean:31125`, row-`0.105` family shared as
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 5.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R32_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-8.01 : Real) ≤ s.im → s.im ≤ (-5.49 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R32_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-8.01 : Real) ≤ s.im → s.im ≤ (-5.49 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R32 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-8.01,-5.49]`
(tight rect `[0.002,0.208] x [-8.008,-5.492]`, loosened for clean numerals). -/
theorem R32_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -8.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ -5.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R32_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R32_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R32_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R32_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R32 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R32_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R32_poly_upper_obligation) (hPi : R32_pi_upper_obligation)
    (hG : R32_gamma_upper_obligation) (hZ : R32_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R32_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R32_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R32.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R32_poly_upper_obligation) (hPi : R32_pi_upper_obligation)
    (hG : R32_gamma_upper_obligation) (hZ : R32_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R32_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R32_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R32 `0.008`-spheres from the four obligations. -/
theorem R32_uniform_sphere_bound
    (hP : R32_poly_upper_obligation) (hPi : R32_pi_upper_obligation)
    (hG : R32_gamma_upper_obligation) (hZ : R32_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R32.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R32_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R32: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R32_deriv_bound_of_factor_bounds
    (hP : R32_poly_upper_obligation) (hPi : R32_pi_upper_obligation)
    (hG : R32_gamma_upper_obligation) (hZ : R32_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R32.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R32 0.008 5600
    (by norm_num) (fun w hw => R32_strip_of_mem hw)
    (R32_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R32 `s`-plane center `s = 1/2 + I * R32.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC32 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R32.center

/-- R32 center coordinates. -/
theorem R32_center_eq :
    CentralCoverAssembly.R32.center =
      (((-6.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R32_x0, CentralCoverAssembly.R32_x1,
      CentralCoverAssembly.R32_y0, CentralCoverAssembly.R32_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R32_x0, CentralCoverAssembly.R32_x1,
      CentralCoverAssembly.R32_y0, CentralCoverAssembly.R32_y1]
    simp
    norm_num

/-- `Re sC32 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC32_re : sC32.re = 0.105 := by
  unfold sC32
  rw [R32_center_eq]
  simp
  norm_num

/-- `Im sC32 = -6.75`. -/
theorem sC32_im : sC32.im = -6.75 := by
  unfold sC32
  rw [R32_center_eq]
  simp

/-- (3) Row-3 closure for R32 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.002 + 700000 * 1.26 = 882000.002`). -/
theorem R32_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC32‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC32‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC32‖)
    (hZeta : Azeta ≤ ‖zeta sC32‖)
    (hP : R32_poly_upper_obligation) (hPi : R32_pi_upper_obligation)
    (hG : R32_gamma_upper_obligation) (hZ : R32_zeta_upper_obligation)
    (hThresh : (0.002 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R32.center =
      sC32 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R32.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R32_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R32.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R32_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R32 sC32 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R32_strip_lo CentralCoverAssembly.R32_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R32SmallR

#print axioms BD_Row3Shared.pi_upper_row3
#print axioms BD_Row3Shared.realGamma_0105_le_mirror
#print axioms BD_R32SmallR.R32_uniform_deriv_of_closedBall_bound
#print axioms BD_R32SmallR.R32_deriv_bound_of_factor_bounds
#print axioms BD_R32SmallR.R32_closed_of_smallR_factorBounds

/-! ## BG row-3 R33+R34 small-r packaging (door-3 rollout, mid tier)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`
  (`sphere_subset_closedBall_of_rect_mem` `:6213`).
* `CentralCoverAssembly.R33` (`(-6,-3.5,0.3,0.49)`) -> `:4345`;
  `R33_x0/x1/y0/y1` -> `:4348-4351`; `R33_strip_lo/hi` -> `:4356-4357`;
  `R33_radius_lt` (`< 1.26`) -> `:4372`; `R33_mem_gridFine` -> `:4375`;
  `R33_leaf_obligations (0.05,0.07)` -> `:4385`.
* `CentralCoverAssembly.R34` (`(-4,-1.5,0.3,0.49)`) -> `:4429`;
  `R34_x0/x1/y0/y1` -> `:4432-4435`; `R34_strip_lo/hi` -> `:4440-4441`;
  `R34_radius_lt` (`< 1.26`) -> `:4456`; `R34_mem_gridFine` -> `:4459`;
  `R34_leaf_obligations (0.05,0.07)` -> `:4469`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`;
  `R02_recovers_AU_163_002` (pilot recovery pattern) -> `:10710`.
* Quoted sup values (obligations only, no import of `interval_arith`, which
  imports this file -- BB/BD pattern): poly `56` (edge-strip poly-56 tier,
  cf. `:6699`); pi `1` (shared `BD_Row3Shared.pi_upper_row3`);
  Gamma `10` (shared `BD_Row3Shared.realGamma_0105_le_mirror`);
  zeta `10` (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).

DERIV CAVEAT (upper rows, cf. G4 `:10836-10840`): `r = 0.25` spheres exit the
strip (`0.49 + 0.25 = 0.74 > 0.5`, proved per cell as `RXX_sphere_025_exits`),
so the template deriv premise uses `r = 0.008`
(`0.49 + 0.008 = 0.498 < 0.5`, `RXX_small_radius_admissible`), giving the
clean tier `M = 5600 / 0.008 = 700000` (`RXX_M_eq`), same as R31/R32.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at mid tier `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`).
Shared per-row facts live once in `BD_Row3Shared`, reused here, not copied.
-/

namespace BG_R33SmallR

/-- R33 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R33_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R33.mem w) :
    -6 ≤ w.re ∧ w.re ≤ -3.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R33.x0 = -6 := CentralCoverAssembly.R33_x0
  have e1 : CentralCoverAssembly.R33.x1 = -3.5 := CentralCoverAssembly.R33_x1
  have e2 : CentralCoverAssembly.R33.y0 = 0.3 := CentralCoverAssembly.R33_y0
  have e3 : CentralCoverAssembly.R33.y1 = 0.49 := CentralCoverAssembly.R33_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R33 point lies in the open strip (deriv transfer applies). -/
theorem R33_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R33.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R33_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R33_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R33
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R33_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R33: `[-6.008,-3.492]`. -/
theorem R33_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -6.008 ≤ u.re ∧ u.re ≤ -3.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R33_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R33: `[0.292,0.498]`. -/
theorem R33_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R33_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R33 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R33_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R33_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R33:
from a single closed-ball sup `C` over
`closedBall R33.center (R33.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R33.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R33_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R33.center
      (CentralCoverAssembly.R33.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R33 0.008 C (by norm_num)
    (fun w hw => R33_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R33 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R33_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R33_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 3.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R33_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R33_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R33 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-6.01,-3.49]`
(tight rect `[0.002,0.208] x [-6.008,-3.492]`, loosened for clean numerals). -/
theorem R33_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -6.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ -3.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R33_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R33_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R33_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R33_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R33 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R33_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R33_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R33_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R33_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R33_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R33 `0.008`-spheres from the four obligations. -/
theorem R33_uniform_sphere_bound
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R33.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R33_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R33: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R33_deriv_bound_of_factor_bounds
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R33 0.008 5600
    (by norm_num) (fun w hw => R33_strip_of_mem hw)
    (R33_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R33 `s`-plane center `s = 1/2 + I * R33.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC33 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R33.center

/-- R33 center coordinates. -/
theorem R33_center_eq :
    CentralCoverAssembly.R33.center =
      (((-4.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R33_x0, CentralCoverAssembly.R33_x1,
      CentralCoverAssembly.R33_y0, CentralCoverAssembly.R33_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R33_x0, CentralCoverAssembly.R33_x1,
      CentralCoverAssembly.R33_y0, CentralCoverAssembly.R33_y1]
    simp
    norm_num

/-- `Re sC33 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC33_re : sC33.re = 0.105 := by
  unfold sC33
  rw [R33_center_eq]
  simp
  norm_num

/-- `Im sC33 = -4.75`. -/
theorem sC33_im : sC33.im = -4.75 := by
  unfold sC33
  rw [R33_center_eq]
  simp

/-- (3) Row-3 closure for R33 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R33_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC33‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC33‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC33‖)
    (hZeta : Azeta ≤ ‖zeta sC33‖)
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-6, -3.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R33.center =
      sC33 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R33.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R33_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R33.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R33_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R33 sC33 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R33_strip_lo CentralCoverAssembly.R33_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R33SmallR

#print axioms BG_R33SmallR.R33_uniform_deriv_of_closedBall_bound
#print axioms BG_R33SmallR.R33_deriv_bound_of_factor_bounds
#print axioms BG_R33SmallR.R33_closed_of_smallR_factorBounds

namespace BG_R34SmallR

/-- R34 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R34_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R34.mem w) :
    -4 ≤ w.re ∧ w.re ≤ -1.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R34.x0 = -4 := CentralCoverAssembly.R34_x0
  have e1 : CentralCoverAssembly.R34.x1 = -1.5 := CentralCoverAssembly.R34_x1
  have e2 : CentralCoverAssembly.R34.y0 = 0.3 := CentralCoverAssembly.R34_y0
  have e3 : CentralCoverAssembly.R34.y1 = 0.49 := CentralCoverAssembly.R34_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R34 point lies in the open strip (deriv transfer applies). -/
theorem R34_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R34.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R34_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R34_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R34
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R34_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R34: `[-4.008,-1.492]`. -/
theorem R34_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -4.008 ≤ u.re ∧ u.re ≤ -1.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R34_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R34: `[0.292,0.498]`. -/
theorem R34_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R34_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R34 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R34_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R34_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R34:
from a single closed-ball sup `C` over
`closedBall R34.center (R34.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R34.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R34_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R34.center
      (CentralCoverAssembly.R34.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R34 0.008 C (by norm_num)
    (fun w hw => R34_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R34 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R34_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R34_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 1.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R34_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R34_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R34 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-4.01,-1.49]`
(tight rect `[0.002,0.208] x [-4.008,-1.492]`, loosened for clean numerals). -/
theorem R34_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -4.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ -1.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R34_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R34_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R34_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R34_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R34 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R34_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R34_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R34_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R34_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R34_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R34 `0.008`-spheres from the four obligations. -/
theorem R34_uniform_sphere_bound
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R34.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R34_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R34: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R34_deriv_bound_of_factor_bounds
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R34 0.008 5600
    (by norm_num) (fun w hw => R34_strip_of_mem hw)
    (R34_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R34 `s`-plane center `s = 1/2 + I * R34.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC34 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R34.center

/-- R34 center coordinates. -/
theorem R34_center_eq :
    CentralCoverAssembly.R34.center =
      (((-2.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R34_x0, CentralCoverAssembly.R34_x1,
      CentralCoverAssembly.R34_y0, CentralCoverAssembly.R34_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R34_x0, CentralCoverAssembly.R34_x1,
      CentralCoverAssembly.R34_y0, CentralCoverAssembly.R34_y1]
    simp
    norm_num

/-- `Re sC34 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC34_re : sC34.re = 0.105 := by
  unfold sC34
  rw [R34_center_eq]
  simp
  norm_num

/-- `Im sC34 = -2.75`. -/
theorem sC34_im : sC34.im = -2.75 := by
  unfold sC34
  rw [R34_center_eq]
  simp

/-- (3) Row-3 closure for R34 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R34_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC34‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC34‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC34‖)
    (hZeta : Azeta ≤ ‖zeta sC34‖)
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-4, -1.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R34.center =
      sC34 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R34.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R34_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R34.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R34_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R34 sC34 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R34_strip_lo CentralCoverAssembly.R34_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R34SmallR

#print axioms BG_R33SmallR.R33_uniform_deriv_of_closedBall_bound
#print axioms BG_R33SmallR.R33_deriv_bound_of_factor_bounds
#print axioms BG_R33SmallR.R33_closed_of_smallR_factorBounds
#print axioms BG_R34SmallR.R34_uniform_deriv_of_closedBall_bound
#print axioms BG_R34SmallR.R34_deriv_bound_of_factor_bounds
#print axioms BG_R34SmallR.R34_closed_of_smallR_factorBounds

/-! ## BG row-3 R35+R36 small-r packaging (door-3 rollout, inner tier)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`.
* `CentralCoverAssembly.R35` (`(-2,0.5,0.3,0.49)`) -> `:4513`;
  `R35_x0/x1/y0/y1` -> `:4516-4519`; `R35_strip_lo/hi` -> `:4524-4525`;
  `R35_radius_lt` (`< 1.26`) -> `:4540`; `R35_mem_gridFine` -> `:4543`;
  `R35_leaf_obligations (0.15,0.06)` -> `:4553`.
* `CentralCoverAssembly.R36` (`(0,2.5,0.3,0.49)`) -> `:4597`;
  `R36_x0/x1/y0/y1` -> `:4600-4603`; `R36_strip_lo/hi` -> `:4608-4609`;
  `R36_radius_lt` (`< 1.26`) -> `:4624`; `R36_mem_gridFine` -> `:4627`;
  `R36_leaf_obligations (0.15,0.06)` -> `:4637`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Quoted sup values (obligations only, no import of `interval_arith`):
  poly `56`; pi `1` (shared `BD_Row3Shared.pi_upper_row3`);
  Gamma `10` (shared `BD_Row3Shared.realGamma_0105_le_mirror`);
  zeta `10`. Same `r = 0.008`, `C = 5600`, `M = 700000` as R31-R34.
  Inner tier: `hThresh` stays a premise needing
  `Apoly * Api * Agam * Azeta >= 0.15 + 700000 * 1.26 = 882000.15`.
-/

namespace BG_R35SmallR

/-- R35 `mem` unpacked to numeric bounds. -/
theorem R35_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R35.mem w) :
    -2 ≤ w.re ∧ w.re ≤ 0.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R35.x0 = -2 := CentralCoverAssembly.R35_x0
  have e1 : CentralCoverAssembly.R35.x1 = 0.5 := CentralCoverAssembly.R35_x1
  have e2 : CentralCoverAssembly.R35.y0 = 0.3 := CentralCoverAssembly.R35_y0
  have e3 : CentralCoverAssembly.R35.y1 = 0.49 := CentralCoverAssembly.R35_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R35 point lies in the open strip (deriv transfer applies). -/
theorem R35_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R35.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R35_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R35_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R35. -/
theorem R35_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R35: `[-2.008,0.508]`. -/
theorem R35_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -2.008 ≤ u.re ∧ u.re ≤ 0.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R35_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R35: `[0.292,0.498]`. -/
theorem R35_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R35_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R35 stays strictly inside the strip. -/
theorem R35_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R35_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R35. -/
theorem R35_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R35.center
      (CentralCoverAssembly.R35.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R35 0.008 C (by norm_num)
    (fun w hw => R35_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R35 small-`r` disc `s`-rect (value `56`). -/
def R35_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R35_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R35_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R35_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R35 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-2.01,0.51]`
(tight `[-2.008,0.508]`, loosened for clean numerals). -/
theorem R35_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -2.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 0.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R35_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R35_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R35_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R35_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R35 small-sphere point. -/
theorem R35_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R35_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R35_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R35_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R35_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R35 `0.008`-spheres from the four obligations. -/
theorem R35_uniform_sphere_bound
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R35.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R35_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R35: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R35_deriv_bound_of_factor_bounds
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R35 0.008 5600
    (by norm_num) (fun w hw => R35_strip_of_mem hw)
    (R35_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R35 `s`-plane center `s = 1/2 + I * R35.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC35 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R35.center

/-- R35 center coordinates (`xmid = -0.75`). -/
theorem R35_center_eq :
    CentralCoverAssembly.R35.center =
      (((-0.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R35_x0, CentralCoverAssembly.R35_x1,
      CentralCoverAssembly.R35_y0, CentralCoverAssembly.R35_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R35_x0, CentralCoverAssembly.R35_x1,
      CentralCoverAssembly.R35_y0, CentralCoverAssembly.R35_y1]
    simp
    norm_num

/-- `Re sC35 = 0.105`. -/
theorem sC35_re : sC35.re = 0.105 := by
  unfold sC35
  rw [R35_center_eq]
  simp
  norm_num

/-- `Im sC35 = -0.75`. -/
theorem sC35_im : sC35.im = -0.75 := by
  unfold sC35
  rw [R35_center_eq]
  simp

/-- (3) Row-3 closure for R35 through `AX_CellTemplate.CellClosed_of_factorBounds`
(inner tier `eps = 0.15`; threshold `882000.15` stays a premise). -/
theorem R35_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC35‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC35‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC35‖)
    (hZeta : Azeta ≤ ‖zeta sC35‖)
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation)
    (hThresh : (0.15 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R35.center =
      sC35 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R35.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R35_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R35.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R35_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R35 sC35 hsC
    Apoly Api Agam Azeta 0.15 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R35_strip_lo CentralCoverAssembly.R35_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R35SmallR

#print axioms BG_R35SmallR.R35_uniform_deriv_of_closedBall_bound
#print axioms BG_R35SmallR.R35_deriv_bound_of_factor_bounds
#print axioms BG_R35SmallR.R35_closed_of_smallR_factorBounds

namespace BG_R36SmallR

/-- R36 `mem` unpacked to numeric bounds. -/
theorem R36_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R36.mem w) :
    0 ≤ w.re ∧ w.re ≤ 2.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R36.x0 = 0 := CentralCoverAssembly.R36_x0
  have e1 : CentralCoverAssembly.R36.x1 = 2.5 := CentralCoverAssembly.R36_x1
  have e2 : CentralCoverAssembly.R36.y0 = 0.3 := CentralCoverAssembly.R36_y0
  have e3 : CentralCoverAssembly.R36.y1 = 0.49 := CentralCoverAssembly.R36_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R36 point lies in the open strip (deriv transfer applies). -/
theorem R36_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R36.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R36_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R36_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R36. -/
theorem R36_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R36: `[-0.008,2.508]`. -/
theorem R36_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -0.008 ≤ u.re ∧ u.re ≤ 2.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R36_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R36: `[0.292,0.498]`. -/
theorem R36_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R36_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R36 stays strictly inside the strip. -/
theorem R36_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R36_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R36. -/
theorem R36_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R36.center
      (CentralCoverAssembly.R36.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R36 0.008 C (by norm_num)
    (fun w hw => R36_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R36 small-`r` disc `s`-rect (value `56`). -/
def R36_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R36_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R36_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R36_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R36 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-0.01,2.51]`
(tight `[-0.008,2.508]`, loosened for clean numerals). -/
theorem R36_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -0.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 2.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R36_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R36_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R36_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R36_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R36 small-sphere point. -/
theorem R36_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R36_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R36_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R36_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R36_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R36 `0.008`-spheres from the four obligations. -/
theorem R36_uniform_sphere_bound
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R36.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R36_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R36: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R36_deriv_bound_of_factor_bounds
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R36 0.008 5600
    (by norm_num) (fun w hw => R36_strip_of_mem hw)
    (R36_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R36 `s`-plane center `s = 1/2 + I * R36.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC36 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R36.center

/-- R36 center coordinates (`xmid = 1.25`). -/
theorem R36_center_eq :
    CentralCoverAssembly.R36.center =
      (((1.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R36_x0, CentralCoverAssembly.R36_x1,
      CentralCoverAssembly.R36_y0, CentralCoverAssembly.R36_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R36_x0, CentralCoverAssembly.R36_x1,
      CentralCoverAssembly.R36_y0, CentralCoverAssembly.R36_y1]
    simp
    norm_num

/-- `Re sC36 = 0.105`. -/
theorem sC36_re : sC36.re = 0.105 := by
  unfold sC36
  rw [R36_center_eq]
  simp
  norm_num

/-- `Im sC36 = 1.25`. -/
theorem sC36_im : sC36.im = 1.25 := by
  unfold sC36
  rw [R36_center_eq]
  simp

/-- (3) Row-3 closure for R36 through `AX_CellTemplate.CellClosed_of_factorBounds`
(inner tier `eps = 0.15`; threshold `882000.15` stays a premise). -/
theorem R36_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC36‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC36‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC36‖)
    (hZeta : Azeta ≤ ‖zeta sC36‖)
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation)
    (hThresh : (0.15 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R36.center =
      sC36 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R36.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R36_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R36.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R36_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R36 sC36 hsC
    Apoly Api Agam Azeta 0.15 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R36_strip_lo CentralCoverAssembly.R36_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R36SmallR

#print axioms BG_R35SmallR.R35_uniform_deriv_of_closedBall_bound
#print axioms BG_R35SmallR.R35_deriv_bound_of_factor_bounds
#print axioms BG_R35SmallR.R35_closed_of_smallR_factorBounds
#print axioms BG_R36SmallR.R36_uniform_deriv_of_closedBall_bound
#print axioms BG_R36SmallR.R36_deriv_bound_of_factor_bounds
#print axioms BG_R36SmallR.R36_closed_of_smallR_factorBounds

/-! ## BG row-3 R37+R38 small-r packaging (door-3 rollout, mid tier)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`.
* `CentralCoverAssembly.R37` (`(2,4.5,0.3,0.49)`) -> `:4681`;
  `R37_x0/x1/y0/y1` -> `:4684-4687`; `R37_strip_lo/hi` -> `:4692-4693`;
  `R37_radius_lt` (`< 1.26`) -> `:4708`; `R37_mem_gridFine` -> `:4711`;
  `R37_leaf_obligations (0.05,0.07)` -> `:4721`.
* `CentralCoverAssembly.R38` (`(4,6.5,0.3,0.49)`) -> `:4765`;
  `R38_x0/x1/y0/y1` -> `:4768-4771`; `R38_strip_lo/hi` -> `:4776-4777`;
  `R38_radius_lt` (`< 1.26`) -> `:4792`; `R38_mem_gridFine` -> `:4795`;
  `R38_leaf_obligations (0.05,0.07)` -> `:4805`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Quoted sup values (obligations only): poly `56`; pi `1`
  (shared `BD_Row3Shared.pi_upper_row3`); Gamma `10`
  (shared `BD_Row3Shared.realGamma_0105_le_mirror`); zeta `10`.
  Same `r = 0.008`, `C = 5600`, `M = 700000`. Mid tier threshold `882000.05`.
-/

namespace BG_R37SmallR

/-- R37 `mem` unpacked to numeric bounds. -/
theorem R37_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R37.mem w) :
    2 ≤ w.re ∧ w.re ≤ 4.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R37.x0 = 2 := CentralCoverAssembly.R37_x0
  have e1 : CentralCoverAssembly.R37.x1 = 4.5 := CentralCoverAssembly.R37_x1
  have e2 : CentralCoverAssembly.R37.y0 = 0.3 := CentralCoverAssembly.R37_y0
  have e3 : CentralCoverAssembly.R37.y1 = 0.49 := CentralCoverAssembly.R37_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R37 point lies in the open strip (deriv transfer applies). -/
theorem R37_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R37.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R37_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R37_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R37. -/
theorem R37_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R37: `[1.992,4.508]`. -/
theorem R37_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    1.992 ≤ u.re ∧ u.re ≤ 4.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R37_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R37: `[0.292,0.498]`. -/
theorem R37_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R37_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R37 stays strictly inside the strip. -/
theorem R37_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R37_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R37. -/
theorem R37_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R37.center
      (CentralCoverAssembly.R37.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R37 0.008 C (by norm_num)
    (fun w hw => R37_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R37 small-`r` disc `s`-rect (value `56`). -/
def R37_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R37_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R37_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R37_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R37 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [1.99,4.51]`
(tight `[1.992,4.508]`, loosened for clean numerals). -/
theorem R37_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    1.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 4.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R37_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R37_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R37_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R37_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R37 small-sphere point. -/
theorem R37_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R37_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R37_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R37_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R37_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R37 `0.008`-spheres from the four obligations. -/
theorem R37_uniform_sphere_bound
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R37.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R37_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R37: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R37_deriv_bound_of_factor_bounds
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R37 0.008 5600
    (by norm_num) (fun w hw => R37_strip_of_mem hw)
    (R37_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R37 `s`-plane center `s = 1/2 + I * R37.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC37 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R37.center

/-- R37 center coordinates (`xmid = 3.25`). -/
theorem R37_center_eq :
    CentralCoverAssembly.R37.center =
      (((3.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R37_x0, CentralCoverAssembly.R37_x1,
      CentralCoverAssembly.R37_y0, CentralCoverAssembly.R37_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R37_x0, CentralCoverAssembly.R37_x1,
      CentralCoverAssembly.R37_y0, CentralCoverAssembly.R37_y1]
    simp
    norm_num

/-- `Re sC37 = 0.105`. -/
theorem sC37_re : sC37.re = 0.105 := by
  unfold sC37
  rw [R37_center_eq]
  simp
  norm_num

/-- `Im sC37 = 3.25`. -/
theorem sC37_im : sC37.im = 3.25 := by
  unfold sC37
  rw [R37_center_eq]
  simp

/-- (3) Row-3 closure for R37 through `AX_CellTemplate.CellClosed_of_factorBounds`
(mid tier `eps = 0.05`; threshold `882000.05` stays a premise). -/
theorem R37_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC37‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC37‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC37‖)
    (hZeta : Azeta ≤ ‖zeta sC37‖)
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R37.center =
      sC37 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R37.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R37_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R37.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R37_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R37 sC37 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R37_strip_lo CentralCoverAssembly.R37_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R37SmallR

#print axioms BG_R37SmallR.R37_uniform_deriv_of_closedBall_bound
#print axioms BG_R37SmallR.R37_deriv_bound_of_factor_bounds
#print axioms BG_R37SmallR.R37_closed_of_smallR_factorBounds

namespace BG_R38SmallR

/-- R38 `mem` unpacked to numeric bounds. -/
theorem R38_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R38.mem w) :
    4 ≤ w.re ∧ w.re ≤ 6.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R38.x0 = 4 := CentralCoverAssembly.R38_x0
  have e1 : CentralCoverAssembly.R38.x1 = 6.5 := CentralCoverAssembly.R38_x1
  have e2 : CentralCoverAssembly.R38.y0 = 0.3 := CentralCoverAssembly.R38_y0
  have e3 : CentralCoverAssembly.R38.y1 = 0.49 := CentralCoverAssembly.R38_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R38 point lies in the open strip (deriv transfer applies). -/
theorem R38_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R38.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R38_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R38_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R38. -/
theorem R38_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R38: `[3.992,6.508]`. -/
theorem R38_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    3.992 ≤ u.re ∧ u.re ≤ 6.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R38_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R38: `[0.292,0.498]`. -/
theorem R38_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R38_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R38 stays strictly inside the strip. -/
theorem R38_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R38_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R38. -/
theorem R38_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R38.center
      (CentralCoverAssembly.R38.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R38 0.008 C (by norm_num)
    (fun w hw => R38_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R38 small-`r` disc `s`-rect (value `56`). -/
def R38_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R38_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R38_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R38_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R38 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [3.99,6.51]`
(tight `[3.992,6.508]`, loosened for clean numerals). -/
theorem R38_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    3.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 6.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R38_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R38_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R38_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R38_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R38 small-sphere point. -/
theorem R38_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R38_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R38_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R38_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R38_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R38 `0.008`-spheres from the four obligations. -/
theorem R38_uniform_sphere_bound
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R38.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R38_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R38: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R38_deriv_bound_of_factor_bounds
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R38 0.008 5600
    (by norm_num) (fun w hw => R38_strip_of_mem hw)
    (R38_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R38 `s`-plane center `s = 1/2 + I * R38.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC38 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R38.center

/-- R38 center coordinates (`xmid = 5.25`). -/
theorem R38_center_eq :
    CentralCoverAssembly.R38.center =
      (((5.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R38_x0, CentralCoverAssembly.R38_x1,
      CentralCoverAssembly.R38_y0, CentralCoverAssembly.R38_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R38_x0, CentralCoverAssembly.R38_x1,
      CentralCoverAssembly.R38_y0, CentralCoverAssembly.R38_y1]
    simp
    norm_num

/-- `Re sC38 = 0.105`. -/
theorem sC38_re : sC38.re = 0.105 := by
  unfold sC38
  rw [R38_center_eq]
  simp
  norm_num

/-- `Im sC38 = 5.25`. -/
theorem sC38_im : sC38.im = 5.25 := by
  unfold sC38
  rw [R38_center_eq]
  simp

/-- (3) Row-3 closure for R38 through `AX_CellTemplate.CellClosed_of_factorBounds`
(mid tier `eps = 0.05`; threshold `882000.05` stays a premise). -/
theorem R38_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC38‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC38‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC38‖)
    (hZeta : Azeta ≤ ‖zeta sC38‖)
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R38.center =
      sC38 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R38.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R38_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R38.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R38_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R38 sC38 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R38_strip_lo CentralCoverAssembly.R38_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R38SmallR

#print axioms BG_R37SmallR.R37_uniform_deriv_of_closedBall_bound
#print axioms BG_R37SmallR.R37_deriv_bound_of_factor_bounds
#print axioms BG_R37SmallR.R37_closed_of_smallR_factorBounds
#print axioms BG_R38SmallR.R38_uniform_deriv_of_closedBall_bound
#print axioms BG_R38SmallR.R38_deriv_bound_of_factor_bounds
#print axioms BG_R38SmallR.R38_closed_of_smallR_factorBounds

/-! ## BG row-3 R39+R40 small-r packaging (door-3 rollout, outer tier)

GREP-first record (2026-09-04, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`.
* `CentralCoverAssembly.R39` (`(6,8.5,0.3,0.49)`) -> `:4849`;
  `R39_x0/x1/y0/y1` -> `:4852-4855`; `R39_strip_lo/hi` -> `:4860-4861`;
  `R39_radius_lt` (`< 1.26`) -> `:4876`; `R39_mem_gridFine` -> `:4879`;
  `R39_leaf_obligations (0.002,0.05)` -> `:4889`.
* `CentralCoverAssembly.R40` (`(7.5,10,0.3,0.49)`) -> `:4933`;
  `R40_x0/x1/y0/y1` -> `:4936-4939`; `R40_strip_lo/hi` -> `:4944-4945`;
  `R40_radius_lt` (`< 1.26`) -> `:4960`; `R40_mem_gridFine` -> `:4963`;
  `R40_leaf_obligations (0.002,0.05)` -> `:4973`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Quoted sup values (obligations only): poly `56`; pi `1`
  (shared `BD_Row3Shared.pi_upper_row3`); Gamma `10`
  (shared `BD_Row3Shared.realGamma_0105_le_mirror`); zeta `10`.
  Same `r = 0.008`, `C = 5600`, `M = 700000`. Outer tier threshold `882000.002`.
-/

namespace BG_R39SmallR

/-- R39 `mem` unpacked to numeric bounds. -/
theorem R39_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R39.mem w) :
    6 ≤ w.re ∧ w.re ≤ 8.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R39.x0 = 6 := CentralCoverAssembly.R39_x0
  have e1 : CentralCoverAssembly.R39.x1 = 8.5 := CentralCoverAssembly.R39_x1
  have e2 : CentralCoverAssembly.R39.y0 = 0.3 := CentralCoverAssembly.R39_y0
  have e3 : CentralCoverAssembly.R39.y1 = 0.49 := CentralCoverAssembly.R39_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R39 point lies in the open strip (deriv transfer applies). -/
theorem R39_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R39.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R39_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R39_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R39. -/
theorem R39_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R39: `[5.992,8.508]`. -/
theorem R39_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    5.992 ≤ u.re ∧ u.re ≤ 8.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R39_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R39: `[0.292,0.498]`. -/
theorem R39_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R39_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R39 stays strictly inside the strip. -/
theorem R39_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R39_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R39. -/
theorem R39_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R39.center
      (CentralCoverAssembly.R39.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R39 0.008 C (by norm_num)
    (fun w hw => R39_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R39 small-`r` disc `s`-rect (value `56`). -/
def R39_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R39_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R39_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R39_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R39 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [5.99,8.51]`
(tight `[5.992,8.508]`, loosened for clean numerals). -/
theorem R39_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    5.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 8.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R39_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R39_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R39_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R39_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R39 small-sphere point. -/
theorem R39_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R39_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R39_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R39_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R39_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R39 `0.008`-spheres from the four obligations. -/
theorem R39_uniform_sphere_bound
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R39.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R39_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R39: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R39_deriv_bound_of_factor_bounds
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R39 0.008 5600
    (by norm_num) (fun w hw => R39_strip_of_mem hw)
    (R39_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R39 `s`-plane center `s = 1/2 + I * R39.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC39 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R39.center

/-- R39 center coordinates (`xmid = 7.25`). -/
theorem R39_center_eq :
    CentralCoverAssembly.R39.center =
      (((7.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R39_x0, CentralCoverAssembly.R39_x1,
      CentralCoverAssembly.R39_y0, CentralCoverAssembly.R39_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R39_x0, CentralCoverAssembly.R39_x1,
      CentralCoverAssembly.R39_y0, CentralCoverAssembly.R39_y1]
    simp
    norm_num

/-- `Re sC39 = 0.105`. -/
theorem sC39_re : sC39.re = 0.105 := by
  unfold sC39
  rw [R39_center_eq]
  simp
  norm_num

/-- `Im sC39 = 7.25`. -/
theorem sC39_im : sC39.im = 7.25 := by
  unfold sC39
  rw [R39_center_eq]
  simp

/-- (3) Row-3 closure for R39 through `AX_CellTemplate.CellClosed_of_factorBounds`
(outer tier `eps = 0.002`; threshold `882000.002` stays a premise). -/
theorem R39_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC39‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC39‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC39‖)
    (hZeta : Azeta ≤ ‖zeta sC39‖)
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation)
    (hThresh : (0.002 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R39.center =
      sC39 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R39.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R39_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R39.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R39_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R39 sC39 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R39_strip_lo CentralCoverAssembly.R39_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R39SmallR

#print axioms BG_R39SmallR.R39_uniform_deriv_of_closedBall_bound
#print axioms BG_R39SmallR.R39_deriv_bound_of_factor_bounds
#print axioms BG_R39SmallR.R39_closed_of_smallR_factorBounds

namespace BG_R40SmallR

/-- R40 `mem` unpacked to numeric bounds. -/
theorem R40_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R40.mem w) :
    7.5 ≤ w.re ∧ w.re ≤ 10 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R40.x0 = 7.5 := CentralCoverAssembly.R40_x0
  have e1 : CentralCoverAssembly.R40.x1 = 10 := CentralCoverAssembly.R40_x1
  have e2 : CentralCoverAssembly.R40.y0 = 0.3 := CentralCoverAssembly.R40_y0
  have e3 : CentralCoverAssembly.R40.y1 = 0.49 := CentralCoverAssembly.R40_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R40 point lies in the open strip (deriv transfer applies). -/
theorem R40_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R40.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R40_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip. -/
theorem R40_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R40. -/
theorem R40_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R40: `[7.492,10.008]`. -/
theorem R40_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    7.492 ≤ u.re ∧ u.re ≤ 10.008 := by
  obtain ⟨hx0, hx1, _, _⟩ := R40_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R40: `[0.292,0.498]`. -/
theorem R40_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R40_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R40 stays strictly inside the strip. -/
theorem R40_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R40_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for R40. -/
theorem R40_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R40.center
      (CentralCoverAssembly.R40.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R40 0.008 C (by norm_num)
    (fun w hw => R40_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R40 small-`r` disc `s`-rect (value `56`). -/
def R40_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared `BD_Row3Shared.pi_upper_row3`). -/
def R40_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`). -/
def R40_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`). -/
def R40_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R40 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [7.49,10.01]`
(tight `[7.492,10.008]`, loosened for clean numerals). -/
theorem R40_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    7.49 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 10.01 := by
  obtain ⟨hre_lo, hre_hi⟩ := R40_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R40_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R40_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R40_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R40 small-sphere point. -/
theorem R40_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R40_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R40_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R40_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R40_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R40 `0.008`-spheres from the four obligations. -/
theorem R40_uniform_sphere_bound
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R40.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R40_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R40: uniform `‖deriv xiShifted‖ ≤ 700000`. -/
theorem R40_deriv_bound_of_factor_bounds
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R40 0.008 5600
    (by norm_num) (fun w hw => R40_strip_of_mem hw)
    (R40_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R40 `s`-plane center `s = 1/2 + I * R40.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC40 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R40.center

/-- R40 center coordinates (`xmid = 8.75`). -/
theorem R40_center_eq :
    CentralCoverAssembly.R40.center =
      (((8.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num

/-- `Re sC40 = 0.105`. -/
theorem sC40_re : sC40.re = 0.105 := by
  unfold sC40
  rw [R40_center_eq]
  simp
  norm_num

/-- `Im sC40 = 8.75`. -/
theorem sC40_im : sC40.im = 8.75 := by
  unfold sC40
  rw [R40_center_eq]
  simp

/-- (3) Row-3 closure for R40 through `AX_CellTemplate.CellClosed_of_factorBounds`
(outer tier `eps = 0.002`; threshold `882000.002` stays a premise). -/
theorem R40_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC40‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC40‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC40‖)
    (hZeta : Azeta ≤ ‖zeta sC40‖)
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation)
    (hThresh : (0.002 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R40.center =
      sC40 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R40.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R40_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R40.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R40_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R40 sC40 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R40_strip_lo CentralCoverAssembly.R40_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BG_R40SmallR

#print axioms BG_R39SmallR.R39_uniform_deriv_of_closedBall_bound
#print axioms BG_R39SmallR.R39_deriv_bound_of_factor_bounds
#print axioms BG_R39SmallR.R39_closed_of_smallR_factorBounds
#print axioms BG_R40SmallR.R40_uniform_deriv_of_closedBall_bound
#print axioms BG_R40SmallR.R40_deriv_bound_of_factor_bounds
#print axioms BG_R40SmallR.R40_closed_of_smallR_factorBounds

/-! ## BD row-3 R33+R34 small-r bridge (door-3 rollout, cover lane)

GREP-first record (2026-09-05, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`
  (`sphere_subset_closedBall_of_rect_mem` `:6213`).
* `CentralCoverAssembly.R33` (`(-6,-3.5,0.3,0.49)`) -> `:4345`;
  `R33_x0/x1/y0/y1` -> `:4348-4351`; `R33_strip_lo/hi` -> `:4356-4357`;
  `R33_radius_lt` (`< 1.26`) -> `:4372`; `R33_mem_gridFine` -> `:4375`;
  `R33_leaf_obligations (0.05,0.07)` -> `:4385`.
* `CentralCoverAssembly.R34` (`(-4,-1.5,0.3,0.49)`) -> `:4429`;
  `R34_x0/x1/y0/y1` -> `:4432-4435`; `R34_strip_lo/hi` -> `:4440-4441`;
  `R34_radius_lt` (`< 1.26`) -> `:4456`; `R34_mem_gridFine` -> `:4459`;
  `R34_leaf_obligations (0.05,0.07)` -> mid tier.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Shared row-3 facts live once in `BD_Row3Shared` (`:11261`: `pi_upper_row3`,
  `realGamma_0105_le_mirror`) and are REUSED here read-only, not copied.
  Per-cell obligations quote sup values only (no import of `interval_arith`,
  which imports this file -- BB/BD pattern): poly `56` (edge-strip poly-56
  tier, cf. `:6699`); pi `1`; Gamma `10`; zeta `10`
  (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).

DERIV CAVEAT: `r = 0.25` spheres exit the strip (`0.49 + 0.25 = 0.74 > 0.5`,
proved per cell as `RXX_sphere_025_exits`), so the deriv premise uses
`r = 0.008` (`0.49 + 0.008 = 0.498 < 0.5`, `RXX_small_radius_admissible`),
giving `M = 5600 / 0.008 = 700000` (`RXX_M_eq`), same as R31/R32.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at mid tier `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`).
Namespaces are fresh `BD_R33SmallR` / `BD_R34SmallR` (distinct from the
`BG_` rollout namespaces); per-cell numerals recomputed below.
-/

namespace BD_R33SmallR

/-- R33 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R33_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R33.mem w) :
    -6 ≤ w.re ∧ w.re ≤ -3.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R33.x0 = -6 := CentralCoverAssembly.R33_x0
  have e1 : CentralCoverAssembly.R33.x1 = -3.5 := CentralCoverAssembly.R33_x1
  have e2 : CentralCoverAssembly.R33.y0 = 0.3 := CentralCoverAssembly.R33_y0
  have e3 : CentralCoverAssembly.R33.y1 = 0.49 := CentralCoverAssembly.R33_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R33 point lies in the open strip (deriv transfer applies). -/
theorem R33_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R33.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R33_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R33_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R33
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R33_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R33: `[-6.008,-3.492]`. -/
theorem R33_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -6.008 ≤ u.re ∧ u.re ≤ -3.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R33_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R33: `[0.292,0.498]`. -/
theorem R33_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R33_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R33 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R33_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R33_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R33:
from a single closed-ball sup `C` over
`closedBall R33.center (R33.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R33.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R33_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R33.center
      (CentralCoverAssembly.R33.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R33 0.008 C (by norm_num)
    (fun w hw => R33_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R33 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R33_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R33_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 3.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R33_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R33_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-6.01 : Real) ≤ s.im → s.im ≤ (-3.49 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R33 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-6.01,-3.49]`
(tight rect `[0.002,0.208] x [-6.008,-3.492]`, loosened for clean numerals). -/
theorem R33_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -6.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ -3.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R33_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R33_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R33_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R33_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R33 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R33_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R33_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R33_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R33.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R33_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R33_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R33 `0.008`-spheres from the four obligations. -/
theorem R33_uniform_sphere_bound
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R33.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R33_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R33: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R33_deriv_bound_of_factor_bounds
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R33.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R33 0.008 5600
    (by norm_num) (fun w hw => R33_strip_of_mem hw)
    (R33_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R33 `s`-plane center `s = 1/2 + I * R33.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC33 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R33.center

/-- R33 center coordinates. -/
theorem R33_center_eq :
    CentralCoverAssembly.R33.center =
      (((-4.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R33_x0, CentralCoverAssembly.R33_x1,
      CentralCoverAssembly.R33_y0, CentralCoverAssembly.R33_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R33_x0, CentralCoverAssembly.R33_x1,
      CentralCoverAssembly.R33_y0, CentralCoverAssembly.R33_y1]
    simp
    norm_num

/-- `Re sC33 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC33_re : sC33.re = 0.105 := by
  unfold sC33
  rw [R33_center_eq]
  simp
  norm_num

/-- `Im sC33 = -4.75`. -/
theorem sC33_im : sC33.im = -4.75 := by
  unfold sC33
  rw [R33_center_eq]
  simp

/-- (3) Row-3 closure for R33 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R33_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC33‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC33‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC33‖)
    (hZeta : Azeta ≤ ‖zeta sC33‖)
    (hP : R33_poly_upper_obligation) (hPi : R33_pi_upper_obligation)
    (hG : R33_gamma_upper_obligation) (hZ : R33_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-6, -3.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R33.center =
      sC33 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R33.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R33_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R33.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R33_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R33 sC33 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R33_strip_lo CentralCoverAssembly.R33_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R33SmallR

#print axioms BD_R33SmallR.R33_uniform_deriv_of_closedBall_bound
#print axioms BD_R33SmallR.R33_deriv_bound_of_factor_bounds
#print axioms BD_R33SmallR.R33_closed_of_smallR_factorBounds

namespace BD_R34SmallR

/-- R34 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R34_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R34.mem w) :
    -4 ≤ w.re ∧ w.re ≤ -1.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R34.x0 = -4 := CentralCoverAssembly.R34_x0
  have e1 : CentralCoverAssembly.R34.x1 = -1.5 := CentralCoverAssembly.R34_x1
  have e2 : CentralCoverAssembly.R34.y0 = 0.3 := CentralCoverAssembly.R34_y0
  have e3 : CentralCoverAssembly.R34.y1 = 0.49 := CentralCoverAssembly.R34_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R34 point lies in the open strip (deriv transfer applies). -/
theorem R34_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R34.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R34_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R34_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R34
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R34_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R34: `[-4.008,-1.492]`. -/
theorem R34_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -4.008 ≤ u.re ∧ u.re ≤ -1.492 := by
  obtain ⟨hx0, hx1, _, _⟩ := R34_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R34: `[0.292,0.498]`. -/
theorem R34_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R34_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R34 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R34_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R34_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R34:
from a single closed-ball sup `C` over
`closedBall R34.center (R34.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R34.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R34_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R34.center
      (CentralCoverAssembly.R34.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R34 0.008 C (by norm_num)
    (fun w hw => R34_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R34 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R34_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R34_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 1.49` -- undischarged, needs the Stirling-disc
treatment, not the crude majorant). -/
def R34_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R34_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-4.01 : Real) ≤ s.im → s.im ≤ (-1.49 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R34 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-4.01,-1.49]`
(tight rect `[0.002,0.208] x [-4.008,-1.492]`, loosened for clean numerals). -/
theorem R34_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -4.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ -1.49 := by
  obtain ⟨hre_lo, hre_hi⟩ := R34_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R34_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R34_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R34_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R34 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R34_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R34_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R34_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R34.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R34_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R34_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R34 `0.008`-spheres from the four obligations. -/
theorem R34_uniform_sphere_bound
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R34.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R34_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R34: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R34_deriv_bound_of_factor_bounds
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R34.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R34 0.008 5600
    (by norm_num) (fun w hw => R34_strip_of_mem hw)
    (R34_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R34 `s`-plane center `s = 1/2 + I * R34.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC34 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R34.center

/-- R34 center coordinates. -/
theorem R34_center_eq :
    CentralCoverAssembly.R34.center =
      (((-2.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R34_x0, CentralCoverAssembly.R34_x1,
      CentralCoverAssembly.R34_y0, CentralCoverAssembly.R34_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R34_x0, CentralCoverAssembly.R34_x1,
      CentralCoverAssembly.R34_y0, CentralCoverAssembly.R34_y1]
    simp
    norm_num

/-- `Re sC34 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC34_re : sC34.re = 0.105 := by
  unfold sC34
  rw [R34_center_eq]
  simp
  norm_num

/-- `Im sC34 = -2.75`. -/
theorem sC34_im : sC34.im = -2.75 := by
  unfold sC34
  rw [R34_center_eq]
  simp

/-- (3) Row-3 closure for R34 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R34_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC34‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC34‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC34‖)
    (hZeta : Azeta ≤ ‖zeta sC34‖)
    (hP : R34_poly_upper_obligation) (hPi : R34_pi_upper_obligation)
    (hG : R34_gamma_upper_obligation) (hZ : R34_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-4, -1.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R34.center =
      sC34 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R34.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R34_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R34.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R34_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R34 sC34 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R34_strip_lo CentralCoverAssembly.R34_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R34SmallR

#print axioms BD_R33SmallR.R33_uniform_deriv_of_closedBall_bound
#print axioms BD_R33SmallR.R33_deriv_bound_of_factor_bounds
#print axioms BD_R33SmallR.R33_closed_of_smallR_factorBounds
#print axioms BD_R34SmallR.R34_uniform_deriv_of_closedBall_bound
#print axioms BD_R34SmallR.R34_deriv_bound_of_factor_bounds
#print axioms BD_R34SmallR.R34_closed_of_smallR_factorBounds

/-! ## BD row-3 R35+R36 small-r bridge (door-3 rollout, cover lane)

GREP-first record (2026-09-05, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`
  (`sphere_subset_closedBall_of_rect_mem` `:6213`).
* `CentralCoverAssembly.R35` (`(-2,0.5,0.3,0.49)`) -> `:4513`;
  `R35_x0/x1/y0/y1` -> `:4516-4519`; `R35_strip_lo/hi` -> `:4524-4525`;
  `R35_radius_lt` (`< 1.26`) -> `:4540`; `R35_mem_gridFine` -> `:4543`;
  `R35_leaf_obligations (0.15,0.06)` -> `:4553` (inner tier).
* `CentralCoverAssembly.R36` (`(0,2.5,0.3,0.49)`) -> `:4597`;
  `R36_x0/x1/y0/y1` -> `:4600-4603`; `R36_strip_lo/hi` -> `:4608-4609`;
  `R36_radius_lt` (`< 1.26`) -> `:4624`; `R36_mem_gridFine` -> `:4627`;
  `R36_leaf_obligations (0.15,0.06)` -> `:4637` (inner tier).
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Shared row-3 facts live once in `BD_Row3Shared` (`:11261`: `pi_upper_row3`,
  `realGamma_0105_le_mirror`) and are REUSED here read-only, not copied.
  Per-cell obligations quote sup values only (no import of `interval_arith`,
  which imports this file -- BB/BD pattern): poly `56` (edge-strip poly-56
  tier, cf. `:6699`); pi `1`; Gamma `10`; zeta `10`
  (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).
* BG rollout `BG_R35SmallR`/`BG_R36SmallR` (`:12262`/`:12537`) already packages
  the same numerals; this BD bridge mirrors the `BD_R33SmallR`/`BD_R34SmallR`
  template under fresh `BD_` namespaces for the cover lane.

DERIV CAVEAT: `r = 0.25` spheres exit the strip (`0.49 + 0.25 = 0.74 > 0.5`,
proved per cell as `RXX_sphere_025_exits`), so the deriv premise uses
`r = 0.008` (`0.49 + 0.008 = 0.498 < 0.5`, `RXX_small_radius_admissible`),
giving `M = 5600 / 0.008 = 700000` (`RXX_M_eq`), same as R31-R34.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at inner tier `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.15 + 700000 * 1.26 = 882000.15`).
Namespaces are fresh `BD_R35SmallR` / `BD_R36SmallR` (distinct from the
`BG_` rollout namespaces); per-cell numerals recomputed below.
-/

namespace BD_R35SmallR

/-- R35 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R35_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R35.mem w) :
    -2 ≤ w.re ∧ w.re ≤ 0.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R35.x0 = -2 := CentralCoverAssembly.R35_x0
  have e1 : CentralCoverAssembly.R35.x1 = 0.5 := CentralCoverAssembly.R35_x1
  have e2 : CentralCoverAssembly.R35.y0 = 0.3 := CentralCoverAssembly.R35_y0
  have e3 : CentralCoverAssembly.R35.y1 = 0.49 := CentralCoverAssembly.R35_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R35 point lies in the open strip (deriv transfer applies). -/
theorem R35_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R35.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R35_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R35_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R35
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R35_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R35: `[-2.008,0.508]`. -/
theorem R35_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -2.008 ≤ u.re ∧ u.re ≤ 0.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R35_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R35: `[0.292,0.498]`. -/
theorem R35_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R35_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R35 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R35_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R35_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R35:
from a single closed-ball sup `C` over
`closedBall R35.center (R35.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R35.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R35_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R35.center
      (CentralCoverAssembly.R35.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R35 0.008 C (by norm_num)
    (fun w hw => R35_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R35 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R35_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R35_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 0.51` on part of the rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R35_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R35_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-2.01 : Real) ≤ s.im → s.im ≤ (0.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R35 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-2.01,0.51]`
(tight rect `[0.002,0.208] x [-2.008,0.508]`, loosened for clean numerals). -/
theorem R35_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -2.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 0.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R35_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R35_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R35_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R35_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R35 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R35_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R35_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R35_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R35.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R35_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R35_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R35 `0.008`-spheres from the four obligations. -/
theorem R35_uniform_sphere_bound
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R35.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R35_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R35: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R35_deriv_bound_of_factor_bounds
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R35.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R35 0.008 5600
    (by norm_num) (fun w hw => R35_strip_of_mem hw)
    (R35_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R35 `s`-plane center `s = 1/2 + I * R35.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC35 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R35.center

/-- R35 center coordinates (`xmid = -0.75`, `ymid = 0.395`). -/
theorem R35_center_eq :
    CentralCoverAssembly.R35.center =
      (((-0.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R35_x0, CentralCoverAssembly.R35_x1,
      CentralCoverAssembly.R35_y0, CentralCoverAssembly.R35_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R35_x0, CentralCoverAssembly.R35_x1,
      CentralCoverAssembly.R35_y0, CentralCoverAssembly.R35_y1]
    simp
    norm_num

/-- `Re sC35 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC35_re : sC35.re = 0.105 := by
  unfold sC35
  rw [R35_center_eq]
  simp
  norm_num

/-- `Im sC35 = -0.75`. -/
theorem sC35_im : sC35.im = -0.75 := by
  unfold sC35
  rw [R35_center_eq]
  simp

/-- (3) Row-3 closure for R35 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at inner tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.15 + 700000 * 1.26 = 882000.15`). -/
theorem R35_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC35‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC35‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC35‖)
    (hZeta : Azeta ≤ ‖zeta sC35‖)
    (hP : R35_poly_upper_obligation) (hPi : R35_pi_upper_obligation)
    (hG : R35_gamma_upper_obligation) (hZ : R35_zeta_upper_obligation)
    (hThresh : (0.15 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-2, 0.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R35.center =
      sC35 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R35.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R35_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R35.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R35_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R35 sC35 hsC
    Apoly Api Agam Azeta 0.15 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R35_strip_lo CentralCoverAssembly.R35_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R35SmallR

namespace BD_R36SmallR

/-- R36 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R36_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R36.mem w) :
    0 ≤ w.re ∧ w.re ≤ 2.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R36.x0 = 0 := CentralCoverAssembly.R36_x0
  have e1 : CentralCoverAssembly.R36.x1 = 2.5 := CentralCoverAssembly.R36_x1
  have e2 : CentralCoverAssembly.R36.y0 = 0.3 := CentralCoverAssembly.R36_y0
  have e3 : CentralCoverAssembly.R36.y1 = 0.49 := CentralCoverAssembly.R36_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R36 point lies in the open strip (deriv transfer applies). -/
theorem R36_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R36.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R36_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R36_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R36
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R36_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R36: `[-0.008,2.508]`. -/
theorem R36_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -0.008 ≤ u.re ∧ u.re ≤ 2.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R36_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R36: `[0.292,0.498]`. -/
theorem R36_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R36_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R36 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R36_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R36_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R36:
from a single closed-ball sup `C` over
`closedBall R36.center (R36.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R36.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R36_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R36.center
      (CentralCoverAssembly.R36.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R36 0.008 C (by norm_num)
    (fun w hw => R36_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R36 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R36_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R36_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 2.50` on most of the rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R36_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R36_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (-0.01 : Real) ≤ s.im → s.im ≤ (2.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R36 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [-0.01,2.51]`
(tight rect `[0.002,0.208] x [-0.008,2.508]`, loosened for clean numerals). -/
theorem R36_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    -0.01 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 2.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R36_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R36_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R36_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R36_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R36 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R36_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R36_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R36_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R36.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R36_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R36_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R36 `0.008`-spheres from the four obligations. -/
theorem R36_uniform_sphere_bound
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R36.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R36_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R36: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R36_deriv_bound_of_factor_bounds
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R36.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R36 0.008 5600
    (by norm_num) (fun w hw => R36_strip_of_mem hw)
    (R36_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R36 `s`-plane center `s = 1/2 + I * R36.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC36 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R36.center

/-- R36 center coordinates (`xmid = 1.25`, `ymid = 0.395`). -/
theorem R36_center_eq :
    CentralCoverAssembly.R36.center =
      (((1.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R36_x0, CentralCoverAssembly.R36_x1,
      CentralCoverAssembly.R36_y0, CentralCoverAssembly.R36_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R36_x0, CentralCoverAssembly.R36_x1,
      CentralCoverAssembly.R36_y0, CentralCoverAssembly.R36_y1]
    simp
    norm_num

/-- `Re sC36 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC36_re : sC36.re = 0.105 := by
  unfold sC36
  rw [R36_center_eq]
  simp
  norm_num

/-- `Im sC36 = 1.25`. -/
theorem sC36_im : sC36.im = 1.25 := by
  unfold sC36
  rw [R36_center_eq]
  simp

/-- (3) Row-3 closure for R36 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at inner tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.15 + 700000 * 1.26 = 882000.15`). -/
theorem R36_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC36‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC36‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC36‖)
    (hZeta : Azeta ≤ ‖zeta sC36‖)
    (hP : R36_poly_upper_obligation) (hPi : R36_pi_upper_obligation)
    (hG : R36_gamma_upper_obligation) (hZ : R36_zeta_upper_obligation)
    (hThresh : (0.15 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (0, 2.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R36.center =
      sC36 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R36.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R36_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R36.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R36_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R36 sC36 hsC
    Apoly Api Agam Azeta 0.15 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R36_strip_lo CentralCoverAssembly.R36_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R36SmallR

#print axioms BD_R35SmallR.R35_uniform_deriv_of_closedBall_bound
#print axioms BD_R35SmallR.R35_deriv_bound_of_factor_bounds
#print axioms BD_R35SmallR.R35_closed_of_smallR_factorBounds
#print axioms BD_R36SmallR.R36_uniform_deriv_of_closedBall_bound
#print axioms BD_R36SmallR.R36_deriv_bound_of_factor_bounds
#print axioms BD_R36SmallR.R36_closed_of_smallR_factorBounds

/-! ## BD row-3 R37+R38 small-r packaging (door-3 cover lane, mid tier)

GREP-first record (2026-09-05, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`.
* `CentralCoverAssembly.R37` (`(2,4.5,0.3,0.49)`) -> `:4681`;
  `R37_x0/x1/y0/y1` -> `:4684-4687`; `R37_strip_lo/hi` -> `:4692-4693`;
  `R37_radius_lt` (`< 1.26`) -> `:4708`.
* `CentralCoverAssembly.R38` (`(4,6.5,0.3,0.49)`) -> `:4765`;
  `R38_x0/x1/y0/y1` -> `:4768-4771`; `R38_strip_lo/hi` -> `:4776-4777`;
  `R38_radius_lt` (`< 1.26`) -> `:4792`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Shared row-3 facts live once in `BD_Row3Shared` (`:11261`: `pi_upper_row3`,
  `realGamma_0105_le_mirror`) and are REUSED here read-only, not copied.
  Per-cell obligations quote sup values only (no import of `interval_arith`,
  which imports this file -- BB/BD pattern): poly `56` (edge-strip poly-56
  tier, cf. `:6699`); pi `1`; Gamma `10`; zeta `10`
  (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).
* BG rollout `BG_R37SmallR`/`BG_R38SmallR` (`:12835`/`:13110`) already packages
  the same numerals; this BD bridge mirrors the `BD_R36SmallR` template
  (`:14917`) under fresh `BD_` namespaces for the cover lane.

DERIV CAVEAT: `r = 0.25` spheres exit the strip (`0.49 + 0.25 = 0.74 > 0.5`,
proved per cell as `RXX_sphere_025_exits`), so the deriv premise uses
`r = 0.008` (`0.49 + 0.008 = 0.498 < 0.5`, `RXX_small_radius_admissible`),
giving `M = 5600 / 0.008 = 700000` (`RXX_M_eq`), same as R31-R36.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at mid tier `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`).
Namespaces are fresh `BD_R37SmallR` / `BD_R38SmallR` (distinct from the
`BG_` rollout namespaces); per-cell numerals recomputed below.
-/

namespace BD_R37SmallR

/-- R37 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R37_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R37.mem w) :
    2 ≤ w.re ∧ w.re ≤ 4.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R37.x0 = 2 := CentralCoverAssembly.R37_x0
  have e1 : CentralCoverAssembly.R37.x1 = 4.5 := CentralCoverAssembly.R37_x1
  have e2 : CentralCoverAssembly.R37.y0 = 0.3 := CentralCoverAssembly.R37_y0
  have e3 : CentralCoverAssembly.R37.y1 = 0.49 := CentralCoverAssembly.R37_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R37 point lies in the open strip (deriv transfer applies). -/
theorem R37_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R37.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R37_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R37_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R37
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R37_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R37: `[1.992,4.508]`. -/
theorem R37_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    1.992 ≤ u.re ∧ u.re ≤ 4.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R37_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R37: `[0.292,0.498]`. -/
theorem R37_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R37_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R37 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R37_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R37_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R37:
from a single closed-ball sup `C` over
`closedBall R37.center (R37.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R37.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R37_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R37.center
      (CentralCoverAssembly.R37.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R37 0.008 C (by norm_num)
    (fun w hw => R37_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R37 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R37_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R37_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 1.99` on the whole rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R37_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R37_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (1.99 : Real) ≤ s.im → s.im ≤ (4.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R37 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [1.99,4.51]`
(tight rect `[1.992,4.508]` from `u.re`, loosened for clean numerals). -/
theorem R37_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    1.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 4.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R37_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R37_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R37_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R37_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R37 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R37_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R37_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R37_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R37.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R37_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R37_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R37 `0.008`-spheres from the four obligations. -/
theorem R37_uniform_sphere_bound
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R37.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R37_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R37: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R37_deriv_bound_of_factor_bounds
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R37.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R37 0.008 5600
    (by norm_num) (fun w hw => R37_strip_of_mem hw)
    (R37_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R37 `s`-plane center `s = 1/2 + I * R37.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC37 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R37.center

/-- R37 center coordinates (`xmid = 3.25`, `ymid = 0.395`). -/
theorem R37_center_eq :
    CentralCoverAssembly.R37.center =
      (((3.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R37_x0, CentralCoverAssembly.R37_x1,
      CentralCoverAssembly.R37_y0, CentralCoverAssembly.R37_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R37_x0, CentralCoverAssembly.R37_x1,
      CentralCoverAssembly.R37_y0, CentralCoverAssembly.R37_y1]
    simp
    norm_num

/-- `Re sC37 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC37_re : sC37.re = 0.105 := by
  unfold sC37
  rw [R37_center_eq]
  simp
  norm_num

/-- `Im sC37 = 3.25`. -/
theorem sC37_im : sC37.im = 3.25 := by
  unfold sC37
  rw [R37_center_eq]
  simp

/-- (3) Row-3 closure for R37 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R37_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC37‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC37‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC37‖)
    (hZeta : Azeta ≤ ‖zeta sC37‖)
    (hP : R37_poly_upper_obligation) (hPi : R37_pi_upper_obligation)
    (hG : R37_gamma_upper_obligation) (hZ : R37_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (2, 4.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R37.center =
      sC37 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R37.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R37_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R37.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R37_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R37 sC37 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R37_strip_lo CentralCoverAssembly.R37_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R37SmallR

namespace BD_R38SmallR

/-- R38 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R38_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R38.mem w) :
    4 ≤ w.re ∧ w.re ≤ 6.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R38.x0 = 4 := CentralCoverAssembly.R38_x0
  have e1 : CentralCoverAssembly.R38.x1 = 6.5 := CentralCoverAssembly.R38_x1
  have e2 : CentralCoverAssembly.R38.y0 = 0.3 := CentralCoverAssembly.R38_y0
  have e3 : CentralCoverAssembly.R38.y1 = 0.49 := CentralCoverAssembly.R38_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R38 point lies in the open strip (deriv transfer applies). -/
theorem R38_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R38.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R38_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R38_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R38
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R38_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R38: `[3.992,6.508]`. -/
theorem R38_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    3.992 ≤ u.re ∧ u.re ≤ 6.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R38_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R38: `[0.292,0.498]`. -/
theorem R38_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R38_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R38 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R38_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R38_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R38:
from a single closed-ball sup `C` over
`closedBall R38.center (R38.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R38.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R38_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R38.center
      (CentralCoverAssembly.R38.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R38 0.008 C (by norm_num)
    (fun w hw => R38_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R38 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R38_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R38_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 3.99` on the whole rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R38_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R38_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (3.99 : Real) ≤ s.im → s.im ≤ (6.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R38 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [3.99,6.51]`
(tight rect `[3.992,6.508]` from `u.re`, loosened for clean numerals). -/
theorem R38_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    3.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 6.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R38_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R38_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R38_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R38_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R38 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R38_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R38_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R38_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R38.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R38_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R38_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R38 `0.008`-spheres from the four obligations. -/
theorem R38_uniform_sphere_bound
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R38.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R38_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R38: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R38_deriv_bound_of_factor_bounds
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R38.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R38 0.008 5600
    (by norm_num) (fun w hw => R38_strip_of_mem hw)
    (R38_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R38 `s`-plane center `s = 1/2 + I * R38.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC38 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R38.center

/-- R38 center coordinates (`xmid = 5.25`, `ymid = 0.395`). -/
theorem R38_center_eq :
    CentralCoverAssembly.R38.center =
      (((5.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R38_x0, CentralCoverAssembly.R38_x1,
      CentralCoverAssembly.R38_y0, CentralCoverAssembly.R38_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R38_x0, CentralCoverAssembly.R38_x1,
      CentralCoverAssembly.R38_y0, CentralCoverAssembly.R38_y1]
    simp
    norm_num

/-- `Re sC38 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC38_re : sC38.re = 0.105 := by
  unfold sC38
  rw [R38_center_eq]
  simp
  norm_num

/-- `Im sC38 = 5.25`. -/
theorem sC38_im : sC38.im = 5.25 := by
  unfold sC38
  rw [R38_center_eq]
  simp

/-- (3) Row-3 closure for R38 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at mid tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.05 + 700000 * 1.26 = 882000.05`). -/
theorem R38_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC38‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC38‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC38‖)
    (hZeta : Azeta ≤ ‖zeta sC38‖)
    (hP : R38_poly_upper_obligation) (hPi : R38_pi_upper_obligation)
    (hG : R38_gamma_upper_obligation) (hZ : R38_zeta_upper_obligation)
    (hThresh : (0.05 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (4, 6.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R38.center =
      sC38 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R38.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R38_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R38.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R38_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R38 sC38 hsC
    Apoly Api Agam Azeta 0.05 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R38_strip_lo CentralCoverAssembly.R38_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R38SmallR

#print axioms BD_R37SmallR.R37_uniform_deriv_of_closedBall_bound
#print axioms BD_R37SmallR.R37_deriv_bound_of_factor_bounds
#print axioms BD_R37SmallR.R37_closed_of_smallR_factorBounds
#print axioms BD_R38SmallR.R38_uniform_deriv_of_closedBall_bound
#print axioms BD_R38SmallR.R38_deriv_bound_of_factor_bounds
#print axioms BD_R38SmallR.R38_closed_of_smallR_factorBounds

/-! ## BD row-3 R39+R40 small-r packaging (door-3 cover lane, outer tier, LANE FINALE)

GREP-first record (2026-09-05, verified before writing; exact names):
* `DerivCauchyBridge.uniform_deriv_of_sphere_bound` -> `central_cover_assembly.lean:6201`;
  `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` -> `:6233`.
* `CentralCoverAssembly.R39` (`(6,8.5,0.3,0.49)`) -> `:4849`;
  `R39_x0/x1/y0/y1` -> `:4852-4855`; `R39_strip_lo/hi` -> `:4860-4861`;
  `R39_radius_lt` (`< 1.26`) -> `:4876`; `R39_mem_gridFine` -> `:4879`.
* `CentralCoverAssembly.R40` (`(7.5,10,0.3,0.49)`) -> `:4933`;
  `R40_x0/x1/y0/y1` -> `:4936-4939`; `R40_strip_lo/hi` -> `:4944-4945`;
  `R40_radius_lt` (`< 1.26`) -> `:4960`; `R40_mem_gridFine` -> `:4963`.
* `AX_CellTemplate.CellClosed_of_factorBounds` -> `:10676`.
* Shared row-3 facts live once in `BD_Row3Shared` (`:11261`: `pi_upper_row3`,
  `realGamma_0105_le_mirror`) and are REUSED here read-only, not copied.
  Per-cell obligations quote sup values only (no import of `interval_arith`,
  which imports this file -- BB/BD pattern): poly `56` (edge-strip poly-56
  tier, cf. `:6699`); pi `1`; Gamma `10`; zeta `10`
  (`DerivCauchyBridge.R02_zeta_upper_obligation`, `:6493`).
* BG rollout `BG_R39SmallR`/`BG_R40SmallR` (`:13408`/`:13683`) already packages
  the same numerals; this BD bridge mirrors the `BD_R38SmallR` template
  under fresh `BD_` namespaces for the cover lane.

DERIV CAVEAT: `r = 0.25` spheres exit the strip (`0.49 + 0.25 = 0.74 > 0.5`,
proved per cell as `RXX_sphere_025_exits`), so the deriv premise uses
`r = 0.008` (`0.49 + 0.008 = 0.498 < 0.5`, `RXX_small_radius_admissible`),
giving `M = 5600 / 0.008 = 700000` (`RXX_M_eq`), same as R31-R38.
Full proofs only; no `sorry`/`admit`/`axiom`; 0 cells claimed closed
(`hThresh` stays a premise: at outer tier `M = 700000` closure needs
`Apoly * Api * Agam * Azeta >= 0.002 + 700000 * 1.26`).
Namespaces are fresh `BD_R39SmallR` / `BD_R40SmallR` (distinct from the
`BG_` rollout namespaces); per-cell numerals recomputed below.
-/

namespace BD_R39SmallR

/-- R39 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R39_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R39.mem w) :
    6 ≤ w.re ∧ w.re ≤ 8.5 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R39.x0 = 6 := CentralCoverAssembly.R39_x0
  have e1 : CentralCoverAssembly.R39.x1 = 8.5 := CentralCoverAssembly.R39_x1
  have e2 : CentralCoverAssembly.R39.y0 = 0.3 := CentralCoverAssembly.R39_y0
  have e3 : CentralCoverAssembly.R39.y1 = 0.49 := CentralCoverAssembly.R39_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R39 point lies in the open strip (deriv transfer applies). -/
theorem R39_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R39.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R39_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R39_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R39
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R39_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R39: `[5.992,8.508]`. -/
theorem R39_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    5.992 ≤ u.re ∧ u.re ≤ 8.508 := by
  obtain ⟨hx0, hx1, _, _⟩ := R39_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R39: `[0.292,0.498]`. -/
theorem R39_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R39_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R39 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R39_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R39_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R39:
from a single closed-ball sup `C` over
`closedBall R39.center (R39.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R39.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R39_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R39.center
      (CentralCoverAssembly.R39.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R39 0.008 C (by norm_num)
    (fun w hw => R39_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R39 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R39_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R39_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 5.99` on the whole rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R39_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R39_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (5.99 : Real) ≤ s.im → s.im ≤ (8.51 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R39 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [5.99,8.51]`
(tight rect `[5.992,8.508]` from `u.re`, loosened for clean numerals). -/
theorem R39_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    5.99 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 8.51 := by
  obtain ⟨hre_lo, hre_hi⟩ := R39_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R39_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R39_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R39_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R39 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R39_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R39_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R39_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R39.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R39_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R39_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R39 `0.008`-spheres from the four obligations. -/
theorem R39_uniform_sphere_bound
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R39.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R39_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R39: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R39_deriv_bound_of_factor_bounds
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R39.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R39 0.008 5600
    (by norm_num) (fun w hw => R39_strip_of_mem hw)
    (R39_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R39 `s`-plane center `s = 1/2 + I * R39.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC39 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R39.center

/-- R39 center coordinates (`xmid = 7.25`, `ymid = 0.395`). -/
theorem R39_center_eq :
    CentralCoverAssembly.R39.center =
      (((7.25 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R39_x0, CentralCoverAssembly.R39_x1,
      CentralCoverAssembly.R39_y0, CentralCoverAssembly.R39_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R39_x0, CentralCoverAssembly.R39_x1,
      CentralCoverAssembly.R39_y0, CentralCoverAssembly.R39_y1]
    simp
    norm_num

/-- `Re sC39 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC39_re : sC39.re = 0.105 := by
  unfold sC39
  rw [R39_center_eq]
  simp
  norm_num

/-- `Im sC39 = 7.25`. -/
theorem sC39_im : sC39.im = 7.25 := by
  unfold sC39
  rw [R39_center_eq]
  simp

/-- (3) Row-3 closure for R39 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at outer tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.002 + 700000 * 1.26`). -/
theorem R39_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC39‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC39‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC39‖)
    (hZeta : Azeta ≤ ‖zeta sC39‖)
    (hP : R39_poly_upper_obligation) (hPi : R39_pi_upper_obligation)
    (hG : R39_gamma_upper_obligation) (hZ : R39_zeta_upper_obligation)
    (hThresh : (0.002 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (6, 8.5, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R39.center =
      sC39 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R39.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R39_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R39.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R39_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R39 sC39 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R39_strip_lo CentralCoverAssembly.R39_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R39SmallR

namespace BD_R40SmallR

/-- R40 `mem` unpacked to numeric bounds
(mirrors `DerivCauchyBridge.R02_mem_bounds` `:6246`). -/
theorem R40_mem_bounds {w : Complex} (hw : CentralCoverAssembly.R40.mem w) :
    7.5 ≤ w.re ∧ w.re ≤ 10 ∧ 0.3 ≤ w.im ∧ w.im ≤ 0.49 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have e0 : CentralCoverAssembly.R40.x0 = 7.5 := CentralCoverAssembly.R40_x0
  have e1 : CentralCoverAssembly.R40.x1 = 10 := CentralCoverAssembly.R40_x1
  have e2 : CentralCoverAssembly.R40.y0 = 0.3 := CentralCoverAssembly.R40_y0
  have e3 : CentralCoverAssembly.R40.y1 = 0.49 := CentralCoverAssembly.R40_y1
  rw [e0] at hx0
  rw [e1] at hx1
  rw [e2] at hy0
  rw [e3] at hy1
  exact ⟨hx0, hx1, hy0, hy1⟩

/-- Every R40 point lies in the open strip (deriv transfer applies). -/
theorem R40_strip_of_mem {w : Complex} (hw : CentralCoverAssembly.R40.mem w) :
    -(1 / 2 : Real) < w.im ∧ w.im < (1 / 2 : Real) := by
  obtain ⟨_, _, hy0, hy1⟩ := R40_mem_bounds hw
  constructor <;> linarith

/-- Exact admissibility: `r = 0.008` keeps the top edge in-strip
(`0.49 + 0.008 = 0.498 < 0.5`). -/
theorem R40_small_radius_admissible : (0.49 : Real) + 0.008 < 0.5 := by
  norm_num

/-- The `r = 0.25` sphere exits the strip over R40
(`0.49 + 0.25 = 0.74 > 0.5`): the R02 `0.25`-sphere numbers are unusable here. -/
theorem R40_sphere_025_exits : (0.5 : Real) < 0.49 + 0.25 := by
  norm_num

/-- Real parts on the `0.008`-sphere over R40: `[7.492,10.008]`. -/
theorem R40_small_sphere_re_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    7.492 ≤ u.re ∧ u.re ≤ 10.008 := by
  obtain ⟨hx0, hx1, _, _⟩ := R40_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have hre : |(u - w).re| ≤ (0.008 : Real) := by
    calc |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
      _ = 0.008 := hnorm
  have here : (u - w).re = u.re - w.re := by simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the `0.008`-sphere over R40: `[0.292,0.498]`. -/
theorem R40_small_sphere_im_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.292 ≤ u.im ∧ u.im ≤ 0.498 := by
  obtain ⟨_, _, hy0, hy1⟩ := R40_mem_bounds hw
  have hdist : dist u w = (0.008 : Real) := Metric.mem_sphere.mp hu
  have hnorm : ‖u - w‖ = (0.008 : Real) := by rwa [dist_eq_norm] at hdist
  have him : |(u - w).im| ≤ (0.008 : Real) := by
    calc |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
      _ = 0.008 := hnorm
  have heim : (u - w).im = u.im - w.im := by simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- The `0.008`-sphere over R40 stays strictly inside the strip
(`[0.292,0.498] subset (-1/2,1/2)`), so `xiShifted = xiShiftedEntire` there. -/
theorem R40_small_sphere_mem_strip {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    -(1 / 2 : Real) < u.im ∧ u.im < (1 / 2 : Real) := by
  obtain ⟨hlo, hhi⟩ := R40_small_sphere_im_bounds hw hu
  constructor <;> linarith

/-- (1) ClosedBall-bridge instantiation for the row-3 cell R40:
from a single closed-ball sup `C` over
`closedBall R40.center (R40.radius + 0.008)`, uniform
`‖deriv xiShifted‖ ≤ C / 0.008` on `R40.mem`.
Mirrors `DerivCauchyBridge.uniform_deriv_of_closedBall_bound` (`:6233`)
at the exact admissible radius `0.008 < 0.01`. -/
theorem R40_uniform_deriv_of_closedBall_bound (C : Real)
    (hCball : ∀ z ∈ Metric.closedBall CentralCoverAssembly.R40.center
      (CentralCoverAssembly.R40.radius + 0.008),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ w, CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ C / 0.008 := by
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CentralCoverAssembly.R40 0.008 C (by norm_num)
    (fun w hw => R40_strip_of_mem hw) hCball

/-- Poly-upper obligation on the R40 small-`r` disc `s`-rect
(value `56`: edge-strip poly-56 tier, cf. `:6699`). -/
def R40_poly_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.polyOf s‖ ≤ (56 : Real)

/-- Pi-upper obligation (value `1`: shared proof
`BD_Row3Shared.pi_upper_row3`; its proof needs only `0 < s.re`). -/
def R40_pi_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.piOf s‖ ≤ (1 : Real)

/-- Gamma-upper obligation (value `10`: shared
`BD_Row3Shared.realGamma_0105_le_mirror`; true sup is `O(0.01)` by
Im-decay since `|s.im| >= 7.49` on the whole rect -- undischarged, needs the
Stirling-disc treatment, not the crude majorant). -/
def R40_gamma_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖DerivCauchyBridge.gammaOf s‖ ≤ (10 : Real)

/-- Zeta-upper obligation (value `10`: `R02_zeta_upper_obligation` value,
`:6493`; true `|zeta| = O(1)` on this rect). -/
def R40_zeta_upper_obligation : Prop :=
  ∀ s : Complex, (0.001 : Real) ≤ s.re → s.re ≤ (0.21 : Real) →
    (7.49 : Real) ≤ s.im → s.im ≤ (10.01 : Real) →
    ‖zeta s‖ ≤ (10 : Real)

/-- `s = 1/2 + I*u` coordinates for `u` on an R40 `0.008`-sphere:
`s.re in [0.001,0.21]`, `s.im in [7.49,10.01]`
(tight rect `[7.492,10.008]` from `u.re`, loosened for clean numerals). -/
theorem R40_s_of_small_sphere_re_im {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real)) :
    0.001 ≤ ((1 / 2 : Complex) + Complex.I * u).re ∧
    ((1 / 2 : Complex) + Complex.I * u).re ≤ 0.21 ∧
    7.49 ≤ ((1 / 2 : Complex) + Complex.I * u).im ∧
    ((1 / 2 : Complex) + Complex.I * u).im ≤ 10.01 := by
  obtain ⟨hre_lo, hre_hi⟩ := R40_small_sphere_re_bounds hw hu
  obtain ⟨him_lo, him_hi⟩ := R40_small_sphere_im_bounds hw hu
  have hsre : ((1 / 2 : Complex) + Complex.I * u).re = 1 / 2 - u.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : ((1 / 2 : Complex) + Complex.I * u).im = u.re := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsre, hsim]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Disc factor product: `56 * 1 * 10 * 10 = 5600`. -/
theorem R40_C_eq : (56 : Real) * 1 * 10 * 10 = 5600 := by
  norm_num

/-- Cauchy `M`: `5600 / 0.008 = 700000`. -/
theorem R40_M_eq : (5600 : Real) / 0.008 = 700000 := by
  norm_num

/-- (2a) Conditional `xiShifted` upper on an R40 small-sphere point:
`‖xi‖ ≤ 56*1*10*10 = 5600` from the four disc-sup obligations
(mirrors `AO_xiShifted_upper_of_zeta_upper_R02` `:10004`). -/
theorem R40_xiShifted_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ‖xiShifted u‖ ≤ 5600 := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    R40_s_of_small_sphere_re_im hw hu
  have hpoly := hP _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := hPi _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hgam := hG _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hzeta := hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  have h123 : ‖DerivCauchyBridge.polyOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : Complex) + Complex.I * u)‖ *
      ‖zeta ((1 / 2 : Complex) + Complex.I * u)‖ ≤ 56 * 1 * 10 * 10 :=
    mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)
  have hnum : (56 : Real) * 1 * 10 * 10 = 5600 := by norm_num
  rw [hnum] at h123
  exact h123

/-- Transfer to the entire extension on the small sphere (agrees in-strip). -/
theorem R40_entire_upper_of_factor_bounds {w u : Complex}
    (hw : CentralCoverAssembly.R40.mem w)
    (hu : u ∈ Metric.sphere w (0.008 : Real))
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 5600 := by
  obtain ⟨hlo, hhi⟩ := R40_small_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R40_xiShifted_upper_of_factor_bounds hw hu hP hPi hG hZ

/-- Uniform sup `5600` on all R40 `0.008`-spheres from the four obligations. -/
theorem R40_uniform_sphere_bound
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R40.mem w → ∀ z ∈ Metric.sphere w (0.008 : Real),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 5600 := by
  intro w hw z hz
  exact R40_entire_upper_of_factor_bounds hw hz hP hPi hG hZ

/-- (2b) Row-3 deriv bound for R40: uniform `‖deriv xiShifted‖ ≤ 700000`
(`5600 / 0.008`) modulo exactly the four disc-sup obligations above.
This is the small-`r` replacement for the `0.25`-sphere `M` on upper rows. -/
theorem R40_deriv_bound_of_factor_bounds
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation) :
    ∀ w, CentralCoverAssembly.R40.mem w → ‖deriv xiShifted w‖ ≤ (700000 : Real) := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R40 0.008 5600
    (by norm_num) (fun w hw => R40_strip_of_mem hw)
    (R40_uniform_sphere_bound hP hPi hG hZ)
  intro w hw
  have hle := hM w hw
  have heq : (5600 : Real) / 0.008 = 700000 := by norm_num
  rw [heq] at hle
  exact hle

/-- R40 `s`-plane center `s = 1/2 + I * R40.center` (row-3 `s.Re = 0.105`). -/
noncomputable def sC40 : Complex :=
  (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R40.center

/-- R40 center coordinates (`xmid = 8.75`, `ymid = 0.395`). -/
theorem R40_center_eq :
    CentralCoverAssembly.R40.center =
      (((8.75 : Real) : Complex)) + Complex.I * (((0.395 : Real) : Complex)) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num

/-- `Re sC40 = 0.105` (row-3 `s`-value, cf. G4 `:10827`). -/
theorem sC40_re : sC40.re = 0.105 := by
  unfold sC40
  rw [R40_center_eq]
  simp
  norm_num

/-- `Im sC40 = 8.75`. -/
theorem sC40_im : sC40.im = 8.75 := by
  unfold sC40
  rw [R40_center_eq]
  simp

/-- (3) Row-3 closure for R40 through `AX_CellTemplate.CellClosed_of_factorBounds`
with the small-`r` deriv bound (`M = 700000`) discharging the template's deriv
premise. Center floors + threshold stay premises (honest residual: at outer tier
`M = 700000` the threshold needs
`Apoly * Api * Agam * Azeta >= 0.002 + 700000 * 1.26`). -/
theorem R40_closed_of_smallR_factorBounds
    (Apoly Api Agam Azeta : Real)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖DerivCauchyBridge.polyOf sC40‖)
    (hpi : Api ≤ ‖DerivCauchyBridge.piOf sC40‖)
    (hGam : Agam ≤ ‖DerivCauchyBridge.gammaOf sC40‖)
    (hZeta : Azeta ≤ ‖zeta sC40‖)
    (hP : R40_poly_upper_obligation) (hPi : R40_pi_upper_obligation)
    (hG : R40_gamma_upper_obligation) (hZ : R40_zeta_upper_obligation)
    (hThresh : (0.002 : Real) + 700000 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (c : Real × Real × Real × Real) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (7.5, 10, 0.3, 0.49)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : Real),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : Real) < R.y0 ∧ R.y1 < (1 / 2 : Real) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hsC : (1 / 2 : Complex) + Complex.I * CentralCoverAssembly.R40.center =
      sC40 := rfl
  have hDeriv : ∀ w, CentralCoverAssembly.R40.mem w →
      ‖deriv xiShifted w‖ ≤ (700000 : Real) :=
    R40_deriv_bound_of_factor_bounds hP hPi hG hZ
  have hRad : CentralCoverAssembly.R40.radius ≤ (1.26 : Real) :=
    le_of_lt CentralCoverAssembly.R40_radius_lt
  subst hc_eq
  exact AX_CellTemplate.CellClosed_of_factorBounds
    CentralCoverAssembly.R40 sC40 hsC
    Apoly Api Agam Azeta 0.002 700000 1.26
    hA0 hB0 hC0 hD0 (by norm_num)
    hpoly hpi hGam hZeta hDeriv hRad hThresh
    CentralCoverAssembly.R40_strip_lo CentralCoverAssembly.R40_strip_hi (by norm_num)
    _ hc_mem rfl rfl rfl rfl

end BD_R40SmallR

#print axioms BD_R39SmallR.R39_uniform_deriv_of_closedBall_bound
#print axioms BD_R39SmallR.R39_deriv_bound_of_factor_bounds
#print axioms BD_R39SmallR.R39_closed_of_smallR_factorBounds
#print axioms BD_R40SmallR.R40_uniform_deriv_of_closedBall_bound
#print axioms BD_R40SmallR.R40_deriv_bound_of_factor_bounds
#print axioms BD_R40SmallR.R40_closed_of_smallR_factorBounds

/-! ## Door-3 residual scout: real axis + Re=+-10 lines + edge-strip status (2026-09-05)

MAPPING (obligations quoted, all read-only above; BD cover lane R31-R40 closed):

1. REAL AXIS (`z.im = 0`): NO feeder covers it.
   - `centralCovers_inner` (l.320-322) takes `(hgap : z.im < -0.01 ∨ 0.01 < z.im)`,
     explicitly excluding the strip `(-0.01,0.01)` ("excludes real-axis strip
     `(-0.01,0.01)`, which needs `BoundaryProofEngine` for coordinator", l.317-318).
   - `strip_nonvanishing_of_base_bounds` (l.2222-2224) needs `(hy_pos : 0 < z.im)`,
     so `z.im = 0` is out of reach of the designated nonzero-base feeder
     (`BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base`, l.2236-2239).
   - `/-- ... -/` inventory (l.755-760): "the strips `(0,0.01]`, `[0.49,1/2)`, the
     lines `x = ±10`, and the real axis need
     `BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base` /
     `..._of_simple_zero_base` (real-axis fencing)".
   - First step banked below: `door3_real_self_star` (`z.im = 0 → star z = z`)
     + `door3_conj_transfer` (nonvanishing reflects across `conj` inside the
     strip via `classicalXi_symmetry.conj_symm`); hence an upper-half
     nonvanishing result at `z` gives the conjugate point for free, and real-axis
     points are self-conjugate (no analysis, no zeta wall).

2. LINES `Re = ±10`: strict-interior hypotheses exclude them; thin rects exist.
   - `centralCovers_inner` (l.320) needs `(hx_lo : (-10.0:ℝ) < z.re)`
     `(hx_hi : z.re < (10.0:ℝ))` (strict; "endpoints `±10` excluded", l.318-319).
   - `CutR10_mem_of_line` (l.6888-6890): `(hx : z.re = 10) → -0.49 ≤ z.im →
     z.im ≤ 0.49 → CutR10.mem z`; `CutL10_mem_of_line` (l.6898-6900): mirror at
     `-10`; `cutoffLines_either` (l.6908-6911): `Re=±10, |Im|<1/2` lands in a thin
     rect or in strip range `0.49 ≤ |Im|`.
   - Residual inventory (l.6956): "Cutoff lines `Re=±10` (2 thin rects `CutL10`,
     `CutR10`): per rect CENTER plus DERIV same two `zeta` enclosures on vertical
     `s`-rects (`Re` in `[0.01,0.99]`, `Im=±10`, true `O(1)`)".
   - First step banked below: `door3_cutoffLine_mem_of_abs_le` reduces the
     `|Im| ≤ 0.49` part of either line to `CutL10.mem z ∨ CutR10.mem z`, i.e. to
     the per-rect fencing H-leaf (`CellFencingHypotheses CutL10/CutR10`, same
     shape as `R00_leaf_obligations`, l.1175-1177).

3. EDGE STRIPS (`y ∈ [0.49,1/2)`, 10 cells): need their OWN obligation shape;
   they do NOT reuse `CellData` / `Rxx_leaf_obligations`.
   - `CellData` (l.111-126) demands `(y1_lt_half : y1 < (1/2:ℝ))`; every
     `edgeStripCells` entry (l.6584-6594) has `y1 = 0.5` (proved
     `door3_edgeStrip_y1_eq_half` below), and `EdgeS00_touches_top` (l.6697):
     `¬ EdgeS00.y1 < (1/2:ℝ)`, so "inner strip fencing
     (`R.y1<1/2`) does NOT apply; outer-bound tool needed" (l.6696-6697).
   - Combinatorics closed: `edgeStripCells_covers` (l.6597-6600) tiles
     `(-10,10) × [0.49,0.5)`; geometry closed: `edgeStrip_radius_bound`
     (l.6685-6689, radius `< 1.26`).
   - Residual inventory (l.6955): per cell CENTER lower needs `Azeta` lower at
     NEW re-value `s.re ∈ (0,0.01]` + DERIV upper needs tight `‖zeta‖ ≤ 10`
     (zeta wall); top-touching `y1 = 0.5` additionally needs
     `upper_boundary_nonvanishing_from_outer_bound`.
   - `conj_of` blocked for full strips: `edgeS00_full_strip_conj_blocked`
     (l.8302-8303); lower mirrors stay residual (l.6974).
   - First step banked below: `door3_edgeStrip_needs_own_obligation`
     (`∀ c ∈ edgeStripCells, ¬ c.2.2.2 < 1/2`): the `CellData`-reuse route is
     formally closed off, pinning the outer-bound obligation shape for the next
     agent.

Cheapest-first order for the next agent: cutoff-line H-leaf → strip outer-bound
→ real-axis base point (needs a `zeta`/entire-extension lower bound at one real
point, the only analytic input).
-/

namespace Door3ResidualScout

open CentralCoverAssembly

/-- Every edge-strip cell has `y0 = 0.49` (pure `rfl` per `edgeStripCells`, l.6584). -/
theorem door3_edgeStrip_y0_eq : ∀ c ∈ edgeStripCells, c.2.2.1 = 0.49 := by
  intro c hc
  unfold edgeStripCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every edge-strip cell has `y1 = 0.5` (pure `rfl` per `edgeStripCells`, l.6584). -/
theorem door3_edgeStrip_y1_eq_half : ∀ c ∈ edgeStripCells, c.2.2.2 = 0.5 := by
  intro c hc
  unfold edgeStripCells at hc
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Strip cells need their OWN obligation shape: `CellData.y1_lt_half`
(`central_cover_assembly.lean:118`) can never hold since `y1 = 0.5`. -/
theorem door3_edgeStrip_needs_own_obligation :
    ∀ c ∈ edgeStripCells, ¬ c.2.2.2 < (1 / 2 : ℝ) := by
  intro c hc hlt
  have heq := door3_edgeStrip_y1_eq_half c hc
  rw [heq] at hlt
  linarith

/-- `Re = ±10` with `|Im| ≤ 0.49` lands in a cutoff thin rect
(`CutL10_mem_of_line` l.6898 / `CutR10_mem_of_line` l.6888): the `±10`-line
obligation reduces to the per-rect fencing H-leaf
(`CellFencingHypotheses`, same shape as `R00_leaf_obligations` l.1175). -/
theorem door3_cutoffLine_mem_of_abs_le {z : ℂ}
    (heq : z.re = 10 ∨ z.re = -10)
    (hy_lo : -0.49 ≤ z.im) (hy_hi : z.im ≤ 0.49) :
    CutL10.mem z ∨ CutR10.mem z := by
  rcases heq with hx | hx
  · exact Or.inr (CutR10_mem_of_line hx hy_lo hy_hi)
  · exact Or.inl (CutL10_mem_of_line hx hy_lo hy_hi)

/-- Real-axis points are self-conjugate (first symmetry step toward the real-axis
residual; `centralCovers_inner` l.320 excludes `z.im = 0` via `hgap`). -/
theorem door3_real_self_star {z : ℂ} (h : z.im = 0) : star z = z := by
  have hre : (star z).re = z.re := by simp [conj_re]
  have him : (star z).im = z.im := by simp [conj_im, h]
  exact Complex.ext hre him

/-- Nonvanishing reflects across conjugation inside the strip
(`classicalXi_symmetry.conj_symm` needs `-(1/2:ℝ) < z.im < 1/2`, same side
conditions as `XiLocalZeroFreeRect.conj_of` l.521): upper-half results transfer
to the lower half, and with `door3_real_self_star` the real axis is fixed. -/
theorem door3_conj_transfer {z : ℂ}
    (hgt : (-1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hz : xiShifted z ≠ 0) : xiShifted (star z) ≠ 0 := by
  have hsym := classicalXi_symmetry.conj_symm z hgt hlt
  intro hcon
  apply hz
  have h2 : star (xiShifted z) = 0 := by
    rw [← hsym]
    exact hcon
  have hcc := congr_arg star h2
  rwa [star_star, star_zero] at hcc

end Door3ResidualScout

#print axioms Door3ResidualScout.door3_edgeStrip_y0_eq
#print axioms Door3ResidualScout.door3_edgeStrip_y1_eq_half
#print axioms Door3ResidualScout.door3_edgeStrip_needs_own_obligation
#print axioms Door3ResidualScout.door3_cutoffLine_mem_of_abs_le
#print axioms Door3ResidualScout.door3_real_self_star
#print axioms Door3ResidualScout.door3_conj_transfer
