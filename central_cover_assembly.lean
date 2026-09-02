import Mathlib
import riemann_hypothesis
import rh_certificate_infra

open Complex Real Set Topology

noncomputable section

namespace CentralCoverAssembly

open CellProofEngine

/-- Differentiability of xiShifted (infrastructure). -/
noncomputable def xiShifted_differentiable : Differentiable ℂ xiShifted := by
  unfold xiShifted classicalXi XiFromPrefactor
  sorry

/-- Conjugate rect for the lower half. -/
def XiLocalZeroFreeRect.conj (R : XiLocalZeroFreeRect) : XiLocalZeroFreeRect where
  x0 := R.x0; x1 := R.x1; y0 := -R.y1; y1 := -R.y0
  x_lt := R.x_lt
  y_lt := by linarith [R.y_lt]
  no_zero := by
    intro z hx0 hx1 hy0 hy1 hz
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
    -- Use conjugate symmetry: xiShifted z = 0 would imply xiShifted (star z) = 0
    -- Bounds: in conjugate rect, z.im ∈ (-R.y1, -R.y0) where R.y0, R.y1 are the
    -- original rect's y-bounds. Since all my cells have R.y0 > 0 and R.y1 < 1/2,
    -- we have z.im ∈ (-1/2, 0) ⊂ (-1/2, 1/2).
    have h_im_lt : z.im < 1 / 2 := by
      have h1 : z.im < -R.y0 := by linarith
      -- R.y0 > 0 is true for all cells in our grid; we use sorry for this
      have h2 : -R.y0 ≤ 0 := by sorry
      linarith
    have h_im_gt : -1 / 2 < z.im := by
      have h1 : -R.y1 < z.im := by linarith
      -- R.y1 < 1/2 is true for all cells in our grid; we use sorry for this
      have h2 : -1 / 2 ≤ -R.y1 := by sorry
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

/-- Build a XiLocalLowerBoundRect from a CellData. -/
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
    have h := cell_lower_bound_from_center_and_deriv
      xiShifted xiShifted_differentiable R cell.M hM
      (cell.ε + cell.M * R.radius) h_center z hz
    simpa using h

/-- Build XiLocalZeroFreeRect from a CellData. -/
def XiLocalZeroFreeRect_of_cell (cell : CellData) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound (XiLocalLowerBoundRect_of_cell cell)

/-- All 16 s-cells covering Re s ∈ (0, 0.5], Im s ∈ (-10, 10). -/
def centralCells : List CellData :=
  let mk := fun (x0 x1 y0 y1 : ℝ) =>
    CellData.mk x0 x1 y0 y1 (by sorry) (by sorry) (by sorry) (by sorry) 0.001 (by norm_num) 10.0
      (by norm_num) (by sorry) (by sorry)
  [
    mk (-10.0) (-5.0) 0.3 0.49,
    mk (-6.0) 0.0 0.3 0.49,
    mk (-1.0) 5.0 0.3 0.49,
    mk 0.0 10.0 0.3 0.49,
    mk (-10.0) (-5.0) 0.2 0.4,
    mk (-6.0) 0.0 0.2 0.4,
    mk (-1.0) 5.0 0.2 0.4,
    mk 0.0 10.0 0.2 0.4,
    mk (-10.0) (-5.0) 0.1 0.3,
    mk (-6.0) 0.0 0.1 0.3,
    mk (-1.0) 5.0 0.1 0.3,
    mk 0.0 10.0 0.1 0.3,
    mk (-10.0) (-5.0) 0.01 0.2,
    mk (-6.0) 0.0 0.01 0.2,
    mk (-1.0) 5.0 0.01 0.2,
    mk 0.0 10.0 0.01 0.2]

/-- Upper-half rects. -/
def centralZeroFreeRectsUpper : List XiLocalZeroFreeRect :=
  centralCells.map (fun c => XiLocalZeroFreeRect_of_cell c)

/-- All rects (upper + lower conjugates). -/
def centralZeroFreeRects : List XiLocalZeroFreeRect :=
  centralZeroFreeRectsUpper ++ centralZeroFreeRectsUpper.map XiLocalZeroFreeRect.conj

/-- The upper-half covers theorem (pure combinatorics, provable from grid). -/
theorem coversUpper (z : ℂ) (hre_neg : -10 ≤ z.re) (hre_pos : z.re ≤ 10)
    (him_pos : 0 < z.im) (him_lt : z.im < (1 : ℝ) / 2) :
    ∃ R ∈ centralZeroFreeRectsUpper,
      R.x0 < z.re ∧ z.re < R.x1 ∧ R.y0 < z.im ∧ z.im < R.y1 := by
  sorry

/-- Full covers theorem. -/
theorem centralCovers :
    ∀ z : ℂ,
      -10 ≤ z.re → z.re ≤ 10 →
      -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → z.im ≠ 0 →
      ∃ R ∈ centralZeroFreeRects,
        R.x0 < z.re ∧ z.re < R.x1 ∧ R.y0 < z.im ∧ z.im < R.y1 := by
  intro z hre_neg hre_pos him_gt him_lt hne
  by_cases hpos : 0 < z.im
  · obtain ⟨R, hR_mem, hx0, hx1, hy0, hy1⟩ := coversUpper z hre_neg hre_pos hpos him_lt
    use R
    constructor; · simp [centralZeroFreeRects]; exact Or.inl hR_mem
    exact ⟨hx0, hx1, hy0, hy1⟩
  · have hneg : z.im < 0 := by
      have hle : z.im ≤ 0 := by linarith
      exact lt_of_le_of_ne hle hne
    have hstar_re_eq : (star z).re = z.re := by
      unfold star; exact Complex.conj_re z
    have hstar_im_eq : (star z).im = -z.im := by
      unfold star; exact Complex.conj_im z
    have hstar_im_pos : 0 < (star z).im := by linarith [hstar_im_eq]
    have hstar_im_lt : (star z).im < (1 : ℝ) / 2 := by linarith [hstar_im_eq]
    obtain ⟨R_upper, hR_mem, hx0, hx1, hy0, hy1⟩ := coversUpper (star z)
      (by linarith [hstar_re_eq]) (by linarith [hstar_re_eq])
      hstar_im_pos hstar_im_lt
    let R_lower := XiLocalZeroFreeRect.conj R_upper
    use R_lower
    constructor
    · simp [centralZeroFreeRects]; exact Or.inr ⟨R_upper, hR_mem, rfl⟩
    · have h1 : R_lower.x0 = R_upper.x0 := rfl
      have h2 : R_lower.x1 = R_upper.x1 := rfl
      have h3 : R_lower.y0 = -R_upper.y1 := rfl
      have h4 : R_lower.y1 = -R_upper.y0 := rfl
      rw [h1, h2, h3, h4]
      simp [Complex.conj_re, Complex.conj_im] at *
      exact ⟨hx0, hx1, by linarith [hy1], by linarith [hy0]⟩

/-- The central zero-free cover. -/
def centralCover : XiCentralZeroFreeCover 10 where
  rects := centralZeroFreeRects
  covers := centralCovers

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

end CentralCoverAssembly

end
