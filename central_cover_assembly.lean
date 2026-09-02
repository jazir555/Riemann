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
-/

end CentralCoverAssembly

end
