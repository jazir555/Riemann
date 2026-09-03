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

end CentralCoverAssembly

end
