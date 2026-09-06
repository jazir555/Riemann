import central_cover_assembly

open Complex Real
open CentralCoverAssembly

noncomputable section

/-!
# Closed-cell Door 3 cover interface

The numerical cells used by Door 3 meet on their boundaries.  A cover stated
with strict inequalities therefore needs artificial overlap columns; a
certificate proved on a closed rectangle does not.  This file records the
closed-cell interface and its direct assembly into the pointwise nonvanishing
obligation.  It is independent of the analytic certificate values.
-/

structure XiLocalClosedZeroFreeRect where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  no_zero :
    ∀ z : ℂ,
      x0 ≤ z.re →
      z.re ≤ x1 →
      y0 ≤ z.im →
      z.im ≤ y1 →
      xiShifted z ≠ 0

structure XiCentralClosedZeroFreeCover (X : ℝ) where
  rects : List XiLocalClosedZeroFreeRect
  covers :
    ∀ z : ℂ,
      -X ≤ z.re →
      z.re ≤ X →
      -(1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      ∃ R ∈ rects,
        R.x0 ≤ z.re ∧
        z.re ≤ R.x1 ∧
        R.y0 ≤ z.im ∧
        z.im ≤ R.y1

/-! The fine grid also covers the *closed* inner rectangle.  This is the
boundary form needed when a point lands exactly on a numerical cell edge. -/

theorem fineGridX_covers_closed {x : ℝ} (hx_lo : -10 ≤ x) (hx_hi : x ≤ 10) :
    ∃ p ∈ fineGridX, p.1 ≤ x ∧ x ≤ p.2 := by
  unfold fineGridX
  by_cases h1 : x ≤ -7.5
  · exact ⟨(-10, -7.5), by simp, hx_lo, h1⟩
  · by_cases h2 : x ≤ -5.5
    · exact ⟨(-8, -5.5), by simp, by linarith, h2⟩
    · by_cases h3 : x ≤ -3.5
      · exact ⟨(-6, -3.5), by simp, by linarith, h3⟩
      · by_cases h4 : x ≤ -1.5
        · exact ⟨(-4, -1.5), by simp, by linarith, h4⟩
        · by_cases h5 : x ≤ 0.5
          · exact ⟨(-2, 0.5), by simp, by linarith, h5⟩
          · by_cases h6 : x ≤ 2.5
            · exact ⟨(0, 2.5), by simp, by linarith, h6⟩
            · by_cases h7 : x ≤ 4.5
              · exact ⟨(2, 4.5), by simp, by linarith, h7⟩
              · by_cases h8 : x ≤ 6.5
                · exact ⟨(4, 6.5), by simp, by linarith, h8⟩
                · by_cases h9 : x ≤ 8.5
                  · exact ⟨(6, 8.5), by simp, by linarith, h9⟩
                  · exact ⟨(7.5, 10), by simp, by linarith, hx_hi⟩

theorem innerGridY_covers_closed {y : ℝ} (hy_lo : 0.01 ≤ y) (hy_hi : y ≤ 0.49) :
    ∃ q ∈ innerGridY, q.1 ≤ y ∧ y ≤ q.2 := by
  unfold innerGridY
  by_cases h1 : 0.3 ≤ y
  · exact ⟨(0.3, 0.49), by simp, h1, hy_hi⟩
  · by_cases h2 : 0.2 ≤ y
    · exact ⟨(0.2, 0.4), by simp, by linarith, by linarith⟩
    · by_cases h3 : 0.1 ≤ y
      · exact ⟨(0.1, 0.3), by simp, by linarith, by linarith⟩
      · exact ⟨(0.01, 0.2), by simp, hy_lo, by linarith⟩

theorem gridFine_covers_closed_inner {x y : ℝ}
    (hx_lo : -10 ≤ x) (hx_hi : x ≤ 10)
    (hy_lo : 0.01 ≤ y) (hy_hi : y ≤ 0.49) :
    ∃ c ∈ gridFine, c.1 ≤ x ∧ x ≤ c.2.1 ∧ c.2.2.1 ≤ y ∧ y ≤ c.2.2.2 := by
  obtain ⟨px, hpx_mem, hpx_lo, hpx_hi⟩ := fineGridX_covers_closed hx_lo hx_hi
  obtain ⟨py, hpy_mem, hpy_lo, hpy_hi⟩ := innerGridY_covers_closed hy_lo hy_hi
  refine ⟨(px.1, px.2, py.1, py.2), ?_, hpx_lo, hpx_hi, hpy_lo, hpy_hi⟩
  unfold gridFine
  rw [List.mem_flatMap]
  exact ⟨px, hpx_mem, by simp [hpy_mem]⟩

/-! The closed-grid counterpart of the existing strict-inner assembly.  The
same fencing supplier is enough because the Taylor estimate is proved on a
closed `Rect2D.mem`; only the geometric inequalities change from `<` to `≤`. -/

theorem closed_inner_nonvanishing_of_fenced_grid_fine
    (H : ∀ c ∈ gridFine, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖)
    {z : ℂ} (hx_lo : -10 ≤ z.re) (hx_hi : z.re ≤ 10)
    (hy_lo : 0.01 ≤ z.im) (hy_hi : z.im ≤ 0.49) :
    xiShifted z ≠ 0 := by
  obtain ⟨c, hc_mem, hloX, hhiX, hloY, hhiY⟩ :=
    gridFine_covers_closed_inner hx_lo hx_hi hy_lo hy_hi
  obtain ⟨R, ε, M, hx0, hx1, hy0, hy1, hStripLo, hStripHi, hε, hM, hcenter⟩ :=
    H c hc_mem
  have hmem : R.mem z := by
    have e1 : R.x0 ≤ z.re := by rw [hx0]; exact hloX
    have e2 : z.re ≤ R.x1 := by rw [hx1]; exact hhiX
    have e3 : R.y0 ≤ z.im := by rw [hy0]; exact hloY
    have e4 : z.im ≤ R.y1 := by rw [hy1]; exact hhiY
    exact ⟨e1, e2, e3, e4⟩
  have hle : ε ≤ ‖xiShifted z‖ :=
    xi_rect_lower_bound_of_center_bound_strip R ε M hStripLo hStripHi hM hcenter z hmem
  intro hzero
  rw [hzero, norm_zero] at hle
  exact (not_le_of_gt hε) hle

/-! A closed-cell constructor from the same Taylor-fencing hypotheses used by
the open-cell assembly.  `Rect2D.mem` is closed, so the resulting certificate
also handles points lying exactly on a cell edge. -/

def xiLocalClosedZeroFreeRect_of_fencing
    (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hStripLo : -(1 / 2 : ℝ) < R.y0)
    (hStripHi : R.y1 < (1 / 2 : ℝ))
    (hε : 0 < ε)
    (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (hCenter : ε + M * R.radius ≤ ‖xiShifted R.center‖) :
    XiLocalClosedZeroFreeRect where
  x0 := R.x0
  x1 := R.x1
  y0 := R.y0
  y1 := R.y1
  x_lt := R.hx
  y_lt := R.hy
  no_zero := by
    intro z hx0 hx1 hy0 hy1
    have hle : ε ≤ ‖xiShifted z‖ :=
      xi_rect_lower_bound_of_center_bound_strip R ε M hStripLo hStripHi
        hM hCenter z ⟨hx0, hx1, hy0, hy1⟩
    intro hzero
    rw [hzero, norm_zero] at hle
    exact (not_le_of_gt hε) hle

theorem xiCentralPointwise_of_closed_cover
    {X : ℝ}
    (C : XiCentralClosedZeroFreeCover X) :
    XiCentralPointwiseNonvanishingForX X where
  central_nonvanishing := by
    intro z hge hle hgt hlt hne hz
    rcases C.covers z hge hle hgt hlt hne with
      ⟨R, _, hx0, hx1, hy0, hy1⟩
    exact R.no_zero z hx0 hx1 hy0 hy1 hz

theorem rh_from_central_closed_zero_free_cover_and_tail_pointwise
    {X : ℝ}
    (C : XiCentralClosedZeroFreeCover X)
    (T : XiTailPointwiseNonvanishingForX X) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_central_pointwise_and_tail_pointwise
      (xiCentralPointwise_of_closed_cover C) T)

#print axioms xiCentralPointwise_of_closed_cover
#print axioms rh_from_central_closed_zero_free_cover_and_tail_pointwise
