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
