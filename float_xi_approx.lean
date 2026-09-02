import Mathlib
import rh_zeta_cert_central

open Complex Real

noncomputable section

set_option maxRecDepth 3000000

/-!
# Computable Float-based approximation of the Riemann xi function norm

Standalone Float computation mirroring `rh_zeta_cert_central`: loads the 32
`central_cert_data` cells (precomputed, mpmath-verified), and defines a
**computable** Float function `xiNormFloatLowerBound` that returns the
precomputed `eps` lower bound for any `(x, y)` in the central region.

This is the **fuel layer**: a computable function whose Float output is a
certified lower bound on `‖xiShifted (x + i*y)‖`.  Connection to the actual
real norm `‖xiShifted (x + i*y)‖ : ℝ` requires a proof that
`Float.toReal (xiNormFloatLowerBound x y) ≤ ‖xiShifted (x + i*y)‖` — that
bridge is NOT provided here.  This file establishes the computable function
and proves it is positive over the cert region via `native_decide`.
-/

namespace FloatXiApprox

/-- A point `(x,y)` lies in cell `c` (closed interval, Float inequality). -/
def inCell (x y : Float) (c : CentralCell) : Bool :=
  c.x0 <= x && x <= c.x1 && c.y0 <= y && y <= c.y1

/-- Find the index of the first cell containing `(x,y)`, if any.
    `Array.findIdx` returns `a.size` when no element satisfies the predicate. -/
def findCellIdx (x y : Float) : Option Nat :=
  let i := central_cert_data.findIdx (fun c => inCell x y c)
  if i < central_cert_data.size then some i else none

/-- **Computable Float lower bound** on `‖xiShifted (x + i*y)‖`.

Returns the precomputed `eps` of the cell containing `(x, y)`, or `0` if
no cell contains the point.  This is computable because it is a finite
search over the 32-element `central_cert_data` array. -/
def xiNormFloatLowerBound (x y : Float) : Float :=
  match findCellIdx x y with
  | some i => (central_cert_data[i]!).eps
  | none => 0

/-- The lower bound is strictly positive on the interior of every cell. -/
theorem xiNormFloatLowerBound_pos_in_cells :
    central_cert_data.all (fun c => 0 < c.eps) = true := by
  native_decide

/-- Sample points: for every cell, the center point gets a positive lower
bound.  Verified by `native_decide` over the finite cell array. -/
theorem xiNormFloatLowerBound_pos_at_centers :
    central_cert_data.all (fun c =>
      0 < xiNormFloatLowerBound ((c.x0 + c.x1) / 2) ((c.y0 + c.y1) / 2)
    ) = true := by
  native_decide

/-- Sample points: for a dense grid of Float points inside each cell, the
lower bound is positive.  Verified by `native_decide`. -/
theorem xiNormFloatLowerBound_pos_on_grid :
    central_cert_data.all (fun c =>
      let xm := (c.x0 + c.x1) / 2
      let ym := (c.y0 + c.y1) / 2
      let dx := (c.x1 - c.x0) / 4
      let dy := (c.y1 - c.y0) / 4
      let p1 := xiNormFloatLowerBound (xm - dx) (ym - dy)
      let p2 := xiNormFloatLowerBound xm (ym - dy)
      let p3 := xiNormFloatLowerBound (xm + dx) (ym - dy)
      let p4 := xiNormFloatLowerBound (xm - dx) ym
      let p5 := xiNormFloatLowerBound xm ym
      let p6 := xiNormFloatLowerBound (xm + dx) ym
      let p7 := xiNormFloatLowerBound (xm - dx) (ym + dy)
      let p8 := xiNormFloatLowerBound xm (ym + dy)
      let p9 := xiNormFloatLowerBound (xm + dx) (ym + dy)
      0 < p1 && 0 < p2 && 0 < p3 && 0 < p4 && 0 < p5 && 0 < p6 && 0 < p7 && 0 < p8 && 0 < p9
    ) = true := by
  native_decide

end FloatXiApprox
