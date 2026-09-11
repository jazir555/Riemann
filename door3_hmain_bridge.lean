/-! # Door 3 Hmain bridge: `full_central_covered` → `XiCentralMainBand10`

What Hmain is: `XiCentralMainBand10` (`riemann_hypothesis.lean`) is the Door-2
  main-band Prop `∀ z, -10 < Re z < 10 → Im ∈ (0,0.49] ∪ [-0.49,0) → xiShifted z ≠ 0`.
What feeds it now: `CentralCoverAssembly.full_central_covered` forwards each point
  to `central_upper_covered` (positive side) or `central_lower_covered` (mirror).
What remains (one line each):
  leaves: 80 per-cell `RXX_H` numerical enclosures behind `FullCentralObligations`.
  BottomStrip: per-`x` `StripBaseBounds` family behind `BottomStripObligations`.
  numeric premises: `R02` zeta/deriv bounds + interval-arithmetic certificates.
-/

import Mathlib
import central_cover_assembly
import riemann_hypothesis

open Complex

/-- Wrapper: the assembled central cover discharges the Door-2 main-band hypothesis.
Application shape copied from `bottom_row_covered` / `central_upper_covered`
(`central_cover_assembly.lean`): forward per-point bounds via `exact`. -/
theorem hmain_of_full_central_covered
    (hFull : CentralCoverAssembly.FullCentralObligations)
    (hStrip : CentralCoverAssembly.BottomStripObligations) :
    XiCentralMainBand10 := by
  show ∀ z : ℂ, -(10 : ℝ) < z.re → z.re < 10 →
    ((0 < z.im ∧ z.im ≤ 0.49) ∨ (-0.49 ≤ z.im ∧ z.im < 0)) →
    xiShifted z ≠ 0
  intro z hx_lo hx_hi hy
  rcases hy with ⟨hpos, hle⟩ | ⟨hge, hneg⟩
  · exact CentralCoverAssembly.full_central_covered hFull hStrip hx_lo hx_hi
      (Or.inl ⟨hpos, hle⟩)
  · exact CentralCoverAssembly.full_central_covered hFull hStrip hx_lo hx_hi
      (Or.inr ⟨hge, hneg⟩)
