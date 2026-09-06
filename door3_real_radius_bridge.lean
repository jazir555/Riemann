import central_cover_trusted

open Float Complex Real CellProofEngine CentralCoverAssembly

noncomputable section

namespace Door3RealRadiusBridge

/-- The exact-real rectangle represented by a bridged certificate cell. -/
def realRect (b : BridgedCell) : Rect2D :=
  Rect2D.mk b.x0 b.x1 b.y0 b.y1 b.x_lt b.y_lt

/--
Corrected bridge interface: a real center certificate is consumed against the
exact real rectangle radius and center. No equality between a rounded Float
radius and the real radius is assumed.
-/
def lowerBoundRectOfRealCertificate (b : BridgedCell)
    (hderiv : ∀ w, (realRect b).mem w → ‖deriv xiShifted w‖ ≤ b.M)
    (hcenter : b.ε + b.M * (realRect b).radius ≤ ‖xiShifted (realRect b).center‖) :
    XiLocalLowerBoundRect :=
  lowerBoundRect_of_rect_center_bound_strip
    (realRect b) b.ε b.ε_pos b.M
    (lt_trans (by norm_num) b.y0_pos)
    b.y1_lt
    hderiv hcenter

def zeroFreeRectOfRealCertificate (b : BridgedCell)
    (hderiv : ∀ w, (realRect b).mem w → ‖deriv xiShifted w‖ ≤ b.M)
    (hcenter : b.ε + b.M * (realRect b).radius ≤ ‖xiShifted (realRect b).center‖) :
    XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound
    (lowerBoundRectOfRealCertificate b hderiv hcenter)

theorem zeroFreeRectOfRealCertificate_bounds (b : BridgedCell)
    (hderiv : ∀ w, (realRect b).mem w → ‖deriv xiShifted w‖ ≤ b.M)
    (hcenter : b.ε + b.M * (realRect b).radius ≤ ‖xiShifted (realRect b).center‖) :
    (zeroFreeRectOfRealCertificate b hderiv hcenter).x0 = b.x0 ∧
      (zeroFreeRectOfRealCertificate b hderiv hcenter).x1 = b.x1 ∧
      (zeroFreeRectOfRealCertificate b hderiv hcenter).y0 = b.y0 ∧
      (zeroFreeRectOfRealCertificate b hderiv hcenter).y1 = b.y1 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

end Door3RealRadiusBridge

#print axioms Door3RealRadiusBridge.zeroFreeRectOfRealCertificate_bounds
