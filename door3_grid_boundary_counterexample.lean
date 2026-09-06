import central_cover_trusted

open Complex Real CellProofEngine CentralCoverAssembly

noncomputable section

namespace Door3GridBoundaryCounterexample

/-- The strict legacy rectangles cannot cover the shared column boundary
`Re z = -7.5`; this is a kernel-checked obstruction to the old cover claim. -/
theorem no_strict_cover_at_neg75 :
    ¬ ∃ b ∈ bridgedCells,
      b.x0 < (-7.5 : ℝ) ∧ (-7.5 : ℝ) < b.x1 := by
  have e0 : (-10.0 : Float).toReal = (-10 : ℝ) := by
    have h : (-10.0 : Float).toRatParts = some (-5629499534213120, -49) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e1 : (-7.5 : Float).toReal = (-7.5 : ℝ) := by
    have h : (-7.5 : Float).toRatParts = some (-8444249301319680, -50) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e2 : (-5.0 : Float).toReal = (-5 : ℝ) := by
    have h : (-5.0 : Float).toRatParts = some (-5629499534213120, -50) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e3 : (-2.5 : Float).toReal = (-2.5 : ℝ) := by
    have h : (-2.5 : Float).toRatParts = some (-5629499534213120, -51) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e4 : (0.0 : Float).toReal = (0 : ℝ) := by
    have h : (0.0 : Float).toRatParts = some (0, -53) := by native_decide
    unfold Float.toReal; simp [h]
  have e5 : (2.5 : Float).toReal = (2.5 : ℝ) := by
    have h : (2.5 : Float).toRatParts = some (5629499534213120, -51) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e6 : (5.0 : Float).toReal = (5 : ℝ) := by
    have h : (5.0 : Float).toRatParts = some (5629499534213120, -50) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e7 : (7.5 : Float).toReal = (7.5 : ℝ) := by
    have h : (7.5 : Float).toRatParts = some (8444249301319680, -50) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  have e8 : (10.0 : Float).toReal = (10 : ℝ) := by
    have h : (10.0 : Float).toRatParts = some (5629499534213120, -49) := by native_decide
    unfold Float.toReal; simp [h]; norm_num
  intro h
  simp [bridgedCells, central_cert_data, e0, e1, e2, e3, e4, e5, e6, e7, e8] at h
  norm_num at h

end Door3GridBoundaryCounterexample

#print axioms Door3GridBoundaryCounterexample.no_strict_cover_at_neg75
