import central_cover_trusted

open Complex Real CellProofEngine CentralCoverAssembly

noncomputable section

namespace Door3TrustedStatementAudit

/-- The legacy universal center-bound statement is inconsistent with the
unbounded `ε` field of `BridgedCell`: a record may choose ε strictly larger
than the norm at its own center. -/
theorem not_universal_bridged_center_bound :
    ¬ (∀ b : BridgedCell,
      b.ε + b.M * Real.sqrt (((b.x1 - b.x0) / 2)^2 + ((b.y1 - b.y0) / 2)^2)
        ≤ ‖xiShifted (((b.x0 + b.x1) / 2 : ℝ) + I * ((b.y0 + b.y1) / 2 : ℝ))‖) := by
  intro h
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + I * (((3 / 20 : ℝ) : ℂ))
  let e : ℝ := ‖xiShifted c‖ + 1
  let b : BridgedCell :=
    { cell := default
      x0 := 0
      x1 := 1
      y0 := (1 / 10 : ℝ)
      y1 := (1 / 5 : ℝ)
      x_lt := by norm_num
      y_lt := by norm_num
      ε := e
      ε_pos := by
        dsimp [e]
        linarith [norm_nonneg (xiShifted c)]
      M := 0
      M_nonneg := by norm_num
      y0_pos := by norm_num
      y1_lt := by norm_num }
  have hb := h b
  dsimp [b, e, c] at hb
  norm_num at hb

end Door3TrustedStatementAudit

#print axioms Door3TrustedStatementAudit.not_universal_bridged_center_bound
