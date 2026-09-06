import float_real_bridge

open Float Real

noncomputable section

namespace Door3FloatBridgeAudit

def r00FloatRadius : ℝ :=
  Float.toReal
    (Float.sqrt ((((-7.5 : Float) - (-10.0 : Float)) / 2)^2 +
      (((0.2 : Float) - (0.01 : Float)) / 2)^2))

def r00RealRadius : ℝ :=
  Real.sqrt ((((-7.5 : ℝ) - (-10 : ℝ)) / 2)^2 +
    (((0.2 : ℝ) - (0.01 : ℝ)) / 2)^2)

private theorem r00FloatRadius_parts :
    (Float.sqrt ((((-7.5 : Float) - (-10.0 : Float)) / 2)^2 +
      (((0.2 : Float) - (0.01 : Float)) / 2)^2)).toRatParts =
      some (5645734119880132, -52) := by
  native_decide

theorem r00_float_radius_ne_real : r00FloatRadius ≠ r00RealRadius := by
  intro h
  have hs := congrArg (fun x : ℝ => x ^ 2) h
  unfold r00FloatRadius Float.toReal at hs
  simp [r00FloatRadius_parts] at hs
  unfold r00RealRadius at hs
  have hnonneg :
      (0 : ℝ) ≤ (((-7.5 : ℝ) - (-10 : ℝ)) / 2)^2 +
        (((0.2 : ℝ) - (0.01 : ℝ)) / 2)^2 := by
    positivity
  rw [Real.sq_sqrt hnonneg] at hs
  norm_num at hs

theorem r00_float_radius_le_real : r00FloatRadius ≤ r00RealRadius := by
  have hnonneg :
      (0 : ℝ) ≤ (((-7.5 : ℝ) - (-10 : ℝ)) / 2)^2 +
        (((0.2 : ℝ) - (0.01 : ℝ)) / 2)^2 := by
    positivity
  have hsqrt : r00RealRadius ^ 2 =
      (((-7.5 : ℝ) - (-10 : ℝ)) / 2)^2 +
        (((0.2 : ℝ) - (0.01 : ℝ)) / 2)^2 := by
    unfold r00RealRadius
    rw [Real.sq_sqrt hnonneg]
  unfold r00FloatRadius r00RealRadius Float.toReal
  simp [r00FloatRadius_parts]
  norm_num at hsqrt ⊢
  have hsq :
      (1411433529970033 / 1125899906842624 : ℝ) ^ 2 ≤ 62861 / 40000 := by
    norm_num
  have hsq' :
      (1411433529970033 / 1125899906842624 : ℝ) ^ 2 ≤
        (Real.sqrt 62861 / 200) ^ 2 := by
    have hs62861 : (Real.sqrt 62861 / 200 : ℝ) ^ 2 = 62861 / 40000 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hs62861]
    exact hsq
  exact (sq_le_sq₀ (by norm_num) (by positivity)).mp hsq'

end Door3FloatBridgeAudit
