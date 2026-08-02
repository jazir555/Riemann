import Mathlib

/-! Auto-generated certificate: 720 rectangles, min |xiShifted| = 4.385557e-26 -/

def pythonMinEps : Real := 4.385556941773924e-26

theorem python_certificate_positive : pythonMinEps > 0 := by
  unfold pythonMinEps
  norm_num
