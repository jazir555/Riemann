import Mathlib

open Complex

noncomputable section

variable (xiShifted : ℂ → ℂ)

noncomputable def testFirstLaguerreCoefficient (r : ℝ) : ℝ :=
  ‖deriv xiShifted (r : ℂ)‖ ^ 2 -
    ((iteratedDeriv 2 xiShifted (r : ℂ)) * star (xiShifted (r : ℂ))).re

noncomputable def testLaguerreCoefficient (n : ℕ) (r : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℝ) ^ (n + j) * (Nat.choose (2 * n) j : ℝ) *
        ((iteratedDeriv j xiShifted (r : ℂ)) *
          star (iteratedDeriv (2 * n - j) xiShifted (r : ℂ))).re) /
    (Nat.factorial (2 * n) : ℝ)

example (r : ℝ) :
    testLaguerreCoefficient xiShifted 1 r = testFirstLaguerreCoefficient xiShifted r := by
  norm_num [testLaguerreCoefficient, testFirstLaguerreCoefficient,
    Finset.sum_range_succ]
  rw [Complex.sq_norm]
  change _ =
    (deriv xiShifted (r : ℂ)).re * (deriv xiShifted (r : ℂ)).re +
      (deriv xiShifted (r : ℂ)).im * (deriv xiShifted (r : ℂ)).im - _
  ring

example (r : ℝ) :
    testLaguerreCoefficient xiShifted 0 r = ‖xiShifted (r : ℂ)‖ ^ 2 := by
  norm_num [testLaguerreCoefficient, Finset.sum_range_succ]
  rw [Complex.sq_norm]
  change _ = (xiShifted (r : ℂ)).re ^ 2 + (xiShifted (r : ℂ)).im ^ 2
  ring
