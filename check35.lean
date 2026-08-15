import Mathlib

open scoped Topology

set_option maxHeartbeats 800000 in
example (g : ℂ → ℂ) (z : ℂ) (hgd : Differentiable ℂ g) :
    HasDerivAt (fun w : ℂ => Complex.exp (g w)) (Complex.exp (g z) * deriv g z) z := by
  simpa [mul_comm] using HasDerivAt.comp z (Complex.hasDerivAt_exp (g z)) hgd.differentiableAt.hasDerivAt

set_option maxHeartbeats 800000 in
example (g : ℂ → ℂ) (z : ℂ) (hgd : Differentiable ℂ g) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.exp (g w)) z := by
  simpa using DifferentiableAt.comp z (Complex.differentiableAt_exp (x := g z)) hgd.differentiableAt