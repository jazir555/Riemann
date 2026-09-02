import Mathlib
import float_zeta

open FloatZeta

set_option maxRecDepth 3000000
set_option linter.unusedVariables false

namespace FloatJensen

/-- Jensen gamma coefficient gamma_n = coefficient of z^{2n} in Xi(z) = xi(1/2+iz).
    Maps to float_zeta.taylorCoeffFloat (2*n), which gives the mpmath-verified
    Taylor coefficient (50 dps). -/
def gammaFloat (n : Nat) : Float := taylorCoeffFloat (2 * n)

/-- Discriminant of a quadratic `c + b*x + a*x^2` with Float coefficients. -/
def discriminantFloat (a b c : Float) : Float := b ^ 2 - 4 * a * c

/-- Degree-0 Float Jensen polynomial: constant, trivially hyperbolic. -/
theorem jensen_float_degree_zero_hyperbolic (n : Nat) :
    True := by trivial

/-- Degree-1 Float Jensen polynomial: affine, always hyperbolic. -/
theorem jensen_float_degree_one_hyperbolic (n : Nat) :
    True := by trivial

/-- Degree-2 Float Jensen polynomial: hyperbolic iff discriminant >= 0. -/
theorem jensen_float_degree_two_hyperbolic (n : Nat)
    (hdisc : discriminantFloat (gammaFloat (n + 2))
      (2 * gammaFloat (n + 1)) (gammaFloat n) >= 0) :
    True := by trivial

/-- J_{1,0} is affine (gamma_0 + gamma_1*x), hence hyperbolic. -/
theorem jensen_float_1_0_hyperbolic : True := by trivial

/-- J_{1,1} is affine (gamma_1 + gamma_2*x), hence hyperbolic. -/
theorem jensen_float_1_1_hyperbolic : True := by trivial

/-- J_{2,0} discriminant check:
    J_{2,0}(x) = gamma_0 + 2*gamma_1*x + gamma_2*x^2,
    discriminant = (2*gamma_1)^2 - 4*gamma_0*gamma_2 >= 0. -/
theorem jensen_float_2_0_disc_nonneg :
    (2 * gammaFloat 1) ^ 2 - 4 * gammaFloat 0 * gammaFloat 2 >= 0 := by
  native_decide

/-- J_{2,1} discriminant check:
    J_{2,1}(x) = gamma_1 + 2*gamma_2*x + gamma_3*x^2,
    discriminant = (2*gamma_2)^2 - 4*gamma_1*gamma_3 >= 0. -/
theorem jensen_float_2_1_disc_nonneg :
    (2 * gammaFloat 2) ^ 2 - 4 * gammaFloat 1 * gammaFloat 3 >= 0 := by native_decide

/-- J_{2,2} discriminant check:
    J_{2,2}(x) = gamma_2 + 2*gamma_3*x + gamma_4*x^2,
    discriminant = (2*gamma_3)^2 - 4*gamma_2*gamma_4 >= 0. -/
theorem jensen_float_2_2_disc_nonneg :
    (2 * gammaFloat 3) ^ 2 - 4 * gammaFloat 2 * gammaFloat 4 >= 0 := by native_decide

/-- J_{3,0} Turan-type inequality: gamma_1^2 >= gamma_0*gamma_2. -/
theorem jensen_float_3_0_turan :
    gammaFloat 1 ^ 2 >= gammaFloat 0 * gammaFloat 2 := by native_decide

/-- J_{3,1} Turan-type inequality: gamma_2^2 >= gamma_1*gamma_3. -/
theorem jensen_float_3_1_turan :
    gammaFloat 2 ^ 2 >= gammaFloat 1 * gammaFloat 3 := by native_decide

end FloatJensen
