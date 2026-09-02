#!/usr/bin/env python3
"""Compute Taylor coefficients of Xi(z) = xi(1/2 + iz) at z=0 using mpmath."""

import mpmath

mpmath.mp.dps = 50

def xi(s):
    """Riemann xi function: xi(s) = 0.5 * s * (s-1) * pi^(-s/2) * Gamma(s/2) * zeta(s)"""
    return 0.5 * s * (s - 1) * mpmath.pi**(-s/2) * mpmath.gamma(s/2) * mpmath.zeta(s)

def Xi(z):
    """Xi(z) = xi(1/2 + iz)"""
    return xi(0.5 + 1j * z)

# Compute Taylor coefficients: taylorCoeff(n) = Xi^(n)(0) / n!
print("Taylor coefficients of Xi(z) = xi(1/2 + iz) at z=0")
print("=" * 70)
print()

for n in range(0, 11):
    # nth derivative of Xi at 0
    deriv = mpmath.diff(Xi, 0, n)
    coeff = deriv / mpmath.factorial(n)
    # Take real part (imaginary should be ~0 for even n)
    coeff_real = mpmath.re(coeff)
    print(f"taylorCoeff({n}) = Xi^({n})(0)/{n}! = {coeff_real}")
    print(f"  Float value: {float(coeff_real)}")
    print()
