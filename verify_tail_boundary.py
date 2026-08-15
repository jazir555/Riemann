"""
Detailed scan near |z.re| = 10 boundary for the tail certificate.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from mpmath import mp, mpf, mpc, pi, gamma, zeta, fabs

mp.dps = 50

def xi_shifted(z):
    s = mpc(1, 0) / 2 + mpc(0, 1) * z
    return mpc(1,0)/2 * s * (s - 1) * (pi ** (-s / 2)) * gamma(s / 2) * zeta(s)

print("Scanning near |z.re| = 10 boundary...")
print(f"{'z.re':>10} {'z.im':>10} {'|xiShifted|':>15}")
print("-" * 40)

min_val = float('inf')
min_pt = None

for re_f in range(10000, 12001, 10):
    re_val = re_f / 1000.0
    for im_f in range(1, 500, 5):
        im_val = im_f / 1000.0
        z = mpc(re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        if val < min_val:
            min_val = val
            min_pt = (re_val, im_val)

# Also scan negative re
for re_f in range(-12001, -9999, 10):
    re_val = re_f / 1000.0
    for im_f in range(1, 500, 5):
        im_val = im_f / 1000.0
        z = mpc(re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        if val < min_val:
            min_val = val
            min_pt = (re_val, im_val)

print(f"\nMinimum near boundary: {min_val:.6e}")
print(f"At: z = ({min_pt[0]}, {min_pt[1]})")

# Show some representative values
print("\nRepresentative values:")
for re_val in [10.01, 10.1, 11, 15, 20]:
    for im_val in [0.001, 0.01, 0.1, 0.3, 0.49]:
        z = mpc(re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        print(f"  z=({re_val:.2f}, {im_val:.3f}): |xiShifted| = {val:.6e}")

# Analytical lower bound via triangle inequality
# |xiShifted z| = (1/2)|z^2 + 1/4| * |pi^(-s/2)| * |Gamma(s/2)| * |zeta(s)|
# For s = 1/2 + iz:
#   |pi^(-s/2)| = pi^(-1/4) (independent of z.im)
#   |Gamma(s/2)| = |Gamma(1/4 + iz/2)| 
#   |zeta(s)| = |zeta(1/2 + iz)|
#
# Lower bound approach:
# |z^2 + 1/4| >= |z.re|^2 - 1/4 (when |z.im| < 1/2)
# For |z.re| >= 10: |z^2 + 1/4| >= 99.75
#
# We need lower bounds on |Gamma(1/4 + it)| and |zeta(1/2 + it)| for t = z.im/2

print("\n--- Analytical bound components ---")
pi_pow = float(mpf(1) / (pi ** mpc(1,0)/4))
print(f"pi^(-1/4) = {pi_pow:.6f}")

# Gamma(1/4 + it) for t in [0, 0.25] (since z.im in (0, 0.5))
print("\n|Gamma(1/4 + it)| for small t:")
for t_f in range(0, 251, 25):
    t = t_f / 1000.0
    val = float(fabs(gamma(mpc(1,0)/4 + mpc(0,1)*t)))
    print(f"  t={t:.3f}: {val:.6f}")

# zeta(1/2 + it) for t in [0, 0.25]
print("\n|zeta(1/2 + it)| for small t:")
for t_f in range(0, 251, 25):
    t = t_f / 1000.0
    val = float(fabs(zeta(mpc(1,0)/2 + mpc(0,1)*t)))
    print(f"  t={t:.3f}: {val:.6f}")
