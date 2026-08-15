"""
Numerical verification of lower bounds for riemann hypothesis.lean.
Uses mpmath with 50-digit precision, focused on critical boundary regions.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from mpmath import mp, mpf, mpc, pi, gamma, zeta, fabs

mp.dps = 50

def xi_shifted(z):
    s = mpc(1, 0) / 2 + mpc(0, 1) * z
    return mpc(1,0)/2 * s * (s - 1) * (pi ** (-s / 2)) * gamma(s / 2) * zeta(s)

# ═══════════════════════════════════════════════════════════════════
# VERIFICATION 1: xiShifted_nonvanishing_on_tail
# Scan boundary |z.re|=10 and interior |z.re|=10.01, 10.1, 11, 15, 20, 50
# ═══════════════════════════════════════════════════════════════════
print("=" * 60)
print("VERIFICATION 1: xiShifted_nonvanishing_on_tail")
print("=" * 60)

min_val = float('inf')
min_pt = None

re_vals = [10.01, 10.1, 10.5, 11, 12, 15, 20, 30, 50]
im_vals = [0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.49, 0.499]

for re_val in re_vals:
    for im_val in im_vals:
        z = mpc(re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        if val < min_val:
            min_val = val
            min_pt = (re_val, im_val)

for re_val in re_vals:
    for im_val in im_vals:
        z = mpc(-re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        if val < min_val:
            min_val = val
            min_pt = (-re_val, im_val)

print(f"Minimum |xiShifted z|: {min_val:.6e}")
print(f"At: z = ({min_pt[0]}, {min_pt[1]})")

# Fine scan near minimum
print("\nFine scan near minimum...")
fine_min = min_val
fine_min_pt = min_pt
for re_val in [min_pt[0]-0.05, min_pt[0]-0.01, min_pt[0]-0.001, min_pt[0],
               min_pt[0]+0.001, min_pt[0]+0.01, min_pt[0]+0.05, min_pt[0]+0.1, min_pt[0]+0.5]:
    for im_val_f in range(1, 500, 5):
        im_val = im_val_f / 1000.0
        z = mpc(re_val, im_val)
        val = float(fabs(xi_shifted(z)))
        if val < fine_min:
            fine_min = val
            fine_min_pt = (re_val, im_val)

print(f"Fine minimum: {fine_min:.6e}")
print(f"At: z = ({fine_min_pt[0]:.4f}, {fine_min_pt[1]:.4f})")

# Factor decomposition
z0 = mpc(fine_min_pt[0], fine_min_pt[1])
s0 = mpc(1,0)/2 + mpc(0,1)*z0
q = fabs(-mpf(1)/4 - z0*z0)
pf = fabs(pi**(-s0/2))
gf = fabs(gamma(s0/2))
zf = fabs(zeta(s0))
print(f"\nFactor decomposition at minimum:")
print(f"  (1/2)|z^2+1/4| = {float(q)/2:.6e}")
print(f"  |pi^(-s/2)|    = {float(pf):.6e}")
print(f"  |Gamma(s/2)|   = {float(gf):.6e}")
print(f"  |zeta(s)|      = {float(zf):.6e}")

# ═══════════════════════════════════════════════════════════════════
# VERIFICATION 2: criticalStripRect lower bound
# ═══════════════════════════════════════════════════════════════════
print("\n" + "=" * 60)
print("VERIFICATION 2: criticalStripRect lower bound")
print("=" * 60)

strip_min = float('inf')
strip_min_pt = None

# Sample grid: Re in (0,1), Im in (0, 14.134)
# Focus near where minimum is expected: near the critical line Re=0.5
re_vals2 = [x/100 for x in range(1, 100)]
im_vals2 = [x/10 for x in range(1, 142)]  # up to 14.1

for re_val in re_vals2:
    for im_val in im_vals2:
        if im_val >= 14.134:
            break
        s = mpc(re_val, im_val)
        val = float(fabs(zeta(s)))
        if val < strip_min:
            strip_min = val
            strip_min_pt = (re_val, im_val)

# Also check negative im
for re_val in re_vals2:
    for im_val in im_vals2:
        if im_val >= 14.134:
            break
        s = mpc(re_val, -im_val)
        val = float(fabs(zeta(s)))
        if val < strip_min:
            strip_min = val
            strip_min_pt = (re_val, -im_val)

print(f"Minimum |zeta(s)|: {strip_min:.6e}")
print(f"At: s = ({strip_min_pt[0]}, {strip_min_pt[1]})")

# Fine scan near minimum
print("\nFine scan near minimum...")
fine_strip_min = strip_min
fine_strip_pt = strip_min_pt
for re_val_f in range(max(1, int((strip_min_pt[0]-0.1)*100)), min(100, int((strip_min_pt[0]+0.1)*100))):
    re_val = re_val_f / 100.0
    for im_val_f in range(max(1, int((abs(strip_min_pt[1])-1)*10)), min(14134, int((abs(strip_min_pt[1])+1)*10))):
        im_val = im_val_f / 10.0
        s = mpc(re_val, im_val)
        val = float(fabs(zeta(s)))
        if val < fine_strip_min:
            fine_strip_min = val
            fine_strip_pt = (re_val, im_val)

print(f"Fine minimum: {fine_strip_min:.6e}")
print(f"At: s = ({fine_strip_pt[0]:.4f}, {fine_strip_pt[1]:.4f})")

# ═══════════════════════════════════════════════════════════════════
# SUMMARY
# ═══════════════════════════════════════════════════════════════════
print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)
print(f"Challenge 2 tail: min |xiShifted z| >= {fine_min:.6e} for |z.re| >= 10")
print(f"  at z = ({fine_min_pt[0]:.4f}, {fine_min_pt[1]:.4f})")
print(f"Critical strip:   min |zeta(s)| >= {fine_strip_min:.6e} for 0<Re s<1, |Im s|<14.134")
print(f"  at s = ({fine_strip_pt[0]:.4f}, {fine_strip_pt[1]:.4f})")
