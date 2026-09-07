#!/usr/bin/env python3
"""Generate high precision *targets* for the Door 3 fine-grid proof.

The output deliberately records sampled numerical estimates, rather than
pretending that mpmath output is a Lean proof.  A later formal interval
implementation can replace the sampled bounds by certified enclosures.
"""
from __future__ import annotations

import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80

X = [(-10, -7.5), (-8, -5.5), (-6, -3.5), (-4, -1.5), (-2, .5),
     (0, 2.5), (2, 4.5), (4, 6.5), (6, 8.5), (7.5, 10)]
Y = [(.3, .49), (.2, .4), (.1, .3), (.01, .2)]

def xi(z: complex) -> complex:
    """Classical xi in the normalization used by TailProofEngine."""
    s = mp.mpc("0.5") + 1j * z
    return (.5 * s * (s - 1) * mp.power(mp.pi, -s / 2)
            * mp.gamma(s / 2) * mp.zeta(s))

def deriv(z: complex) -> complex:
    s = mp.mpc("0.5") + 1j * z
    a = (.5 * s * (s - 1) * mp.power(mp.pi, -s / 2)
         * mp.gamma(s / 2))
    zz = mp.zeta(s)
    # d/dz = i d/ds; this avoids an expensive numerical differentiation.
    log_a_prime = 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2
    return 1j * a * (log_a_prime * zz + mp.zeta(s, derivative=1))

def f(x: float, y: float) -> mp.mpc:
    return xi(mp.mpc(x, y))

def d(x: float, y: float) -> mp.mpf:
    return abs(deriv(mp.mpc(x, y)))

rows = []
for ix, (x0, x1) in enumerate(X):
    for iy, (y0, y1) in enumerate(Y):
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        # A mesh is useful for choosing targets; it is not a proof of a sup.
        mesh_n = 13
        samples = [d(x0 + (x1-x0)*i/(mesh_n-1), y0 + (y1-y0)*j/(mesh_n-1))
                   for i in range(mesh_n) for j in range(mesh_n)]
        center = abs(f(cx, cy))
        mesh_max = max(samples)
        radius = mp.sqrt(((x1-x0)/2)**2 + ((y1-y0)/2)**2)
        # Conservative target parameters with a visible numerical margin.
        M = mp.mpf("1.05") * mesh_max
        eps = mp.mpf("0.10") * center
        margin = center - (eps + M*radius)
        rows.append({
            "index": ix*4 + iy, "x0": str(x0), "x1": str(x1),
            "y0": str(y0), "y1": str(y1), "cx": mp.nstr(cx, 50),
            "cy": mp.nstr(cy, 50), "center_norm": mp.nstr(center, 50),
            "mesh_deriv_max": mp.nstr(mesh_max, 50),
            "target_M": mp.nstr(M, 50), "target_epsilon": mp.nstr(eps, 50),
            "radius": mp.nstr(radius, 50), "sampled_margin": mp.nstr(margin, 50),
            "samples": mesh_n*mesh_n,
        })

out = {
    "description": "Door 3 fine-grid numerical targets; sampled, not certified",
    "precision_digits": mp.mp.dps,
    "grid_x": X, "grid_y": Y, "rows": rows,
    "soundness": "Values require formal interval enclosures before entering a Lean theorem.",
}
dest = Path(__file__).resolve().parent.parent / "door3_numeric_targets.json"
dest.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
print(f"wrote {dest} ({len(rows)} cells)")
print("minimum sampled margin:", min(mp.mpf(r["sampled_margin"]) for r in rows))
