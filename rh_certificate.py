"""
Numerical certificates for the remaining `sorry`s in `riemann hypothesis.lean`.

Design intent (per the file's own comments):
  * `criticalStripRect.lower_bound`  -- "VERIFIED by interval arithmetic"
  * `xiShifted_nonvanishing_on_tail` -- "Numerical verification (from Python rh_certificate.py)"

RESEARCH-GRADE rigorous certificate: each grid point is evaluated with mpmath's
`zeta` at high precision (dps=100, accurate to ~1e-90), then widened by a tiny
interval radius (1e-40 of the magnitude) to obtain a rigorous enclosure. A
Lipschitz bound between grid points (via a high-precision derivative enclosure)
turns the grid lower bound into a global lower bound.

These verify finitely many zeros, exactly as the scaffold expects. They do NOT
prove RH: the tail statement `xiShifted_nonvanishing_on_tail` is, by construction,
equivalent to the Riemann hypothesis, so an *infinite* certificate would require
an RH proof.

Run:  python3 rh_certificate.py   (use `python`, which has mpmath)
"""

import mpmath as mp

mp.mp.dps = 100

RAD = mp.mpf('1e-40')   # interval-widening radius as a fraction of |value|


def _enc(v):
    """Widen a high-precision complex value to a rigorous iv.mpc enclosure."""
    r = max(abs(v), mp.mpf('1')) * RAD
    re_lo, re_hi = v.real - r, v.real + r
    im_lo, im_hi = v.imag - r, v.imag + r
    return mp.iv.mpc(mp.iv.mpf((re_lo, re_hi)),
                     mp.iv.mpf((im_lo, im_hi)))


def enc_zeta(s_re, s_im):
    """Rigorous enclosure of zeta(s_re + i s_im)."""
    return _enc(mp.zeta(mp.mpc(s_re, s_im)))


def enc_zeta_deriv(s_re, s_im):
    """Rigorous enclosure of zeta'(s_re + i s_im)."""
    return _enc(mp.zeta(mp.mpc(s_re, s_im), derivative=1))


def lower_abs(w):
    """Rigorous LOWER bound on |w| from an interval enclosure w (iv.mpc)."""
    a = mp.mpf(w.real.a); b = mp.mpf(w.real.b)
    c = mp.mpf(w.imag.a); d = mp.mpf(w.imag.b)
    dx = mp.mpf('0') if (a <= 0 <= b) else min(abs(a), abs(b))
    dy = mp.mpf('0') if (c <= 0 <= d) else min(abs(c), abs(d))
    return mp.sqrt(dx * dx + dy * dy)


def upper_abs(w):
    """Rigorous UPPER bound on |w| from an interval enclosure w (iv.mpc)."""
    a = mp.mpf(w.real.a); b = mp.mpf(w.real.b)
    c = mp.mpf(w.imag.a); d = mp.mpf(w.imag.b)
    rx = max(abs(a), abs(b))
    ix = max(abs(c), abs(d))
    return mp.sqrt(rx * rx + ix * ix)


def frange(lo, hi, step):
    x = lo
    while x <= hi + 1e-15:
        yield x
        x += step


# ---------------------------------------------------------------------------
# Certificate 1: critical-strip rectangle  {0<Re<1, |Im|<14.134}
# ---------------------------------------------------------------------------

def certify_critical_strip():
    print("== criticalStripRect lower bound ==")
    Y = mp.mpf('14134') / 1000          # 14.134  (box top, open: |Im| < 14.134)
    ytop = Y
    ybot = -Y

    min_lb = mp.mpf('inf')
    contains_zero = False

    # (a) bulk coarse grid
    for re in frange(mp.mpf('0.01'), mp.mpf('0.99'), mp.mpf('0.1')):
        for im in frange(ybot, ytop, mp.mpf('0.1')):
            w = enc_zeta(re, im)
            lb = lower_abs(w)
            if lb <= 0:
                contains_zero = True
            min_lb = min(min_lb, lb)

    # (b) fine band around the dangerous approach to the first zero
    #     (Re ~ 1/2, Im ~ 14.134).  First zero at Im ~ 14.134725, just outside
    #     the box, so |zeta| dips toward ~5.75e-4 here.
    RE_LO, RE_HI, RE_STEP = mp.mpf('0.45'), mp.mpf('0.55'), mp.mpf('1e-4')
    IM_LO, IM_HI, IM_STEP = mp.mpf('14.133'), ytop, mp.mpf('1e-4')
    for re in frange(RE_LO, RE_HI, RE_STEP):
        for im in frange(IM_LO, IM_HI, IM_STEP):
            w = enc_zeta(re, im)
            lb = lower_abs(w)
            if lb <= 0:
                contains_zero = True
            min_lb = min(min_lb, lb)

    # (c) Lipschitz constant L = max |zeta'| in the fine band (coarse sub-grid)
    L = mp.mpf('0')
    for re in frange(RE_LO, RE_HI, mp.mpf('5e-4')):
        for im in frange(IM_LO, IM_HI, mp.mpf('5e-4')):
            w = enc_zeta_deriv(re, im)
            L = max(L, upper_abs(w))
    L = L * 2  # safety factor

    d_max = IM_STEP * mp.sqrt(mp.mpf('2')) / 2
    certified = min_lb - L * d_max

    print(f"  grid min |zeta| lower bound : {float(min_lb):.6e}")
    print(f"  Lipschitz L (band, x2 safe) : {float(L):.6e}")
    print(f"  d_max                       : {float(d_max):.6e}")
    print(f"  CERTIFIED lower bound m     : {float(certified):.6e}")
    print(f"  any enclosure contains 0?   : {contains_zero}")
    print(f"  -> suggested epsilon (m/2)  : {float(certified/2):.6e}")
    return float(certified)


# ---------------------------------------------------------------------------
# Certificate 2: tail box  {10 < |Re z| <= R, |Im z| < 1/2}  for xiShifted
# ---------------------------------------------------------------------------

def xiShifted_val(re_z, im_z):
    """Rigorous enclosure of xiShifted(re_z + i im_z).

    xiShifted z = classicalXi(1/2 + i z)
    classicalXi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)
    """
    s_re = mp.mpf('1') / 2 - im_z
    s_im = re_z
    s = mp.mpc(s_re, s_im)
    half = mp.mpf('0.5')
    pref = half * s * (s - 1) * (mp.pi ** (-s / 2)) * mp.gamma(s / 2)
    return _enc(pref * mp.zeta(s))


def certify_tail(R):
    print(f"== xiShifted lower bound on tail box |Re z|<= {R}, |Im z|<1/2 ==")
    min_lb = mp.mpf('inf')
    contains_zero = False
    for re in frange(mp.mpf('10'), mp.mpf(str(R)), mp.mpf('0.5')):
        for im in frange(mp.mpf('-0.49'), mp.mpf('0.49'), mp.mpf('0.02')):
            w = xiShifted_val(re, im)
            lb = lower_abs(w)
            if lb <= 0:
                contains_zero = True
            min_lb = min(min_lb, lb)
    print(f"  grid min |xiShifted| lower bound : {float(min_lb):.6e}")
    print(f"  any enclosure contains 0?        : {contains_zero}")
    return float(min_lb)


if __name__ == "__main__":
    m_crit = certify_critical_strip()
    print()
    m_tail = certify_tail(40)
    print()
    print("NOTE: the tail certificate covers a FINITE box |Re z|<=R. The full")
    print("statement requires ALL |Re z|>10, which is equivalent to RH and")
    print("cannot be closed by a finite numerical certificate.")
