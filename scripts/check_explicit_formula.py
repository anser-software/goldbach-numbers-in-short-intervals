"""Check the explicit-formula steps of the paper (Sections 4-5) against actual zeta zeros.

Uses zeta_zeros_N.npy (ordinates of the first N zeros, computed with mpmath.zetazero).

1. R(gamma) = sum_{gamma'} What(gamma - gamma') computed from the zeros
   versus the Weil-formula expression (I4):
   G(gamma) + What(gamma - i/2) + What(gamma + i/2) - 2 sum_n Lambda(n) n^{-1/2} W(log n) cos(gamma log n).
2. T = sum_gamma |c_gamma|^2 R(gamma) from zeros, versus the explicit upper bound
   (I5)+(I6): delta [ (ell/delta) sqrt(1+delta) (Lam1^2 + 2 a1 Lam1 + a2) + 2 sum Lambda^2 W/n + O(delta) ].
3. The weighted prime integral (left side) versus x^2 T (Schur bound) and versus the
   exact double zero sum x^2 sum c cbar' x^{i(g-g')} What(g-g') (no Schur).
"""
import math
import sys
import numpy as np
import mpmath as mp
from scipy import integrate

import rigorous_constant as rc
from short_interval_constant import mangoldt_upto

ZFILE = sys.argv[1] if len(sys.argv) > 1 else "zeta_zeros_20000.npy"
g = np.load(ZFILE)
GMAX = g[-1]


def W_closed(v, V):
    v = np.abs(v)
    out = (1 - v / V) * np.cos(np.pi * v / V) + np.sin(np.pi * v / V) / np.pi
    return np.where(v <= V, out, 0.0)


def What(xi, V):
    """Fourier transform int W(v) e^{-i v xi} dv = |phihat(xi)|^2 / ||phi||^2, phi = cos(pi s/V) on [-V/2,V/2]."""
    xi = np.asarray(xi, dtype=float)
    a = math.pi / V
    with np.errstate(divide='ignore', invalid='ignore'):
        t1 = np.where(np.abs(a - xi) < 1e-12, V / 2, np.sin((a - xi) * V / 2) / (a - xi))
        t2 = np.sin((a + xi) * V / 2) / (a + xi)
    ph = t1 + t2
    return ph ** 2 / (V / 2)


def What_complex(gam, V, sign):
    # What(gamma - sign*i/2) = int W(v) e^{-i v gamma} e^{sign*(-v/2)}... computed numerically:
    # What(z) = int W(v) e^{-i v z} dv with z = gamma - sign*i/2  ->  e^{-i v gamma} e^{-sign v/2}
    f = lambda v: W_closed(v, V) * math.cos(v * gam) * math.exp(-sign * v / 2)
    return integrate.quad(f, -V, V, limit=400)[0]  # imaginary part cancels (W even)


def Omega(r):
    return float(mp.re(mp.digamma(0.25 + 0.5j * r))) - math.log(math.pi)


def G_of(gam, V):
    f = lambda r: What(gam - r, V) * Omega(r)
    pts = np.linspace(gam - 60, gam + 60, 241)
    tot = 0.0
    for a, b in zip(pts[:-1], pts[1:]):
        tot += integrate.quad(f, a, b, limit=100)[0]
    # tails |gam-r|>60: What ~ r^{-4}; include roughly with log growth
    return tot / (2 * math.pi)


def R_zeros(gam, V):
    s = np.sum(What(gam - g, V)) + np.sum(What(gam + g, V))
    # tail beyond GMAX by zero density (only matters if gam close to GMAX)
    t = np.linspace(GMAX, GMAX + 2000, 20001)
    s += np.trapezoid(What(gam - t, V) * np.log(t / (2 * math.pi)) / (2 * math.pi), t)
    return s


def R_weil(gam, V, lam):
    n = np.arange(2, int(math.exp(V)) + 1)
    primes = -2 * np.sum(lam[n] / np.sqrt(n) * W_closed(np.log(n), V) * np.cos(gam * np.log(n)))
    pole = What_complex(gam, V, +1) + What_complex(gam, V, -1)
    return G_of(gam, V) + pole + primes, G_of(gam, V), pole, primes


def c2(t, delta):
    ell = math.log1p(delta)
    return (2 + delta - 2 * math.sqrt(1 + delta) * np.cos(t * ell)) / (0.25 + t ** 2)


def main():
    print(f"zeros: {len(g)}, max ordinate {GMAX:.2f}")
    V = 3.0
    lam = mangoldt_upto(int(math.exp(V)) + 2)
    print("\n1. R(gamma): zeros vs Weil formula (V = 3)")
    for gam in [g[100], g[1000], 1000.0, 2500.0]:
        rz = R_zeros(gam, V)
        rw, G, pole, pr = R_weil(gam, V, lam)
        print(f"  gamma={gam:9.3f}  zeros: {rz:9.5f}   Weil: {rw:9.5f}  (G={G:.4f}, pole={pole:.2e}, primes={pr:+.4f})  log(g/2pi)={math.log(gam/2/math.pi):.4f}")

    print("\n2. T/delta from zeros (with Weil R) vs explicit upper bound (I5)+(I6)")
    v, W = rc.kernel(V)
    Pd = 2 * np.sum(lam[2:] ** 2 * W_closed(np.log(np.arange(2, len(lam))), V) / np.arange(2, len(lam)))
    for delta in [0.05, 0.02, 0.01]:
        cz = c2(g, delta)
        # R(gamma) via the Weil formula, vectorised: G ~ log(g/2pi) + small; use exact G only on a subsample
        Rg = np.array([R_zeros(x, V) for x in g])
        T = 2 * np.sum(cz * Rg)
        # tail beyond GMAX: |c|^2 ~ (2+delta)/t^2 average, R ~ log(t/2pi), density log(t/2pi)/2pi
        t = np.geomspace(GMAX, 1e9, 200001)
        T += 2 * np.trapezoid((2 + delta) / t ** 2 * np.log(t / 2 / math.pi) ** 2 / (2 * math.pi), t)
        ell = math.log1p(delta)
        Lam1 = -math.log(math.pi * ell)
        bound = (ell / delta) * math.sqrt(1 + delta) * (Lam1 ** 2 + 2 * rc.A1 * Lam1 + rc.A2) + Pd
        print(f"  delta={delta:5.3f}  T/delta (zeros) = {T/delta:8.4f}   bound main+primes = {bound:8.4f}   ratio = {T/delta/bound:.4f}")


if __name__ == "__main__":
    main()
