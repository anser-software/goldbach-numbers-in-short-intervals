"""Floating-point cross-checks against the first 20 000 zeta zeros (not used in the proof).

Uses zeta_zeros_20000.npy: the ordinates 0 < gamma_1 < ... < gamma_20000 (about 18 digits,
computed with mpmath.zetazero), in this directory unless a path is given as argv[1].

1. The explicit formula for psi (the Lean hypothesis ExplicitFormulaPsi): for non-integer y > 1,
       sum_{|gamma| <= T} y^rho/rho  ->  y - psi(y) - log(2 pi) - (1/2) log(1 - y^{-2}),
   compared for T = gamma_5000, gamma_10000, gamma_20000.
2. Lemma 9: R(gamma) = sum_{gamma'} What(gamma - gamma') computed from the zeros, against the
   Weil-formula expression G(gamma) + What(gamma - i/2) + What(gamma + i/2)
   - 2 sum_n Lambda(n) n^{-1/2} W(log n) cos(gamma log n), with V = 3.
3. Lemma 12 (L4): sum_gamma gamma^{-2} over all zeros (both signs), against the bound 0.12.
4. T/delta = sum_gamma |c(gamma)|^2 R(gamma) / delta from the zeros, against the main and prime
   terms of the bound (Lemmas 9-11), for V = 3 and three values of delta.

    .venv/bin/python scripts/check_explicit_formula.py          (a few minutes)
"""
import math
import os
import sys
import numpy as np
from scipy import integrate, special

HERE = os.path.dirname(os.path.abspath(__file__))
ZFILE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "zeta_zeros_20000.npy")
g = np.load(ZFILE)
GMAX = float(g[-1])

EULER = 0.57721566490153286061
A1 = 1 - EULER - math.log(2)
A2 = A1 ** 2 + 1 + math.pi ** 2 / 12


def mangoldt_upto(n):
    """Lambda(m) for m = 0..n."""
    lam = np.zeros(n + 1)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, n + 1):
        if sieve[p]:
            sieve[p * p::p] = False
            q = p
            while q <= n:
                lam[q] = math.log(p)
                q *= p
    return lam


def psi(y):
    return float(np.sum(mangoldt_upto(int(math.floor(y)))))


def W_closed(v, V):
    v = np.abs(v)
    out = (1 - v / V) * np.cos(np.pi * v / V) + np.sin(np.pi * v / V) / np.pi
    return np.where(v <= V, out, 0.0)


def What(xi, V):
    """What(xi) = int W(v) e^{-i v xi} dv = phihat(xi)^2/||phi||^2, phi = cos(pi s/V) on [-V/2, V/2].
    The closed form is entire, so it also gives What at complex xi (the pole terms of Lemma 9)."""
    xi = np.asarray(xi, dtype=complex)
    a = math.pi / V

    def sinc_part(z):
        small = np.abs(z) < 1e-8
        zs = np.where(small, 1.0, z)
        return np.where(small, V / 2, np.sin(zs * V / 2) / zs)

    ph = sinc_part(a - xi) + sinc_part(a + xi)
    out = ph ** 2 / (V / 2)
    return out.real if np.all(np.abs(out.imag) < 1e-12 * (1 + np.abs(out.real))) else out


def Omega(r):
    return float(special.psi(0.25 + 0.5j * r).real) - math.log(math.pi)


def G_of(gam, V, width=400.0):
    """(2 pi)^{-1} int What(gam - r) Omega(r) dr over |r - gam| <= width (What decays like r^{-4})."""
    f = lambda r: float(What(gam - r, V)) * Omega(r)
    pts = np.arange(gam - width, gam + width + 1e-9, 1.0)
    tot = sum(integrate.quad(f, a, b, limit=100, epsabs=1e-13)[0] for a, b in zip(pts[:-1], pts[1:]))
    return tot / (2 * math.pi)


def R_zeros(gam, V):
    s = np.sum(What(gam - g, V)) + np.sum(What(gam + g, V))
    # zeros beyond GMAX, by the zero density log(t/2 pi)/(2 pi); negligible unless gam is near GMAX
    t = np.linspace(GMAX, GMAX + 2000, 20001)
    s += np.trapezoid(What(gam - t, V) * np.log(t / (2 * math.pi)) / (2 * math.pi), t)
    return float(s)


def R_weil(gam, V, lam):
    n = np.arange(2, int(math.exp(V)) + 1)
    primes = -2 * np.sum(lam[n] / np.sqrt(n) * W_closed(np.log(n), V) * np.cos(gam * np.log(n)))
    pole = float(np.real(What(gam - 0.5j, V) + What(gam + 0.5j, V)))
    G = G_of(gam, V)
    return G + pole + primes, G, pole, primes


def c2(t, delta):
    ell = math.log1p(delta)
    return (2 + delta - 2 * math.sqrt(1 + delta) * np.cos(t * ell)) / (0.25 + t ** 2)


def main():
    print(f"zeros: {len(g)}, largest ordinate {GMAX:.2f}")

    print("\n1. Explicit formula for psi: truncated zero sum vs y - psi(y) - log 2pi - log(1 - y^-2)/2")
    for y in [10.5, 100.5, 1000.5]:
        rhs = y - psi(y) - math.log(2 * math.pi) - 0.5 * math.log(1 - y ** -2)
        rho = 0.5 + 1j * g
        terms = 2 * np.real(np.exp(rho * math.log(y)) / rho)     # rho and its conjugate
        row = []
        for m in [5000, 10000, 20000]:
            row.append(f"T = {g[m - 1]:8.1f}: diff {np.sum(terms[:m]) - rhs:+.2e}")
        print(f"  y = {y:7.1f}  target {rhs:+.6f}   " + ";  ".join(row))

    V = 3.0
    lam = mangoldt_upto(int(math.exp(V)) + 2)
    print("\n2. Lemma 9, R(gamma): zeros vs Weil formula (V = 3)")
    worst = 0.0
    for gam in [float(g[100]), float(g[1000]), 1000.0, 2500.0]:
        rz = R_zeros(gam, V)
        rw, G, pole, pr = R_weil(gam, V, lam)
        worst = max(worst, abs(rz - rw))
        print(f"  gamma = {gam:9.3f}  zeros: {rz:.9f}  Weil: {rw:.9f}  diff {rz - rw:+.1e}"
              f"  (G = {G:.5f}, poles = {pole:+.2e}, primes = {pr:+.5f})")
    print(f"  largest difference: {worst:.1e}")

    print("\n3. Lemma 12 (L4): sum over zeros of gamma^{-2}")
    tail = (math.log(GMAX / (2 * math.pi)) + 1) / (math.pi * GMAX)   # 2 int_GMAX^inf log(t/2pi)/(2pi t^2) dt
    s = 2 * float(np.sum(1 / g ** 2)) + tail
    print(f"  2 sum_(n<=20000) gamma_n^-2 + tail estimate = {s:.6f}   (bound used in the paper: 0.12)")

    print("\n4. T/delta from the zeros vs the main and prime terms of the bound (V = 3)")
    Rg = np.array([R_zeros(x, V) for x in g])
    n = np.arange(2, len(lam))
    Pd = 2 * np.sum(lam[2:] ** 2 * W_closed(np.log(n), V) / n)
    for delta in [0.05, 0.02, 0.01]:
        T = 2 * np.sum(c2(g, delta) * Rg)
        # zeros beyond GMAX: |c|^2 ~ (2 + delta)/t^2 on average, R ~ log(t/2 pi), density log(t/2 pi)/2 pi
        t = np.geomspace(GMAX, 1e9, 200001)
        T += 2 * np.trapezoid((2 + delta) / t ** 2 * np.log(t / 2 / math.pi) ** 2 / (2 * math.pi), t)
        ell = math.log1p(delta)
        Lam1 = -math.log(math.pi * ell)
        bound = (ell / delta) * math.sqrt(1 + delta) * (Lam1 ** 2 + 2 * A1 * Lam1 + A2) + Pd
        print(f"  delta = {delta:5.3f}  T/delta (zeros) = {T / delta:8.4f}   main + prime terms = {bound:8.4f}"
              f"   ratio = {T / delta / bound:.4f}")


if __name__ == "__main__":
    main()
