"""Rigorous range argument for C = 2 (Section 8 of the paper).

Assume RH, C = 2, x >= 3.9e18, L = log x >= L0 = log(3.9e18) = 42.807..., V = 3 sqrt(L),
delta = 2 L^2 / x, ell = log(1 + delta), sigma = pi/V.  A contradiction (hence a Goldbach number
in (x, x + 2 log^2 x]) follows from (Section 8 of the paper, inequality (target))

    (sqrt(T) + sqrt(E) + sqrt(B))^2  <  2 L^2 m_W                                     (*)

with every quantity bounded explicitly below (no placeholders).  Labels refer to section 10.

    T <= Tmain + Tprime + R_T, where
      Tmain  = (Lam1 + a1)^2 + (a2 - a1^2),  Lam1 = L - 2 log L - log(2 pi)            [(I5), exact]
      Tprime = (2/pi^2) V^2 + 2 c_L2,         c_L2 = 0.04                              [(I6) + (K2) + Lemma L2]
      R_T    = delta (L^2 + 3L)                              (factor sqrt(1+delta)ell/delta, Lam1 shift <= delta)
             + delta [(8/3) L^3 + 33 L^2 + 136 L + 250] + 0.1 delta                    [(I5) N(T) piece, delta^2/4 piece]
             + 0.025 delta (1 + delta)(1/4 + sigma^2)                                  [(I4) Jensen 1/t^2 piece]
             + 2.02 delta (psi(e^V) + 2.4 (V^2/2 + 0.04)/log 2)                       [(I6) E_n]
             + 0.2 delta (1 + delta)(sigma^2 + sigma + 1/4) e^{V/2}                    [(I7) poles]
    E <= ((L + V + 1)/log 2)(1 + delta) * Sum_k                                        [(I8) prime powers]
    B <= 0.8 delta e^{-5(L - V)}                                                       [(I8) B term]
    m_W >= 1/2 - 9.55/V^2 - e^{-V}                                                     [(K1)]

Rearranged: (*) <=> M(L) > R(L) with
    M(L) = 2L^2 (1/2 - 9.55/V^2 - e^{-V}) - Tmain - Tprime        (increasing for L >= L0)
    R(L) = R_T + 2 sqrt(T)(sqrt E + sqrt B) + (sqrt E + sqrt B)^2
         <= Rt(L) := R_T + 2L (sqrt E + sqrt B) + (sqrt E + sqrt B)^2   (using T <= L^2; checked)
Every summand of Rt is decreasing for L >= L0 (checked below on a grid, and argued in section 10),
so M(L) >= M(L0) > Rt(L0) >= Rt(L) >= R(L) for all L >= L0.
"""
import math
import numpy as np

A1 = 1 - 0.5772156649015329 - math.log(2)     # a1 = -0.27036...
A2 = 1.895563101630140345                      # a2 (exact, rigorous_constant.py)
C_L2 = 0.04                                    # Lemma L2 (lambda2_constant.py: 0.03907)
SUM_INV_GAMMA2 = 0.12                          # sum over all zeros of 1/gamma^2 (Lemma L4; true value 0.0462)
THETA_RS = 1.01624                             # theta(t) < 1.01624 t (Rosser-Schoenfeld 1962)
L0 = math.log(3.9e18)


def pieces(L):
    V = 3 * math.sqrt(L)
    sig = math.pi / V
    logdelta = math.log(2) + 2 * math.log(L) - L
    d = math.exp(logdelta)
    lam1 = L - 2 * math.log(L) - math.log(2 * math.pi)
    Tmain = (lam1 + A1) ** 2 + (A2 - A1 ** 2)
    Tprime = (2 / math.pi ** 2) * V ** 2 + 2 * C_L2
    # delta * psi(e^V) with Schoenfeld (RH): psi(e^V) <= e^V + e^{V/2} V^2/(8 pi), e^V >= 73.2; log space
    d_psi = math.exp(logdelta + V) + math.exp(logdelta + V / 2) * V ** 2 / (8 * math.pi)
    RT = {
        "delta-shift": d * (L ** 2 + 3 * L),
        "N(T)":        d * ((8 / 3) * L ** 3 + 33 * L ** 2 + 136 * L + 250) + 0.1 * d,
        "Jensen":      0.06 * d * (1 + d) * (0.25 + sig ** 2),
        "E_n":         2.02 * (d_psi + d * 2.4 * (V ** 2 / 2 + 0.04) / math.log(2)),
        "poles":       0.5 * (1 + d) * (sig ** 2 + sig + 0.25) * math.exp(logdelta + V / 2),
    }
    # (I8): sum_{k>=2} sum_{p^k >= y0} log^2 p / p^k, y0 = x e^{-V}, via theta(t) <= 1.01624 t
    ly0 = L - V
    # closed form: k = 2 term; 3 <= k < k1 (count <= ly0/log 2, each <= 1.01624 (ly0/2 + 0.75) e^{-2 ly0/3});
    # k >= k1 (z = 2): <= 3.1 * 2^{-(k1-2)} <= 12.4 e^{-ly0}, since 2^{k1} > y0.
    s = THETA_RS * ((ly0 + 2) * math.exp(-ly0 / 2)
                    + (ly0 / math.log(2)) * (ly0 / 2 + 0.75) * math.exp(-2 * ly0 / 3)
                    + 12.4 / THETA_RS * math.exp(-ly0))
    E = ((L + V + 1) / math.log(2)) * (1 + d) * s
    B = 0.8 * d * math.exp(-5 * (L - V))
    m_low = 0.5 - 9.55 / V ** 2 - math.exp(-V)
    M = 2 * L * L * m_low - Tmain - Tprime
    sRT = sum(RT.values())
    T = Tmain + Tprime + sRT
    sq = math.sqrt(E) + math.sqrt(B)
    R = sRT + 2 * math.sqrt(T) * sq + sq * sq
    Rt = sRT + 2 * L * sq + sq * sq
    lhs = (math.sqrt(T) + sq) ** 2
    return dict(V=V, delta=d, T=T, E=E, B=B, m_low=m_low, M=M, R=R, Rt=Rt, RT=RT,
                ratio=lhs / (2 * L * L * m_low),
                one_power=L - V - 4 * math.log(L) - math.log(2))   # > 0: <= one k-th power per interval


if __name__ == "__main__":
    p0 = pieces(L0)
    print(f"L0 = log(3.9e18) = {L0:.6f},  V = {p0['V']:.4f},  delta = {p0['delta']:.3e}")
    print(f"  M(L0)  = {p0['M']:.4f}")
    print(f"  Rt(L0) = {p0['Rt']:.4f}   [R_T pieces: " +
          ", ".join(f"{k} {v:.2e}" for k, v in p0['RT'].items()) +
          f";  E = {p0['E']:.3e}, B = {p0['B']:.1e}]")
    print(f"  T(L0) = {p0['T']:.2f} <= L0^2 = {L0**2:.2f};  m_low = {p0['m_low']:.5f};  "
          f"ratio (*) = {p0['ratio']:.5f};  one-power condition {p0['one_power']:.2f} > 0")
    assert p0['M'] > p0['Rt'] and p0['T'] <= L0 ** 2 and p0['one_power'] > 0

    # monotonicity checks on a fine grid, L0 .. 1e8
    grid = np.unique(np.concatenate([np.linspace(L0, 1000, 40001), np.geomspace(1000, 1e8, 40001)]))
    P = [pieces(L) for L in grid]
    Ms = np.array([p['M'] for p in P])
    names = ["M"] + list(p0['RT'].keys()) + ["2L sqrtE", "E", "B"]
    series = {"M": Ms}
    for k in p0['RT']:
        series[k] = np.array([p['RT'][k] for p in P])
    clip = lambda v: v if v > 1e-280 else 0.0   # subnormal inputs to sqrt give rounding noise
    series["2L sqrtE"] = np.array([2 * L * (math.sqrt(clip(p['E'])) + math.sqrt(clip(p['B']))) for L, p in zip(grid, P)])
    series["E"] = np.array([p['E'] for p in P])
    series["B"] = np.array([p['B'] for p in P])
    ok = True
    for k, s in series.items():
        keep = s > 1e-280                      # below this, subnormal rounding noise; analytic argument in section 10
        dif = np.diff(s[keep])
        good = np.all(dif > 0) if k == "M" else np.all(dif <= 0)
        ok &= good
        print(f"  {k:10s} {'increasing' if k == 'M' else 'non-increasing'} on grid: {good}")
    TleL2 = all(p['T'] <= L * L for L, p in zip(grid, P))
    ok &= TleL2
    print(f"  T <= L^2 on grid: {TleL2};   one-power condition on grid: {all(p['one_power'] > 0 for p in P)}")
    worst = max(p['ratio'] for p in P)
    print(f"  direct check of (*) on the grid: max ratio = {worst:.7f}")
    print("Samples (L, M, Rt, ratio):")
    for L in [L0, 50, 100, 1000, 1e4, 1e6, 1e8]:
        p = pieces(L)
        print(f"  {L:10.4g}  {p['M']:.6e}  {p['Rt']:.3e}  {p['ratio']:.7f}")
    print("RESULT:", "M(L0) > Rt(L0) and monotonicity hold -> (*) for all L >= L0" if ok else "FAILED")
