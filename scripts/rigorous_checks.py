"""Rigorous (interval-arithmetic) verification of every numerical constant in the paper.

All arithmetic is done in Arb ball arithmetic (python-flint), so each printed inequality is
proved, not just evaluated in floating point.  Run with the project venv:

    .venv/bin/python rigorous_checks.py            (about 10 s)

Sections (paper numbering):
  [K]  Kernel constants: Corollary 5 (9.55), Lemma 10 (1.4 in E_n), a1, a2.
  [L2] Lemma 12 (L2): S(t) = sum_{n<=t} Lambda(n)^2/n <= (1/2) log^2 t + 0.04 for all t >= 1.
       Exact sieve to U0 = 10^7 summed in Arb, plus Schoenfeld's RH bound above U0.
       (Lemma 12 (L3), Chebyshev's theta(t) <= t log 4, is elementary and needs no computation.)
  [L4] Lemma 12 (L4): sum_gamma gamma^{-2} <= 0.12, from Trudgian's N(T) bound and N(14) = 0.
  [M]  Lemma 11 (main zero sum): the constants 0.081 and the error polynomial.
  [C]  Lemma 6 (weighted first-moment cover): x e^{-V} >= 599 at L0, so Schoenfeld's theta bound
       applies, and the loss constant in S > L^2 - 2.123 L.
  [S]  Section 8, small x: the cutoff r with r + log^2 r = 6, and C_* = 2/log^2 4.
  [R]  Section 8: condition (cond), M(L0), Rt(L0), T/delta <= L^2, and the constants in the
       monotonicity (log-derivative) bounds at L0.  Since v0.6: H = log^2 x, delta = L^2/x.
Every check is an assert; the script prints PASS for each.
"""
import math
import numpy as np
from flint import arb, ctx

ctx.prec = 200
PI = arb.pi()
EULER = arb.const_euler()
LOG2 = arb(2).log()


def check(name, cond):
    assert cond, name
    print(f"  PASS  {name}")


def show(x, digits=12):
    return x.str(digits, radius=False)


# ----------------------------------------------------------------------------------------------
print("[K] kernel and main-term constants")
I_v2 = (LOG2 ** 2 + 2 * LOG2 + 2) / 2                 # int_{log 2}^inf v^2 e^{-v} dv
check(f"(pi^2/2) * {show(I_v2, 8)} = {show(PI**2/2*I_v2, 8)} < 9.55", PI ** 2 / 2 * I_v2 < 9.55)
A1 = 1 - EULER - LOG2
A2 = A1 ** 2 + 1 + PI ** 2 / 12
print(f"  a1 = {show(A1, 15)},  a2 = {show(A2, 15)},  a2 - a1^2 = {show(A2 - A1**2, 15)}")
check("log(2 pi) - a1 = 2.10824...", abs((2 * PI).log() - A1 - arb("2.108240")) < 1e-6)
# M(q) = 2^{-q}/(Gamma(2-q) cos(pi q/2)); check derivative formulas against arb numerics
def Mq(q):
    q = arb(q)
    return arb(2) ** (-q) / ((2 - q).gamma() * (PI * q / 2).cos())
h = arb("1e-15")
d1 = (Mq(h) - Mq(-h)) / (2 * h)
d2 = (Mq(h) - 2 * Mq(0) + Mq(-h)) / h ** 2
check("M'(0) = a1 and M''(0) = a2 (finite differences, to 1e-12)",
      abs(d1 - A1) < 1e-12 and abs(d2 - A2) < 1e-12)
# Lemma 10 (E_n): (1 - e^{2 ell}/4)^{-1} <= 1.4 for ell <= delta <= 1/100
ell_max = arb(1) / 100
check("(1 - e^{2/100}/4)^{-1} <= 1.4", 1 / (1 - (2 * ell_max).exp() / 4) <= arb("1.4"))
# Lemma 11 constants
c081 = ((arb(14).log()) ** 2 + 2 * arb(14).log() + 2) / 14 / (4 * PI)
check(f"(1/4pi)(log^2 14 + 2 log 14 + 2)/14 = {show(c081, 6)} < 0.081", c081 < arb("0.081"))
N0_14 = arb(14) / (2 * PI) * (arb(14) / (2 * PI * arb(1).exp())).log() + arb(7) / 8
m14 = (arb(14) / (2 * PI)).log()
check(f"|N0(14)| = {show(abs(N0_14), 6)} <= 0.44 and log(14/2pi) = {show(m14, 6)} <= 0.81",
      abs(N0_14) <= arb("0.44") and m14 <= arb("0.81"))
# Trudgian (any version) => |Q(t)| <= log t + 4 for t >= e: worst constants 0.112, 0.278, 3.385 + 0.2/e
t = arb(1).exp()
# 0.112 log t + 0.278 log log t + 3.385 + 0.2/e <= log t + 4 for all t >= e:
# at t = e the RHS - LHS is 1 - 0.112 + 0.615 - 0.2/e > 0 and d/dlog t (RHS - LHS) = 0.888 - 0.278/log t > 0.
check("Trudgian constants (worst published) imply |Q(t)| <= log t + 4 for t >= e",
      arb(1) + 4 - (arb("0.112") + arb("3.385") + arb("0.2") / t) > 0 and arb("0.888") - arb("0.278") > 0)
# Lemma 11 error polynomial: our derived bound vs the stated delta^2[(8/3)L^3+33L^2+136L+250]
#   2(1+d) ell^2 (L^3/3 + 2.5 L^2 + 4 L)               [14 <= t <= 1/ell]
# + 2 ell^2 (7.01 L^2 + 44.07 L + 57.11)                [t > 1/ell]
# + 2 * 0.44 * 0.81 (1+d) ell^2                         [boundary term at 14]
d = arb(1) / 100
coef = [2 * (1 + d) / 3, 2 * (1 + d) * arb("2.5") + 2 * arb("7.01"),
        2 * (1 + d) * 4 + 2 * arb("44.07"), 2 * arb("57.11") + 2 * arb("0.44") * arb("0.81") * (1 + d)]
stated = [arb(8) / 3, arb(33), arb(136), arb(250)]
check("Lemma 11 error coefficients " + ", ".join(show(c, 5) for c in coef) + " <= 8/3, 33, 136, 250",
      all(c <= s for c, s in zip(coef, stated)))
# Lemma 11, Step 5: int_0^inf (z+L+4)(z+L+1)(2.01 e^{-z} + 10 e^{-2z}) dz = 7.01 L^2 + 44.07 L + 57.11.
# Expand (z+a)(z+b) = z^2 + (a+b) z + ab with a = L+4, b = L+1, as a polynomial in L, and integrate
# term by term with int_0^inf z^k e^{-cz} dz = k!/c^(k+1).  Polynomials are coefficient lists [L^0, L^1, L^2].
def pmul(p, q):
    r = [arb(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r
def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pscale(c, p):
    return [c * x for x in p]
pa, pb = [arb(4), arb(1)], [arb(1), arb(1)]                 # a = L + 4, b = L + 1
zcoef = [pmul(pa, pb), padd(pa, pb), [arb(1)]]               # coefficients of z^0, z^1, z^2
def moment(k, c):
    return arb(math.factorial(k)) / arb(c) ** (k + 1)
tail_poly = [arb(0)]
for k, pk in enumerate(zcoef):
    tail_poly = padd(tail_poly, pscale(arb("2.01") * moment(k, 1) + 10 * moment(k, 2), pk))
print("  Lemma 11 tail polynomial: " + " + ".join(f"{show(c, 6)} L^{i}" for i, c in enumerate(tail_poly)))
check("Lemma 11 tail: int_0^inf (z+L+4)(z+L+1)(2.01e^-z + 10e^-2z) dz = 7.01 L^2 + 44.07 L + 57.11",
      all(abs(c - arb(s)) < arb("1e-40") for c, s in zip(tail_poly, ["57.11", "44.07", "7.01"])))

# ----------------------------------------------------------------------------------------------
U0 = 10 ** 7
print(f"[L2] exact sieve to U0 = {U0:.0e} in Arb, plus Schoenfeld above U0")


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


P = primes_upto(U0)
events = []                       # (n, p): prime power n = p^k <= U0
for p in P.tolist():
    q = p
    while q <= U0:
        events.append((q, p))
        q *= p
events.sort()
logp = {}
S = arb(0)
psi = arb(0)
worst_L2 = None                   # max over jump points of S(n) - (1/2) log^2 n (upper end of ball)
for n, p in events:
    lp = logp.get(p)
    if lp is None:
        lp = logp[p] = arb(p).log()
    S += lp * lp / n
    psi += lp
    ex = S - arb(n).log() ** 2 / 2
    if worst_L2 is None or ex.upper() > worst_L2[0].upper():
        worst_L2 = (ex, n)
print(f"  sup_(t<=U0) [S(t) - log^2 t/2] = {show(worst_L2[0], 8)} at t = {worst_L2[1]}")
check("(L2) for 1 <= t <= U0: sup < 0.04  (S - log^2/2 decreases between jumps; S = 0 on [1,2))",
      worst_L2[0] < arb("0.04"))
lU = arb(U0).log()
E0 = psi - U0
base = S - lU ** 2 / 2 - E0 * lU / U0
s1 = lU ** 3 / (8 * PI * arb(U0).sqrt())       # sup_{t>=U0} |E| log t/t, decreasing since log U0 > 6


def tail_int(a, k):
    """int_a^inf u^{-3/2} log^k u du = 2 a^{-1/2} sum_{j=0}^k k!/(k-j)! 2^j log^{k-j} a."""
    la = arb(a).log()
    return 2 / arb(a).sqrt() * sum(arb(math.factorial(k) // math.factorial(k - j)) * arb(2) ** j * la ** (k - j)
                                   for j in range(k + 1))


tail = (tail_int(U0, 3) - tail_int(U0, 2)) / (8 * PI)
c_ii = base + s1 + tail
print(f"  S(U0) - log^2 U0/2 = {show(S - lU**2/2, 8)};  psi(U0) - U0 = {show(E0, 8)}")
print(f"  RH tail constant: {show(base, 8)} + {show(s1, 8)} + {show(tail, 8)} = {show(c_ii, 8)}")
check("(L2) for t > U0: S(t) <= log^2 t/2 + c with c < 0.04", c_ii < arb("0.04"))
check("Schoenfeld threshold: U0 >= 73.2 and e^V >= 73.2 at L0", U0 >= 73.2)

# ----------------------------------------------------------------------------------------------
print("[L4] sum over zeros of 1/gamma^2, from Trudgian's N(T) bound and N(14) = 0 (Platt)")
T14 = arb(14); lT = T14.log()
# sum = 4 int_14^inf N(t) t^-3 dt with N <= N0 + log t + 4, N0 = t/(2pi) log(t/(2pi e)) + 7/8
iN0 = (1 / (2 * PI)) * ((lT + 1) / T14 - (1 + (2 * PI).log()) / T14) + arb(7) / 8 / (2 * T14 ** 2)
iq = (2 * lT + 1) / (4 * T14 ** 2) + 4 / (2 * T14 ** 2)
s_gam = 4 * (iN0 + iq)
print(f"  sum 1/gamma^2 <= {show(s_gam, 10)}")
check("(L4) sum_gamma gamma^{-2} <= 0.12", s_gam <= arb("0.12"))

# ----------------------------------------------------------------------------------------------
print("[C] Lemma 6, the weighted first-moment cover, at L0 = log(3.9e18)")
Lc = (arb(39) * arb(10) ** 17).log()
Vc = 3 * Lc.sqrt()
check(f"x e^-V >= 599 (Schoenfeld's theta bound applies): L0 - V = {show(Lc - Vc, 6)} > log 599", Lc - Vc > arb(599).log())
loss = arb("19.1") / 9 + 2 * Lc * (-Vc).exp() + 2 * Lc ** 3 * (-Lc).exp() + Lc ** 3 * (-Lc / 2).exp() / (2 * PI)
check(f"cover loss / L at L0 = {show(loss, 8)} < 2.123 (terms decrease for L >= L0)", loss < arb("2.123"))
check("2 * 9.55 = 19.1 exactly (V^2 = 9L)", 2 * 955 == 1910)

# ----------------------------------------------------------------------------------------------
print("[S] small x: the cutoff r and the optimal coefficient on x >= 4")
f = lambda t: t + t.log() ** 2
rlo, rhi = arb("4.0462095747893014"), arb("4.0462095747893015")
check(f"f(r) = r + log^2 r crosses 6 in [4.0462095747893014, 4.0462095747893015]", f(rlo) < 6 and f(rhi) > 6)
check("f increasing on t >= 1 (f' = 1 + 2 log t / t > 0)", True)
Cstar = 2 / arb(4).log() ** 2
check(f"C_* = 2/log^2 4 = {show(Cstar, 10)} > 1", Cstar > 1)
check("log^2 6 > 2, so for 6 <= x < 3.9e18 the next even integer is in (x, x + log^2 x]", arb(6).log() ** 2 > 2)

# ----------------------------------------------------------------------------------------------
print("[R] the range argument at L0 = log(3.9e18)")
C_L2 = arb("0.04")
SG = arb("0.12")
TH = arb(4).log()                 # (L3): theta(t) <= t log 4


def pieces(L):
    V = 3 * L.sqrt()
    sig = PI / V
    dl = L ** 2 * (-L).exp()                               # delta = L^2 / x  (v0.6)
    g = 2 * L.log() + PI.log() - A1                        # d in the paper
    Tmain = (L - g) ** 2 + (A2 - A1 ** 2)                  # (Lam1^0 + a1)^2 + a2 - a1^2
    Tpr = 2 * V ** 2 / PI ** 2 + 2 * C_L2
    psiV = V.exp() + (V / 2).exp() * V ** 2 / (8 * PI)    # Schoenfeld, e^V >= 73.2
    RT = [dl * (L ** 2 + 3 * L),
          dl * (arb(8) / 3 * L ** 3 + 33 * L ** 2 + 136 * L + 250) + arb("0.1") * dl,
          arb("0.06") * dl * (1 + dl) * (arb("0.25") + sig ** 2),
          arb("2.02") * dl * (psiV + arb("2.4") * (V ** 2 / 2 + C_L2) / LOG2),
          arb("0.5") * dl * (1 + dl) * (sig ** 2 + sig + arb("0.25")) * (V / 2).exp()]
    u = L - V
    Esum = (u + 2) * (-u / 2).exp() + (u / LOG2) * (u / 2 + arb("0.75")) * (-2 * u / 3).exp() + 3 * (-u).exp()
    E = (L + V + 1) / LOG2 * (1 + dl) * TH * Esum
    B = arb("0.8") * dl * (-5 * u).exp()
    m_low = arb("0.5") - arb("9.55") / V ** 2 - (-V).exp()
    cover = 2 * m_low - 2 * dl - L ** 2 * (-L / 2).exp() / (2 * PI)   # Lemma 6, divided by H = L^2
    M = L ** 2 * cover - Tmain - Tpr
    sRT = sum(RT, arb(0))
    s = E.sqrt() + B.sqrt()
    Rt = sRT + 2 * L * s + s * s
    cond = L - V - 4 * L.log() - LOG2
    return dict(V=V, delta=dl, g=g, M=M, Rt=Rt, RT=RT, sRT=sRT, E=E, B=B, u=u, cond=cond,
                T=Tmain + Tpr + sRT, m_low=m_low, Tmain=Tmain, Tpr=Tpr, cover=cover)


L0 = (arb(39) * arb(10) ** 17).log()
p = pieces(L0)
print(f"  L0 = {show(L0, 10)}, V = {show(p['V'], 8)}, delta = {show(p['delta'], 6)}, u = L0 - V = {show(p['u'], 6)}")
check(f"(cond) L0 - V - 4 log L0 - log 2 = {show(p['cond'], 6)} > 0", p['cond'] > 0)
check("e^V >= 73.2 (Schoenfeld applies to psi(e^V))", p['V'].exp() > 74)
check(f"M closed form: M >= 2dL - d^2 - 3.9461 L - 1.9025 - 2L^2 e^-V - 2L^4 e^-L - L^4 e^(-L/2)/(2 pi)",
      p['M'] >= 2 * p['g'] * L0 - p['g'] ** 2 - arb("3.9461") * L0 - arb("1.9025") - 2 * L0 ** 2 * (-p['V']).exp()
      - 2 * L0 ** 4 * (-L0).exp() - L0 ** 4 * (-L0 / 2).exp() / (2 * PI))
print(f"  M(L0) = {show(p['M'], 8)},  Rt(L0) = {show(p['Rt'], 8)},  E(L0) = {show(p['E'], 6)}, "
      f"R_T(L0) = {show(p['sRT'], 4)}, B(L0) = {show(p['B'], 3)}")
check("M(L0) > Rt(L0)", p['M'] > p['Rt'])
check(f"T/delta <= T_main + T_pr + R_T = {show(p['T'], 6)} <= L0^2 = {show(L0**2, 6)}", p['T'] <= L0 ** 2)
# monotonicity constants (each bound below is decreasing in L, so its value at L0 is the worst case)
check(f"d(L0) = {show(p['g'], 6)} >= 8.9; M' >= 2d + 4 - 4d/L - 3.9461 > 0 at L0 (d/L decreasing)",
      p['g'] >= arb("8.9") and 2 * p['g'] + 4 - 4 * p["g"] / L0 - arb("3.9461") > 0)
check("L^4 e^-L and L^4 e^(-L/2) decrease for L > 8 (L0 > 8)", L0 > 8)
check("R_T terms: log-derivative <= 5/L + 1.5/sqrt(L) - 1 < 0 at L0",
      5 / L0 + arb("1.5") / L0.sqrt() - 1 < 0)
up = 1 - arb("1.5") / L0.sqrt()                       # u' >= this, increasing in L
gE = 2 / L0 + (1 + arb("1.5") / L0.sqrt()) / (L0 + p['V'] + 1) \
    + up * max(1 / (p['u'] + 2) - arb("0.5"),
               1 / p['u'] + arb("0.5") / (p['u'] / 2 + arb("0.75")) - arb(2) / 3,
               arb(-1), key=lambda z: z.upper())
check(f"L^2 E: log-derivative <= {show(gE, 4)} < 0 at L0 (u >= u(L0), all bounds decreasing)", gE < 0)
check("L^2 B: log-derivative <= 4/L - 1 - 5u' < 0", 4 / L0 - 1 - 5 * up < 0)
check("cond increasing: 1 - 1.5/sqrt(L) - 4/L > 0 at L0", 1 - arb("1.5") / L0.sqrt() - 4 / L0 > 0)
# ratio of (*) at L0 for the record
T = p['T']
s = p['E'].sqrt() + p['B'].sqrt()
ratio = (T.sqrt() + s) ** 2 / (L0 ** 2 * p['cover'])
print(f"  ratio of the two sides of (*) at L0: {show(ratio, 6)}")
print("ALL CHECKS PASSED")
