"""Numerical values quoted in Section 9 of the paper (not used in the proof).

    J(N, K) = int_1^N (theta(u + K) - theta(u) - K)^2 du,
    Z(N; h) = sum_{p, p' <= N, p' - p = h} log p log p'          (Goldston's eq. (11)),
    A(N, K) = sum_{0 < h < K} (K - h) Z(N; h) / (K^2 N / 2)     (averaged prime-pair constant),

for N = 10^8 and K = c log^2 N, c = 1/4, 1/2, 1 (K = 339 for c = 1).

For integer K, theta(u + K) - theta(u) is constant on each [n, n + 1), so
    J(N, K) = sum_{n=1}^{N-1} (theta(n + K) - theta(n) - K)^2
exactly. Z(N; h) is a dot product of the log p indicator with its shift by h. Everything is
evaluated in floating point (float64). As a consistency check, the script prints the difference
between the right side of Goldston's identity (25) without its o(K^2 N) term,
    K N log N + 2 sum_{h<K} (K - h) Z(N; h) - K^2 N,
and J, divided by K^2 N; it should be small.

    .venv/bin/python scripts/selberg_numeric.py        (about 30 s, ~2 GB of memory)
"""
import math
import numpy as np

N = 10 ** 8
LN = math.log(N)
KS = [(c, round(c * LN ** 2)) for c in (0.25, 0.5, 1.0)]
KMAX = max(K for _, K in KS)
M = N + KMAX

sieve = np.ones(M + 1, dtype=bool)
sieve[:2] = False
for i in range(2, math.isqrt(M) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
logp = np.zeros(M + 1)
np.log(np.arange(M + 1, dtype=np.float64), where=sieve, out=logp)
del sieve

# Z(N; h) for 0 < h < KMAX, with p, p' <= N
lp = logp[:N + 1]
Z = np.zeros(KMAX)
for h in range(1, KMAX):
    Z[h] = float(np.dot(lp[:N + 1 - h], lp[h:N + 1]))

# theta(n) for n = 0..M as a cumulative sum, in place
theta = np.cumsum(logp, out=logp)

n = np.arange(1, N, dtype=np.int64)
print(f"N = {N:.0e}")
print(f"{'c':>5} {'K':>5} {'A(N,K)':>9} {'J/(KN log^2 N)':>15} {'J/(KN log(N/K))':>16} {'((25) - J)/(K^2 N)':>20}")
for c, K in KS:
    J = 0.0
    B = 10 ** 7
    for a in range(0, len(n), B):
        nn = n[a:a + B]
        d = theta[nn + K] - theta[nn] - K
        J += float(np.dot(d, d))
    S = float(sum((K - h) * Z[h] for h in range(1, K)))
    A = S / (K * K * N / 2)
    rhs25 = K * N * LN + 2 * S - K * K * N
    print(f"{c:5.2f} {K:5d} {A:9.4f} {J / (K * N * LN ** 2):15.4f} {J / (K * N * math.log(N / K)):16.4f}"
          f" {(rhs25 - J) / (K * K * N):20.4f}")
