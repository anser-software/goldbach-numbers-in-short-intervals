"""Numerical value of J(N, K) quoted in Section 9 of the paper (not used in the proof).

    J(N, K) = int_1^N (theta(u + K) - theta(u) - K)^2 du,   N = 10^8,  K = 339 = round(log^2 N).

For integer K, theta(u + K) - theta(u) is constant on each [n, n + 1), so
    J(N, K) = sum_{n=1}^{N-1} (theta(n + K) - theta(n) - K)^2
exactly. The sum is evaluated in floating point (float64), in blocks.

    .venv/bin/python scripts/selberg_numeric.py        (about 15 s, ~1 GB of memory)
"""
import math
import numpy as np

N = 10 ** 8
K = round(math.log(N) ** 2)
M = N + K

sieve = np.ones(M + 1, dtype=bool)
sieve[:2] = False
for i in range(2, math.isqrt(M) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
logp = np.where(sieve, np.log(np.arange(M + 1, dtype=np.float64), where=sieve, out=np.zeros(M + 1)), 0.0)
del sieve

# theta(n) for n = 0..M as a cumulative sum (float64; theta(M) ~ 1e8)
theta = np.cumsum(logp)
del logp

n = np.arange(1, N, dtype=np.int64)
J = 0.0
B = 10 ** 7
for a in range(0, len(n), B):
    nn = n[a:a + B]
    d = theta[nn + K] - theta[nn] - K
    J += float(np.dot(d, d))

LN = math.log(N)
print(f"N = {N:.0e}, K = {K}")
print(f"J(N, K)                  = {J:.4e}")
print(f"J / (K N log(N/K))       = {J / (K * N * math.log(N / K)):.4f}")
print(f"J / (K N log^2 N)        = {J / (K * N * LN ** 2):.4f}")
