# Goldbach numbers in intervals of length log² x under RH

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24441477.svg)](https://doi.org/10.5281/zenodo.24441477)

**Claim (conditional on the Riemann hypothesis).** For every real x ≥ r = 4.0462…, where
r + log² r = 6, the interval (x, x + log² x] contains an even number that is a sum of two
primes. The starting point is sharp: for 4 ≤ x < r the interval contains none. On the whole
range x ≥ 4 the optimal constant is C\* = 2/log² 4 = 1.0406…. The best published constant was 123
(Chirre–Hagen, Res. Number Theory 2026). Hubbard has since announced 4.45 in an unrefereed
preprint (Hexagon 2610.00542), and version 0.5 of this work gave 2. He Li independently found the
first-moment refinement of the cover lemma that gives the constant 1, and posted it as
[issue #1](https://github.com/anser-software/goldbach-numbers-in-short-intervals/issues/1)
before v0.6 appeared.

> **Status: unreviewed preprint.** The work was done largely with an AI model (Claude, Anthropic).
> RH is assumed throughout; an announced formal proof of GRH has not been independently confirmed.

## Author
Anton Vynohradov. Licence: MIT for code, CC BY 4.0 for the paper (see `LICENSE`).

## Contents
- `paper/`: the paper (LaTeX and PDF).
- `scripts/rigorous_checks.py`: every numerical constant in the proof, checked in Arb ball
  arithmetic. Setup: `python3 -m venv .venv && .venv/bin/pip install -r requirements.txt`,
  then run `.venv/bin/python scripts/rigorous_checks.py`.
  The other scripts are floating-point cross-checks and are not used in the proof
  (`selberg_numeric.py` computes the values of J(10⁸, K) and A(10⁸, K) quoted in §9).
- `lean/`: a **conditional** Lean 4 / Mathlib formalization (build with `cd lean && lake build`).

## What the Lean formalization proves
The main result is `GoldbachRH.goldbach_log_sq_main` in `lean/GoldbachRH/Main.lean`:

    RiemannHypothesis → (RiemannHypothesis → SchoenfeldTheta) → ExplicitFormulaPsi →
      GoldbachVerifiedUpTo (4·10^18) → Prop13T →
      ∀ x ≥ 4, 6 ≤ x + log² x → ∃ n, IsGoldbachNumber n ∧ x < n ∧ n ≤ x + log² x

With the same hypotheses, `goldbach_Cstar_main` gives n ≤ x + (2/log² 4) log² x for every
x ≥ 4, and `goldbach_two_log_sq_main` recovers the v0.5 statement. Two companion theorems are
unconditional. `no_goldbach_below_cutoff` shows that (x, x + log² x] contains no Goldbach
number when 4 ≤ x and x + log² x < 6. `Cstar_optimal` shows that no constant below 2/log² 4
works at x = 4.

These theorems use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
and contain no `sorry`. `RiemannHypothesis` and `riemannZeta` are Mathlib's definitions.

**Machine-checked:**
- the kernel facts that the cover argument uses (Lemma 4 (i) and (iv): W ≥ 0, monotonicity and (K1));
- Lemma 4 (ii): Ŵ ≥ 0, (2π)⁻¹∫Ŵ = 1 and (2π)⁻¹∫ξ²Ŵ = σ², via explicit closed forms and
  Mathlib's Fourier inversion theorem; and Lemma 4 (v), (K2);
- the first-moment cover (Lemma 6 with Corollary 5; `cover_lower_bound_fm` in `CoverFM*.lean`):
  the symmetric weight q(y) = min(w(y), w(x − y)), the structure of its level sets, the first
  moment of θ on each level from Schoenfeld's bound, the layer-cake integration over levels, the
  pair inequality and the reflection y ↦ x − y, the closed-form integral and the constant 9.55;
- Lemma 7 (the Schur bound ‖A‖²_ω ≤ x²𝒯), from the explicit formula, Fatou's lemma, a change
  of variables and Lemma 4 (ii);
- Lemma 8 (the term B);
- the ℰ row of Proposition 13 (prime powers), via Abel summation (Mathlib), Cauchy–Schwarz
  over exponents, and Bernoulli's inequality for the spacing of k-th powers. Its arithmetic input,
  Lemma 12 (L3), is Chebyshev's θ(t) ≤ t log 4, which Mathlib proves;
- the identity V_θ = A + B − P and the triangle-inequality step in (6);
- the complete range argument for all log x ≥ 42.8, with H = log² x. This follows a cruder but
  derivative-free route that is independent of the paper's;
- the range below 3.9·10¹⁸, from the verification hypothesis, and the cutoff r: the bound for
  x + log² x ≥ 6, its failure below, and the constant 2/log² 4 with its optimality at x = 4.

**Cited results, taken as hypotheses** (`lean/GoldbachRH/Zeros.lean`, `Defs.lean`):
- `RiemannHypothesis`;
- `SchoenfeldTheta`: Schoenfeld's bound |θ(t) − t| < √t log² t/(8π) for t ≥ 599 under RH
  (Math. Comp. 30 (1976), Thm. 10, (6.3)). Only the cover uses it;
- `ExplicitFormulaPsi`: the explicit formula for ψ, with zeros counted with multiplicity.
  The statement has been checked numerically against the first 20 000 zeros;
- `GoldbachVerifiedUpTo (4·10^18)`: the computation of Oliveira e Silva, Herzog and Pardi.

**The paper's own lemma not yet formalized** (stated in `lean/GoldbachRH/Assembly.lean`):
- `Prop13T`: the 𝒯 row of Proposition 13. Its proof uses Lemma 4 (ii), (iii), (v) (of which (ii) and (v)
  are now proved in Lean) and Lemmas 9–12,
  which in turn cite the Weil explicit formula, Chandee, Trudgian, Platt and Schoenfeld.

This row is the paper's main remaining analytic content. It is verified by hand and
numerically, but not formally. Sums over zeros are taken in `[0, ∞]`, so a divergent sum is
`∞` and cannot silently become `0`.
