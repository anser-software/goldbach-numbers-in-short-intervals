# Goldbach numbers in intervals of length 2 log² x under RH

[![DOI](https://zenodo.org/badge/1467471122.svg)](https://doi.org/10.5281/zenodo.24441477)

**Claim (conditional on the Riemann hypothesis).** For every real x ≥ 4, the interval
(x, x + 2 log² x] contains an even number that is a sum of two primes. The previous best
constant was 123 (Chirre–Hagen, Res. Number Theory 2026).

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
  (`selberg_numeric.py` computes the value of J(10⁸, 339) quoted in §9).
- `lean/`: a **conditional** Lean 4 / Mathlib formalization (build with `cd lean && lake build`).

## What the Lean formalization proves
The main result is `GoldbachRH.goldbach_short_intervals_main` in `lean/GoldbachRH/Main.lean`:

    RiemannHypothesis → ExplicitFormulaPsi → GoldbachVerifiedUpTo (4·10^18) →
      Prop13T →
      ∀ x ≥ 4, ∃ n, IsGoldbachNumber n ∧ x < n ∧ n ≤ x + 2 log² x

It uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and contains
no `sorry`. `RiemannHypothesis` and `riemannZeta` are Mathlib's definitions.

**Machine-checked:**
- the kernel facts that the cover argument uses (Lemma 4 (i) and (iv): W ≥ 0, monotonicity and (K1));
- Lemma 4 (ii): Ŵ ≥ 0, (2π)⁻¹∫Ŵ = 1 and (2π)⁻¹∫ξ²Ŵ = σ², via explicit closed forms and
  Mathlib's Fourier inversion theorem; and Lemma 4 (v), (K2);
- the weighted cover argument (Lemma 6 with Corollary 5), including the closed-form integral and the constant 9.55;
- Lemma 7 (the Schur bound ‖A‖²_ω ≤ x²𝒯), from the explicit formula, Fatou's lemma, a change
  of variables and Lemma 4 (ii);
- Lemma 8 (the term B);
- the ℰ row of Proposition 13 (prime powers), via Abel summation (Mathlib), Cauchy–Schwarz
  over exponents, and Bernoulli's inequality for the spacing of k-th powers. Its arithmetic input,
  Lemma 12 (L3), is Chebyshev's θ(t) ≤ t log 4, which Mathlib proves;
- the identity V_θ = A + B − P and the triangle-inequality step in (6);
- the complete range argument for all log x ≥ 42.8. This follows a cruder but derivative-free
  route that is independent of the paper's;
- the range below 3.9·10¹⁸, from the verification hypothesis.

**Cited results, taken as hypotheses** (`lean/GoldbachRH/Zeros.lean`, `Defs.lean`):
- `RiemannHypothesis`;
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
