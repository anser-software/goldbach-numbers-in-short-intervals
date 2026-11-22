import Mathlib

/-!
# Definitions and hypotheses

This file fixes the objects of the paper *Goldbach numbers in intervals of length `2 log² x`
under the Riemann hypothesis* and states the hypotheses that the formalization takes as inputs.

* `IsGoldbachNumber n`: `n` is even and a sum of two primes.
* `kerProfile`, `W`: the kernel `W_V(v) = φ(|v|/V)` of §2 (equation (1)), with
  `φ(t) = (1 - t) cos(π t) + sin(π t)/π` on `[0, 1]` and `W_V = 0` outside `[-V, V]`.
* `weight x V y = (x/y)² W_V(log(x/y))`, the weight `ω` of §3.
* `Vθ δ y = θ((1+δ)y) - θ(y) - δ y`, with Mathlib's `Chebyshev.theta`.
* `Tb`, `Eb`, `Bb`: the explicit bounds of Table 1 for `𝒯/δ`, `ℰ` and `ℬ`, as functions of `L = log x`.

Hypotheses (not proved in Lean):

* `GoldbachVerifiedUpTo N`: every even `n` with `4 < n ≤ N` is a Goldbach number.
  This is the computation of Oliveira e Silva, Herzog and Pardi with `N = 4·10¹⁸`.
* `WeightedMeanSquareBound`: the weighted mean-square bound (the right-hand inequalities of (6)
  in §8, together with Proposition 13). It is used as a hypothesis only by the intermediate
  theorem `goldbach_short_intervals`. Most of its proof is now formalized: Lemmas 7 and 8 and the
  `ℰ` row of Proposition 13 are proved (`Lemma7`, `Lemma8`, `PrimePowers`), and the main
  theorem `goldbach_short_intervals_main` needs only the `𝒯` row (`Prop13T`); see the README.
-/

open Real

namespace GoldbachRH

/-- An even natural number that is the sum of two primes. -/
def IsGoldbachNumber (n : ℕ) : Prop :=
  Even n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Every even `n` with `4 < n ≤ N` is a Goldbach number. -/
def GoldbachVerifiedUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, Even n → 4 < n → n ≤ N → IsGoldbachNumber n

/-- The kernel profile `φ(t) = (1 - t) cos(π t) + sin(π t)/π` (equation (1) of the paper). -/
noncomputable def kerProfile (t : ℝ) : ℝ := (1 - t) * cos (π * t) + sin (π * t) / π

/-- The kernel `W_V`: `W_V(v) = φ(|v|/V)` for `|v| ≤ V`, and `0` otherwise. -/
noncomputable def W (V v : ℝ) : ℝ := if |v| ≤ V then kerProfile (|v| / V) else 0

/-- The weight `ω(y) = (x/y)² W_V(log(x/y))`. -/
noncomputable def weight (x V y : ℝ) : ℝ := (x / y) ^ 2 * W V (log (x / y))

/-- `V_θ(y) = θ((1+δ)y) - θ(y) - δ y`. -/
noncomputable def Vθ (δ y : ℝ) : ℝ :=
  Chebyshev.theta ((1 + δ) * y) - Chebyshev.theta y - δ * y

/-! ### The parameters of §8 as functions of `L = log x` -/

/-- `V = 3 √L`. -/
noncomputable def Vp (L : ℝ) : ℝ := 3 * √L
/-- `δ = 2 L² / x = 2 L² e^{-L}`. -/
noncomputable def dl (L : ℝ) : ℝ := 2 * L ^ 2 * exp (-L)
/-- `σ = π / V`. -/
noncomputable def sg (L : ℝ) : ℝ := π / Vp L
/-- `ℓ_y = L - V`. -/
noncomputable def uL (L : ℝ) : ℝ := L - Vp L
/-- `a₁ = 1 - γ - log 2`. -/
noncomputable def a1 : ℝ := 1 - eulerMascheroniConstant - log 2

/-- `T_main = (Λ₁⁰ + a₁)² + (a₂ - a₁²)`, where `Λ₁⁰ = L - 2 log L - log 2π` and `a₂ - a₁² = 1 + π²/12`. -/
noncomputable def Tmain (L : ℝ) : ℝ := (L - 2 * log L - log (2 * π) + a1) ^ 2 + (1 + π ^ 2 / 12)

/-- `T_pr = 2V²/π² + 0.08`. -/
noncomputable def Tpr (L : ℝ) : ℝ := 2 * Vp L ^ 2 / π ^ 2 + 0.08

/-- The five `R_T` rows of Table 1. -/
noncomputable def RT (L : ℝ) : ℝ :=
  dl L * (L ^ 2 + 3 * L)
  + (dl L * (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250) + 0.1 * dl L)
  + 0.06 * dl L * (1 + dl L) * (1 / 4 + sg L ^ 2)
  + 2.02 * dl L * (exp (Vp L) + exp (Vp L / 2) * Vp L ^ 2 / (8 * π)
      + 2.4 * (Vp L ^ 2 / 2 + 0.04) / log 2)
  + 0.5 * dl L * (1 + dl L) * (sg L ^ 2 + sg L + 1 / 4) * exp (Vp L / 2)

/-- Table 1 bound for `𝒯/δ`. -/
noncomputable def Tb (L : ℝ) : ℝ := Tmain L + Tpr L + RT L

/-- Table 1 bound for `ℰ` (prime powers). -/
noncomputable def Eb (L : ℝ) : ℝ :=
  (L + Vp L + 1) / log 2 * (1 + dl L) * log 4 *
    ((uL L + 2) * exp (-uL L / 2)
      + uL L / log 2 * (uL L / 2 + 0.75) * exp (-(2 * uL L) / 3)
      + 3 * exp (-uL L))

/-- Table 1 bound for `ℬ`. -/
noncomputable def Bb (L : ℝ) : ℝ := 0.8 * dl L * exp (-5 * uL L)

/-- **Hypothesis (analytic core).** For `x ≥ 3.9·10¹⁸`, with `L = log x`, `V = 3√L` and
`δ = 2L²/x`, the weighted mean square of `V_θ` is at most `δ x² (√𝒯 + √ℰ + √ℬ)²` with the
bounds of Table 1. This is the right-hand part of inequality (6) combined with Proposition 13.
Those inequalities do not use the assumption that there is no Goldbach number.
In the paper they are derived from RH (Lemma 4 (ii), (iii), (v) and Lemmas 7–12). -/
def WeightedMeanSquareBound : Prop :=
  ∀ x : ℝ, 3.9e18 ≤ x →
    ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Vθ (2 * log x ^ 2 / x) y ^ 2 * weight x (Vp (log x)) y)
      ≤ ENNReal.ofReal (2 * log x ^ 2 / x * x ^ 2 *
          (√(Tb (log x)) + √(Eb (log x)) + √(Bb (log x))) ^ 2)

end GoldbachRH
