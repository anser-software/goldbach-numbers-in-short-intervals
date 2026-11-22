import GoldbachRH.Defs

/-!
# Zeros of ζ, the functions `A`, `B`, `P` of §4, and the explicit formula for ψ

* `IsNontrivialZero`, `zeroMult`: nontrivial zeros of Mathlib's `riemannZeta`, counted with
  multiplicity (the order of vanishing, `analyticOrderAt`).
* `zerosUpTo T`: the finite set of nontrivial zeros with `|Im ρ| ≤ T`.
* `zsum f`: the sum of `f ρ` over nontrivial zeros, with multiplicity. It takes values in
  `ℝ≥0∞`, so a divergent sum is `∞` and never silently becomes `0`.
* `What V ξ`: the Fourier transform `Ŵ(ξ) = ∫ W(v) e^{-ivξ} dv` of the kernel. Since `W` is
  even and real, this is `∫ W(v) cos(ξv) dv`.
* `cco δ r`: `c(r) = ((1+δ)^{1/2+ir} - 1)/(1/2+ir)` of §4.
* `Rsum V γ = R(γ) = Σ_{γ'} Ŵ(γ - γ')` and `Tsum δ V = 𝒯 = Σ_γ |c(γ)|² R(γ)` (Lemma 7).
  Under RH the zeros are `ρ = 1/2 + iγ` with `γ = Im ρ`.
* `Vψ`, `Bfun`, `Pfun`, `Afun`: the functions `V_ψ`, `B`, `P`, `A` of §4. Here `P` is written
  as `(ψ - θ)((1+δ)y) - (ψ - θ)(y)`, which is the paper's sum of `log p` over prime powers
  `p^k ∈ (y, (1+δ)y]` with `k ≥ 2`, and `A` is defined as `V_ψ - B`. Then
  `V_θ = A + B - P` holds by definition (`Vθ_eq`). The explicit formula
  (`ExplicitFormulaPsi`) is what identifies `A` with the sum over zeros `-Σ_ρ c(γ) y^ρ`;
  it is used only in Lemma 7.
-/

open Real Filter Topology
open scoped ENNReal

namespace GoldbachRH

/-! ### Zeros -/

/-- `ρ` is a nontrivial zero of ζ: a zero in the critical strip `0 < Re ρ < 1`. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The multiplicity of `ρ` as a zero of ζ. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

lemma finite_zerosUpTo (T : ℝ) : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + T)).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨⟨h0, h1, h2⟩, hT⟩
  refine ⟨?_, mem_riemannZetaZeros.2 h0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + T := by rw [abs_of_pos h1]; linarith

/-- The nontrivial zeros with `|Im ρ| ≤ T` (a finite set). -/
noncomputable def zerosUpTo (T : ℝ) : Finset ℂ := (finite_zerosUpTo T).toFinset

/-- The sum of `f ρ` over the nontrivial zeros, counted with multiplicity. -/
noncomputable def zsum (f : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' ρ : {ρ : ℂ // IsNontrivialZero ρ}, (zeroMult ρ : ℝ≥0∞) * f ρ

/-! ### The zero sums of Lemma 7 -/

/-- The Fourier transform `Ŵ(ξ) = ∫ W(v) e^{-ivξ} dv = ∫ W(v) cos(ξ v) dv` (`W` is even). -/
noncomputable def What (V ξ : ℝ) : ℝ := ∫ v, W V v * cos (ξ * v)

/-- `c(r) = ((1+δ)^{1/2+ir} - 1)/(1/2+ir)`. -/
noncomputable def cco (δ r : ℝ) : ℂ :=
  (((1 + δ : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + r * Complex.I) - 1) / ((1 / 2 : ℂ) + r * Complex.I)

/-- `R(γ) = Σ_{γ'} Ŵ(γ - γ')`, with multiplicity. -/
noncomputable def Rsum (V γ : ℝ) : ℝ≥0∞ :=
  zsum fun ρ' => ENNReal.ofReal (What V (γ - ρ'.im))

/-- `𝒯 = Σ_γ |c(γ)|² R(γ)`, with multiplicity. -/
noncomputable def Tsum (δ V : ℝ) : ℝ≥0∞ :=
  zsum fun ρ => ENNReal.ofReal (Complex.normSq (cco δ ρ.im)) * Rsum V ρ.im

/-! ### The functions of §4 -/

/-- `V_ψ(y) = ψ((1+δ)y) - ψ(y) - δy`. -/
noncomputable def Vψ (δ y : ℝ) : ℝ := Chebyshev.psi ((1 + δ) * y) - Chebyshev.psi y - δ * y

/-- `B(y) = ½ log(1 - y⁻²) - ½ log(1 - (1+δ)⁻² y⁻²)`. -/
noncomputable def Bfun (δ y : ℝ) : ℝ :=
  log (1 - 1 / y ^ 2) / 2 - log (1 - 1 / ((1 + δ) ^ 2 * y ^ 2)) / 2

/-- `P(y)`: the contribution of prime powers `p^k`, `k ≥ 2`, in `(y, (1+δ)y]`. -/
noncomputable def Pfun (δ y : ℝ) : ℝ :=
  (Chebyshev.psi ((1 + δ) * y) - Chebyshev.theta ((1 + δ) * y))
    - (Chebyshev.psi y - Chebyshev.theta y)

/-- `A(y) = V_ψ(y) - B(y)`. By the explicit formula this is `-Σ_ρ c(γ) y^ρ`. -/
noncomputable def Afun (δ y : ℝ) : ℝ := Vψ δ y - Bfun δ y

lemma Vθ_eq (δ y : ℝ) : Vθ δ y = Afun δ y + Bfun δ y - Pfun δ y := by
  unfold Vθ Afun Vψ Pfun; ring

/-! ### Cited result -/

/-- **The explicit formula for ψ** (von Mangoldt; in the paper, [CH, eq. (3.2)]).
For non-integer `y > 1`,
`ψ(y) = y - lim_{T→∞} Σ_{|γ| ≤ T} y^ρ/ρ - log 2π - ½ log(1 - y⁻²)`,
the sum being over nontrivial zeros with multiplicity. This holds unconditionally. -/
def ExplicitFormulaPsi : Prop :=
  ∀ y : ℝ, 1 < y → (∀ n : ℕ, y ≠ n) →
    Tendsto (fun T : ℝ => ∑ ρ ∈ zerosUpTo T, (zeroMult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)) atTop
      (𝓝 (((y - Chebyshev.psi y - log (2 * π) - log (1 - 1 / y ^ 2) / 2 : ℝ)) : ℂ))

end GoldbachRH
