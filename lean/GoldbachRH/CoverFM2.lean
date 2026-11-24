import GoldbachRH.CoverFM

/-!
# The first-moment cover, part 2: one symmetric interval

Under Schoenfeld's bound, for `599 ≤ A ≤ x/2` and `0 < δ ≤ 1`,
`∫_A^{x-A} G ≥ (x - 2A) - δx - 2ε`, with `ε = √x log² x / (8π)`.
-/

open Real Set MeasureTheory

namespace GoldbachRH

lemma theta_err_le {x t : ℝ} (hSch : SchoenfeldTheta) (h1 : 599 ≤ t) (h2 : t ≤ x) :
    |Chebyshev.theta t - t| ≤ √x * log x ^ 2 / (8 * π) := by
  refine (hSch t h1).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ht : 0 < t := by linarith
  apply mul_le_mul (sqrt_le_sqrt h2) _ (sq_nonneg _) (sqrt_nonneg _)
  exact pow_le_pow_left₀ (log_nonneg (by linarith)) (log_le_log ht h2) 2

lemma intervalIntegrable_const_div {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => c / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div continuousOn_id
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact (ha.trans_le ht.1).ne'

lemma integral_const_div_eq {c a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∫ t in a..(1 + δ) * a, c / t = c * log (1 + δ) := by
  have h : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    ext t
    rw [div_eq_mul_inv]
  rw [h, intervalIntegral.integral_const_mul, integral_inv_of_pos ha (by positivity),
    mul_div_cancel_right₀ _ ha.ne']

/-- Lower bound for `∫_b^{(1+δ)b} θ(t)/t dt`. -/
lemma integral_theta_div_ge {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) :
    Chebyshev.theta b * log (1 + δ) ≤ ∫ t in b..(1 + δ) * b, Chebyshev.theta t / t := by
  have hbb : b ≤ (1 + δ) * b := by nlinarith
  rw [← integral_const_div_eq hb hδ]
  apply intervalIntegral.integral_mono_on hbb (intervalIntegrable_const_div hb hbb)
    (intervalIntegrable_theta_div hb hbb)
  intro t ht
  exact div_le_div_of_nonneg_right (Chebyshev.theta_mono ht.1) (hb.trans_le ht.1).le

/-- Upper bound for `∫_a^{(1+δ)a} θ(t)/t dt`. -/
lemma integral_theta_div_le {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∫ t in a..(1 + δ) * a, Chebyshev.theta t / t ≤ Chebyshev.theta ((1 + δ) * a) * log (1 + δ) := by
  have haa : a ≤ (1 + δ) * a := by nlinarith
  rw [← integral_const_div_eq ha hδ]
  apply intervalIntegral.integral_mono_on haa (intervalIntegrable_theta_div ha haa)
    (intervalIntegrable_const_div ha haa)
  intro t ht
  exact div_le_div_of_nonneg_right (Chebyshev.theta_mono ht.2) (ha.trans_le ht.1).le

/-- **First moment on one symmetric interval.** -/
lemma integral_G_ge {x δ A : ℝ} (hSch : SchoenfeldTheta) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 599 ≤ A) (hAx : A ≤ x / 2) :
    (x - 2 * A) - δ * x - 2 * (√x * log x ^ 2 / (8 * π)) ≤ ∫ y in A..(x - A), Gfun δ y := by
  set ε := √x * log x ^ 2 / (8 * π) with hε
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < x - A := by linarith
  have hAB : A ≤ x - A := by linarith
  have hcp : 0 < 1 + δ := by linarith
  set ℓ := log (1 + δ) with hℓ
  have hℓle : ℓ ≤ δ := by
    have := log_le_sub_one_of_pos hcp
    linarith
  have hℓge : δ / (1 + δ) ≤ ℓ := by
    have h := one_sub_inv_le_log_of_pos hcp
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by
      field_simp
      ring
    rw [e] at h
    exact h
  -- the identity and the two monotonicity bounds
  rw [integral_Gfun_eq hδ hA0 hAB]
  have h1 := integral_theta_div_ge hB0 hδ
  have h2 := integral_theta_div_le hA0 hδ
  -- Schoenfeld at `x - A` and at `(1+δ)A`
  have hS1 := theta_err_le (x := x) hSch (by linarith) (by linarith : x - A ≤ x)
  have hS2 := theta_err_le (x := x) hSch (by nlinarith : 599 ≤ (1 + δ) * A)
    (by nlinarith : (1 + δ) * A ≤ x)
  rw [← hε] at hS1 hS2
  have hS1' : x - A - ε ≤ Chebyshev.theta (x - A) := by
    have := neg_abs_le (Chebyshev.theta (x - A) - (x - A)); linarith
  have hS2' : Chebyshev.theta ((1 + δ) * A) ≤ (1 + δ) * A + ε := by
    have := le_abs_self (Chebyshev.theta ((1 + δ) * A) - (1 + δ) * A); linarith
  have hε0 : 0 ≤ ε := by positivity
  -- `D₀ ≤ D` with `D = θ(x-A) - θ((1+δ)A)`
  set D₀ := (x - 2 * A) - δ * A - 2 * ε with hD₀
  have hexp : (1 + δ) * A = A + δ * A := by ring
  have hD : D₀ ≤ Chebyshev.theta (x - A) - Chebyshev.theta ((1 + δ) * A) := by
    rw [hD₀]; linarith
  -- `k = ℓ/δ ∈ [1 - δ, 1]`
  set k := ℓ / δ with hk
  have hk1 : k ≤ 1 := by rw [hk, div_le_one hδ]; exact hℓle
  have hk0 : 1 - δ ≤ k := by
    rw [hk, le_div_iff₀ hδ]
    have : (1 - δ) * δ ≤ δ / (1 + δ) := by
      rw [le_div_iff₀ hcp]
      nlinarith [sq_nonneg δ]
    linarith
  have hkpos : 0 ≤ k := by linarith
  have hmain : k * D₀ ≤
      ((∫ t in (x - A)..(1 + δ) * (x - A), Chebyshev.theta t / t)
        - ∫ t in A..(1 + δ) * A, Chebyshev.theta t / t) / δ := by
    have hθ : k * D₀ ≤ k * (Chebyshev.theta (x - A) - Chebyshev.theta ((1 + δ) * A)) :=
      mul_le_mul_of_nonneg_left hD hkpos
    have hint : ℓ * (Chebyshev.theta (x - A) - Chebyshev.theta ((1 + δ) * A)) ≤
        (∫ t in (x - A)..(1 + δ) * (x - A), Chebyshev.theta t / t)
          - ∫ t in A..(1 + δ) * A, Chebyshev.theta t / t := by
      nlinarith
    calc k * D₀ ≤ k * (Chebyshev.theta (x - A) - Chebyshev.theta ((1 + δ) * A)) := hθ
      _ = ℓ * (Chebyshev.theta (x - A) - Chebyshev.theta ((1 + δ) * A)) / δ := by
          rw [hk]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hint hδ.le
  refine le_trans ?_ hmain
  -- `(x - 2A) - δx - 2ε ≤ k D₀`
  have hDle : D₀ ≤ x - 2 * A := by rw [hD₀]; nlinarith
  rcases le_or_gt 0 D₀ with h0 | h0
  · nlinarith [mul_le_mul_of_nonneg_right hk0 h0]
  · nlinarith [mul_le_mul_of_nonneg_right hk1 (le_of_lt (neg_pos.2 h0))]

end GoldbachRH
