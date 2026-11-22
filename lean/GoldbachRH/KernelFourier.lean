import GoldbachRH.Kernel
import GoldbachRH.Zeros

/-!
# Lemma 4 (ii) and (v): the Fourier transform of the kernel, and (K2)

Notation: `φ = kerProfile`, `a = Vξ`, `σ = π/V`.

* (v), (K2): `2 ∫₀^V v W(v) dv = 2V²/π²` (`K2`).
* (ii): `Ŵ ≥ 0` (`What_nonneg`), `(2π)⁻¹ ∫ Ŵ = 1` (`integral_What`) and
  `(2π)⁻¹ ∫ ξ² Ŵ(ξ) dξ = σ²` (`integral_sq_What`).

Route. `Ŵ(ξ) = 2V I(Vξ)` with `I(a) = ∫₀¹ φ(t) cos(at) dt`, and an explicit antiderivative gives
`(π² - a²)² I(a) = 2π²(1 + cos a)`, so `I(a) ≥ 0` away from `a = ±π`; at `a = ±π`, `I = 1/4`.
For the moments, Fourier inversion (Mathlib) at `0` gives `∫ Ŵ = 2π W(0)`. The function
`g = -W''` is explicit, `g(v) = V⁻² (π²(1-t) cos πt - π sin πt)` with `t = |v|/V`, and the same
method gives `ĝ(ξ) = ξ² Ŵ(ξ)`; inversion then gives `∫ ξ² Ŵ = 2π g(0) = 2π σ²`.
-/

open Real MeasureTheory Set FourierTransform

namespace GoldbachRH

/-! ### Derivative helpers -/

lemma hasDerivAt_sin_mul (k t : ℝ) : HasDerivAt (fun t => sin (k * t)) (k * cos (k * t)) t := by
  have h := ((hasDerivAt_id t).const_mul k).sin
  simp only [id, mul_one] at h
  convert h using 1; ring

lemma hasDerivAt_cos_mul (k t : ℝ) : HasDerivAt (fun t => cos (k * t)) (-(k * sin (k * t))) t := by
  have h := ((hasDerivAt_id t).const_mul k).cos
  simp only [id, mul_one] at h
  convert h using 1; ring

lemma hd_term (c e : ℝ) {f1 f2 : ℝ → ℝ} {d1 d2 t : ℝ} (h1 : HasDerivAt f1 d1 t)
    (h2 : HasDerivAt f2 d2 t) :
    HasDerivAt (fun t => (c + e * t) * (f1 t * f2 t))
      (e * (f1 t * f2 t) + (c + e * t) * (d1 * f2 t + f1 t * d2)) t := by
  have hl : HasDerivAt (fun t => c + e * t) e t := by
    simpa using ((hasDerivAt_id t).const_mul e).const_add c
  exact hl.mul (h1.mul h2)

lemma hd_quad (t : ℝ) : HasDerivAt (fun t => π ^ 2 * (2 * t - t ^ 2)) (π ^ 2 * (2 - 2 * t)) t := by
  have h := (((hasDerivAt_id t).const_mul 2).sub (hasDerivAt_pow 2 t)).const_mul (π ^ 2)
  simp only [id, mul_one] at h
  convert h using 1; push_cast; ring

lemma continuous_cos_mul (a : ℝ) : Continuous fun t : ℝ => cos (a * t) :=
  continuous_cos.comp (continuous_const.mul continuous_id)

/-! ### (K2) -/

/-- **(K2)**, Lemma 4 (v): `2 ∫₀^V v W(v) dv = 2V²/π²`. -/
theorem K2 {V : ℝ} (hV : 0 < V) : 2 * ∫ v in (0 : ℝ)..V, v * W V v = 2 * V ^ 2 / π ^ 2 := by
  -- antiderivative `V² F(v/V)` with `F(t) = (t - t²) sin πt/π + (1 - 3t) cos πt/π² + 3 sin πt/π³`
  set F : ℝ → ℝ := fun v => V ^ 2 * ((v / V - (v / V) ^ 2) * sin (π * (v / V)) / π
    + (1 - 3 * (v / V)) * cos (π * (v / V)) / π ^ 2 + 3 * sin (π * (v / V)) / π ^ 3) with hF
  have hd : ∀ v, HasDerivAt F (v * kerProfile (v / V)) v := by
    intro v
    have hu : HasDerivAt (fun v : ℝ => v / V) (1 / V) v := by
      simpa using (hasDerivAt_id v).div_const V
    have hs := (hasDerivAt_sin_mul π (v / V)).comp v hu
    have hc := (hasDerivAt_cos_mul π (v / V)).comp v hu
    have h := ((((hu.sub (hu.pow 2)).mul hs).div_const π).add
      (((hu.const_mul 3).const_sub 1).mul hc |>.div_const (π ^ 2))).add
      ((hs.const_mul 3).div_const (π ^ 3)) |>.const_mul (V ^ 2)
    convert h using 1
    · ext y; simp [hF, Function.comp_def]
    · simp only [Function.comp_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
      unfold kerProfile
      have := pi_pos.ne'
      have := hV.ne'
      have hVV : V ^ 2 * V⁻¹ = V := by field_simp
      generalize sin (π * (v / V)) = S
      generalize cos (π * (v / V)) = C
      field_simp
      linear_combination (2 * v * π * S) * hVV
  have hcont : Continuous fun v => v * kerProfile (v / V) :=
    continuous_id.mul (continuous_kerProfile.comp (continuous_id.div_const V))
  have hcongr : ∫ v in (0 : ℝ)..V, v * W V v = ∫ v in (0 : ℝ)..V, v * kerProfile (v / V) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hV.le] at hv
    simp only
    rw [W_of_mem hV hv.1 hv.2]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (hcont.intervalIntegrable _ _)]
  simp only [hF, div_self hV.ne', zero_div, mul_one, mul_zero, sin_pi, cos_pi, sin_zero, cos_zero]
  have := pi_pos.ne'
  field_simp
  ring

/-! ### The cosine integrals `I` and `J` -/

/-- `I(a) = ∫₀¹ φ(t) cos(at) dt`. -/
noncomputable def Iint (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, kerProfile t * cos (a * t)

/-- The profile of `g = -W''`: `π²(1-t) cos πt - π sin πt`. -/
noncomputable def gProfile (t : ℝ) : ℝ := π ^ 2 * (1 - t) * cos (π * t) - π * sin (π * t)

lemma continuous_gProfile : Continuous gProfile := by unfold gProfile; fun_prop

/-- `J(a) = ∫₀¹ (π²(1-t) cos πt - π sin πt) cos(at) dt`. -/
noncomputable def Jint (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, gProfile t * cos (a * t)

lemma Iint_closed (a : ℝ) : (π ^ 2 - a ^ 2) ^ 2 * Iint a = 2 * π ^ 2 * (1 + cos a) := by
  set D := π ^ 2 - a ^ 2
  set H : ℝ → ℝ := fun t =>
    (π * D + (-(π * D)) * t) * (sin (π * t) * cos (a * t))
    + (-(a * D) + a * D * t) * (cos (π * t) * sin (a * t))
    + (-(a * (3 * π ^ 2 - a ^ 2)) / π + 0 * t) * (sin (π * t) * sin (a * t))
    + (-(2 * π ^ 2) + 0 * t) * (cos (π * t) * cos (a * t)) with hH
  have hd : ∀ t, HasDerivAt H (D ^ 2 * (kerProfile t * cos (a * t))) t := by
    intro t
    have h := (((hd_term (π * D) (-(π * D)) (hasDerivAt_sin_mul π t) (hasDerivAt_cos_mul a t)).add
      (hd_term (-(a * D)) (a * D) (hasDerivAt_cos_mul π t) (hasDerivAt_sin_mul a t))).add
      (hd_term (-(a * (3 * π ^ 2 - a ^ 2)) / π) 0 (hasDerivAt_sin_mul π t)
        (hasDerivAt_sin_mul a t))).add
      (hd_term (-(2 * π ^ 2)) 0 (hasDerivAt_cos_mul π t) (hasDerivAt_cos_mul a t))
    convert h using 1
    unfold kerProfile
    have := pi_pos.ne'
    simp only [D]
    field_simp
    ring
  have hcont : Continuous fun t => D ^ 2 * (kerProfile t * cos (a * t)) :=
    continuous_const.mul (continuous_kerProfile.mul (continuous_cos_mul a))
  unfold Iint
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [hH, mul_one, mul_zero, sin_pi, cos_pi, sin_zero, cos_zero]
  ring

lemma Jint_closed (a : ℝ) : (π ^ 2 - a ^ 2) ^ 2 * Jint a = 2 * a ^ 2 * π ^ 2 * (1 + cos a) := by
  set D := π ^ 2 - a ^ 2
  set H : ℝ → ℝ := fun t =>
    (π ^ 3 * D + (-(π ^ 3 * D)) * t) * (sin (π * t) * cos (a * t))
    + (-(a * π ^ 2 * D) + a * π ^ 2 * D * t) * (cos (π * t) * sin (a * t))
    + (-(a * π * (a ^ 2 + π ^ 2)) + 0 * t) * (sin (π * t) * sin (a * t))
    + (-(2 * a ^ 2 * π ^ 2) + 0 * t) * (cos (π * t) * cos (a * t)) with hH
  have hd : ∀ t, HasDerivAt H (D ^ 2 * (gProfile t * cos (a * t))) t := by
    intro t
    have h := (((hd_term (π ^ 3 * D) (-(π ^ 3 * D)) (hasDerivAt_sin_mul π t)
      (hasDerivAt_cos_mul a t)).add
      (hd_term (-(a * π ^ 2 * D)) (a * π ^ 2 * D) (hasDerivAt_cos_mul π t)
        (hasDerivAt_sin_mul a t))).add
      (hd_term (-(a * π * (a ^ 2 + π ^ 2))) 0 (hasDerivAt_sin_mul π t)
        (hasDerivAt_sin_mul a t))).add
      (hd_term (-(2 * a ^ 2 * π ^ 2)) 0 (hasDerivAt_cos_mul π t) (hasDerivAt_cos_mul a t))
    convert h using 1
    unfold gProfile
    simp only [D]
    ring
  have hcont : Continuous fun t => D ^ 2 * (gProfile t * cos (a * t)) :=
    continuous_const.mul (continuous_gProfile.mul (continuous_cos_mul a))
  unfold Jint
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [hH, mul_one, mul_zero, sin_pi, cos_pi, sin_zero, cos_zero]
  ring

lemma Iint_pi : Iint π = 1 / 4 := by
  set H : ℝ → ℝ := fun t => (π ^ 2 * (2 * t - t ^ 2)
    + (2 * π + (-(2 * π)) * t) * (sin (π * t) * cos (π * t))
    + (3 + 0 * t) * (sin (π * t) * sin (π * t))) / (4 * π ^ 2) with hH
  have hd : ∀ t, HasDerivAt H (kerProfile t * cos (π * t)) t := by
    intro t
    have h := (((hd_quad t).add (hd_term (2 * π) (-(2 * π)) (hasDerivAt_sin_mul π t)
      (hasDerivAt_cos_mul π t))).add (hd_term 3 0 (hasDerivAt_sin_mul π t)
      (hasDerivAt_sin_mul π t))).div_const (4 * π ^ 2)
    convert h using 1
    rw [← sub_eq_zero]
    have hsc := sin_sq_add_cos_sq (π * t)
    have e : kerProfile t * cos (π * t) - (π ^ 2 * (2 - 2 * t) + (-(2 * π) * (sin (π * t) *
        cos (π * t)) + (2 * π + -(2 * π) * t) * (π * cos (π * t) * cos (π * t) + sin (π * t) *
        -(π * sin (π * t)))) + (0 * (sin (π * t) * sin (π * t)) + (3 + 0 * t) * (π * cos (π * t) *
        sin (π * t) + sin (π * t) * (π * cos (π * t))))) / (4 * π ^ 2)
        = (1 - t) / 2 * (sin (π * t) ^ 2 + cos (π * t) ^ 2 - 1) := by
      unfold kerProfile
      have := pi_pos.ne'
      field_simp
      ring
    rw [e, hsc]; ring
  have hcont : Continuous fun t => kerProfile t * cos (π * t) :=
    continuous_kerProfile.mul (continuous_cos_mul π)
  unfold Iint
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [hH, mul_one, mul_zero, sin_pi, cos_pi, sin_zero, cos_zero]
  have := pi_pos.ne'
  field_simp
  ring

lemma Jint_pi : Jint π = π ^ 2 / 4 := by
  set H : ℝ → ℝ := fun t => (π ^ 2 * (2 * t - t ^ 2)
    + (2 * π + (-(2 * π)) * t) * (sin (π * t) * cos (π * t))
    + (-1 + 0 * t) * (sin (π * t) * sin (π * t))) / 4 with hH
  have hd : ∀ t, HasDerivAt H (gProfile t * cos (π * t)) t := by
    intro t
    have h := (((hd_quad t).add (hd_term (2 * π) (-(2 * π)) (hasDerivAt_sin_mul π t)
      (hasDerivAt_cos_mul π t))).add (hd_term (-1) 0 (hasDerivAt_sin_mul π t)
      (hasDerivAt_sin_mul π t))).div_const 4
    convert h using 1
    rw [← sub_eq_zero]
    have hsc := sin_sq_add_cos_sq (π * t)
    have e : gProfile t * cos (π * t) - (π ^ 2 * (2 - 2 * t) + (-(2 * π) * (sin (π * t) *
        cos (π * t)) + (2 * π + -(2 * π) * t) * (π * cos (π * t) * cos (π * t) + sin (π * t) *
        -(π * sin (π * t)))) + (0 * (sin (π * t) * sin (π * t)) + (-1 + 0 * t) * (π * cos (π * t) *
        sin (π * t) + sin (π * t) * (π * cos (π * t))))) / 4
        = π ^ 2 * (1 - t) / 2 * (sin (π * t) ^ 2 + cos (π * t) ^ 2 - 1) := by
      unfold gProfile
      ring
    rw [e, hsc]; ring
  have hcont : Continuous fun t => gProfile t * cos (π * t) :=
    continuous_gProfile.mul (continuous_cos_mul π)
  unfold Jint
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [hH, mul_one, mul_zero, sin_pi, cos_pi, sin_zero, cos_zero]
  ring

/-! ### Radial functions and their cosine transforms -/

/-- `rad V p v = p(|v|/V)` for `|v| ≤ V`, and `0` otherwise. `W V = rad V kerProfile`. -/
noncomputable def rad (V : ℝ) (prof : ℝ → ℝ) (v : ℝ) : ℝ := if |v| ≤ V then prof (|v| / V) else 0

lemma W_eq_rad (V : ℝ) : W V = rad V kerProfile := rfl

section Radial
variable {V : ℝ} {prof : ℝ → ℝ}

lemma continuous_rad (hV : 0 < V) (hp : Continuous prof) (h1 : prof 1 = 0) :
    Continuous (rad V prof) := by
  unfold rad
  refine Continuous.if_le (hp.comp (continuous_abs.div_const V)) continuous_const continuous_abs
    continuous_const ?_
  intro v hv
  simp only [hv, div_self hV.ne', h1]

lemma rad_neg (v : ℝ) : rad V prof (-v) = rad V prof v := by simp [rad, abs_neg]

lemma rad_eq_zero {v : ℝ} (hv : v ∉ Icc (-V) V) : rad V prof v = 0 := by
  have h : ¬ |v| ≤ V := fun h =>
    hv ⟨by linarith [neg_abs_le v], by linarith [le_abs_self v]⟩
  simp only [rad, h, ite_false]

lemma hasCompactSupport_rad : HasCompactSupport (rad V prof) :=
  HasCompactSupport.intro isCompact_Icc fun _ hv => rad_eq_zero hv

/-- The cosine transform of a radial function: `∫ rad(v) cos(ξv) dv = 2V ∫₀¹ p(t) cos(Vξ t) dt`. -/
lemma integral_rad_cos (hV : 0 < V) (hp : Continuous prof) (h1 : prof 1 = 0) (ξ : ℝ) :
    ∫ v, rad V prof v * cos (ξ * v) = 2 * V * ∫ t in (0 : ℝ)..1, prof t * cos (V * ξ * t) := by
  set f : ℝ → ℝ := fun v => rad V prof v * cos (ξ * v) with hf
  have hfc : Continuous f := (continuous_rad hV hp h1).mul (continuous_cos_mul ξ)
  have hzero : ∀ v ∉ Icc (-V) V, f v = 0 := fun v hv => by simp [hf, rad_eq_zero hv]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)]
  have hneg : ∫ v in (-V)..0, f v = ∫ v in (0 : ℝ)..V, f v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := V) f
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun v _ => ?_
    show rad V prof (-v) * cos (ξ * -v) = rad V prof v * cos (ξ * v)
    rw [rad_neg, mul_neg, cos_neg]
  have hpos : ∫ v in (0 : ℝ)..V, f v = ∫ v in (0 : ℝ)..V, prof (v / V) * cos (ξ * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hV.le] at hv
    simp only [hf, rad, abs_of_nonneg hv.1, hv.2, ite_true]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun v => prof (v / V) * cos (ξ * v)) hV.ne'
  simp only [mul_zero, mul_one] at hsub
  have hsimp : ∀ t : ℝ, prof (V * t / V) * cos (ξ * (V * t)) = prof t * cos (V * ξ * t) := by
    intro t; rw [mul_div_cancel_left₀ t hV.ne']; ring_nf
  simp only [hsimp] at hsub
  rw [hneg, hpos, hsub, smul_eq_mul, ← mul_assoc, mul_assoc 2 V, mul_inv_cancel₀ hV.ne', mul_one,
    two_mul]

end Radial

/-! ### Fourier inversion for cosine transforms -/

/-- For a continuous, even, compactly supported `f` whose cosine transform
`F(ξ) = ∫ f(v) cos(ξv) dv` is integrable, `∫ F = 2π f(0)`. From Mathlib's Fourier inversion. -/
lemma integral_cos_transform {f : ℝ → ℝ} (hc : Continuous f) (hcs : HasCompactSupport f)
    (hev : ∀ v, f (-v) = f v) (hF : Integrable fun ξ => ∫ v, f v * cos (ξ * v)) :
    ∫ ξ, (∫ v, f v * cos (ξ * v)) = 2 * π * f 0 := by
  set F : ℝ → ℝ := fun ξ => ∫ v, f v * cos (ξ * v) with hFdef
  set fC : ℝ → ℂ := fun v => (f v : ℂ) with hfCdef
  have hfC : Continuous fC := Complex.continuous_ofReal.comp hc
  have hfCi : Integrable fC :=
    hfC.integrable_of_hasCompactSupport (hcs.comp_left Complex.ofReal_zero)
  have key : ∀ w, 𝓕 fC w = ((F (2 * π * w) : ℝ) : ℂ) := by
    intro w
    rw [Real.fourier_real_eq]
    set u : ℝ → ℂ := fun v => 𝐞 (-(v * w)) • fC v with hu
    have huc : Continuous u := by rw [hu]; fun_prop
    have hui : Integrable u :=
      hfCi.norm.mono' huc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun v => by simp [hu, Circle.smul_def])
    have h1 : ∫ v, u v = ∫ v, u (-v) := (integral_neg_eq_self u volume).symm
    have hsum : ∀ v, u v + u (-v) = (((2 * (f v * cos (2 * π * w * v))) : ℝ) : ℂ) := by
      intro v
      simp only [hu, hfCdef, Circle.smul_def, Real.fourierChar_apply, hev, smul_eq_mul]
      have e1 : ((2 * π * -(v * w) : ℝ) : ℂ) = -((2 * π * w * v : ℝ) : ℂ) := by push_cast; ring
      have e2 : ((2 * π * -(-v * w) : ℝ) : ℂ) = ((2 * π * w * v : ℝ) : ℂ) := by push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      push_cast
      ring
    calc ∫ v, u v = (1 / 2 : ℂ) * ((∫ v, u v) + ∫ v, u (-v)) := by rw [← h1]; ring
      _ = (1 / 2 : ℂ) * ∫ v, (u v + u (-v)) := by rw [integral_add hui hui.comp_neg]
      _ = (1 / 2 : ℂ) * ∫ v, (((2 * (f v * cos (2 * π * w * v))) : ℝ) : ℂ) := by simp_rw [hsum]
      _ = ((F (2 * π * w) : ℝ) : ℂ) := by
        rw [integral_complex_ofReal, integral_const_mul, hFdef]
        push_cast
        ring
  have hFi : Integrable (𝓕 fC) := by
    rw [show 𝓕 fC = fun w => ((F (2 * π * w) : ℝ) : ℂ) from funext key]
    exact (hF.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).ofReal
  have h0 := congrFun (hfC.fourierInv_fourier_eq hfCi hFi) 0
  rw [Real.fourierInv_eq] at h0
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at h0
  rw [show 𝓕 fC = fun w => ((F (2 * π * w) : ℝ) : ℂ) from funext key] at h0
  simp only [hfCdef] at h0
  rw [integral_complex_ofReal] at h0
  have h0' : ∫ w, F (2 * π * w) = f 0 := by exact_mod_cast h0
  rw [Measure.integral_comp_mul_left F (2 * π), smul_eq_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)] at h0'
  have := pi_pos.ne'
  field_simp at h0'
  linarith

/-! ### Lemma 4 (ii) -/

lemma Iint_neg (a : ℝ) : Iint (-a) = Iint a := by simp [Iint, neg_mul, cos_neg]
lemma Jint_neg (a : ℝ) : Jint (-a) = Jint a := by simp [Jint, neg_mul, cos_neg]

lemma Iint_nonneg (a : ℝ) : 0 ≤ Iint a := by
  by_cases h : (π ^ 2 - a ^ 2) ^ 2 = 0
  · have ha : a = π ∨ a = -π := by
      have : (π - a) * (π + a) = 0 := by nlinarith [sq_nonneg ((π - a) * (π + a))]
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases ha with rfl | rfl
    · rw [Iint_pi]; norm_num
    · rw [Iint_neg, Iint_pi]; norm_num
  · have hpos : 0 < (π ^ 2 - a ^ 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm h)
    have := Iint_closed a
    have hc : 0 ≤ 1 + cos a := by linarith [neg_one_le_cos a]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π ^ 2) hc]

/-- `J(a) = a² I(a)`: the transform of `g = -W''` is `ξ² Ŵ`. -/
lemma Jint_eq (a : ℝ) : Jint a = a ^ 2 * Iint a := by
  by_cases h : (π ^ 2 - a ^ 2) ^ 2 = 0
  · have ha : a = π ∨ a = -π := by
      have : (π - a) * (π + a) = 0 := by nlinarith [sq_nonneg ((π - a) * (π + a))]
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases ha with rfl | rfl
    · rw [Jint_pi, Iint_pi]; ring
    · rw [Jint_neg, Iint_neg, Jint_pi, Iint_pi]; ring
  · have h1 := Iint_closed a
    have h2 := Jint_closed a
    apply mul_left_cancel₀ h
    rw [h2, show (π ^ 2 - a ^ 2) ^ 2 * (a ^ 2 * Iint a) = a ^ 2 * ((π ^ 2 - a ^ 2) ^ 2 * Iint a)
      by ring, h1]
    ring

lemma What_eq {V : ℝ} (hV : 0 < V) (ξ : ℝ) : What V ξ = 2 * V * Iint (V * ξ) := by
  unfold What Iint
  rw [W_eq_rad, integral_rad_cos hV continuous_kerProfile kerProfile_one]

/-- **Lemma 4 (ii), first part:** `Ŵ ≥ 0`. -/
theorem What_nonneg {V : ℝ} (hV : 0 < V) (ξ : ℝ) : 0 ≤ What V ξ := by
  rw [What_eq hV]; have := Iint_nonneg (V * ξ); positivity

lemma continuous_Iint : Continuous Iint :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun a t => kerProfile t * cos (a * t))
    ((continuous_kerProfile.comp continuous_snd).mul
      (continuous_cos.comp (continuous_fst.mul continuous_snd))) continuous_const

lemma continuous_Jint : Continuous Jint :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun a t => gProfile t * cos (a * t))
    ((continuous_gProfile.comp continuous_snd).mul
      (continuous_cos.comp (continuous_fst.mul continuous_snd))) continuous_const

lemma pi_sq_bounds : 9.86 ≤ π ^ 2 ∧ π ^ 2 ≤ 9.87 := by
  have h1 := pi_gt_d6; have h2 := pi_lt_d6
  constructor <;> nlinarith

/-- Decay of `I`: `|I(a)| ≤ 41/(1+a²)`. -/
lemma abs_Iint_le (a : ℝ) : |Iint a| ≤ 41 / (1 + a ^ 2) := by
  obtain ⟨hp1, hp2⟩ := pi_sq_bounds
  rw [abs_of_nonneg (Iint_nonneg a), le_div_iff₀ (by positivity)]
  by_cases ha : a ^ 2 ≤ 4 * π ^ 2
  · have hI : Iint a ≤ 1 := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 1)
        (f := fun t => kerProfile t * cos (a * t)) (by
          intro t ht
          rw [uIoc_of_le zero_le_one] at ht
          have h0 := kerProfile_nonneg ht.1.le ht.2
          have h1 : kerProfile t ≤ 1 := by
            have := kerProfile_antitoneOn ⟨le_refl 0, zero_le_one⟩ ⟨ht.1.le, ht.2⟩ ht.1.le
            have h00 : kerProfile 0 = 1 := by simp [kerProfile]
            linarith
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
          nlinarith [abs_cos_le_one (a * t), abs_nonneg (cos (a * t))])
      rw [Real.norm_eq_abs] at this
      simp only [sub_zero, abs_one, mul_one] at this
      exact (le_abs_self _).trans this
    have := Iint_nonneg a
    nlinarith
  · push Not at ha
    have hD : (3 / 4 * a ^ 2) ^ 2 ≤ (π ^ 2 - a ^ 2) ^ 2 := by nlinarith
    have hc := Iint_closed a
    have hcos : 1 + cos a ≤ 2 := by linarith [cos_le_one a]
    have hI0 := Iint_nonneg a
    -- `(9/16) a⁴ I ≤ 4π²`
    have h4 : 9 / 16 * a ^ 4 * Iint a ≤ 4 * π ^ 2 := by nlinarith
    nlinarith

/-- Decay of `J`: `|J(a)| ≤ 1700/(1+a²)`. -/
lemma abs_Jint_le (a : ℝ) : |Jint a| ≤ 1700 / (1 + a ^ 2) := by
  obtain ⟨hp1, hp2⟩ := pi_sq_bounds
  have hpi := pi_lt_d2
  have hpi0 := pi_pos
  rw [Jint_eq, abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (Iint_nonneg a),
    le_div_iff₀ (by positivity)]
  have hc := Iint_closed a
  have hI0 := Iint_nonneg a
  by_cases ha : a ^ 2 ≤ 4 * π ^ 2
  · have hI := abs_Iint_le a
    rw [abs_of_nonneg hI0, le_div_iff₀ (by positivity)] at hI
    have := mul_le_mul ha hI (by positivity) (by positivity)
    nlinarith
  · push Not at ha
    have hD : (3 / 4 * a ^ 2) ^ 2 ≤ (π ^ 2 - a ^ 2) ^ 2 := by nlinarith
    have hcos : 1 + cos a ≤ 2 := by linarith [cos_le_one a]
    have h4 : 9 / 16 * a ^ 4 * Iint a ≤ 4 * π ^ 2 := by nlinarith
    have h5 : 0 ≤ a ^ 2 * Iint a * (a ^ 2 - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) hI0) (by nlinarith)
    nlinarith

lemma integrable_scaled {V C : ℝ} (hV : 0 < V) {g : ℝ → ℝ} (hg : Continuous g)
    (hb : ∀ a, |g a| ≤ C / (1 + a ^ 2)) : Integrable fun ξ => g (V * ξ) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.comp_mul_left' hV.ne').const_mul C)
    (hg.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  simpa [div_eq_mul_inv] using hb (V * ξ)

/-- **Lemma 4 (ii), second part:** `(2π)⁻¹ ∫ Ŵ = 1`. -/
theorem integral_What {V : ℝ} (hV : 0 < V) : ∫ ξ, What V ξ = 2 * π := by
  have hF : Integrable fun ξ => ∫ v, W V v * cos (ξ * v) := by
    have := (integrable_scaled hV continuous_Iint abs_Iint_le).const_mul (2 * V)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [← What_eq hV]; rfl
  have hWc : Continuous (W V) := continuous_rad hV continuous_kerProfile kerProfile_one
  have hWs : HasCompactSupport (W V) := hasCompactSupport_rad
  have := integral_cos_transform hWc hWs (fun v => rad_neg v) hF
  have hW0 : W V 0 = 1 := by simp [W, hV.le, kerProfile]
  unfold What
  rw [this, hW0, mul_one]

/-- `g = -W''`, explicitly: `g(v) = V⁻² (π²(1-t) cos πt - π sin πt)`, `t = |v|/V`. -/
noncomputable def gW (V v : ℝ) : ℝ := rad V gProfile v / V ^ 2

lemma gProfile_one : gProfile 1 = 0 := by simp [gProfile]

/-- **Lemma 4 (ii), third part:** `(2π)⁻¹ ∫ ξ² Ŵ(ξ) dξ = σ²` with `σ = π/V`. -/
theorem integral_sq_What {V : ℝ} (hV : 0 < V) :
    ∫ ξ, ξ ^ 2 * What V ξ = 2 * π * (π / V) ^ 2 := by
  have hg : ∀ ξ, ∫ v, gW V v * cos (ξ * v) = ξ ^ 2 * What V ξ := by
    intro ξ
    simp only [gW, div_mul_eq_mul_div]
    rw [integral_div, integral_rad_cos hV continuous_gProfile gProfile_one, What_eq hV]
    rw [show ∫ t in (0 : ℝ)..1, gProfile t * cos (V * ξ * t) = Jint (V * ξ) from rfl, Jint_eq]
    field_simp
  have hgc : Continuous (gW V) := (continuous_rad hV continuous_gProfile gProfile_one).div_const _
  have hgs : HasCompactSupport (gW V) :=
    HasCompactSupport.intro (K := Icc (-V) V) isCompact_Icc fun v (hv : v ∉ Icc (-V) V) => by
      simp [gW, rad_eq_zero hv]
  have hF : Integrable fun ξ => ∫ v, gW V v * cos (ξ * v) := by
    have := (integrable_scaled hV continuous_Jint abs_Jint_le).const_mul (2 / V)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hg, What_eq hV, Jint_eq]
    field_simp
  have := integral_cos_transform hgc hgs (fun v => by simp [gW, rad_neg]) hF
  simp_rw [hg] at this
  rw [this]
  simp [gW, rad, hV.le, gProfile]
  field_simp

end GoldbachRH
