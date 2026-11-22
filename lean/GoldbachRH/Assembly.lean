import GoldbachRH.Lemma8
import GoldbachRH.Range

/-!
# From the lemmas of §§4–7 to the weighted mean-square bound

This file states three of the paper's results as propositions and proves that, together with
Lemma 8, they imply `WeightedMeanSquareBound`, the right-hand part of (6).

* `Lemma7`: `‖A‖²_ω ≤ x² 𝒯` (the Schur bound). Its statement includes the hypotheses it needs
  (RH and the explicit formula for ψ). Proved in `GoldbachRH.Lemma7` (`GoldbachRH.lemma7`).
* `PrimePowerBound`: the `ℰ` row of Proposition 13, `‖P‖²_ω ≤ δ x² ℰ`. Proved in
  `GoldbachRH.PrimePowers` (`GoldbachRH.primePowerBound`).
* `Prop13T`: the `𝒯` row of Proposition 13, `𝒯 ≤ δ (T_main + T_pr + R_T)`. **Not yet
  formalized.** In the paper it rests on Lemmas 4 (ii), (iii), (v) and 9–12; 4 (ii) and (v) are
  proved in `KernelFourier`.

Also proved here: the identity `V_θ = A + B - P` and the triangle inequality step
(`wms_of_lemmas`).
-/

open Real MeasureTheory Set
open scoped ENNReal

namespace GoldbachRH

/-- **Lemma 7** (proved in `GoldbachRH.Lemma7`). Under RH and the explicit formula, `‖A‖²_ω ≤ x² 𝒯`. -/
def Lemma7 : Prop :=
  RiemannHypothesis → ExplicitFormulaPsi →
    ∀ x V δ : ℝ, 0 < x → 0 < V → 0 ≤ δ → 1 < x * exp (-V) →
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Afun δ y ^ 2 * weight x V y)
        ≤ ENNReal.ofReal (x ^ 2) * Tsum δ V

/-- **Proposition 13, row `𝒯`** (not yet formalized). With `L = log x`, `δ = 2L²/x`, `V = 3√L`:
`𝒯 ≤ δ (T_main + T_pr + R_T)`. -/
def Prop13T : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 3.9e18 ≤ x →
    Tsum (dl (log x)) (Vp (log x)) ≤ ENNReal.ofReal (dl (log x) * Tb (log x))

/-- **Proposition 13, row `ℰ`** (proved in `GoldbachRH.PrimePowers`). `‖P‖²_ω ≤ δ x² ℰ` with `ℰ` the Table 1 bound. -/
def PrimePowerBound : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 3.9e18 ≤ x →
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Pfun (dl (log x)) y ^ 2 * weight x (Vp (log x)) y)
      ≤ ENNReal.ofReal (dl (log x) * x ^ 2 * Eb (log x))

/-! ### Auxiliary facts -/

lemma exp_42_8_le : exp 42.8 ≤ 3.9e18 := by
  have h1 : exp 42.8 = exp 43 / exp 0.2 := by rw [← exp_sub]; norm_num
  have h43 : exp (43 : ℝ) ≤ 2.7182818286 ^ 43 := by
    rw [show (43 : ℝ) = (43 : ℕ) * 1 by norm_num, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 43
  have h02 : (1.22 : ℝ) ≤ exp 0.2 := by
    have := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.2 by norm_num); norm_num at this ⊢
    linarith
  rw [h1, div_le_iff₀ (exp_pos _)]
  calc exp (43 : ℝ) ≤ 2.7182818286 ^ 43 := h43
    _ ≤ 3.9e18 * 1.22 := by norm_num
    _ ≤ 3.9e18 * exp 0.2 := by gcongr

lemma log_ge_of_ge {x : ℝ} (hx : 3.9e18 ≤ x) : (42.8 : ℝ) ≤ log x := by
  rw [le_log_iff_exp_le (by linarith)]; exact exp_42_8_le.trans hx

/-- Weighted Cauchy–Schwarz: `(a+b+c)² ≤ a²/α + b²/β + c²/γ` when `α + β + γ = 1`. -/
lemma sq_three_le {a b c α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (h : α + β + γ = 1) : (a + b + c) ^ 2 ≤ a ^ 2 / α + b ^ 2 / β + c ^ 2 / γ := by
  obtain ⟨u, rfl⟩ : ∃ u, a = α * u := ⟨a / α, by field_simp⟩
  obtain ⟨v, rfl⟩ : ∃ v, b = β * v := ⟨b / β, by field_simp⟩
  obtain ⟨w, rfl⟩ : ∃ w, c = γ * w := ⟨c / γ, by field_simp⟩
  have e1 : (α * u) ^ 2 / α = α * u ^ 2 := by field_simp
  have e2 : (β * v) ^ 2 / β = β * v ^ 2 := by field_simp
  have e3 : (γ * w) ^ 2 / γ = γ * w ^ 2 := by field_simp
  rw [e1, e2, e3]
  have hs : α * u ^ 2 + β * v ^ 2 + γ * w ^ 2
      = (α + β + γ) * (α * u ^ 2 + β * v ^ 2 + γ * w ^ 2) := by rw [h, one_mul]
  rw [hs]
  nlinarith [mul_nonneg (mul_nonneg hα.le hβ.le) (sq_nonneg (u - v)),
    mul_nonneg (mul_nonneg hβ.le hγ.le) (sq_nonneg (v - w)),
    mul_nonneg (mul_nonneg hα.le hγ.le) (sq_nonneg (u - w))]

/-- The triangle inequality in `L²(ω)` for three functions, in the form used in (6). -/
lemma lintegral_three {ω A B P : ℝ → ℝ} (hω : ∀ y, 0 ≤ ω y)
    (hAm : Measurable fun y => A y ^ 2 * ω y) (hBm : Measurable fun y => B y ^ 2 * ω y)
    {K sa sb sc : ℝ} (hK : 0 ≤ K) (ha : 0 < sa) (hb : 0 < sb) (hc : 0 < sc)
    (hA : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (A y ^ 2 * ω y) ≤ ENNReal.ofReal (K * sa ^ 2))
    (hB : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (B y ^ 2 * ω y) ≤ ENNReal.ofReal (K * sb ^ 2))
    (hP : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (P y ^ 2 * ω y) ≤ ENNReal.ofReal (K * sc ^ 2)) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((A y + B y - P y) ^ 2 * ω y)
      ≤ ENNReal.ofReal (K * (sa + sb + sc) ^ 2) := by
  set S := sa + sb + sc with hS
  have hS0 : 0 < S := by positivity
  have hα : 0 < sa / S := by positivity
  have hβ : 0 < sb / S := by positivity
  have hγ : 0 < sc / S := by positivity
  have hsum : sa / S + sb / S + sc / S = 1 := by
    rw [← add_div, ← add_div, ← hS, div_self hS0.ne']
  set fA : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (S / sa) * ENNReal.ofReal (A y ^ 2 * ω y)
  set fB : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (S / sb) * ENNReal.ofReal (B y ^ 2 * ω y)
  set fP : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (S / sc) * ENNReal.ofReal (P y ^ 2 * ω y)
  have hpt : ∀ y, ENNReal.ofReal ((A y + B y - P y) ^ 2 * ω y) ≤ fA y + fB y + fP y := by
    intro y
    have h3 := mul_le_mul_of_nonneg_right
      (sq_three_le (a := A y) (b := B y) (c := -P y) hα hβ hγ hsum) (hω y)
    simp only [fA, fB, fP]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity [hω y]) (by positivity [hω y]),
      ← ENNReal.ofReal_add (by positivity [hω y]) (by positivity [hω y])]
    apply ENNReal.ofReal_le_ofReal
    have e : (A y + B y + -P y) ^ 2 = (A y + B y - P y) ^ 2 := by ring
    rw [e] at h3
    calc (A y + B y - P y) ^ 2 * ω y ≤ _ := h3
      _ = S / sa * (A y ^ 2 * ω y) + S / sb * (B y ^ 2 * ω y) + S / sc * (P y ^ 2 * ω y) := by
        field_simp
  have mA : Measurable fA := (ENNReal.measurable_ofReal.comp hAm).const_mul _
  have mB : Measurable fB := (ENNReal.measurable_ofReal.comp hBm).const_mul _
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((A y + B y - P y) ^ 2 * ω y)
      ≤ ∫⁻ y in Ioi (0 : ℝ), (fA y + fB y + fP y) := lintegral_mono hpt
    _ = ENNReal.ofReal (S / sa) * (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (A y ^ 2 * ω y))
        + ENNReal.ofReal (S / sb) * (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (B y ^ 2 * ω y))
        + ENNReal.ofReal (S / sc) * (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (P y ^ 2 * ω y)) := by
      have e1 : ∫⁻ y in Ioi (0 : ℝ), (fA y + fB y + fP y)
          = (∫⁻ y in Ioi (0 : ℝ), (fA y + fB y)) + ∫⁻ y in Ioi (0 : ℝ), fP y :=
        lintegral_add_left (mA.add mB) _
      have e2 : ∫⁻ y in Ioi (0 : ℝ), (fA y + fB y)
          = (∫⁻ y in Ioi (0 : ℝ), fA y) + ∫⁻ y in Ioi (0 : ℝ), fB y :=
        lintegral_add_left mA _
      rw [e1, e2]
      simp only [fA, fB, fP]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (S / sa) * ENNReal.ofReal (K * sa ^ 2)
        + ENNReal.ofReal (S / sb) * ENNReal.ofReal (K * sb ^ 2)
        + ENNReal.ofReal (S / sc) * ENNReal.ofReal (K * sc ^ 2) := by gcongr
    _ = ENNReal.ofReal (K * S ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hS]; field_simp

/-! ### Measurability -/

lemma measurable_psi : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
lemma measurable_theta : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable

lemma measurable_weight (x V : ℝ) : Measurable (weight x V) := by
  unfold weight
  exact ((measurable_const.div measurable_id).pow_const 2).mul
    ((measurable_W V).comp (Real.measurable_log.comp (measurable_const.div measurable_id)))

lemma measurable_Bfun (δ : ℝ) : Measurable (Bfun δ) := by
  unfold Bfun
  refine ((Real.measurable_log.comp ?_).div_const _).sub ((Real.measurable_log.comp ?_).div_const _)
  · exact measurable_const.sub (measurable_const.div (measurable_id.pow_const 2))
  · exact measurable_const.sub (measurable_const.div (measurable_const.mul
      (measurable_id.pow_const 2)))

lemma measurable_Afun (δ : ℝ) : Measurable (Afun δ) := by
  unfold Afun Vψ
  exact ((measurable_psi.comp (measurable_const.mul measurable_id)).sub measurable_psi
    |>.sub (measurable_const.mul measurable_id)).sub (measurable_Bfun δ)

/-! ### Assembly -/

lemma dl_log {x : ℝ} (hx : 0 < x) : dl (log x) = 2 * log x ^ 2 / x := by
  unfold dl; rw [exp_neg, exp_log hx]; ring

lemma x_exp_neg_Vp {x : ℝ} (hx : 0 < x) : x * exp (-Vp (log x)) = exp (uL (log x)) := by
  rw [uL, sub_eq_add_neg, exp_add, exp_log hx]

/-- **The weighted mean-square bound from the lemmas.** Lemma 7, the two rows of
Proposition 13 and Lemma 8 (proved) give the right-hand part of (6). -/
theorem wms_of_lemmas (h7 : Lemma7) (h13 : Prop13T) (hPP : PrimePowerBound)
    (hRH : RiemannHypothesis) (hEF : ExplicitFormulaPsi) : WeightedMeanSquareBound := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hL := log_ge_of_ge hx
  rw [← dl_log hx0]
  set L := log x with hLdef
  set δ := dl L with hδdef
  set V := Vp L with hVdef
  have hV : 0 < V := by linarith [Vp_ge hL]
  have hδ : 0 < δ := by rw [hδdef]; unfold dl; positivity
  have hu := uL_ge hL
  have hy0 : x * exp (-V) = exp (uL L) := x_exp_neg_Vp hx0
  have hexpu : 3 ≤ exp (uL L) := by linarith [add_one_le_exp (uL L)]
  -- positivity of the three Table 1 bounds
  have hTb : 0 < Tb L := by
    unfold Tb Tmain Tpr
    have := RT_nonneg hL
    positivity
  have hEb : 0 < Eb L := by
    unfold Eb
    have h1 : 0 < (L + Vp L + 1) / log 2 := by
      have := Vp_ge hL; have : 0 < log 2 := log_pos (by norm_num); positivity
    have h2 : 0 < uL L / log 2 * (uL L / 2 + 0.75) := by
      have : 0 < log 2 := log_pos (by norm_num); positivity
    have := dl_nonneg hL
    positivity
  have hBb : 0 < Bb L := by unfold Bb; rw [← hδdef]; positivity
  -- the three bounds
  have hA : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Afun δ y ^ 2 * weight x V y)
      ≤ ENNReal.ofReal (δ * x ^ 2 * √(Tb L) ^ 2) := by
    calc _ ≤ ENNReal.ofReal (x ^ 2) * Tsum δ V :=
          h7 hRH hEF x V δ hx0 hV hδ.le (by rw [hy0]; linarith)
      _ ≤ ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (δ * Tb L) := by gcongr; exact h13 hRH x hx
      _ = _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg x), sq_sqrt hTb.le]; congr 1; ring
  have hB : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Bfun δ y ^ 2 * weight x V y)
      ≤ ENNReal.ofReal (δ * x ^ 2 * √(Bb L) ^ 2) := by
    calc _ ≤ ENNReal.ofReal (4 / 5 * δ ^ 2 * x ^ 2 / (x * exp (-V)) ^ 5) :=
          lemma8 hx0 hV hδ.le (by rw [hy0]; exact hexpu)
      _ = _ := by
        rw [sq_sqrt hBb.le, hy0, ← exp_nat_mul]
        congr 1
        unfold Bb
        rw [← hδdef, show -5 * uL L = -((5 : ℕ) * uL L) by push_cast; ring, exp_neg]
        field_simp
        norm_num
  have hP : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Pfun δ y ^ 2 * weight x V y)
      ≤ ENNReal.ofReal (δ * x ^ 2 * √(Eb L) ^ 2) := by
    rw [sq_sqrt hEb.le]; exact hPP hRH x hx
  have hmain := lintegral_three (ω := weight x V) (A := Afun δ) (B := Bfun δ) (P := Pfun δ)
    (weight_nonneg hV) (((measurable_Afun δ).pow_const 2).mul (measurable_weight x V))
    (((measurable_Bfun δ).pow_const 2).mul (measurable_weight x V))
    (by positivity) (sqrt_pos.2 hTb) (sqrt_pos.2 hBb) (sqrt_pos.2 hEb) hA hB hP
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Vθ δ y ^ 2 * weight x V y)
      = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((Afun δ y + Bfun δ y - Pfun δ y) ^ 2 * weight x V y) := by
        simp_rw [Vθ_eq]
    _ ≤ _ := hmain
    _ = _ := by congr 1; ring

end GoldbachRH
