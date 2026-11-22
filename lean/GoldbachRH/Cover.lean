import GoldbachRH.Kernel

/-!
# The weighted cover (Lemma 6 of the paper, combined with Corollary 5)

If `(x, (1+δ)x]` contains no Goldbach number, then
`∫_{y > 0} V_θ(y)² ω(y) dy ≥ δ² x³ (1/2 - 9.55/V² - e^{-V})`.
-/

open Real Set MeasureTheory

namespace GoldbachRH

/-- If there is no prime in `(z, w]`, then `θ(w) = θ(z)`. -/
lemma theta_eq_of_no_prime {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w)
    (h : ∀ p : ℕ, p.Prime → z < p → (p : ℝ) ≤ w → False) :
    Chebyshev.theta w = Chebyshev.theta z := by
  unfold Chebyshev.theta
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp0, hpw⟩, hp⟩
    refine ⟨⟨hp0, ?_⟩, hp⟩
    by_contra hlt
    push Not at hlt
    exact h p hp ((Nat.floor_lt hz).1 hlt) ((Nat.le_floor_iff (hz.trans hzw)).1 hpw)
  · rintro ⟨⟨hp0, hpz⟩, hp⟩
    exact ⟨⟨hp0, hpz.trans (Nat.floor_le_floor hzw)⟩, hp⟩

lemma Vθ_of_no_prime {δ z : ℝ} (hδ : 0 ≤ δ) (hz : 0 ≤ z)
    (h : ∀ p : ℕ, p.Prime → z < p → (p : ℝ) ≤ (1 + δ) * z → False) : Vθ δ z = -(δ * z) := by
  have hzw : z ≤ (1 + δ) * z := by nlinarith
  rw [Vθ, theta_eq_of_no_prime hz hzw h]
  ring

/-- If `(x, (1+δ)x]` contains no Goldbach number and `y, x - y > 2`, then one of
`(y, (1+δ)y]` and `(x-y, (1+δ)(x-y)]` contains no prime. -/
lemma no_prime_of_no_goldbach {x δ y : ℝ} (hy : 2 < y) (hxy : 2 < x - y)
    (hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False) :
    (∀ p : ℕ, p.Prime → y < p → (p : ℝ) ≤ (1 + δ) * y → False) ∨
    (∀ q : ℕ, q.Prime → x - y < q → (q : ℝ) ≤ (1 + δ) * (x - y) → False) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩ := hcon
  have hpo : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso; subst h; norm_num at hp1; linarith
    · exact h
  have hqo : Odd q := by
    rcases hq.eq_two_or_odd' with h | h
    · exfalso; subst h; norm_num at hq1; linarith
    · exact h
  apply hNG (p + q) ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩
  · push_cast; linarith
  · push_cast; nlinarith

/-- The integrand `F(y) = V_θ(y)² ω(y)`. -/
noncomputable def Fint (x V δ y : ℝ) : ℝ := Vθ δ y ^ 2 * weight x V y

lemma weight_nonneg {x V : ℝ} (hV : 0 < V) (y : ℝ) : 0 ≤ weight x V y :=
  mul_nonneg (sq_nonneg _) (W_nonneg hV _)

lemma Fint_nonneg {x V δ : ℝ} (hV : 0 < V) (y : ℝ) : 0 ≤ Fint x V δ y :=
  mul_nonneg (sq_nonneg _) (weight_nonneg hV y)

lemma measurable_W (V : ℝ) : Measurable (W V) := by
  unfold W
  refine Measurable.ite (measurableSet_le measurable_abs measurable_const) ?_ measurable_const
  exact (continuous_kerProfile.comp (continuous_abs.div_const V)).measurable

lemma measurable_Fint (x V δ : ℝ) : Measurable (Fint x V δ) := by
  have hθ : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  unfold Fint Vθ weight
  have h1 : Measurable fun y : ℝ => Chebyshev.theta ((1 + δ) * y) :=
    hθ.comp (measurable_const.mul measurable_id)
  have h2 : Measurable fun y : ℝ => W V (log (x / y)) :=
    (measurable_W V).comp (Real.measurable_log.comp (measurable_const.div measurable_id))
  exact ((h1.sub hθ).sub (measurable_const.mul measurable_id)).pow_const 2 |>.mul
    (((measurable_const.div measurable_id).pow_const 2).mul h2)

/-- If `(z, (1+δ)z]` has no prime and `0 < z`, then `F(z) = δ² x² W_V(log(x/z))`. -/
lemma Fint_of_no_prime {x V δ z : ℝ} (hδ : 0 ≤ δ) (hz : 0 < z)
    (h : ∀ p : ℕ, p.Prime → z < p → (p : ℝ) ≤ (1 + δ) * z → False) :
    Fint x V δ z = δ ^ 2 * x ^ 2 * W V (log (x / z)) := by
  rw [Fint, Vθ_of_no_prime hδ hz.le h, weight]
  field_simp

/-- Pointwise cover inequality: for `x e^{-V} ≤ y ≤ x/2` (with `x e^{-V} > 2`),
`F(y) + F(x - y) ≥ δ² x² W_V(log(x/y))`. -/
lemma cover_pointwise {x V δ y : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 ≤ δ)
    (hy0 : 2 < x * exp (-V)) (hy1 : x * exp (-V) ≤ y) (hy2 : y ≤ x / 2)
    (hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False) :
    δ ^ 2 * x ^ 2 * W V (log (x / y)) ≤ Fint x V δ y + Fint x V δ (x - y) := by
  have hy : 0 < y := by linarith
  have hy2' : 2 < y := by linarith
  have hxy : 2 < x - y := by linarith
  -- `log(x/y) ≤ V`
  have hxe : exp V * (x * exp (-V)) = x := by
    rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
  have hlogy : log (x / y) ≤ V := by
    rw [log_le_iff_le_exp (by positivity), div_le_iff₀ hy]
    nlinarith [mul_le_mul_of_nonneg_left hy1 (exp_pos V).le]
  have hF0 := Fint_nonneg (x := x) (δ := δ) hV y
  have hF1 := Fint_nonneg (x := x) (δ := δ) hV (x - y)
  rcases no_prime_of_no_goldbach hy2' hxy hNG with h | h
  · rw [Fint_of_no_prime hδ hy h]; linarith
  · rw [Fint_of_no_prime hδ (by linarith) h]
    have hmono : W V (log (x / y)) ≤ W V (log (x / (x - y))) := by
      apply W_antitone hV
      · apply log_nonneg; rw [le_div_iff₀ (by linarith)]; linarith
      · apply log_le_log (by positivity)
        apply div_le_div_of_nonneg_left hx.le hy (by linarith)
      · exact hlogy
    have : 0 ≤ δ ^ 2 * x ^ 2 := by positivity
    nlinarith

/-- `∫_{y₀}^{x/2} log(x/y)² dy ≤ (x/2)(log² 2 + 2 log 2 + 2)`, through the antiderivative
`A(y) = y (ℓ² + 2ℓ + 2)` with `ℓ = log(x/y)`. -/
lemma integral_log_sq {x y0 : ℝ} (hy0 : 0 < y0) (hy0x : y0 ≤ x / 2) :
    ∫ y in y0..x / 2, (log x - log y) ^ 2 ≤
      x / 2 * ((log 2) ^ 2 + 2 * log 2 + 2) := by
  have hx : 0 < x := by linarith
  set A : ℝ → ℝ := fun y => y * ((log x - log y) ^ 2 + 2 * (log x - log y) + 2) with hA
  have hderiv : ∀ y ∈ uIcc y0 (x / 2), HasDerivAt A ((log x - log y) ^ 2) y := by
    intro y hy
    rw [uIcc_of_le hy0x] at hy
    have hy' : 0 < y := lt_of_lt_of_le hy0 hy.1
    have hl : HasDerivAt (fun y => log x - log y) (-y⁻¹) y := by
      simpa using (hasDerivAt_log hy'.ne').const_sub (log x)
    have := (hasDerivAt_id' y).mul (((hl.pow 2).add (hl.const_mul 2)).add_const 2)
    convert this using 1
    simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hlogc : ContinuousOn (fun y => log y) (uIcc y0 (x / 2)) := by
    apply continuousOn_log.mono
    intro y hy
    rw [uIcc_of_le hy0x] at hy
    exact (lt_of_lt_of_le hy0 hy.1).ne'
  have hcont : ContinuousOn (fun y => (log x - log y) ^ 2) (uIcc y0 (x / 2)) :=
    (continuousOn_const.sub hlogc).pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have hAy0 : 0 ≤ A y0 := by
    simp only [hA]
    apply mul_nonneg hy0.le
    nlinarith [sq_nonneg (log x - log y0 + 1)]
  have hAx : A (x / 2) = x / 2 * ((log 2) ^ 2 + 2 * log 2 + 2) := by
    simp only [hA]
    rw [log_div hx.ne' (by norm_num)]
    ring
  linarith

/-- The numerical constant: `π² (log² 2 + 2 log 2 + 2) / 4 ≤ 9.55`. -/
lemma const_955 : π ^ 2 * ((log 2) ^ 2 + 2 * log 2 + 2) / 4 ≤ 9.55 := by
  have hp := pi_lt_d6
  have hp0 := pi_pos
  have hl := log_two_lt_d9
  have hl0 : 0 < log 2 := log_pos (by norm_num)
  have h1 : π ^ 2 ≤ 3.141593 ^ 2 := by nlinarith
  have h2 : (log 2) ^ 2 + 2 * log 2 + 2 ≤ 0.6931471808 ^ 2 + 2 * 0.6931471808 + 2 := by nlinarith
  have h3 : 0 ≤ (log 2) ^ 2 + 2 * log 2 + 2 := by positivity
  calc π ^ 2 * ((log 2) ^ 2 + 2 * log 2 + 2) / 4
      ≤ 3.141593 ^ 2 * (0.6931471808 ^ 2 + 2 * 0.6931471808 + 2) / 4 := by gcongr
    _ ≤ 9.55 := by norm_num

/-- **Cover lemma.** If `(x, (1+δ)x]` contains no Goldbach number, then
`δ² x³ (1/2 - 9.55/V² - e^{-V}) ≤ ∫_{y>0} V_θ(y)² ω(y) dy`. -/
theorem cover_lower_bound {x V δ : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 ≤ δ)
    (hy0 : 2 < x * exp (-V)) (hy0' : x * exp (-V) ≤ x / 2)
    (hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False) :
    ENNReal.ofReal (δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
      ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Fint x V δ y) := by
  set y0 := x * exp (-V) with hy0def
  have hy0pos : 0 < y0 := by linarith
  set c := π ^ 2 / (2 * V ^ 2) with hc
  set g : ℝ → ℝ := fun y => δ ^ 2 * x ^ 2 * (1 - c * (log x - log y) ^ 2) with hg
  set F := Fint x V δ with hF
  -- Step 1: restrict to `Ioc y0 (x/2) ∪ Ioo (x/2) (x - y0)`.
  have hsub : Ioc y0 (x / 2) ∪ Ioo (x / 2) (x - y0) ⊆ Ioi 0 := by
    intro y hy
    rcases hy with hy | hy <;> simp only [mem_Ioi] <;> linarith [hy.1]
  have hdisj : Disjoint (Ioc y0 (x / 2)) (Ioo (x / 2) (x - y0)) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    linarith [h1.2, h2.1]
  have step1 : (∫⁻ y in Ioc y0 (x / 2), ENNReal.ofReal (F y)) +
      ∫⁻ y in Ioo (x / 2) (x - y0), ENNReal.ofReal (F y)
      ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (F y) := by
    rw [← lintegral_union measurableSet_Ioo hdisj]
    exact lintegral_mono_set hsub
  -- Step 2: reflect the second piece.
  have step2 : ∫⁻ y in Ioo (x / 2) (x - y0), ENNReal.ofReal (F y)
      = ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F (x - y)) := by
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
    rw [← lintegral_sub_left_eq_self
      ((Ioo (x / 2) (x - y0)).indicator fun y => ENNReal.ofReal (F y)) x]
    congr 1
    ext y
    simp only [Set.indicator_apply, mem_Ioo]
    by_cases h : y0 < y ∧ y < x / 2
    · have h' : x / 2 < x - y ∧ x - y < x - y0 := ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    · have h' : ¬(x / 2 < x - y ∧ x - y < x - y0) := by
        rintro ⟨h1, h2⟩
        exact h ⟨by linarith, by linarith⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]
  -- Step 3: shrink the first piece to `Ioo` and combine.
  have step3 : ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F y)
      ≤ ∫⁻ y in Ioc y0 (x / 2), ENNReal.ofReal (F y) :=
    lintegral_mono_set Ioo_subset_Ioc_self
  have hFm : Measurable fun y => ENNReal.ofReal (F y) :=
    ENNReal.measurable_ofReal.comp (measurable_Fint x V δ)
  have step4 : ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (max (g y) 0)
      ≤ ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F y) + ENNReal.ofReal (F (x - y)) := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro y hy
    rw [← ENNReal.ofReal_add (Fint_nonneg hV y) (Fint_nonneg hV (x - y))]
    apply ENNReal.ofReal_le_ofReal
    have hyp : 0 < y := lt_trans hy0pos hy.1
    have hpt := cover_pointwise hx hV hδ hy0 hy.1.le hy.2.le hNG
    have hlogxy : log (x / y) = log x - log y := log_div hx.ne' hyp.ne'
    have hv0 : 0 ≤ log (x / y) := by
      apply log_nonneg; rw [le_div_iff₀ hyp]; linarith [hy.2]
    have hv1 : log (x / y) ≤ V := by
      rw [log_le_iff_le_exp (by positivity), div_le_iff₀ hyp]
      have hxe : exp V * (x * exp (-V)) = x := by
        rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      nlinarith [mul_lt_mul_of_pos_left hy.1 (exp_pos V)]
    have hK1 := W_K1 hV hv0 hv1
    rw [hlogxy] at hK1 hpt
    have hsum : 0 ≤ F y + F (x - y) := add_nonneg (Fint_nonneg hV y) (Fint_nonneg hV (x - y))
    apply max_le _ hsum
    simp only [hg]
    have : 0 ≤ δ ^ 2 * x ^ 2 := by positivity
    calc δ ^ 2 * x ^ 2 * (1 - c * (log x - log y) ^ 2)
        ≤ δ ^ 2 * x ^ 2 * W V (log x - log y) := by
          apply mul_le_mul_of_nonneg_left _ this
          simpa [hc, mul_comm] using hK1
      _ ≤ F y + F (x - y) := hpt
  -- Step 5: the Bochner integral of `g`.
  have hlogc' : ContinuousOn (fun y => log y) (Icc y0 (x / 2)) :=
    continuousOn_log.mono fun y hy => (lt_of_lt_of_le hy0pos hy.1).ne'
  have hgcont : ContinuousOn g (Icc y0 (x / 2)) :=
    continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_const.mul ((continuousOn_const.sub hlogc').pow 2)))
  have hgint : IntegrableOn g (Ioo y0 (x / 2)) :=
    (hgcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hmaxint : IntegrableOn (fun y => max (g y) 0) (Ioo y0 (x / 2)) :=
    hgint.sup (integrableOn_const (by simp))
  have step5 : ENNReal.ofReal (∫ y in Ioo y0 (x / 2), g y)
      ≤ ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (max (g y) 0) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmaxint
      (Filter.Eventually.of_forall fun y => le_max_right _ _)]
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono hgint hmaxint (fun y => le_max_left _ _)
  -- Step 6: evaluate the integral of `g`.
  have hint_eq : ∫ y in Ioo y0 (x / 2), g y = ∫ y in y0..x / 2, g y := by
    rw [intervalIntegral.integral_of_le hy0', integral_Ioc_eq_integral_Ioo]
  have hlogint := integral_log_sq hy0pos hy0'
  have hcont2 : ContinuousOn (fun y => (log x - log y) ^ 2) (uIcc y0 (x / 2)) := by
    rw [uIcc_of_le hy0']
    exact (continuousOn_const.sub hlogc').pow 2
  have hgval : ∫ y in y0..x / 2, g y =
      δ ^ 2 * x ^ 2 * ((x / 2 - y0) - c * ∫ y in y0..x / 2, (log x - log y) ^ 2) := by
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const ((hcont2.intervalIntegrable).const_mul c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp
  have hbound : δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) ≤ ∫ y in y0..x / 2, g y := by
    rw [hgval]
    have hc0 : 0 ≤ c := by positivity
    have h955 := const_955
    have hδx : 0 ≤ δ ^ 2 * x ^ 2 := by positivity
    have key : x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) ≤
        (x / 2 - y0) - c * ∫ y in y0..x / 2, (log x - log y) ^ 2 := by
      have h1 : c * ∫ y in y0..x / 2, (log x - log y) ^ 2 ≤
          c * (x / 2 * ((log 2) ^ 2 + 2 * log 2 + 2)) := mul_le_mul_of_nonneg_left hlogint hc0
      have h2 : c * (x / 2 * ((log 2) ^ 2 + 2 * log 2 + 2)) ≤ x * (9.55 / V ^ 2) := by
        simp only [hc]
        rw [show π ^ 2 / (2 * V ^ 2) * (x / 2 * ((log 2) ^ 2 + 2 * log 2 + 2))
            = x * (π ^ 2 * ((log 2) ^ 2 + 2 * log 2 + 2) / 4) / V ^ 2 by field_simp; ring]
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hx.le
        exact div_le_div_of_nonneg_right h955 (by positivity)
      have h3 : x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) = x / 2 - y0 - x * (9.55 / V ^ 2) := by
        rw [hy0def]; ring
      linarith
    calc δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V))
        = δ ^ 2 * x ^ 2 * (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key hδx
  -- Assemble.
  have hadd : ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F y) + ENNReal.ofReal (F (x - y))
      = (∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F y)) +
        ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (F (x - y)) :=
    lintegral_add_left hFm _
  calc ENNReal.ofReal (δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
      ≤ ENNReal.ofReal (∫ y in Ioo y0 (x / 2), g y) := by
        apply ENNReal.ofReal_le_ofReal; rw [hint_eq]; exact hbound
    _ ≤ ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (max (g y) 0) := step5
    _ ≤ _ := step4
    _ = _ := hadd
    _ ≤ (∫⁻ y in Ioc y0 (x / 2), ENNReal.ofReal (F y)) +
        ∫⁻ y in Ioo (x / 2) (x - y0), ENNReal.ofReal (F y) := by
        rw [step2]; gcongr
    _ ≤ _ := step1

end GoldbachRH
