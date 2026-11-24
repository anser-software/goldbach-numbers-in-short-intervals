import GoldbachRH.CoverFM3

/-!
# The first-moment cover, part 4: assembly (Lemma 6 of the paper, version 0.6)

**Theorem** (`cover_lower_bound_fm`). Assume Schoenfeld's bound for `θ`. If `0 < δ ≤ 1`,
`599 ≤ x e^{-V} ≤ x/2` and `(x, (1+δ)x]` contains no Goldbach number, then
`δ² x³ (2m - 2δ - log² x/(2π√x)) ≤ ∫_{y>0} V_θ(y)² ω(y) dy`, with `m = 1/2 - 9.55/V² - e^{-V}`.
-/

open Real Set MeasureTheory

namespace GoldbachRH

/-- The reflection `y ↦ x - y` preserves Lebesgue measure on `(0, x)`. -/
lemma lintegral_Ioo_reflect (x : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y in Ioo 0 x, f (x - y) = ∫⁻ y in Ioo 0 x, f y := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  rw [← lintegral_sub_left_eq_self ((Ioo 0 x).indicator f) x]
  congr 1
  ext y
  simp only [Set.indicator_apply, mem_Ioo]
  by_cases h : 0 < y ∧ y < x
  · have h' : 0 < x - y ∧ x - y < x := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
  · have h' : ¬(0 < x - y ∧ x - y < x) := by
      rintro ⟨h1, h2⟩
      exact h ⟨by linarith, by linarith⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]

/-- The pointwise pair inequality: if `ab = 0` then `2qa + 2qb ≤ q(a-1)² + q(b-1)² + 2q`. -/
lemma pair_pointwise {q a b : ℝ} (hq : 0 ≤ q) (hab : a = 0 ∨ b = 0) :
    2 * (q * a) + 2 * (q * b) ≤ q * (a - 1) ^ 2 + q * (b - 1) ^ 2 + 2 * q := by
  rcases hab with h | h <;> subst h
  · nlinarith [mul_nonneg hq (sq_nonneg (b - 2))]
  · nlinarith [mul_nonneg hq (sq_nonneg (a - 2))]

/-- **The pair step.** `2 ∫ q G ≤ ∫ q (G-1)² + ∫ q` on `(0, x)`. -/
lemma pair_integral {x V δ : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 < δ)
    (hy0 : 2 < x * exp (-V))
    (hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False) :
    (∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y))
        + ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y)
      ≤ (∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * (Gfun δ y - 1) ^ 2))
        + ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y) := by
  set M : ℝ → ENNReal := fun y => ENNReal.ofReal (qfun x V y * Gfun δ y) with hM
  set P : ℝ → ENNReal := fun y => ENNReal.ofReal (qfun x V y * (Gfun δ y - 1) ^ 2) with hP
  set Q : ℝ → ENNReal := fun y => ENNReal.ofReal (qfun x V y) with hQ
  have hqm := measurable_qfun x V
  have hGm := measurable_Gfun δ
  have hMm : Measurable M := (hqm.mul hGm).ennreal_ofReal
  have hPm : Measurable P := (hqm.mul ((hGm.sub measurable_const).pow_const 2)).ennreal_ofReal
  have hQm : Measurable Q := hqm.ennreal_ofReal
  have hr : Measurable fun y : ℝ => x - y := measurable_const.sub measurable_id
  have hMr' : Measurable fun y => M (x - y) := hMm.comp hr
  have hPr' : Measurable fun y => P (x - y) := hPm.comp hr
  have hMM : Measurable fun y => M y + M y := hMm.add hMm
  have hPP : Measurable fun y => P y + P (x - y) := hPm.add hPr'
  -- pointwise inequality on `(0, x)`
  have hpt : ∀ y ∈ Ioo 0 x, (M y + M y) + (M (x - y) + M (x - y))
      ≤ (P y + P (x - y)) + (Q y + Q y) := by
    intro y hy
    have hq0 := qfun_nonneg (x := x) hV y
    have hqs : qfun x V (x - y) = qfun x V y := qfun_symm x V y
    have ha := Gfun_nonneg hδ hy.1
    have hb := Gfun_nonneg hδ (by linarith [hy.2] : 0 < x - y)
    have hreal : 2 * (qfun x V y * Gfun δ y) + 2 * (qfun x V y * Gfun δ (x - y))
        ≤ qfun x V y * (Gfun δ y - 1) ^ 2 + qfun x V y * (Gfun δ (x - y) - 1) ^ 2
          + 2 * qfun x V y := by
      rcases hq0.lt_or_eq with hpos | hzero
      · apply pair_pointwise hq0
        have hgt := gt_of_qfun_pos hx hV hy.1 hy.2 hpos
        rcases no_prime_of_no_goldbach (by linarith [hgt.1]) (by linarith [hgt.2]) hNG with h | h
        · exact Or.inl (Gfun_of_no_prime hδ hy.1 h)
        · exact Or.inr (Gfun_of_no_prime hδ (by linarith [hy.2]) h)
      · rw [← hzero]; simp
    simp only [hM, hP, hQ, hqs]
    have e1 : 0 ≤ qfun x V y * Gfun δ y := mul_nonneg hq0 ha
    have e2 : 0 ≤ qfun x V y * Gfun δ (x - y) := mul_nonneg hq0 hb
    have e3 : 0 ≤ qfun x V y * (Gfun δ y - 1) ^ 2 := mul_nonneg hq0 (sq_nonneg _)
    have e4 : 0 ≤ qfun x V y * (Gfun δ (x - y) - 1) ^ 2 := mul_nonneg hq0 (sq_nonneg _)
    rw [← ENNReal.ofReal_add e1 e1, ← ENNReal.ofReal_add e2 e2,
      ← ENNReal.ofReal_add (add_nonneg e1 e1) (add_nonneg e2 e2),
      ← ENNReal.ofReal_add e3 e4, ← ENNReal.ofReal_add hq0 hq0,
      ← ENNReal.ofReal_add (add_nonneg e3 e4) (add_nonneg hq0 hq0)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  -- integrate, and use the reflection
  have hint := setLIntegral_mono' (μ := volume) measurableSet_Ioo hpt
  have hMr : ∫⁻ y in Ioo 0 x, M (x - y) = ∫⁻ y in Ioo 0 x, M y := lintegral_Ioo_reflect x M
  have hPr : ∫⁻ y in Ioo 0 x, P (x - y) = ∫⁻ y in Ioo 0 x, P y := lintegral_Ioo_reflect x P
  rw [lintegral_add_left hMM, lintegral_add_left hMm, lintegral_add_left hMr',
    lintegral_add_left hPP, lintegral_add_left hPm, lintegral_add_left hQm, hMr, hPr] at hint
  have h2 : 2 * ((∫⁻ y in Ioo 0 x, M y) + ∫⁻ y in Ioo 0 x, M y)
      ≤ 2 * ((∫⁻ y in Ioo 0 x, P y) + ∫⁻ y in Ioo 0 x, Q y) := by
    calc 2 * ((∫⁻ y in Ioo 0 x, M y) + ∫⁻ y in Ioo 0 x, M y)
        = ((∫⁻ y in Ioo 0 x, M y) + ∫⁻ y in Ioo 0 x, M y)
          + ((∫⁻ y in Ioo 0 x, M y) + ∫⁻ y in Ioo 0 x, M y) := two_mul _
      _ ≤ ((∫⁻ y in Ioo 0 x, P y) + ∫⁻ y in Ioo 0 x, P y)
          + ((∫⁻ y in Ioo 0 x, Q y) + ∫⁻ y in Ioo 0 x, Q y) := hint
      _ = 2 * ((∫⁻ y in Ioo 0 x, P y) + ∫⁻ y in Ioo 0 x, Q y) := by ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h2

/-- `∫_{(y₀, x/2)} w ≥ x (1/2 - 9.55/V² - e^{-V})`, from (K1). -/
lemma integral_w_lower {x V : ℝ} (hx : 0 < x) (hV : 0 < V) (hy0pos : 0 < x * exp (-V))
    (hy0' : x * exp (-V) ≤ x / 2) :
    ENNReal.ofReal (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
      ≤ ∫⁻ y in Ioo (x * exp (-V)) (x / 2), ENNReal.ofReal (wfun x V y) := by
  set y0 := x * exp (-V) with hy0def
  set c := π ^ 2 / (2 * V ^ 2) with hc
  set g : ℝ → ℝ := fun y => 1 - c * (log x - log y) ^ 2 with hg
  have hpt : ∀ y ∈ Ioo y0 (x / 2),
      ENNReal.ofReal (max (g y) 0) ≤ ENNReal.ofReal (wfun x V y) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    have hyp : 0 < y := hy0pos.trans hy.1
    have hlogxy : log (x / y) = log x - log y := log_div hx.ne' hyp.ne'
    have hv0 : 0 ≤ log (x / y) := by
      apply log_nonneg; rw [le_div_iff₀ hyp]; linarith [hy.2]
    have hv1 : log (x / y) ≤ V := by
      rw [log_le_iff_le_exp (by positivity), div_le_iff₀ hyp]
      have hxe : exp V * (x * exp (-V)) = x := by
        rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      nlinarith [mul_lt_mul_of_pos_left hy.1 (exp_pos V)]
    have hK1 := W_K1 hV hv0 hv1
    rw [hlogxy] at hK1
    apply max_le _ (wfun_nonneg hV y)
    simp only [hg, wfun, hlogxy]
    simpa [hc, mul_comm] using hK1
  have hlogc' : ContinuousOn (fun y => log y) (Icc y0 (x / 2)) :=
    continuousOn_log.mono fun y hy => (lt_of_lt_of_le hy0pos hy.1).ne'
  have hgcont : ContinuousOn g (Icc y0 (x / 2)) :=
    continuousOn_const.sub (continuousOn_const.mul ((continuousOn_const.sub hlogc').pow 2))
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
  have hint_eq : ∫ y in Ioo y0 (x / 2), g y = ∫ y in y0..x / 2, g y := by
    rw [intervalIntegral.integral_of_le hy0', integral_Ioc_eq_integral_Ioo]
  have hlogint := integral_log_sq hy0pos hy0'
  have hcont2 : ContinuousOn (fun y => (log x - log y) ^ 2) (uIcc y0 (x / 2)) := by
    rw [uIcc_of_le hy0']
    exact (continuousOn_const.sub hlogc').pow 2
  have hgval : ∫ y in y0..x / 2, g y =
      (x / 2 - y0) - c * ∫ y in y0..x / 2, (log x - log y) ^ 2 := by
    simp only [hg]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((hcont2.intervalIntegrable).const_mul c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp
  have key : x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) ≤ ∫ y in y0..x / 2, g y := by
    rw [hgval]
    have hc0 : 0 ≤ c := by positivity
    have h955 := const_955
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
  calc ENNReal.ofReal (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
      ≤ ENNReal.ofReal (∫ y in Ioo y0 (x / 2), g y) := by
        apply ENNReal.ofReal_le_ofReal; rw [hint_eq]; exact key
    _ ≤ ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (max (g y) 0) := step5
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hpt

/-- `∫_{(0,x)} q ≥ 2 ∫_{(y₀, x/2)} w`. -/
lemma integral_q_lower {x V : ℝ} (hx : 0 < x) (hV : 0 < V) (hy0pos : 0 < x * exp (-V))
    (hy0' : x * exp (-V) ≤ x / 2) :
    ENNReal.ofReal (2 * (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))))
      ≤ ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y) := by
  set y0 := x * exp (-V) with hy0def
  set Q₁ : ℝ → ENNReal := (Ioo y0 (x / 2)).indicator fun y => ENNReal.ofReal (qfun x V y)
    with hQ₁
  have hQ₁m : Measurable Q₁ := ((measurable_qfun x V).ennreal_ofReal).indicator measurableSet_Ioo
  -- pointwise `Q₁(y) + Q₁(x - y) ≤ Q(y)` on `(0, x)`
  have hpt : ∀ y ∈ Ioo 0 x, Q₁ y + Q₁ (x - y) ≤ ENNReal.ofReal (qfun x V y) := by
    intro y hy
    simp only [hQ₁, Set.indicator_apply, mem_Ioo]
    by_cases h1 : y0 < y ∧ y < x / 2
    · have h2 : ¬(y0 < x - y ∧ x - y < x / 2) := fun h => by linarith [h.2, h1.2]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
        add_zero]
    · by_cases h2 : y0 < x - y ∧ x - y < x / 2
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
          zero_add, qfun_symm]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
          add_zero]
        exact zero_le
  have hint := setLIntegral_mono' (μ := volume) measurableSet_Ioo hpt
  rw [lintegral_add_left hQ₁m, lintegral_Ioo_reflect x Q₁] at hint
  -- `∫_{(0,x)} Q₁ = ∫_{(y₀, x/2)} w`
  have hsub : Ioo y0 (x / 2) ⊆ Ioo 0 x := fun y hy => ⟨hy0pos.trans hy.1, by linarith [hy.2]⟩
  have hQ₁int : ∫⁻ y in Ioo 0 x, Q₁ y = ∫⁻ y in Ioo y0 (x / 2), ENNReal.ofReal (wfun x V y) := by
    rw [hQ₁, lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.2 hsub]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro y hy
    have hyp : 0 < y := hy0pos.trans hy.1
    have : qfun x V y = wfun x V y :=
      min_eq_left (wfun_mono hV hyp (by linarith [hy.2]) (by linarith [hy.2]))
    simp only [this]
  rw [hQ₁int] at hint
  have hw := integral_w_lower hx hV hy0pos hy0'
  calc ENNReal.ofReal (2 * (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))))
      = ENNReal.ofReal (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))
          + x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))) := by ring_nf
    _ ≤ ENNReal.ofReal (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
          + ENNReal.ofReal (x * (1 / 2 - 9.55 / V ^ 2 - exp (-V))) := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add hw hw
    _ ≤ _ := hint

/-- **The first-moment cover** (Lemma 6 of the paper, version 0.6). -/
theorem cover_lower_bound_fm {x V δ : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hy0 : 599 ≤ x * exp (-V)) (hy0' : x * exp (-V) ≤ x / 2)
    (hSch : SchoenfeldTheta)
    (hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False) :
    ENNReal.ofReal (δ ^ 2 * x ^ 3 * (2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) - 2 * δ
        - log x ^ 2 / (2 * π * √x)))
      ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Fint x V δ y) := by
  set m := 1 / 2 - 9.55 / V ^ 2 - exp (-V) with hm
  set c := δ * x + 2 * (√x * log x ^ 2 / (8 * π)) with hc
  have hc0 : 0 ≤ c := by positivity
  set P := ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * (Gfun δ y - 1) ^ 2) with hP
  set Q := ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y) with hQ
  set M := ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y) with hM
  have hpos : 0 < x * exp (-V) := by positivity
  have hfm : Q ≤ M + ENNReal.ofReal c := first_moment hx hV hδ hδ1 hy0 hSch
  have hpair : M + M ≤ P + Q := pair_integral hx hV hδ (by linarith) hNG
  have hQlow : ENNReal.ofReal (2 * (x * m)) ≤ Q := integral_q_lower hx hV hpos hy0'
  have hQfin : Q ≠ ⊤ := by
    have hle : Q ≤ volume (Ioo (0 : ℝ) x) := by
      calc Q ≤ ∫⁻ _ in Ioo (0 : ℝ) x, (1 : ENNReal) := by
            apply lintegral_mono
            intro y
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (qfun_le_one hV y)
        _ = volume (Ioo (0 : ℝ) x) := by rw [setLIntegral_const, one_mul]
    refine ne_top_of_le_ne_top ?_ hle
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hQP : Q ≤ P + ENNReal.ofReal (2 * c) := by
    have h1 : Q + Q ≤ (P + ENNReal.ofReal (2 * c)) + Q := by
      calc Q + Q ≤ (M + ENNReal.ofReal c) + (M + ENNReal.ofReal c) := add_le_add hfm hfm
        _ = (M + M) + (ENNReal.ofReal c + ENNReal.ofReal c) := by ring
        _ ≤ (P + Q) + (ENNReal.ofReal c + ENNReal.ofReal c) := add_le_add hpair le_rfl
        _ = (P + ENNReal.ofReal (2 * c)) + Q := by
            rw [two_mul c, ENNReal.ofReal_add hc0 hc0]
            ring
    exact (ENNReal.add_le_add_iff_right hQfin).1 h1
  have hsx : 0 < √x := sqrt_pos.2 hx
  have hxx : √x * √x = x := mul_self_sqrt hx.le
  have h3 : x * (log x ^ 2 / (2 * π * √x)) = 4 * (√x * log x ^ 2 / (8 * π)) := by
    calc x * (log x ^ 2 / (2 * π * √x)) = (√x * √x) * (log x ^ 2 / (2 * π * √x)) := by
          rw [hxx]
      _ = 4 * (√x * log x ^ 2 / (8 * π)) := by
          field_simp
          ring
  have hPlow : ENNReal.ofReal (x * (2 * m - 2 * δ - log x ^ 2 / (2 * π * √x))) ≤ P := by
    have e : x * (2 * m - 2 * δ - log x ^ 2 / (2 * π * √x)) = 2 * (x * m) - 2 * c := by
      rw [hc]
      linear_combination (-1 : ℝ) * h3
    rw [e, ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ 2 * c), tsub_le_iff_right]
    exact hQlow.trans hQP
  have hPm : Measurable fun y => ENNReal.ofReal (qfun x V y * (Gfun δ y - 1) ^ 2) :=
    ((measurable_qfun x V).mul (((measurable_Gfun δ).sub measurable_const).pow_const 2)).ennreal_ofReal
  have hsub : Ioo 0 x ⊆ Ioi (0 : ℝ) := fun y hy => hy.1
  have hd : (0 : ℝ) ≤ δ ^ 2 * x ^ 2 := by positivity
  calc ENNReal.ofReal (δ ^ 2 * x ^ 3 * (2 * m - 2 * δ - log x ^ 2 / (2 * π * √x)))
      = ENNReal.ofReal (δ ^ 2 * x ^ 2 * (x * (2 * m - 2 * δ - log x ^ 2 / (2 * π * √x)))) := by
        congr 1
        ring
    _ = ENNReal.ofReal (δ ^ 2 * x ^ 2)
          * ENNReal.ofReal (x * (2 * m - 2 * δ - log x ^ 2 / (2 * π * √x))) :=
        ENNReal.ofReal_mul hd
    _ ≤ ENNReal.ofReal (δ ^ 2 * x ^ 2) * P := by gcongr
    _ = ∫⁻ y in Ioo 0 x, ENNReal.ofReal (δ ^ 2 * x ^ 2)
          * ENNReal.ofReal (qfun x V y * (Gfun δ y - 1) ^ 2) := (lintegral_const_mul _ hPm).symm
    _ ≤ ∫⁻ y in Ioo 0 x, ENNReal.ofReal (Fint x V δ y) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro y hy
        rw [← ENNReal.ofReal_mul hd, Fint_eq_G hδ hy.1]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hd
        exact mul_le_mul_of_nonneg_right (qfun_le_wfun x V y) (sq_nonneg _)
    _ ≤ ∫⁻ y in Ioi 0, ENNReal.ofReal (Fint x V δ y) := lintegral_mono_set hsub

end GoldbachRH
