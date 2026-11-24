import GoldbachRH.Assembly
import GoldbachRH.Lemma7
import GoldbachRH.PrimePowers
import GoldbachRH.CoverFM4

/-!
# Main theorems (version 0.6)

Assume RH. Let `r = 4.0462…` be the solution of `r + log² r = 6`; since `x + log² x` is
increasing, `x ≥ r` is the same as `x + log² x ≥ 6`.

* `goldbach_log_sq_main`: for every real `x ≥ 4` with `x + log² x ≥ 6`, the interval
  `(x, x + log² x]` contains a Goldbach number.
* `no_goldbach_below_cutoff` (unconditional): for `4 ≤ x` with `x + log² x < 6`, it contains none.
* `goldbach_Cstar_main`: for every `x ≥ 4`, `(x, x + C_* log² x]` contains a Goldbach number,
  where `C_* = 2 / log² 4 = 1.0406…`.
* `Cstar_optimal` (unconditional): no smaller constant works at `x = 4`.
* `goldbach_two_log_sq_main`: the result of version 0.5 (`(x, x + 2 log² x]`), as a corollary.

Hypotheses of the `_main` forms:
  - cited results: RH, Schoenfeld's bound for `θ` under RH (`SchoenfeldTheta`), the explicit
    formula for ψ (`ExplicitFormulaPsi`) and the verification of Oliveira e Silva, Herzog and
    Pardi (`GoldbachVerifiedUpTo (4·10¹⁸)`);
  - one result of the paper not yet formalized: the `𝒯` row of Proposition 13 (`Prop13T`).
Lemma 6 (the first-moment cover, `cover_lower_bound_fm`), Lemmas 7 and 8, the `ℰ` row of
Proposition 13 and the range argument are proved.
-/

open Real MeasureTheory

namespace GoldbachRH

/-- Below `3.9·10¹⁸`: if `2 ≤ h` then `(x, x + h]` contains an even number `n` with
`4 < n ≤ 4·10¹⁸`, hence a Goldbach number. -/
lemma small_range_gen (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) {x h : ℝ} (hx : 4 ≤ x)
    (hx' : x < 3.9e18) (hh : 2 ≤ h) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h := by
  have hx0 : 0 ≤ x / 2 := by linarith
  set m := ⌊x / 2⌋₊ with hm
  have hm1 : (m : ℝ) ≤ x / 2 := Nat.floor_le hx0
  have hm2 : x / 2 < m + 1 := Nat.lt_floor_add_one _
  have hm3 : 2 ≤ m := by
    rw [hm]; exact Nat.le_floor (by norm_num; linarith)
  refine ⟨2 * (m + 1), hOHP _ (even_two_mul _) (by omega) ?_, ?_, ?_⟩
  · have : ((2 * (m + 1) : ℕ) : ℝ) ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this
  · push_cast; linarith
  · push_cast; linarith

lemma six_isGoldbach (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) : IsGoldbachNumber 6 :=
  hOHP 6 (by decide) (by norm_num) (by norm_num)

/-- `e^{3/2} ≤ 6`. -/
lemma exp_three_halves_le : exp (1.5 : ℝ) ≤ 6 := by
  have h : exp (1.5 : ℝ) ^ 2 = exp 1 ^ 3 := by
    rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
  have he := exp_one_lt_d9
  have h3 : exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (exp_pos 1).le he.le 3
  have h36 : exp (1.5 : ℝ) ^ 2 ≤ 36 := by rw [h]; norm_num at h3 ⊢; linarith
  have hpos := exp_pos (1.5 : ℝ)
  nlinarith

/-- `log² x ≥ 2` for `x ≥ 6`. -/
lemma two_le_log_sq {x : ℝ} (hx : 6 ≤ x) : 2 ≤ log x ^ 2 := by
  have h : 1.5 ≤ log x := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_three_halves_le]
  nlinarith

/-- Below `3.9·10¹⁸`, coefficient `1`, for `x + log² x ≥ 6`. -/
lemma small_range_one (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) {x : ℝ} (hx : 4 ≤ x)
    (h6 : 6 ≤ x + log x ^ 2) (hx' : x < 3.9e18) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + log x ^ 2 := by
  by_cases hx6 : x < 6
  · exact ⟨6, six_isGoldbach hOHP, by push_cast; linarith, by push_cast; linarith⟩
  · push Not at hx6
    exact small_range_gen hOHP hx hx' (two_le_log_sq hx6)

/-- **Main theorem, coefficient 1** (from the single analytic hypothesis
`RiemannHypothesis → WeightedMeanSquareBound`). Assume RH, Schoenfeld's bound and the
verification up to `4·10¹⁸`. For every real `x ≥ 4` with `x + log² x ≥ 6`, the interval
`(x, x + log² x]` contains a Goldbach number. -/
theorem goldbach_log_sq (hRH : RiemannHypothesis) (hSch : RiemannHypothesis → SchoenfeldTheta)
    (hWMS : RiemannHypothesis → WeightedMeanSquareBound)
    (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) :
    ∀ x : ℝ, 4 ≤ x → 6 ≤ x + log x ^ 2 →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + log x ^ 2 := by
  intro x hx h6
  by_cases hsmall : x < 3.9e18
  · exact small_range_one hOHP hx h6 hsmall
  push Not at hsmall
  by_contra hcon
  push Not at hcon
  have hx0 : 0 < x := by linarith
  set L := log x with hLdef
  have hL : (42.8 : ℝ) ≤ L := by
    rw [hLdef, le_log_iff_exp_le hx0]; exact exp_42_8_le.trans hsmall
  have hL0 : 0 < L := by linarith
  set V := Vp L with hVdef
  set δ := L ^ 2 / x with hδdef
  have hV : 0 < V := by linarith [Vp_ge hL]
  have hδ : 0 < δ := by positivity
  have hδx : δ * x = L ^ 2 := by rw [hδdef]; field_simp
  have hδdl : δ = dl L := by rw [hδdef, hLdef, dl_log hx0]
  have hδ1 : δ ≤ 1 := by rw [hδdl]; linarith [dl_le hL]
  -- `x e^{-V} = e^{u}` with `u ≥ 23.15`
  have hxe : x * exp (-V) = exp (uL L) := by
    rw [uL, ← hVdef, sub_eq_add_neg, exp_add, hLdef, exp_log hx0]
  have hy0 : 599 ≤ x * exp (-V) := by
    rw [hxe]
    have hu := uL_ge hL
    have h3 := pow_div_factorial_le_exp (uL L) (by linarith) 3
    norm_num [Nat.factorial] at h3
    have hu3 : (23.15 : ℝ) ^ 3 ≤ uL L ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    norm_num at hu3
    linarith
  have hy0' : x * exp (-V) ≤ x / 2 := by
    have h1 : exp (-V) ≤ exp (-1) := exp_le_exp.2 (by linarith [Vp_ge hL])
    have h2 : exp (-1) ≤ 1 / 2 := by
      rw [exp_neg, inv_le_comm₀ (exp_pos 1) (by norm_num)]
      linarith [exp_one_gt_d9]
    nlinarith
  -- no Goldbach number in `(x, (1+δ)x]`
  have hNG : ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ (1 + δ) * x → False := by
    intro n hn h1 h2
    have := hcon n hn h1
    have e : (1 + δ) * x = x + log x ^ 2 := by rw [add_mul, one_mul, hδx]
    linarith
  have hlow := cover_lower_bound_fm hx0 hV hδ hδ1 hy0 hy0' (hSch hRH) hNG
  have hup := hWMS hRH x hsmall
  set S := √(Tb L) + √(Eb L) + √(Bb L) with hS
  have hRHS0 : 0 ≤ log x ^ 2 / x * x ^ 2 * S ^ 2 := by positivity
  have hcomb : δ ^ 2 * x ^ 3 * (2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) - 2 * δ
      - L ^ 2 / (2 * π * √x)) ≤ δ * x ^ 2 * S ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff hRHS0).1 (hlow.trans hup)
  -- `√x = e^{L/2}`
  have hsx : √x = exp (L / 2) := by
    rw [exp_half, hLdef, exp_log hx0]
  have hrange := range_inequality hL
  rw [← hVdef, ← hS, ← hδdl, ← hsx] at hrange
  have hpos : 0 < δ * x ^ 2 := by positivity
  have : δ * x ^ 2 * (L ^ 2 * (2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) - 2 * δ
      - L ^ 2 / (2 * π * √x))) ≤ δ * x ^ 2 * S ^ 2 := by
    calc δ * x ^ 2 * (L ^ 2 * (2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) - 2 * δ
          - L ^ 2 / (2 * π * √x)))
        = δ ^ 2 * x ^ 3 * (2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) - 2 * δ
          - L ^ 2 / (2 * π * √x)) := by rw [← hδx]; ring
      _ ≤ _ := hcomb
  have := le_of_mul_le_mul_left this hpos
  linarith

/-- **Main theorem, coefficient 1, with the analytic part split into its pieces.** -/
theorem goldbach_log_sq_of_lemmas (hRH : RiemannHypothesis)
    (hSch : RiemannHypothesis → SchoenfeldTheta)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (h7 : Lemma7) (h13 : Prop13T) (hPP : PrimePowerBound) :
    ∀ x : ℝ, 4 ≤ x → 6 ≤ x + log x ^ 2 →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + log x ^ 2 :=
  goldbach_log_sq hRH hSch (fun h => wms_of_lemmas h7 h13 hPP h hEF) hOHP

/-- **Main theorem (version 0.6), current form.** Assume RH, Schoenfeld's bound for `θ` under
RH, the explicit formula for ψ, the verification up to `4·10¹⁸`, and the `𝒯` row of
Proposition 13. For every real `x ≥ 4` with `x + log² x ≥ 6` (that is, `x ≥ r = 4.0462…`),
the interval `(x, x + log² x]` contains a Goldbach number. -/
theorem goldbach_log_sq_main (hRH : RiemannHypothesis)
    (hSch : RiemannHypothesis → SchoenfeldTheta)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (h13 : Prop13T) :
    ∀ x : ℝ, 4 ≤ x → 6 ≤ x + log x ^ 2 →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + log x ^ 2 :=
  goldbach_log_sq_of_lemmas hRH hSch hEF hOHP lemma7 h13 primePowerBound

/-- A Goldbach number in `(4, 6)` does not exist. -/
lemma no_goldbach_between_four_and_six {n : ℕ} (hn : IsGoldbachNumber n) (h4 : (4 : ℝ) < n)
    (h6 : (n : ℝ) < 6) : False := by
  have h4' : 4 < n := by exact_mod_cast h4
  have h6' : n < 6 := by exact_mod_cast h6
  have h5 : n = 5 := by omega
  rw [h5] at hn
  exact absurd hn.1 (by decide)

/-- **The cutoff is sharp** (unconditional). If `4 ≤ x` and `x + log² x < 6`, then
`(x, x + log² x]` contains no Goldbach number. -/
theorem no_goldbach_below_cutoff {x : ℝ} (hx : 4 ≤ x) (h6 : x + log x ^ 2 < 6) :
    ∀ n : ℕ, IsGoldbachNumber n → x < n → (n : ℝ) ≤ x + log x ^ 2 → False :=
  fun _ hn h1 h2 => no_goldbach_between_four_and_six hn (by linarith) (by linarith)

/-- `log² 4 ≤ 2`, so `C_* = 2 / log² 4 ≥ 1`. -/
lemma log_four_sq_le_two : log 4 ^ 2 ≤ 2 := by
  have h : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  rw [h]
  have := log_two_lt_d9
  have := log_two_gt_d9
  nlinarith

lemma log_four_pos : 0 < log (4 : ℝ) := log_pos (by norm_num)

/-- **The optimal constant on `x ≥ 4`.** Assume the hypotheses of `goldbach_log_sq_main`.
For every `x ≥ 4`, `(x, x + C_* log² x]` contains a Goldbach number, `C_* = 2 / log² 4`. -/
theorem goldbach_Cstar_main (hRH : RiemannHypothesis)
    (hSch : RiemannHypothesis → SchoenfeldTheta)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (h13 : Prop13T) :
    ∀ x : ℝ, 4 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) ≤ x + 2 / log 4 ^ 2 * log x ^ 2 := by
  intro x hx
  have hl4 := log_four_pos
  have hC : 1 ≤ 2 / log 4 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith [log_four_sq_le_two]
  have hlx : log 4 ≤ log x := log_le_log (by norm_num) hx
  by_cases h6 : 6 ≤ x + log x ^ 2
  · obtain ⟨n, hn, h1, h2⟩ := goldbach_log_sq_main hRH hSch hEF hOHP h13 x hx h6
    refine ⟨n, hn, h1, h2.trans ?_⟩
    have := mul_le_mul_of_nonneg_right hC (sq_nonneg (log x))
    linarith
  · push Not at h6
    refine ⟨6, six_isGoldbach hOHP, by push_cast; nlinarith [sq_nonneg (log x)], ?_⟩
    -- `C_* log² x ≥ C_* log² 4 = 2`
    have h2 : 2 / log 4 ^ 2 * log 4 ^ 2 ≤ 2 / log 4 ^ 2 * log x ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl4.le hlx 2) (by positivity)
    have e : 2 / log 4 ^ 2 * log 4 ^ 2 = 2 := by field_simp
    push_cast
    linarith

/-- **`C_*` is optimal** (unconditional): for `c < C_*`, `(4, 4 + c log² 4]` contains no
Goldbach number. -/
theorem Cstar_optimal {c : ℝ} (hc : c < 2 / log 4 ^ 2) :
    ∀ n : ℕ, IsGoldbachNumber n → (4 : ℝ) < n → (n : ℝ) ≤ 4 + c * log 4 ^ 2 → False := by
  intro n hn h1 h2
  have hl4 := log_four_pos
  have : c * log 4 ^ 2 < 2 := by
    have := mul_lt_mul_of_pos_right hc (by positivity : (0 : ℝ) < log 4 ^ 2)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  exact no_goldbach_between_four_and_six hn h1 (by linarith)

/-- **The result of version 0.5**, as a corollary: `(x, x + 2 log² x]` for every `x ≥ 4`. -/
theorem goldbach_two_log_sq_main (hRH : RiemannHypothesis)
    (hSch : RiemannHypothesis → SchoenfeldTheta)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (h13 : Prop13T) :
    ∀ x : ℝ, 4 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 2 * log x ^ 2 := by
  intro x hx
  obtain ⟨n, hn, h1, h2⟩ := goldbach_Cstar_main hRH hSch hEF hOHP h13 x hx
  refine ⟨n, hn, h1, h2.trans ?_⟩
  have hl4 := log_four_pos
  have h1' : 1 ≤ log 4 := by
    rw [le_log_iff_exp_le (by norm_num)]; linarith [exp_one_lt_d9]
  have hC : 2 / log 4 ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have := mul_le_mul_of_nonneg_right hC (sq_nonneg (log x))
  linarith

end GoldbachRH
