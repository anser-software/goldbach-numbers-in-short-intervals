import GoldbachRH.Assembly
import GoldbachRH.Lemma7
import GoldbachRH.PrimePowers

/-!
# Main theorem

Assume RH. For every real `x ≥ 4`, the interval `(x, x + 2 log² x]` contains a Goldbach number.

Two forms are proved.

* `goldbach_short_intervals_main` (the main result): as below, with Lemma 7 proved and the `ℰ`
  row of Proposition 13 derived from Lemma 12 (L3) (`ThetaBound`).
* `goldbach_short_intervals_of_lemmas`. Hypotheses:
  - cited results: RH, the explicit formula for ψ (`ExplicitFormulaPsi`) and the verification
    of Oliveira e Silva, Herzog and Pardi (`GoldbachVerifiedUpTo (4·10¹⁸)`);
  - the paper's own lemmas not yet formalized: `Lemma7`, `Prop13T` and `PrimePowerBound`
    (see `GoldbachRH.Assembly`).
  Lemma 8 and the step from these lemmas to (6) are proved.
* `goldbach_short_intervals`: the same conclusion from the single hypothesis
  `RiemannHypothesis → WeightedMeanSquareBound`.
-/

open Real MeasureTheory

namespace GoldbachRH

/-- The range `4 ≤ x < 3.9·10¹⁸`, from the verification up to `4·10¹⁸`. -/
lemma small_range (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) {x : ℝ} (hx : 4 ≤ x)
    (hx' : x < 3.9e18) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 2 * log x ^ 2 := by
  have hx0 : 0 ≤ x / 2 := by linarith
  set m := ⌊x / 2⌋₊ with hm
  have hm1 : (m : ℝ) ≤ x / 2 := Nat.floor_le hx0
  have hm2 : x / 2 < m + 1 := Nat.lt_floor_add_one _
  have hm3 : 2 ≤ m := by
    rw [hm]; exact Nat.le_floor (by norm_num; linarith)
  have hlog : 1 ≤ log x := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  refine ⟨2 * (m + 1), hOHP _ (even_two_mul _) (by omega) ?_, ?_, ?_⟩
  · have : ((2 * (m + 1) : ℕ) : ℝ) ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this
  · push_cast; linarith
  · push_cast; nlinarith

/-- **Main theorem.** Assume RH, the verification of binary Goldbach up to `4·10¹⁸`, and the
analytic estimate of the paper (`RiemannHypothesis → WeightedMeanSquareBound`). Then for every
real `x ≥ 4`, `(x, x + 2 log² x]` contains a Goldbach number. -/
theorem goldbach_short_intervals (hRH : RiemannHypothesis)
    (hWMS : RiemannHypothesis → WeightedMeanSquareBound)
    (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18)) :
    ∀ x : ℝ, 4 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 2 * log x ^ 2 := by
  intro x hx
  by_cases hsmall : x < 3.9e18
  · exact small_range hOHP hx hsmall
  push Not at hsmall
  by_contra hcon
  push Not at hcon
  have hx0 : 0 < x := by linarith
  set L := log x with hLdef
  have hL : (42.8 : ℝ) ≤ L := by
    rw [hLdef, le_log_iff_exp_le hx0]; exact exp_42_8_le.trans hsmall
  have hL0 : 0 < L := by linarith
  set V := Vp L with hVdef
  set δ := 2 * L ^ 2 / x with hδdef
  have hV : 0 < V := by linarith [Vp_ge hL]
  have hδ : 0 ≤ δ := by positivity
  have hδx : δ * x = 2 * L ^ 2 := by rw [hδdef]; field_simp
  -- `x e^{-V} = e^{u}` with `u ≥ 23.15`
  have hxe : x * exp (-V) = exp (uL L) := by
    rw [uL, ← hVdef, sub_eq_add_neg, exp_add, hLdef, exp_log hx0]
  have hy0 : 2 < x * exp (-V) := by
    rw [hxe]
    have := add_one_le_exp (uL L)
    linarith [uL_ge hL]
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
    have e : (1 + δ) * x = x + 2 * log x ^ 2 := by rw [add_mul, one_mul, hδx]
    linarith
  have hlow := cover_lower_bound hx0 hV hδ hy0 hy0' hNG
  have hup := hWMS hRH x hsmall
  set S := √(Tb L) + √(Eb L) + √(Bb L) with hS
  have hRHS0 : 0 ≤ 2 * log x ^ 2 / x * x ^ 2 * S ^ 2 := by positivity
  have hcomb : δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) ≤
      δ * x ^ 2 * S ^ 2 := by
    have h := hlow.trans hup
    rw [ENNReal.ofReal_le_ofReal_iff hRHS0] at h
    simpa [hδdef] using h
  have hrange := range_inequality hL
  rw [← hVdef, ← hS] at hrange
  have hpos : 0 < δ * x ^ 2 := by
    have : 0 < δ := by rw [hδdef]; positivity
    positivity
  have : δ * x ^ 2 * (2 * L ^ 2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V))) ≤ δ * x ^ 2 * S ^ 2 := by
    calc δ * x ^ 2 * (2 * L ^ 2 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)))
        = δ ^ 2 * x ^ 3 * (1 / 2 - 9.55 / V ^ 2 - exp (-V)) := by rw [← hδx]; ring
      _ ≤ _ := hcomb
  have := le_of_mul_le_mul_left this hpos
  linarith

/-- **Main theorem, with the analytic part split into its pieces.** Assume RH, the explicit
formula for ψ, the verification up to `4·10¹⁸`, and the paper's Lemma 7 and the two rows of
Proposition 13 that are not yet formalized. Then every interval `(x, x + 2 log² x]` with
`x ≥ 4` contains a Goldbach number. -/
theorem goldbach_short_intervals_of_lemmas (hRH : RiemannHypothesis)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (h7 : Lemma7) (h13 : Prop13T) (hPP : PrimePowerBound) :
    ∀ x : ℝ, 4 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 2 * log x ^ 2 :=
  goldbach_short_intervals hRH (fun h => wms_of_lemmas h7 h13 hPP h hEF) hOHP

/-- **Main theorem, current form.** As `goldbach_short_intervals_of_lemmas`, with Lemma 7 now
proved (`GoldbachRH.lemma7`). Remaining hypotheses: RH, the explicit formula for ψ, the
verification up to `4·10¹⁸`, Lemma 12 (L3) and the `𝒯` row of Proposition 13. -/
theorem goldbach_short_intervals_main (hRH : RiemannHypothesis)
    (hEF : ExplicitFormulaPsi) (hOHP : GoldbachVerifiedUpTo (4 * 10 ^ 18))
    (hL3 : ThetaBound) (h13 : Prop13T) :
    ∀ x : ℝ, 4 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 2 * log x ^ 2 :=
  goldbach_short_intervals_of_lemmas hRH hEF hOHP lemma7 h13 (primePowerBound_of_L3 hL3)

end GoldbachRH
