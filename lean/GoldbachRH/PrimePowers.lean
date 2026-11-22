import GoldbachRH.Assembly

/-!
# The prime-power row `ℰ` of Proposition 13

`‖P‖²_ω ≤ δ x² ℰ`, with `ℰ` the Table 1 bound. The only arithmetic input is Lemma 12 (L3),
Chebyshev's bound `θ(t) ≤ t log 4`, which Mathlib proves (`Chebyshev.theta_le_log4_mul_x`).

Proof (the paper's, with one simplification noted below).
1. `P(y) = Σ_{k=2}^N P_k(y)` with `P_k(y) = Σ_{p : y < p^k ≤ (1+δ)y} log p` (Mathlib's
   `ψ = θ + Σ_{k≥2} θ(x^{1/k})`), and Cauchy–Schwarz gives `P² ≤ (N-1) Σ_k P_k²`.
2. For `y` in the support of `ω`, `P_k(y)` has at most one term (Bernoulli's inequality), so
   `P_k(y)² = Σ_p log² p · 1[y < p^k ≤ (1+δ)y]`.
3. `∫ 1[y < p^k ≤ (1+δ)y] ω ≤ δ(1+δ) x²/p^k`, and the integral vanishes unless `p^k > y₀`.
   (Bounding `ω ≤ x²/y²` by its maximum on the window gives the factor `1+δ` of Table 1.)
4. Abel summation against `θ`, with (L3), bounds `Σ_{p^k > y₀} log² p/p^k`.
5. Summing over `k` in the three ranges `k = 2`, `3 ≤ k ≤ ℓ/log 2`, `k > ℓ/log 2`.
-/

open Real MeasureTheory Set Filter
open scoped ENNReal

namespace GoldbachRH

/-! ### Step 4: Abel summation against `θ` -/

/-- `c(n) = log n` for prime `n`, else `0`; its partial sums are `θ`. -/
noncomputable def cθ (n : ℕ) : ℝ := if n.Prime then log n else 0

lemma theta_eq_sum_cθ (t : ℝ) : Chebyshev.theta t = ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, cθ n := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]; rfl

/-- `f(t) = log t / t^k` with `k = j + 2`. -/
noncomputable def fk (j : ℕ) (t : ℝ) : ℝ := log t / t ^ (j + 2)
/-- `f'(t) = (1 - k log t)/t^{k+1}`. -/
noncomputable def fkd (j : ℕ) (t : ℝ) : ℝ := (1 - (j + 2) * log t) / t ^ (j + 3)
/-- An antiderivative of `f`: `F(t) = -(log t/(k-1) + 1/(k-1)²)/t^{k-1}`. -/
noncomputable def Fk (j : ℕ) (t : ℝ) : ℝ := (-(log t) / (j + 1) - 1 / (j + 1) ^ 2) / t ^ (j + 1)

lemma hasDerivAt_fk (j : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (fk j) (fkd j t) t := by
  have h := (hasDerivAt_log ht.ne').div (hasDerivAt_pow (j + 2) t) (pow_ne_zero _ ht.ne')
  simp only [show j + 2 - 1 = j + 1 by omega] at h
  convert h using 1
  · funext s; simp [fk]
  · unfold fkd
    have := ht.ne'
    field_simp
    push_cast
    ring

lemma hasDerivAt_Fk (j : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (Fk j) (fk j t) t := by
  have hn : HasDerivAt (fun t => -(log t) / (j + 1) - 1 / ((j : ℝ) + 1) ^ 2)
      (-(1 / t) / (j + 1)) t := by
    have := ((hasDerivAt_log ht.ne').neg.div_const ((j : ℝ) + 1)).sub_const (1 / ((j : ℝ) + 1) ^ 2)
    convert this using 1; ring
  have h := hn.div (hasDerivAt_pow (j + 1) t) (pow_ne_zero _ ht.ne')
  simp only [Nat.add_sub_cancel] at h
  convert h using 1
  · funext s; simp [Fk]
  · unfold fk
    have := ht.ne'
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

lemma continuousOn_fkd (j : ℕ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (fkd j) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
  apply ContinuousAt.continuousWithinAt
  unfold fkd
  exact (continuousAt_const.sub (continuousAt_const.mul (continuousAt_log ht0))).div
    ((continuous_pow _).continuousAt) (pow_ne_zero _ ht0)

lemma continuousOn_fk (j : ℕ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (fk j) (Icc a b) :=
  fun t ht => (hasDerivAt_fk j (by linarith [ht.1])).continuousAt.continuousWithinAt

lemma fkd_nonpos (j : ℕ) {t : ℝ} (ht : 2 ≤ t) : fkd j t ≤ 0 := by
  unfold fkd
  have hl : log 2 ≤ log t := log_le_log (by norm_num) ht
  have h2 := log_two_gt_d9
  have h1 : 1 - (j + 2) * log t ≤ 0 := by
    have : (2 : ℝ) ≤ j + 2 := by have := j.cast_nonneg (α := ℝ); linarith
    nlinarith
  exact div_nonpos_iff.2 (Or.inr ⟨h1, by positivity⟩)

lemma Fk_nonpos (j : ℕ) {t : ℝ} (ht : 1 ≤ t) : Fk j t ≤ 0 := by
  unfold Fk
  have := log_nonneg ht
  have h : -(log t) / (j + 1) - 1 / ((j : ℝ) + 1) ^ 2 ≤ 0 := by
    have : 0 ≤ log t / ((j : ℝ) + 1) := by positivity
    have : 0 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by positivity
    rw [neg_div]; linarith
  exact div_nonpos_iff.2 (Or.inr ⟨h, by positivity⟩)

/-- **Abel summation against `θ`.** If `θ(t) ≤ C t` for `t > 0` and `2 ≤ a ≤ b`, then
`Σ_{a < n ≤ b} f(n) c(n) ≤ C (a f(a) - F(a)) - f(a) θ(a)`. -/
lemma abel_bound {C : ℝ} (hC : 0 ≤ C) (hθ : ∀ t : ℝ, 0 < t → Chebyshev.theta t ≤ C * t)
    (j : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, fk j n * cθ n
      ≤ C * (a * fk j a - Fk j a) - fk j a * Chebyshev.theta a := by
  have hpos : ∀ t ∈ Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have ha0 : 0 < a := by linarith
  have hdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fk j) t :=
    fun t ht => (hasDerivAt_fk j (hpos t ht)).differentiableAt
  have hderiv : ∀ t ∈ Icc a b, deriv (fk j) t = fkd j t :=
    fun t ht => (hasDerivAt_fk j (hpos t ht)).deriv
  have hint : IntegrableOn (deriv (fk j)) (Icc a b) :=
    ((continuousOn_fkd j ha0).integrableOn_Icc).congr_fun (fun t ht => (hderiv t ht).symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul cθ (by linarith) hab hdiff hint
  simp only [← theta_eq_sum_cθ] at habel
  rw [habel]
  -- replace `deriv f` by `f'`
  have hcongr : ∫ t in Ioc a b, deriv (fk j) t * Chebyshev.theta t
      = ∫ t in Ioc a b, fkd j t * Chebyshev.theta t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [hderiv t (Ioc_subset_Icc_self ht)]
  rw [hcongr]
  -- `∫ f' θ ≥ ∫ f' · C t`
  have hθint : IntegrableOn Chebyshev.theta (Icc a b) :=
    (Chebyshev.theta_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hI1 : IntegrableOn (fun t => fkd j t * Chebyshev.theta t) (Ioc a b) := by
    have := hθint.mul_continuousOn (continuousOn_fkd j ha0) isCompact_Icc
    refine (this.mono_set Ioc_subset_Icc_self).congr_fun (fun t _ => by ring) measurableSet_Ioc
  have hcont2 : ContinuousOn (fun t => fkd j t * (C * t)) (Icc a b) :=
    (continuousOn_fkd j ha0).mul (continuousOn_const.mul continuousOn_id)
  have hI2 : IntegrableOn (fun t => fkd j t * (C * t)) (Ioc a b) :=
    hcont2.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmono : ∫ t in Ioc a b, fkd j t * (C * t) ≤ ∫ t in Ioc a b, fkd j t * Chebyshev.theta t :=
    setIntegral_mono_on hI2 hI1 measurableSet_Ioc fun t ht =>
      mul_le_mul_of_nonpos_left (hθ t (by linarith [ht.1])) (fkd_nonpos j (by linarith [ht.1]))
  -- integration by parts: `∫ t f'(t) = b f(b) - a f(a) - ∫ f`
  have hfc := continuousOn_fk j ha0 (b := b)
  have hparts : ∫ t in a..b, (fk j t + t * fkd j t) = b * fk j b - a * fk j a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * fk j t)]
    · intro t ht
      rw [uIcc_of_le hab] at ht
      have := (hasDerivAt_id' t).mul (hasDerivAt_fk j (hpos t ht))
      convert this using 1; ring
    · exact (hfc.add (continuousOn_id.mul (continuousOn_fkd j ha0))).intervalIntegrable_of_Icc hab
  have hsplit : ∫ t in a..b, (fk j t + t * fkd j t)
      = (∫ t in a..b, fk j t) + ∫ t in a..b, t * fkd j t :=
    intervalIntegral.integral_add (hfc.intervalIntegrable_of_Icc hab)
      ((continuousOn_id.mul (continuousOn_fkd j ha0)).intervalIntegrable_of_Icc hab)
  have hF : ∫ t in a..b, fk j t = Fk j b - Fk j a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_Fk j (hpos t (by rwa [uIcc_of_le hab] at ht)))
      (hfc.intervalIntegrable_of_Icc hab)
  have hC2 : ∫ t in Ioc a b, fkd j t * (C * t) = C * ∫ t in a..b, t * fkd j t := by
    rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
    congr 1; ext t; ring
  have hFb := Fk_nonpos j (show 1 ≤ b by linarith)
  have hb0 : 0 ≤ fk j b := by
    unfold fk; have := log_nonneg (show (1 : ℝ) ≤ b by linarith)
    have : 0 < b := by linarith
    positivity
  have hθb : fk j b * Chebyshev.theta b ≤ fk j b * (C * b) :=
    mul_le_mul_of_nonneg_left (hθ b (by linarith)) hb0
  rw [hsplit, hF] at hparts
  rw [hC2] at hmono
  nlinarith [mul_nonneg hC (neg_nonneg.2 hFb)]

lemma fk_mul_cθ_nonneg (j n : ℕ) : 0 ≤ fk j n * cθ n := by
  unfold cθ
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h.one_lt.le
    have := log_nonneg h1
    unfold fk; have : (0 : ℝ) < n := by linarith
    positivity
  · simp

lemma theta_ge_log_two {a : ℝ} (ha : 2 ≤ a) : log 2 ≤ Chebyshev.theta a := by
  rw [theta_eq_sum_cθ]
  have h2 : 2 ∈ Finset.Icc 0 ⌊a⌋₊ := Finset.mem_Icc.2 ⟨by norm_num, Nat.le_floor (by exact_mod_cast ha)⟩
  have := Finset.single_le_sum (f := cθ) (fun n _ => by
    unfold cθ; split_ifs with h
    · exact log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl 0) h2
  simpa [cθ, Nat.prime_two] using this

/-- **Step 4, per exponent.** For `k = j + 2` and `y₀ = e^ℓ`,
`Σ_{p ≤ M, p^k > y₀} log² p / p^k ≤ C (a f(a) - F(a))` with `a = max(y₀^{1/k}, 2)`. -/
lemma sum_k_bound {C : ℝ} (hC : 0 ≤ C) (hθ : ∀ t : ℝ, 0 < t → Chebyshev.theta t ≤ C * t)
    (j : ℕ) (ℓ : ℝ) (M : ℕ) :
    ∑ p ∈ (Finset.Ioc 0 M).filter Nat.Prime,
        (if exp ℓ < (p : ℝ) ^ (j + 2) then log p ^ 2 / (p : ℝ) ^ (j + 2) else 0)
      ≤ C * (max (exp (ℓ / (j + 2))) 2 * fk j (max (exp (ℓ / (j + 2))) 2)
        - Fk j (max (exp (ℓ / (j + 2))) 2)) := by
  set r := exp (ℓ / (j + 2)) with hr
  set a := max r 2 with ha
  set b := max (M : ℝ) a with hb
  have ha2 : 2 ≤ a := le_max_right _ _
  have hab : a ≤ b := le_max_right _ _
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hrk : r ^ (j + 2) = exp ℓ := by
    rw [hr, ← exp_nat_mul]; congr 1; push_cast; field_simp
  have hcond : ∀ n : ℕ, (exp ℓ < (n : ℝ) ^ (j + 2) ↔ r < n) := by
    intro n; rw [← hrk]; exact pow_lt_pow_iff_left₀ hr0 (Nat.cast_nonneg n) (by omega)
  set g : ℕ → ℝ := fun n => if n.Prime ∧ r < n then fk j n * cθ n else 0 with hg
  have hLHS : ∑ p ∈ (Finset.Ioc 0 M).filter Nat.Prime,
      (if exp ℓ < (p : ℝ) ^ (j + 2) then log p ^ 2 / (p : ℝ) ^ (j + 2) else 0)
      = ∑ n ∈ Finset.Ioc 0 M, g n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · by_cases hn : r < n
      · simp [hg, hp, hn, hcond, fk, cθ]; ring
      · simp [hg, hp, hn, hcond]
    · simp [hg, hp]
  have hg_le : ∀ n, g n ≤ fk j n * cθ n := by
    intro n; simp only [hg]; split_ifs
    · exact le_refl _
    · exact fk_mul_cθ_nonneg j n
  rw [hLHS, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 M) (fun n => n ≤ ⌊a⌋₊)]
  -- the part `n > ⌊a⌋`
  have hpart2 : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => ¬ n ≤ ⌊a⌋₊), g n
      ≤ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, fk j n * cθ n := by
    refine (Finset.sum_le_sum fun n _ => hg_le n).trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => fk_mul_cθ_nonneg j n)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_le] at hn
    exact Finset.mem_Ioc.2 ⟨hn.2, hn.1.2.trans (Nat.le_floor (le_max_left _ _))⟩
  -- the part `n ≤ ⌊a⌋`
  have hθa0 : 0 ≤ fk j a * Chebyshev.theta a := by
    have := log_nonneg (show (1 : ℝ) ≤ a by linarith)
    have : 0 < a := by linarith
    have := Chebyshev.theta_nonneg a
    unfold fk; positivity
  have hpart1 : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => n ≤ ⌊a⌋₊), g n
      ≤ fk j a * Chebyshev.theta a := by
    by_cases hr2 : 2 ≤ r
    · have hae : a = r := max_eq_left hr2
      refine le_trans (le_of_eq (Finset.sum_eq_zero fun n hn => ?_)) hθa0
      simp only [Finset.mem_filter] at hn
      have : (n : ℝ) ≤ r := by
        rw [← hae]; exact (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
      simp [hg, not_lt.2 this]
    · push Not at hr2
      have hae : a = 2 := max_eq_right hr2.le
      have hfl : ⌊a⌋₊ = 2 := by rw [hae]; norm_num
      have hle : ∀ n ∈ (Finset.Ioc 0 M).filter (fun n => n ≤ ⌊a⌋₊),
          g n ≤ if n = 2 then fk j 2 * log 2 else 0 := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioc, hfl] at hn
        rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
        · simp [hg, Nat.not_prime_one]
        · simp only [hg, ite_true]
          split_ifs
          · simp [cθ, Nat.prime_two]
          · exact fk_mul_cθ_nonneg j 2 |>.trans (le_of_eq (by simp [cθ, Nat.prime_two]))
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_ite_eq']
      have h2pos : 0 ≤ fk j 2 * log 2 := by
        have := fk_mul_cθ_nonneg j 2; simpa [cθ, Nat.prime_two] using this
      have hθ2 := theta_ge_log_two (le_refl (2 : ℝ))
      have hfk2 : 0 ≤ fk j 2 := by unfold fk; have := log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
      rw [hae]
      split_ifs
      · exact mul_le_mul_of_nonneg_left hθ2 hfk2
      · exact mul_nonneg hfk2 (Chebyshev.theta_nonneg 2)
  have habel := abel_bound hC hθ j ha2 hab
  linarith

/-! ### Step 5: summing over the exponents -/

/-- `G(a) = a f(a) - F(a)`, the per-exponent bound of `sum_k_bound`. -/
noncomputable def Gk (j : ℕ) (a : ℝ) : ℝ := a * fk j a - Fk j a

lemma Gk_eq (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Gk j a = (log a * (1 + 1 / (j + 1)) + 1 / (j + 1) ^ 2) / a ^ (j + 1) := by
  unfold Gk fk Fk
  have := ha.ne'
  have : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The per-exponent bound for `k = j + 2` and `y₀ = e^u`. -/
noncomputable def Bk (u : ℝ) (j : ℕ) : ℝ := Gk j (max (exp (u / (j + 2))) 2)

lemma Bk_nonneg (u : ℝ) (j : ℕ) : 0 ≤ Bk u j := by
  unfold Bk
  have ha : 2 ≤ max (exp (u / (j + 2))) 2 := le_max_right _ _
  rw [Gk_eq j (by linarith)]
  have := log_nonneg (show (1 : ℝ) ≤ max (exp (u / (j + 2))) 2 by linarith)
  have : 0 < max (exp (u / (j + 2))) 2 := by linarith
  positivity

lemma Bk_zero {u : ℝ} (hu : 2 ≤ u) : Bk u 0 ≤ (u + 2) * exp (-u / 2) := by
  unfold Bk
  simp only [Nat.cast_zero, zero_add]
  have h2 : 2 ≤ exp (u / 2) := by linarith [add_one_le_exp (u / 2)]
  rw [max_eq_left h2, Gk_eq 0 (exp_pos _), log_exp, pow_one, div_eq_mul_inv, ← exp_neg,
    neg_div]
  have : 0 ≤ exp (-(u / 2)) := (exp_pos _).le
  norm_num
  nlinarith

lemma Bk_mid {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) (h2 : 2 ≤ exp (u / (j + 2))) :
    Bk u j ≤ (u / 2 + 3 / 4) * exp (-(2 * u) / 3) := by
  unfold Bk
  rw [max_eq_left h2, Gk_eq j (exp_pos _), log_exp, ← exp_nat_mul, div_eq_mul_inv, ← exp_neg]
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have e1 : u / (j + 2) * (1 + 1 / (j + 1)) = u / (j + 1) := by field_simp; ring
  rw [e1]
  have h1 : u / (j + 1) ≤ u / 2 := div_le_div_of_nonneg_left hu (by norm_num) (by linarith)
  have h1' : 1 / ((j : ℝ) + 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3 : -(((j + 1 : ℕ) : ℝ) * (u / (j + 2))) ≤ -(2 * u) / 3 := by
    push_cast
    have : 2 * u / 3 ≤ ((j : ℝ) + 1) * (u / ((j : ℝ) + 2)) := by
      rw [show ((j : ℝ) + 1) * (u / ((j : ℝ) + 2)) = (j + 1) * u / (j + 2) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  exact mul_le_mul (by linarith) (exp_le_exp.2 h3) (exp_pos _).le (by positivity)

lemma Bk_large {u : ℝ} (hu : 23.15 ≤ u) {j : ℕ} (h2 : exp (u / (j + 2)) < 2) :
    Bk u j ≤ 1.5 * (1 / 2) ^ (j + 2) := by
  unfold Bk
  rw [max_eq_right h2.le, Gk_eq j (by norm_num)]
  have hl1 := log_two_lt_d9
  have hl0 := log_two_gt_d9
  have hlt : u / (j + 2) < log 2 := by
    rw [← exp_lt_exp, exp_log (by norm_num)]; exact h2
  have hj : (31 : ℝ) < j := by
    rw [div_lt_iff₀ (by positivity)] at hlt
    nlinarith
  have hjn : 32 ≤ j := by
    have : (31 : ℕ) < j := by exact_mod_cast hj
    omega
  have hj32 : (32 : ℝ) ≤ j := by exact_mod_cast hjn
  have hj1 : 1 / ((j : ℝ) + 1) ≤ 1 / 33 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hj2 : 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / 1089 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hnum : log 2 * (1 + 1 / ((j : ℝ) + 1)) + 1 / ((j : ℝ) + 1) ^ 2 ≤ 0.75 := by
    have : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
    nlinarith
  rw [show (1.5 : ℝ) * (1 / 2) ^ (j + 2) = 0.75 / 2 ^ (j + 1) by
    rw [one_div_pow, pow_succ]; field_simp; norm_num]
  exact div_le_div_of_nonneg_right hnum (by positivity)

lemma half_pow_eq (n : ℕ) : (1 / 2 : ℝ) ^ n = exp (-(n * log 2)) := by
  rw [show (1 / 2 : ℝ) = exp (-log 2) by rw [exp_neg, exp_log (by norm_num)]; norm_num,
    ← exp_nat_mul]; ring_nf

/-- **Step 5.** `Σ_j B_j ≤ (u+2)e^{-u/2} + (u/log 2)(u/2 + 3/4)e^{-2u/3} + 3e^{-u}`. -/
lemma sum_Bk_le {u : ℝ} (hu : 23.15 ≤ u) (R : ℕ) :
    ∑ j ∈ Finset.range R, Bk u j
      ≤ (u + 2) * exp (-u / 2) + u / log 2 * (u / 2 + 3 / 4) * exp (-(2 * u) / 3)
        + 3 * exp (-u) := by
  classical
  have hl0 := log_two_gt_d9
  have hl1 := log_two_lt_d9
  have hlog : 0 < log 2 := log_pos (by norm_num)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j : ℕ => 2 ≤ exp (u / ((j : ℝ) + 2))),
    ← Finset.sum_filter_add_sum_filter_not ((Finset.range R).filter
      (fun j : ℕ => 2 ≤ exp (u / ((j : ℝ) + 2)))) (fun j : ℕ => j = 0)]
  -- `j = 0`
  have hP0 : ∑ j ∈ ((Finset.range R).filter (fun j : ℕ => 2 ≤ exp (u / ((j : ℝ) + 2)))).filter
      (fun j : ℕ => j = 0), Bk u j ≤ (u + 2) * exp (-u / 2) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {0}) ?_
      fun j _ _ => Bk_nonneg u j) ?_
    · intro j hj; simp only [Finset.mem_filter] at hj; simp [hj.2]
    · rw [Finset.sum_singleton]; exact Bk_zero (by linarith)
  -- `1 ≤ j`, `2 ≤ e^{u/(j+2)}`
  have hPmid : ∑ j ∈ ((Finset.range R).filter (fun j : ℕ => 2 ≤ exp (u / ((j : ℝ) + 2)))).filter
      (fun j : ℕ => ¬ j = 0), Bk u j ≤ u / log 2 * (u / 2 + 3 / 4) * exp (-(2 * u) / 3) := by
    set S := ((Finset.range R).filter (fun j : ℕ => 2 ≤ exp (u / ((j : ℝ) + 2)))).filter (fun j : ℕ => ¬ j = 0)
    have hsub : S ⊆ Finset.Icc 1 ⌊u / log 2⌋₊ := by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      refine Finset.mem_Icc.2 ⟨by omega, Nat.le_floor ?_⟩
      have h := log_le_log (by norm_num) hj.1.2
      rw [log_exp, le_div_iff₀ (by positivity)] at h
      rw [le_div_iff₀ hlog]
      have := j.cast_nonneg (α := ℝ)
      nlinarith
    have hcard : (S.card : ℝ) ≤ u / log 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      calc (S.card : ℝ) ≤ ((⌊u / log 2⌋₊ + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast this
        _ = ⌊u / log 2⌋₊ := by simp
        _ ≤ u / log 2 := Nat.floor_le (by positivity)
    have hb : ∀ j ∈ S, Bk u j ≤ (u / 2 + 3 / 4) * exp (-(2 * u) / 3) := by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      exact Bk_mid (by linarith) (by omega) hj.1.2
    calc ∑ j ∈ S, Bk u j ≤ S.card • ((u / 2 + 3 / 4) * exp (-(2 * u) / 3)) :=
          Finset.sum_le_card_nsmul S _ _ hb
      _ = S.card * ((u / 2 + 3 / 4) * exp (-(2 * u) / 3)) := by rw [nsmul_eq_mul]
      _ ≤ u / log 2 * ((u / 2 + 3 / 4) * exp (-(2 * u) / 3)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  -- `e^{u/(j+2)} < 2`
  have hPlarge : ∑ j ∈ (Finset.range R).filter (fun j : ℕ => ¬ 2 ≤ exp (u / ((j : ℝ) + 2))), Bk u j
      ≤ 3 * exp (-u) := by
    set m0 := ⌊u / log 2⌋₊ - 1
    have hfl : (33 : ℝ) ≤ ⌊u / log 2⌋₊ := by
      have : (33 : ℝ) ≤ u / log 2 := by rw [le_div_iff₀ hlog]; nlinarith
      exact_mod_cast Nat.le_floor (by exact_mod_cast this : ((33 : ℕ) : ℝ) ≤ u / log 2)
    have hsub : (Finset.range R).filter (fun j : ℕ => ¬ 2 ≤ exp (u / ((j : ℝ) + 2))) ⊆ Finset.Ico m0 R := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, not_le] at hj
      refine Finset.mem_Ico.2 ⟨?_, hj.1⟩
      have h := log_lt_log (exp_pos _) hj.2
      rw [log_exp, div_lt_iff₀ (by positivity)] at h
      have h' : u / log 2 < j + 2 := by rw [div_lt_iff₀ hlog]; linarith
      have := Nat.floor_lt (by positivity : 0 ≤ u / log 2) |>.2 (by exact_mod_cast h' :
        u / log 2 < ((j + 2 : ℕ) : ℝ))
      omega
    calc ∑ j ∈ (Finset.range R).filter (fun j : ℕ => ¬ 2 ≤ exp (u / ((j : ℝ) + 2))), Bk u j
        ≤ ∑ j ∈ (Finset.range R).filter (fun j : ℕ => ¬ 2 ≤ exp (u / ((j : ℝ) + 2))),
            1.5 * (1 / 2 : ℝ) ^ (j + 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_filter, not_le] at hj
          exact Bk_large hu hj.2
      _ ≤ ∑ j ∈ Finset.Ico m0 R, 1.5 * (1 / 2 : ℝ) ^ (j + 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
      _ = 3 / 8 * ∑ j ∈ Finset.Ico m0 R, (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ 3 / 8 * ((1 / 2 : ℝ) ^ m0 / (1 - 1 / 2)) := by
          gcongr; exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = 3 / 4 * (1 / 2 : ℝ) ^ m0 := by ring
      _ ≤ 3 * exp (-u) := by
          rw [half_pow_eq]
          have hm0 : (m0 : ℝ) = ⌊u / log 2⌋₊ - 1 := by
            rw [Nat.cast_sub (by exact_mod_cast (by linarith : (1 : ℝ) ≤ ⌊u / log 2⌋₊))]; simp
          have hfl2 : u / log 2 - 1 < ⌊u / log 2⌋₊ := Nat.sub_one_lt_floor _
          have hlt : -u + 2 * log 2 ≥ -((m0 : ℝ) * log 2) := by
            rw [hm0]
            have : u < (⌊u / log 2⌋₊ + 1) * log 2 := by
              have := (div_lt_iff₀ hlog).1 (show u / log 2 < ⌊u / log 2⌋₊ + 1 by linarith)
              linarith
            nlinarith
          have : exp (-((m0 : ℝ) * log 2)) ≤ exp (-u) * 4 := by
            calc exp (-((m0 : ℝ) * log 2)) ≤ exp (-u + 2 * log 2) := exp_le_exp.2 hlt
              _ = exp (-u) * 4 := by
                rw [exp_add, show 2 * log 2 = log 4 by
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num, exp_log (by norm_num)]
          linarith
  linarith

/-! ### Step 1: `P = Σ_k P_k` -/

/-- The primes up to `M`. -/
def Pset (M : ℕ) : Finset ℕ := (Finset.Ioc 0 M).filter Nat.Prime

/-- `P_k(y) = Σ_{p : y < p^k ≤ (1+δ)y} log p` (primes `p ≤ M`). -/
noncomputable def Pk (δ : ℝ) (M k : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ Pset M, (if y < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ (1 + δ) * y then log p else 0)

lemma theta_eq_sum_ite {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : t ≤ M) :
    Chebyshev.theta t = ∑ p ∈ Pset M, (if (p : ℝ) ≤ t then log p else 0) := by
  rw [← Finset.sum_filter]
  have h : Chebyshev.theta t = ∑ p ∈ (Finset.Ioc 0 ⌊t⌋₊).filter Nat.Prime, log p := rfl
  rw [h]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Pset, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, h1⟩, hp⟩
    have : (p : ℝ) ≤ t := (Nat.le_floor_iff ht).1 h1
    exact ⟨⟨⟨h0, by exact_mod_cast this.trans hM⟩, hp⟩, this⟩
  · rintro ⟨⟨⟨h0, _⟩, hp⟩, h⟩
    exact ⟨⟨h0, (Nat.le_floor_iff ht).2 h⟩, hp⟩

lemma theta_root_diff {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 1 ≤ y) {k M : ℕ} (hk : 1 ≤ k)
    (hM : (1 + δ) * y ≤ M) :
    Chebyshev.theta (((1 + δ) * y) ^ ((1 : ℝ) / k)) - Chebyshev.theta (y ^ ((1 : ℝ) / k))
      = Pk δ M k y := by
  have hb : 1 ≤ (1 + δ) * y := by nlinarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) / k ≤ 1 := by rw [div_le_one hk0]; exact_mod_cast hk
  rw [theta_eq_sum_ite (by positivity) ((rpow_le_self_of_one_le hb hk1).trans hM),
    theta_eq_sum_ite (by positivity) ((rpow_le_self_of_one_le hy hk1).trans (by nlinarith)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : ∀ z : ℝ, 0 ≤ z → ((p : ℝ) ≤ z ^ ((1 : ℝ) / k) ↔ (p : ℝ) ^ k ≤ z) := by
    intro z hz
    rw [one_div, le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hz hk0, rpow_natCast]
  simp only [hiff _ (show 0 ≤ (1 + δ) * y by positivity), hiff _ (show 0 ≤ y by positivity)]
  by_cases hA : (p : ℝ) ^ k ≤ (1 + δ) * y <;> by_cases hB : (p : ℝ) ^ k ≤ y
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_left_of_eq_true _ _ (eq_true hB), ite_eq_right_of_eq_false _ _ (eq_false (fun h => absurd hB (not_le.2 h.1)))]; ring
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_right_of_eq_false _ _ (eq_false hB), ite_eq_left_of_eq_true _ _ (eq_true ⟨not_le.1 hB, hA⟩)]; ring
  · exact absurd (hB.trans (by nlinarith)) hA
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hA), ite_eq_right_of_eq_false _ _ (eq_false hB), ite_eq_right_of_eq_false _ _ (eq_false (fun h => hA h.2))]; ring

lemma Pfun_eq {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 2 ≤ y) {M N : ℕ} (hM : (1 + δ) * y ≤ M)
    (hN : ⌊log ((1 + δ) * y) / log 2⌋₊ ≤ N) :
    Pfun δ y = ∑ k ∈ Finset.Icc 2 N, Pk δ M k y := by
  have hb : 2 ≤ (1 + δ) * y := by nlinarith
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hNy : ⌊log y / log 2⌋₊ ≤ N :=
    (Nat.floor_le_floor (div_le_div_of_nonneg_right
      (log_le_log (by linarith) (by nlinarith)) hl2.le)).trans hN
  unfold Pfun
  rw [Chebyshev.psi_eq_theta_add_sum_theta' hb hN, Chebyshev.psi_eq_theta_add_sum_theta' hy hNy]
  simp only [add_sub_cancel_left]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact theta_root_diff hδ (by linarith) (by have := (Finset.mem_Icc.1 hk).1; omega) hM

/-! ### Step 2: at most one prime power per exponent -/

lemma sq_sum_of_unique {s : Finset ℕ} {f : ℕ → ℝ}
    (h : ∀ a ∈ s, ∀ b ∈ s, f a ≠ 0 → f b ≠ 0 → a = b) :
    (∑ a ∈ s, f a) ^ 2 = ∑ a ∈ s, f a ^ 2 := by
  by_cases hz : ∃ a ∈ s, f a ≠ 0
  · obtain ⟨a, ha, hfa⟩ := hz
    have h1 : ∑ b ∈ s, f b = f a := Finset.sum_eq_single a
      (fun b hb hba => by by_contra hfb; exact hba (h b hb a ha hfb hfa)) (fun h' => absurd ha h')
    have h2 : ∑ b ∈ s, f b ^ 2 = f a ^ 2 := Finset.sum_eq_single a
      (fun b hb hba => by
        by_contra hfb
        exact hba (h b hb a ha (fun h0 => hfb (by simp [h0])) hfa)) (fun h' => absurd ha h')
    rw [h1, h2]
  · push Not at hz
    rw [Finset.sum_eq_zero hz, Finset.sum_eq_zero (fun a ha => by simp [hz a ha])]; ring

/-- Consecutive `k`-th powers are far apart: `(1+δ) p^k ≤ q^k` for `p < q` when `δ p ≤ 2`. -/
lemma bernoulli_gap {δ : ℝ} {k p q : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p) (hpq : p < q)
    (hδp : δ * p ≤ 2) : (1 + δ) * (p : ℝ) ^ k ≤ (q : ℝ) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hb := one_add_mul_le_pow (a := 1 / (p : ℝ))
    (by have : 0 < 1 / (p : ℝ) := (by positivity); linarith) k
  have e : ((p : ℝ) + 1) ^ k = (p : ℝ) ^ k * (1 + 1 / p) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hkp : 1 + δ ≤ 1 + k * (1 / (p : ℝ)) := by
    have h1 : δ ≤ 2 / p := by rw [le_div_iff₀ hp0]; linarith
    have h2 : (2 : ℝ) / p ≤ k * (1 / p) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hk) hp0.le
    linarith
  calc (1 + δ) * (p : ℝ) ^ k ≤ (1 + k * (1 / (p : ℝ))) * (p : ℝ) ^ k := by gcongr
    _ ≤ (1 + 1 / (p : ℝ)) ^ k * (p : ℝ) ^ k := by gcongr
    _ = ((p : ℝ) + 1) ^ k := by rw [e]; ring
    _ ≤ (q : ℝ) ^ k := by gcongr

lemma Pk_sq {δ y : ℝ} (hδ : 0 ≤ δ) {M k : ℕ} (hk : 2 ≤ k) (hsmall : δ ^ 2 * ((1 + δ) * y) ≤ 4) :
    Pk δ M k y ^ 2 = ∑ p ∈ Pset M,
      (if y < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ (1 + δ) * y then log p ^ 2 else 0) := by
  unfold Pk
  rw [sq_sum_of_unique]
  · exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  · intro a ha b hb hfa hfb
    have ca : y < (a : ℝ) ^ k ∧ (a : ℝ) ^ k ≤ (1 + δ) * y := by
      by_contra h; simp [h] at hfa
    have cb : y < (b : ℝ) ^ k ∧ (b : ℝ) ^ k ≤ (1 + δ) * y := by
      by_contra h; simp [h] at hfb
    have hpa := (Finset.mem_filter.1 ha).2
    have hpb := (Finset.mem_filter.1 hb).2
    have hδp : ∀ q : ℕ, q.Prime → (q : ℝ) ^ k ≤ (1 + δ) * y → δ * q ≤ 2 := by
      intro q hq hqk
      have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      have h2 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ k := pow_le_pow_right₀ h1 hk
      have h3 : (δ * q) ^ 2 ≤ 4 := by
        rw [mul_pow]; nlinarith [sq_nonneg δ]
      nlinarith [mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) q)]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := bernoulli_gap hk hpa.one_lt.le hlt (hδp a hpa ca.2)
      nlinarith [ca.1, cb.2]
    · have := bernoulli_gap hk hpb.one_lt.le hlt (hδp b hpb cb.2)
      nlinarith [cb.1, ca.2]

/-! ### Step 3: one window -/

lemma weight_eq_zero_of_ge {x V y : ℝ} (hx : 0 < x) (hV : 0 < V) (hy : x * exp V ≤ y) :
    weight x V y = 0 := by
  unfold weight
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have h : log (x / y) ≤ -V := by
    rw [log_div hx.ne' hy0.ne']
    have := log_le_log (by positivity) hy
    rw [log_mul hx.ne' (exp_pos V).ne', log_exp] at this
    linarith
  have hW : W V (log (x / y)) = W V (-log (x / y)) := by simp [W, abs_neg]
  rw [hW, W_eq_zero_of_le hV (by linarith), mul_zero]

lemma lintegral_window {x V δ c n : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hn : 0 < n) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((if y < n ∧ n ≤ (1 + δ) * y then c else 0) * weight x V y)
      ≤ ENNReal.ofReal (if x * exp (-V) < n then c * δ * (1 + δ) * x ^ 2 / n else 0) := by
  have hδ1 : 0 < 1 + δ := by linarith
  by_cases h : x * exp (-V) < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    set a := n / (1 + δ) with ha_def
    have ha : 0 < a := by positivity
    set K := c * x ^ 2 * (1 + δ) ^ 2 / n ^ 2 with hK
    have hpt : ∀ y ∈ Ioi (0 : ℝ), ENNReal.ofReal ((if y < n ∧ n ≤ (1 + δ) * y then c else 0)
        * weight x V y) ≤ (Ico a n).indicator (fun _ => ENNReal.ofReal K) y := by
      intro y hy
      have hy : 0 < y := hy
      by_cases hc' : y < n ∧ n ≤ (1 + δ) * y
      · have hya : a ≤ y := by rw [ha_def, div_le_iff₀ hδ1]; linarith [hc'.2]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc'), indicator_of_mem (show y ∈ Ico a n from ⟨hya, hc'.1⟩)]
        apply ENNReal.ofReal_le_ofReal
        have hw := weight_le (x := x) (y := y) hV
        have hxy : (x / y) ^ 2 ≤ x ^ 2 * (1 + δ) ^ 2 / n ^ 2 := by
          rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
          have : n ^ 2 ≤ ((1 + δ) * y) ^ 2 := pow_le_pow_left₀ hn.le hc'.2 2
          nlinarith [sq_nonneg x]
        calc c * weight x V y ≤ c * (x ^ 2 * (1 + δ) ^ 2 / n ^ 2) :=
              mul_le_mul_of_nonneg_left (hw.trans hxy) hc
          _ = K := by rw [hK]; ring
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc'), zero_mul, ENNReal.ofReal_zero]; exact bot_le
    calc _ ≤ ∫⁻ y in Ioi (0 : ℝ), (Ico a n).indicator (fun _ => ENNReal.ofReal K) y :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ ∫⁻ y, (Ico a n).indicator (fun _ => ENNReal.ofReal K) y :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * volume (Ico a n) := lintegral_indicator_const measurableSet_Ico _
      _ = ENNReal.ofReal (K * (n - a)) := by
          rw [Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
          congr 1; rw [hK, ha_def]; field_simp; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ENNReal.ofReal_zero]
    push Not at h
    refine le_of_eq ?_
    refine (setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_).trans lintegral_zero
    have hy : 0 < y := hy
    by_cases hc' : y < n ∧ n ≤ (1 + δ) * y
    · rw [weight_eq_zero hx hV hy (hc'.1.le.trans h), mul_zero, ENNReal.ofReal_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc'), zero_mul, ENNReal.ofReal_zero]

/-! ### Assembly -/

lemma measurable_window (x V δ c n : ℝ) :
    Measurable fun y : ℝ =>
      ENNReal.ofReal ((if y < n ∧ n ≤ (1 + δ) * y then c else 0) * weight x V y) := by
  have hs : MeasurableSet {y : ℝ | y < n ∧ n ≤ (1 + δ) * y} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul measurable_id))
  exact ENNReal.measurable_ofReal.comp
    ((Measurable.ite hs measurable_const measurable_const).mul (measurable_weight x V))

/-- `δ²·2xe^V ≤ 4` for `L ≥ 42.8`. -/
lemma small_param {x : ℝ} (hx0 : 0 < x) (hL : (42.8 : ℝ) ≤ log x) :
    dl (log x) ^ 2 * (2 * (x * exp (Vp (log x)))) ≤ 4 := by
  set L := log x with hLdef
  have hxL : x = exp L := (exp_log hx0).symm
  have hu := uL_ge hL
  have hLu := L_le_two_u hL
  have e : dl L ^ 2 * (2 * (x * exp (Vp L))) = 8 * L ^ 4 * exp (-(1 * uL L)) := by
    rw [hxL, dl, uL]
    have : exp (-L) ^ 2 * exp L * exp (Vp L) = exp (-(1 * (L - Vp L))) := by
      rw [sq, ← exp_add, ← exp_add, ← exp_add]; congr 1; ring
    calc (2 * L ^ 2 * exp (-L)) ^ 2 * (2 * (exp L * exp (Vp L)))
        = 8 * L ^ 4 * (exp (-L) ^ 2 * exp L * exp (Vp L)) := by ring
      _ = _ := by rw [this]
  rw [e]
  have h1 := pow_mul_exp_neg_le (k := 4) (c := 1) (u0 := 23.15) (u := uL L) (by norm_num)
    (by norm_num) hu
  have h2 := num_RT
  have hL4 : L ^ 4 ≤ 16 * uL L ^ 4 := by
    have hL0 : 0 ≤ L := by linarith
    calc L ^ 4 ≤ (2 * uL L) ^ 4 := pow_le_pow_left₀ hL0 hLu 4
      _ = 16 * uL L ^ 4 := by ring
  have hexp : 0 ≤ exp (-(1 * uL L)) := (exp_pos _).le
  have h3 : (23.15 : ℝ) ^ 4 * exp (-(1 * 23.15)) ≤ 1 / (256 * 23.15) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [exp_pos (-(1 * (23.15 : ℝ)))]
  nlinarith [mul_le_mul_of_nonneg_right hL4 hexp]

/-- **The `ℰ` row of Proposition 13.** Unconditional apart from the statement's RH premise,
which is not used. -/
theorem primePowerBound : PrimePowerBound := by
  intro _hRH x hx
  have hx0 : 0 < x := by linarith
  have hL := log_ge_of_ge hx
  have hsmall0 := small_param hx0 hL
  set L := log x with hLdef
  set δ := dl L with hδdef
  set V := Vp L with hVdef
  set u := uL L with hudef
  have hV : 0 < V := by linarith [Vp_ge hL]
  have hδ0 : 0 ≤ δ := dl_nonneg hL
  have hδ1 : δ ≤ 0.29 := dl_le hL
  have hu : (23.15 : ℝ) ≤ u := uL_ge hL
  have hy0 : x * exp (-V) = exp u := x_exp_neg_Vp hx0
  have hθ : ∀ t : ℝ, 0 < t → Chebyshev.theta t ≤ log 4 * t := fun t ht =>
    Chebyshev.theta_le_log4_mul_x ht.le
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  set Y1 := x * exp V with hY1
  set M : ℕ := ⌊2 * Y1⌋₊ + 1 with hM
  set N : ℕ := ⌊(L + V + 1) / log 2⌋₊ with hN
  have hY1pos : 0 < Y1 := by positivity
  have hlogY1 : log Y1 = L + V := by rw [hY1, log_mul hx0.ne' (exp_pos _).ne', log_exp]
  have hexpu : 3 ≤ exp u := by linarith [add_one_le_exp u]
  -- the pointwise bound
  set T : ℕ → ℕ → ℝ → ℝ := fun k p y =>
    (if y < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ (1 + δ) * y then (N : ℝ) * log p ^ 2 else 0)
      * weight x V y with hT
  have hTnn : ∀ k p y, 0 ≤ T k p y := by
    intro k p y
    simp only [hT]
    exact mul_nonneg (by split_ifs <;> positivity) (weight_nonneg (x := x) hV y)
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ENNReal.ofReal (Pfun δ y ^ 2 * weight x V y)
      ≤ ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, ENNReal.ofReal (T k p y) := by
    intro y hy
    have hy : 0 < y := hy
    have hsum : ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, ENNReal.ofReal (T k p y)
        = ENNReal.ofReal (∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, T k p y) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun p _ => hTnn k p y]
      exact Finset.sum_congr rfl fun k _ =>
        (ENNReal.ofReal_sum_of_nonneg fun p _ => hTnn k p y).symm
    rw [hsum]
    apply ENNReal.ofReal_le_ofReal
    by_cases hw : weight x V y = 0
    · rw [hw, mul_zero]
      exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun p _ => hTnn k p y
    have hy0' : exp u < y := by
      rw [← hy0]; by_contra h; exact hw (weight_eq_zero hx0 hV hy (not_lt.1 h))
    have hyY : y < Y1 := by
      by_contra h; exact hw (weight_eq_zero_of_ge hx0 hV (not_lt.1 h))
    have hy2 : 2 ≤ y := by linarith
    have hb2 : (1 + δ) * y ≤ 2 * Y1 := by nlinarith
    have hbM : (1 + δ) * y ≤ M := by
      have := Nat.lt_floor_add_one (2 * Y1)
      rw [hM]; push_cast; linarith
    have hNb : ⌊log ((1 + δ) * y) / log 2⌋₊ ≤ N := by
      apply Nat.floor_le_floor
      apply div_le_div_of_nonneg_right _ hl2.le
      rw [log_mul (by positivity) hy.ne']
      have h1 : log (1 + δ) ≤ δ := by linarith [log_le_sub_one_of_pos (show 0 < 1 + δ by linarith)]
      have h2 : log y ≤ L + V := by rw [← hlogY1]; exact log_le_log hy hyY.le
      linarith
    have hsm : δ ^ 2 * ((1 + δ) * y) ≤ 4 := by
      calc δ ^ 2 * ((1 + δ) * y) ≤ δ ^ 2 * (2 * Y1) := by gcongr
        _ ≤ 4 := hsmall0
    rw [Pfun_eq hδ0 hy2 hbM hNb]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 2 N) (f := fun k => Pk δ M k y)
    have hcard : ((Finset.Icc 2 N).card : ℝ) ≤ N := by
      rw [Nat.card_Icc]; exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    have hR : ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, T k p y
        = (N : ℝ) * (∑ k ∈ Finset.Icc 2 N, Pk δ M k y ^ 2) * weight x V y := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Pk_sq hδ0 (Finset.mem_Icc.1 hk).1 hsm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hT]
      split_ifs <;> ring
    rw [hR]
    have hw0 := weight_nonneg (x := x) hV y
    have hsq : (∑ k ∈ Finset.Icc 2 N, Pk δ M k y) ^ 2
        ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 2 N, Pk δ M k y ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    exact mul_le_mul_of_nonneg_right hsq hw0
  -- integrate term by term
  have hmeas : ∀ k p, Measurable fun y => ENNReal.ofReal (T k p y) := fun k p =>
    measurable_window x V δ _ _
  have hwin : ∀ k ∈ Finset.Icc 2 N, ∀ p ∈ Pset M,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (T k p y)
        ≤ ENNReal.ofReal (if exp u < (p : ℝ) ^ k then
            (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0) := by
    intro k _ p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
    rw [← hy0]
    exact lintegral_window hx0 hV hδ0 (by positivity) (by positivity)
  -- the real sum
  set Sk : ℕ → ℝ := fun k => ∑ p ∈ Pset M,
    (if exp u < (p : ℝ) ^ k then log p ^ 2 / (p : ℝ) ^ k else 0) with hSk
  have hSk_le : ∀ k ∈ Finset.Icc 2 N, Sk k ≤ log 4 * Bk u (k - 2) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := (Finset.mem_Icc.1 hk).1; omega⟩
    simp only [hSk, Nat.add_sub_cancel]
    have := sum_k_bound (log_nonneg (by norm_num)) hθ j u M
    simpa [Pset, Bk, Gk] using this
  have hsumB : ∑ k ∈ Finset.Icc 2 N, Bk u (k - 2) ≤ (u + 2) * exp (-u / 2)
      + u / log 2 * (u / 2 + 3 / 4) * exp (-(2 * u) / 3) + 3 * exp (-u) := by
    rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by ext; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact sum_Bk_le hu _
  have hreal : ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, (if exp u < (p : ℝ) ^ k then
      (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0)
      ≤ δ * x ^ 2 * Eb L := by
    have e : ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, (if exp u < (p : ℝ) ^ k then
        (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0)
        = (N : ℝ) * δ * (1 + δ) * x ^ 2 * ∑ k ∈ Finset.Icc 2 N, Sk k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hSk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> ring
    rw [e]
    have hS1 : ∑ k ∈ Finset.Icc 2 N, Sk k ≤ log 4 * ((u + 2) * exp (-u / 2)
        + u / log 2 * (u / 2 + 3 / 4) * exp (-(2 * u) / 3) + 3 * exp (-u)) := by
      calc ∑ k ∈ Finset.Icc 2 N, Sk k ≤ ∑ k ∈ Finset.Icc 2 N, log 4 * Bk u (k - 2) :=
            Finset.sum_le_sum hSk_le
        _ = log 4 * ∑ k ∈ Finset.Icc 2 N, Bk u (k - 2) := by rw [Finset.mul_sum]
        _ ≤ _ := by gcongr
    have hNle : (N : ℝ) ≤ (L + V + 1) / log 2 := Nat.floor_le (by have := Vp_ge hL; positivity)
    have hSnn : 0 ≤ ∑ k ∈ Finset.Icc 2 N, Sk k :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun p _ => by
        split_ifs
        · have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; positivity
        · exact le_refl 0
    have hEb : δ * x ^ 2 * Eb L = (L + V + 1) / log 2 * δ * (1 + δ) * x ^ 2 * (log 4 *
        ((u + 2) * exp (-u / 2) + u / log 2 * (u / 2 + 3 / 4) * exp (-(2 * u) / 3)
          + 3 * exp (-u))) := by
      rw [Eb, ← hδdef, ← hVdef, ← hudef]; norm_num; ring
    rw [hEb]
    have hA : 0 ≤ δ * (1 + δ) * x ^ 2 := by positivity
    calc (N : ℝ) * δ * (1 + δ) * x ^ 2 * ∑ k ∈ Finset.Icc 2 N, Sk k
        ≤ (L + V + 1) / log 2 * δ * (1 + δ) * x ^ 2 * ∑ k ∈ Finset.Icc 2 N, Sk k := by
          have := mul_le_mul_of_nonneg_right hNle (mul_nonneg hA hSnn)
          nlinarith [this]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hS1
          have := Vp_ge hL
          positivity
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Pfun δ y ^ 2 * weight x V y)
      ≤ ∫⁻ y in Ioi (0 : ℝ), ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, ENNReal.ofReal (T k p y) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (T k p y) := by
        rw [lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun p _ => hmeas k p]
        exact Finset.sum_congr rfl fun k _ => lintegral_finsetSum _ fun p _ => hmeas k p
    _ ≤ ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, ENNReal.ofReal (if exp u < (p : ℝ) ^ k then
          (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun p hp => hwin k hk p hp
    _ = ENNReal.ofReal (∑ k ∈ Finset.Icc 2 N, ∑ p ∈ Pset M, (if exp u < (p : ℝ) ^ k then
          (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0)) := by
        have hnn : ∀ k p : ℕ, 0 ≤ (if exp u < (p : ℝ) ^ k then
            (N : ℝ) * log p ^ 2 * δ * (1 + δ) * x ^ 2 / (p : ℝ) ^ k else 0) := by
          intro k p; split_ifs
          · have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; positivity
          · exact le_refl 0
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun p _ => hnn k p]
        exact Finset.sum_congr rfl fun k _ =>
          (ENNReal.ofReal_sum_of_nonneg fun p _ => hnn k p).symm
    _ ≤ ENNReal.ofReal (δ * x ^ 2 * Eb L) := ENNReal.ofReal_le_ofReal hreal

end GoldbachRH
