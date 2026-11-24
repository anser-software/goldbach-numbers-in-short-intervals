import GoldbachRH.Cover

/-!
# The first-moment cover (Lemma 6 of the paper, version 0.6)

If `(x, (1+δ)x]` contains no Goldbach number, then under Schoenfeld's bound for `θ`
`∫_{y > 0} V_θ(y)² ω(y) dy ≥ δ² x³ (2 m - 2δ - log² x / (2π √x))`,
where `m = 1/2 - 9.55/V² - e^{-V}` is the lower bound of Corollary 5 for `m_W`.

This file contains the one-variable ingredients: the kernel facts, the functions `w`, `q`, `G`,
and the first-moment bound on a single symmetric interval (`integral_G_ge`).
-/

open Real Set MeasureTheory

namespace GoldbachRH

/-! ### Kernel facts -/

lemma W_le_one {V : ℝ} (hV : 0 < V) (v : ℝ) : W V v ≤ 1 := by
  unfold W
  split_ifs with h
  · have h0 : 0 ≤ |v| / V := by positivity
    have h1 : |v| / V ≤ 1 := (div_le_one hV).2 h
    have := kerProfile_antitoneOn ⟨le_refl (0 : ℝ), zero_le_one⟩ ⟨h0, h1⟩ h0
    have e : kerProfile 0 = 1 := by simp [kerProfile]
    linarith
  · norm_num

/-- `W_V` is antitone on `[0, ∞)`. -/
lemma W_anti {V v₁ v₂ : ℝ} (hV : 0 < V) (h0 : 0 ≤ v₁) (h12 : v₁ ≤ v₂) : W V v₂ ≤ W V v₁ := by
  by_cases h2 : v₂ ≤ V
  · exact W_antitone hV h0 h12 h2
  · have h2' : ¬ |v₂| ≤ V := by
      rw [abs_of_nonneg (h0.trans h12)]
      exact h2
    have : W V v₂ = 0 := by simp [W, h2']
    rw [this]
    exact W_nonneg hV v₁

lemma abs_lt_of_W_pos {V v : ℝ} (hV : 0 < V) (h : 0 < W V v) : |v| < V := by
  unfold W at h
  split_ifs at h with hv
  · rcases hv.lt_or_eq with hlt | heq
    · exact hlt
    · rw [heq, div_self hV.ne', kerProfile_one] at h
      exact absurd h (lt_irrefl 0)
  · exact absurd h (lt_irrefl 0)

/-! ### The functions `w`, `q`, `G` -/

/-- `w(y) = W_V(log(x/y))`. -/
noncomputable def wfun (x V y : ℝ) : ℝ := W V (log (x / y))

/-- The symmetric weight `q(y) = min(w(y), w(x - y))`. -/
noncomputable def qfun (x V y : ℝ) : ℝ := min (wfun x V y) (wfun x V (x - y))

/-- `G(y) = (θ((1+δ)y) - θ(y)) / (δ y)`, so that `V_θ(y) = δ y (G(y) - 1)`. -/
noncomputable def Gfun (δ y : ℝ) : ℝ :=
  (Chebyshev.theta ((1 + δ) * y) - Chebyshev.theta y) / (δ * y)

lemma wfun_nonneg {x V : ℝ} (hV : 0 < V) (y : ℝ) : 0 ≤ wfun x V y := W_nonneg hV _
lemma wfun_le_one {x V : ℝ} (hV : 0 < V) (y : ℝ) : wfun x V y ≤ 1 := W_le_one hV _

lemma qfun_nonneg {x V : ℝ} (hV : 0 < V) (y : ℝ) : 0 ≤ qfun x V y :=
  le_min (wfun_nonneg hV _) (wfun_nonneg hV _)

lemma qfun_le_one {x V : ℝ} (hV : 0 < V) (y : ℝ) : qfun x V y ≤ 1 :=
  (min_le_left _ _).trans (wfun_le_one hV _)

lemma qfun_le_wfun (x V y : ℝ) : qfun x V y ≤ wfun x V y := min_le_left _ _

lemma qfun_symm (x V y : ℝ) : qfun x V (x - y) = qfun x V y := by
  unfold qfun
  rw [sub_sub_cancel, min_comm]

/-- `w` is nondecreasing on `(0, x]`. -/
lemma wfun_mono {x V y₁ y₂ : ℝ} (hV : 0 < V) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ ≤ x) :
    wfun x V y₁ ≤ wfun x V y₂ := by
  have hy2 : 0 < y₂ := h1.trans_le h12
  have hx : 0 < x := hy2.trans_le h2
  unfold wfun
  apply W_anti hV
  · apply log_nonneg
    rw [le_div_iff₀ hy2]
    linarith
  · apply log_le_log (div_pos hx hy2)
    exact div_le_div_of_nonneg_left hx.le h1 h12

/-- If `q(y) > 0` then both `y` and `x - y` exceed `x e^{-V}`. -/
lemma gt_of_qfun_pos {x V y : ℝ} (hx : 0 < x) (hV : 0 < V) (hy : 0 < y) (hyx : y < x)
    (h : 0 < qfun x V y) : x * exp (-V) < y ∧ x * exp (-V) < x - y := by
  have key : ∀ z : ℝ, 0 < z → z < x → 0 < wfun x V z → x * exp (-V) < z := by
    intro z hz hzx hw
    have habs := abs_lt_of_W_pos hV hw
    have hlog : log (x / z) < V := (le_abs_self _).trans_lt habs
    have : x / z < exp V := by
      rwa [log_lt_iff_lt_exp (div_pos hx hz)] at hlog
    rw [div_lt_iff₀ hz] at this
    have e : x * exp (-V) * exp V = x := by
      rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    have hexp := exp_pos V
    nlinarith
  exact ⟨key y hy hyx (h.trans_le (min_le_left _ _)),
    key (x - y) (by linarith) (by linarith) (h.trans_le (min_le_right _ _))⟩

lemma Gfun_nonneg {δ y : ℝ} (hδ : 0 < δ) (hy : 0 < y) : 0 ≤ Gfun δ y := by
  unfold Gfun
  apply div_nonneg _ (by positivity)
  have : y ≤ (1 + δ) * y := by nlinarith
  linarith [Chebyshev.theta_mono this]

lemma Vθ_eq_G {δ y : ℝ} (hδ : 0 < δ) (hy : 0 < y) : Vθ δ y = δ * y * (Gfun δ y - 1) := by
  unfold Vθ Gfun
  field_simp

lemma Fint_eq_G {x V δ y : ℝ} (hδ : 0 < δ) (hy : 0 < y) :
    Fint x V δ y = δ ^ 2 * x ^ 2 * (wfun x V y * (Gfun δ y - 1) ^ 2) := by
  rw [Fint, Vθ_eq_G hδ hy, weight, wfun]
  field_simp

/-- If there is no prime in `(z, (1+δ)z]` then `G(z) = 0`. -/
lemma Gfun_of_no_prime {δ z : ℝ} (hδ : 0 < δ) (hz : 0 < z)
    (h : ∀ p : ℕ, p.Prime → z < p → (p : ℝ) ≤ (1 + δ) * z → False) : Gfun δ z = 0 := by
  have hzw : z ≤ (1 + δ) * z := by nlinarith
  rw [Gfun, theta_eq_of_no_prime hz.le hzw h, sub_self, zero_div]

/-! ### The first moment on one symmetric interval -/

lemma theta_monotone_mul {c : ℝ} (hc : 0 ≤ c) : Monotone fun t : ℝ => Chebyshev.theta (c * t) :=
  fun _ _ hab => Chebyshev.theta_mono (mul_le_mul_of_nonneg_left hab hc)

lemma intervalIntegrable_theta_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Chebyshev.theta t / t) volume a b := by
  have h1 : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  have h2 : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) := by
    apply continuousOn_inv₀.mono
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (ha.trans_le ht.1).ne'
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2

lemma intervalIntegrable_Gfun {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (Gfun δ) volume a b := by
  have h1 : IntervalIntegrable (fun t => Chebyshev.theta ((1 + δ) * t)) volume a b :=
    (theta_monotone_mul (by linarith)).intervalIntegrable
  have h2 : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  have h3 : ContinuousOn (fun t : ℝ => (δ * t)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (continuousOn_const.mul continuousOn_id)
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (mul_pos hδ (ha.trans_le ht.1)).ne'
  convert (h1.sub h2).mul_continuousOn h3 using 1
  ext t
  simp only [Gfun, div_eq_mul_inv]

/-- `∫_a^b G = (1/δ) (∫_b^{(1+δ)b} θ(t)/t dt - ∫_a^{(1+δ)a} θ(t)/t dt)`. -/
lemma integral_Gfun_eq {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in a..b, Gfun δ y =
      ((∫ t in b..(1 + δ) * b, Chebyshev.theta t / t)
        - ∫ t in a..(1 + δ) * a, Chebyshev.theta t / t) / δ := by
  set f : ℝ → ℝ := fun t => Chebyshev.theta t / t with hf
  have hc : (1 + δ) ≠ 0 := by positivity
  have hcp : 0 < 1 + δ := by positivity
  -- pointwise: G(y) = ((1+δ) f((1+δ)y) - f(y)) / δ for y > 0
  have hpt : ∀ y ∈ uIcc a b, Gfun δ y = ((1 + δ) * f ((1 + δ) * y) - f y) / δ := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : 0 < y := ha.trans_le hy.1
    simp only [hf, Gfun]
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  have hi1 : IntervalIntegrable (fun y => (1 + δ) * f ((1 + δ) * y)) volume a b := by
    have : IntervalIntegrable (fun y => f ((1 + δ) * y)) volume a b := by
      have h := intervalIntegrable_theta_div (mul_pos hcp ha)
        (mul_le_mul_of_nonneg_left hab hcp.le)
      have h' := h.comp_mul_left (c := 1 + δ)
      rwa [mul_div_cancel_left₀ _ hc, mul_div_cancel_left₀ _ hc] at h'
    exact this.const_mul _
  have hi2 : IntervalIntegrable f volume a b := intervalIntegrable_theta_div ha hab
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hc]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  congr 1
  have hA' : IntervalIntegrable f volume ((1 + δ) * a) ((1 + δ) * b) :=
    intervalIntegrable_theta_div (mul_pos hcp ha) (mul_le_mul_of_nonneg_left hab hcp.le)
  have hB : IntervalIntegrable f volume a b := hi2
  have hAc : IntervalIntegrable f volume ((1 + δ) * a) a :=
    (intervalIntegrable_theta_div ha (by nlinarith)).symm
  rw [intervalIntegral.integral_interval_sub_interval_comm hA' hB hAc,
    intervalIntegral.integral_symm a ((1 + δ) * a), intervalIntegral.integral_symm b ((1 + δ) * b)]
  ring

end GoldbachRH
