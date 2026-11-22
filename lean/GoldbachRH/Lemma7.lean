import GoldbachRH.KernelFourier
import GoldbachRH.Assembly

/-!
# Lemma 7 of the paper: the Schur bound `‖A‖²_ω ≤ x² 𝒯`

Proof, following the paper.
1. *Truncations.* For a finite set `S` of zeros put `A_S(y) = Σ_{ρ∈S} m_ρ c(γ) y^ρ`. The
   explicit formula at `y` and at `(1+δ)y` gives `A_S(y) → -A(y)` along `S = zerosUpTo n`, for
   every `y > 1` outside the countable set where `y` or `(1+δ)y` is an integer.
2. *Fatou.* `‖A‖²_ω ≤ liminf ‖A_S‖²_ω`.
3. *Change of variables* `y = x e^{-v}`. Under RH, `y^ρ = √x e^{-v/2} x^{iγ} e^{-iγv}`, so
   `‖A_S‖²_ω = x² ∫ W(v) |Σ m_ρ β_ρ e^{-iγv}|² dv` with `|β_ρ| = |c(γ)|`.
4. *Expanding the square* and using `∫ W(v) e^{-iθv} dv = Ŵ(θ)`, `Ŵ ≥ 0`, `Ŵ` even and
   `2 Re(β β̄') ≤ |β|² + |β'|²` bounds this by `x² Σ_ρ m_ρ |c|² Σ_{ρ'} m_ρ' Ŵ(γ - γ') ≤ x² 𝒯`.
-/

open Real MeasureTheory Set Filter Topology ComplexConjugate
open scoped ENNReal

namespace GoldbachRH

/-! ### Step 4: the integral in `v` -/

lemma W_neg {V : ℝ} (v : ℝ) : W V (-v) = W V v := by simp [W, abs_neg]

lemma What_neg {V : ℝ} (θ : ℝ) : What V (-θ) = What V θ := by
  simp only [What, neg_mul, cos_neg]

lemma continuous_W {V : ℝ} (hV : 0 < V) : Continuous (W V) :=
  continuous_rad hV continuous_kerProfile kerProfile_one

lemma integrable_W_mul {V : ℝ} (hV : 0 < V) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable fun v => W V v * g v :=
  ((continuous_W hV).mul hg).integrable_of_hasCompactSupport
    ((hasCompactSupport_rad (V := V) (prof := kerProfile)).mul_right)

lemma integral_W_sin {V : ℝ} (θ : ℝ) : ∫ v, W V v * sin (θ * v) = 0 := by
  have h : ∫ v, W V (-v) * sin (θ * -v) = ∫ v, W V v * sin (θ * v) :=
    integral_neg_eq_self (fun v => W V v * sin (θ * v)) volume
  simp only [W_neg, mul_neg, sin_neg, integral_neg] at h
  linarith

lemma norm_sq_sum_eq (S : Finset ℂ) (a : ℂ → ℂ) :
    ‖∑ ρ ∈ S, a ρ‖ ^ 2 = ∑ ρ ∈ S, ∑ ρ' ∈ S, (a ρ * conj (a ρ')).re := by
  have h : ‖∑ ρ ∈ S, a ρ‖ ^ 2 = ((∑ ρ ∈ S, a ρ) * conj (∑ ρ ∈ S, a ρ)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  simp_rw [Complex.re_sum]

/-- The phase `e^{-iγv}`. -/
noncomputable def ph (γ v : ℝ) : ℂ := Complex.exp (((-(γ * v) : ℝ) : ℂ) * Complex.I)

lemma norm_ph (γ v : ℝ) : ‖ph γ v‖ = 1 := by
  unfold ph; exact Complex.norm_exp_ofReal_mul_I _

lemma re_pair (m m' : ℝ) (β β' : ℂ) (γ γ' v : ℝ) :
    ((m : ℂ) * β * ph γ v * conj ((m' : ℂ) * β' * ph γ' v)).re
      = m * m' * ((β * conj β').re * cos ((γ - γ') * v)
        + (β * conj β').im * sin ((γ - γ') * v)) := by
  simp only [ph, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, ← Complex.exp_conj,
    Complex.conj_ofReal, map_mul, Complex.conj_I]
  have e1 : ∀ r : ℝ, (Complex.exp ((r : ℂ) * -Complex.I)).re = cos r := by
    intro r
    rw [show (r : ℂ) * -Complex.I = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, cos_neg]
  have e2 : ∀ r : ℝ, (Complex.exp ((r : ℂ) * -Complex.I)).im = -sin r := by
    intro r
    rw [show (r : ℂ) * -Complex.I = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, sin_neg]
  simp only [e1, e2, cos_neg, sin_neg, sub_mul, cos_sub, sin_sub]
  ring

lemma integral_W_normSq {V : ℝ} (hV : 0 < V) (S : Finset ℂ) (m : ℂ → ℝ) (β : ℂ → ℂ)
    (γ : ℂ → ℝ) :
    ∫ v, W V v * ‖∑ ρ ∈ S, (m ρ : ℂ) * β ρ * ph (γ ρ) v‖ ^ 2
      = ∑ ρ ∈ S, ∑ ρ' ∈ S, m ρ * m ρ' * (β ρ * conj (β ρ')).re * What V (γ ρ - γ ρ') := by
  simp_rw [norm_sq_sum_eq, re_pair, Finset.mul_sum]
  have hc : ∀ ρ ρ' : ℂ, Continuous fun v : ℝ => m ρ * m ρ' * ((β ρ * conj (β ρ')).re *
      cos ((γ ρ - γ ρ') * v) + (β ρ * conj (β ρ')).im * sin ((γ ρ - γ ρ') * v)) := by
    intro ρ ρ'; fun_prop
  rw [integral_finsetSum _ (fun ρ _ => integrable_finsetSum _ fun ρ' _ =>
    integrable_W_mul hV (hc ρ ρ'))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [integral_finsetSum _ (fun ρ' _ => integrable_W_mul hV (hc ρ ρ'))]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  have e : ∀ v, W V v * (m ρ * m ρ' * ((β ρ * conj (β ρ')).re * cos ((γ ρ - γ ρ') * v)
      + (β ρ * conj (β ρ')).im * sin ((γ ρ - γ ρ') * v)))
      = m ρ * m ρ' * (β ρ * conj (β ρ')).re * (W V v * cos ((γ ρ - γ ρ') * v))
        + m ρ * m ρ' * (β ρ * conj (β ρ')).im * (W V v * sin ((γ ρ - γ ρ') * v)) := by
    intro v; ring
  simp_rw [e]
  rw [integral_add ((integrable_W_mul hV (continuous_cos_mul _)).const_mul _)
    ((integrable_W_mul hV (by fun_prop)).const_mul _), integral_const_mul, integral_const_mul,
    integral_W_sin, mul_zero, add_zero]
  rfl

/-- `Σ_ρ Σ_ρ' m m' Re(β β̄') w(γ - γ') ≤ Σ_ρ m |β|² Σ_ρ' m' w(γ - γ')` for `w ≥ 0` even. -/
lemma double_sum_le (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ ρ, 0 ≤ m ρ) (β : ℂ → ℂ) (γ : ℂ → ℝ)
    (w : ℝ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hwe : ∀ θ, w (-θ) = w θ) :
    ∑ ρ ∈ S, ∑ ρ' ∈ S, m ρ * m ρ' * (β ρ * conj (β ρ')).re * w (γ ρ - γ ρ')
      ≤ ∑ ρ ∈ S, m ρ * ‖β ρ‖ ^ 2 * ∑ ρ' ∈ S, m ρ' * w (γ ρ - γ ρ') := by
  have hterm : ∀ ρ ρ', m ρ * m ρ' * (β ρ * conj (β ρ')).re * w (γ ρ - γ ρ')
      ≤ m ρ * m ρ' * ‖β ρ‖ ^ 2 * w (γ ρ - γ ρ') / 2
        + m ρ * m ρ' * ‖β ρ'‖ ^ 2 * w (γ ρ - γ ρ') / 2 := by
    intro ρ ρ'
    have h1 : (β ρ * conj (β ρ')).re ≤ (‖β ρ‖ ^ 2 + ‖β ρ'‖ ^ 2) / 2 := by
      have := Complex.re_le_norm (β ρ * conj (β ρ'))
      rw [norm_mul, Complex.norm_conj] at this
      nlinarith [sq_nonneg (‖β ρ‖ - ‖β ρ'‖)]
    have h2 : 0 ≤ m ρ * m ρ' * w (γ ρ - γ ρ') := mul_nonneg (mul_nonneg (hm ρ) (hm ρ')) (hw0 _)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hswap : ∑ ρ ∈ S, ∑ ρ' ∈ S, m ρ * m ρ' * ‖β ρ'‖ ^ 2 * w (γ ρ - γ ρ') / 2
      = ∑ ρ ∈ S, ∑ ρ' ∈ S, m ρ * m ρ' * ‖β ρ‖ ^ 2 * w (γ ρ - γ ρ') / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
    rw [← hwe, neg_sub]; ring
  calc _ ≤ ∑ ρ ∈ S, ∑ ρ' ∈ S, (m ρ * m ρ' * ‖β ρ‖ ^ 2 * w (γ ρ - γ ρ') / 2
          + m ρ * m ρ' * ‖β ρ'‖ ^ 2 * w (γ ρ - γ ρ') / 2) :=
        Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun ρ' _ => hterm ρ ρ'
    _ = ∑ ρ ∈ S, ∑ ρ' ∈ S, m ρ * m ρ' * ‖β ρ‖ ^ 2 * w (γ ρ - γ ρ') := by
        simp_rw [Finset.sum_add_distrib]
        rw [hswap, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ρ' _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ' _ => ?_
        ring

/-! ### Step 3: change of variables `y = x e^{-v}` -/

lemma image_x_exp_neg {x : ℝ} (hx : 0 < x) : (fun v : ℝ => x * exp (-v)) '' univ = Ioi 0 := by
  ext y
  simp only [mem_image, mem_univ, true_and, mem_Ioi]
  constructor
  · rintro ⟨v, rfl⟩; positivity
  · intro hy
    refine ⟨-log (y / x), ?_⟩
    rw [neg_neg, exp_log (div_pos hy hx)]
    field_simp

lemma lintegral_Ioi_eq {x : ℝ} (hx : 0 < x) (G : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioi (0 : ℝ), G y = ∫⁻ v, ENNReal.ofReal (x * exp (-v)) * G (x * exp (-v)) := by
  have hd : ∀ v ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun v => x * exp (-v)) (-(x * exp (-v))) univ v := by
    intro v _
    have h := ((hasDerivAt_neg v).exp).const_mul x
    convert h.hasDerivWithinAt using 1; ring
  have hinj : InjOn (fun v : ℝ => x * exp (-v)) univ := by
    intro a _ b _ h
    have : exp (-a) = exp (-b) := mul_left_cancel₀ hx.ne' h
    exact neg_inj.1 (exp_injective this)
  have := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj G
  rw [image_x_exp_neg hx, Measure.restrict_univ] at this
  rw [this]
  refine lintegral_congr fun v => ?_
  rw [abs_neg, abs_of_pos (by positivity)]

/-! ### Zeros under RH -/

lemma re_eq_half {ρ : ℂ} (hRH : RiemannHypothesis) (h : IsNontrivialZero ρ) : ρ.re = 1 / 2 := by
  refine hRH ρ h.1 ?_ ?_
  · rintro ⟨n, rfl⟩
    have h1 := h.2.1
    have e : ((-2 * ((n : ℂ) + 1)) : ℂ).re = -2 * ((n : ℝ) + 1) := by simp
    rw [e] at h1
    have := n.cast_nonneg (α := ℝ)
    linarith
  · rintro rfl
    have := h.2.2
    simp at this

lemma eq_half_add {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ = 1 / 2 + (ρ.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [h]

/-- `c_ρ = ((1+δ)^ρ - 1)/ρ`. Under RH this is `c(γ)` (`cz_eq_cco`). -/
noncomputable def cz (δ : ℝ) (ρ : ℂ) : ℂ := ((((1 + δ : ℝ)) : ℂ) ^ ρ - 1) / ρ

lemma cz_eq_cco {δ : ℝ} {ρ : ℂ} (h : ρ.re = 1 / 2) : cz δ ρ = cco δ ρ.im := by
  rw [cco, ← eq_half_add h]; rfl

/-- The truncated sum over zeros `A_S(y) = Σ_{ρ∈S} m_ρ c_ρ y^ρ`. -/
noncomputable def AS (δ : ℝ) (S : Finset ℂ) (y : ℝ) : ℂ :=
  ∑ ρ ∈ S, (zeroMult ρ : ℂ) * cz δ ρ * (y : ℂ) ^ ρ

lemma cpow_x_exp {x v : ℝ} (hx : 0 < x) {ρ : ℂ} (h : ρ.re = 1 / 2) :
    (((x * exp (-v)) : ℝ) : ℂ) ^ ρ = (x : ℂ) ^ ρ * ((exp (-v / 2) : ℝ) : ℂ) * ph ρ.im v := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (exp_pos _).le, mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (exp_pos (-v)).ne'),
    ← Complex.ofReal_log (exp_pos _).le, log_exp, ph, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [eq_half_add h]
  push_cast; ring

/-! ### Step 3–4: the integral of a truncation -/

lemma weight_x_exp {x V v : ℝ} (hx : 0 < x) :
    weight x V (x * exp (-v)) = exp v ^ 2 * W V v := by
  unfold weight
  have : x / (x * exp (-v)) = exp v := by rw [exp_neg]; field_simp
  rw [this, log_exp]

lemma finset_le_zsum (S : Finset ℂ) (hS : ∀ ρ ∈ S, IsNontrivialZero ρ) (f : ℂ → ℝ≥0∞) :
    ∑ ρ ∈ S, (zeroMult ρ : ℝ≥0∞) * f ρ ≤ zsum f := by
  classical
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_tsum (f := fun ρ : {ρ : ℂ // IsNontrivialZero ρ} =>
    (zeroMult ρ : ℝ≥0∞) * f ρ) _

/-- **Steps 3–4.** For a finite set `S` of nontrivial zeros, under RH,
`‖A_S‖²_ω ≤ x² 𝒯`. -/
lemma lintegral_AS_le {x V δ : ℝ} (hRH : RiemannHypothesis) (hx : 0 < x) (hV : 0 < V)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, IsNontrivialZero ρ) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖AS δ S y‖ ^ 2 * weight x V y)
      ≤ ENNReal.ofReal (x ^ 2) * Tsum δ V := by
  have hre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => re_eq_half hRH (hS ρ hρ)
  set m : ℂ → ℝ := fun ρ => (zeroMult ρ : ℝ) with hm
  set β : ℂ → ℂ := fun ρ => cz δ ρ * (x : ℂ) ^ ρ / ((√x : ℝ) : ℂ) with hβ
  set Sv : ℝ → ℂ := fun v => ∑ ρ ∈ S, (m ρ : ℂ) * β ρ * ph ρ.im v with hSv
  have hsx : 0 < √x := sqrt_pos.2 hx
  -- `A_S(x e^{-v}) = √x e^{-v/2} Σ(v)`
  have hAS : ∀ v, AS δ S (x * exp (-v)) = ((√x * exp (-v / 2) : ℝ) : ℂ) * Sv v := by
    intro v
    simp only [AS, hSv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [cpow_x_exp hx (hre ρ hρ), hβ, hm]
    have : ((√x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsx.ne'
    push_cast
    field_simp
  have hpt : ∀ v, ENNReal.ofReal (x * exp (-v))
      * ENNReal.ofReal (‖AS δ S (x * exp (-v))‖ ^ 2 * weight x V (x * exp (-v)))
      = ENNReal.ofReal (x ^ 2 * (W V v * ‖Sv v‖ ^ 2)) := by
    intro v
    rw [← ENNReal.ofReal_mul (by positivity), hAS, weight_x_exp hx, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    congr 1
    have h1 : √x ^ 2 = x := sq_sqrt hx.le
    have h2 : exp (-v / 2) ^ 2 = exp (-v) := by rw [← exp_nat_mul]; congr 1; push_cast; ring
    have h3 : exp (-v) * exp v = 1 := by rw [← exp_add]; simp
    calc x * exp (-v) * ((√x * exp (-v / 2) * ‖Sv v‖) ^ 2 * (exp v ^ 2 * W V v))
        = x * (√x ^ 2) * (exp (-v) * exp v) ^ 2 * (W V v * ‖Sv v‖ ^ 2) := by
          rw [mul_pow, mul_pow, h2]; ring
      _ = _ := by rw [h1, h3]; ring
  have hSvc : Continuous fun v => ‖Sv v‖ ^ 2 := by
    simp only [hSv, ph]; fun_prop
  have hint : Integrable fun v => x ^ 2 * (W V v * ‖Sv v‖ ^ 2) :=
    (integrable_W_mul hV hSvc).const_mul _
  have hnn : 0 ≤ᵐ[volume] fun v => x ^ 2 * (W V v * ‖Sv v‖ ^ 2) :=
    Filter.Eventually.of_forall fun v => by have := W_nonneg hV v; positivity
  -- the bound in `v`
  have hnormβ : ∀ ρ ∈ S, ‖β ρ‖ = ‖cz δ ρ‖ := by
    intro ρ hρ
    rw [hβ, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre ρ hρ,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsx, ← sqrt_eq_rpow, mul_div_assoc,
      div_self hsx.ne', mul_one]
  have hW : ∫ v, W V v * ‖Sv v‖ ^ 2
      ≤ ∑ ρ ∈ S, m ρ * ‖cz δ ρ‖ ^ 2 * ∑ ρ' ∈ S, m ρ' * What V (ρ.im - ρ'.im) := by
    rw [integral_W_normSq hV S m β (fun ρ => ρ.im)]
    refine (double_sum_le S m (fun ρ => Nat.cast_nonneg _) β (fun ρ => ρ.im) (What V)
      (What_nonneg hV) What_neg).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [hnormβ ρ hρ]
  have hRHS0 : 0 ≤ ∑ ρ ∈ S, m ρ * ‖cz δ ρ‖ ^ 2 * ∑ ρ' ∈ S, m ρ' * What V (ρ.im - ρ'.im) :=
    Finset.sum_nonneg fun ρ _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (What_nonneg hV _))
  -- comparison with `𝒯`
  have hT : ENNReal.ofReal (∑ ρ ∈ S, m ρ * ‖cz δ ρ‖ ^ 2 *
      ∑ ρ' ∈ S, m ρ' * What V (ρ.im - ρ'.im)) ≤ Tsum δ V := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ρ _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (What_nonneg hV _))]
    refine le_trans (Finset.sum_le_sum fun ρ hρ => ?_) (finset_le_zsum S hS _)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast, mul_assoc]
    gcongr
    · rw [cz_eq_cco (hre ρ hρ), Complex.normSq_eq_norm_sq]
    · rw [ENNReal.ofReal_sum_of_nonneg fun ρ' _ =>
        mul_nonneg (Nat.cast_nonneg _) (What_nonneg hV _)]
      refine le_trans (Finset.sum_le_sum fun ρ' _ => ?_) (finset_le_zsum S hS _)
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖AS δ S y‖ ^ 2 * weight x V y)
      = ∫⁻ v, ENNReal.ofReal (x ^ 2 * (W V v * ‖Sv v‖ ^ 2)) := by
        rw [lintegral_Ioi_eq hx]; exact lintegral_congr hpt
    _ = ENNReal.ofReal (x ^ 2 * ∫ v, W V v * ‖Sv v‖ ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul]
    _ ≤ ENNReal.ofReal (x ^ 2 * ∑ ρ ∈ S, m ρ * ‖cz δ ρ‖ ^ 2 *
          ∑ ρ' ∈ S, m ρ' * What V (ρ.im - ρ'.im)) := by gcongr
    _ = ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (∑ ρ ∈ S, m ρ * ‖cz δ ρ‖ ^ 2 *
          ∑ ρ' ∈ S, m ρ' * What V (ρ.im - ρ'.im)) := ENNReal.ofReal_mul (sq_nonneg x)
    _ ≤ _ := by gcongr

/-! ### Steps 1–2: the truncations converge to `-A`, and Fatou -/

lemma AS_eq_diff {δ : ℝ} (hδ : 0 ≤ δ) (S : Finset ℂ) {y : ℝ} (hy : 0 ≤ y) :
    AS δ S y = ∑ ρ ∈ S, (zeroMult ρ : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ ρ / ρ)
      - ∑ ρ ∈ S, (zeroMult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by linarith) hy, cz]
  ring

/-- **Step 1.** By the explicit formula at `y` and `(1+δ)y`, `A_S(y) → -A(y)`. -/
lemma tendsto_AS (hEF : ExplicitFormulaPsi) {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 1 < y)
    (h1 : ∀ n : ℕ, y ≠ n) (h2 : ∀ n : ℕ, (1 + δ) * y ≠ n) :
    Tendsto (fun T : ℝ => AS δ (zerosUpTo T) y) atTop (𝓝 (-(Afun δ y : ℂ))) := by
  have hy2 : 1 < (1 + δ) * y := by nlinarith
  have h := (hEF _ hy2 h2).sub (hEF y hy h1)
  simp_rw [AS_eq_diff hδ _ (by linarith : (0 : ℝ) ≤ y)]
  convert h using 2
  rw [← Complex.ofReal_sub, ← Complex.ofReal_neg]
  congr 1
  unfold Afun Vψ Bfun
  rw [mul_pow]
  ring

/-- **Lemma 7.** Under RH and the explicit formula, `‖A‖²_ω ≤ x² 𝒯`. -/
theorem lemma7 : Lemma7 := by
  intro hRH hEF x V δ hx hV hδ hy0
  have hδ1 : (1 + δ) ≠ 0 := by positivity
  set F : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ENNReal.ofReal (‖AS δ (zerosUpTo n) y‖ ^ 2 * weight x V y) with hFdef
  have hmeas : ∀ n, Measurable (F n) := by
    intro n
    have hA : Measurable fun y : ℝ => AS δ (zerosUpTo n) y := by simp only [AS]; fun_prop
    exact ENNReal.measurable_ofReal.comp ((hA.norm.pow_const 2).mul (measurable_weight x V))
  set N : Set ℝ := range (fun n : ℕ => (n : ℝ)) ∪ range (fun n : ℕ => (n : ℝ) / (1 + δ))
  have hNc : N.Countable := (countable_range _).union (countable_range _)
  have hlim : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      liminf (fun n => F n y) atTop = ENNReal.ofReal (Afun δ y ^ 2 * weight x V y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (hNc.ae_notMem volume)] with y hy hyN
    have hy : 0 < y := hy
    by_cases hyy : y ≤ x * exp (-V)
    · have hw := weight_eq_zero hx hV hy hyy
      simp only [hFdef, hw, mul_zero, ENNReal.ofReal_zero, liminf_const]
    · push Not at hyy
      have hy1 : 1 < y := lt_trans hy0 hyy
      have h1 : ∀ n : ℕ, y ≠ n := fun n h => hyN (Or.inl ⟨n, h.symm⟩)
      have h2 : ∀ n : ℕ, (1 + δ) * y ≠ n := fun n h =>
        hyN (Or.inr ⟨n, by show (n : ℝ) / (1 + δ) = y; rw [← h, mul_div_cancel_left₀ _ hδ1]⟩)
      have hT := (tendsto_AS hEF hδ hy1 h1 h2).comp tendsto_natCast_atTop_atTop
      have hF : Tendsto (fun n => F n y) atTop
          (𝓝 (ENNReal.ofReal (Afun δ y ^ 2 * weight x V y))) := by
        have h3 := (((continuous_norm.tendsto _).comp hT).pow 2).mul_const (weight x V y)
        have h4 := (ENNReal.continuous_ofReal.tendsto _).comp h3
        simpa [hFdef, Function.comp_def, norm_neg, Complex.norm_real, sq_abs] using h4
      exact hF.liminf_eq
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Afun δ y ^ 2 * weight x V y)
      = ∫⁻ y in Ioi (0 : ℝ), liminf (fun n => F n y) atTop := (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun n => ∫⁻ y in Ioi (0 : ℝ), F n y) atTop :=
        lintegral_liminf_le' fun n => (hmeas n).aemeasurable
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall fun n =>
        lintegral_AS_le hRH hx hV _ fun ρ hρ =>
          ((finite_zerosUpTo _).mem_toFinset.1 hρ).1).frequently

end GoldbachRH
