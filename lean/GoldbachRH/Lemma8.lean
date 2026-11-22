import GoldbachRH.Zeros
import GoldbachRH.Cover

/-!
# Lemma 8 of the paper: the term `B`

If `y₀ = x e^{-V} ≥ 3`, then `‖B‖²_ω ≤ (4/5) δ² x² y₀⁻⁵`.
-/

open Real MeasureTheory Set
open scoped ENNReal

namespace GoldbachRH

lemma W_le_one {V : ℝ} (hV : 0 < V) (v : ℝ) : W V v ≤ 1 := by
  unfold W
  split_ifs with h
  · have h0 : 0 ≤ |v| / V := div_nonneg (abs_nonneg v) hV.le
    have h1 : |v| / V ≤ 1 := (div_le_one hV).2 h
    have := kerProfile_antitoneOn ⟨le_refl 0, zero_le_one⟩ ⟨h0, h1⟩ h0
    have h00 : kerProfile 0 = 1 := by simp [kerProfile]
    linarith
  · norm_num

lemma W_eq_zero_of_le {V v : ℝ} (hV : 0 < V) (hv : V ≤ v) : W V v = 0 := by
  unfold W
  split_ifs with h
  · have : |v| = V := le_antisymm h (hv.trans (le_abs_self v))
    rw [this, div_self hV.ne', kerProfile_one]
  · rfl

/-- The weight vanishes for `0 < y ≤ x e^{-V}`. -/
lemma weight_eq_zero {x V y : ℝ} (hx : 0 < x) (hV : 0 < V) (hy : 0 < y)
    (hy0 : y ≤ x * exp (-V)) : weight x V y = 0 := by
  unfold weight
  have hxy : exp V ≤ x / y := by
    rw [le_div_iff₀ hy]
    calc exp V * y ≤ exp V * (x * exp (-V)) := by gcongr
      _ = x := by rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
  have : V ≤ log (x / y) := by
    rw [le_log_iff_exp_le (by positivity)]; exact hxy
  rw [W_eq_zero_of_le hV this, mul_zero]

lemma weight_le {x V y : ℝ} (hV : 0 < V) : weight x V y ≤ (x / y) ^ 2 := by
  unfold weight
  have := W_le_one hV (log (x / y))
  have h2 : 0 ≤ (x / y) ^ 2 := sq_nonneg _
  nlinarith

/-- `|B(y)| ≤ 2δ/y²` for `y ≥ 3`. -/
lemma abs_Bfun_le {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 3 ≤ y) : |Bfun δ y| ≤ 2 * δ / y ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hy2 : 9 ≤ y ^ 2 := by nlinarith
  set b := 1 / y ^ 2 with hb
  set a := 1 / ((1 + δ) ^ 2 * y ^ 2) with ha
  have hb0 : 0 < b := by positivity
  have hb9 : b ≤ 1 / 9 := by
    rw [hb]; exact one_div_le_one_div_of_le (by norm_num) hy2
  have hd1 : 1 ≤ (1 + δ) ^ 2 := by nlinarith
  have hab : a = b / (1 + δ) ^ 2 := by rw [ha, hb]; field_simp
  have ha0 : 0 < a := by positivity
  have hale : a ≤ b := by rw [hab]; exact div_le_self hb0.le hd1
  have hba : b - a ≤ 2 * δ * b := by
    have : b - 2 * δ * b ≤ a := by
      rw [hab, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hb0.le (sq_nonneg δ), mul_nonneg hb0.le (pow_nonneg hδ 3)]
    linarith
  have hpos : 0 < 1 - b := by linarith
  have h1 : log (1 - a) - log (1 - b) ≤ (b - a) / (1 - b) := by
    rw [← log_div (by linarith) hpos.ne']
    have := log_le_sub_one_of_pos (x := (1 - a) / (1 - b)) (div_pos (by linarith) hpos)
    have e : (1 - a) / (1 - b) - 1 = (b - a) / (1 - b) := by field_simp; ring
    linarith
  have h2 : 0 ≤ log (1 - a) - log (1 - b) :=
    sub_nonneg.2 (log_le_log hpos (by linarith))
  have h3 : (b - a) / (1 - b) ≤ 9 / 8 * (b - a) := by
    rw [div_le_iff₀ hpos]; nlinarith
  have hB : Bfun δ y = -(log (1 - a) - log (1 - b)) / 2 := by unfold Bfun; rw [← ha, ← hb]; ring
  rw [hB, abs_div, abs_neg, abs_of_nonneg h2, abs_two, show 2 * δ / y ^ 2 = 2 * δ * b by
    rw [hb]; ring]
  nlinarith

/-- **Lemma 8.** If `y₀ = x e^{-V} ≥ 3`, then `‖B‖²_ω ≤ (4/5) δ² x² y₀⁻⁵`. -/
theorem lemma8 {x V δ : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 ≤ δ) (hy0 : 3 ≤ x * exp (-V)) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Bfun δ y ^ 2 * weight x V y)
      ≤ ENNReal.ofReal (4 / 5 * δ ^ 2 * x ^ 2 / (x * exp (-V)) ^ 5) := by
  set y0 := x * exp (-V) with hy0def
  have hy00 : 0 < y0 := by linarith
  set C := 4 * δ ^ 2 * x ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set G : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (C * y ^ (-6 : ℝ)) with hG
  -- pointwise bound
  have hpt : ∀ y ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (Bfun δ y ^ 2 * weight x V y) ≤ (Ioi y0).indicator G y := by
    intro y hy
    have hy : 0 < y := hy
    by_cases h : y0 < y
    · rw [indicator_of_mem (show y ∈ Ioi y0 from h), hG]
      apply ENNReal.ofReal_le_ofReal
      have hB := abs_Bfun_le hδ (show 3 ≤ y by linarith)
      have hB2 : Bfun δ y ^ 2 ≤ (2 * δ / y ^ 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      have hw := weight_le (x := x) (y := y) hV
      have hw0 := weight_nonneg (x := x) hV y
      have hr : y ^ (-6 : ℝ) = 1 / y ^ 6 := by
        rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, rpow_neg hy.le, rpow_natCast, one_div]
      calc Bfun δ y ^ 2 * weight x V y ≤ (2 * δ / y ^ 2) ^ 2 * (x / y) ^ 2 := by
            gcongr
        _ = C * y ^ (-6 : ℝ) := by rw [hr, hC]; field_simp; ring
    · rw [indicator_of_notMem (show y ∉ Ioi y0 from h),
        weight_eq_zero hx hV hy (not_lt.1 h), mul_zero, ENNReal.ofReal_zero]
  -- the integral of `C y^{-6}` over `(y₀, ∞)`
  have hint : IntegrableOn (fun y : ℝ => C * y ^ (-6 : ℝ)) (Ioi y0) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hy00).const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi y0)] fun y : ℝ => C * y ^ (-6 : ℝ) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy =>
      mul_nonneg hC0 (rpow_nonneg (le_trans hy00.le (le_of_lt hy)) _))
  have hval : ∫ y in Ioi y0, C * y ^ (-6 : ℝ) = 4 / 5 * δ ^ 2 * x ^ 2 / y0 ^ 5 := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy00,
      show (-6 : ℝ) + 1 = -((5 : ℕ) : ℝ) by norm_num, rpow_neg hy00.le, rpow_natCast, hC]
    field_simp
    ring
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Bfun δ y ^ 2 * weight x V y)
      ≤ ∫⁻ y in Ioi (0 : ℝ), (Ioi y0).indicator G y := setLIntegral_mono' measurableSet_Ioi hpt
    _ ≤ ∫⁻ y, (Ioi y0).indicator G y := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y in Ioi y0, G y := lintegral_indicator measurableSet_Ioi _
    _ = ENNReal.ofReal (∫ y in Ioi y0, C * y ^ (-6 : ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = _ := by rw [hval]

end GoldbachRH
