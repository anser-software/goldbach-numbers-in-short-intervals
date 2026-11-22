import GoldbachRH.Defs

/-!
# The kernel (Lemma 4 (i) and (iv) of the paper: the parts used by the cover argument)

For `V > 0` and `0 ≤ v ≤ V`:
* `W_V(v) ≥ 0`;
* `W_V` is nonincreasing on `[0, V]`;
* (K1) `W_V(v) ≥ 1 - π² v² / (2V²)`.
-/

open Real Set

namespace GoldbachRH

lemma hasDerivAt_kerProfile (t : ℝ) :
    HasDerivAt kerProfile (-(π * (1 - t) * sin (π * t))) t := by
  have hm : HasDerivAt (fun t : ℝ => π * t) π t := by
    simpa using (hasDerivAt_id t).const_mul π
  have hc : HasDerivAt (fun t : ℝ => cos (π * t)) (-sin (π * t) * π) t :=
    (Real.hasDerivAt_cos (π * t)).comp t hm
  have hs : HasDerivAt (fun t : ℝ => sin (π * t)) (cos (π * t) * π) t :=
    (Real.hasDerivAt_sin (π * t)).comp t hm
  have hl : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h := (hl.mul hc).add (hs.div_const π)
  have hfun : kerProfile = (fun t => (1 - t) * cos (π * t) + sin (π * t) / π) := rfl
  rw [hfun]
  convert h using 1
  field_simp
  ring

lemma continuous_kerProfile : Continuous kerProfile := by
  unfold kerProfile; fun_prop

lemma sin_pi_mul_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ sin (π * t) :=
  sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])

lemma kerProfile_antitoneOn : AntitoneOn kerProfile (Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) continuous_kerProfile.continuousOn
  · intro t _; exact (hasDerivAt_kerProfile t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_kerProfile t).deriv]
    have := sin_pi_mul_nonneg ht.1.le ht.2.le
    have : 0 ≤ π * (1 - t) := by nlinarith [pi_pos, ht.2]
    nlinarith

lemma kerProfile_one : kerProfile 1 = 0 := by simp [kerProfile]

lemma kerProfile_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ kerProfile t := by
  have := kerProfile_antitoneOn ⟨h0, h1⟩ ⟨zero_le_one, le_rfl⟩ h1
  rwa [kerProfile_one] at this

/-- (K1) for the profile: `φ(t) ≥ 1 - π² t² / 2` on `[0, 1]`. -/
lemma kerProfile_K1 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 1 - π ^ 2 * t ^ 2 / 2 ≤ kerProfile t := by
  set g : ℝ → ℝ := fun t => kerProfile t - 1 + π ^ 2 * t ^ 2 / 2 with hg
  have hgd : ∀ t, HasDerivAt g (-(π * (1 - t) * sin (π * t)) + π ^ 2 * t) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => π ^ 2 * t ^ 2 / 2) (π ^ 2 * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (π ^ 2)).div_const 2
      convert this using 1; push_cast; ring
    exact ((hasDerivAt_kerProfile t).sub_const 1).add h2
  have hmono : MonotoneOn g (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (continuous_kerProfile.sub continuous_const).add (by fun_prop) |>.continuousOn
    · intro t _; exact (hgd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgd t).deriv]
      have hs0 := sin_pi_mul_nonneg ht.1.le ht.2.le
      have hs1 : sin (π * t) ≤ π * t := sin_le (by nlinarith [pi_pos, ht.1])
      have hp := pi_pos
      have : π * (1 - t) * sin (π * t) ≤ π * sin (π * t) := by
        have : 0 ≤ π * t * sin (π * t) := by nlinarith [ht.1]
        nlinarith
      nlinarith
  have h := hmono ⟨le_rfl, zero_le_one⟩ ⟨h0, h1⟩ h0
  have hg0 : g 0 = 0 := by simp [hg, kerProfile]
  have hgt : g t = kerProfile t - 1 + π ^ 2 * t ^ 2 / 2 := rfl
  linarith

lemma W_of_mem {V v : ℝ} (_hV : 0 < V) (h0 : 0 ≤ v) (h1 : v ≤ V) : W V v = kerProfile (v / V) := by
  simp [W, abs_of_nonneg h0, h1]

lemma W_nonneg {V : ℝ} (hV : 0 < V) (v : ℝ) : 0 ≤ W V v := by
  unfold W
  split_ifs with h
  · exact kerProfile_nonneg (div_nonneg (abs_nonneg v) hV.le) ((div_le_one hV).2 h)
  · exact le_rfl

lemma W_antitone {V v₁ v₂ : ℝ} (hV : 0 < V) (h0 : 0 ≤ v₁) (h12 : v₁ ≤ v₂) (h2 : v₂ ≤ V) :
    W V v₂ ≤ W V v₁ := by
  rw [W_of_mem hV h0 (h12.trans h2), W_of_mem hV (h0.trans h12) h2]
  apply kerProfile_antitoneOn ⟨div_nonneg h0 hV.le, (div_le_one hV).2 (h12.trans h2)⟩
    ⟨div_nonneg (h0.trans h12) hV.le, (div_le_one hV).2 h2⟩
  exact div_le_div_of_nonneg_right h12 hV.le

/-- (K1): `W_V(v) ≥ 1 - π² v² / (2V²)` for `0 ≤ v ≤ V`. -/
lemma W_K1 {V v : ℝ} (hV : 0 < V) (h0 : 0 ≤ v) (h1 : v ≤ V) :
    1 - π ^ 2 / (2 * V ^ 2) * v ^ 2 ≤ W V v := by
  rw [W_of_mem hV h0 h1]
  have := kerProfile_K1 (div_nonneg h0 hV.le) ((div_le_one hV).2 h1)
  convert this using 1
  field_simp

end GoldbachRH
