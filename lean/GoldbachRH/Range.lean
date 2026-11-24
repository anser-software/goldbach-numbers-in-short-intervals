import GoldbachRH.ExpBounds

/-!
# The range argument (§8 of the paper)

For every `L ≥ 42.8` (version 0.6: `H = L²`, `δ = L²/x`),
`(√𝒯 + √ℰ + √ℬ)² < L² (2m - 2δ - L²/(2π e^{L/2}))`, with `m = 1/2 - 9.55/V² - e^{-V}`,
where `𝒯, ℰ, ℬ` are the Table 1 bounds `Tb L`, `Eb L`, `Bb L` and `V = 3√L`.
The right side is `1/H` times the first-moment cover bound of Lemma 6 (`√x = e^{L/2}`).

The route is cruder than the paper's `𝓜 > 𝓡̃` comparison but needs no derivatives:
* `𝒯 ≤ L² - 4 L + 2.91`, using `γ > 1/2`, `log L ≤ 4(L^{1/4} - 1)` and `R_T ≤ 1`;
* `L² ℰ ≤ 140`, `L² ℬ ≤ 5` and `L² δ ≤ 5.62`, using the monotonicity of `uᵏ e^{-cu}` for
  `u ≥ 23.15`, and `L⁴ e^{-L/2} ≤ 1`.
-/

open Real

namespace GoldbachRH

/-- `D X ≤ D E X` when `D, X ≥ 0` and `E ≥ 1`. -/
lemma le_mul_of_one_le' {D X E : ℝ} (hD : 0 ≤ D) (hX : 0 ≤ X) (hE : 1 ≤ E) :
    D * X ≤ D * E * X := by
  nlinarith [mul_nonneg (mul_nonneg hD hX) (sub_nonneg.2 hE)]

/-- The polynomial bound behind `R_T ≤ 1`, over plain real variables. -/
lemma P_bound {L D σ V E E2 : ℝ} (hL : 42.8 ≤ L) (hD0 : 0 ≤ D) (hD1 : D ≤ 0.29)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 0.17) (hV2 : V ^ 2 = 9 * L)
    (hE1 : 1 ≤ E) (hE2E : E2 ≤ E) (_hE20 : 0 ≤ E2) :
    (L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1)
      + 0.06 * (1 + D) * (1 / 4 + σ ^ 2)
      + 2.02 * (E + E2 * V ^ 2 / (8 * π) + 2.4 * (V ^ 2 / 2 + 0.04) / log 2)
      + 0.5 * (1 + D) * (σ ^ 2 + σ + 1 / 4) * E2 ≤ E * (4 * L ^ 3) := by
  have hL0 : 0 < L := by linarith
  have hpi := pi_gt_d6
  have hl2 := log_two_gt_d9
  have hl2pos : 0 < log 2 := by linarith
  have hσ2 : σ ^ 2 ≤ 0.0289 := by nlinarith
  have hV8pi : V ^ 2 / (8 * π) ≤ 0.36 * L := by
    rw [hV2, div_le_iff₀ (by positivity)]; nlinarith
  have hlogt : 2.4 * (V ^ 2 / 2 + 0.04) / log 2 ≤ 15.66 * L + 0.14 := by
    rw [hV2, div_le_iff₀ hl2pos]; nlinarith
  have a : E2 * V ^ 2 / (8 * π) ≤ E * (0.36 * L) := by
    rw [mul_div_assoc]
    exact mul_le_mul hE2E hV8pi (div_nonneg (by positivity) (by positivity)) (by linarith)
  have b : 2.4 * (V ^ 2 / 2 + 0.04) / log 2 ≤ E * (15.66 * L + 0.14) := by
    have : 0 ≤ 15.66 * L + 0.14 := by positivity
    nlinarith
  have p3 : 0.06 * (1 + D) * (1 / 4 + σ ^ 2) ≤ E * 0.022 := by
    have : (1 + D) * (1 / 4 + σ ^ 2) ≤ 1.29 * 0.2789 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    nlinarith
  have p5 : 0.5 * (1 + D) * (σ ^ 2 + σ + 1 / 4) * E2 ≤ E * 0.29 := by
    have : (1 + D) * (σ ^ 2 + σ + 1 / 4) ≤ 1.29 * 0.4489 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have h0 : 0 ≤ 0.5 * (1 + D) * (σ ^ 2 + σ + 1 / 4) := by positivity
    have : 0.5 * (1 + D) * (σ ^ 2 + σ + 1 / 4) * E2 ≤ 0.5 * (1 + D) * (σ ^ 2 + σ + 1 / 4) * E :=
      mul_le_mul_of_nonneg_left hE2E h0
    nlinarith
  have hX0 : 0 ≤ (L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1) := by positivity
  have q1 : (L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1) ≤
      E * ((L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1)) := by
    nlinarith [mul_nonneg hX0 (sub_nonneg.2 hE1)]
  have q2 : (L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1) + 0.022
      + 2.02 * (16.02 * L + 1.14) + 0.29 ≤ 4 * L ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hL) (sq_nonneg L), mul_nonneg (sub_nonneg.2 hL) hL0.le]
  have q3 : E * ((L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1) + 0.022
      + 2.02 * (16.02 * L + 1.14) + 0.29) ≤ E * (4 * L ^ 3) :=
    mul_le_mul_of_nonneg_left q2 (by linarith)
  nlinarith

section
variable {L : ℝ} (hL : (42.8 : ℝ) ≤ L)
include hL

lemma L_pos : 0 < L := by linarith

lemma sqrtL_ge : (6.54 : ℝ) ≤ √L := by
  rw [show (6.54 : ℝ) = √(6.54 ^ 2) by rw [sqrt_sq (by norm_num)]]
  exact sqrt_le_sqrt (by norm_num; linarith)

lemma sqrtL_sq : √L ^ 2 = L := sq_sqrt (L_pos hL).le

lemma Vp_sq : Vp L ^ 2 = 9 * L := by
  unfold Vp; rw [mul_pow, sqrtL_sq hL]; ring

lemma Vp_ge : (19.62 : ℝ) ≤ Vp L := by unfold Vp; linarith [sqrtL_ge hL]

lemma uL_ge : (23.15 : ℝ) ≤ uL L := by
  unfold uL Vp
  have h1 := sqrtL_ge hL
  have h2 := sqrtL_sq hL
  nlinarith

lemma L_le_two_u : L ≤ 2 * uL L := by
  unfold uL Vp
  have h1 := sqrtL_ge hL
  have h2 := sqrtL_sq hL
  nlinarith

lemma Vp_add_one_le : Vp L + 1 ≤ L / 2 := by
  unfold Vp
  have h1 := sqrtL_ge hL
  have h2 := sqrtL_sq hL
  nlinarith

lemma dl_nonneg : 0 ≤ dl L := by unfold dl; positivity

lemma dl_le : dl L ≤ 0.29 := by
  have hL0 := L_pos hL
  have h3 := pow_div_factorial_le_exp L hL0.le 3
  norm_num [Nat.factorial] at h3
  unfold dl
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos L)]
  nlinarith [mul_le_mul_of_nonneg_left hL (sq_nonneg L)]

omit hL in
lemma dl_mul_exp_Vp : dl L * exp (Vp L) = L ^ 2 * exp (-(1 * uL L)) := by
  unfold dl uL
  rw [mul_assoc, ← exp_add]
  ring_nf

lemma sg_nonneg : 0 ≤ sg L := by
  unfold sg; exact div_nonneg pi_pos.le (by linarith [Vp_ge hL])

lemma sg_le : sg L ≤ 0.17 := by
  unfold sg
  rw [div_le_iff₀ (by linarith [Vp_ge hL])]
  nlinarith [Vp_ge hL, pi_lt_d6]

/-- `R_T ≤ 1`. -/
lemma RT_le_one : RT L ≤ 1 := by
  have hL0 := L_pos hL
  have hD0 := dl_nonneg hL
  have hE1 : 1 ≤ exp (Vp L) := one_le_exp (by linarith [Vp_ge hL])
  have hE2E : exp (Vp L / 2) ≤ exp (Vp L) := exp_le_exp.2 (by linarith [Vp_ge hL])
  have hP := P_bound hL hD0 (dl_le hL) (sg_nonneg hL) (sg_le hL) (Vp_sq hL) hE1 hE2E
    (exp_pos _).le
  have hRT : RT L = dl L * ((L ^ 2 + 3 * L) + (8 / 3 * L ^ 3 + 33 * L ^ 2 + 136 * L + 250.1)
      + 0.06 * (1 + dl L) * (1 / 4 + sg L ^ 2)
      + 2.02 * (exp (Vp L) + exp (Vp L / 2) * Vp L ^ 2 / (8 * π)
          + 2.4 * (Vp L ^ 2 / 2 + 0.04) / log 2)
      + 0.5 * (1 + dl L) * (sg L ^ 2 + sg L + 1 / 4) * exp (Vp L / 2)) := by
    unfold RT; ring
  rw [hRT]
  have hDE : dl L * exp (Vp L) = L ^ 2 * exp (-(1 * uL L)) := dl_mul_exp_Vp
  have hu := uL_ge hL
  have hLu := L_le_two_u hL
  have hmono := pow_mul_exp_neg_le (k := 5) (c := 1) (u0 := 23.15) (u := uL L)
    (by norm_num) (by norm_num) hu
  have hnum := num_RT
  have hL5 : L ^ 5 ≤ 32 * uL L ^ 5 := by
    calc L ^ 5 ≤ (2 * uL L) ^ 5 := pow_le_pow_left₀ hL0.le hLu 5
      _ = 32 * uL L ^ 5 := by ring
  calc _ ≤ dl L * (exp (Vp L) * (4 * L ^ 3)) := mul_le_mul_of_nonneg_left hP hD0
    _ = 4 * L ^ 5 * exp (-(1 * uL L)) := by rw [← mul_assoc, hDE]; ring
    _ ≤ 4 * (32 * uL L ^ 5) * exp (-(1 * uL L)) := by gcongr
    _ = 128 * (uL L ^ 5 * exp (-(1 * uL L))) := by ring
    _ ≤ 128 * ((23.15 : ℝ) ^ 5 * exp (-(1 * 23.15))) := by gcongr
    _ ≤ 1 := by
        have h0 : 0 ≤ (23.15 : ℝ) ^ 5 * exp (-(1 * 23.15)) := by positivity
        linarith

lemma RT_nonneg : 0 ≤ RT L := by
  have := dl_nonneg hL
  have := sg_nonneg hL
  have : 0 < log 2 := log_pos (by norm_num)
  unfold RT
  have : 0 ≤ Vp L := by linarith [Vp_ge hL]
  positivity

/-- `𝒯 ≤ L² - 4 L + 2.91`. -/
lemma Tb_le : Tb L ≤ L ^ 2 - 4 * L + 2.91 := by
  have hL0 := L_pos hL
  have hs := sqrtL_ge hL
  have hs2 := sqrtL_sq hL
  set s := √L with hsdef
  clear_value s
  set r := √s with hrdef
  have hr2 : r ^ 2 = s := sq_sqrt (by linarith)
  clear_value r
  have hr : (2.557 : ℝ) ≤ r := by
    rw [hrdef, show (2.557 : ℝ) = √(2.557 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num; linarith)
  have hL4 : L = r ^ 4 := by rw [← hs2, ← hr2]; ring
  -- G := 2 log L + log π - a₁
  have hTm : Tmain L = (L - (2 * log L + log π - a1)) ^ 2 + (1 + π ^ 2 / 12) := by
    unfold Tmain; ring
  set G := 2 * log L + log π - a1 with hG
  have hl2a := log_two_gt_d9
  have hl2b := log_two_lt_d9
  have hγa := Real.one_half_lt_eulerMascheroniConstant
  have hγb := Real.eulerMascheroniConstant_lt_two_thirds
  have hpa := pi_gt_d6
  have hpb := pi_lt_d6
  have hlogL_lo : 5 * log 2 ≤ log L := by
    have h := log_le_log (show (0 : ℝ) < 2 ^ 5 by norm_num) (show (2 : ℝ) ^ 5 ≤ L by linarith)
    rw [log_pow] at h; push_cast at h; linarith
  have hlogpi_lo : log 2 ≤ log π :=
    log_le_log (by norm_num) (by linarith)
  have hlogpi_hi : log π ≤ 2 * log 2 := by
    have h := log_le_log pi_pos (show π ≤ (2 : ℝ) ^ 2 by nlinarith)
    rw [log_pow] at h; push_cast at h; linarith
  have hlogL_hi : log L ≤ 4 * (r - 1) := by
    rw [hL4, log_pow]; push_cast
    have := log_le_sub_one_of_pos (show 0 < r by linarith)
    linarith
  have hGlo : 7.81 ≤ G := by rw [hG]; unfold a1; linarith
  have hGhi : G ≤ 8 * r - 5.56 := by rw [hG]; unfold a1; linarith
  clear_value G
  have hG2 : G ^ 2 ≤ 64 * s := by
    have h1 : G ^ 2 ≤ (8 * r - 5.56) ^ 2 := pow_le_pow_left₀ (by linarith) hGhi 2
    have h2 : (8 * r - 5.56) ^ 2 ≤ 64 * r ^ 2 := by nlinarith
    rw [hr2] at h2
    linarith
  have h64 : 64 * s ≤ 9.79 * L := by
    rw [← hs2]; nlinarith
  have hpi2a : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpa.le 2
  have hpi2b : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := pow_le_pow_left₀ pi_pos.le hpb.le 2
  have hTmain : Tmain L ≤ L ^ 2 - 15.62 * L + 9.79 * L + 1.8225 := by
    rw [hTm]
    have e : (L - G) ^ 2 = L ^ 2 - 2 * (L * G) + G ^ 2 := by ring
    have hLG : L * 7.81 ≤ L * G := mul_le_mul_of_nonneg_left hGlo hL0.le
    rw [e]
    norm_num at hpi2b
    linarith
  have hTpr : Tpr L ≤ 1.8238 * L + 0.08 := by
    unfold Tpr; rw [Vp_sq hL]
    have : 2 * (9 * L) / π ^ 2 ≤ 1.8238 * L := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hpi2a hL0.le
      norm_num at this
      linarith
    linarith
  have hRT := RT_le_one hL
  unfold Tb
  linarith

lemma Tb_nonneg : 0 ≤ Tb L := by
  unfold Tb Tmain Tpr
  have := RT_nonneg hL
  positivity

/-- `L² ℰ ≤ 110`. -/
lemma L2_Eb_le : L ^ 2 * Eb L ≤ 140 := by
  have hL0 := L_pos hL
  have hu := uL_ge hL
  have hLu := L_le_two_u hL
  have hV1 := Vp_add_one_le hL
  have hD0 := dl_nonneg hL
  have hD1 := dl_le hL
  have hl2 := log_two_gt_d9
  have hl2pos : 0 < log 2 := by linarith
  set u := uL L with hudef
  set e1 := exp (-(1 / 2 * u)) with he1
  set e2 := exp (-(2 / 3 * u)) with he2
  have he1' : exp (-u / 2) = e1 := by rw [he1]; congr 1; ring
  have he2' : exp (-(2 * u) / 3) = e2 := by rw [he2]; congr 1; ring
  have he3 : exp (-u) ≤ e1 := by rw [he1]; exact exp_le_exp.2 (by linarith)
  have he10 : 0 ≤ e1 := (exp_pos _).le
  have he20 : 0 ≤ e2 := (exp_pos _).le
  -- the bracket
  set X := (u + 2) * exp (-u / 2) + u / log 2 * (u / 2 + 0.75) * exp (-(2 * u) / 3)
    + 3 * exp (-u) with hX
  have hX0 : 0 ≤ X := by rw [hX]; have := (exp_pos (-u)).le; positivity
  have hXle : X ≤ 1.22 * u * e1 + 0.773 * u ^ 2 * e2 := by
    rw [hX, he1', he2']
    have a : (u + 2) * e1 + 3 * exp (-u) ≤ 1.22 * u * e1 := by nlinarith
    have hinv : u / log 2 ≤ 1.45 * u := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have b : u / log 2 * (u / 2 + 0.75) * e2 ≤ 0.773 * u ^ 2 * e2 := by
      have : u / log 2 * (u / 2 + 0.75) ≤ 1.45 * u * (0.533 * u) :=
        mul_le_mul hinv (by linarith) (by linarith) (by positivity)
      nlinarith
    linarith
  -- the prefactor
  have hpref : L ^ 2 * ((L + Vp L + 1) / log 2 * (1 + dl L) * log 4) ≤ 31.2 * u ^ 3 := by
    have h1 : (L + Vp L + 1) / log 2 ≤ 1.45 * (1.5 * L) := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have h2 : (L + Vp L + 1) / log 2 * (1 + dl L) * log 4 ≤ 3.89 * L := by
      have h0 : 0 ≤ (L + Vp L + 1) / log 2 := by
        apply div_nonneg _ hl2pos.le; linarith [Vp_ge hL]
      have : (L + Vp L + 1) / log 2 * (1 + dl L) ≤ 1.45 * (1.5 * L) * 1.29 :=
        mul_le_mul h1 (by linarith) (by linarith) (by positivity)
      have hl4 : log 4 ≤ 1.3863 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; linarith [log_two_lt_d9]
      have hl40 : 0 ≤ log 4 := log_nonneg (by norm_num)
      calc (L + Vp L + 1) / log 2 * (1 + dl L) * log 4 ≤ 1.45 * (1.5 * L) * 1.29 * 1.3863 :=
            mul_le_mul this hl4 hl40 (by positivity)
        _ ≤ 3.89 * L := by nlinarith
    have hL3 : L ^ 3 ≤ 8 * u ^ 3 := by
      calc L ^ 3 ≤ (2 * u) ^ 3 := pow_le_pow_left₀ hL0.le hLu 3
        _ = 8 * u ^ 3 := by ring
    calc L ^ 2 * ((L + Vp L + 1) / log 2 * (1 + dl L) * log 4) ≤ L ^ 2 * (3.89 * L) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3.89 * L ^ 3 := by ring
      _ ≤ 31.2 * u ^ 3 := by nlinarith
  have hEb : Eb L = ((L + Vp L + 1) / log 2 * (1 + dl L) * log 4) * X := by
    unfold Eb; rw [← hudef]
  have hm4 := pow_mul_exp_neg_le (k := 4) (c := 1 / 2) (u0 := 23.15) (u := u)
    (by norm_num) (by norm_num) hu
  have hm5 := pow_mul_exp_neg_le (k := 5) (c := 2 / 3) (u0 := 23.15) (u := u)
    (by norm_num) (by norm_num) hu
  have n4 := num_u4
  have n5 := num_u5
  have hpref0 : 0 ≤ (L + Vp L + 1) / log 2 * (1 + dl L) * log 4 := by
    have : 0 ≤ L + Vp L + 1 := by linarith [Vp_ge hL]
    positivity
  calc L ^ 2 * Eb L = (L ^ 2 * ((L + Vp L + 1) / log 2 * (1 + dl L) * log 4)) * X := by
        rw [hEb]; ring
    _ ≤ (31.2 * u ^ 3) * X := mul_le_mul_of_nonneg_right hpref hX0
    _ ≤ (31.2 * u ^ 3) * (1.22 * u * e1 + 0.773 * u ^ 2 * e2) :=
        mul_le_mul_of_nonneg_left hXle (by positivity)
    _ = 38.064 * (u ^ 4 * e1) + 24.1176 * (u ^ 5 * e2) := by ring
    _ ≤ 38.064 * 2.76 + 24.1176 * 1.34 := by
        rw [he1, he2]; gcongr <;> linarith
    _ ≤ 140 := by norm_num

lemma Eb_nonneg : 0 ≤ Eb L := by
  have hu := uL_ge hL
  have hD0 := dl_nonneg hL
  have : 0 < log 2 := log_pos (by norm_num)
  have : 0 ≤ L + Vp L + 1 := by linarith [Vp_ge hL]
  unfold Eb
  positivity

/-- `L² δ ≤ 5.62`. -/
lemma L2_dl_le : L ^ 2 * dl L ≤ 5.62 := by
  have hL0 := L_pos hL
  have h5 := pow_div_factorial_le_exp L hL0.le 5
  norm_num [Nat.factorial] at h5
  unfold dl
  rw [exp_neg, ← div_eq_mul_inv]
  rw [show L ^ 2 * (L ^ 2 / exp L) = L ^ 4 / exp L by ring,
    div_le_iff₀ (exp_pos L)]
  have h45 : 42.8 * L ^ 4 ≤ L ^ 5 := by
    have := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0.le 4)
    calc 42.8 * L ^ 4 ≤ L * L ^ 4 := this
      _ = L ^ 5 := by ring
  have h5' := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 5.62)
  have : L ^ 4 ≤ 5.62 * (L ^ 5 / 120) := by linarith [pow_nonneg hL0.le 4]
  linarith

/-- `L² ℬ ≤ 5`. -/
lemma L2_Bb_le : L ^ 2 * Bb L ≤ 5 := by
  have hu := uL_ge hL
  have he : exp (-5 * uL L) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have he0 : 0 ≤ exp (-5 * uL L) := (exp_pos _).le
  have hD := L2_dl_le hL
  unfold Bb
  have hD0 : 0 ≤ L ^ 2 * dl L := mul_nonneg (by positivity) (dl_nonneg hL)
  calc L ^ 2 * (0.8 * dl L * exp (-5 * uL L)) = 0.8 * (L ^ 2 * dl L) * exp (-5 * uL L) := by ring
    _ ≤ 0.8 * (L ^ 2 * dl L) * 1 := by gcongr
    _ ≤ 5 := by nlinarith

lemma Bb_nonneg : 0 ≤ Bb L := by
  have := dl_nonneg hL
  unfold Bb; positivity

/-- `2 L² e^{-V} ≤ 0.05`. -/
lemma two_L2_exp_neg_V : 2 * L ^ 2 * exp (-Vp L) ≤ 0.05 := by
  have hs := sqrtL_ge hL
  have hs2 := sqrtL_sq hL
  have h6 := pow_div_factorial_le_exp (3 * √L) (by linarith) 6
  norm_num [Nat.factorial] at h6
  have hpos := exp_pos (3 * √L)
  unfold Vp
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have hs4 : 0 ≤ √L ^ 4 := by positivity
  have hL2 : L ^ 2 = √L ^ 4 := by rw [show √L ^ 4 = (√L ^ 2) ^ 2 by ring, hs2]
  rw [hL2]
  have : 2 * √L ^ 4 ≤ 0.05 * ((3 * √L) ^ 6 / 720) := by
    have hsq : 42.8 ≤ √L ^ 2 := by rw [hs2]; exact hL
    nlinarith [mul_le_mul_of_nonneg_left hsq hs4]
  linarith

/-- `L⁴ ≤ e^{L/2}`, i.e. `L⁴ / e^{L/2} ≤ 1`. -/
lemma L4_div_exp_half_le : L ^ 4 / exp (L / 2) ≤ 1 := by
  have hL0 := L_pos hL
  rw [div_le_one (exp_pos _)]
  have h := pow_div_factorial_le_exp (L / 2) (by linarith) 10
  norm_num [Nat.factorial] at h
  have hL6 : (42.8 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
  have h10 : L ^ 4 * 42.8 ^ 6 ≤ L ^ 10 := by
    calc L ^ 4 * 42.8 ^ 6 ≤ L ^ 4 * L ^ 6 := mul_le_mul_of_nonneg_left hL6 (pow_nonneg hL0.le 4)
      _ = L ^ 10 := by ring
  have h4 : 0 ≤ L ^ 4 := pow_nonneg hL0.le 4
  norm_num at h10
  nlinarith

/-- **Range inequality** (version 0.6). For every `L ≥ 42.8`,
`(√𝒯 + √ℰ + √ℬ)² < L² (2m - 2δ - L²/(2π e^{L/2}))`, with `m = 1/2 - 9.55/V² - e^{-V}`. -/
theorem range_inequality :
    (√(Tb L) + √(Eb L) + √(Bb L)) ^ 2 <
      L ^ 2 * (2 * (1 / 2 - 9.55 / Vp L ^ 2 - exp (-Vp L)) - 2 * dl L
        - L ^ 2 / (2 * π * exp (L / 2))) := by
  have hL0 := L_pos hL
  have hT := Tb_le hL
  have hT0 := Tb_nonneg hL
  have hE := L2_Eb_le hL
  have hE0 := Eb_nonneg hL
  have hB := L2_Bb_le hL
  have hB0 := Bb_nonneg hL
  have hX := two_L2_exp_neg_V hL
  have hV2 := Vp_sq hL
  have hD := L2_dl_le hL
  have hQ := L4_div_exp_half_le hL
  -- `√𝒯 ≤ L`
  have hTL : √(Tb L) ≤ L := (sqrt_le_left hL0.le).2 (by nlinarith)
  -- `L √ℰ ≤ 11.84` and `L √ℬ ≤ 2.24`
  have hEs0 := sqrt_nonneg (Eb L)
  have hBs0 := sqrt_nonneg (Bb L)
  have hEL : L * √(Eb L) ≤ 11.84 := by
    have h2 : (L * √(Eb L)) ^ 2 = L ^ 2 * Eb L := by rw [mul_pow, sq_sqrt hE0]
    nlinarith [mul_nonneg hL0.le hEs0]
  have hBL : L * √(Bb L) ≤ 2.24 := by
    have h2 : (L * √(Bb L)) ^ 2 = L ^ 2 * Bb L := by rw [mul_pow, sq_sqrt hB0]
    nlinarith [mul_nonneg hL0.le hBs0]
  set b := √(Eb L) + √(Bb L) with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hLb : L * b ≤ 14.08 := by rw [hbdef]; nlinarith
  have hb : b ≤ 0.33 := by nlinarith [mul_le_mul_of_nonneg_right hL hb0]
  have hS : (√(Tb L) + √(Eb L) + √(Bb L)) ^ 2 ≤ L ^ 2 - 4 * L + 2.91 + 28.16 + 0.11 := by
    have e : (√(Tb L) + √(Eb L) + √(Bb L)) ^ 2 = Tb L + 2 * √(Tb L) * b + b ^ 2 := by
      rw [hbdef]; nlinarith [sq_sqrt hT0]
    rw [e]
    have h1 : 2 * √(Tb L) * b ≤ 2 * L * b := by
      have := mul_le_mul_of_nonneg_right hTL hb0; linarith
    nlinarith
  have hR0 : 2 * L ^ 2 * (1 / 2 - 9.55 / Vp L ^ 2 - exp (-Vp L))
      = L ^ 2 - 19.1 / 9 * L - 2 * L ^ 2 * exp (-Vp L) := by
    rw [hV2]; field_simp; ring
  have hQ' : L ^ 2 * (L ^ 2 / (2 * π * exp (L / 2))) ≤ 1 := by
    have e : L ^ 2 * (L ^ 2 / (2 * π * exp (L / 2))) = L ^ 4 / exp (L / 2) / (2 * π) := by
      field_simp
    rw [e, div_le_one (by positivity)]
    nlinarith [pi_gt_three]
  have hR : L ^ 2 * (2 * (1 / 2 - 9.55 / Vp L ^ 2 - exp (-Vp L)) - 2 * dl L
        - L ^ 2 / (2 * π * exp (L / 2)))
      = 2 * L ^ 2 * (1 / 2 - 9.55 / Vp L ^ 2 - exp (-Vp L)) - 2 * (L ^ 2 * dl L)
        - L ^ 2 * (L ^ 2 / (2 * π * exp (L / 2))) := by ring
  rw [hR, hR0]
  nlinarith

end

end GoldbachRH
