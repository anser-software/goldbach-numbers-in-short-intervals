import GoldbachRH.Defs

/-!
# Elementary bounds for `exp`

* `pow_mul_exp_neg_le`: `u ↦ u^k e^{-cu}` is nonincreasing for `u ≥ k/c`.
* `exp_lower`: `e^{n+r} ≥ 2.7182818283ⁿ (1 + r + r²/2)` for `r ≥ 0`.
-/

open Real

namespace GoldbachRH

lemma pow_mul_exp_neg_le {k : ℕ} {c u0 u : ℝ} (hu0 : 0 < u0)
    (hk : (k : ℝ) ≤ c * u0) (hu : u0 ≤ u) :
    u ^ k * exp (-(c * u)) ≤ u0 ^ k * exp (-(c * u0)) := by
  have hu' : 0 < u := lt_of_lt_of_le hu0 hu
  have h1 : u / u0 ≤ exp (u / u0 - 1) := by linarith [add_one_le_exp (u / u0 - 1)]
  have h2 : (u / u0) ^ k ≤ exp (c * (u - u0)) := by
    calc (u / u0) ^ k ≤ exp (u / u0 - 1) ^ k := pow_le_pow_left₀ (by positivity) h1 k
      _ = exp (k * (u / u0 - 1)) := by rw [← exp_nat_mul]
      _ ≤ exp (c * (u - u0)) := by
          apply exp_le_exp.2
          have e : (k : ℝ) * (u / u0 - 1) = (k / u0) * (u - u0) := by field_simp
          rw [e]
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [div_le_iff₀ hu0]; linarith
  calc u ^ k * exp (-(c * u)) = u0 ^ k * ((u / u0) ^ k * exp (-(c * u))) := by
        rw [div_pow]; field_simp
    _ ≤ u0 ^ k * (exp (c * (u - u0)) * exp (-(c * u))) := by gcongr
    _ = u0 ^ k * exp (-(c * u0)) := by rw [← exp_add]; ring_nf

lemma exp_lower (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (2.7182818283 : ℝ) ^ n * (1 + r + r ^ 2 / 2) ≤ exp (n + r) := by
  rw [exp_add]
  have hn : exp (n : ℝ) = exp 1 ^ n := by rw [← exp_nat_mul]; simp
  rw [hn]
  exact mul_le_mul (pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le n)
    (quadratic_le_exp_of_nonneg hr) (by positivity) (by positivity)

/-- `u₀⁴ e^{-u₀/2} ≤ 2.76` at `u₀ = 23.15`. -/
lemma num_u4 : (23.15 : ℝ) ^ 4 * exp (-(1 / 2 * 23.15)) ≤ 2.76 := by
  have h := exp_lower 11 (r := 0.575) (by norm_num)
  have e : ((11 : ℕ) : ℝ) + 0.575 = 1 / 2 * 23.15 := by norm_num
  rw [e] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  nlinarith

/-- `u₀⁵ e^{-2u₀/3} ≤ 1.34` at `u₀ = 23.15`. -/
lemma num_u5 : (23.15 : ℝ) ^ 5 * exp (-(2 / 3 * 23.15)) ≤ 1.34 := by
  have h := exp_lower 15 (r := 2 / 3 * 23.15 - 15) (by norm_num)
  have e : ((15 : ℕ) : ℝ) + (2 / 3 * 23.15 - 15) = 2 / 3 * 23.15 := by norm_num
  rw [e] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  nlinarith

/-- `256 u₀⁵ e^{-u₀} ≤ 1` at `u₀ = 23.15`. -/
lemma num_RT : 256 * ((23.15 : ℝ) ^ 5 * exp (-(1 * 23.15))) ≤ 1 := by
  have h := exp_lower 23 (r := 0.15) (by norm_num)
  have e : ((23 : ℕ) : ℝ) + 0.15 = 1 * 23.15 := by norm_num
  rw [e] at h
  rw [exp_neg, ← div_eq_mul_inv, ← mul_div_assoc, div_le_iff₀ (exp_pos _)]
  nlinarith

end GoldbachRH
