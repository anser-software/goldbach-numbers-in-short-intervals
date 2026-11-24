import GoldbachRH.CoverFM2

/-!
# The first-moment cover, part 3: level sets

For a level `t ∈ (0, 1)`, the superlevel set `I_t = {q > t} ∩ (0, x)` of the symmetric weight is an
interval `(A, x - A)` up to its endpoints, with `x e^{-V} ≤ A ≤ x/2`. Hence (`level_bound`)
`|I_t| ≤ ∫_{I_t} G + c`, with `c = δx + 2ε`. Integrating over `t` (layer cake) gives
`∫ q ≤ ∫ q G + c` (`first_moment`).
-/

open Real Set MeasureTheory

namespace GoldbachRH

lemma measurable_wfun (x V : ℝ) : Measurable (wfun x V) :=
  (measurable_W V).comp (measurable_log.comp (measurable_const.div measurable_id))

lemma measurable_qfun (x V : ℝ) : Measurable (qfun x V) := by
  have h2 : Measurable fun y : ℝ => wfun x V (x - y) :=
    (measurable_wfun x V).comp (measurable_const.sub measurable_id)
  exact (measurable_wfun x V).min h2

lemma measurable_Gfun (δ : ℝ) : Measurable (Gfun δ) := by
  have h1 : Measurable fun y : ℝ => Chebyshev.theta ((1 + δ) * y) :=
    Chebyshev.theta_mono.measurable.comp (measurable_const.mul measurable_id)
  exact (h1.sub Chebyshev.theta_mono.measurable).div (measurable_const.mul measurable_id)

/-- The superlevel set of `q` inside `(0, x)`. -/
def Ilev (x V t : ℝ) : Set ℝ := {y | t < qfun x V y} ∩ Ioo 0 x

lemma measurableSet_Ilev (x V t : ℝ) : MeasurableSet (Ilev x V t) :=
  (measurableSet_lt measurable_const (measurable_qfun x V)).inter measurableSet_Ioo

/-- **One level.** -/
lemma level_bound {x V δ t : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hy0 : 599 ≤ x * exp (-V)) (hSch : SchoenfeldTheta) (ht : 0 < t) :
    volume (Ilev x V t) ≤ (∫⁻ y in Ilev x V t, ENNReal.ofReal (Gfun δ y))
      + (Iio (1 : ℝ)).indicator
          (fun _ => ENNReal.ofReal (δ * x + 2 * (√x * log x ^ 2 / (8 * π)))) t := by
  set I := Ilev x V t with hI
  by_cases hne : I.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.1 hne, measure_empty]
    exact zero_le
  have ht1 : t < 1 := by
    obtain ⟨y, hy⟩ := hne
    exact hy.1.trans_le (qfun_le_one hV y)
  simp only [indicator_of_mem (mem_Iio.2 ht1)]
  -- symmetry and order-connectedness of `I`
  have hsymm : ∀ y ∈ I, x - y ∈ I := by
    intro y hy
    refine ⟨?_, ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩⟩
    show t < qfun x V (x - y)
    rw [qfun_symm]
    exact hy.1
  have hconn : ∀ a ∈ I, ∀ b ∈ I, ∀ y, a ≤ y → y ≤ b → y ∈ I := by
    intro a ha b hb y hay hyb
    have ha0 : 0 < a := ha.2.1
    have hbx : b < x := hb.2.2
    refine ⟨?_, ⟨by linarith, by linarith⟩⟩
    show t < min (wfun x V y) (wfun x V (x - y))
    have h1 : wfun x V a ≤ wfun x V y := wfun_mono hV ha0 hay (by linarith)
    have h2 : wfun x V (x - b) ≤ wfun x V (x - y) :=
      wfun_mono hV (by linarith) (by linarith) (by linarith)
    have hta : t < wfun x V a := ha.1.trans_le (min_le_left _ _)
    have htb : t < wfun x V (x - b) := hb.1.trans_le (min_le_right _ _)
    exact lt_min (hta.trans_le h1) (htb.trans_le h2)
  have hlow : ∀ y ∈ I, x * exp (-V) < y := fun y hy =>
    (gt_of_qfun_pos hx hV hy.2.1 hy.2.2 (ht.trans hy.1)).1
  have hbdd : BddBelow I := ⟨0, fun y hy => hy.2.1.le⟩
  set A := sInf I with hA
  have hA1 : x * exp (-V) ≤ A := le_csInf hne fun y hy => (hlow y hy).le
  have hA2 : A ≤ x / 2 := by
    obtain ⟨y, hy⟩ := hne
    have h1 : A ≤ y := csInf_le hbdd hy
    have h2 : A ≤ x - y := csInf_le hbdd (hsymm y hy)
    linarith
  have hsub1 : I ⊆ Icc A (x - A) := by
    intro y hy
    refine ⟨csInf_le hbdd hy, ?_⟩
    have := csInf_le hbdd (hsymm y hy)
    linarith
  have hsub2 : Ioo A (x - A) ⊆ I := by
    intro y hy
    obtain ⟨a, ha, hay⟩ := exists_lt_of_csInf_lt hne hy.1
    obtain ⟨b', hb', hb'y⟩ := exists_lt_of_csInf_lt hne (by linarith [hy.2] : A < x - y)
    exact hconn a ha (x - b') (hsymm b' hb') y hay.le (by linarith)
  -- measure of `I`
  have hvol : volume I ≤ ENNReal.ofReal (x - A - A) := by
    calc volume I ≤ volume (Icc A (x - A)) := measure_mono hsub1
      _ = ENNReal.ofReal (x - A - A) := Real.volume_Icc
  -- the first moment on `(A, x - A)`
  have hA599 : 599 ≤ A := hy0.trans hA1
  have hA0 : 0 < A := by linarith
  have hAB : A ≤ x - A := by linarith
  have hGint : IntegrableOn (Gfun δ) (Ioo A (x - A)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hAB).1 (intervalIntegrable_Gfun hδ hA0 hAB)
  have hGnn : 0 ≤ᵐ[volume.restrict (Ioo A (x - A))] Gfun δ :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
      fun y hy => Gfun_nonneg hδ (hA0.trans hy.1))
  have hint : ENNReal.ofReal (∫ y in A..(x - A), Gfun δ y)
      ≤ ∫⁻ y in I, ENNReal.ofReal (Gfun δ y) := by
    rw [intervalIntegral.integral_of_le hAB, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hGint hGnn]
    exact lintegral_mono_set hsub2
  have hG := integral_G_ge hSch hδ hδ1 hA599 hA2
  calc volume I ≤ ENNReal.ofReal (x - A - A) := hvol
    _ ≤ ENNReal.ofReal ((∫ y in A..(x - A), Gfun δ y)
          + (δ * x + 2 * (√x * log x ^ 2 / (8 * π)))) := by
        apply ENNReal.ofReal_le_ofReal
        linarith
    _ ≤ ENNReal.ofReal (∫ y in A..(x - A), Gfun δ y)
          + ENNReal.ofReal (δ * x + 2 * (√x * log x ^ 2 / (8 * π))) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add hint le_rfl

/-- **The first moment.** `∫_{(0,x)} q ≤ ∫_{(0,x)} q G + c`. -/
lemma first_moment {x V δ : ℝ} (hx : 0 < x) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hy0 : 599 ≤ x * exp (-V)) (hSch : SchoenfeldTheta) :
    ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y)
      ≤ (∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y))
        + ENNReal.ofReal (δ * x + 2 * (√x * log x ^ 2 / (8 * π))) := by
  set c := δ * x + 2 * (√x * log x ^ 2 / (8 * π)) with hc
  have hq := measurable_qfun x V
  have hGm : Measurable fun y => ENNReal.ofReal (Gfun δ y) :=
    ENNReal.measurable_ofReal.comp (measurable_Gfun δ)
  set μ := (volume.restrict (Ioo (0 : ℝ) x)).withDensity fun y => ENNReal.ofReal (Gfun δ y)
    with hμ
  -- layer cake for `μ`
  have hLC1 : ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y)
      = ∫⁻ t in Ioi 0, ∫⁻ y in Ilev x V t, ENNReal.ofReal (Gfun δ y) := by
    have h := lintegral_eq_lintegral_meas_lt μ (f := qfun x V)
      (Filter.Eventually.of_forall fun y => qfun_nonneg hV y) hq.aemeasurable
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hGm hq.ennreal_ofReal] at h
    have e1 : ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y * Gfun δ y)
        = ∫⁻ y in Ioo 0 x, ((fun y => ENNReal.ofReal (Gfun δ y)) *
            fun y => ENNReal.ofReal (qfun x V y)) y := by
      apply lintegral_congr
      intro y
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (qfun_nonneg hV y), mul_comm]
    rw [e1, h]
    apply lintegral_congr
    intro t
    rw [withDensity_apply _ (measurableSet_lt measurable_const hq),
      Measure.restrict_restrict (measurableSet_lt measurable_const hq)]
    rfl
  -- layer cake for Lebesgue measure
  have hLC2 : ∫⁻ y in Ioo 0 x, ENNReal.ofReal (qfun x V y)
      = ∫⁻ t in Ioi 0, volume (Ilev x V t) := by
    rw [lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall fun y => qfun_nonneg hV y)
      hq.aemeasurable]
    apply lintegral_congr
    intro t
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hq)]
    rfl
  -- integrate the level bound
  have hind : ∫⁻ t in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal c) t
      = ENNReal.ofReal c := by
    rw [lintegral_indicator_const measurableSet_Iio,
      Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo]
    simp
  have hindm : Measurable fun t : ℝ => (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal c) t :=
    measurable_const.indicator measurableSet_Iio
  rw [hLC2, hLC1]
  calc ∫⁻ t in Ioi 0, volume (Ilev x V t)
      ≤ ∫⁻ t in Ioi 0, ((∫⁻ y in Ilev x V t, ENNReal.ofReal (Gfun δ y))
          + (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal c) t) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => level_bound hx hV hδ hδ1 hy0 hSch ht
    _ = (∫⁻ t in Ioi 0, ∫⁻ y in Ilev x V t, ENNReal.ofReal (Gfun δ y))
          + ∫⁻ t in Ioi 0, (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal c) t :=
        lintegral_add_right _ hindm
    _ = _ := by rw [hind]

end GoldbachRH
