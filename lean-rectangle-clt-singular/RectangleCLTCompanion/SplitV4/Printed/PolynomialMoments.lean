import RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! The printed `E ‖X_i‖² ≤ B²` and `‖C_i^0‖max ≤ 2 B²`
intermediates in Appendix E.  The preserved proof bounded the same covariance
by `2 T²` and combined it directly with the tail probability; the moment route
printed in the manuscript is established here as well. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {p : ℕ} {μ : Measure (Vector p)} [IsProbabilityMeasure μ] {B T q : ℝ}

/-- The exact Lyapunov step stated in the printed clipping proof. -/
theorem norm_second_moment_le_envelope_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    (∫ x, ‖x‖ ^ 2 ∂μ) ≤ B ^ 2 := by
  have hq : 0 < q := by linarith [h.q_gt_two]
  have ha0 : 0 ≤ 2 / q := div_nonneg (by norm_num) hq.le
  have ha1 : 2 / q ≤ 1 := (div_le_one hq).mpr h.q_gt_two.le
  have heq (x : Vector p) : (‖x‖ ^ q) ^ (2 / q) = ‖x‖ ^ 2 := by
    rw [← Real.rpow_mul (norm_nonneg x), mul_div_cancel₀ _ hq.ne', Real.rpow_two]
  have hgi : Integrable ((fun u : ℝ => u ^ (2 / q)) ∘ (fun x : Vector p => ‖x‖ ^ q)) μ := by
    simpa only [Function.comp_def, heq] using
      integrable_norm_sq_of_envelope_moment μ h.q_gt_two.le h.integrable_q
  have hj := (Real.concaveOn_rpow ha0 ha1).le_map_integral
    (Real.continuous_rpow_const ha0).continuousOn isClosed_Ici
    (ae_of_all _ (fun x : Vector p => Real.rpow_nonneg (norm_nonneg x) q)) h.integrable_q hgi
  simp only [heq] at hj
  have hb := Real.rpow_le_rpow
    (integral_nonneg (fun x : Vector p => Real.rpow_nonneg (norm_nonneg x) q)) h.moment_le ha0
  have hB : (B ^ q) ^ (2 / q) = B ^ 2 := by
    rw [← Real.rpow_mul h.B_pos.le, mul_div_cancel₀ _ hq.ne', Real.rpow_two]
  exact hj.trans (hb.trans_eq hB)

theorem integrable_goodConditional_norm_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    Integrable (fun x : Vector p => ‖x‖ ^ 2) (goodConditionalLaw μ T) := by
  apply (integrable_const (T ^ 2)).mono' (measurable_norm.pow_const 2).aestronglyMeasurable
  filter_upwards [goodConditionalLaw_ae_norm_le μ h.threshold_pos.le] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  exact pow_le_pow_left₀ (norm_nonneg x) hx 2

/-- Conditioning on an event of probability at least `1/2` preserves this
second-moment bound with exactly the printed factor two. -/
theorem goodConditional_norm_second_moment_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    (∫ x, ‖x‖ ^ 2 ∂goodConditionalLaw μ T) ≤ 2 * B ^ 2 := by
  have hi := integrable_norm_sq_of_envelope_moment μ h.q_gt_two.le h.integrable_q
  have hs : (∫ x in goodTruncationSet T, ‖x‖ ^ 2 ∂μ) ≤ B ^ 2 :=
    (integral_mono_measure μ.restrict_le_self (ae_of_all _ (fun x => sq_nonneg ‖x‖)) hi).trans
      (norm_second_moment_le_envelope_sq h)
  have hp : (μ.real (goodTruncationSet T))⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀
      (lt_of_lt_of_le (by norm_num) h.good_probability_ge_half)).mpr
    linarith [h.good_probability_ge_half]
  rw [goodConditionalLaw, conditionalVectorLaw_eq_cond μ _ h.good_mass_ne_zero,
    ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real (goodTruncationSet T))⁻¹ *
    (∫ x in goodTruncationSet T, ‖x‖ ^ 2 ∂μ) ≤ _
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr measureReal_nonneg)).trans
    (mul_le_mul_of_nonneg_right hp (sq_nonneg B))

/-- A covariance entry is bounded by the average of its two centered
second moments, hence by the full squared-envelope moment. -/
theorem abs_good_covariance_le_norm_second_moment
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance (goodConditionalLaw μ T) id j k| ≤
      ∫ x, ‖x‖ ^ 2 ∂goodConditionalLaw μ T := by
  let m := conditionalGoodMean μ T
  let ν := goodConditionalLaw μ T
  have hT : 0 ≤ T := h.threshold_pos.le
  have hi (j k : Fin p) : Integrable (fun x : Vector p => (x - m) j * (x - m) k) ν := by
    apply (integrable_const ((2 * T) ^ 2)).mono'
      (((measurable_pi_apply j).sub measurable_const).mul
        ((measurable_pi_apply k).sub measurable_const)).aestronglyMeasurable
    filter_upwards [conditionalGood_ae_centered_norm_le μ h.threshold_pos.le] with x hx
    have hj := (norm_le_pi_norm (x - m) j).trans hx
    have hk := (norm_le_pi_norm (x - m) k).trans hx
    simpa only [Real.norm_eq_abs, norm_mul, Real.norm_eq_abs, pow_two] using
      mul_le_mul hj hk (norm_nonneg _) (by positivity : 0 ≤ 2 * T)
  have hid (j k : Fin p) : (∫ x : Vector p, (x - m) j * (x - m) k ∂ν) =
      covariance ν id j k := integral_conditionalGood_centered_pair μ h.threshold_pos.le j k
  have hdiag (j : Fin p) : covariance ν id j j ≤ ∫ x : Vector p, ‖x‖ ^ 2 ∂ν := by
    have hc : covariance ν id j j ≤ ∫ x : Vector p, x j ^ 2 ∂ν := by
      change (∫ x : Vector p, x j * x j ∂ν) - (∫ x : Vector p, x j ∂ν) *
        (∫ x : Vector p, x j ∂ν) ≤ _
      simp only [pow_two]
      nlinarith [sq_nonneg (∫ x : Vector p, x j ∂ν)]
    apply hc.trans
    apply integral_mono
      (by simpa only [pow_two] using integrable_goodConditional_coordinate_pair μ h.threshold_pos.le j j)
      (integrable_goodConditional_norm_sq h)
    intro x
    have hx : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x j)) hx 2
  have hab : |∫ x : Vector p, (x - m) j * (x - m) k ∂ν| ≤
      ∫ x : Vector p, |(x - m) j * (x - m) k| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun x : Vector p => (x - m) j * (x - m) k) (μ := ν)
  have hb := integral_mono (hi j k).abs (((hi j j).add (hi k k)).div_const 2)
    (fun x : Vector p => (show |(x - m) j * (x - m) k| ≤
      ((x - m) j * (x - m) j + (x - m) k * (x - m) k) / 2 by
        rw [abs_mul]
        nlinarith [sq_nonneg (|(x - m) j| - |(x - m) k|),
          sq_abs ((x - m) j), sq_abs ((x - m) k)]))
  simp only [Pi.add_apply, Pi.div_apply] at hb
  rw [integral_div, integral_add (hi j j) (hi k k), hid j j, hid k k] at hb
  rw [← hid j k]
  exact (hab.trans hb).trans (by linarith [hdiag j, hdiag k])

/-- The precise conditional covariance bound printed in Appendix E. -/
theorem abs_good_covariance_le_envelope_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance (goodConditionalLaw μ T) id j k| ≤ 2 * B ^ 2 :=
  (abs_good_covariance_le_norm_second_moment h j k).trans
    (goodConditional_norm_second_moment_le h)


/-- The unconditioned covariance bound printed immediately before the
conditional covariance estimate. -/
theorem abs_original_covariance_le_envelope_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance μ id j k| ≤ B ^ 2 := by
  have hi := integrable_norm_sq_of_envelope_moment μ h.q_gt_two.le h.integrable_q
  have hb : |∫ x : Vector p, x j * x k ∂μ| ≤ ∫ x : Vector p, ‖x‖ ^ 2 ∂μ := by
    apply (show |∫ x : Vector p, x j * x k ∂μ| ≤ ∫ x : Vector p, |x j * x k| ∂μ by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x : Vector p => x j * x k) (μ := μ)).trans
    apply integral_mono (h.integrable_coordinate_pair j k).abs hi
    intro x
    change |x j * x k| ≤ ‖x‖ ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul
      (show |x j| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
      (show |x k| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k)
      (abs_nonneg _) (norm_nonneg x)
  simpa only [covariance, id_eq, h.centered, zero_mul, sub_zero] using
    hb.trans (norm_second_moment_le_envelope_sq h)

/-- The printed second-moment covariance bound combines with Markov's
probability bound at the actual threshold. -/
theorem bad_probability_mul_envelope_sq_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    μ.real (goodTruncationSet T)ᶜ * B ^ 2 ≤ truncationVarianceBudget B T q := by
  have hBT : B ≤ T := by linarith [h.threshold, h.B_pos]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h.B_pos.le hBT 2)
    measureReal_nonneg).trans h.bad_probability_mul_threshold_sq_le


theorem abs_good_covariance_bias_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance (goodConditionalLaw μ T) id j k - covariance μ id j k| ≤
      4 * truncationVarianceBudget B T q := by
  rw [h.good_covariance_bias_identity j k]
  have hpT := bad_probability_mul_envelope_sq_le h
  have hpmean := mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ)
    (s := goodTruncationSet T)) h.varianceBudget_nonneg
  calc
    _ ≤ |μ.real (goodTruncationSet T)ᶜ * covariance (goodConditionalLaw μ T) id j k| +
        |μ.real (goodTruncationSet T) * (conditionalGoodMean μ T j * conditionalGoodMean μ T k)| +
        |∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ μ.real (goodTruncationSet T)ᶜ * (2 * B ^ 2) +
        μ.real (goodTruncationSet T) * truncationVarianceBudget B T q + truncationVarianceBudget B T q := by
      simp only [abs_mul, abs_of_nonneg measureReal_nonneg]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (abs_good_covariance_le_envelope_sq h j k) measureReal_nonneg)
        (mul_le_mul_of_nonneg_left
          (by simpa only [abs_mul] using h.abs_mean_coordinate_mul_le_varianceBudget j k) measureReal_nonneg))
        (h.abs_bad_coordinate_pair_integral_le j k)
    _ ≤ 4 * truncationVarianceBudget B T q := by nlinarith

theorem conditional_covariance_entry_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (mask : Fin n → Bool) (j k : Fin p) :
    |(conditionalCovarianceForMask μ T mask - originalAverageCovariance μ) j k| ≤
      4 * truncationVarianceBudget B T q + (2 * B ^ 2 / (n : ℝ)) * exceptionalCount mask := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint (i : Fin n) :
      |(if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k| ≤
        4 * truncationVarianceBudget B T q + 2 * B ^ 2 * (if mask i then 1 else 0) := by
    have he : (if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k =
        (covariance (goodConditionalLaw (μ i) T) id j k - covariance (μ i) id j k) -
          (if mask i then covariance (goodConditionalLaw (μ i) T) id j k else 0) := by
      split_ifs <;> ring
    rw [he]
    apply (abs_sub _ _).trans
    apply add_le_add (abs_good_covariance_bias_le (h i) j k)
    by_cases hi : mask i = true
    · simpa only [hi, if_true, mul_one] using abs_good_covariance_le_envelope_sq (h i) j k
    · have hi' : mask i = false := Bool.eq_false_iff.mpr hi
      simp only [hi', Bool.false_eq_true, if_false, abs_zero, mul_zero, le_refl]
  unfold conditionalCovarianceForMask originalAverageCovariance
  simp only [Matrix.sub_apply, ← mul_sub, ← Finset.sum_sub_distrib]
  calc
    _ = (1 / (n : ℝ)) * |∑ i,
      ((if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k)| := by
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hnR)]
    _ ≤ (1 / (n : ℝ)) * ∑ i,
      |(if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (one_div_pos.mpr hnR).le
    _ ≤ (1 / (n : ℝ)) * ∑ i,
      (4 * truncationVarianceBudget B T q + 2 * B ^ 2 * (if mask i then 1 else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpoint i) (one_div_pos.mpr hnR).le
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, exceptionalCount]
      field_simp
      ring

theorem conditional_covariance_max_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (mask : Fin n → Bool) :
    matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - originalAverageCovariance μ) ≤
      4 * truncationVarianceBudget B T q + (2 * B ^ 2 / (n : ℝ)) * exceptionalCount mask := by
  let i : Fin n := ⟨0, by omega⟩
  have hv := (h i).varianceBudget_nonneg
  have hcount : 0 ≤ exceptionalCount mask := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hnonneg : 0 ≤ 4 * truncationVarianceBudget B T q + (2 * B ^ 2 / (n : ℝ)) * exceptionalCount mask := by
    positivity
  unfold matrixMaxEntryNorm
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro k
  simpa only [Real.norm_eq_abs] using conditional_covariance_entry_deviation_le μ h hn mask j k

theorem expected_conditional_covariance_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    (∫ x, matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T (observedTruncationMask T x) - originalAverageCovariance μ)
      ∂Measure.pi μ) ≤ 6 * truncationVarianceBudget B T q := by
  let i : Fin n := ⟨0, by omega⟩
  have hv := (h i).varianceBudget_nonneg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let D : (Fin n → Vector p) → ℝ := fun x => matrixMaxEntryNorm
    (conditionalCovarianceForMask μ T (observedTruncationMask T x) - originalAverageCovariance μ)
  let R : (Fin n → Vector p) → ℝ := fun x =>
    4 * truncationVarianceBudget B T q + (2 * B ^ 2 / (n : ℝ)) * exceptionalCount (observedTruncationMask T x)
  have hR : Integrable R (Measure.pi μ) :=
    (integrable_const _).add ((integrable_finset_sum Finset.univ
      (fun i _ => integrable_observed_exceptional_indicator μ T i)).const_mul _)
  have hmD : Measurable D :=
    (measurable_of_countable (fun mask : Fin n → Bool =>
      matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - originalAverageCovariance μ))).comp
        (measurable_observedTruncationMask T)
  have hD : Integrable D (Measure.pi μ) := hR.mono' hmD.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ D x from norm_nonneg _)]
      exact conditional_covariance_max_deviation_le μ h hn _)
  have hs : (∑ i, (μ i).real (goodTruncationSet T)ᶜ * B ^ 2) ≤ (n : ℝ) * truncationVarianceBudget B T q := by
    calc
      _ ≤ ∑ _i : Fin n, truncationVarianceBudget B T q :=
        Finset.sum_le_sum (fun i _ => bad_probability_mul_envelope_sq_le (h i))
      _ = _ := by simp
  have hcost : (2 * B ^ 2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ) ≤
      2 * truncationVarianceBudget B T q := by
    calc
      _ = (2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ * B ^ 2) := by
        simp only [← Finset.sum_mul]
        ring
      _ ≤ (2 / (n : ℝ)) * ((n : ℝ) * truncationVarianceBudget B T q) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp; ring
  calc
    (∫ x, D x ∂Measure.pi μ) ≤ ∫ x, R x ∂Measure.pi μ :=
      integral_mono hD hR (fun x => conditional_covariance_max_deviation_le μ h hn _)
    _ = 4 * truncationVarianceBudget B T q +
        (2 * B ^ 2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ) := by
      dsimp only [R, exceptionalCount]
      rw [integral_add (integrable_const _)
        ((integrable_finset_sum Finset.univ (fun i _ => integrable_observed_exceptional_indicator μ T i)).const_mul _)]
      simp only [integral_const_mul]
      rw [integral_finset_sum Finset.univ (fun i _ => integrable_observed_exceptional_indicator μ T i)]
      simp only [integral_const, measureReal_univ_eq_one, one_smul, integral_observed_exceptional_indicator]
    _ ≤ 6 * truncationVarianceBudget B T q := by linarith

theorem expected_conditional_covariance_deviation_actual {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    (∫ x, matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T (observedTruncationMask T x) -
        covariance (Measure.pi μ) (normalizedObservationSum (fun i x => x i))) ∂Measure.pi μ) ≤
      6 * truncationVarianceBudget B T q := by
  rw [product_normalized_covariance_eq_average μ h hn]
  exact expected_conditional_covariance_deviation_le μ h hn
end
end RectangleCLT.Companion.SplitV4.Printed
