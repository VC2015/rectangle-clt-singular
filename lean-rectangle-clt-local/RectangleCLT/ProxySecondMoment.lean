import RectangleCLT.ProxyDerivativeCaps
import RectangleCLT.GaussianComparisonAverage

/-! Jensen bounds for the actual common-point Hessian and its uniform
short-scale estimate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem sum_abs_second_le_bandwidth_sq_fourth (x : Vector p) :
    (∑ j, ∑ k, |s.mixedSecondDerivativeF x j k|) ≤
      3 * s.bandwidth ^ 2 *
        (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) := by
  let θ := (s.weights x).theta
  have hθ : 0 ≤ θ := (s.weights x).theta_nonneg
  have hpoly : θ ≤ 24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ := by
    nlinarith [pow_nonneg hθ 4, pow_nonneg hθ 3, sq_nonneg θ]
  have he : 1 ≤ (Real.exp 2) ^ 5 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  have hP : 0 ≤ 24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ := by positivity
  have hc : 0 ≤ 3 * s.F x / s.bandwidth ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (s.F_pos x).le) (sq_nonneg _)
  have hmass : (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) =
      (Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4) *
        (24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ) := by
    simp only [fourthLocalMajorant, ← Finset.mul_sum]
    rw [(s.weights x).sum_fourthMajorant]
  apply (s.sum_abs_mixedSecondDerivativeF_le_variance x).trans
  rw [hmass]
  have hscalar : θ ≤ (Real.exp 2) ^ 5 *
      (24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ) :=
    hpoly.trans (by nlinarith [mul_le_mul_of_nonneg_right he hP])
  have hh := mul_le_mul_of_nonneg_left hscalar hc
  convert hh using 1 <;>
    dsimp [θ, FaceWeights.theta, FaceSmoother.F] <;>
    field_simp [ne_of_gt s.bandwidth_pos] <;> ring

theorem sum_abs_convolutionSecond_le_bandwidth_sq_fourth
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x : Vector p) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative ν x j k|) ≤
      3 * s.bandwidth ^ 2 *
        (∑ j, ∑ k, ∑ l, ∑ m, s.convolutionFourthLocalMajorant ν x j k l m) := by
  have hi (j k : Fin p) :
      Integrable (fun z => s.mixedSecondDerivativeF (x + z) j k) ν :=
    s.integrable_secondDerivative_shift ν x j k
  have hW : Measurable (fun z : Vector p => x + z) := measurable_const.add measurable_id
  have hi4 := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_fourthLocalMajorant_comp ν _ hW j k l m))))
  calc
    _ ≤ ∑ j, ∑ k, ∫ z, |s.mixedSecondDerivativeF (x + z) j k| ∂ν := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [s.convolutionSecondDerivative_eq_integral]
      exact abs_integral_le_integral_abs
    _ = ∫ z, ∑ j, ∑ k, |s.mixedSecondDerivativeF (x + z) j k| ∂ν := by
      rw [integral_finset_sum Finset.univ (fun j _ =>
        integrable_finset_sum Finset.univ (fun k _ => (hi j k).abs))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finset_sum Finset.univ (fun k _ => (hi j k).abs)]
    _ ≤ ∫ z, 3 * s.bandwidth ^ 2 *
        (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (x + z) j k l m) ∂ν := by
      exact integral_mono
        (integrable_finset_sum Finset.univ (fun j _ =>
          integrable_finset_sum Finset.univ (fun k _ => (hi j k).abs)))
        (hi4.const_mul _) (fun z => s.sum_abs_second_le_bandwidth_sq_fourth (x + z))
    _ = _ := by rw [integral_const_mul, s.sum_convolutionFourthLocalMajorant_eq_integral]

noncomputable def selectorSecondExpectedAbsolute
    (ν : Measure (Vector p)) {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ mask, Kane.maskWeight q mask *
    ∫ ω, ∑ j, ∑ k,
      |s.convolutionSecondDerivative ν (x + a • maskObservationSum ξ mask ω) j k| ∂μ

theorem selectorSecondExpectedAbsolute_eq_integral_bernoulliArrayLaw
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorSecondExpectedAbsolute ν μ ξ x (thinningProbability t) (thinningScale t) =
      ∫ b, ∑ j, ∑ k,
        |s.convolutionSecondDerivative ν (x + arraySum b) j k| ∂bernoulliArrayLaw μ ξ t := by
  let G : Vector p → ℝ := fun y => ∑ j, ∑ k, |s.convolutionSecondDerivative ν y j k|
  have hG : Continuous G := continuous_finset_sum _ (fun j _ =>
    continuous_finset_sum _ (fun k _ => (s.continuous_convolutionSecondDerivative ν j k).abs))
  have hm : Measurable (fun b : Fin n → Vector p => G (x + arraySum b)) :=
    hG.measurable.comp (measurable_const.add (measurable_arraySum p n))
  have hGi (mask : Kane.Cube n) :
      Integrable (fun b : Fin n → Vector p => G (x + arraySum b))
        (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        (integrable_bounded_test_comp _ _
          (measurable_const.add (measurable_arraySum p n)) _
          (s.continuous_convolutionSecondDerivative ν j k) _
          (fun y => s.norm_convolutionSecondDerivative_le ν y j k)).abs))
  symm
  change (∫ b, G (x + arraySum b) ∂bernoulliArrayLaw μ ξ t) = _
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _ hGi]
  unfold selectorSecondExpectedAbsolute
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hm.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun ω => by
    change G (x + arraySum (retainedArray ξ t mask ω)) = _
    rw [arraySum_retainedArray_eq_maskObservationSum]))

theorem selectorSecondAbsoluteSum_le_expected
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (a : ℝ) :
    s.selectorSecondAbsoluteSum ν μ ξ x q a ≤
      s.selectorSecondExpectedAbsolute ν μ ξ x q a := by
  have hi (mask : Kane.Cube n) (j k : Fin p) : Integrable (fun ω =>
      s.convolutionSecondDerivative ν (x + a • maskObservationSum ξ mask ω) j k) μ :=
    integrable_bounded_test_comp μ _
      (measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))) _
      (s.continuous_convolutionSecondDerivative ν j k) _
      (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  have heq : s.selectorSecondExpectedAbsolute ν μ ξ x q a =
      ∑ j, ∑ k, ∑ mask, Kane.maskWeight q mask *
        ∫ ω, |s.convolutionSecondDerivative ν
          (x + a • maskObservationSum ξ mask ω) j k| ∂μ := by
    unfold selectorSecondExpectedAbsolute
    simp_rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (hi _ j k).abs)),
      integral_finset_sum Finset.univ (fun k _ => (hi _ _ k).abs)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [heq]
  unfold selectorSecondAbsoluteSum
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  unfold selectorSecondDerivativeAverage
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro mask _
  rw [abs_mul, abs_of_nonneg (Kane.maskWeight_nonneg hq hq1 mask)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
    (Kane.maskWeight_nonneg hq hq1 mask)

theorem selectorSecondExpectedAbsolute_le_fourth
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorSecondExpectedAbsolute ν μ ξ x (thinningProbability t) (thinningScale t) ≤
      3 * s.bandwidth ^ 2 * selectorFourthEnvelopeAverage μ ξ x t
        (s.convolutionFourthLocalMajorant ν) := by
  unfold selectorSecondExpectedAbsolute selectorFourthEnvelopeAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mask _
  have hW : Measurable (fun ω => x + thinningScale t • maskObservationSum ξ mask ω) :=
    measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))
  have hi2 := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (integrable_bounded_test_comp μ _ hW _ (s.continuous_convolutionSecondDerivative ν j k) _
        (fun y => s.norm_convolutionSecondDerivative_le ν y j k)).abs))
  have hi4 := s.integrable_sum_convolutionFourthLocalMajorant_mask ν μ ξ hξ x (thinningScale t) mask
  have hh := integral_mono hi2 (hi4.const_mul (3 * s.bandwidth ^ 2))
    (fun ω => s.sum_abs_convolutionSecond_le_bandwidth_sq_fourth ν _)
  rw [integral_const_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
  convert hm using 1 <;> ring

theorem selectorSecondAbsoluteSum_shortScale_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      (3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)) *
        Real.sqrt (dimensionLog p) / s.bandwidth := by
  let ν := gaussianLaw (Real.sqrt t • A)
  have hJ := s.selectorSecondAbsoluteSum_le_expected ν μ ξ h.measurable 0
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) (thinningScale t)
  have hF := s.selectorSecondExpectedAbsolute_le_fourth ν μ ξ h.measurable 0 ht ht1
  have hcap := s.selectorFourthEnvelopeAverage_shortScale_le_proxy μ ξ h hp hunit A hA hband ht ht1
  have hh := hJ.trans (hF.trans (mul_le_mul_of_nonneg_left hcap (by positivity)))
  convert hh using 1
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

noncomputable def proxySecondConstant : ℝ :=
  3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) +
    gaussianSecondAverageConstant

theorem proxySecondConstant_pos : 0 < proxySecondConstant := by
  have hp := gaussianSecondAverageConstant_pos
  unfold proxySecondConstant interpolationShortScaleConstant
  positivity

/-- The pair-face cap and short-scale averaging combine to give an
integrable time singularity for the actual common-point Hessian. -/
theorem selectorSecondAbsoluteSum_time_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      proxySecondConstant * dimensionLog p /
        (pairGap (A * A.transpose) * Real.sqrt t) := by
  let K := 3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  have hLK : K ≤ proxySecondConstant := by
    change K ≤ K + gaussianSecondAverageConstant
    linarith [gaussianSecondAverageConstant_pos]
  have hLC : gaussianSecondAverageConstant ≤ proxySecondConstant := by
    change gaussianSecondAverageConstant ≤ K + gaussianSecondAverageConstant
    linarith
  have hL : 0 < dimensionLog p := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  by_cases hlarge : s.bandwidth ^ 2 * dimensionLog p ≤ t
  · have hh := s.selectorSecondAbsoluteSum_le_expected
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0
      (thinningProbability_nonneg ht1.le) (thinningProbability_le_one ht.le) (thinningScale t)
    rw [s.selectorSecondExpectedAbsolute_eq_integral_bernoulliArrayLaw
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht.le ht1.le] at hh
    simp only [zero_add] at hh
    exact hh.trans ((s.integral_sum_abs_second_bernoulli_largeTime_le
      h hp hunit A hA hc hband ht ht1 hlarge).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hL.le)
        (mul_nonneg hc.le hroot.le)))
  · have hs := s.selectorSecondAbsoluteSum_shortScale_le_proxy μ ξ h hp hunit A hA
      hband ht.le ht1.le
    have htime : Real.sqrt t ≤ s.bandwidth * Real.sqrt (dimensionLog p) := by
      calc
        _ ≤ Real.sqrt (s.bandwidth ^ 2 * dimensionLog p) :=
          Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hlarge))
        _ = _ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq s.bandwidth_pos.le]
    have hct : pairGap (A * A.transpose) * Real.sqrt t ≤
        s.bandwidth * Real.sqrt (dimensionLog p) :=
      (mul_le_of_le_one_left hroot.le (pairGap_le_one _)).trans htime
    have hsmall : K * Real.sqrt (dimensionLog p) / s.bandwidth ≤
        K * dimensionLog p / (pairGap (A * A.transpose) * Real.sqrt t) := by
      apply (div_le_div_iff₀ s.bandwidth_pos (mul_pos hc hroot)).mpr
      have hm := mul_le_mul_of_nonneg_left hct
        (mul_nonneg hK (Real.sqrt_nonneg (dimensionLog p)))
      calc
        _ ≤ (K * Real.sqrt (dimensionLog p)) *
            (s.bandwidth * Real.sqrt (dimensionLog p)) := hm
        _ = K * s.bandwidth * (Real.sqrt (dimensionLog p)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hL.le]; ring
    exact hs.trans (hsmall.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLK hL.le)
        (mul_nonneg hc.le hroot.le)))

end RectangleCLT.FaceSmoother
