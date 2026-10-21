import RectangleCLT.GaussianFourthFinal
import RectangleCLT.ProxyBernoulli

/-! Actual derivative caps along the unequal-covariance Bernoulli path.
The true bounded-sum covariance and Gaussian proxy need only have unit
coordinate variances; covariance equality is not assumed. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology Interval

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem interpolationFourthMajorantIntegral_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.interpolationFourthMajorantIntegral μ ξ A t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let B := bernoulliArrayLaw μ ξ t
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hsqrt {v : ℝ} (hv : 1 / 2 ≤ v) := sqrt_dimensionLog_div_le_two_sqrt hp hv
  have hC0 : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 := by positivity
  by_cases hhalf : t ≤ 1 / 2
  · have hv : 0 < 1 - t := by linarith
    have hraw := (h.thinned t ht ht1).integral_sum_fourthLocalMajorant_independent_shift_le
      hp hv (h.thinned_sum_unit_diagonal hunit t ht ht1) s ν id measurable_id
    have hlen : s.bandwidth + 2 * δ ≤ 2 * s.bandwidth := by linarith [h.delta_nonneg]
    calc
      _ ≤ (75 * (Real.exp 2) ^ 5) *
          (2147483648 * (s.bandwidth + 2 * δ) * Real.sqrt (dimensionLog p / (1 - t))) /
            s.bandwidth ^ 4 := hraw
      _ ≤ (75 * (Real.exp 2) ^ 5) *
          (2147483648 * (2 * s.bandwidth) * (2 * Real.sqrt (dimensionLog p))) /
            s.bandwidth ^ 4 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlen (by norm_num))
          (hsqrt (by linarith)) (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) s.bandwidth_pos.le))
      _ = (75 * (Real.exp 2) ^ 5 * 8589934592) *
          Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
        field_simp [ne_of_gt s.bandwidth_pos]
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC0
        unfold interpolationShortScaleConstant
        linarith [Real.exp_pos (3 / 2 : ℝ)]
  · have hthalf : 1 / 2 ≤ t := le_of_lt (lt_of_not_ge hhalf)
    have htpos : 0 < t := by linarith
    have hdiag (j : Fin p) :
        ((Real.sqrt t • A) * (Real.sqrt t • A).transpose) j j = t := by
      have hh := congrArg (fun M : Matrix (Fin p) (Fin p) ℝ => M j j)
        (interpolatedGaussian_covariance A ht)
      rw [covariance_gaussianLaw] at hh
      change ((Real.sqrt t • A) * (Real.sqrt t • A).transpose) j j = t * (A * A.transpose) j j at hh
      simpa only [hA, mul_one] using hh
    have hraw := s.gaussian_integral_sum_fourthLocalMajorant_independent_shift_le hp
      (Real.sqrt t • A) htpos hdiag B arraySum (measurable_arraySum p n)
    have heq : s.interpolationFourthMajorantIntegral μ ξ A t =
        (∫ z : Vector p × (Fin n → Vector p), ∑ j, ∑ k, ∑ l, ∑ m,
          s.fourthLocalMajorant (z.1 + arraySum z.2) j k l m ∂ν.prod B) := by
      unfold interpolationFourthMajorantIntegral
      change (∫ z : (Fin n → Vector p) × Vector p, ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant (arraySum z.1 + z.2) j k l m ∂B.prod ν) = _
      rw [← integral_prod_swap (fun z : (Fin n → Vector p) × Vector p =>
        ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (arraySum z.1 + z.2) j k l m)]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        change (∑ j, ∑ k, ∑ l, ∑ m,
          s.fourthLocalMajorant (arraySum z.2 + z.1) j k l m) = _
        simp only [add_comm])
    rw [heq]
    calc
      _ ≤ (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
          Real.sqrt (dimensionLog p / t) / s.bandwidth ^ 3 := hraw
      _ ≤ (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
          (2 * Real.sqrt (dimensionLog p)) / s.bandwidth ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        exact mul_le_mul_of_nonneg_left (hsqrt hthalf) (by positivity)
      _ = (75 * (Real.exp 2) ^ 5 * (2 * Real.exp (3 / 2 : ℝ))) *
          Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC0
        unfold interpolationShortScaleConstant
        linarith

theorem selectorFourthEnvelopeAverage_shortScale_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    selectorFourthEnvelopeAverage μ ξ 0 t
      (s.convolutionFourthLocalMajorant (gaussianLaw (Real.sqrt t • A))) ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  rw [s.selectorFourthEnvelopeAverage_eq_prod_integral
    (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht ht1]
  simpa only [zero_add] using
    s.interpolationFourthMajorantIntegral_le_proxy μ ξ h hp hunit A hA hband ht ht1

theorem sharpFourthAverage_shortScale_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.sharpFourthAverage μ ξ A δ t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  rw [s.sharpFourthAverage_eq_selectorEnvelope μ ξ h.measurable A h.delta_nonneg t]
  have hc : selectorFourthEnvelopeAverage μ ξ 0 t
      (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m) ≤
      selectorFourthEnvelopeAverage μ ξ 0 t
        (s.convolutionFourthLocalMajorant (gaussianLaw (Real.sqrt t • A))) := by
    unfold selectorFourthEnvelopeAverage
    apply Finset.sum_le_sum
    intro mask _
    apply mul_le_mul_of_nonneg_left _
      (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
    let W : Ω → Vector p := fun ω => 0 + thinningScale t • maskObservationSum ξ mask ω
    have hW : Measurable W := measurable_const.add
      (measurable_const.smul (measurable_maskObservationSum ξ h.measurable mask))
    have hi := integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg) t μ W hW j k l m))))
    have hj := s.integrable_sum_convolutionFourthLocalMajorant_mask
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 (thinningScale t) mask
    apply integral_mono hi hj
    intro ω
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
        s.localConvolutionFourthSup_le_coarseMajorant A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg)
          (by linarith [h.delta_nonneg]) _ t j k l m
  exact hc.trans (s.selectorFourthEnvelopeAverage_shortScale_le_proxy μ ξ h hp hunit A hA hband ht ht1)

/-- The actual fourth-order integral retains the proxy's local covariance
cost under unequal covariances. Every derivative cap is supplied by a
proved theorem about the concrete path. -/
theorem integral_sharpFourthAverage_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hproxy : LocalCovarianceHypotheses (A * A.transpose))
    (hband : 12 * δ ≤ s.bandwidth) :
    (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
      (3 * gaussianFourthConstant) * dimensionLog p * Real.sqrt (dimensionLog p) /
        (s.bandwidth * Real.rpow
          (pairGap (A * A.transpose) * a3 (A * A.transpose) * a4 (A * A.transpose))
            (2 / 3 : ℝ)) := by
  let Q := A * A.transpose
  let cost := pairGap Q * a3 Q * a4 Q
  have hc := hproxy.pairGap_pos hp
  have ha₃ := hproxy.a3_pos hp
  have ha₄ := hproxy.a4_pos
  have hcost : 0 < cost := mul_pos (mul_pos hc ha₃) ha₄
  have hc1 : pairGap Q ≤ 1 := pairGap_le_one Q
  have ha31 : a3 Q ≤ 1 :=
    (a3_le_pairGap hp hproxy.posSemidef hproxy.unit_diagonal).trans hc1
  have ha41 : a4 Q ≤ 1 := (a4_le_a3 hp hproxy.posSemidef).trans ha31
  have hca : pairGap Q * a3 Q ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hc1 ha31 ha₃.le (by norm_num : (0 : ℝ) ≤ 1)
  have hcost1 : cost ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hca ha41 ha₄.le (by norm_num : (0 : ℝ) ≤ 1)
  have hD : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    (s.continuousOn_sharpFourthAverage μ ξ hdata.measurable A hdata.delta_nonneg).intervalIntegrable_of_Icc
      (by norm_num)
  have hsmallCap (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      s.sharpFourthAverage μ ξ A δ t ≤
        gaussianFourthConstant * Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 :=
    (s.sharpFourthAverage_shortScale_le_proxy μ ξ hdata hp hunit A hproxy.unit_diagonal
      hband ht.1.le ht.2.le).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right gaussianFourthConstant_ge_short (Real.sqrt_nonneg _))
        (pow_nonneg s.bandwidth_pos.le _))
  have hQ3 : LocalCovarianceLower Q 3 (a3 Q) :=
    localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hproxy.posSemidef)
  have hQ4 : LocalCovarianceLower Q 4 (a4 Q) :=
    localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hproxy.posSemidef)
  have hlarge (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
      (hb : s.bandwidth ^ 2 * dimensionLog p ≤ t) :
      s.sharpFourthAverage μ ξ A δ t ≤
        gaussianFourthConstant / cost * (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by
    exact s.sharpFourthAverage_largeTime_le hdata hp hunit A
      hQ3 ha₃ hQ4 ha₄ (a4_le_a3 hp hproxy.posSemidef)
      (a3_le_pairGap hp hproxy.posSemidef hproxy.unit_diagonal)
      hproxy.unit_diagonal hc hband ht.1 ht.2 hb
  have hh := integral_fourth_time_le_of_covariance_cost gaussianFourthConstant_pos.le
    hcost hcost1 (log_exp_mul_nat_ge_one hp) s.bandwidth_pos hD hsmallCap hlarge
  have hL : 0 < dimensionLog p :=
    lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hLpow : (dimensionLog p) ^ (3 / 2 : ℝ) =
      dimensionLog p * Real.sqrt (dimensionLog p) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  change (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
    3 * gaussianFourthConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
      (s.bandwidth * cost ^ (2 / 3 : ℝ)) at hh
  rw [hLpow] at hh
  convert hh using 1 <;> simp only [Real.rpow_eq_pow] <;> dsimp [cost, Q] <;> ring

end RectangleCLT.FaceSmoother
