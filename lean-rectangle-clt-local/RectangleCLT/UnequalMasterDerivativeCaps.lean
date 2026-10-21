import RectangleCLT.GlobalDerivativeAveragedCaps
import RectangleCLT.GlobalDerivativeIntegration
import RectangleCLT.ProxySharpAssembly

/-! Actual cubic and fourth-order integral alternatives with unequal
covariances. Three-coordinate positivity is used only for the cubic local
entry; neither covariance equality nor four-coordinate positivity is
silently imposed on that entry. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem sharpThirdAverage_le_of_a3
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose))
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    s.sharpThirdAverage μ ξ A t ≤
      gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap (A * A.transpose) * a * t ^ (3 / 2 : ℝ)) := by
  let B := gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
    (pairGap (A * A.transpose) * a * t ^ (3 / 2 : ℝ))
  have hi (mask : Kane.Cube n) := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        (s.integrable_convolutionThirdDerivative_mask (gaussianLaw (Real.sqrt t • A))
          μ ξ hξ 0 (thinningScale t) mask j k l).abs)))
  have hm (mask : Kane.Cube n) :
      (∫ ω, ∑ j, ∑ k, ∑ l,
        |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A))
          (0 + thinningScale t • maskObservationSum ξ mask ω) j k l| ∂μ) ≤ B := by
    have hh := integral_mono (hi mask) (integrable_const B) (fun ω =>
      s.sum_abs_convolutionThirdDerivative_gaussian_sqrt_le hp A _ ht hQ ha hdiag hc hac)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh
  unfold sharpThirdAverage selectorThirdAbsoluteAverage
  calc
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask * B :=
      Finset.sum_le_sum (fun mask _ => mul_le_mul_of_nonneg_left (hm mask)
        (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1)
          (thinningProbability_le_one ht.le) mask))
    _ = B := by rw [← Finset.sum_mul, Kane.maskWeight_sum, one_mul]

theorem integral_time_mul_sharpThirdAverage_le_of_a3
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
      2 * gaussianThirdConstant * dimensionLog p * Real.sqrt (dimensionLog p) /
        (pairGap (A * A.transpose) * a) := by
  have hD : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    (continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ hξ A)).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hL : 0 < dimensionLog p :=
    lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hh := integral_time_mul_third_le (B := gaussianThirdConstant *
    (dimensionLog p) ^ (3 / 2 : ℝ) / (pairGap (A * A.transpose) * a)) hD (fun t ht => by
      have hb := s.sharpThirdAverage_le_of_a3 μ ξ hξ hp A hQ ha hdiag hc hac ht.1 ht.2.le
      apply hb.trans_eq
      rw [Real.rpow_neg ht.1.le]
      ring)
  have hpL : (dimensionLog p) ^ (3 / 2 : ℝ) =
      dimensionLog p * Real.sqrt (dimensionLog p) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpL] at hh
  convert hh using 1 <;> ring

theorem integral_time_mul_sharpThirdAverage_le_full
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) :
    (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
      2 * globalThirdAverageConstant * dimensionLog p * Real.sqrt (dimensionLog p) / ν := by
  have hD : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    (continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ hξ A)).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hh := integral_time_mul_third_le
    (B := globalThirdAverageConstant * dimensionLog p * Real.sqrt (dimensionLog p) / ν)
    hD (fun t ht => by
      convert s.sharpThirdAverage_global_le μ ξ hξ hp A hdiag hν hlower ht.1 ht.2.le
        using 1 <;> ring)
  convert hh using 1 <;> ring

theorem integral_sharpFourthAverage_le_full_proxy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) :
    (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
      3 * globalFourthAverageConstant * dimensionLog p * Real.sqrt (dimensionLog p) /
        (ν * s.bandwidth) := by
  have hC : 0 ≤ globalFourthAverageConstant := globalFourthAverageConstant_pos.le
  have hCshort : 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant ≤
      globalFourthAverageConstant :=
    gaussianFourthConstant_ge_short.trans globalFourthAverageConstant_ge_short
  have hD : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    (s.continuousOn_sharpFourthAverage μ ξ hdata.measurable A hdata.delta_nonneg).intervalIntegrable_of_Icc
      (by norm_num)
  have hsmallCap (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      s.sharpFourthAverage μ ξ A δ t ≤
        globalFourthAverageConstant * Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 :=
    (s.sharpFourthAverage_shortScale_le_proxy μ ξ hdata hp hunit A hdiag hband
      ht.1.le ht.2.le).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCshort (Real.sqrt_nonneg _))
        (pow_nonneg s.bandwidth_pos.le 3))
  exact integral_fourth_time_le_full_eigenvalue hC hν (log_exp_mul_nat_ge_one hp)
    s.bandwidth_pos hD hsmallCap (fun t ht htime =>
      s.sharpFourthAverage_global_largeTime_le hdata hp hunit A hdiag hν hlower
        hband ht.1 ht.2 htime)

end

end RectangleCLT.FaceSmoother
