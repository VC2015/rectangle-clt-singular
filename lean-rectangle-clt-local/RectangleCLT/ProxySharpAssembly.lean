import RectangleCLT.ProxySecondMoment
import RectangleCLT.ProxySmoothing

/-! Actual unequal-covariance interpolation and endpoint integration. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology Interval

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem abs_selectorHeatDerivative_le_proxy_sharpAverages
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A 0 t| ≤
      (1 / 2 : ℝ) *
        proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
          (thinningProbability t) (thinningScale t) +
      t / 3 * gamma3 μ ξ * s.sharpThirdAverage μ ξ A t +
        6 * gamma4 μ ξ * s.sharpFourthAverage μ ξ A δ t := by
  have hHi (mask : Kane.Cube n) : Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      s.localConvolutionFourthSup A (4 * δ)
        (0 + thinningScale t • maskObservationSum ξ mask ω) t j k l m) μ :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg) t μ _
              (measurable_const.add (measurable_const.smul
                (measurable_maskObservationSum ξ h.measurable mask))) j k l m))))
  have hh := s.abs_selectorHeatDerivative_le_proxy_comparison μ ξ h A 0 ht ht1
    (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m)
    (fun x v hv j k l m => s.abs_convolutionFourthDerivative_le_localSup A x t hv j k l m) hHi
  rw [← s.sharpFourthAverage_eq_selectorEnvelope μ ξ h.measurable A h.delta_nonneg t] at hh
  exact hh


/-- The actual smoother gap, with the quadratic covariance cost integrated
using the proved pair-face cap, plus the existing signed cubic and actual
local fourth-derivative time integrals. -/
theorem interpolation_smoother_gap_le_proxy_timeIntegrals
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      proxySecondConstant *
        proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        dimensionLog p / pairGap (A * A.transpose) +
      gamma3 μ ξ / 3 * (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) +
      6 * gamma4 μ ξ * (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) := by
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose)
  have hΔ0 : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  let B := proxySecondConstant * dimensionLog p / pairGap (A * A.transpose)
  let f : ℝ → ℝ := fun t => t ^ (-(1 / 2 : ℝ))
  let g : ℝ → ℝ := fun t => Δ / 2 * B * f t +
    gamma3 μ ξ / 3 * (t * s.sharpThirdAverage μ ξ A t) +
    6 * gamma4 μ ξ * s.sharpFourthAverage μ ξ A δ t
  have hi2 : IntervalIntegrable f volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hi3 : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    (continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ h.measurable A)).intervalIntegrable_of_Icc
      (by norm_num)
  have hi4 : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    (s.continuousOn_sharpFourthAverage μ ξ h.measurable A h.delta_nonneg).intervalIntegrable_of_Icc
      (by norm_num)
  have hig : IntervalIntegrable g volume 0 1 :=
    (((hi2.const_mul (Δ / 2 * B)).add (hi3.const_mul (gamma3 μ ξ / 3))).add
      (hi4.const_mul (6 * gamma4 μ ξ)))
  have hsecond (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
        (thinningProbability t) (thinningScale t) ≤ B * f t := by
    have hh := s.selectorSecondAbsoluteSum_time_le_proxy μ ξ h hp hunit A hA hc hband ht.1 ht.2
    apply hh.trans_eq
    dsimp [B, f]
    rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
    ring
  have hg := s.interpolation_smoother_gap_le_integral μ h A
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hig)
    (fun t ht => by
      have hh := s.abs_selectorHeatDerivative_le_proxy_sharpAverages μ ξ h A ht.1.le ht.2.le
      have hm := mul_le_mul_of_nonneg_left (hsecond t ht)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hΔ0)
      exact hh.trans (by
        dsimp [g, Δ]
        nlinarith only [hm]))
  have hfi : (∫ t in (0 : ℝ)..1, f t) = 2 := by
    dsimp [f]
    rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num
  apply hg.trans_eq
  rw [intervalIntegral.integral_add
    ((hi2.const_mul _).add (hi3.const_mul _)) (hi4.const_mul _),
    intervalIntegral.integral_add (hi2.const_mul _) (hi3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hfi]
  dsimp [Δ, B]
  ring

end RectangleCLT.FaceSmoother
