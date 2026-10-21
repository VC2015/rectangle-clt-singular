import RectangleCLT.ProxySharpAssembly

/-! Fundamental-theorem integration for an actual unequal covariance path.
The quadratic majorant is displayed explicitly so the final assembly can
supply independently selected, proved covariance alternatives. -/

open MeasureTheory Set

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem interpolation_smoother_gap_le_unequal_integrals
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (B2 : ℝ)
    (hsecond : ∀ t ∈ Ioo (0 : ℝ) 1,
      s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
        (thinningProbability t) (thinningScale t) ≤ B2 * t ^ (-(1 / 2 : ℝ))) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) * B2 +
      gamma3 μ ξ / 3 * (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) +
      6 * gamma4 μ ξ * (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) := by
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose)
  have hΔ0 : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  let B := B2
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
