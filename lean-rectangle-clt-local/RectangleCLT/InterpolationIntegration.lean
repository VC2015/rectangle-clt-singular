import RectangleCLT.InterpolationContinuity
import RectangleCLT.LocalMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integrating a proved derivative bound for the actual interpolation.
Continuity and differentiability are discharged by the concrete path; the
remaining comparison bound is displayed explicitly in the theorem type. -/

open MeasureTheory Set
open scoped Interval

namespace RectangleCLT

theorem abs_sub_le_integral_of_derivative_bound
    {P d g : ℝ → ℝ} (hc : ContinuousOn P (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (d t) t)
    (hg : IntegrableOn g (Icc 0 1))
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, |d t| ≤ g t) :
    |P 1 - P 0| ≤ ∫ t in (0 : ℝ)..1, g t := by
  have hp := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hc
    (fun t ht => (hd t ht).hasDerivWithinAt) hg
    (fun t ht => (abs_le.mp (hbound t ht)).2)
  have hn := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hc.neg
    (fun t ht => (hd t ht).neg.hasDerivWithinAt) hg
    (fun t ht => by linarith [(abs_le.mp (hbound t ht)).1])
  exact abs_le.mpr ⟨by linarith, hp⟩

namespace FaceSmoother

theorem interpolation_smoother_gap_le_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 1))
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
      |s.selectorHeatDerivative μ ξ A 0 t| ≤ g t) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      ∫ t in (0 : ℝ)..1, g t := by
  have hh := abs_sub_le_integral_of_derivative_bound
    (s.continuousOn_integral_interpolationLaw μ ξ h.measurable A)
    (fun t ht => s.hasDerivAt_integral_interpolationLaw μ ξ h.measurable
      h.delta_nonneg h.bounded A ht.1 ht.2) hg hbound
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => h.measurable i)
  rw [interpolationLaw_zero μ ξ h.measurable A, interpolationLaw_one μ ξ A,
    integral_map hW.aemeasurable s.continuous_F.aestronglyMeasurable] at hh
  simpa only [abs_sub_comm] using hh

end FaceSmoother

end RectangleCLT
