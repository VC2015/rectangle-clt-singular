import RectangleCLT.ThinningMoments
import RectangleCLT.LocalMoments

/-! The covariance of a bounded independent sum is the sum of the actual
observation second-moment matrices. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.BoundedIndependentHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem covariance_sum (h : BoundedIndependentHypotheses μ ξ δ) (j k : Fin p) :
    covariance μ (sumVector ξ) j k = ∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
  have hi (i : Fin n) (j : Fin p) : Integrable (fun ω => ξ i ω j) μ := by
    simpa using integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
  have hip (i l : Fin n) (j k : Fin p) :
      Integrable (fun ω => ξ i ω j * ξ l ω k) μ := by
    apply (integrable_const (δ ^ 2)).mono'
      (((measurable_pi_apply j).comp (h.measurable i)).mul
        ((measurable_pi_apply k).comp (h.measurable l))).aestronglyMeasurable
    filter_upwards [h.abs_coordinate_le i j, h.abs_coordinate_le l k] with ω hij hlk
    simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
      mul_le_mul hij hlk (abs_nonneg _) (h.delta_nonneg)
  exact covariance_sum_of_centered_cross hi hip h.centered
    (independent_centered_cross_zero h.independent hi h.centered) j k

end RectangleCLT.BoundedIndependentHypotheses
