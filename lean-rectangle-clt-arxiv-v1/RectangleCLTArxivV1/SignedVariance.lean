import RectangleCLTArxivV1.SignedObservations
import RectangleCLTCompanion.SupportCoordinates

/-! # Actual covariance of signed observation contrasts -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ξ : Fin n → Ω → RectangleCLT.Vector p} {δ : ℝ}

/-- The actual contrast variances sum to the covariance quadratic form. -/
theorem sum_variance_signedContrast (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) :
    (∑ i, ∫ ω, signedContrast ξ s t i ω ^ 2 ∂μ) =
      matrixQuadratic (covariance μ (sumVector ξ)) (signedDirection t - signedDirection s) := by
  simp only [signedContrast_eq_dotProduct]
  exact RectangleCLT.Companion.sum_integral_observation_projection_sq h _

/-- A zero canonical variance forces every constituent signed contrast to
vanish almost surely, so no positive variance assumption is needed. -/
theorem signedContrast_ae_zero_of_quadratic_zero (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p)
    (hzero : matrixQuadratic (covariance μ (sumVector ξ))
      (signedDirection t - signedDirection s) = 0) (i : Fin n) :
    signedContrast ξ s t i =ᵐ[μ] 0 := by
  have hh := RectangleCLT.Companion.observation_projection_ae_zero_of_quadratic_zero h
    (signedDirection t - signedDirection s) hzero i
  filter_upwards [hh] with ω hω
  simpa only [signedContrast_eq_dotProduct] using hω

end RectangleCLTArxivV1
