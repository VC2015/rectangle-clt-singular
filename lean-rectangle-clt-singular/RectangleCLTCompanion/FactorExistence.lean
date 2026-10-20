import RectangleCLTCompanion.SupportCoordinates

/-! Every bounded independent array has an actual square covariance factor,
including when the covariance is singular.  Thus the Gaussian factor
parameter in the companion CLT statements is available for every admissible
probability model; no covariance lower bound is needed to choose it. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

theorem covariance_posSemidef_of_boundedIndependent
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) :
    (covariance μ (sumVector ξ)).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact covariance_transpose μ (sumVector ξ)
  · intro v
    have hquad : 0 ≤ matrixQuadratic (covariance μ (sumVector ξ)) v := by
      rw [← sum_integral_observation_projection_sq h]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => sq_nonneg _))
    simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hquad

/-- The concrete Gaussian representation required by the three companion
rates exists for every bounded independent array, without rank restrictions. -/
theorem gaussian_factor_exists_of_boundedIndependent
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector ξ) := by
  let hCov := covariance_posSemidef_of_boundedIndependent h
  refine ⟨hCov.sqrt, ?_⟩
  have hsymmetric : hCov.sqrt.transpose = hCov.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hCov.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hCov.sqrt_mul_self

end RectangleCLT.Companion
