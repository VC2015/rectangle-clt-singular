import RectangleCLT.Statement
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Every admissible covariance has an actual Gaussian factor.
This rules out vacuity of the factor quantifier in the intended CLT.
No central limit estimate is proved here. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

theorem BoundedHypotheses.covariance_posSemidef {Ω : Type u}
    [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {δ b : ℝ}
    (h : BoundedHypotheses μ ξ δ b) :
    (covariance μ (sumVector ξ)).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact covariance_transpose μ (sumVector ξ)
  · intro v
    have hzero : 0 ≤ b ^ 2 * (∑ j, (v j) ^ 2) :=
      mul_nonneg (sq_nonneg b) (Finset.sum_nonneg fun j _ => sq_nonneg (v j))
    have hquad := hzero.trans (h.spectral_lower v)
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hquad

/-- The factor required by `BoundedRectangleCLT` exists for every admissible
array, by the positive semidefinite matrix square root in mathlib. -/
theorem BoundedHypotheses.gaussian_factor_exists {Ω : Type u}
    [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {δ b : ℝ}
    (h : BoundedHypotheses μ ξ δ b) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector ξ) := by
  let hCov := h.covariance_posSemidef
  refine ⟨hCov.sqrt, ?_⟩
  have hsymmetric : hCov.sqrt.transpose = hCov.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hCov.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hCov.sqrt_mul_self

end RectangleCLT
