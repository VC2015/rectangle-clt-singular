import RectangleCLTCompanion.SubexponentialMain
import RectangleCLTCompanion.RectangleDistance

/-!
Corollary 2 in the actual rectangle-distance formulation of split-V4.
The underlying historical theorem supplies the genuine Orlicz contract,
average marginal normalization and exact Gaussian covariance factor.
These bridges do not certify the revised bounded relative-moment proof.
-/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- Corollary 2 for the actual supremum over every measurable rectangle.
The Orlicz hypothesis uses the genuine infimum, including its infinite
value when there is no integrable admissible exponential scale. -/
theorem subexponentialRectangleDistanceCLT_psi1
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      (2 * subexponentialUniversalConstant) *
        min 1 (unrestrictedRate (subexponentialScale n K) (dimensionLog p)) :=
  rectangleDistance_le μ (normalizedObservationSum X) A
    (subexponentialCLT_psi1 h hp hn haverage A hA)

/-- The Corollary 2 constant is fixed before dimensions, scales and
probability models. No eigenvalue, correlation gap or identical-law
hypothesis is added to the manuscript's upper bound. -/
theorem subexponentialRectangleDistanceCLTExists :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (p n : ℕ), 1 ≤ p → 1 ≤ n →
        ∀ (X : Fin n → Ω → Vector p) (K : ℝ)
          (A : Matrix (Fin p) (Fin p) ℝ),
          Psi1IndependentHypotheses μ X K →
          (∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1) →
          A * A.transpose = covariance μ (normalizedObservationSum X) →
          rectangleDistance μ (normalizedObservationSum X) A ≤
            C * min 1 (unrestrictedRate (subexponentialScale n K) (dimensionLog p)) := by
  refine ⟨2 * subexponentialUniversalConstant,
    by linarith [one_le_subexponentialUniversalConstant], ?_⟩
  intro Ω _ μ _ p n hp hn X K A h haverage hA
  exact subexponentialRectangleDistanceCLT_psi1 h hp hn haverage A hA

end

end RectangleCLT.Companion.SplitV4
