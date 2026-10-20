import RectangleCLT

/-! Semantic checks of singular covariance, actual probability-law endpoints,
Gaussian factors, and the quantified conditional reduction. -/

open MeasureTheory

namespace RectangleCLT.LocalChecks

example : LocalCovarianceHypotheses LocalExamples.simplexMatrix :=
  ⟨LocalExamples.simplexMatrix_posSemidef, LocalExamples.simplexMatrix_diagonal,
    LocalExamples.simplexMatrix_a4_pos⟩

example : ∃ v : Vector 5, v ≠ 0 ∧ LocalExamples.simplexMatrix.mulVec v = 0 :=
  ⟨fun _ => 1, LocalExamples.allOnes_ne_zero, LocalExamples.simplexMatrix_allOnes_kernel⟩

/-- The same covariance is admitted locally and excluded by every strictly
positive global quadratic lower bound. -/
example (a : ℝ) (ha : 0 < a) :
    ¬∀ v : Vector 5, a * vectorNormSq v ≤ matrixQuadratic LocalExamples.simplexMatrix v :=
  LocalExamples.simplexMatrix_no_positive_global_lower a ha

example : covariance (gaussianLaw (0 : Matrix (Fin 1) (Fin 1) ℝ)) id = 0 := by
  rw [covariance_gaussianLaw]
  simp

example : covariance (gaussianLaw (1 : Matrix (Fin 1) (Fin 1) ℝ)) id = 1 := by
  rw [covariance_gaussianLaw]
  simp

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    interpolationLaw μ ξ A 0 = μ.map (sumVector ξ) ∧
      interpolationLaw μ ξ A 1 = gaussianLaw A :=
  ⟨interpolationLaw_zero μ ξ hξ A, interpolationLaw_one μ ξ A⟩

/-- A zero fourth moment still gives an admissible strictly positive bandwidth
when the original unit-variance observations have a positive envelope. -/
example (δ L c a₃ a₄ : ℝ) (hδ : 0 < δ)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    12 * δ ≤ localOptimizedBandwidth δ 0 L c a₃ a₄ ∧
      0 < localOptimizedBandwidth δ 0 L c a₃ a₄ :=
  ⟨twelve_delta_le_localOptimizedBandwidth hc ha₃ ha₄,
    localOptimizedBandwidth_pos hδ hc ha₃ ha₄⟩

end RectangleCLT.LocalChecks
