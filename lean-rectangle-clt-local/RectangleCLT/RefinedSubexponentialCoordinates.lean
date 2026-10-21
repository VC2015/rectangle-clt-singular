import RectangleCLT.RefinedSubexponentialAssembly
import RectangleCLT.SubexponentialCoordinates

/-! Proposition 5 in the actual original coordinate units. Positive
coordinate normalization changes the rectangle exactly, retains the
separate fourth-moment and tail scales, and computes every covariance
coefficient from the correlation matrix. -/

open MeasureTheory

namespace RectangleCLT
noncomputable section

/-- The matched combined sub-exponential bound for the original `X_i`.
The moment and tail assumptions concern exactly `X_ij/σ_j`, while the
Gaussian covariance and rectangle error use the original units. -/
theorem refinedSubexponentialCoordinatesRectangleCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p) (σ : Vector p) (hσ : ∀ j, 0 < σ j)
    {B4 K : ℝ}
    (h : SubexponentialHypotheses μ (coordinateStandardizedObservations X σ) B4 K)
    (hlocal : LocalCovarianceHypotheses
      (covariance μ (sumVector
        (sampleNormalizedObservations (coordinateStandardizedObservations X σ)))))
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (sumVector (sampleNormalizedObservations X)))
    (R : Rect p) :
    rectangleError μ (sumVector (sampleNormalizedObservations X)) A R ≤
      refinedSubexponentialProxyConstant * min 1
        (refinedSubexponentialRate n B4 K (covariance μ (sumVector
          (sampleNormalizedObservations (coordinateStandardizedObservations X σ))))) := by
  let Y := coordinateStandardizedObservations X σ
  let A_Y := rowScaledFactor (fun j => (σ j)⁻¹) A
  have hsum := coordinateStandardizedObservations_sample_sum X σ
  have hfactorY : A_Y * A_Y.transpose =
      covariance μ (sumVector (sampleNormalizedObservations Y)) := by
    ext j k
    dsimp only [A_Y, Y]
    rw [rowScaledFactor_covariance, hfactor, hsum, covariance_scaleCoordinates]
  have hb := refinedSubexponentialRectangleCLT h A_Y hlocal hfactorY
    (R.preimageCoordinateScale σ hσ)
  have heq := rectangleError_coordinateNormalize μ
    (sumVector (sampleNormalizedObservations X)) A σ hσ R
  rw [← hsum] at heq
  exact heq.le.trans hb

end
end RectangleCLT
