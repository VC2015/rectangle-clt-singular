import RectangleCLT.SubexponentialAssembly
import RectangleCLT.CoordinateRescaling

/-!
# The sub-exponential corollary in the original coordinate units

The observations below are the actual `X_i`.  Their standardized versions
are exactly `Y_ij = X_ij / σ_j`, with arbitrary positive coordinate scales.
All interval endpoints are handled by the exact diagonal rectangle map.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def coordinateStandardizedObservations {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (σ : Vector p) : Fin n → Ω → Vector p :=
  fun i ω j => X i ω j / σ j

theorem coordinateStandardizedObservations_restore {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (σ : Vector p) (hσ : ∀ j, 0 < σ j)
    (i : Fin n) (ω : Ω) :
    scaleCoordinates σ (coordinateStandardizedObservations X σ i ω) = X i ω := by
  funext j
  simp only [scaleCoordinates, coordinateStandardizedObservations]
  field_simp [(hσ j).ne']

theorem coordinateStandardizedObservations_sample_sum {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (σ : Vector p) :
    sumVector (sampleNormalizedObservations (coordinateStandardizedObservations X σ)) =
      fun ω => scaleCoordinates (fun j => (σ j)⁻¹)
        (sumVector (sampleNormalizedObservations X) ω) := by
  funext ω j
  simp only [sumVector, sampleNormalizedObservations, coordinateStandardizedObservations,
    scaleCoordinates, Finset.sum_apply, div_eq_mul_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coordinateStandardizedObservations_sample_restore {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (σ : Vector p) (hσ : ∀ j, 0 < σ j) :
    sumVector (sampleNormalizedObservations X) = fun ω => scaleCoordinates σ
      (sumVector (sampleNormalizedObservations (coordinateStandardizedObservations X σ)) ω) := by
  rw [coordinateStandardizedObservations_sample_sum]
  funext ω
  exact (scaleCoordinates_inverse_cancel σ _ hσ).symm

namespace SubexponentialHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
  {X : Fin n → Ω → Vector p} {σ : Vector p} {B4 K : ℝ}

/-- The standardized hypotheses imply the paper's hypotheses on the actual
original observations, through the invertible positive coordinate map. -/
theorem original_measurable
    (h : SubexponentialHypotheses μ (coordinateStandardizedObservations X σ) B4 K)
    (hσ : ∀ j, 0 < σ j) (i : Fin n) : Measurable (X i) := by
  have heq : X i = fun ω =>
      scaleCoordinates σ (coordinateStandardizedObservations X σ i ω) := by
    funext ω
    exact (coordinateStandardizedObservations_restore X σ hσ i ω).symm
  rw [heq]
  exact (measurable_scaleCoordinates σ).comp (h.measurable i)

theorem original_independent
    (h : SubexponentialHypotheses μ (coordinateStandardizedObservations X σ) B4 K)
    (hσ : ∀ j, 0 < σ j) : iIndepFun X μ := by
  have heq : X = fun i ω =>
      scaleCoordinates σ (coordinateStandardizedObservations X σ i ω) := by
    funext i ω
    exact (coordinateStandardizedObservations_restore X σ hσ i ω).symm
  rw [heq]
  exact h.independent.comp (fun _ => scaleCoordinates σ) (fun _ => measurable_scaleCoordinates σ)

theorem original_centered
    (h : SubexponentialHypotheses μ (coordinateStandardizedObservations X σ) B4 K)
    (hσ : ∀ j, 0 < σ j) (i : Fin n) (j : Fin p) :
    (∫ ω, X i ω j ∂μ) = 0 := by
  have heq : (fun ω => X i ω j) = fun ω =>
      σ j * coordinateStandardizedObservations X σ i ω j := by
    funext ω
    exact (congrFun (coordinateStandardizedObservations_restore X σ hσ i ω) j).symm
  rw [heq, integral_const_mul, h.centered, mul_zero]

/-- Unit variance after genuine coordinate standardization identifies each
positive `σ_j` with the standard deviation of the original normalized sum. -/
theorem original_covariance_diagonal
    (h : SubexponentialHypotheses μ (coordinateStandardizedObservations X σ) B4 K)
    (hσ : ∀ j, 0 < σ j) (j : Fin p) :
    covariance μ (sumVector (sampleNormalizedObservations X)) j j = σ j ^ 2 := by
  rw [coordinateStandardizedObservations_sample_restore X σ hσ,
    covariance_scaleCoordinates, h.unit_diagonal]
  ring

end SubexponentialHypotheses

/-- Corollary 1 for the original observations and their actual Gaussian
target.  The hypotheses on moments and tails concern exactly `X_ij/σ_j`;
the two scales remain separate.  No approximation estimate is a premise. -/
theorem subexponentialCoordinatesRectangleCLT
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
      subexponentialProxyConstant * min 1
        (subexponentialRate n B4 K (covariance μ (sumVector
          (sampleNormalizedObservations (coordinateStandardizedObservations X σ))))) := by
  let Y := coordinateStandardizedObservations X σ
  let A_Y := rowScaledFactor (fun j => (σ j)⁻¹) A
  have hsum := coordinateStandardizedObservations_sample_sum X σ
  have hfactorY : A_Y * A_Y.transpose =
      covariance μ (sumVector (sampleNormalizedObservations Y)) := by
    ext j k
    dsimp only [A_Y, Y]
    rw [rowScaledFactor_covariance, hfactor, hsum, covariance_scaleCoordinates]
  have hb := subexponentialRectangleCLT h A_Y hlocal hfactorY
    (R.preimageCoordinateScale σ hσ)
  have heq := rectangleError_coordinateNormalize μ
    (sumVector (sampleNormalizedObservations X)) A σ hσ R
  rw [← hsum] at heq
  exact heq.le.trans hb

end

end RectangleCLT
