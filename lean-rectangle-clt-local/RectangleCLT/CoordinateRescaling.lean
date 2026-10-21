import RectangleCLT.Statement
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring

/-! Exact positive coordinate rescaling for arbitrary measurable rectangles,
the concrete Gaussian factors, and their rectangle discrepancies. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def scaleCoordinates {p : ℕ} (d x : Vector p) : Vector p := fun j => d j * x j

theorem measurable_scaleCoordinates {p : ℕ} (d : Vector p) :
    Measurable (scaleCoordinates d) := by
  exact measurable_pi_lambda _ (fun j => measurable_const.mul (measurable_pi_apply j))

theorem sumVector_scaleCoordinates {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (d : Vector p) (ω : Ω) :
    sumVector (fun i ω => scaleCoordinates d (ξ i ω)) ω =
      scaleCoordinates d (sumVector ξ ω) := by
  funext j
  simp only [sumVector, scaleCoordinates, Finset.sum_apply, Finset.mul_sum]

theorem covariance_scaleCoordinates {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {p : ℕ} (W : Ω → Vector p) (d : Vector p) (j k : Fin p) :
    covariance μ (fun ω => scaleCoordinates d (W ω)) j k =
      d j * covariance μ W j k * d k := by
  unfold covariance
  simp only [scaleCoordinates]
  have hprod : (fun ω => (d j * W ω j) * (d k * W ω k)) =
      (fun ω => (d j * d k) * (W ω j * W ω k)) := by
    funext ω
    ring
  rw [hprod, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- Row scaling is the factor of the correspondingly rescaled Gaussian. -/
def rowScaledFactor {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => d j * A j k

theorem rowScaledFactor_mulVec {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (z : Vector p) :
    (rowScaledFactor d A).mulVec z = scaleCoordinates d (A.mulVec z) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, rowScaledFactor, scaleCoordinates, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rowScaledFactor_covariance {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    ((rowScaledFactor d A) * (rowScaledFactor d A).transpose) j k =
      d j * (A * A.transpose) j k * d k := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowScaledFactor,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem gaussianLaw_rowScaledFactor {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    gaussianLaw (rowScaledFactor d A) = (gaussianLaw A).map (scaleCoordinates d) := by
  unfold gaussianLaw
  rw [Measure.map_map (measurable_scaleCoordinates d) (measurable_mulVec A)]
  congr 1
  funext z
  exact rowScaledFactor_mulVec d A z

def Rect.preimageCoordinateScale {p : ℕ} (R : Rect p) (d : Vector p)
    (hd : ∀ j, 0 < d j) : Rect p where
  interval j := (fun x : ℝ => d j * x) ⁻¹' R.interval j
  ordConnected j := (R.ordConnected j).preimage_mono
    (fun _ _ hxy => mul_le_mul_of_nonneg_left hxy (hd j).le)
  measurable j := (R.measurable j).preimage (measurable_const.mul measurable_id)

theorem Rect.preimageCoordinateScale_carrier {p : ℕ} (R : Rect p) (d : Vector p)
    (hd : ∀ j, 0 < d j) :
    (R.preimageCoordinateScale d hd).carrier = (scaleCoordinates d) ⁻¹' R.carrier := by
  ext x
  rfl

/-- Rectangle discrepancy is exactly preserved when the model, Gaussian
factor and rectangle are transformed by the same positive diagonal map. -/
theorem rectangleError_coordinateScale
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (d : Vector p) (hd : ∀ j, 0 < d j) (R : Rect p) :
    rectangleError μ (fun ω => scaleCoordinates d (W ω)) (rowScaledFactor d A) R =
      rectangleError μ W A (R.preimageCoordinateScale d hd) := by
  unfold rectangleError
  rw [gaussianLaw_rowScaledFactor, map_measureReal_apply (measurable_scaleCoordinates d)
    R.measurableSet_carrier, Rect.preimageCoordinateScale_carrier]
  rfl

theorem scaleCoordinates_inverse_cancel {p : ℕ} (σ x : Vector p)
    (hσ : ∀ j, 0 < σ j) :
    scaleCoordinates σ (scaleCoordinates (fun j => (σ j)⁻¹) x) = x := by
  funext j
  simp [scaleCoordinates, ← mul_assoc, ne_of_gt (hσ j)]

theorem rowScaledFactor_inverse_cancel {p : ℕ} (σ : Vector p)
    (hσ : ∀ j, 0 < σ j) (A : Matrix (Fin p) (Fin p) ℝ) :
    rowScaledFactor σ (rowScaledFactor (fun j => (σ j)⁻¹) A) = A := by
  ext j k
  simp [rowScaledFactor, ← mul_assoc, ne_of_gt (hσ j)]

/-- Transfer the original rectangle discrepancy to the standardized vector
without restricting the endpoint conventions or the coordinate scales. -/
theorem rectangleError_coordinateNormalize
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (σ : Vector p) (hσ : ∀ j, 0 < σ j) (R : Rect p) :
    rectangleError μ W A R =
      rectangleError μ (fun ω => scaleCoordinates (fun j => (σ j)⁻¹) (W ω))
        (rowScaledFactor (fun j => (σ j)⁻¹) A)
        (R.preimageCoordinateScale σ hσ) := by
  have hh := rectangleError_coordinateScale μ
    (fun ω => scaleCoordinates (fun j => (σ j)⁻¹) (W ω))
    (rowScaledFactor (fun j => (σ j)⁻¹) A) σ hσ R
  simp only [scaleCoordinates_inverse_cancel σ _ hσ, rowScaledFactor_inverse_cancel σ hσ] at hh
  exact hh

end

end RectangleCLT
