import RectangleCLTArxivV1.SeededIntrinsicConcentration
import RectangleCLTArxivV1.SmoothingIntrinsic

/-! Lemma 2 with the endpoint concentration supplied from the actual array. -/
namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4

set_option autoImplicit false

theorem lemma_2_smoothing_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {ξ : Fin n → Ω → Vector p} {δ h : ℝ}
    (hb : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hh : 0 < h) (hδh : δ ≤ h) :
    rectangleDistance μ (sumVector ξ) A ≤ smoothingDiscrepancy μ (sumVector ξ) A h hh +
      (9 * intrinsicBoundaryConstant) * h * intrinsicBoundaryCoefficient μ ξ A * dimensionLog p := by
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA, hunit j]
  have hk : 0 ≤ intrinsicBoundaryCoefficient μ ξ A :=
    zero_le_one.trans (one_le_intrinsicBoundaryCoefficient μ ξ A hp)
  have hW : Measurable (sumVector ξ) := by
    unfold sumVector
    exact Finset.measurable_sum _ (fun i _ => hb.measurable i)
  simpa only [mul_assoc] using
    rectangleDistance_le_smoothingDiscrepancy_intrinsic hp μ (sumVector ξ)
      hW A intrinsicBoundaryConstant_pos.le
      hb.delta_nonneg hk hh hδh
      (intrinsicRectangleConcentration_bounded_endpoint hb hp hunit A)
      (intrinsicRectangleConcentration_gaussian_endpoint μ ξ hp A hdiag)

end RectangleCLTArxivV1
