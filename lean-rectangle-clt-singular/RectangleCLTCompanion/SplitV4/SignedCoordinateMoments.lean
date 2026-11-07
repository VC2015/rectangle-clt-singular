import RectangleCLTCompanion.SplitV4.SignedCoordinateSmoother
import RectangleCLT.BoundedIndependentScaling

/-! Exact covariance and variance identities for the actual signed
coordinate face family. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem signedCoordinateRows_quadratic {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (α : Fin (2*p)) :
    dotProduct (signedCoordinateRows p α) (S.mulVec (signedCoordinateRows p α)) =
      S (signedCoordinateFaceEquiv p α).1 (signedCoordinateFaceEquiv p α).1 := by
  cases hb : (signedCoordinateFaceEquiv p α).2 <;>
    simp [signedCoordinateRows, hb, Matrix.mulVec, dotProduct, FaceSmoother.coordinateDirection]

theorem signedCoordinateRows_variance_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (α : Fin (2*p)) :
    variance (fun ω => dotProduct (signedCoordinateRows p α) (sumVector ξ ω)) μ =
      covariance μ (sumVector ξ) (signedCoordinateFaceEquiv p α).1 (signedCoordinateFaceEquiv p α).1 := by
  change variance (fun ω => faceDot (signedCoordinateRows p α) (sumVector ξ ω)) μ = _
  simp_rw [signedCoordinateRows_projection]
  cases hb : (signedCoordinateFaceEquiv p α).2
  · simp only [FaceSmoother.normalDot, hb, Bool.false_eq_true, if_false]
    have he := variance_mul (-1) (fun ω => sumVector ξ ω (signedCoordinateFaceEquiv p α).1) μ
    norm_num only [neg_one_mul, neg_one_sq, one_mul] at he
    rw [he]
    exact (projected_covariance_diagonal_eq_variance μ ξ h _).symm
  · simp only [FaceSmoother.normalDot, hb, if_true]
    exact (projected_covariance_diagonal_eq_variance μ ξ h _).symm

theorem indepFun_constant_right
    {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (c : F) :
    IndepFun X (fun _ : Ω => c) μ := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t _ _
  by_cases hc : c ∈ t <;> simp [hc]

end
end RectangleCLT.Companion.SplitV4
