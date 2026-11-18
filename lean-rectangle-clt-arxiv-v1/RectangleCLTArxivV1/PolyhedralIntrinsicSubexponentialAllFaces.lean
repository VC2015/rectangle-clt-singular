import RectangleCLTArxivV1.PolyhedralIntrinsicSubexponential
import RectangleCLTArxivV1.PolyhedralIntrinsicZeroFaces

/-! The sub-exponential polyhedral bound after deleting actual zero-variance
faces. The empty surviving family has zero distance and zero Gaussian width. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

 theorem orliczPolyhedralCLT_intrinsic_all_faces
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (K : ℝ)
    (h : Psi1IndependentHypotheses μ X K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J)
    (hν : PolyhedralNormalBound A ν J) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      subexponentialWidthConstant * min 1
        (subexponentialWidthRate n (positivePolyhedralFaceCount A ν) (J*K)
          (polyhedralIntrinsicWidth A ν)) := by
  have hExp := psi1_exponentialHypotheses_exact h
  have hL2 := normalizedObservationSum_coordinate_memLp_two hExp
  have hc := normalizedObservationSum_coordinate_centered hExp
  by_cases hk : positivePolyhedralFaceCount A ν=0
  · rw [polyhedralDistance_zero_of_no_positive_faces μ _ A hL2 hc hA ν hk,
      polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk]
    simp [subexponentialWidthRate]
  · rw [polyhedralDistance_eq_positive_faces μ _ A hL2 hc hA ν]
    have hm : 1 ≤ positivePolyhedralFaceCount A ν := by omega
    exact orliczPolyhedralCLT_intrinsic μ hm hn X K h A hA
      (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) J
      (positivePolyhedralFaceScale_pos A ν) hJ hν.positive_faces
      (positivePolyhedralFace_variance_identity μ _ A hA ν)

end
end RectangleCLTArxivV1
