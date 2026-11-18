import RectangleCLTArxivV1.PolyhedralIntrinsicZeroFaces
import RectangleCLTArxivV1.IntrinsicMain

/-! Corollary 3's bounded polyhedral conclusions, using the checked
intrinsic Theorem 1 and both actual projected fourth-moment matrices. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- Both bounded-summand inequalities, with the exact substituted Gaussian
width and an internally chosen factor of the standardized covariance. -/
theorem boundedPolyhedralCLT_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthBudgets μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|)≤J*σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α))=(σ α)^2) :
    let gP := projectedGaussianMean A (standardizedFaceMap ν σ)
    (polyhedralDistance μ (sumVector ξ) A ν ≤ intrinsicUniversalConstant*
      min 1 (intrinsicRelativeRate gP (J*δ) (J^2*s₄) (dimensionLog m))) ∧
    (polyhedralDistance μ (sumVector ξ) A ν ≤ intrinsicUniversalConstant*
      min 1 ((J*δ)*gP*dimensionLog m*Real.sqrt (D_L (J*δ) (dimensionLog m)))) ∧
    gP≤2*Real.sqrt (dimensionLog m) := by
  let M := standardizedFaceMap ν σ
  let η := fun i ω => M.mulVec (ξ i ω)
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  obtain ⟨hη,hrη,hunit⟩ := standardizedProjection_inputs h hr ν σ J hσ hJ0 hν hvariance
  obtain ⟨C,hC⟩ := gaussian_factor_exists_of_boundedIndependent hη
  have hM := standardizedFaceMap_row_l1_le ν σ J hσ hν
  have hcov := covariance_projected_sum h M J hJ0 hM
  have hgram : C*C.transpose=M*(A*A.transpose)*M.transpose := by
    rw [hA]
    exact hC.trans hcov
  have hwidth := gaussianMaximumMean_projected M A C hgram
  have hd := polyhedralDistance_le_standardizedRectangleDistance μ (sumVector ξ) A C ν σ hσ hgram
  have hsum : sumVector η = fun ω => M.mulVec (sumVector ξ ω) :=
    funext (sumVector_mulVec M ξ)
  change polyhedralDistance μ (sumVector ξ) A ν≤rectangleDistance μ (fun ω => M.mulVec (sumVector ξ ω)) C at hd
  rw [←hsum] at hd
  have hf := intrinsicFourthMomentCLT_of_quadratic_bounds μ η hη hm hunit hrη.nonneg
    hrη.same_copy hrη.independent_copy C hC
  have he := intrinsicEnvelopeCLT μ η hη hm hunit C hC
  rw [hwidth] at hf he
  refine ⟨hd.trans hf,hd.trans he,?_⟩
  apply projectedGaussianMean_le_sqrt_dimension hm M A C hgram
  intro α
  rw [hC]
  exact hunit α


/-- Zero-variance directions are handled before standardization; no face
selection or auxiliary comparison estimate is supplied by the user. -/
theorem boundedPolyhedralCLT_all_faces_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthBudgets μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J) (hν : PolyhedralNormalBound A ν J) :
    let k := positivePolyhedralFaceCount A ν
    let gP := polyhedralIntrinsicWidth A ν
    (polyhedralDistance μ (sumVector ξ) A ν ≤ intrinsicUniversalConstant*
      min 1 (intrinsicRelativeRate gP (J*δ) (J^2*s₄) (dimensionLog k))) ∧
    (polyhedralDistance μ (sumVector ξ) A ν ≤ intrinsicUniversalConstant*
      min 1 ((J*δ)*gP*dimensionLog k*Real.sqrt (D_L (J*δ) (dimensionLog k)))) ∧
    gP≤2*Real.sqrt (dimensionLog k) := by
  have hL2 : ∀ j, MemLp (fun ω => sumVector ξ ω j) 2 μ := by
    apply memLp_sumVector_coordinate
    intro i j
    apply MemLp.of_bound (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable) δ
    simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j
  have hc : ∀ j, (∫ ω, sumVector ξ ω j ∂μ)=0 := by
    apply integral_sumVector_coordinate_zero _ h.centered
    intro i j
    simpa only [pow_one] using
      integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
  by_cases hk : positivePolyhedralFaceCount A ν=0
  · have hd := polyhedralDistance_zero_of_no_positive_faces μ (sumVector ξ) A hL2 hc hA ν hk
    have hg := polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk
    simp only [hd,hg,intrinsicRelativeRate,zero_mul,mul_zero,min_eq_right (zero_le_one),le_refl,true_and]
    exact mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg _)
  · have hpos : 1 ≤ positivePolyhedralFaceCount A ν := by omega
    have hd := polyhedralDistance_eq_positive_faces μ (sumVector ξ) A hL2 hc hA ν
    rw [hd]
    exact boundedPolyhedralCLT_intrinsic μ hpos ξ h hr A hA
      (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) J
      (positivePolyhedralFaceScale_pos A ν) hJ hν.positive_faces
      (positivePolyhedralFace_variance_identity μ (sumVector ξ) A hA ν)


/-- The envelope conclusion requires boundedness alone. The proof supplies
both genuine fourth budgets from that envelope before invoking Theorem 1. -/
theorem boundedPolyhedralEnvelopeCLT_all_faces_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J) (hν : PolyhedralNormalBound A ν J) :
    polyhedralDistance μ (sumVector ξ) A ν ≤ intrinsicUniversalConstant*
      min 1 ((J*δ)*polyhedralIntrinsicWidth A ν*dimensionLog (positivePolyhedralFaceCount A ν)*
        Real.sqrt (D_L (J*δ) (dimensionLog (positivePolyhedralFaceCount A ν)))) := by
  have hmom := relativeMomentBounds_of_envelope h
  have hr : RelativeFourthBudgets μ ξ (δ^2) :=
    ⟨sq_nonneg δ,hmom.fourth_upper,hmom.fresh_fourth_upper⟩
  exact (boundedPolyhedralCLT_all_faces_intrinsic μ ξ h hr A hA ν J hJ hν).2.1

end
end RectangleCLTArxivV1
