import RectangleCLTCompanion.SplitV4.RelativeUniform
import RectangleCLTCompanion.SplitV4.ZeroVarianceFaces
import RectangleCLTCompanion.SplitV4.RelativeMain

/-! The exact relative fourth-moment model under standardized face maps.
Both actual fourth matrices transfer with J², including independent-copy
moments. The terminal relative probability bound is assembled separately
from the proved relative CLT. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem relativeIndependent_standardizedFaces
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthAdmissible μ ξ s₄)
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 0 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J*σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = (σ α)^2) :
    RelativeIndependentHypotheses μ
      (fun i ω => (standardizedFaceMap ν σ).mulVec (ξ i ω)) (J*δ) (J^2*s₄) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  refine
    { toBoundedIndependentHypotheses := boundedIndependent_projected h M J hJ hM
      toRelativeFourthAdmissible := relativeFourthAdmissible_projected h hr M J hJ hM
      unit_variance := ?_ }
  intro α
  rw [covariance_projected_sum h M J hJ hM]
  exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α

theorem bounded_sum_coordinate_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    MemLp (fun ω => sumVector ξ ω j) 2 μ := by
  apply memLp_sumVector_coordinate
  intro i j
  apply MemLp.of_bound (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable) δ
  simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j

theorem bounded_sum_coordinate_centered
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    (∫ ω, sumVector ξ ω j ∂μ) = 0 := by
  apply integral_sumVector_coordinate_zero _ h.centered j
  intro i k
  simpa only [pow_one] using
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i k 1

/-- The relative branch of Corollary 3. Both fourth budgets and the
envelope undergo the exact substitutions J²s4 and Jδ. The logarithm D_L
is evaluated at those substituted parameters and the number of faces. -/
theorem relativePolyhedralCLT
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthAdmissible μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hν : ∀ α, (∑ j, |ν α j|) ≤ J*σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = (σ α)^2) :
    polyhedralDistance μ (sumVector ξ) A ν ≤
      relativeUniversalConstant*min 1 (relativeRate (J*δ) (J^2*s₄) (dimensionLog m)) := by
  let α : Fin m := ⟨0,by omega⟩
  have hJ : 0 ≤ J := by
    by_contra hneg
    have hp : J*σ α < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (hσ α)
    have hs : 0 ≤ ∑ j, |ν α j| := Finset.sum_nonneg (fun j _ => abs_nonneg (ν α j))
    exact (not_lt_of_ge (hs.trans (hν α))) hp
  let M := standardizedFaceMap ν σ
  let η : Fin n → Ω → Vector m := fun i ω => M.mulVec (ξ i ω)
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  have hη : RelativeIndependentHypotheses μ η (J*δ) (J^2*s₄) :=
    relativeIndependent_standardizedFaces h hr ν σ J hσ hJ hν hvariance
  obtain ⟨C,hC⟩ := gaussian_factor_exists_of_boundedIndependent hη.toBoundedIndependentHypotheses
  have hcov : covariance μ (sumVector η) = M*covariance μ (sumVector ξ)*M.transpose :=
    covariance_projected_sum h M J hJ hM
  have hgram : C*C.transpose = M*(A*A.transpose)*M.transpose := by
    rw [hA]
    exact hC.trans hcov
  have hsum : sumVector η = fun ω => M.mulVec (sumVector ξ ω) := funext (sumVector_mulVec M ξ)
  have hd := polyhedralDistance_le_projected_rectangleDistance μ (sumVector ξ) A C ν σ hσ hgram
  rw [← hsum] at hd
  exact hd.trans (relativeMomentCLT μ hm η hη C hC)

theorem relativePolyhedralCLT_delete_zero_variance_faces
    {Ω : Type*} [MeasurableSpace Ω] {p m r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hr : 1 ≤ r)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeFourthAdmissible μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = 0)
    (σ : Vector r) (J : ℝ) (hσ : ∀ β, 0 < σ β)
    (hν : ∀ β, (∑ j, |ν (keep β) j|) ≤ J*σ β)
    (hvariance : ∀ β, dotProduct (ν (keep β))
      ((covariance μ (sumVector ξ)).mulVec (ν (keep β))) = (σ β)^2) :
    polyhedralDistance μ (sumVector ξ) A ν ≤
      relativeUniversalConstant*min 1 (relativeRate (J*δ) (J^2*s₄) (dimensionLog r)) := by
  apply (polyhedralDistance_le_delete_zero_variance_faces (sumVector ξ) A
    (bounded_sum_coordinate_memLp_two h) (bounded_sum_coordinate_centered h) hA ν keep hzero).trans
  exact relativePolyhedralCLT μ hr ξ h hrel A hA (retainedFaceNormals ν keep) σ J hσ hν hvariance

theorem relativePolyhedralDistance_zero_of_all_face_variances_zero
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ)
    (hzero : ∀ α, dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = 0) :
    polyhedralDistance μ (sumVector ξ) A ν = 0 :=
  polyhedralDistance_zero_of_all_face_variances_zero (sumVector ξ) A
    (bounded_sum_coordinate_memLp_two h) (bounded_sum_coordinate_centered h) hA ν hzero

end
end RectangleCLT.Companion.SplitV4
