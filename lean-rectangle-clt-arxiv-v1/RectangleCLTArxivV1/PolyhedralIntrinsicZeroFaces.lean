import RectangleCLTArxivV1.PolyhedralIntrinsicInputs

/-! Canonical removal of the actual zero-variance projections, before
standardization. Empty retained families have zero discrepancy and width. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def polyhedralFaceVariance {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (α : Fin m) : ℝ :=
  dotProduct (ν α) ((A*A.transpose).mulVec (ν α))

theorem polyhedralFaceVariance_nonneg {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (α : Fin m) : 0 ≤ polyhedralFaceVariance A ν α := by
  unfold polyhedralFaceVariance
  rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose]
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)

def positivePolyhedralFaceCount {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : ℕ := by
  classical
  exact Fintype.card {α : Fin m // 0 < polyhedralFaceVariance A ν α}

def positivePolyhedralFaceIndex {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : Fin (positivePolyhedralFaceCount A ν) → Fin m := by
  classical
  exact fun i => ((Fintype.equivFin {α : Fin m // 0 < polyhedralFaceVariance A ν α}).symm i).val

theorem positivePolyhedralFaceIndex_injective {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : Function.Injective (positivePolyhedralFaceIndex A ν) := by
  classical
  exact Subtype.val_injective.comp (Fintype.equivFin _).symm.injective

theorem positivePolyhedralFaceIndex_range {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) :
    Set.range (positivePolyhedralFaceIndex A ν) = {α | 0 < polyhedralFaceVariance A ν α} := by
  classical
  ext α
  constructor
  · rintro ⟨i,rfl⟩
    exact ((Fintype.equivFin {α : Fin m // 0 < polyhedralFaceVariance A ν α}).symm i).property
  · intro hα
    refine ⟨Fintype.equivFin _ ⟨α,hα⟩,?_⟩
    simp [positivePolyhedralFaceIndex]

theorem positivePolyhedralFaceIndex_variance_pos {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (i : Fin (positivePolyhedralFaceCount A ν)) :
    0 < polyhedralFaceVariance A ν (positivePolyhedralFaceIndex A ν i) := by
  have hi : positivePolyhedralFaceIndex A ν i ∈ Set.range (positivePolyhedralFaceIndex A ν) := ⟨i,rfl⟩
  rwa [positivePolyhedralFaceIndex_range] at hi

theorem omittedPolyhedralFace_variance_zero {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (α : Fin m)
    (hα : α ∉ Set.range (positivePolyhedralFaceIndex A ν)) : polyhedralFaceVariance A ν α=0 := by
  rw [positivePolyhedralFaceIndex_range] at hα
  exact le_antisymm (le_of_not_gt hα) (polyhedralFaceVariance_nonneg A ν α)

def positivePolyhedralFaceNormals {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin (positivePolyhedralFaceCount A ν)) (Fin p) ℝ :=
  retainedFaceNormals ν (positivePolyhedralFaceIndex A ν)

def positivePolyhedralFaceScale {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : Vector (positivePolyhedralFaceCount A ν) :=
  fun i => Real.sqrt (polyhedralFaceVariance A ν (positivePolyhedralFaceIndex A ν i))

def positivePolyhedralFaceMap {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) :=
  standardizedFaceMap (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν)

def polyhedralIntrinsicWidth {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : ℝ := projectedGaussianMean A (positivePolyhedralFaceMap A ν)

theorem positivePolyhedralFaceScale_pos {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (i : Fin (positivePolyhedralFaceCount A ν)) :
    0 < positivePolyhedralFaceScale A ν i :=
  Real.sqrt_pos.mpr (positivePolyhedralFaceIndex_variance_pos A ν i)

theorem positivePolyhedralFaceScale_sq {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (i : Fin (positivePolyhedralFaceCount A ν)) :
    polyhedralFaceVariance A ν (positivePolyhedralFaceIndex A ν i)=(positivePolyhedralFaceScale A ν i)^2 :=
  (Real.sq_sqrt (polyhedralFaceVariance_nonneg A ν _)).symm

/-- This is equality of the original threshold suprema, with no assumed
comparison estimate. Negative omitted thresholds give zero under both laws. -/
theorem polyhedralDistance_eq_positive_faces
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ) (hc : ∀ j, (∫ ω, W ω j ∂μ)=0)
    (hA : A*A.transpose=covariance μ W) (ν : Matrix (Fin m) (Fin p) ℝ) :
    polyhedralDistance μ W A ν=polyhedralDistance μ W A (positivePolyhedralFaceNormals A ν) := by
  apply polyhedralDistance_delete_zero_variance_faces W A hL2 hc hA ν
    (positivePolyhedralFaceIndex A ν) (positivePolyhedralFaceIndex_injective A ν)
  intro α hα
  rw [←hA]
  exact omittedPolyhedralFace_variance_zero A ν α hα

theorem polyhedralIntrinsicWidth_zero_of_no_positive_faces {p m : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : Matrix (Fin m) (Fin p) ℝ)
    (hzero : positivePolyhedralFaceCount A ν=0) : polyhedralIntrinsicWidth A ν=0 := by
  have he (x : Vector p) : ‖(positivePolyhedralFaceMap A ν).mulVec x‖=0 := by
    apply norm_eq_zero.mpr
    funext i
    have hi := i.isLt
    omega
  simp only [polyhedralIntrinsicWidth,projectedGaussianMean,he,integral_zero]

theorem polyhedralDistance_zero_of_no_positive_faces
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ) (hc : ∀ j, (∫ ω, W ω j ∂μ)=0)
    (hA : A*A.transpose=covariance μ W) (ν : Matrix (Fin m) (Fin p) ℝ)
    (hzero : positivePolyhedralFaceCount A ν=0) : polyhedralDistance μ W A ν=0 := by
  apply polyhedralDistance_zero_of_all_face_variances_zero W A hL2 hc hA ν
  intro α
  rw [←hA]
  apply omittedPolyhedralFace_variance_zero A ν α
  rintro ⟨i,_⟩
  have hi := i.isLt
  omega


/-- The amplification condition is imposed only on positive-variance faces. -/
def PolyhedralNormalBound {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) : Prop :=
  ∀ α, 0 < polyhedralFaceVariance A ν α →
    (∑ j, |ν α j|)≤J*Real.sqrt (polyhedralFaceVariance A ν α)

theorem PolyhedralNormalBound.positive_faces {p m : ℕ}
    {A : Matrix (Fin p) (Fin p) ℝ} {ν : Matrix (Fin m) (Fin p) ℝ} {J : ℝ}
    (h : PolyhedralNormalBound A ν J) (i : Fin (positivePolyhedralFaceCount A ν)) :
    (∑ j, |positivePolyhedralFaceNormals A ν i j|)≤J*positivePolyhedralFaceScale A ν i :=
  h _ (positivePolyhedralFaceIndex_variance_pos A ν i)

theorem positivePolyhedralFace_variance_identity
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ} (μ : Measure Ω) (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (i : Fin (positivePolyhedralFaceCount A ν)) :
    dotProduct (positivePolyhedralFaceNormals A ν i)
      ((covariance μ W).mulVec (positivePolyhedralFaceNormals A ν i))=(positivePolyhedralFaceScale A ν i)^2 := by
  rw [←hA]
  exact positivePolyhedralFaceScale_sq A ν i


theorem positivePolyhedralFaceCount_le {p m : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : positivePolyhedralFaceCount A ν≤m := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (positivePolyhedralFaceIndex_injective A ν)

/-- A square factor of the projected Gaussian covariance is constructed
from its actual positive semidefinite Gram matrix, even when singular. -/
theorem projectedGaussian_factor_exists {p m : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (M : Matrix (Fin m) (Fin p) ℝ) :
    ∃ C : Matrix (Fin m) (Fin m) ℝ, C*C.transpose=M*(A*A.transpose)*M.transpose := by
  have hQ : (M*(A*A.transpose)*M.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul,Matrix.mul_assoc]
      using Matrix.posSemidef_self_mul_conjTranspose (M*A)
  refine ⟨hQ.sqrt,?_⟩
  have hs : hQ.sqrt.transpose=hQ.sqrt := by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
      using hQ.posSemidef_sqrt.isHermitian
  rw [hs]
  exact hQ.sqrt_mul_self

/-- The actual canonical Gaussian width has the printed dimension bound,
without requiring any array, moment, rank or angle hypothesis. -/
theorem polyhedralIntrinsicWidth_le {p m : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : Matrix (Fin m) (Fin p) ℝ) :
    polyhedralIntrinsicWidth A ν≤2*Real.sqrt (dimensionLog (positivePolyhedralFaceCount A ν)) := by
  by_cases hk : positivePolyhedralFaceCount A ν=0
  · rw [polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · have hpos : 1 ≤ positivePolyhedralFaceCount A ν := by omega
    obtain ⟨C,hC⟩ := projectedGaussian_factor_exists A (positivePolyhedralFaceMap A ν)
    apply projectedGaussianMean_le_sqrt_dimension hpos (positivePolyhedralFaceMap A ν) A C hC
    intro i
    rw [hC]
    exact standardizedFaceMap_covariance_unit_diagonal
      (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) (A*A.transpose)
      (positivePolyhedralFaceScale_pos A ν) (positivePolyhedralFaceScale_sq A ν) i

end
end RectangleCLTArxivV1
