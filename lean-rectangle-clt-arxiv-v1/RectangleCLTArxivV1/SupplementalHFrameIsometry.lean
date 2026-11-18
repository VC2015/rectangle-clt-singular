import RectangleCLTArxivV1.SupplementalHFrameSections

/-! The actual linear isometry of an orthonormal frame, and its true
normal coordinates. These connect frame conditional laws to cone transport. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual synthesis isometry of a finite orthonormal frame. -/
def orthonormalFrameIsometry {q : ℕ} (v : Fin q → E) (hv : Orthonormal ℝ v) :
    EuclideanSpace ℝ (Fin q) →ₗᵢ[ℝ] E where
  toFun x := ∑ i, x i • v i
  map_add' x y := by
    simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖∑ i, x i • v i‖^2=‖x‖^2
    rw [gaussianFrame_normalPoint_normSq v hv,PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]

theorem orthonormalFrameIsometry_apply {q : ℕ} (v : Fin q → E) (hv : Orthonormal ℝ v)
    (x : EuclideanSpace ℝ (Fin q)) : orthonormalFrameIsometry v hv x=∑ i, x i • v i := rfl

theorem orthonormalFrameIsometry_single {q : ℕ} (v : Fin q → E) (hv : Orthonormal ℝ v) (i : Fin q) :
    orthonormalFrameIsometry v hv (EuclideanSpace.single i 1)=v i := by
  classical
  simp [orthonormalFrameIsometry,EuclideanSpace.single_apply]

/-- The actual analysis coordinates of a point in a finite frame. -/
def orthonormalFrameCoordinates {q : ℕ} (v : Fin q → E) (x : E) : EuclideanSpace ℝ (Fin q) :=
  (WithLp.equiv 2 (Fin q → ℝ)).symm (fun i => ⟪v i,x⟫_ℝ)

theorem orthonormalFrameCoordinates_apply {q : ℕ} (v : Fin q → E) (x : E) (i : Fin q) :
    orthonormalFrameCoordinates v x i=⟪v i,x⟫_ℝ := rfl

theorem orthonormalFrameCoordinates_isometry_apply {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (x : EuclideanSpace ℝ (Fin q)) :
    orthonormalFrameCoordinates v (orthonormalFrameIsometry v hv x)=x := by
  apply PiLp.ext
  intro i
  change ⟪v i,∑ j, x j • v j⟫_ℝ=x i
  exact hv.inner_right_fintype (fun j => x j) i

section Finite
variable [FiniteDimensional ℝ E]

theorem orthonormalFrameIsometry_coordinates {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (x : E) :
    orthonormalFrameIsometry v hv (orthonormalFrameCoordinates v x)=
      (Submodule.span ℝ (Set.range v)).orthogonalProjection x := by
  change gaussianFrameProjection v x=_
  exact gaussianFrameProjection_eq_orthogonalProjection v hv x

theorem orthonormalFrameIsometry_coordinates_of_mem {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (x : E)
    (hx : x∈Submodule.span ℝ (Set.range v)) :
    orthonormalFrameIsometry v hv (orthonormalFrameCoordinates v x)=x := by
  rw [orthonormalFrameIsometry_coordinates v hv]
  exact Submodule.orthogonalProjection_eq_self_iff.mpr hx

omit [FiniteDimensional ℝ E] in
theorem orthonormalFrameIsometry_range {q : ℕ} (v : Fin q → E) (hv : Orthonormal ℝ v) :
    LinearMap.range (orthonormalFrameIsometry v hv).toLinearMap=Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change (∑ i, x i • v i)∈Submodule.span ℝ (Set.range v)
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨EuclideanSpace.single i 1,orthonormalFrameIsometry_single v hv i⟩

end Finite
end
end RectangleCLTArxivV1
