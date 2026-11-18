import RectangleCLTArxivV1.SupplementalHSphericalBalance

/-! The archived normal-section chart is an actual Euclidean linear
isometry onto its supporting plane, with an explicit inverse there. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

theorem normalSectionChart_zero_add {n : ℕ} (j : Fin (n+1)) (u : Vector (n+1)) (a b : Vector n) :
    normalSectionChart j u 0 (a+b)=normalSectionChart j u 0 a+normalSectionChart j u 0 b := by
  unfold normalSectionChart
  rw [←gaussianRotation_add]
  congr 1
  ext k
  by_cases hk : k=j
  · subst k
    simp
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
    simp

/-- The actual orthogonal tangent chart in Euclidean norms. -/
def euclideanNormalSectionIsometry {n : ℕ} (j : Fin (n+1)) (u : Vector (n+1)) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun y := (WithLp.equiv 2 (Vector (n+1))).symm
    (normalSectionChart j u 0 (WithLp.equiv 2 (Vector n) y))
  map_add' a b := by
    change (WithLp.equiv 2 (Vector (n+1))).symm
      (normalSectionChart j u 0 (WithLp.equiv 2 (Vector n) a+WithLp.equiv 2 (Vector n) b))=_
    rw [normalSectionChart_zero_add]
    rfl
  map_smul' a b := by
    change (WithLp.equiv 2 (Vector (n+1))).symm
      (normalSectionChart j u 0 (a • WithLp.equiv 2 (Vector n) b))=_
    rw [supplementalH_normalSectionChart_smul]
    rfl
  norm_map' y := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.equiv 2 (Vector (n+1))).symm
      (normalSectionChart j u 0 (WithLp.equiv 2 (Vector n) y))‖^2=‖y‖^2
    rw [←vectorNormSq_eq_euclidean_norm_sq,vectorNormSq_normalSectionChart]
    simp only [zero_pow (by decide : (2:ℕ)≠0),zero_add]
    exact supplementalH_vectorNormSq_equiv y

/-- Explicit tangent coordinates of a point, obtained from the actual
inverse orthogonal rotation and deletion of its normal coordinate. -/
def normalSectionCoordinates {n : ℕ} (j : Fin (n+1)) (u x : Vector (n+1)) : Vector n :=
  j.removeNth ((gaussianRotation (coordinateNormalRotation j u)).symm x)

theorem normalSectionChart_coordinates {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1)
    (x : Vector (n+1)) (hx : faceDot u x=0) :
    normalSectionChart j u 0 (normalSectionCoordinates j u x)=x := by
  let e := gaussianRotation (coordinateNormalRotation j u)
  have hj : e.symm x j=0 := by
    have h := gaussianRotation_faceDot (coordinateNormalRotation j u) (Pi.single j 1) (e.symm x)
    rw [coordinateNormalRotation_unit j u hu] at h
    change faceDot u (e (e.symm x))=faceDot (Pi.single j 1) (e.symm x) at h
    rw [e.apply_symm_apply,hx] at h
    simpa [faceDot,Pi.single_apply,ite_mul] using h.symm
  unfold normalSectionChart normalSectionCoordinates
  change e (j.insertNth 0 (j.removeNth (e.symm x)))=x
  rw [←hj,Fin.insertNth_self_removeNth,e.apply_symm_apply]

theorem euclideanNormalSectionIsometry_surjective_on_plane {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1)
    (x : EuclideanSpace ℝ (Fin (n+1))) (hx : faceDot u (WithLp.equiv 2 (Vector (n+1)) x)=0) :
    ∃ y : EuclideanSpace ℝ (Fin n), euclideanNormalSectionIsometry j u y=x := by
  refine ⟨(WithLp.equiv 2 (Vector n)).symm (normalSectionCoordinates j u (WithLp.equiv 2 (Vector (n+1)) x)),?_⟩
  change (WithLp.equiv 2 (Vector (n+1))).symm
    (normalSectionChart j u 0 (normalSectionCoordinates j u (WithLp.equiv 2 (Vector (n+1)) x)))=x
  rw [normalSectionChart_coordinates j u hu _ hx]
  exact Equiv.symm_apply_apply _ _

end
end RectangleCLTArxivV1
