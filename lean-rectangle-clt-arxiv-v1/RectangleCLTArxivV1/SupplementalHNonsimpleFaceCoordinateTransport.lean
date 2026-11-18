import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinateSpherical
import RectangleCLTArxivV1.SupplementalHTripleTransportGeometry
import RectangleCLTArxivV1.SupplementalHFrameIsometry

/-! Exact coordinate/ambient normal-cone and signed-vector transport.
The actual complete active cone is identified by coefficient reindexing. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}

def nonsimpleFaceCoordinateLift (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) : E3 →ₗᵢ[ℝ] E :=
  (nonsimpleFaceNormalSpace u H.1).subtypeₗᵢ.comp (nonsimpleFaceBasis u b H).repr.symm.toLinearIsometry

theorem nonsimpleFaceCoordinateLift_apply (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E3) :
    nonsimpleFaceCoordinateLift u b H x=((nonsimpleFaceBasis u b H).repr.symm x : E) := rfl

theorem nonsimpleFaceCoordinateLift_map_of_mem (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E) (hx : x∈nonsimpleFaceNormalSpace u H.1) :
    nonsimpleFaceCoordinateLift u b H (nonsimpleFaceCoordinateMap u b H x)=x := by
  rw [nonsimpleFaceCoordinateLift_apply,nonsimpleFaceCoordinateMap_of_mem u b H x hx]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem nonsimpleFaceCoordinateMap_lift (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E3) :
    nonsimpleFaceCoordinateMap u b H (nonsimpleFaceCoordinateLift u b H x)=x := by
  rw [nonsimpleFaceCoordinateLift_apply,nonsimpleFaceCoordinateMap_of_mem u b H _
    ((nonsimpleFaceBasis u b H).repr.symm x).property]
  change (nonsimpleFaceBasis u b H).repr ((nonsimpleFaceBasis u b H).repr.symm x)=x
  exact (nonsimpleFaceBasis u b H).repr.apply_symm_apply x

theorem nonsimpleFaceCoordinateLift_range (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) :
    LinearMap.range (nonsimpleFaceCoordinateLift u b H).toLinearMap=nonsimpleFaceNormalSpace u H.1 := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    exact ((nonsimpleFaceBasis u b H).repr.symm y).property
  · intro x hx
    exact ⟨nonsimpleFaceCoordinateMap u b H x,nonsimpleFaceCoordinateLift_map_of_mem u b H x hx⟩

theorem nonsimpleFaceCoordinateLift_eq_frameIsometry (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) :
    nonsimpleFaceCoordinateLift u b H=orthonormalFrameIsometry (nonsimpleFaceFrame u b H)
      (nonsimpleFaceFrame_orthonormal u b H) := by
  ext x
  rw [nonsimpleFaceCoordinateLift_apply,orthonormalFrameIsometry_apply]
  simpa only [Submodule.coe_sum,Submodule.coe_smul,nonsimpleFaceFrame] using
    congrArg (fun y : nonsimpleFaceNormalSpace u H.1 => (y : E))
      ((nonsimpleFaceBasis u b H).sum_repr_symm x).symm

def nonsimpleFaceCoordinatePoint (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) : E3 :=
  nonsimpleFaceCoordinateMap u b H (nonsimpleFaceNormalPoint u b H)

theorem nonsimpleFaceCoordinateLift_point (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) :
    nonsimpleFaceCoordinateLift u b H (nonsimpleFaceCoordinatePoint u b H)=nonsimpleFaceNormalPoint u b H :=
  nonsimpleFaceCoordinateLift_map_of_mem u b H _ (nonsimpleFaceNormalPoint_mem u b H)

theorem nonsimpleFaceCoordinateLift_generator (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (i : Fin (Fintype.card H.1)) :
    nonsimpleFaceCoordinateLift u b H (nonsimpleFaceCoordinateNormals u b H i)=
      u (nonsimpleFaceActiveIndex H.1 i) :=
  nonsimpleFaceCoordinateLift_map_of_mem u b H _
    (nonsimple_normal_mem u H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i))

theorem nonsimpleFaceCoordinateLift_conormal (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (e : Fin (Fintype.card (NonsimpleRidgeAt u b H))) :
    nonsimpleFaceCoordinateLift u b H (nonsimpleRidgeCoordinateConormal u b H e)=
      nonsimpleIncidentConormal u b H (nonsimpleFaceRidgeIndex u b H e) :=
  nonsimpleFaceCoordinateLift_map_of_mem u b H _ (nonsimpleIncidentConormal_mem u b H _)

theorem nonsimpleFaceCoordinateLift_mem_generated_iff (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E3) :
    x∈sphericalPolygonGeneratedCone (nonsimpleFaceCoordinateNormals u b H) ↔
      nonsimpleFaceCoordinateLift u b H x∈nonsimpleActiveGeneratedCone u H.1 := by
  classical
  let e := Fintype.equivFin H.1
  constructor
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun j : H.1 => a (e j),fun j => ha (e j),?_⟩
    rw [hx,map_sum]
    simp_rw [map_smul,nonsimpleFaceCoordinateLift_generator]
    exact (by simpa only [e,nonsimpleFaceActiveIndex,Equiv.apply_symm_apply] using
      (Fintype.equivFin H.1).symm.sum_comp (fun j : H.1 => a (Fintype.equivFin H.1 j) • u j.val))
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun i => a (e.symm i),fun i => ha (e.symm i),?_⟩
    have he : (∑ i : Fin (Fintype.card H.1),a (e.symm i) • u (nonsimpleFaceActiveIndex H.1 i))=
        ∑ j : H.1,a j • u j.val := by
      simpa only [e,nonsimpleFaceActiveIndex] using e.symm.sum_comp (fun j : H.1 => a j • u j.val)
    apply (nonsimpleFaceCoordinateLift u b H).injective
    rw [map_sum]
    simp_rw [map_smul,nonsimpleFaceCoordinateLift_generator]
    exact hx.trans he.symm

section Original
variable {r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
local notation "uE" => (fun j => projectionEuclideanVector (u j))
local notation "N" => nonsimpleRidgeCoordinateConormal uE b H
local notation "Ridges" => NonsimpleRidgeAt uE b H

theorem nonsimpleFaceCoordinateCone_eq_actual_normalCone :
    nonsimpleFaceCoordinateCone u b H=
      tripleOutwardNormalCone u H.1 (nonsimpleFaceCoordinateLift uE b H) := by
  ext x
  rw [nonsimpleFaceCoordinateCone,nonsimpleFaceCoordinateLift_mem_generated_iff,
    nonsimpleActiveGeneratedCone_mem_iff]
  rfl

include hi hw hu in
theorem nonsimpleActualNormalCone_eq_incident_halfspaces :
    tripleOutwardNormalCone u H.1 (nonsimpleFaceCoordinateLift uE b H)=
      {x : E3 | ∀ e,⟪-N e,x⟫_ℝ≤0} := by
  rw [←nonsimpleFaceCoordinateCone_eq_actual_normalCone,
    nonsimpleFaceCoordinateCone_eq_incident_halfspaces u b hi hw hu H]

include hi hw hu in
theorem nonsimpleActualNormalCone_isClosed :
    IsClosed (tripleOutwardNormalCone u H.1 (nonsimpleFaceCoordinateLift uE b H)) := by
  rw [nonsimpleActualNormalCone_eq_incident_halfspaces u b hi hw hu H]
  have he : {x : E3 | ∀ e,⟪-N e,x⟫_ℝ≤0}=⋂ e,{x : E3 | ⟪-N e,x⟫_ℝ≤0} := by
    ext x
    simp
  rw [he]
  apply isClosed_iInter
  intro e
  exact isClosed_le (by fun_prop : Continuous (fun x : E3 => ⟪-N e,x⟫_ℝ)) continuous_const

include hi hw hu in
theorem nonsimpleActualNormalCone_measurable :
    MeasurableSet (tripleOutwardNormalCone u H.1 (nonsimpleFaceCoordinateLift uE b H)) :=
  (nonsimpleActualNormalCone_isClosed u b hi hw hu H).measurableSet

theorem nonsimpleFaceNative_spherical_balance :
    (∑ e,nonsimpleRidgeOriginalAngle u b hi hw hu H e •
      nonsimpleIncidentConormal uE b H (nonsimpleFaceRidgeIndex uE b H e))=
      nonsimpleFaceCoordinateLift uE b H ((2 : ℝ) •
        ∫ ω in supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H),
          ω.1 ∂(volume : Measure E3).toSphere) := by
  have h := congrArg (nonsimpleFaceCoordinateLift uE b H)
    (nonsimpleFaceCoordinate_spherical_balance u b hi hw hu H)
  simpa only [map_sum,map_smul,nonsimpleFaceCoordinateLift_conormal] using h

theorem nonsimpleFaceNative_spherical_balance_norm_le :
    ‖∑ e,nonsimpleRidgeOriginalAngle u b hi hw hu H e •
      nonsimpleIncidentConormal uE b H (nonsimpleFaceRidgeIndex uE b H e)‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H)) := by
  have h := nonsimpleFaceCoordinate_spherical_balance_norm_le u b hi hw hu H
  have hn := (nonsimpleFaceCoordinateLift uE b H).norm_map
    (∑ e,nonsimpleRidgeOriginalAngle u b hi hw hu H e • N e)
  simp only [map_sum,map_smul,nonsimpleFaceCoordinateLift_conormal] at hn
  exact hn.symm ▸ h

end Original
end
end RectangleCLTArxivV1
