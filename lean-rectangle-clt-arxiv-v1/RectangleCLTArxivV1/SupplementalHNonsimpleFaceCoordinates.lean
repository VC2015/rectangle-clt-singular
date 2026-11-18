import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoverage
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceFrame
import RectangleCLTArxivV1.SupplementalHSphericalPolygonCoverage

/-! Canonical coordinates of all original normals active at an actual
rank-three face. The number of active facets is unrestricted. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

def nonsimpleFaceActiveIndex {m : ℕ} (S : Finset (Fin m))
    (i : Fin (Fintype.card S)) : Fin m := ((Fintype.equivFin S).symm i).val

theorem nonsimpleFaceActiveIndex_mem {m : ℕ} (S : Finset (Fin m))
    (i : Fin (Fintype.card S)) : nonsimpleFaceActiveIndex S i∈S :=
  ((Fintype.equivFin S).symm i).property

theorem nonsimpleFaceActiveIndex_injective {m : ℕ} (S : Finset (Fin m)) :
    Function.Injective (nonsimpleFaceActiveIndex S) :=
  Subtype.val_injective.comp (Fintype.equivFin S).symm.injective

def nonsimpleFaceLocalIndex {m : ℕ} (S : Finset (Fin m)) (j : Fin m) (hj : j∈S) :
    Fin (Fintype.card S) := Fintype.equivFin S ⟨j,hj⟩

@[simp] theorem nonsimpleFaceActiveIndex_localIndex {m : ℕ}
    (S : Finset (Fin m)) (j : Fin m) (hj : j∈S) :
    nonsimpleFaceActiveIndex S (nonsimpleFaceLocalIndex S j hj)=j := by
  simp [nonsimpleFaceActiveIndex,nonsimpleFaceLocalIndex]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}
local notation "E3" => EuclideanSpace ℝ (Fin 3)

def nonsimpleFaceCoordinateMap (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) : E →ₗ[ℝ] E3 :=
  (nonsimpleFaceBasis u b H).repr.toLinearMap.comp
    (nonsimpleFaceNormalSpace u H.1).orthogonalProjection.toLinearMap

theorem nonsimpleFaceCoordinateMap_of_mem (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E) (hx : x∈nonsimpleFaceNormalSpace u H.1) :
    nonsimpleFaceCoordinateMap u b H x=(nonsimpleFaceBasis u b H).repr ⟨x,hx⟩ := by
  change (nonsimpleFaceBasis u b H).repr ((nonsimpleFaceNormalSpace u H.1).orthogonalProjection x)=_
  congr 1
  apply Subtype.ext
  exact Submodule.orthogonalProjection_eq_self_iff.mpr hx

theorem nonsimpleFaceCoordinateMap_norm (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x : E) (hx : x∈nonsimpleFaceNormalSpace u H.1) :
    ‖nonsimpleFaceCoordinateMap u b H x‖=‖x‖ := by
  rw [nonsimpleFaceCoordinateMap_of_mem u b H x hx]
  exact (nonsimpleFaceBasis u b H).repr.norm_map _

theorem nonsimpleFaceCoordinateMap_inner_left (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (x y : E) (hx : x∈nonsimpleFaceNormalSpace u H.1) :
    ⟪nonsimpleFaceCoordinateMap u b H x,nonsimpleFaceCoordinateMap u b H y⟫_ℝ=⟪x,y⟫_ℝ := by
  rw [nonsimpleFaceCoordinateMap_of_mem u b H x hx]
  change ⟪(nonsimpleFaceBasis u b H).repr ⟨x,hx⟩,
    (nonsimpleFaceBasis u b H).repr ((nonsimpleFaceNormalSpace u H.1).orthogonalProjection y)⟫_ℝ=_
  rw [(nonsimpleFaceBasis u b H).repr.inner_map_map]
  exact (nonsimpleFaceNormalSpace u H.1).inner_orthogonalProjection_eq_of_mem_left ⟨x,hx⟩ y

def nonsimpleFaceCoordinateNormals (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) : Fin (Fintype.card H.1) → E3 :=
  fun i => nonsimpleFaceCoordinateMap u b H (u (nonsimpleFaceActiveIndex H.1 i))

theorem nonsimpleFaceCoordinateNormals_inner (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (i j : Fin (Fintype.card H.1)) :
    ⟪nonsimpleFaceCoordinateNormals u b H i,nonsimpleFaceCoordinateNormals u b H j⟫_ℝ=
      ⟪u (nonsimpleFaceActiveIndex H.1 i),u (nonsimpleFaceActiveIndex H.1 j)⟫_ℝ :=
  nonsimpleFaceCoordinateMap_inner_left u b H _ _
    (nonsimple_normal_mem u H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i))

theorem nonsimpleFaceCoordinateNormals_span (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) :
    Submodule.span ℝ (Set.range (nonsimpleFaceCoordinateNormals u b H))=⊤ := by
  classical
  let K := Submodule.span ℝ (Set.range (nonsimpleFaceCoordinateNormals u b H))
  have hmap : ∀ x∈nonsimpleFaceNormalSpace u H.1,nonsimpleFaceCoordinateMap u b H x∈K := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j,hj,rfl⟩ := hx
      have hgen : nonsimpleFaceCoordinateNormals u b H (nonsimpleFaceLocalIndex H.1 j hj)∈K :=
        Submodule.subset_span ⟨_,rfl⟩
      simpa only [nonsimpleFaceCoordinateNormals,nonsimpleFaceActiveIndex_localIndex] using hgen
    | zero => simpa only [map_zero] using K.zero_mem
    | add x y hx hy hx0 hy0 => simpa only [map_add] using K.add_mem hx0 hy0
    | smul c x hx hx0 => simpa only [map_smul] using K.smul_mem c hx0
  apply top_unique
  intro y _
  let X := (nonsimpleFaceBasis u b H).repr.symm y
  have h := hmap X.val X.property
  rw [nonsimpleFaceCoordinateMap_of_mem u b H X.val X.property] at h
  change (nonsimpleFaceBasis u b H).repr X∈K at h
  exact ((nonsimpleFaceBasis u b H).repr.apply_symm_apply y) ▸ h

theorem nonsimpleFaceCoordinateNormals_unit (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (hu : ∀ j,‖u j‖=1) (i : Fin (Fintype.card H.1)) :
    ‖nonsimpleFaceCoordinateNormals u b H i‖=1 := by
  rw [nonsimpleFaceCoordinateNormals,nonsimpleFaceCoordinateMap_norm u b H _
    (nonsimple_normal_mem u H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i)),hu]

theorem nonsimpleFaceCoordinateNormals_exists_strictPolar (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (hi : ∃ x : E,∀ j,⟪u j,x⟫_ℝ<b j) :
    ∃ d : E3,∀ i,⟪nonsimpleFaceCoordinateNormals u b H i,d⟫_ℝ<0 := by
  obtain ⟨d,hd⟩ := nonsimpleFace_exists_strictPolar u b hi H
  refine ⟨nonsimpleFaceCoordinateMap u b H d,?_⟩
  intro i
  rw [nonsimpleFaceCoordinateNormals,nonsimpleFaceCoordinateMap_inner_left u b H _ _
    (nonsimple_normal_mem u H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i))]
  exact hd _ (nonsimpleFaceActiveIndex_mem H.1 i)

end
end RectangleCLTArxivV1
