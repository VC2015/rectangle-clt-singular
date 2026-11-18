import RectangleCLTArxivV1.SupplementalHTripleIncidenceGeometry
import RectangleCLTArxivV1.SupplementalHFrameIsometry
import RectangleCLTArxivV1.SupplementalHTrihedralNormals
import RectangleCLTArxivV1.SupplementalHTripleTransportThreeFace
import RectangleCLTArxivV1.SupplementalHIndependentTriples

/-! The actual coordinate model of a selected independent triple.  The
orthonormal conditioning frame, its normal point, and its generated cone
are constructed from the original normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tripleIncidenceTransportIsometry {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) :=
  orthonormalFrameIsometry (tripleIncidenceFrame u F 0)
    (tripleIncidenceFrame_orthonormal u F hi hu 0)

def tripleIncidenceTransportPoint {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (tripleIncidenceLevels u b F 0)

def tripleIncidenceTransportRay {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  orthonormalFrameCoordinates (tripleIncidenceFrame u F 0)
    (tripleIncidenceOriginalNormals u F i)

theorem tripleIncidenceTransportIsometry_ray {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    tripleIncidenceTransportIsometry u F hi hu (tripleIncidenceTransportRay u F i)=
      tripleIncidenceOriginalNormals u F i := by
  apply orthonormalFrameIsometry_coordinates_of_mem
  rw [tripleIncidenceFrame_span u F hi hu 0]
  exact Submodule.subset_span ⟨i,rfl⟩

theorem tripleIncidenceTransportRay_linearIndependent {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    LinearIndependent ℝ (tripleIncidenceTransportRay u F) := by
  have ho : LinearIndependent ℝ (tripleIncidenceOriginalNormals u F) :=
    hi.map' (WithLp.linearEquiv 2 ℝ (Vector r)).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Vector r)).symm.injective)
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  apply Fintype.linearIndependent_iff.mp ho a
  have h := congrArg (tripleIncidenceTransportIsometry u F hi hu) ha
  simpa only [map_sum,map_smul,map_zero,tripleIncidenceTransportIsometry_ray] using h

def tripleIncidenceTransportBasis {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  basisOfLinearIndependentOfCardEqFinrank
    (tripleIncidenceTransportRay_linearIndependent u F hi hu) (by simp)

theorem tripleIncidenceTransportBasis_apply {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    tripleIncidenceTransportBasis u F hi hu i=tripleIncidenceTransportRay u F i := by
  simp [tripleIncidenceTransportBasis]

theorem tripleIncidenceTransportIsometry_basis {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    tripleIncidenceTransportIsometry u F hi hu (tripleIncidenceTransportBasis u F hi hu i)=
      tripleIncidenceOriginalNormals u F i := by
  rw [tripleIncidenceTransportBasis_apply,tripleIncidenceTransportIsometry_ray]

theorem tripleIncidenceTransportBasis_norm {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    ‖tripleIncidenceTransportBasis u F hi hu i‖=1 := by
  rw [← (tripleIncidenceTransportIsometry u F hi hu).norm_map,
    tripleIncidenceTransportIsometry_basis]
  exact thresholdEuclideanNormal_unit _ (hu i)

theorem tripleIncidenceTransportIsometry_point {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    tripleIncidenceTransportIsometry u F hi hu (tripleIncidenceTransportPoint u b F)=
      tripleIncidenceNormalPoint u b F 0 := rfl

theorem tripleIncidenceTransportFrame_eq {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    tripleTransportFrame (tripleIncidenceTransportIsometry u F hi hu)=tripleIncidenceFrame u F 0 := by
  funext i
  change orthonormalFrameIsometry _ _ (EuclideanSpace.basisFun (Fin 3) ℝ i)=_
  simpa only [EuclideanSpace.basisFun_apply] using
    orthonormalFrameIsometry_single (tripleIncidenceFrame u F 0)
      (tripleIncidenceFrame_orthonormal u F hi hu 0) i

theorem tripleIncidenceTransportFrame_span {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    Submodule.span ℝ (range (tripleTransportFrame (tripleIncidenceTransportIsometry u F hi hu)))=
      Submodule.span ℝ (range (tripleIncidenceOriginalNormals u F)) := by
  rw [tripleIncidenceTransportFrame_eq,tripleIncidenceFrame_span u F hi hu 0]

theorem tripleIncidenceTransport_supporting_levels {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    ⟪tripleIncidenceOriginalNormals u F i,
      tripleIncidenceTransportIsometry u F hi hu (tripleIncidenceTransportPoint u b F)⟫_ℝ=b (F i) := by
  rw [tripleIncidenceTransportIsometry_point]
  exact tripleIncidenceNormalPoint_supporting_levels u b F hi hu 0 i

end
end RectangleCLTArxivV1
