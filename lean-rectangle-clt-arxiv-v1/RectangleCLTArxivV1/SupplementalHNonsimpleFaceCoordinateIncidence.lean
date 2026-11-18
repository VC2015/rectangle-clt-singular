import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinates

/-! All actual ridge incidences in canonical normal-space coordinates.
The endpoint indices come from the proved two-facet property of actual
ridges in an irredundant full-dimensional original presentation. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}

def nonsimpleFaceRidgeIndex (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) :
    Fin (Fintype.card (NonsimpleRidgeAt u b H)) ≃ NonsimpleRidgeAt u b H :=
  (Fintype.equivFin (NonsimpleRidgeAt u b H)).symm

def nonsimpleRidgeCoordinateConormal (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (e : Fin (Fintype.card (NonsimpleRidgeAt u b H))) : E3 :=
  nonsimpleFaceCoordinateMap u b H
    (nonsimpleIncidentConormal u b H (nonsimpleFaceRidgeIndex u b H e))

theorem nonsimpleRidgeCoordinateConormal_unit (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (e : Fin (Fintype.card (NonsimpleRidgeAt u b H))) :
    ‖nonsimpleRidgeCoordinateConormal u b H e‖=1 := by
  rw [nonsimpleRidgeCoordinateConormal,nonsimpleFaceCoordinateMap_norm u b H _
    (nonsimpleIncidentConormal_mem u b H _),nonsimpleIncidentConormal_unit]

theorem nonsimpleRidgeCoordinateConormal_inner (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (e : Fin (Fintype.card (NonsimpleRidgeAt u b H)))
    (i : Fin (Fintype.card H.1)) :
    ⟪nonsimpleRidgeCoordinateConormal u b H e,nonsimpleFaceCoordinateNormals u b H i⟫_ℝ=
      ⟪nonsimpleIncidentConormal u b H (nonsimpleFaceRidgeIndex u b H e),
        u (nonsimpleFaceActiveIndex H.1 i)⟫_ℝ :=
  nonsimpleFaceCoordinateMap_inner_left u b H _ _ (nonsimpleIncidentConormal_mem u b H _)

theorem nonsimpleRidgeCoordinateConormal_nonneg (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (e : Fin (Fintype.card (NonsimpleRidgeAt u b H)))
    (i : Fin (Fintype.card H.1)) :
    0≤⟪nonsimpleRidgeCoordinateConormal u b H e,nonsimpleFaceCoordinateNormals u b H i⟫_ℝ := by
  rw [nonsimpleRidgeCoordinateConormal_inner]
  exact nonsimpleIncidentConormal_nonneg u b H _ _ (nonsimpleFaceActiveIndex_mem H.1 i)

section Original
variable {r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
local notation "uE" => (fun j => projectionEuclideanVector (u j))
local notation "Ridges" => NonsimpleRidgeAt uE b H

def nonsimpleActualRidgePair (I : Ridges) :
    {p : Fin m × Fin m // p.1≠p.2 ∧ I.1.1={p.1,p.2}} := by
  classical
  have hex : ∃ p : Fin m × Fin m,p.1≠p.2 ∧ I.1.1={p.1,p.2} := by
    obtain ⟨a,d,had,hI⟩ := Finset.card_eq_two.mp (nonsimple_ridge_card_eq_two u b hi hw hu I.1)
    exact ⟨(a,d),had,hI⟩
  exact ⟨hex.choose,hex.choose_spec⟩

def nonsimpleRidgeCoordinateLeft (e : Fin (Fintype.card Ridges)) : Fin (Fintype.card H.1) :=
  nonsimpleFaceLocalIndex H.1 (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).1.1
    ((nonsimpleFaceRidgeIndex uE b H e).2 (by
      exact (Finset.ext_iff.mp
        (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2 _).mpr
          (by simp)))

def nonsimpleRidgeCoordinateRight (e : Fin (Fintype.card Ridges)) : Fin (Fintype.card H.1) :=
  nonsimpleFaceLocalIndex H.1 (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).1.2
    ((nonsimpleFaceRidgeIndex uE b H e).2 (by
      exact (Finset.ext_iff.mp
        (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2 _).mpr
          (by simp)))

theorem nonsimpleRidgeCoordinateLeft_original (e : Fin (Fintype.card Ridges)) :
    nonsimpleFaceActiveIndex H.1 (nonsimpleRidgeCoordinateLeft u b hi hw hu H e)=
      (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).1.1 := by
  exact nonsimpleFaceActiveIndex_localIndex _ _ _

theorem nonsimpleRidgeCoordinateRight_original (e : Fin (Fintype.card Ridges)) :
    nonsimpleFaceActiveIndex H.1 (nonsimpleRidgeCoordinateRight u b hi hw hu H e)=
      (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).1.2 := by
  exact nonsimpleFaceActiveIndex_localIndex _ _ _

theorem nonsimpleRidgeCoordinate_pair_distinct (e : Fin (Fintype.card Ridges)) :
    nonsimpleRidgeCoordinateLeft u b hi hw hu H e≠nonsimpleRidgeCoordinateRight u b hi hw hu H e := by
  intro he
  have h := congrArg (nonsimpleFaceActiveIndex H.1) he
  rw [nonsimpleRidgeCoordinateLeft_original,nonsimpleRidgeCoordinateRight_original] at h
  exact (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.1 h

theorem nonsimpleRidgeCoordinate_pair_image (e : Fin (Fintype.card Ridges)) :
    ({nonsimpleRidgeCoordinateLeft u b hi hw hu H e,nonsimpleRidgeCoordinateRight u b hi hw hu H e} :
      Finset (Fin (Fintype.card H.1))).image (nonsimpleFaceActiveIndex H.1)=
      (nonsimpleFaceRidgeIndex uE b H e).1.1 := by
  classical
  rw [Finset.image_insert,Finset.image_singleton,nonsimpleRidgeCoordinateLeft_original,nonsimpleRidgeCoordinateRight_original]
  exact (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2.symm

theorem nonsimpleRidgeCoordinate_pairs_injective :
    Function.Injective (fun e => ({nonsimpleRidgeCoordinateLeft u b hi hw hu H e,
      nonsimpleRidgeCoordinateRight u b hi hw hu H e} : Finset (Fin (Fintype.card H.1)))) := by
  intro e f hef
  apply (nonsimpleFaceRidgeIndex uE b H).injective
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (Finset.image (nonsimpleFaceActiveIndex H.1)) hef
  simpa only [nonsimpleRidgeCoordinate_pair_image] using h

end Original
end
end RectangleCLTArxivV1
