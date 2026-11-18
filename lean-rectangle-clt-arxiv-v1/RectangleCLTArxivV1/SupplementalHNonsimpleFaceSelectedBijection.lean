import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelectedExistence

/-! Exact finite bijection between selected tangent facets of a genuine
ridge and all its original codimension-three cofaces. No simplicity or
generic-threshold hypothesis is present. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev NonsimpleFacesAtPair {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :=
  {H : NonsimpleFaceIndex (fun k => projectionEuclideanVector (u k)) b 3 // j∈H.1 ∧ l∈H.1}

noncomputable instance nonsimpleFacesAtPairFintype {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (j l : Fin m) : Fintype (NonsimpleFacesAtPair u b j l) := Fintype.ofFinite _

theorem ActualRidgeFacetPresentation.selectedActualFace_eq_of_supporting_index {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (fun k => projectionEuclideanVector (u k)) b 3)
    (hjH : j∈H.1) (hlH : l∈H.1) (hiH : P.index i∈H.1) :
    P.selectedActualFace hi hw hu hjl hridge i=H := by
  have hki : P.index i≠j := (Finset.mem_erase.mp (Finset.mem_erase.mp (P.retained i)).2).1
  have hkl : P.index i≠l := (Finset.mem_erase.mp (P.retained i)).1
  let F : Fin 3 → Fin m := ![j,l,P.index i]
  have hF : Function.Injective F := by
    intro p q he
    fin_cases p <;> fin_cases q <;> first
      | rfl
      | exact False.elim (hjl he)
      | exact False.elim (hjl he.symm)
      | exact False.elim (hki he)
      | exact False.elim (hki he.symm)
      | exact False.elim (hkl he)
      | exact False.elim (hkl he.symm)
  have hmem (p : Fin 3) : F p∈H.1 := by
    fin_cases p
    · exact hjH
    · exact hlH
    · exact hiH
  have hspan := nonsimple_codimThree_triple_spans u b hi hw hu H F hF hmem
  have hc := nonsimpleClosedFace_eq_spanning_levels (fun k => projectionEuclideanVector (u k)) b H F hmem hspan
  have heq : nonsimpleClosedFace (fun k => projectionEuclideanVector (u k)) b
      (P.selectedActualFace hi hw hu hjl hridge i).1=
      nonsimpleClosedFace (fun k => projectionEuclideanVector (u k)) b H.1 :=
    (P.selectedActualFace_closedFace hi hw hu hjl hridge i).trans hc.symm
  exact Subtype.ext ((nonsimpleClosedFace_eq_iff _ b _ _
    (P.selectedActualFace hi hw hu hjl hridge i).2.1 H.2.1).mp heq)

def ActualRidgeFacetPresentation.selectedFaceAtPair {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) : NonsimpleFacesAtPair u b j l :=
  ⟨P.selectedActualFace hi hw hu hjl hridge i,
    (P.selectedActualFace_supporting_indices hi hw hu hjl hridge i).1,
    (P.selectedActualFace_supporting_indices hi hw hu hjl hridge i).2.1⟩

theorem ActualRidgeFacetPresentation.selectedFaceAtPair_bijective {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) :
    Function.Bijective (P.selectedFaceAtPair hi hw hu hjl hridge) := by
  constructor
  · intro i k he
    exact P.selectedActualFace_injective hi hw hu hjl hridge (congrArg Subtype.val he)
  · intro H
    obtain ⟨i,hiH⟩ := P.incident_face_has_selected_active hi hw hu hjl H.1 H.2.1 H.2.2
    exact ⟨i,Subtype.ext (P.selectedActualFace_eq_of_supporting_index hi hw hu hjl hridge i H.1 H.2.1 H.2.2 hiH)⟩

def ActualRidgeFacetPresentation.selectedActualFaceEquiv {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) : Fin P.count ≃ NonsimpleFacesAtPair u b j l :=
  Equiv.ofBijective _ (P.selectedFaceAtPair_bijective hi hw hu hjl hridge)

theorem ActualRidgeFacetPresentation.sum_selectedActualFace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (f : NonsimpleFacesAtPair u b j l → ℝ) :
    (∑ i,f (P.selectedFaceAtPair hi hw hu hjl hridge i))=∑ H,f H :=
  (P.selectedActualFaceEquiv hi hw hu hjl hridge).sum_comp f

end
end RectangleCLTArxivV1
