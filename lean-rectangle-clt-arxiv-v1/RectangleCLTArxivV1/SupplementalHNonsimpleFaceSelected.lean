import RectangleCLTArxivV1.SupplementalHNonsimpleFaceRetained
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceIndependence
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSpanning
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenFacetPoint

/-! An actual selected tangent facet of an original ridge determines a
complete original codimension-three face. Deleted coincident residual
constraints are retained when the complete active set is formed. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ActualRidgeFacetPresentation.exists_complete_active_face_rank_three_with_selected_strictness {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    ∃ x : Vector r, (∀ k,faceDot (u k) x≤b k) ∧
      faceDot (u j) x=b j ∧ faceDot (u l) x=b l ∧ faceDot (u (P.index i)) x=b (P.index i) ∧
      (∀ k : Fin P.count,k≠i → faceDot (u (P.index k)) x<b (P.index k)) ∧
      Module.finrank ℝ (nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k))
        (nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b (projectionEuclideanVector x)))=3 := by
  classical
  obtain ⟨xr,hxrj,hxrl,hxrstrict⟩ := hridge
  have hp := actualFacet_pair_support_nonparallel u b hi hw j l hjl xr hxrj hxrl
  obtain ⟨x,hx,hxj,hxl,hxi,hxsel⟩ := P.exists_original_boundary_point (hu j) (hu l) hp i
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  let V := hardPairResidualNormals u e f
  let B := hardPairResidualLevels u b e f a c
  let s := (Finset.univ.erase j).erase l
  have hef : faceDot e f=0 := thresholdPair_frame_orthogonal u j l (hu j) (hu l)
  obtain ⟨hxe,hxf⟩ := thresholdPair_frame_levels_of_support u b j l x hp.1 hp.2 hxj hxl
  have hdot (k : Fin m) : faceDot (V k) x-B k=faceDot (u k) x-b k := by
    dsimp only [V,B,hardPairResidualNormals,hardPairResidualLevels]
    rw [hardPairResidualNormal_eq_sub e f (u k) hef,threshold_faceDot_sub_left,
      threshold_faceDot_sub_left,threshold_faceDot_smul_left,threshold_faceDot_smul_left,hxe,hxf]
    ring
  have hinner (v : Vector r) (z : EuclideanSpace ℝ (Fin r)) :
      ⟪projectionEuclideanVector v,z⟫_ℝ=faceDot v (WithLp.equiv 2 (Vector r) z) := by
    rw [faceDot_eq_euclidean_inner]
    rfl
  have hinnerProj (v w : Vector r) :
      ⟪projectionEuclideanVector v,projectionEuclideanVector w⟫_ℝ=faceDot v w :=
    (faceDot_eq_euclidean_inner v w).symm
  have hpoly (z : EuclideanSpace ℝ (Fin r)) :
      (∀ k,⟪projectionEuclideanVector (P.normals k),z⟫_ℝ≤P.levels k) ↔
      ∀ k∈s,⟪projectionEuclideanVector (V k),z⟫_ℝ≤B k := by
    simp_rw [hinner]
    exact P.event_iff _
  have horig : ∃ z : EuclideanSpace ℝ (Fin r),∀ k∈s,⟪projectionEuclideanVector (V k),z⟫_ℝ<B k := by
    obtain ⟨g,hg⟩ := (hasStrictRidgeInterior_iff_residual u b j l (hu j) (hu l) hp).mp
      ⟨xr,hxrj,hxrl,hxrstrict⟩
    refine ⟨projectionEuclideanVector g,?_⟩
    intro k hk
    rw [hinnerProj]
    exact hg k hk
  have hselected : ∃ z : EuclideanSpace ℝ (Fin r),∀ k,⟪projectionEuclideanVector (P.normals k),z⟫_ℝ<P.levels k := by
    obtain ⟨g,hg⟩ := P.strict
    refine ⟨projectionEuclideanVector g,?_⟩
    intro k
    rw [hinnerProj]
    exact hg k
  have hsingleton : ⟪projectionEuclideanVector (P.normals i),projectionEuclideanVector x⟫_ℝ=P.levels i ∧
      ∀ k,k≠i → ⟪projectionEuclideanVector (P.normals k),projectionEuclideanVector x⟫_ℝ<P.levels k := by
    constructor
    · have hh := hdot (P.index i)
      rw [hinnerProj]
      change faceDot (V (P.index i)) x=B (P.index i)
      linarith
    · intro k hki
      have hh := hdot (P.index k)
      rw [hinnerProj]
      change faceDot (V (P.index k)) x<B (P.index k)
      linarith [hxsel k hki]
  let F : Fin 3 → Fin m := ![j,l,P.index i]
  have hkji : P.index i≠j := (Finset.mem_erase.mp (Finset.mem_erase.mp (P.retained i)).2).1
  have hkli : P.index i≠l := (Finset.mem_erase.mp (P.retained i)).1
  have hF : Function.Injective F := by
    intro p q he
    fin_cases p <;> fin_cases q <;> first
      | rfl
      | exact False.elim (hjl he)
      | exact False.elim (hjl he.symm)
      | exact False.elim (hkji he)
      | exact False.elim (hkji he.symm)
      | exact False.elim (hkli he)
      | exact False.elim (hkli he.symm)
  have hlev (p : Fin 3) : faceDot (u (F p)) x=b (F p) := by
    fin_cases p
    · exact hxj
    · exact hxl
    · exact hxi
  have hlin := nonsimple_active_triple_euclidean_linearIndependent u b hi hw hu F hF x hlev
  let T := Submodule.span ℝ (range (fun p => projectionEuclideanVector (u (F p))))
  have hmj : projectionEuclideanVector (u j)∈T := Submodule.subset_span ⟨0,rfl⟩
  have hml : projectionEuclideanVector (u l)∈T := Submodule.subset_span ⟨1,rfl⟩
  have hmi : projectionEuclideanVector (u (P.index i))∈T := Submodule.subset_span ⟨2,rfl⟩
  have he : projectionEuclideanVector e∈T := by
    have heq : projectionEuclideanVector e=
        ‖projectionEuclideanVector (u j)+projectionEuclideanVector (u l)‖⁻¹ •
          (projectionEuclideanVector (u j)+projectionEuclideanVector (u l)) := by
      apply PiLp.ext
      intro k
      rfl
    rw [heq]
    exact T.smul_mem _ (T.add_mem hmj hml)
  have hf : projectionEuclideanVector f∈T := by
    have heq : projectionEuclideanVector f=
        ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖⁻¹ •
          (projectionEuclideanVector (u j)-projectionEuclideanVector (u l)) := by
      apply PiLp.ext
      intro k
      rfl
    rw [heq]
    exact T.smul_mem _ (T.sub_mem hmj hml)
  have hres (k : Fin m) : projectionEuclideanVector (V k)=projectionEuclideanVector (u k)-
      faceDot (u k) e • projectionEuclideanVector e-faceDot (u k) f • projectionEuclideanVector f := by
    apply (WithLp.equiv 2 (Vector r)).injective
    exact hardPairResidualNormal_eq_sub e f (u k) hef
  have hvi : projectionEuclideanVector (P.normals i)∈T := by
    change projectionEuclideanVector (V (P.index i))∈T
    rw [hres]
    exact T.sub_mem (T.sub_mem hmi (T.smul_mem _ he)) (T.smul_mem _ hf)
  let S := nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b (projectionEuclideanVector x)
  have hSlev (k : Fin m) (hk : k∈S) : faceDot (u k) x=b k := by
    have hh := (mem_nonsimpleActiveSet _ b _ k).mp hk
    rw [hinnerProj] at hh
    exact hh
  have hall (k : Fin m) (hk : k∈S) : projectionEuclideanVector (u k)∈T := by
    by_cases hkj : k=j
    · simpa only [hkj] using hmj
    by_cases hkl : k=l
    · simpa only [hkl] using hml
    have hks : k∈s := Finset.mem_erase.mpr ⟨hkl,Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ _⟩⟩
    have hractive : ⟪projectionEuclideanVector (V k),projectionEuclideanVector x⟫_ℝ=B k := by
      rw [hinnerProj]
      have hh := hdot k
      linarith [hSlev k hk]
    obtain ⟨c,hc,hprop,_⟩ := nonsimple_retained_presentation_active_multiple
      (fun k => projectionEuclideanVector (V k)) B s (fun k => projectionEuclideanVector (P.normals k)) P.levels
      hpoly horig hselected (projectionEuclideanVector x) i hsingleton k hks hractive
    have hrmem : projectionEuclideanVector (V k)∈T := by rw [hprop]; exact T.smul_mem _ hvi
    have hdecomp : projectionEuclideanVector (u k)=projectionEuclideanVector (V k)+
        faceDot (u k) e • projectionEuclideanVector e+faceDot (u k) f • projectionEuclideanVector f := by
      rw [hres]
      module
    rw [hdecomp]
    exact T.add_mem (T.add_mem hrmem (T.smul_mem _ he)) (T.smul_mem _ hf)
  have hsub : nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k)) S≤T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact hall k hk
  have hsup : T≤nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k)) S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    apply nonsimple_normal_mem
    apply (mem_nonsimpleActiveSet _ b _ (F p)).mpr
    rw [hinnerProj]
    exact hlev p
  have heq := le_antisymm hsub hsup
  refine ⟨x,hx,hxj,hxl,hxi,hxsel,?_⟩
  rw [show nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k)) S=T from heq]
  exact (finrank_span_eq_card hlin).trans (Fintype.card_fin 3)

theorem ActualRidgeFacetPresentation.exists_complete_active_face_rank_three {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    ∃ x : Vector r, (∀ k,faceDot (u k) x≤b k) ∧
      faceDot (u j) x=b j ∧ faceDot (u l) x=b l ∧ faceDot (u (P.index i)) x=b (P.index i) ∧
      Module.finrank ℝ (nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k))
        (nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b (projectionEuclideanVector x)))=3 := by
  obtain ⟨x,hx,hj,hl,hi,_,hr⟩ := P.exists_complete_active_face_rank_three_with_selected_strictness hi hw hu hjl hridge i
  exact ⟨x,hx,hj,hl,hi,hr⟩

def ActualRidgeFacetPresentation.selectedFacePoint {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) : Vector r :=
  (P.exists_complete_active_face_rank_three_with_selected_strictness hi hw hu hjl hridge i).choose

theorem ActualRidgeFacetPresentation.selectedFacePoint_spec {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    let x := P.selectedFacePoint hi hw hu hjl hridge i
    (∀ k,faceDot (u k) x≤b k) ∧ faceDot (u j) x=b j ∧ faceDot (u l) x=b l ∧
      faceDot (u (P.index i)) x=b (P.index i) ∧
      (∀ k : Fin P.count,k≠i → faceDot (u (P.index k)) x<b (P.index k)) ∧
      Module.finrank ℝ (nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k))
        (nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b (projectionEuclideanVector x)))=3 :=
  (P.exists_complete_active_face_rank_three_with_selected_strictness hi hw hu hjl hridge i).choose_spec

def ActualRidgeFacetPresentation.selectedActualFace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    NonsimpleFaceIndex (fun k => projectionEuclideanVector (u k)) b 3 := by
  let x := P.selectedFacePoint hi hw hu hjl hridge i
  have hs := P.selectedFacePoint_spec hi hw hu hjl hridge i
  refine ⟨nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b (projectionEuclideanVector x),
    ⟨projectionEuclideanVector x,nonsimpleActiveSet_exactStratum _ b ?_⟩,hs.2.2.2.2.2⟩
  intro k
  have hh := hs.1 k
  rw [faceDot_eq_euclidean_inner] at hh
  exact hh

theorem ActualRidgeFacetPresentation.selectedActualFace_mem_iff {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) (k : Fin m) :
    k∈(P.selectedActualFace hi hw hu hjl hridge i).1 ↔
      faceDot (u k) (P.selectedFacePoint hi hw hu hjl hridge i)=b k := by
  change k∈nonsimpleActiveSet (fun k => projectionEuclideanVector (u k)) b
    (projectionEuclideanVector (P.selectedFacePoint hi hw hu hjl hridge i)) ↔ _
  rw [mem_nonsimpleActiveSet]
  have he : ⟪projectionEuclideanVector (u k),
      projectionEuclideanVector (P.selectedFacePoint hi hw hu hjl hridge i)⟫_ℝ=
      faceDot (u k) (P.selectedFacePoint hi hw hu hjl hridge i) :=
    (faceDot_eq_euclidean_inner _ _).symm
  rw [he]

theorem ActualRidgeFacetPresentation.selectedActualFace_supporting_indices {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    j∈(P.selectedActualFace hi hw hu hjl hridge i).1 ∧
      l∈(P.selectedActualFace hi hw hu hjl hridge i).1 ∧
      P.index i∈(P.selectedActualFace hi hw hu hjl hridge i).1 := by
  have hs := P.selectedFacePoint_spec hi hw hu hjl hridge i
  simp only [P.selectedActualFace_mem_iff hi hw hu hjl hridge i]
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1⟩

theorem ActualRidgeFacetPresentation.selectedActualFace_injective {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) :
    Function.Injective (P.selectedActualFace hi hw hu hjl hridge) := by
  intro i k he
  by_contra hne
  have hm := (P.selectedActualFace_supporting_indices hi hw hu hjl hridge k).2.2
  rw [←he,P.selectedActualFace_mem_iff hi hw hu hjl hridge i] at hm
  have hs := (P.selectedFacePoint_spec hi hw hu hjl hridge i).2.2.2.2.1 k (fun h => hne h.symm)
  exact (ne_of_lt hs) hm

theorem ActualRidgeFacetPresentation.selectedActualFace_triple_span {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    Submodule.span ℝ (range (fun p : Fin 3 => projectionEuclideanVector (u ((![j,l,P.index i] : Fin 3 → Fin m) p)) ))=
      nonsimpleFaceNormalSpace (fun k => projectionEuclideanVector (u k))
        (P.selectedActualFace hi hw hu hjl hridge i).1 := by
  have hki : P.index i≠j := (Finset.mem_erase.mp (Finset.mem_erase.mp (P.retained i)).2).1
  have hkl : P.index i≠l := (Finset.mem_erase.mp (P.retained i)).1
  have hF : Function.Injective (![j,l,P.index i] : Fin 3 → Fin m) := by
    intro p q he
    fin_cases p <;> fin_cases q <;> first
      | rfl
      | exact False.elim (hjl he)
      | exact False.elim (hjl he.symm)
      | exact False.elim (hki he)
      | exact False.elim (hki he.symm)
      | exact False.elim (hkl he)
      | exact False.elim (hkl he.symm)
  have hm := P.selectedActualFace_supporting_indices hi hw hu hjl hridge i
  apply nonsimple_codimThree_triple_spans u b hi hw hu _ _ hF
  intro p
  fin_cases p
  · exact hm.1
  · exact hm.2.1
  · exact hm.2.2

theorem ActualRidgeFacetPresentation.selectedActualFace_closedFace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count) :
    nonsimpleClosedFace (fun k => projectionEuclideanVector (u k)) b
      (P.selectedActualFace hi hw hu hjl hridge i).1=
      {x | x∈polyhedron (fun k => projectionEuclideanVector (u k)) b ∧
        ∀ p : Fin 3,⟪projectionEuclideanVector (u ((![j,l,P.index i] : Fin 3 → Fin m) p)),x⟫_ℝ=
          b ((![j,l,P.index i] : Fin 3 → Fin m) p)} := by
  have hm := P.selectedActualFace_supporting_indices hi hw hu hjl hridge i
  apply nonsimpleClosedFace_eq_spanning_levels _ b _ (![j,l,P.index i] : Fin 3 → Fin m)
  · intro p
    fin_cases p
    · exact hm.1
    · exact hm.2.1
    · exact hm.2.2
  · exact P.selectedActualFace_triple_span hi hw hu hjl hridge i

end
end RectangleCLTArxivV1
