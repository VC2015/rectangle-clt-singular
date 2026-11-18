import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelected

/-! A genuine retained supporting inequality cannot be active at a
strict interior point of an equivalent selected presentation. Applied
to an incident actual face, this constructs a selected tangent facet. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem nonsimple_retained_active_has_selected_active {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {m q : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (s : Finset (Fin m))
    (v : Fin q → E) (c : Fin q → ℝ)
    (hpoly : ∀ x,(∀ i,⟪v i,x⟫_ℝ≤c i) ↔ ∀ k∈s,⟪u k,x⟫_ℝ≤b k)
    (hiv : ∃ z : E,∀ i,⟪v i,z⟫_ℝ<c i) (x : E) (hx : ∀ i,⟪v i,x⟫_ℝ≤c i)
    (k : Fin m) (hks : k∈s) (hk : ⟪u k,x⟫_ℝ=b k) (hkn : u k≠0) :
    ∃ i,⟪v i,x⟫_ℝ=c i := by
  classical
  by_contra hn
  have hstr : x∈exactStratum v c ∅ := by
    refine ⟨hx,fun i => ?_⟩
    simp only [Finset.not_mem_empty,iff_false]
    exact fun he => hn ⟨i,he⟩
  have hout : IsOutwardNormal (polyhedron v c) x (u k) := by
    intro y hy
    rw [inner_sub_right,hk]
    exact sub_nonpos.mpr (((hpoly y).mp hy) k hks)
  have hcone := (nonsimple_isOutwardNormal_iff_activeGeneratedCone v c ∅ hiv hstr (u k)).mp hout
  obtain ⟨a,_,he⟩ := (nonsimpleActiveGeneratedCone_mem_iff v ∅ (u k)).mp hcone
  exact hkn (by simpa only [Finset.sum_empty] using he)

theorem ActualRidgeFacetPresentation.incident_face_has_selected_active {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k,vectorNormSq (u k)=1) (hjl : j≠l)
    (H : NonsimpleFaceIndex (fun k => projectionEuclideanVector (u k)) b 3)
    (hjH : j∈H.1) (hlH : l∈H.1) : ∃ i : Fin P.count,P.index i∈H.1 := by
  classical
  let z := nonsimpleFaceRepresentative (fun k => projectionEuclideanVector (u k)) b H
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have hinnerProj (v w : Vector r) :
      ⟪projectionEuclideanVector v,projectionEuclideanVector w⟫_ℝ=faceDot v w :=
    (faceDot_eq_euclidean_inner v w).symm
  have hz : projectionEuclideanVector x=z := by rfl
  have hlevel (k : Fin m) (hk : k∈H.1) : faceDot (u k) x=b k := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceRepresentative_levels _ b H k hk
  have hx (k : Fin m) : faceDot (u k) x≤b k := by
    rw [faceDot_eq_euclidean_inner]
    exact (nonsimpleFaceRepresentative_mem _ b H).1 k
  have hp := actualFacet_pair_support_nonparallel u b hi hw j l hjl x (hlevel j hjH) (hlevel l hlH)
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let d := thresholdPairSecondLevel u b j l
  let V := hardPairResidualNormals u e f
  let B := hardPairResidualLevels u b e f a d
  let s := (Finset.univ.erase j).erase l
  have hef : faceDot e f=0 := thresholdPair_frame_orthogonal u j l (hu j) (hu l)
  obtain ⟨hxe,hxf⟩ := thresholdPair_frame_levels_of_support u b j l x hp.1 hp.2 (hlevel j hjH) (hlevel l hlH)
  have hdot (k : Fin m) : faceDot (V k) x-B k=faceDot (u k) x-b k := by
    dsimp only [V,B,hardPairResidualNormals,hardPairResidualLevels]
    rw [hardPairResidualNormal_eq_sub e f (u k) hef,threshold_faceDot_sub_left,
      threshold_faceDot_sub_left,threshold_faceDot_smul_left,threshold_faceDot_smul_left,hxe,hxf]
    ring
  have hcard := nonsimpleFaceNormalSpace_finrank_le_card (fun k => projectionEuclideanVector (u k)) H.1
  rw [H.2.2] at hcard
  have hnot : ¬H.1⊆({j,l} : Finset (Fin m)) := by
    intro hs
    have h := (Finset.card_le_card hs).trans (Finset.card_le_two (a := j) (b := l))
    omega
  obtain ⟨k,hkH,hk⟩ := Finset.not_subset.mp hnot
  have hkj : k≠j := by intro he; subst k; simp at hk
  have hkl : k≠l := by intro he; subst k; simp at hk
  have hks : k∈s := Finset.mem_erase.mpr ⟨hkl,Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ _⟩⟩
  have hractive : faceDot (V k) x=B k := by linarith [hdot k,hlevel k hkH]
  have hrne : V k≠0 := by
    intro he
    have hor := actualFacet_pairResidual_nonzero_or_level u b hi hw hu j l hjl k hks
    rcases hor with hn|hn
    · exact hn he
    · apply hn
      change B k=0
      rw [←hractive,he]
      simp [faceDot]
  have hpoly (y : EuclideanSpace ℝ (Fin r)) :
      (∀ i,⟪projectionEuclideanVector (P.normals i),y⟫_ℝ≤P.levels i) ↔
        ∀ k∈s,⟪projectionEuclideanVector (V k),y⟫_ℝ≤B k := by
    have heq (v : Vector r) : ⟪projectionEuclideanVector v,y⟫_ℝ=
        faceDot v (WithLp.equiv 2 (Vector r) y) := by rw [faceDot_eq_euclidean_inner]; rfl
    simp_rw [heq]
    exact P.event_iff _
  have hiv : ∃ y : EuclideanSpace ℝ (Fin r),∀ i,⟪projectionEuclideanVector (P.normals i),y⟫_ℝ<P.levels i := by
    obtain ⟨g,hg⟩ := P.strict
    refine ⟨projectionEuclideanVector g,?_⟩
    intro i
    rw [hinnerProj]
    exact hg i
  have hsel (i : Fin P.count) : ⟪projectionEuclideanVector (P.normals i),projectionEuclideanVector x⟫_ℝ≤P.levels i := by
    rw [hinnerProj]
    change faceDot (V (P.index i)) x≤B (P.index i)
    linarith [hdot (P.index i),hx (P.index i)]
  obtain ⟨i,hi⟩ := nonsimple_retained_active_has_selected_active
    (fun k => projectionEuclideanVector (V k)) B s (fun i => projectionEuclideanVector (P.normals i)) P.levels
    hpoly hiv (projectionEuclideanVector x) hsel k hks (by rw [hinnerProj]; exact hractive)
    (by intro he; apply hrne; exact (WithLp.equiv 2 (Vector r)).symm.injective he)
  have hselected : faceDot (V (P.index i)) x=B (P.index i) := by
    rw [hinnerProj] at hi
    exact hi
  have horig : faceDot (u (P.index i)) x=b (P.index i) := by linarith [hdot (P.index i)]
  refine ⟨i,?_⟩
  exact ((nonsimpleFaceRepresentative_mem _ b H).2 (P.index i)).mp
    (by
      change ⟪projectionEuclideanVector (u (P.index i)),z⟫_ℝ=b (P.index i)
      rw [←hz,hinnerProj]
      exact horig)

end
end RectangleCLTArxivV1
