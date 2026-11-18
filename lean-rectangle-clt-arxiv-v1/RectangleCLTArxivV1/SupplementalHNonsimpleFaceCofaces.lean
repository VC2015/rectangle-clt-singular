import RectangleCLTArxivV1.SupplementalHNonsimpleFaceNormalCone
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceIndependence

/-! Genuine ridge incidences at a possibly nonsimple codimension-three
face. A supporting normal-cone facet supplies an inward movement in the
original polyhedron and constructs the actual ridge, rather than merely
an abstract pair of zero generators. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem nonsimple_exactStratum_move_to_active_subset {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (S T : Finset (Fin m)) (hTS : T⊆S)
    {x : E} (hx : x∈exactStratum u b S) (y : E)
    (hkeep : ∀ j∈T,⟪u j,y⟫_ℝ=0) (hdrop : ∀ j∈S,j∉T → ⟪u j,y⟫_ℝ<0) :
    ∃ t : ℝ,0<t ∧ x+t • y∈exactStratum u b T := by
  classical
  let c : Fin m → ℝ := fun j => if j∈S then b j else (b j+⟪u j,x⟫_ℝ)/2
  have hgap (j : Fin m) (hj : j∉S) : ⟪u j,x⟫_ℝ<b j :=
    lt_of_le_of_ne (hx.1 j) (fun he => hj ((hx.2 j).mp he))
  have hxc : x∈exactStratum u c S := by
    constructor
    · intro j
      by_cases hj : j∈S
      · simpa only [c,if_pos hj] using hx.1 j
      · simp only [c,if_neg hj]
        linarith [hgap j hj]
    · intro j
      by_cases hj : j∈S
      · simp only [hj,iff_true,c,if_pos hj]
        exact (hx.2 j).mpr hj
      · simp only [hj,iff_false,c,if_neg hj]
        have hg := hgap j hj
        linarith
  have hyle (j : Fin m) (hj : j∈S) : ⟪u j,y⟫_ℝ≤0 := by
    by_cases ht : j∈T
    · exact (hkeep j ht).le
    · exact (hdrop j hj ht).le
  obtain ⟨t,ht,hfeas⟩ := nonsimple_exactStratum_local_feasible_ray u c S hxc y hyle
  have hstrict (j : Fin m) (hj : j∉T) : ⟪u j,x+t • y⟫_ℝ<b j := by
    by_cases hjs : j∈S
    · rw [inner_add_right,inner_smul_right,(hx.2 j).mpr hjs]
      exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg ht (hdrop j hjs hj))
    · have hh := hfeas j
      simp only [c,if_neg hjs] at hh
      linarith [hgap j hjs]
  have heq (j : Fin m) (hj : j∈T) : ⟪u j,x+t • y⟫_ℝ=b j := by
    rw [inner_add_right,inner_smul_right,(hx.2 j).mpr (hTS hj),hkeep j hj,mul_zero,add_zero]
  refine ⟨t,ht,?_,?_⟩
  · intro j
    by_cases hj : j∈T
    · exact (heq j hj).le
    · exact (hstrict j hj).le
  · intro j
    constructor
    · intro hj
      by_contra hn
      exact (ne_of_lt (hstrict j hn)) hj
    · exact heq j

theorem nonsimple_supporting_pair_has_actual_stratum {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
    (n : EuclideanSpace ℝ (Fin r)) (hn : n≠0)
    (hnS : n∈nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1)
    (hpos : ∀ j∈H.1,0≤⟪n,projectionEuclideanVector (u j)⟫_ℝ)
    (a d : Fin m) (ha : a∈H.1) (hd : d∈H.1) (had : a≠d)
    (hna : ⟪n,projectionEuclideanVector (u a)⟫_ℝ=0)
    (hnd : ⟪n,projectionEuclideanVector (u d)⟫_ℝ=0) :
    (exactStratum (fun j => projectionEuclideanVector (u j)) b {a,d}).Nonempty := by
  classical
  let z := nonsimpleFaceRepresentative (fun j => projectionEuclideanVector (u j)) b H
  have hsub : ({a,d} : Finset (Fin m))⊆H.1 := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl
    · exact ha
    · exact hd
  have hkeep (j : Fin m) (hj : j∈({a,d} : Finset (Fin m))) :
      ⟪projectionEuclideanVector (u j),-n⟫_ℝ=0 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl <;> rw [inner_neg_right,real_inner_comm] <;> simp [hna,hnd]
  have hdrop (j : Fin m) (hj : j∈H.1) (hjt : j∉({a,d} : Finset (Fin m))) :
      ⟪projectionEuclideanVector (u j),-n⟫_ℝ<0 := by
    rw [inner_neg_right,real_inner_comm,neg_lt_zero]
    exact nonsimple_codimThree_supporting_pair_strict u b hi hw hu H n hn hnS hpos a d ha hd had hna hnd
      j hj (by intro h; subst j; simp at hjt) (by intro h; subst j; simp at hjt)
  obtain ⟨t,ht,hstr⟩ := nonsimple_exactStratum_move_to_active_subset _ b H.1 {a,d} hsub
    (nonsimpleFaceRepresentative_mem _ b H) (-n) hkeep hdrop
  exact ⟨z+t • (-n),hstr⟩

theorem nonsimple_pair_normalSpace_rank {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : Fin m → E) (a d : Fin m) (hli : LinearIndependent ℝ ![u a,u d]) :
    Module.finrank ℝ (nonsimpleFaceNormalSpace u {a,d})=2 := by
  classical
  have he : range ![u a,u d]=u '' ({a,d} : Set (Fin m)) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact ⟨a,by simp,rfl⟩
      · exact ⟨d,by simp,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simp only [mem_insert_iff,mem_singleton_iff] at hj
      rcases hj with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hh := finrank_span_eq_card hli
  rw [he,Fintype.card_fin] at hh
  change Module.finrank ℝ (Submodule.span ℝ (u '' (({a,d} : Finset (Fin m)) : Set (Fin m))))=2
  rw [Finset.coe_pair]
  exact hh

/-- Every pair-supported nonzero polar ray gives an actual original
ridge incident to H. The required ridge is constructed by a feasible
movement, including when H has more than three active facets. -/
theorem nonsimple_supporting_pair_has_actual_ridge {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
    (n : EuclideanSpace ℝ (Fin r)) (hn : n≠0)
    (hnS : n∈nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1)
    (hpos : ∀ j∈H.1,0≤⟪n,projectionEuclideanVector (u j)⟫_ℝ)
    (a d : Fin m) (ha : a∈H.1) (hd : d∈H.1) (had : a≠d)
    (hna : ⟪n,projectionEuclideanVector (u a)⟫_ℝ=0)
    (hnd : ⟪n,projectionEuclideanVector (u d)⟫_ℝ=0) :
    ∃ R : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 2,
      R.1={a,d} ∧ R.1⊆H.1 := by
  classical
  have hstr := nonsimple_supporting_pair_has_actual_stratum u b hi hw hu H n hn hnS hpos a d ha hd had hna hnd
  let z := nonsimpleFaceRepresentative (fun j => projectionEuclideanVector (u j)) b H
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have hlev (j : Fin m) (hj : j∈H.1) : faceDot (u j) x=b j := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceRepresentative_levels _ b H j hj
  have hp := nonsimple_active_pair_linearIndependent u b hi hw hu a d had x (hlev a ha) (hlev d hd)
  let L := (WithLp.linearEquiv 2 ℝ (Vector r)).symm
  have hpe : LinearIndependent ℝ ![projectionEuclideanVector (u a),projectionEuclideanVector (u d)] := by
    convert hp.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective) using 1
  refine ⟨⟨{a,d},hstr,nonsimple_pair_normalSpace_rank _ a d hpe⟩,rfl,?_⟩
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl
  · exact ha
  · exact hd

end
end RectangleCLTArxivV1
