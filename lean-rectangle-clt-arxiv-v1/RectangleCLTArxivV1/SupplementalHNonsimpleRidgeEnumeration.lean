import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCofaces
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNative
import RectangleCLTArxivV1.SupplementalHNonsimpleGreenSum

/-! The exact two-to-one passage from ordered facet pairs to actual
ridges. No ordered-triple multiplicity is used at nonsimple faces. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

theorem strictRidgeInterior_iff_actual_ridge_face {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ t,vectorNormSq (u t)=1) (j k : Fin m) (hjk : j ≠ k) :
    HasStrictRidgeInterior u b j k ↔
      ∃ R : NonsimpleFaceIndex (fun t => projectionEuclideanVector (u t)) b 2,
        R.1 = {j,k} := by
  classical
  constructor
  · rintro ⟨x,hxj,hxk,hstrict⟩
    let z := projectionEuclideanVector x
    have he (t : Fin m) : ⟪projectionEuclideanVector (u t),z⟫_ℝ=faceDot (u t) x := by
      exact (faceDot_eq_euclidean_inner _ _).symm
    have hz : z ∈ exactStratum (fun t => projectionEuclideanVector (u t)) b {j,k} := by
      constructor
      · intro t
        rw [he]
        by_cases htj : t=j
        · simpa [htj] using hxj.le
        · by_cases htk : t=k
          · simpa [htk] using hxk.le
          · exact (hstrict t htj htk).le
      · intro t
        rw [he]
        simp only [Finset.mem_insert,Finset.mem_singleton]
        constructor
        · intro ht
          by_cases htj : t=j
          · exact Or.inl htj
          · by_cases htk : t=k
            · exact Or.inr htk
            · exact False.elim ((ne_of_lt (hstrict t htj htk)) ht)
        · rintro (rfl | rfl)
          · exact hxj
          · exact hxk
    have hlin : LinearIndependent ℝ ![projectionEuclideanVector (u j),projectionEuclideanVector (u k)] := by
      let L := (WithLp.linearEquiv 2 ℝ (Vector r)).symm
      have h := (nonsimple_active_pair_linearIndependent u b hi hw hu j k hjk x hxj hxk).map'
        L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
      exact h
    exact ⟨⟨{j,k},⟨z,hz⟩,nonsimple_pair_normalSpace_rank _ j k hlin⟩,rfl⟩
  · rintro ⟨R,hR⟩
    let z := nonsimpleFaceRepresentative (fun t => projectionEuclideanVector (u t)) b R
    let x := WithLp.equiv 2 (Vector r) z
    have he (t : Fin m) : faceDot (u t) x=⟪projectionEuclideanVector (u t),z⟫_ℝ := by
      rw [faceDot_eq_euclidean_inner]
      rfl
    refine ⟨x,?_,?_,?_⟩
    · rw [he]
      exact nonsimpleFaceRepresentative_levels _ b R j (by simp [hR])
    · rw [he]
      exact nonsimpleFaceRepresentative_levels _ b R k (by simp [hR])
    · intro t htj htk
      rw [he]
      exact nonsimpleFaceRepresentative_strict _ b R t (by simp [hR,htj,htk])

/-- A scalar coefficient associated to an actual ridge may be summed
over the ordered original facet pairs with exactly the factor one half.
The two pointwise hypotheses are for instantiating an already proved
coefficient, rather than assumptions of a surface or Green formula. -/
theorem half_native_pair_sum_eq_actual_ridge_sum {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ t,vectorNormSq (u t)=1)
    (B : Fin m → Fin m → ℝ)
    (c : NonsimpleFaceIndex (fun t => projectionEuclideanVector (u t)) b 2 → ℝ)
    (hzero : ∀ j k, ¬(j ≠ k ∧ HasStrictRidgeInterior u b j k) → B j k=0)
    (hvalue : ∀ R j k, j ≠ k → R.1={j,k} → B j k=c R) :
    (1/2 : ℝ) * (∑ p : Fin m × Fin m, B p.1 p.2) = ∑ R,c R := by
  classical
  have hp (p : Fin m × Fin m) : B p.1 p.2 =
      ∑ R : NonsimpleFaceIndex (fun t => projectionEuclideanVector (u t)) b 2,
        if p ∈ nonsimpleOrderedFacetPairs R.1 then c R else 0 := by
    by_cases h : p.1 ≠ p.2 ∧ HasStrictRidgeInterior u b p.1 p.2
    · obtain ⟨R,hR⟩ := (strictRidgeInterior_iff_actual_ridge_face u b hi hw hu p.1 p.2 h.1).mp h.2
      rw [hvalue R p.1 p.2 h.1 hR]
      symm
      calc
        _ = (if p ∈ nonsimpleOrderedFacetPairs R.1 then c R else 0) := by
          apply Finset.sum_eq_single R
          · intro S _ hSR
            have hn : p ∉ nonsimpleOrderedFacetPairs S.1 := by
              intro hm
              have hset := (Finset.mem_filter.mp hm).2.2
              apply hSR
              exact Subtype.ext (hset.symm.trans hR.symm)
            simp only [hn,if_false]
          · simp
        _ = c R := by simp [nonsimpleOrderedFacetPairs,h.1,hR]
    · rw [hzero p.1 p.2 h]
      symm
      apply Finset.sum_eq_zero
      intro R _
      have hn : p ∉ nonsimpleOrderedFacetPairs R.1 := by
        intro hm
        obtain ⟨hne,hset⟩ := (Finset.mem_filter.mp hm).2
        apply h
        exact ⟨hne,(strictRidgeInterior_iff_actual_ridge_face u b hi hw hu p.1 p.2 hne).mpr
          ⟨R,hset.symm⟩⟩
      simp only [hn,if_false]
  simp_rw [hp]
  exact half_ordered_pair_sum_eq_actual_ridge_sum _ (nonsimple_ridge_card_eq_two u b hi hw hu) c

end
end RectangleCLTArxivV1
