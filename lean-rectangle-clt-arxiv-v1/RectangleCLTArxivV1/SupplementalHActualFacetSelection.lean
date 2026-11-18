import RectangleCLTArxivV1.SupplementalHActualFacetRegularity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max

/-! Actual deletion of redundant inequalities, preserving exactly the
polyhedron and constructing every irredundancy witness. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def FacetPresentationEquivalent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (s : Finset (Fin m)) : Prop :=
  ∀ x : Vector r,(∀ k∈s,faceDot (u k) x≤b k) ↔ ∀ k,faceDot (u k) x≤b k

theorem exists_irredundant_facet_subfamily {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) :
    ∃ s : Finset (Fin m),FacetPresentationEquivalent u b s ∧
      ∀ j∈s,∃ x : Vector r,(∀ k∈s.erase j,faceDot (u k) x≤b k) ∧ b j<faceDot (u j) x := by
  classical
  let candidates : Finset (Finset (Fin m)) := Finset.univ.filter (FacetPresentationEquivalent u b)
  have hall : FacetPresentationEquivalent u b Finset.univ := by
    intro x
    simp
  have hnon : candidates.Nonempty := ⟨Finset.univ,by simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]; exact hall⟩
  obtain ⟨s,hs,hmin⟩ := candidates.exists_min_image Finset.card hnon
  have hseq : FacetPresentationEquivalent u b s := (Finset.mem_filter.mp hs).2
  refine ⟨s,hseq,?_⟩
  intro j hj
  by_contra hw
  have herase : FacetPresentationEquivalent u b (s.erase j) := by
    intro x
    constructor
    · intro hx
      apply (hseq x).mp
      intro k hk
      by_cases hkj : k=j
      · subst k
        by_contra hviol
        exact hw ⟨x,hx,lt_of_not_ge hviol⟩
      · exact hx k (Finset.mem_erase.mpr ⟨hkj,hk⟩)
    · intro hx k _
      exact hx k
  have hc : s.erase j∈candidates := by simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]; exact herase
  exact (not_lt_of_ge (hmin _ hc)) (Finset.card_erase_lt_of_mem hj)

/-- A genuine selected finite presentation of the same polyhedron. The
deleted-inequality witnesses are constructed by finite minimality. -/
theorem exists_actual_facet_presentation {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) :
    ∃ (q : ℕ) (e : Fin q → Fin m),q≤m ∧ Function.Injective e ∧
      (∀ x : Vector r,(∀ i,faceDot (u (e i)) x≤b (e i)) ↔ ∀ k,faceDot (u k) x≤b k) ∧
      HasStrictFacetInterior (fun i => u (e i)) (fun i => b (e i)) ∧
      HasIrredundantFacetWitnesses (fun i => u (e i)) (fun i => b (e i)) := by
  classical
  obtain ⟨s,hs,hw⟩ := exists_irredundant_facet_subfamily u b
  let q := Fintype.card s
  let E : s ≃ Fin q := Fintype.equivFin s
  let e : Fin q → Fin m := fun i => (E.symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp E.symm.injective
  refine ⟨q,e,?_,he,?_,?_,?_⟩
  · have h := Fintype.card_le_of_injective e he
    simpa only [Fintype.card_fin] using h
  · intro x
    constructor
    · intro hx
      apply (hs x).mp
      intro k hk
      simpa only [e,Equiv.symm_apply_apply] using hx (E ⟨k,hk⟩)
    · intro hx i
      exact hx (e i)
  · obtain ⟨x,hx⟩ := hinterior
    exact ⟨x,fun i => hx (e i)⟩
  · intro i
    obtain ⟨x,hx,hxi⟩ := hw (e i) (E.symm i).property
    refine ⟨x,?_,hxi⟩
    intro k hki
    apply hx (e k)
    exact Finset.mem_erase.mpr ⟨he.ne hki,(E.symm k).property⟩

/-- Every full-dimensional finite signed-normal polyhedron has an exact
actual-facet presentation satisfying the pointwise genuine J_f bound. -/
theorem exists_actual_facet_weightedIntegral_bound {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hinterior : HasStrictFacetInterior (fun k => U (f k)) b) :
    ∃ (q : ℕ) (e : Fin q → Fin m),q≤m ∧ Function.Injective e ∧
      (∀ x : Vector (n+1),(∀ i,faceDot (U (f (e i))) x≤b (e i)) ↔
        ∀ k,faceDot (U (f k)) x≤b k) ∧
      |hardGaussianWeightedFacetIntegral (fun i => U (f (e i))) (fun i => b (e i))|≤
        (16384*Real.exp ((3:ℝ)/2))*(∫ g,
          (fourthOuterLayer (fun i => U (f (e i))) (fun i => b (e i)) (fourthThreeFaceRadius U)).indicator
            (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  obtain ⟨q,e,hq,he,hpoly,hint,hw⟩ := exists_actual_facet_presentation (fun k => U (f k)) b hinterior
  exact ⟨q,e,hq,he,hpoly,actualFacet_abs_weightedFacetIntegral_le_threeFace_tube hp U (fun i => f (e i))
    (fun i => b (e i)) (fun i => hu (e i)) hint hw⟩

end
end RectangleCLTArxivV1
