import RectangleCLTArxivV1.SupplementalHActualFacetSelection
import RectangleCLTArxivV1.SupplementalHPairSectionTrace

/-! Exact actual facets for a retained finite family. Inequalities outside
the retained family are padded by the harmless strict inequality `0 < 1`;
minimality then proves that none can be selected. This construction deletes
duplicate supporting inequalities rather than counting their labels. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def HasStrictRetainedInterior {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∃ x : Vector r, ∀ k ∈ s, faceDot (u k) x < b k

theorem exists_actual_retained_facet_presentation {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hint : HasStrictRetainedInterior s u b) :
    ∃ (q : ℕ) (e : Fin q → Fin m), q ≤ m ∧ Function.Injective e ∧
      (∀ i, e i ∈ s) ∧
      (∀ x : Vector r, (∀ i, faceDot (u (e i)) x ≤ b (e i)) ↔
        ∀ k ∈ s, faceDot (u k) x ≤ b k) ∧
      HasStrictFacetInterior (fun i => u (e i)) (fun i => b (e i)) ∧
      HasIrredundantFacetWitnesses (fun i => u (e i)) (fun i => b (e i)) := by
  classical
  let v : Fin m → Vector r := fun k => if k ∈ s then u k else 0
  let d : Vector m := fun k => if k ∈ s then b k else 1
  have hv : HasStrictFacetInterior v d := by
    obtain ⟨x, hx⟩ := hint
    refine ⟨x, ?_⟩
    intro k
    by_cases hk : k ∈ s
    · simpa only [v, d, if_pos hk] using hx k hk
    · simp [v, d, hk, faceDot]
  obtain ⟨q, e, hq, he, hequiv, hstrict, hw⟩ := exists_actual_facet_presentation v d hv
  have hmem (i : Fin q) : e i ∈ s := by
    by_contra hn
    obtain ⟨x, _, hx⟩ := hw i
    have hbad : (1 : ℝ) < 0 := by simpa [v, d, hn, faceDot] using hx
    linarith
  have hve : (fun i => v (e i)) = (fun i => u (e i)) := by
    funext i
    simp only [v, if_pos (hmem i)]
  have hde : (fun i => d (e i)) = (fun i => b (e i)) := by
    funext i
    simp only [d, if_pos (hmem i)]
  refine ⟨q, e, hq, he, hmem, ?_, ?_, ?_⟩
  · intro x
    have hpad : (∀ k, faceDot (v k) x ≤ d k) ↔ ∀ k ∈ s, faceDot (u k) x ≤ b k := by
      constructor
      · intro hx k hk
        simpa only [v, d, if_pos hk] using hx k
      · intro hx k
        by_cases hk : k ∈ s
        · simpa only [v, d, if_pos hk] using hx k hk
        · simp [v, d, hk, faceDot]
    simpa only [v, d, hmem, if_true] using (hequiv x).trans hpad
  · simpa only [hve, hde] using hstrict
  · simpa only [hve, hde] using hw

theorem selected_retained_threshold_event_eq {m q r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e : Fin q → Fin m)
    (hequiv : ∀ x : Vector r, (∀ i, faceDot (u (e i)) x ≤ b (e i)) ↔
      ∀ k ∈ s, faceDot (u k) x ≤ b k) :
    gaussianFiniteThresholdEvent Finset.univ (fun i => u (e i)) (fun i => b (e i)) =
      gaussianFiniteThresholdEvent s u b := by
  ext x
  simpa only [gaussianFiniteThresholdEvent, mem_setOf_eq, Finset.mem_univ,
    forall_const] using hequiv x

theorem hardPairResidual_strictInterior_of_section_witness {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (hef : faceDot e f = 0)
    (hw : ∃ g : Vector r, ∀ k ∈ s,
      faceDot (u k) (gaussianPairSectionPoint e f a c g) < b k) :
    HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) := by
  obtain ⟨g, hg⟩ := hw
  refine ⟨g, ?_⟩
  intro k hk
  have h := hg k hk
  rw [gaussianPairSectionPoint_faceDot_residual e f (u k) a c g hef] at h
  change faceDot (hardPairResidualNormal e f (u k)) g <
    b k - a * faceDot (u k) e - c * faceDot (u k) f
  linarith

end
end RectangleCLTArxivV1
