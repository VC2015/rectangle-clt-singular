import RectangleCLTArxivV1.SupplementalHActualFacetSelection

/-! Pointwise Gaussian radial Green for an exact irredundant finite
halfspace presentation. Normals need not be unit vectors. In particular,
duplicate normalized constraints at a tied threshold are deleted before
coordinate differentiation; the original hard event is preserved exactly.
No generic-threshold or limiting argument is used. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Strict interior and actual deletion witnesses rule out every parallel
coincident pair in the finite presentation. This is a first-order condition
on its actual facets, with no triple independence requirement. -/
theorem actualFacet_localFiniteThresholdRegularity {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) :
    LocalFiniteThresholdRegularity Finset.univ u b := by
  have hnonzero (j : Fin m) : u j ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hinterior
    obtain ⟨y, _, hy⟩ := hwitness j
    have hj := hx j
    simp only [hz, faceDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hj hy
    exact (not_lt_of_ge hj.le) hy
  intro j _
  refine ⟨Or.inl (hnonzero j), ?_⟩
  intro l hl
  have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
  let σ := localFiniteThresholdScale u j
  let D := localFiniteThresholdDirection u j
  let c := faceDot (u l) D * σ⁻¹
  by_cases hz : gaussianNormalProjection D (u l) = 0
  · right
    intro hb
    have hnormal : u l = c • u j := by
      have h := sub_eq_zero.mp hz
      change u l = faceDot (u l) D • (σ⁻¹ • u j) at h
      simpa only [smul_smul] using h
    apply actualFacet_pair_affine_inconsistent u b hinterior hwitness j l hlj c hnormal
    change b l - (b j / σ) * faceDot (u l) D = 0 at hb
    dsimp only [c]
    rw [div_eq_mul_inv] at hb
    linear_combination hb
  · exact Or.inl hz

/-- The actual radial Gaussian trace is the finite threshold-gradient
pairing of an irredundant full-dimensional presentation, at this threshold. -/
theorem gaussianFiniteThreshold_radialTrace_of_actualFacets {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) :
    (∫ g, (gaussianFiniteThresholdEvent Finset.univ u b).indicator
      (fun g => vectorNormSq g - ((n+1 : ℕ) : ℝ)) g ∂standardGaussian (n+1)) =
      -(∑ j, b j * gaussianFiniteThresholdFirst Finset.univ u b j) := by
  simpa using gaussianFiniteThreshold_radialTrace_retained_of_slack
    Finset.univ u b (actualFacet_localFiniteThresholdRegularity u b hinterior hwitness)

/-- Select actual inequalities of the same polyhedron and apply the
pointwise radial Green identity to that exact presentation. Tied duplicate
inequalities contribute one selected facet, rather than undefined partials
of the unmerged threshold CDF. -/
theorem exists_actual_facet_radial_green {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) :
    ∃ (q : ℕ) (e : Fin q → Fin m), q ≤ m ∧ Function.Injective e ∧
      (∀ x : Vector (n+1),
        (∀ i, faceDot (u (e i)) x ≤ b (e i)) ↔ ∀ k, faceDot (u k) x ≤ b k) ∧
      HasStrictFacetInterior (fun i => u (e i)) (fun i => b (e i)) ∧
      HasIrredundantFacetWitnesses (fun i => u (e i)) (fun i => b (e i)) ∧
      (∫ g, (gaussianFiniteThresholdEvent Finset.univ u b).indicator
        (fun g => vectorNormSq g - ((n+1 : ℕ) : ℝ)) g ∂standardGaussian (n+1)) =
        -(∑ i, b (e i) * gaussianFiniteThresholdFirst Finset.univ
          (fun k => u (e k)) (fun k => b (e k)) i) := by
  obtain ⟨q, e, hq, he, hpoly, hint, hw⟩ := exists_actual_facet_presentation u b hinterior
  refine ⟨q, e, hq, he, hpoly, hint, hw, ?_⟩
  have hevent : gaussianFiniteThresholdEvent Finset.univ
      (fun k => u (e k)) (fun k => b (e k)) =
        gaussianFiniteThresholdEvent Finset.univ u b := by
    ext g
    simpa only [gaussianFiniteThresholdEvent, Set.mem_setOf_eq, Finset.mem_univ,
      forall_const] using hpoly g
  rw [← hevent]
  exact gaussianFiniteThreshold_radialTrace_of_actualFacets _ _ hint hw

end
end RectangleCLTArxivV1
