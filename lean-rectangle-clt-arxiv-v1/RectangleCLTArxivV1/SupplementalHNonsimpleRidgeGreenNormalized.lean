import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenPair
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenBoundary

/-! Actual pointwise ridge Green with signed support distances and unit
outward conormal Gaussian masses. Its selected tangent facets are genuine
facets of the residual polyhedron, including at nonsimple thresholds. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- An arbitrary exact actual-facet presentation may be used, so the
analytic formula is independent of the finite geometric selector used by
the actual-face incidence construction. All premises are geometric data. -/
theorem hardGaussianPairSection_Green_of_actual_presentation {m q n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (hef : faceDot e f = 0) (a c W : ℝ) (ι : Fin q → Fin m)
    (hpoly : ∀ x : Vector (n+1),
      (∀ i, faceDot (hardPairResidualNormals u e f (ι i)) x ≤
        hardPairResidualLevels u b e f a c (ι i)) ↔
      ∀ k ∈ s, faceDot (hardPairResidualNormals u e f k) x ≤
        hardPairResidualLevels u b e f a c k)
    (hstrict : HasStrictFacetInterior (fun i => hardPairResidualNormals u e f (ι i))
      (fun i => hardPairResidualLevels u b e f a c (ι i)))
    (hw : HasIrredundantFacetWitnesses (fun i => hardPairResidualNormals u e f (ι i))
      (fun i => hardPairResidualLevels u b e f a c (ι i))) :
    W * hardGaussianPairSignedSection s u b e f a c =
      (a^2+c^2-2) * (W * hardGaussianPairSectionProbability s u b e f a c) -
      ∑ i, actualFacetSignedSupportDistance
        (fun k => hardPairResidualNormals u e f (ι k))
        (fun k => hardPairResidualLevels u b e f a c (ι k)) i *
        (W * actualFacetGaussianBoundaryMass
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i) := by
  have hevent := selected_retained_threshold_event_eq s (hardPairResidualNormals u e f)
    (hardPairResidualLevels u b e f a c) ι hpoly
  have htrace : gaussianFiniteThresholdRadialTrace s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) =
      -(∑ i, actualFacetSignedSupportDistance
        (fun k => hardPairResidualNormals u e f (ι k))
        (fun k => hardPairResidualLevels u b e f a c (ι k)) i *
        actualFacetGaussianBoundaryMass
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i) := by
    unfold gaussianFiniteThresholdRadialTrace
    rw [← hevent]
    exact gaussianFiniteThreshold_radialTrace_eq_actualBoundary _ _ hstrict hw
  rw [hardGaussianPairSignedSection_eq_residual_trace s u b e f he hf hef a c,
    htrace, mul_add, mul_neg, Finset.mul_sum]
  simp only [sub_eq_add_neg]
  congr 1
  · ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem exists_hardGaussianPairSection_Green_normalized {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (hef : faceDot e f = 0) (a c W : ℝ)
    (hint : HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    ∃ (q : ℕ) (ι : Fin q → Fin m), q ≤ m ∧ Function.Injective ι ∧
      (∀ i, ι i ∈ s) ∧
      (∀ x : Vector (n+1),
        (∀ i, faceDot (hardPairResidualNormals u e f (ι i)) x ≤
          hardPairResidualLevels u b e f a c (ι i)) ↔
        ∀ k ∈ s, faceDot (hardPairResidualNormals u e f k) x ≤
          hardPairResidualLevels u b e f a c k) ∧
      HasStrictFacetInterior (fun i => hardPairResidualNormals u e f (ι i))
        (fun i => hardPairResidualLevels u b e f a c (ι i)) ∧
      HasIrredundantFacetWitnesses (fun i => hardPairResidualNormals u e f (ι i))
        (fun i => hardPairResidualLevels u b e f a c (ι i)) ∧
      W * hardGaussianPairSignedSection s u b e f a c =
        (a^2+c^2-2) * (W * hardGaussianPairSectionProbability s u b e f a c) -
        ∑ i, actualFacetSignedSupportDistance
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i *
          (W * actualFacetGaussianBoundaryMass
            (fun k => hardPairResidualNormals u e f (ι k))
            (fun k => hardPairResidualLevels u b e f a c (ι k)) i) := by
  obtain ⟨q, ι, hq, hi, hmem, hpoly, hstrict, hw, hgreen⟩ :=
    exists_hardGaussianPairSection_Green_actualFacets s u b e f he hf hef a c hint
  refine ⟨q, ι, hq, hi, hmem, hpoly, hstrict, hw, ?_⟩
  rw [hgreen, mul_sub, Finset.mul_sum]
  have hterm (i : Fin q) : W *
      (hardPairResidualLevels u b e f a c (ι i) *
        gaussianFiniteThresholdFirst Finset.univ
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i) =
      actualFacetSignedSupportDistance
        (fun k => hardPairResidualNormals u e f (ι k))
        (fun k => hardPairResidualLevels u b e f a c (ι k)) i *
        (W * actualFacetGaussianBoundaryMass
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i) := by
    rw [actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass
      _ _ hstrict hw i]
    ring
  simp_rw [hterm]
  ring

end
end RectangleCLTArxivV1
