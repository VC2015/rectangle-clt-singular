import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeEnumeration
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedQuantities
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenActual

/-! Assembly of the printed actual-face ridge formula. The finite
reduction below is private; the pointwise ridge identities are supplied
by the actual tangent-facet proofs when constructing the final theorem. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section

private theorem printedGreen_of_actual_ridge_values {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ t,vectorNormSq (u t)=1)
    (hvalue : ∀ (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
      (j k : Fin m), j ≠ k → R.1 = {j,k} →
      hardGaussianSignedRidgeTerm u b j k = nonsimpleActualRidgeLeading u b R -
        ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
          nonsimpleActualRidgeAngle u b R *
            (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
              nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H)) :
    hardGaussianWeightedRidgeIntegral u b =
      (∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
        nonsimpleActualRidgeLeading u b R) - nonsimpleActualThirdBoundary u b := by
  have hzero (j k : Fin m) (hnot : ¬(j ≠ k ∧ HasStrictRidgeInterior u b j k)) :
      hardGaussianSignedRidgeTerm u b j k = 0 := by
    by_cases hne : j ≠ k
    · exact (actualFacet_nativeRidgeTerms_zero_of_no_strictInterior u b hi hw hu j k
        (fun h => hnot ⟨hne,h⟩)).1
    · have he : j=k := not_ne_iff.mp hne
      subst k
      simp [hardGaussianSignedRidgeTerm,hardGaussianRidgeNonparallel]
  have hh := half_native_pair_sum_eq_actual_ridge_sum u b hi hw hu
    (hardGaussianSignedRidgeTerm u b)
    (fun R => nonsimpleActualRidgeLeading u b R -
      ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
        nonsimpleActualRidgeAngle u b R *
          (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
            nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H))
    hzero hvalue
  change hardGaussianWeightedRidgeIntegral u b = _ at hh
  rw [Finset.sum_sub_distrib] at hh
  rw [hh,nonsimpleActualThirdBoundary_eq_ridge_incidence_sum]
  rfl

/-- The printed pointwise ridge Gauss--Green identity for the actual
facets of an arbitrary full-dimensional polyhedron. Complete actual
codimension-three faces are counted once, with no simplicity, generic
threshold, derivative regularity, or limiting premise. -/
theorem hardGaussianWeightedRidgeIntegral_Green_actualFaces {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ t,vectorNormSq (u t)=1) :
    hardGaussianWeightedRidgeIntegral u b =
      (∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
        nonsimpleActualRidgeAngle u b R *
          (‖nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b R‖^2-2) *
            nonsimpleActualGaussianMass u b R) -
      ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
        ⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
          ∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
            nonsimpleActualRidgeAngle u b R • nonsimpleActualIncidenceConormal u b R H⟫_ℝ *
          nonsimpleActualGaussianMass u b H := by
  simpa only [nonsimpleActualRidgeLeading,nonsimpleActualThirdBoundary,nonsimpleActualConormalSum]
    using printedGreen_of_actual_ridge_values u b hi hw hu
      (fun R j k hjk hR => hardGaussianSignedRidgeTerm_Green_actualFace u b hi hw hu j k hjk R hR)

theorem hardGaussianWeightedRidgeIntegral_Green_actualFaces_compact {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ t,vectorNormSq (u t)=1) :
    hardGaussianWeightedRidgeIntegral u b =
      (∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
        nonsimpleActualRidgeLeading u b R) - nonsimpleActualThirdBoundary u b := by
  exact printedGreen_of_actual_ridge_values u b hi hw hu
    (fun R j k hjk hR => hardGaussianSignedRidgeTerm_Green_actualFace u b hi hw hu j k hjk R hR)

/-- An arbitrary original full-dimensional halfspace presentation may
first be reduced to actual facets. The chosen exact injective subsystem
then satisfies the pointwise identity, including at nonsimple faces. -/
theorem exists_actual_facet_ridge_Green {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hu : ∀ t,vectorNormSq (u t)=1) :
    ∃ (q : ℕ) (e : Fin q → Fin m), q ≤ m ∧ Function.Injective e ∧
      (∀ x : Vector (n+1),(∀ i,faceDot (u (e i)) x≤b (e i)) ↔ ∀ k,faceDot (u k) x≤b k) ∧
      HasStrictFacetInterior (fun i => u (e i)) (fun i => b (e i)) ∧
      HasIrredundantFacetWitnesses (fun i => u (e i)) (fun i => b (e i)) ∧
      hardGaussianWeightedRidgeIntegral (fun i => u (e i)) (fun i => b (e i)) =
        (∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals (fun i => u (e i))) (fun i => b (e i)) 2,
          nonsimpleActualRidgeLeading (fun i => u (e i)) (fun i => b (e i)) R) -
        nonsimpleActualThirdBoundary (fun i => u (e i)) (fun i => b (e i)) := by
  obtain ⟨q,e,hq,he,heq,hint,hirr⟩ := exists_actual_facet_presentation u b hi
  exact ⟨q,e,hq,he,heq,hint,hirr,
    hardGaussianWeightedRidgeIntegral_Green_actualFaces_compact _ _ hint hirr (fun i => hu (e i))⟩

end
end RectangleCLTArxivV1
