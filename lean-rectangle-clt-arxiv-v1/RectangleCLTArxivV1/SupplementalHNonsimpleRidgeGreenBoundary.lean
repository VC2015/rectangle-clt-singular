import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenRadial

/-! The normalized outward conormal, signed support distance and genuine
Gaussian boundary mass of a selected actual finite halfspace presentation.
The coordinate derivative includes its inverse-normal-length Jacobian;
after multiplying by the threshold it is exactly distance times mass. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The normalized outward normal of the selected inequality. -/
def actualFacetOutwardConormal {m r : ℕ} (u : Fin m → Vector r) (j : Fin m) : Vector r :=
  localFiniteThresholdDirection u j

/-- The signed distance of its supporting plane from the origin. -/
def actualFacetSignedSupportDistance {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  b j / localFiniteThresholdScale u j

/-- Actual scalar Gaussian normal density times the probability of every
other retained inequality on the supporting hyperplane. -/
def actualFacetGaussianBoundaryMass {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  gaussianPDFReal 0 1 (actualFacetSignedSupportDistance u b j) *
    gaussianThresholdSectionProbability (Finset.univ.erase j) u b
      (actualFacetOutwardConormal u j) (actualFacetSignedSupportDistance u b j)

theorem actualFacet_normal_ne_zero {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (j : Fin m) : u j ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := hinterior
  obtain ⟨y, _, hy⟩ := hwitness j
  have hj := hx j
  simp only [hz, faceDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hj hy
  exact (not_lt_of_ge hj.le) hy

theorem actualFacet_scale_pos {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (j : Fin m) :
    0 < localFiniteThresholdScale u j :=
  Real.sqrt_pos.mpr (vectorNormSq_pos (actualFacet_normal_ne_zero u b hinterior hwitness j))

theorem actualFacetOutwardConormal_unit {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (j : Fin m) :
    vectorNormSq (actualFacetOutwardConormal u j) = 1 := by
  let σ := localFiniteThresholdScale u j
  have hσ : 0 < σ := actualFacet_scale_pos u b hinterior hwitness j
  have hnorm : vectorNormSq (u j) = σ ^ 2 :=
    (Real.sq_sqrt (vectorNormSq_nonneg (u j))).symm
  have hsmul (a : ℝ) (v : Vector r) : vectorNormSq (a • v) = a ^ 2 * vectorNormSq v := by
    simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  change vectorNormSq (σ⁻¹ • u j) = 1
  rw [hsmul, hnorm]
  field_simp

theorem actualFacetGaussianBoundaryMass_nonneg {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    0 ≤ actualFacetGaussianBoundaryMass u b j :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)

/-- Differentiating the actual selected threshold has the exact inverse
normal-length Jacobian. The mass itself uses unit-normal surface scale. -/
theorem actualFacet_finiteThresholdFirst_eq_boundaryMass_div {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (j : Fin m) :
    gaussianFiniteThresholdFirst Finset.univ u b j =
      actualFacetGaussianBoundaryMass u b j / localFiniteThresholdScale u j := by
  have hreg := actualFacet_localFiniteThresholdRegularity u b hinterior hwitness
  have hfirst := gaussianFiniteThresholdFirst_eq_section_of_slack Finset.univ u b j
    (Finset.mem_univ j) (actualFacet_scale_pos u b hinterior hwitness j)
    (Real.sq_sqrt (vectorNormSq_nonneg (u j))).symm
    (hreg j (Finset.mem_univ j)).2
  rw [hfirst]
  unfold actualFacetGaussianBoundaryMass actualFacetSignedSupportDistance actualFacetOutwardConormal
    localFiniteThresholdDirection
  ring

theorem actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (j : Fin m) :
    b j * gaussianFiniteThresholdFirst Finset.univ u b j =
      actualFacetSignedSupportDistance u b j * actualFacetGaussianBoundaryMass u b j := by
  rw [actualFacet_finiteThresholdFirst_eq_boundaryMass_div u b hinterior hwitness j]
  unfold actualFacetSignedSupportDistance
  ring

/-- Pointwise Gaussian radial Green in its geometric distance-times-mass
form, for arbitrary nonunit actual facets of this full-dimensional event. -/
theorem gaussianFiniteThreshold_radialTrace_eq_actualBoundary {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) :
    (∫ g, (gaussianFiniteThresholdEvent Finset.univ u b).indicator
      (fun g => vectorNormSq g - ((n+1 : ℕ) : ℝ)) g ∂standardGaussian (n+1)) =
      -(∑ j, actualFacetSignedSupportDistance u b j * actualFacetGaussianBoundaryMass u b j) := by
  rw [gaussianFiniteThreshold_radialTrace_of_actualFacets u b hinterior hwitness]
  congr 1
  exact Finset.sum_congr rfl (fun j _ =>
    actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass u b hinterior hwitness j)

end
end RectangleCLTArxivV1
