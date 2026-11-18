import RectangleCLTArxivV1.PositiveMixedCoareaTests

/-! Actual mixed coarea for the positive mass and pair-plane tests.
The selected pair is unit and nonparallel; all remaining normals may be
dependent. Every inactive hard inequality is retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

private theorem positiveMixed_updated_residual_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (z : ℝ) :
    (fun k => Function.update b l z k-b j*faceDot (u k) (u j))=
      Function.update (fun k => b k-b j*faceDot (u k) (u j)) l
        (z-b j*faceDot (u l) (u j)) := by
  classical
  funext k
  by_cases hk : k=l
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]

theorem positiveMixedFirstMassDensity_update_eq_weightedThreshold {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l) (z : ℝ) :
    positiveMixedFirstMassDensity u (Function.update b l z) j=
      gaussianPDFReal 0 1 (b j)*gaussianFiniteWeightedThreshold (Finset.univ.erase j)
        (fun k => gaussianNormalProjection (u j) (u k))
        (Function.update (fun k => b k-b j*faceDot (u k) (u j)) l
          (z-b j*faceDot (u l) (u j))) (fun _ => 1) := by
  simp only [positiveMixedFirstMassDensity,Function.update_of_ne hjl]
  rw [positiveMixed_updated_residual_levels]

theorem positiveMixedFirstPlaneDensity_update_eq_weightedThreshold {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l) (z : ℝ) :
    positiveMixedFirstPlaneDensity u (Function.update b l z) j l=
      gaussianPDFReal 0 1 (b j)*gaussianFiniteWeightedThreshold (Finset.univ.erase j)
        (fun k => gaussianNormalProjection (u j) (u k))
        (Function.update (fun k => b k-b j*faceDot (u k) (u j)) l
          (z-b j*faceDot (u l) (u j)))
        (positiveMixedPlaneFacetWeight (gaussianPairConditionalDirection u j l) (b j)) := by
  simp only [positiveMixedFirstPlaneDensity,Function.update_of_ne hjl]
  rw [positiveMixed_updated_residual_levels]

theorem hasDerivAt_positiveMixedFirstMassDensity_conditional {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => positiveMixedFirstMassDensity u (Function.update b l z) j)
      (gaussianPDFReal 0 1 (b j)*((gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
        gaussianThresholdResidualScale u j l)*hardGaussianPairSectionProbability
        ((Finset.univ.erase j).erase l) u b (u j) (gaussianPairConditionalDirection u j l)
        (b j) (gaussianPairConditionalLevel u b j l))) (b l) := by
  let s := Finset.univ.erase j
  let v := fun k => gaussianNormalProjection (u j) (u k)
  let d := fun k => b k-b j*faceDot (u k) (u j)
  let q := gaussianPairConditionalDirection u j l
  let ν := gaussianThresholdResidualScale u j l
  obtain ⟨hq,heq,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hl : l∈s := Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩
  have hul : v l=ν • q := by
    change v l=ν • (ν⁻¹ • v l)
    rw [smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  have hcont : ContinuousAt (gaussianFiniteWeightedSection (s.erase l) v d q (fun _ => 1)) (d l/ν) := by
    have hc := continuousAt_gaussianThresholdSectionProbability_of_slack (s.erase l) v d q (d l/ν) hreg
    simpa only [show gaussianFiniteWeightedSection (s.erase l) v d q (fun _ => 1)=
      gaussianThresholdSectionProbability (s.erase l) v d q from
      funext (gaussianFiniteWeightedSection_one_eq_sectionProbability (s.erase l) v d q)] using hc
  have hd := hasDerivAt_gaussianFiniteWeightedThreshold_update s v d l hl q hq hν hul (fun _ => 1)
    measurable_const (integrable_const _) (d l) hcont
  have hd' := (hd.comp (b l) ((hasDerivAt_id (b l)).sub_const
    (b j*faceDot (u l) (u j)))).const_mul (gaussianPDFReal 0 1 (b j))
  have hh := hd'.congr_of_eventuallyEq (Eventually.of_forall
    (positiveMixedFirstMassDensity_update_eq_weightedThreshold u b j l hjl))
  rw [gaussianFiniteWeightedSection_one_eq_pairProbability] at hh
  simpa only [mul_one] using hh

theorem hasDerivAt_positiveMixedFirstPlaneDensity_conditional {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => positiveMixedFirstPlaneDensity u (Function.update b l z) j l)
      (gaussianPDFReal 0 1 (b j)*((gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
        gaussianThresholdResidualScale u j l)*(((b j)^2+(gaussianPairConditionalLevel u b j l)^2)*
        hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b (u j)
          (gaussianPairConditionalDirection u j l) (b j) (gaussianPairConditionalLevel u b j l)))) (b l) := by
  let s := Finset.univ.erase j
  let v := fun k => gaussianNormalProjection (u j) (u k)
  let d := fun k => b k-b j*faceDot (u k) (u j)
  let q := gaussianPairConditionalDirection u j l
  let ν := gaussianThresholdResidualScale u j l
  obtain ⟨hq,heq,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hl : l∈s := Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩
  have hul : v l=ν • q := by
    change v l=ν • (ν⁻¹ • v l)
    rw [smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  have hcont : ContinuousAt (gaussianFiniteWeightedSection (s.erase l) v d q
      (positiveMixedPlaneFacetWeight q (b j))) (d l/ν) := by
    have hc := continuousAt_gaussianThresholdSectionProbability_of_slack (s.erase l) v d q (d l/ν) hreg
    have hh : ContinuousAt (fun t : ℝ => ((b j)^2+t^2)*
        gaussianThresholdSectionProbability (s.erase l) v d q t) (d l/ν) :=
      (continuousAt_const.add (continuousAt_id.pow 2)).mul hc
    convert hh using 1
    funext t
    exact gaussianFiniteWeightedSection_plane_eq_probability (s.erase l) v d q hq (b j) t
  have hd := hasDerivAt_gaussianFiniteWeightedThreshold_update s v d l hl q hq hν hul
    (positiveMixedPlaneFacetWeight q (b j)) (measurable_positiveMixedPlaneFacetWeight _ _)
    (integrable_positiveMixedPlaneFacetWeight _ _) (d l) hcont
  have hd' := (hd.comp (b l) ((hasDerivAt_id (b l)).sub_const
    (b j*faceDot (u l) (u j)))).const_mul (gaussianPDFReal 0 1 (b j))
  have hh := hd'.congr_of_eventuallyEq (Eventually.of_forall
    (positiveMixedFirstPlaneDensity_update_eq_weightedThreshold u b j l hjl))
  rw [gaussianFiniteWeightedSection_plane_eq_probability _ _ _ _ hq,
    ← gaussianFiniteWeightedSection_one_eq_sectionProbability,
    gaussianFiniteWeightedSection_one_eq_pairProbability] at hh
  simpa only [mul_one] using hh

theorem hasDerivAt_positiveMixedFirstMassDensity_native {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => positiveMixedFirstMassDensity u (Function.update b l z) j)
      ((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
        hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
          (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) (b l) := by
  have hd := hasDerivAt_positiveMixedFirstMassDensity_conditional u b j l hjl hu hv hp hm hreg
  have hcoef : gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
      gaussianThresholdResidualScale u j l)=
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2) := by
    convert gaussianPair_conditional_density_jacobian_eq u b j l hu hv hp hm using 1
    ring
  rw [← mul_assoc,hcoef,hardGaussianConditionalPairProbability_eq_native _ u b j l hu hv hp hm] at hd
  exact hd

theorem hasDerivAt_positiveMixedFirstPlaneDensity_native {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => positiveMixedFirstPlaneDensity u (Function.update b l z) j l)
      (((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
        hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
          (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))*
        ((b j)^2+(gaussianPairConditionalLevel u b j l)^2)) (b l) := by
  have hd := hasDerivAt_positiveMixedFirstPlaneDensity_conditional u b j l hjl hu hv hp hm hreg
  have hcoef : gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
      gaussianThresholdResidualScale u j l)=
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2) := by
    convert gaussianPair_conditional_density_jacobian_eq u b j l hu hv hp hm using 1
    ring
  rw [← mul_assoc,hcoef,hardGaussianConditionalPairProbability_eq_native _ u b j l hu hv hp hm] at hd
  convert hd using 1
  ring

/-- On the actual native pair section, the actual original-normal plane
projection has exactly the conditional normal squared length. -/
theorem positiveMixedPairPlane_projection_normSq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (g : Vector r) :
    vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec (gaussianPairBase u b j l g))=
      (b j)^2+(gaussianPairConditionalLevel u b j l)^2 := by
  rw [← gaussianPairConditionalBase_eq_pairBase u b j l hu hv hp hm g]
  change vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec
    (gaussianSectionPoint (u j) (b j) (gaussianSectionPoint (gaussianPairConditionalDirection u j l)
      (gaussianPairConditionalLevel u b j l) g)))=_
  rw [← positiveMixedPlaneFacetWeight_eq_actual_projection u j l hu hv hp hm]
  unfold positiveMixedPlaneFacetWeight
  rw [gaussianSectionPoint_on_hyperplane _ _
    (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).1]

end
end RectangleCLTArxivV1
