import RectangleCLTArxivV1.SupplementalHPairSectionTrace
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea

/-! Exact conditional-to-symmetric coordinates for the actual signed
mixed Gaussian section. Every retained hard inequality and the signed
radial score are preserved pointwise; the Gaussian density and Gram
Jacobian are then converted without any local slack or family-rank
hypothesis. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

theorem gaussianPairConditionalDirection_geometry_nonparallel {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    vectorNormSq (gaussianPairConditionalDirection u j l)=1 ∧
      faceDot (u j) (gaussianPairConditionalDirection u j l)=0 ∧
      0<gaussianThresholdResidualScale u j l := by
  let ν := gaussianThresholdResidualScale u j l
  have hν : 0<ν := by
    rw [show ν=2*thresholdPairFirstCoefficient u j l*thresholdPairSecondCoefficient u j l from
      thresholdPair_residualScale_eq u j l hu hv hp hm]
    exact mul_pos (mul_pos (by norm_num)
      (div_pos (norm_pos_iff.mpr hp) (by norm_num)))
      (div_pos (norm_pos_iff.mpr hm) (by norm_num))
  have hn : vectorNormSq (gaussianNormalProjection (u j) (u l))=ν^2 :=
    (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  refine ⟨?_,?_,hν⟩
  · unfold gaussianPairConditionalDirection
    simp only [vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    change ν⁻¹^2*vectorNormSq (gaussianNormalProjection (u j) (u l))=1
    rw [hn]
    field_simp
  · rw [gaussianPairConditionalDirection,threshold_faceDot_smul_right,
      gaussianNormalProjection_orthogonal (u j) (u l) hu,mul_zero]

/-- Actual weighted hard pair sections are unchanged by the concrete
orthogonal coordinate rotation, with the original weight evaluated at
the actual point. This is a pointwise integral identity. -/
theorem hardGaussianConditionalPairSection_eq_pairSection {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (H : Vector r → ℝ) :
    (∫ g,(gaussianFiniteThresholdEvent s u b).indicator H
      (gaussianPairSectionPoint (u j) (gaussianPairConditionalDirection u j l) (b j)
        (gaussianPairConditionalLevel u b j l) g) ∂standardGaussian r)=
      ∫ g,(gaussianFiniteThresholdEvent s u b).indicator H
        (gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g)
          ∂standardGaussian r := by
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change (gaussianFiniteThresholdEvent s u b).indicator H (gaussianPairConditionalBase u b j l g)=
      (gaussianFiniteThresholdEvent s u b).indicator H (gaussianPairBase u b j l g)
    rw [gaussianPairConditionalBase_eq_pairBase u b j l hu hv hp hm g])

theorem hardGaussianConditionalPairSignedSection_eq_pairSection {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    hardGaussianPairSignedSection s u b (u j) (gaussianPairConditionalDirection u j l)
        (b j) (gaussianPairConditionalLevel u b j l)=
      hardGaussianPairSignedSection s u b (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) (thresholdPairFirstLevel u b j l)
        (thresholdPairSecondLevel u b j l) :=
  hardGaussianConditionalPairSection_eq_pairSection s u b j l hu hv hp hm _

theorem hardGaussianConditionalPairSignedSection_integrable {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    Integrable (fun g => (gaussianFiniteThresholdEvent s u b).indicator
      (fun x => vectorNormSq x-((n+1:ℕ):ℝ))
      (gaussianPairSectionPoint (u j) (gaussianPairConditionalDirection u j l)
        (b j) (gaussianPairConditionalLevel u b j l) g)) (standardGaussian (n+1)) := by
  exact hardGaussianPairSignedSection_integrable s u b _ _ hu
    (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).1
    (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).2.1 _ _

/-- The true conditional normal density, including its residual-normal
Jacobian, is the symmetric pair normal density with its exact Gram
Jacobian. No derivative or strictness premise occurs. -/
theorem gaussianPair_conditional_density_jacobian_eq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
        gaussianThresholdResidualScale u j l=
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/
        Real.sqrt (1-faceDot (u j) (u l)^2) := by
  rw [gaussianPair_conditional_density_eq u b j l hu hv hp hm,
    gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv]

theorem hardGaussianConditionalMixedSignedSection_eq_pairSection {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    (gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
      gaussianThresholdResidualScale u j l)*
      hardGaussianPairSignedSection s u b (u j) (gaussianPairConditionalDirection u j l)
        (b j) (gaussianPairConditionalLevel u b j l)=
      (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/
        Real.sqrt (1-faceDot (u j) (u l)^2))*
      hardGaussianPairSignedSection s u b (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) (thresholdPairFirstLevel u b j l)
        (thresholdPairSecondLevel u b j l) := by
  rw [gaussianPair_conditional_density_jacobian_eq u b j l hu hv hp hm,
    hardGaussianConditionalPairSignedSection_eq_pairSection s u b j l hu hv hp hm]

/-- Literal multiplicative association of the mixed first-coarea output,
for the actual remaining face set. -/
theorem hardGaussianConditionalMixedSignedSection_nested_eq_pairSection {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    gaussianPDFReal 0 1 (b j)*
      ((gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
        gaussianThresholdResidualScale u j l)*
      hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b (u j)
        (gaussianPairConditionalDirection u j l) (b j) (gaussianPairConditionalLevel u b j l))=
      (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/
        Real.sqrt (1-faceDot (u j) (u l)^2))*
      hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) := by
  convert hardGaussianConditionalMixedSignedSection_eq_pairSection
    ((Finset.univ.erase j).erase l) u b j l hu hv hp hm using 1
  ring

end
end RectangleCLTArxivV1
