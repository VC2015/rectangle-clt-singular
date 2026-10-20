import RectangleCLTCompanion.SignedSurfaceConcentration
import RectangleCLTCompanion.SignedSurfacePowerMajorant

/-! Actual finite singleton and nondegenerate-pair tube probabilities.
The complete active sets are disjoint, so no face-count factor appears. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

lemma scaled_normal_norm_le {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {σ : ℝ} (hσ : 0 < σ) (f : Face p) :
    ‖projectionEuclideanVector (signedRowNormal (σ • A) f)‖ ≤ σ := by
  change ‖euclideanNormal (σ • A) f‖ ≤ σ
  rw [euclideanNormal_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hσ,
    euclideanNormal_unit A hdiag, mul_one]

/-- Every parameterized common-space image probability is genuinely
integrable over the arbitrary base probability law. -/
theorem integrable_image_probability {p q : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Integrable (fun r => ((standardGaussian p).prod τ).real (imageEventOf S s A r B D)) μ := by
  let γ := (standardGaussian p).prod τ
  let E := liftedImageEventOf S s A id B D
  have hE := measurableSet_liftedImageEventOf S s A id measurable_id B D hB hD hd
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (γ.prod μ) :=
    (integrable_const (1 : ℝ)).indicator hE
  apply hi.integral_prod_right.congr
  exact ae_of_all _ fun r => by
    have hs : MeasurableSet (imageEventOf S s A r B D) :=
      hE.preimage (measurable_id.prodMk measurable_const)
    exact integral_indicator_one hs

theorem sum_facet_shell_image_probability_le {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {C η v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v) (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    (∑ f ∈ s.faces, ∫ r, ((standardGaussian p).prod (gammaRectangleLaw p a)).real
      (imageEventOf (singletonFaceTuple f) s (σ • A) r
        (dyadicShell (fourFaceProjectionRadius (σ • A)) n)
        (facetTubeCoefficients σ (tubeRadius (dyadicRadius n)))) ∂μ) ≤
      C * (σ * tubeRadius (dyadicRadius n) + η) * Real.sqrt (dimensionLog p / v) *
        (standardGaussian p).real
          {g | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius (σ • A) g} := by
  classical
  have hR : 0 ≤ dyadicRadius n := by unfold dyadicRadius; positivity
  have hε := tubeRadius_pos hR
  apply sum_dyadic_image_probability_le μ (gammaRectangleLaw p a) id measurable_id
    s.faces singletonFaceTuple s (σ • A) (fun _ => facetTubeCoefficients σ (tubeRadius (dyadicRadius n)))
    (fun _ _ => facetTubeCoefficients_measurable _ _)
    (fun f hf _ => hf)
    (fun _ _ c hc i => facetTubeCoefficients_positive hσ hε hc i)
    (fun f _ => facet_normalMatrix_scaled_gram_isUnit (singletonFaceTuple f) A hdiag hσ)
    (fun f _ g _ heq => by
      simpa only [activeFaces_singleton, singletonFaceTuple, Finset.singleton_inj] using heq)
    hσ.le hε.le (tubeRadius_le_one hR) (scaled_normal_norm_le A hdiag hσ)
    (fun f _ c hc => facetTubeCoefficients_displacement_le (singletonFaceTuple f) A hdiag hσ hε.le hc)
    (by norm_num) n _
  intro e
  exact hconc.section_bound s (σ • A) hσ hε e

lemma nondegeneratePair_active {p : ℕ} {s : FaceSmoother p}
    {A : Matrix (Fin p) (Fin p) ℝ} (T : NondegenerateFacePairs s.faces A) (i : Fin 2) :
    T.tuple.face i ∈ s.faces := by
  apply T.val.property.1
  rw [← activeFaces_compatibleSetTuple T.val]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

lemma nondegeneratePair_scaled_gram_isUnit {p : ℕ} {s : FaceSmoother p}
    {A : Matrix (Fin p) (Fin p) ℝ} (T : NondegenerateFacePairs s.faces A)
    {σ : ℝ} (hσ : 0 < σ) :
    IsUnit ((normalMatrix T.tuple (σ • A)).transpose * normalMatrix T.tuple (σ • A)).det := by
  rw [normalMatrix_scaled_gram_det]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hσ.ne'))
    T.tuple_det_pos.ne')

theorem sum_pair_shell_image_probability_le {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {C η v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v) (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    (∑ T : NondegenerateFacePairs s.faces A, ∫ r,
      ((standardGaussian p).prod (gammaRectangleLaw p a)).real
        (imageEventOf T.tuple s (σ • A) r
          (dyadicShell (fourFaceProjectionRadius (σ • A)) n)
          (pairTubeCoefficients T.tuple A σ (tubeRadius (dyadicRadius n)))) ∂μ) ≤
      C * (σ * tubeRadius (dyadicRadius n) + η) * Real.sqrt (dimensionLog p / v) *
        (standardGaussian p).real
          {g | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius (σ • A) g} := by
  classical
  have hR : 0 ≤ dyadicRadius n := by unfold dyadicRadius; positivity
  have hε := tubeRadius_pos hR
  apply sum_dyadic_image_probability_le μ (gammaRectangleLaw p a) id measurable_id
    (Finset.univ : Finset (NondegenerateFacePairs s.faces A)) (fun T => T.tuple) s (σ • A)
    (fun T => pairTubeCoefficients T.tuple A σ (tubeRadius (dyadicRadius n)))
  · intro T _
    exact pairCoefficientDomain_measurable _ _ _ _
  · intro T _ i
    exact nondegeneratePair_active T i
  · intro T _ c hc i
    exact pairTubeCoefficients_positive T.tuple A hdiag T.tuple_det_pos hσ hε hc i
  · intro T _
    exact nondegeneratePair_scaled_gram_isUnit T hσ
  · intro T _ U _ heq
    apply Subtype.ext
    apply Subtype.ext
    simpa only [NondegenerateFacePairs.tuple, activeFaces_compatibleSetTuple] using heq
  · exact hσ.le
  · exact hε.le
  · exact tubeRadius_le_one hR
  · exact scaled_normal_norm_le A hdiag hσ
  · intro T _ c hc
    exact pairTubeCoefficients_displacement_le T.tuple A hdiag T.tuple_det_pos σ hε.le hc
  · norm_num
  · intro e
    exact hconc.section_bound s (σ • A) hσ hε e

end
end RectangleCLT.Companion.SignedSurface
