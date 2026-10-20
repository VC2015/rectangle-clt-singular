import RectangleCLTCompanion.SignedSurfaceImageCaps
import RectangleCLTCompanion.SignedSurfaceFacetDyadic
import RectangleCLTCompanion.SignedSurfaceAveraging

/-! The actual finite facet and ridge shell estimates are combined with
uniform rectangle concentration in one probability experiment. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

/-- A genuine averaged source-shell cap. Every probability, integrability,
active-set, and Gram hypothesis of the tube bounds is discharged; the sole
probabilistic input is the uniform concentration property proved for the
actual bounded and Gaussian base laws. -/
theorem averagedSurfaceShell_le_concentration {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {C η v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v)
    (_hC : 0 ≤ C) (_hη : 0 ≤ η) (_hv : 0 < v)
    (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    averagedSurfaceShell μ s a A σ n ≤
      (80 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 /
        (((a : ℝ) + 1) * σ)) *
        (C * (σ * tubeRadius (dyadicRadius n) + η) * Real.sqrt (dimensionLog p / v) *
          (standardGaussian p).real
            {g | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius (σ • A) g}) := by
  classical
  let B := dyadicShell (fourFaceProjectionRadius (σ • A)) n
  let ε := tubeRadius (dyadicRadius n)
  let Q := C * (σ * ε + η) * Real.sqrt (dimensionLog p / v) *
    (standardGaussian p).real {g | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius (σ • A) g}
  let kf := 16 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 /
    (((a : ℝ) + 1) * σ)
  let kp := 64 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 /
    (((a : ℝ) + 1) * σ)
  have hband : 0 < s.bandwidth := s.bandwidth_pos
  have hrad : 0 < dyadicRadius n := by unfold dyadicRadius; positivity
  have hkf : 0 ≤ kf := by dsimp [kf]; positivity
  have hkp : 0 ≤ kp := by dsimp [kp]; positivity
  have hB : MeasurableSet B := measurableSet_dyadicShell _ (measurable_fourFaceProjectionRadius _) n
  let Pf := fun f r => ((standardGaussian p).prod (gammaRectangleLaw p a)).real
    (imageEventOf (singletonFaceTuple f) s (σ • A) r B (facetTubeCoefficients σ ε))
  let Pp := fun T : NondegenerateFacePairs s.faces A => fun r =>
    ((standardGaussian p).prod (gammaRectangleLaw p a)).real
      (imageEventOf T.tuple s (σ • A) r B (pairTubeCoefficients T.tuple A σ ε))
  have hPf (f : Face p) : Integrable (Pf f) μ :=
    integrable_image_probability μ (gammaRectangleLaw p a) (singletonFaceTuple f) s (σ • A)
      B (facetTubeCoefficients σ ε) hB (facetTubeCoefficients_measurable _ _)
      (facet_normalMatrix_scaled_gram_isUnit (singletonFaceTuple f) A hdiag hσ)
  have hPp (T : NondegenerateFacePairs s.faces A) : Integrable (Pp T) μ :=
    integrable_image_probability μ (gammaRectangleLaw p a) T.tuple s (σ • A)
      B (pairTubeCoefficients T.tuple A σ ε) hB (pairCoefficientDomain_measurable _ _ _ _)
      (nondegeneratePair_scaled_gram_isUnit T hσ)
  have hf (f : Face p) (hf : f ∈ s.faces) :
      (∫ r, facetSurfaceMoment a f s A σ r B ∂μ) ≤ kf * ∫ r, Pf f r ∂μ := by
    calc
      _ ≤ ∫ r, kf * Pf f r ∂μ :=
        integral_mono (integrable_facetSurfaceMoment_base μ hp a f s A σ B)
          ((hPf f).const_mul kf) (fun r => by
            rw [facetSurfaceMoment_eq_Fpow_pi]
            exact facet_surface_dyadic_shell_le_image_probability hp a (singletonFaceTuple f)
              s A hdiag (fun _ => hf) hσ r n)
      _ = _ := integral_const_mul _ _
  have hpairs (T : NondegenerateFacePairs s.faces A) :
      (∫ r, pairSurfacePenalty a T.tuple s A σ r B ∂μ) ≤ kp * ∫ r, Pp T r ∂μ := by
    calc
      _ ≤ ∫ r, kp * Pp T r ∂μ :=
        integral_mono (integrable_pairSurfacePenalty_base μ hp a T.tuple s A σ B)
          ((hPp T).const_mul kp) (fun r =>
            pair_surface_dyadic_shell_le_image_probability hp a T.tuple s A hdiag
              (nondegeneratePair_active T) T.tuple_det_pos hσ r n)
      _ = _ := integral_const_mul _ _
  have hfacet : (∑ f ∈ s.faces, ∫ r, facetSurfaceMoment a f s A σ r B ∂μ) ≤ kf * Q := by
    calc
      _ ≤ ∑ f ∈ s.faces, kf * ∫ r, Pf f r ∂μ := Finset.sum_le_sum (fun f hf' => hf f hf')
      _ = kf * ∑ f ∈ s.faces, ∫ r, Pf f r ∂μ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_facet_shell_image_probability_le μ hconc s a A hdiag hσ n) hkf
  have hpair : (∑ T : NondegenerateFacePairs s.faces A,
      ∫ r, pairSurfacePenalty a T.tuple s A σ r B ∂μ) ≤ kp * Q := by
    calc
      _ ≤ ∑ T : NondegenerateFacePairs s.faces A, kp * ∫ r, Pp T r ∂μ :=
        Finset.sum_le_sum (fun T _ => hpairs T)
      _ = kp * ∑ T : NondegenerateFacePairs s.faces A, ∫ r, Pp T r ∂μ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_pair_shell_image_probability_le μ hconc s a A hdiag hσ n) hkp
  unfold averagedSurfaceShell
  rw [averagedSurfaceMomentOn_eq_sum_integrals μ hp]
  exact (add_le_add hfacet hpair).trans_eq (by dsimp [kf, kp, Q, ε]; ring)

end
end RectangleCLT.Companion.SignedSurface
