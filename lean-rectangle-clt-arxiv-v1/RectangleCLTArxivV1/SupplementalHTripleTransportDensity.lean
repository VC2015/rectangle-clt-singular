import RectangleCLTArxivV1.SupplementalHTripleTransportCoordinates

/-! The actual Euclidean-three Gaussian density and genuine translated
normal-fiber domination for unbounded integrable event tests. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

def tripleEuclideanDensity (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹^3*RectangleCLT.Companion.SignedSurface.gaussianKernel z

theorem continuous_tripleEuclideanDensity : Continuous tripleEuclideanDensity := by
  unfold tripleEuclideanDensity RectangleCLT.Companion.SignedSurface.gaussianKernel
  fun_prop

theorem tripleEuclideanDensity_nonneg (z : EuclideanSpace ℝ (Fin 3)) : 0≤tripleEuclideanDensity z := by
  unfold tripleEuclideanDensity RectangleCLT.Companion.SignedSurface.gaussianKernel
  positivity

theorem tripleEuclideanDensity_pullback (x : Vector 3) :
    tripleEuclideanDensity (projectionEuclideanVector x)=standardGaussianDensity 3 x := by
  rw [standardGaussianDensity_eq_kernel]
  unfold tripleEuclideanDensity RectangleCLT.gaussianKernel RectangleCLT.Companion.SignedSurface.gaussianKernel
  rw [RectangleCLT.Companion.SignedSurface.vectorNormSq_eq_euclidean_norm_sq]
  rfl

theorem tripleEuclideanGaussian_integral_density
    (F : EuclideanSpace ℝ (Fin 3) → ℝ) (hF : Measurable F) :
    (∫ z,F z ∂tripleEuclideanGaussian)=∫ z,tripleEuclideanDensity z*F z := by
  have hproj : Measurable (projectionEuclideanVector : Vector 3 → EuclideanSpace ℝ (Fin 3)) :=
    (PiLp.continuous_equiv_symm 2 _).measurable
  rw [tripleEuclideanGaussian_eq_map_standardGaussian,
    integral_map hproj.aemeasurable hF.aestronglyMeasurable,standardGaussian_integral_density_mul]
  have hD : Measurable (fun z => tripleEuclideanDensity z*F z) := continuous_tripleEuclideanDensity.measurable.mul hF
  have hh := (PiLp.volume_preserving_equiv_symm (ι := Fin 3)).integral_comp
    (EuclideanSpace.measurableEquiv (Fin 3)).symm.measurableEmbedding (fun z => tripleEuclideanDensity z*F z)
  change (∫ x,tripleEuclideanDensity (projectionEuclideanVector x)*F (projectionEuclideanVector x))=
    ∫ z,tripleEuclideanDensity z*F z at hh
  simpa only [tripleEuclideanDensity_pullback] using hh

theorem tripleEuclideanGaussian_integrable_density_iff
    (F : EuclideanSpace ℝ (Fin 3) → ℝ) (hF : Measurable F) :
    Integrable F tripleEuclideanGaussian ↔ Integrable (fun z => tripleEuclideanDensity z*F z) volume := by
  have hG : MeasurePreserving projectionEuclideanVector (standardGaussian 3) tripleEuclideanGaussian :=
    ⟨(PiLp.continuous_equiv_symm 2 _).measurable,tripleEuclideanGaussian_eq_map_standardGaussian.symm⟩
  rw [← hG.integrable_comp hF.aestronglyMeasurable,standardGaussian_integrable_density_mul_iff]
  have hD : Measurable (fun z => tripleEuclideanDensity z*F z) := continuous_tripleEuclideanDensity.measurable.mul hF
  have hh := (PiLp.volume_preserving_equiv_symm (ι := Fin 3)).integrable_comp hD.aestronglyMeasurable
  change Integrable (fun x => tripleEuclideanDensity (projectionEuclideanVector x)*F (projectionEuclideanVector x)) volume ↔
    Integrable (fun z => tripleEuclideanDensity z*F z) volume at hh
  simpa only [tripleEuclideanDensity_pullback] using hh

/-- Actual normal-coordinate Gaussian integration dominates a genuine
translated finite cone fiber with its exact normalized Gaussian density. -/
theorem tripleEuclideanGaussian_integral_dominates_translated_fiber
    (F W : EuclideanSpace ℝ (Fin 3) → ℝ) (hFm : Measurable F)
    (hFi : Integrable F tripleEuclideanGaussian) (hF0 : ∀ z,0≤F z)
    (Z : EuclideanSpace ℝ (Fin 3)) (D : Set (EuclideanSpace ℝ (Fin 3))) (hD : MeasurableSet D)
    (hmatch : ∀ y∈D,F (Z+y)=W y) :
    (∫ y in D,W y*tripleEuclideanDensity (Z+y))≤∫ z,F z ∂tripleEuclideanGaussian := by
  have hi := (tripleEuclideanGaussian_integrable_density_iff F hFm).mp hFi
  have his := hi.comp_add_left Z
  calc
    _ = ∫ y in D,tripleEuclideanDensity (Z+y)*F (Z+y) := by
      apply setIntegral_congr_fun hD
      intro y hy
      dsimp only
      rw [hmatch y hy,mul_comm]
    _ ≤ ∫ y,tripleEuclideanDensity (Z+y)*F (Z+y) :=
      setIntegral_le_integral his (ae_of_all _ (fun y => mul_nonneg (tripleEuclideanDensity_nonneg _) (hF0 _)))
    _ = ∫ z,tripleEuclideanDensity z*F z := integral_add_left_eq_self (μ := volume)
      (fun z : EuclideanSpace ℝ (Fin 3) => tripleEuclideanDensity z*F z) Z
    _ = _ := (tripleEuclideanGaussian_integral_density F hFm).symm


/-- The intrinsic normal density is the product of the three genuine
scalar standard-normal densities in its orthonormal coordinates. -/
theorem tripleEuclideanDensity_eq_scalarProduct (z : EuclideanSpace ℝ (Fin 3)) :
    tripleEuclideanDensity z=(gaussianPDFReal 0 1 (z 0)*gaussianPDFReal 0 1 (z 1))*gaussianPDFReal 0 1 (z 2) := by
  have he : tripleEuclideanDensity z=standardGaussianDensity 3 (fun i => z i) := tripleEuclideanDensity_pullback _
  rw [he]
  simp only [standardGaussianDensity,Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.reduceSucc,mul_one]
  ring

end
end RectangleCLTArxivV1
