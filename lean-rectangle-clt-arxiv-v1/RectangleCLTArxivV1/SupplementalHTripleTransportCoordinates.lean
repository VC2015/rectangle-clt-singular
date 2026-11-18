import RectangleCLTArxivV1.SupplementalHTripleTransportSections
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual scalar-product, coordinate, and Euclidean-three-space laws.
All volume and Gaussian transports are genuine measurable equivalences. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

def tripleScalarEquiv : Vector 3 ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))).trans
      (MeasurableEquiv.prodComm : ℝ × (ℝ × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ)))

@[simp] theorem tripleScalarEquiv_apply (x : Vector 3) : tripleScalarEquiv x=((x 0,x 1),x 2) := rfl

@[simp] theorem tripleScalarEquiv_symm_apply (x : (ℝ × ℝ) × ℝ) :
    tripleScalarEquiv.symm x=![x.1.1,x.1.2,x.2] := by
  apply tripleScalarEquiv.injective
  simp

theorem tripleScalarEquiv_measurePreserving (μ : Measure ℝ) [SigmaFinite μ] :
    MeasurePreserving tripleScalarEquiv (Measure.pi (fun _ : Fin 3 => μ)) ((μ.prod μ).prod μ) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) (2 : Fin 3)
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_piFinTwo (fun _ : Fin 2 => μ))
  exact (Measure.measurePreserving_swap).comp (h2.comp h1)

theorem tripleScalarEquiv_volumePreserving :
    MeasurePreserving tripleScalarEquiv (volume : Measure (Vector 3))
      (((volume : Measure ℝ).prod volume).prod volume) := by
  simpa only [volume_pi] using tripleScalarEquiv_measurePreserving (volume : Measure ℝ)

def tripleEuclideanScalarEquiv : EuclideanSpace ℝ (Fin 3) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans tripleScalarEquiv

@[simp] theorem tripleEuclideanScalarEquiv_apply (x : EuclideanSpace ℝ (Fin 3)) :
    tripleEuclideanScalarEquiv x=((x 0,x 1),x 2) := rfl

@[simp] theorem tripleEuclideanScalarEquiv_symm_apply (x : (ℝ × ℝ) × ℝ) :
    tripleEuclideanScalarEquiv.symm x=projectionEuclideanVector ![x.1.1,x.1.2,x.2] := by
  apply tripleEuclideanScalarEquiv.injective
  simp [projectionEuclideanVector]

theorem tripleEuclideanScalarEquiv_volumePreserving :
    MeasurePreserving tripleEuclideanScalarEquiv (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (((volume : Measure ℝ).prod volume).prod volume) :=
  tripleScalarEquiv_volumePreserving.comp (PiLp.volume_preserving_equiv (ι := Fin 3))

def tripleScalarGaussian : Measure ((ℝ × ℝ) × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (gaussianReal 0 1)

def tripleEuclideanGaussian : Measure (EuclideanSpace ℝ (Fin 3)) :=
  tripleScalarGaussian.map tripleEuclideanScalarEquiv.symm

instance tripleScalarGaussian_isProbability : IsProbabilityMeasure tripleScalarGaussian := by
  unfold tripleScalarGaussian
  infer_instance

instance tripleEuclideanGaussian_isProbability : IsProbabilityMeasure tripleEuclideanGaussian :=
  isProbabilityMeasure_map tripleEuclideanScalarEquiv.symm.measurable.aemeasurable

theorem tripleEuclideanScalarEquiv_gaussianPreserving :
    MeasurePreserving tripleEuclideanScalarEquiv tripleEuclideanGaussian tripleScalarGaussian := by
  have hi : MeasurePreserving tripleEuclideanScalarEquiv.symm tripleScalarGaussian tripleEuclideanGaussian :=
    ⟨tripleEuclideanScalarEquiv.symm.measurable,rfl⟩
  exact MeasurePreserving.symm tripleEuclideanScalarEquiv.symm hi

/-- The intrinsic Euclidean law is exactly the ordinary three-coordinate
standard Gaussian pushed through the actual Euclidean coordinate map. -/
theorem tripleEuclideanGaussian_eq_map_standardGaussian :
    tripleEuclideanGaussian=(standardGaussian 3).map projectionEuclideanVector := by
  have hs := (tripleScalarEquiv_measurePreserving (gaussianReal 0 1)).map_eq
  change (standardGaussian 3).map tripleScalarEquiv=tripleScalarGaussian at hs
  unfold tripleEuclideanGaussian
  rw [← hs,Measure.map_map tripleEuclideanScalarEquiv.symm.measurable tripleScalarEquiv.measurable]
  congr 1
  funext x
  apply tripleEuclideanScalarEquiv.injective
  simp [projectionEuclideanVector]

/-- True Gaussian law for Euclidean-three normal coordinates and residual
ambient coordinates, before any conical event is selected. -/
theorem gaussianTripleEuclideanSectionMap_measurePreserving {n : ℕ}
    (e f h : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 3) × Vector (n+1) =>
      gaussianTripleSectionPoint e f h (z.1 0) (z.1 1) (z.1 2) z.2)
      (tripleEuclideanGaussian.prod (standardGaussian (n+1))) (standardGaussian (n+1)) := by
  have hi := tripleEuclideanScalarEquiv_gaussianPreserving.prod (MeasurePreserving.id (standardGaussian (n+1)))
  exact (gaussianTripleSectionMap_measurePreserving e f h he hf hh).comp hi

end
end RectangleCLTArxivV1
