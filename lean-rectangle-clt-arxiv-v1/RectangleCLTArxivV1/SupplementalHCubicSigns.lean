import RectangleCLTArxivV1.SupplementalHLineReference

/-! Both signs in the cubic split use the same actual smoothing point.
Negating the Gaussian factor and its scalar scale preserves that point. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem supplementalH_selectorFaceNormal_neg {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (f : Face p) :
    selectorFaceNormal (-A) f = -selectorFaceNormal A f := by
  ext j
  unfold selectorFaceNormal
  cases hf : f.2 <;> simp [hf]

theorem supplementalH_negative_scale_factor {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) : (-σ) • (-A)=σ • A := by
  ext j k
  simp

theorem supplementalH_negative_cubic_mean_reference_bound_all {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ)
    (α : Fin (K+1) → Face p)
    (hu : vectorNormSq (selectorFaceNormal A (α 0))=1) :
    supplementalHCubicMeanEnergy s (σ • A) v α (-(selectorFaceNormal A (α 0))) ≤
      (∫ g, (supplementalHPositiveDirection (-(selectorFaceNormal A (α 0))) g*
        selectorWeight s α ((σ • A).mulVec g+v))*(faceDot (-(selectorFaceNormal A (α 0))) g)^2
        ∂standardGaussian r)+
      2*weightMass (standardGaussian r)
        (fun g => supplementalHPositiveDirection (-(selectorFaceNormal A (α 0))) g*
          selectorWeight s α ((σ • A).mulVec g+v))*
        Real.log ((∫ g, supplementalHPositiveDirection (-(selectorFaceNormal A (α 0))) g*
          oneFaceReference s (α 0) ((σ • A).mulVec g+v) ∂standardGaussian r)/
          weightMass (standardGaussian r)
            (fun g => supplementalHPositiveDirection (-(selectorFaceNormal A (α 0))) g*
              selectorWeight s α ((σ • A).mulVec g+v))) := by
  have hun : vectorNormSq (selectorFaceNormal (-A) (α 0))=1 := by
    rw [supplementalH_selectorFaceNormal_neg]
    simpa only [vectorNormSq,Pi.neg_apply,neg_sq] using hu
  have h := supplementalH_cubic_mean_reference_bound_all s (-A) v (-σ) α hun
  simpa only [supplementalH_selectorFaceNormal_neg,supplementalH_negative_scale_factor] using h

end
end RectangleCLTArxivV1
