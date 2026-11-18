import RectangleCLTArxivV1.SupplementalGSeededSmallAngle
import RectangleCLTArxivV1.SupplementalGArrayDecomposition
import RectangleCLTArxivV1.SupplementalGGaussianHalves

/-! Named actual signed components of each calibrated fourth-order copy
pattern, and the exact identity that sums them to the actual derivative. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def capSeededSingleContribution {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ : ℝ) (f : Face p)
    (freshY freshW freshShift : Bool) : ℝ :=
  -(1/(s.bandwidth*(seededSplitGaussianScale ε t)^3))*(∫ g, ∫ ω, ∑ i, ∫ z,
    ((normalDot f (capOriginalCopy ξ freshY i z)*normalDot f (capOriginalCopy ξ freshW i z))*
      capThirdHermiteScore (capRectangularFactorNormal A f) (capWhitenedCopy A ξ i z) g)*
      selectorTupleWeight s ![f] ((seededSplitGaussianScale ε t • A).mulVec g+
        capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ
        ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r) ∂standardGaussian r)

def capSeededPairContribution {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ : ℝ) (f g : Face p)
    (freshY freshW freshShift : Bool) : ℝ :=
  (1/(s.bandwidth^2*(seededSplitGaussianScale ε t)^2))*(∫ z, ∫ ω, ∑ i, ∫ a,
    (capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a)
      (capOriginalCopy ξ freshW i a)*repeatedDirectionScore z (capWhitenedCopy A ξ i a))*
      selectorTupleWeight s ![f,g] ((seededSplitGaussianScale ε t • A).mulVec z+
        capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂μ.prod μ
        ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r) ∂standardGaussian r)

def capSeededFourthPattern {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ : ℝ)
    (freshY freshW freshShift : Bool) : ℝ :=
  restorationFourthExpectation s
    (((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ)) A
    (fun z => capSeededBaseValue A x ε t z.1) (fun i z => capWhitenedCopy A ξ i z.2)
    (fun i z => capOriginalCopy ξ freshY i z.2) (fun i z => capOriginalCopy ξ freshW i z.2)
    (capSeededCopyShift ξ freshShift t θ) (seededSplitGaussianScale ε t)

/-- Every signed component belongs to the actual fourth derivative used by
the seeded copy pattern. No analytic bound is an input to this identity. -/
theorem cap_seeded_fourth_pattern_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (x : Vector p) {ε t θ : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift =
      (∑ f, capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift)+
      ∑ f, ∑ g, capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hσ : seededSplitGaussianScale ε t ≠ 0 := (Real.sqrt_pos.mpr (half_pos hpos)).ne'
  have he := cap_array_fourth_expectation_product_single_pair s
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) (μ.prod μ) A hdiag
    (capSeededBaseValue A x ε t) (capSeededBaseValue_measurable A x ε t)
    (capWhitenedCopy A ξ) (capWhitenedCopy_measurable h A) (capWhitenedCopy_integrable_coordinate_pair h A)
    (capOriginalCopy ξ freshY) (capOriginalCopy ξ freshW)
    (capOriginalCopy_measurable ξ h.measurable freshY) (capOriginalCopy_measurable ξ h.measurable freshW)
    (capSeededCopyShift ξ freshShift t θ) (capSeededCopyShift_measurable ξ h.measurable freshShift t θ)
    h.delta_nonneg (capOriginalCopy_bounded h freshY) (capOriginalCopy_bounded h freshW) hσ
  simpa only [capSeededFourthPattern,capSeededSingleContribution,capSeededPairContribution,Finset.mul_sum] using he

end
end RectangleCLTArxivV1
