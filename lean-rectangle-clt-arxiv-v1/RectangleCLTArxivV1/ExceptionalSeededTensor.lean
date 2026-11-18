import RectangleCLTArxivV1.ExceptionalFourthBound
import RectangleCLTArxivV1.SupplementalIExceptional

/-! The exact actual seeded separated pattern is the first-pair-cutoff
product tensor expectation. Every copy/Gaussian exchange is justified by
actual coordinate-pair moments and bounded physical coefficient slots. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem exceptional_copy_gaussian_outer_sum_eq_product
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [Fintype ι] {r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Measure Ξ) [IsProbabilityMeasure κ]
    (F : Fin n → ι → (Ω × Ξ) × Vector r → ℝ)
    (hF : ∀ i a,Integrable (F i a) ((μ.prod κ).prod (standardGaussian r))) :
    (∑ a,∫ g,∫ ω,∑ i,∫ ξ,F i a ((ω,ξ),g) ∂κ ∂μ ∂standardGaussian r)=
      ∫ z : (Ω × Ξ) × Vector r,∑ i,∑ a,F i a z ∂(μ.prod κ).prod (standardGaussian r) := by
  have hm (a : ι) : (∫ g,∫ z,∑ i,F i a (z,g) ∂μ.prod κ ∂standardGaussian r)=
      ∫ g,∫ ω,∑ i,∫ ξ,F i a ((ω,ξ),g) ∂κ ∂μ ∂standardGaussian r := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hF i a).prod_left_ae)] with g hg
    exact cap_product_array_marginal μ κ (fun i z => F i a (z,g)) hg
  simp_rw [← hm]
  exact hFourth_gaussian_outer_sum_eq_product (μ.prod κ) F hF

theorem exceptional_seeded_separated_eq_cutoff_product
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) (ε t θ c : ℝ)
    (ht : t∈Set.Icc (0:ℝ) 1) (freshY freshW freshShift : Bool) :
    capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift=
      exceptionalFourthCutoffExpectation s
        (((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ)) A
        (fun z => capSeededBaseValue A x ε t z.1) (fun i z => capWhitenedCopy A ξ i z.2)
        (fun i z => capOriginalCopy ξ freshY i z.2) (fun i z => capOriginalCopy ξ freshW i z.2)
        (capSeededCopyShift ξ freshShift t θ) (seededSplitGaussianScale ε t)
        (fun f g => c≤1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|) := by
  classical
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let μb := (bernoulliArrayLaw μ ξ t).prod (standardGaussian r)
  let κ := μ.prod μ
  let ν := μb.prod κ
  let σ := seededSplitGaussianScale ε t
  let Y := capOriginalCopy ξ freshY
  let W := capOriginalCopy ξ freshW
  let Z := capWhitenedCopy A ξ
  let V := capSeededBaseValue (n := n) A x ε t
  let v := capSeededCopyShift (r := r) ξ freshShift t θ
  let P := fun f g : Face p => c≤1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|
  let B := fun i (α : Fin 2 → Face p) (z : ((Fin n → Vector p) × Vector r) × (Ω × Ω)) =>
    if P (α 0) (α 1) then capRectangularPairCoefficient A (α 0) (α 1) (Y i z.2) (W i z.2) else 0
  let X := fun i (z : (((Fin n → Vector p) × Vector r) × (Ω × Ω)) × Vector r) =>
    (σ•A).mulVec z.2+V z.1.1+v i z.1
  let S := fun i (f : Face p) (z : (((Fin n → Vector p) × Vector r) × (Ω × Ω)) × Vector r) =>
    ((normalDot f (Y i z.1.2)*normalDot f (W i z.1.2))*
      capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1.2) z.2)*
        selectorTupleWeight s ![f] (X i z)
  let T := fun i (α : Fin 2 → Face p) (z : (((Fin n → Vector p) × Vector r) × (Ω × Ω)) × Vector r) =>
    (B i α z.1*repeatedDirectionScore z.2 (Z i z.1.2))*selectorTupleWeight s α (X i z)
  have hdiag : ∀ j,(A*A.transpose) j j=1 := by intro j;rw [hA];exact hunit j
  have hZl (i : Fin n) (j k : Fin r) : Integrable (fun z : ((Fin n → Vector p) × Vector r) × (Ω × Ω) =>
      Z i z.2 j*Z i z.2 k) ν := by
    simpa only [one_mul] using (integrable_const (1:ℝ) (μ := μb)).mul_prod
      (capWhitenedCopy_integrable_coordinate_pair h A i j k)
  have hYl (i : Fin n) : ∀ᵐ z ∂ν,‖Y i z.2‖≤δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshY i)
  have hWl (i : Fin n) : ∀ᵐ z ∂ν,‖W i z.2‖≤δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshW i)
  have hXm (i : Fin n) : Measurable (X i) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      ((capSeededBaseValue_measurable A x ε t).comp measurable_fst.fst)).add
      ((capSeededCopyShift_measurable ξ h.measurable freshShift t θ i).comp measurable_fst)
  have hCm (i : Fin n) (f : Face p) : Measurable
      (fun z : ((Fin n → Vector p) × Vector r) × (Ω × Ω) =>
        normalDot f (Y i z.2)*normalDot f (W i z.2)) :=
    (((continuous_normalDot f).measurable.comp (capOriginalCopy_measurable ξ h.measurable freshY i)).comp measurable_snd).mul
      (((continuous_normalDot f).measurable.comp (capOriginalCopy_measurable ξ h.measurable freshW i)).comp measurable_snd)
  have hCb (i : Fin n) (f : Face p) : ∀ᵐ z ∂ν,
      |normalDot f (Y i z.2)*normalDot f (W i z.2)|≤δ^2 :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_face_product_bounded h freshY freshW f i)
  have hBm (i : Fin n) (α : Fin 2 → Face p) : Measurable (B i α) := by
    have hYm : Measurable (fun z : ((Fin n → Vector p) × Vector r) × (Ω × Ω) => Y i z.2) :=
      (capOriginalCopy_measurable ξ h.measurable freshY i).comp measurable_snd
    have hWm : Measurable (fun z : ((Fin n → Vector p) × Vector r) × (Ω × Ω) => W i z.2) :=
      (capOriginalCopy_measurable ξ h.measurable freshW i).comp measurable_snd
    have hYn (f : Face p) := (continuous_normalDot f).measurable.comp hYm
    have hWn (f : Face p) := (continuous_normalDot f).measurable.comp hWm
    dsimp only [B]
    split_ifs
    · unfold capRectangularPairCoefficient
      exact (((hYn (α 0)).mul (hWn (α 1))).add ((hYn (α 1)).mul (hWn (α 0)))).sub
        (measurable_const.mul (((hYn (α 0)).mul (hWn (α 0))).add ((hYn (α 1)).mul (hWn (α 1)))))
    · exact measurable_const
  have hBb (i : Fin n) (α : Fin 2 → Face p) : ∀ᵐ z ∂ν,|B i α z|≤4*δ^2 := by
    filter_upwards [hYl i,hWl i] with z hy hw
    dsimp only [B]
    split_ifs
    · exact cap_original_pair_coefficient_abs_le A hdiag _ _ _ _ h.delta_nonneg hy hw
    · simp only [abs_zero];positivity
  have hSi (i : Fin n) (f : Face p) : Integrable (S i f) (ν.prod (standardGaussian r)) := by
    simpa only [S,mul_assoc] using cap_integrable_bounded_coefficient_score ν (standardGaussian r) _ _
      (integrable_random_capThirdHermiteScore ν _ (fun z => Z i z.2) (hZl i))
      (measurable_selectorTupleWeight_comp s ![f] _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)];exact selectorTupleWeight_le_one s _ _)
      _ (hCm i f) (hCb i f)
  have hTi (i : Fin n) (α : Fin 2 → Face p) : Integrable (T i α) (ν.prod (standardGaussian r)) := by
    simpa only [T,mul_assoc] using cap_integrable_bounded_coefficient_score ν (standardGaussian r) _ _
      (integrable_random_repeatedDirectionScore ν (fun z => Z i z.2) (hZl i))
      (measurable_selectorTupleWeight_comp s α _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)];exact selectorTupleWeight_le_one s _ _)
      _ (hBm i α) (hBb i α)
  have hS := exceptional_copy_gaussian_outer_sum_eq_product μb κ S hSi
  have hT := exceptional_copy_gaussian_outer_sum_eq_product μb κ T hTi
  rw [hFourth_sum_pair_tuples] at hT
  have hsingle : (∑ f,capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift)=
      -(1/(s.bandwidth*σ^3))*(∫ z,∑ i,∑ f,S i f z ∂ν.prod (standardGaussian r)) := by
    rw [← hS]
    simp only [capSeededSingleContribution,Finset.mul_sum]
    rfl
  have hpair : (∑ f : Face p,∑ g : Face p,
      if c≤correlationGap (A*A.transpose) f.1 g.1 then
        capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift else 0)=
      (1/(s.bandwidth^2*σ^2))*(∫ z,∑ i,∑ α,T i α z ∂ν.prod (standardGaussian r)) := by
    rw [← hT,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    have hgap : correlationGap (A*A.transpose) f.1 g.1=
        1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| := by
      rw [cap_signed_correlation_abs]
      rfl
    rw [hgap]
    dsimp only [T,B,Matrix.cons_val_zero,Matrix.cons_val_one]
    by_cases hp : P f g
    · have hp' : c≤1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| := hp
      rw [if_pos hp']
      simp only [if_pos hp]
      rfl
    · have hp' : ¬c≤1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| := hp
      rw [if_neg hp']
      simp only [if_neg hp,zero_mul,Finset.sum_const_zero,integral_zero,mul_zero]
  change _=-(1/(s.bandwidth*σ^3))*(∫ z,∑ i,∑ f,S i f z ∂ν.prod (standardGaussian r))+
    (1/(s.bandwidth^2*σ^2))*(∫ z,∑ i,∑ α,T i α z ∂ν.prod (standardGaussian r))
  exact congrArg₂ (fun a b : ℝ => a+b) hsingle hpair

end
end RectangleCLTArxivV1
