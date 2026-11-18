import RectangleCLTArxivV1.SupplementalGSeededPatterns
import RectangleCLTArxivV1.SupplementalGCopySlots
import RectangleCLTArxivV1.SupplementalGSmallAngle
import RectangleCLTArxivV1.SupplementalGSecondTransfer

/-! The small-angle estimate for the actual calibrated copy patterns,
with retained-array covariance, copy budgets, and shifts all discharged. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def capSeededWholeValue {p r n : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (ε t : ℝ) (z : (Fin n → Vector p) × Vector r) : Vector p :=
  x+arraySum z.1+(Real.sqrt (t+ε) • A).mulVec z.2

theorem cap_seeded_small_angle_pattern_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f₁ f₂ : Face p)
    (hρ : (faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂))^2 < 1)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (freshY freshW freshShift : Bool) :
    |(1/s.bandwidth^2)*(∫ ω, ∑ i, ∫ z,
      capRectangularPairCoefficient A f₁ f₂ (capOriginalCopy ξ freshY i z) (capOriginalCopy ξ freshW i z)*
        capSoftFaceSecond s {f₁,f₂} (capOriginalCopy ξ false i z)
          (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r))| ≤
      7168*Real.exp 6*Real.pi^3*δ^2*
        Real.sqrt (1-(faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂))^2)/s.bandwidth^2 := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hu := capRectangularFactorNormal_unit A hdiag f₁
  have hv := capRectangularFactorNormal_unit A hdiag f₂
  have hρ' : |dotProduct (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)| < 1 := by
    change |faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)| < 1
    nlinarith [sq_abs (faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)),
      abs_nonneg (faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂))]
  have hfg : f₁ ≠ f₂ := by
    intro he
    subst f₂
    have hu' : faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₁)= 1 := by
      simpa only [faceDot,vectorNormSq,pow_two] using hu
    rw [hu'] at hρ
    norm_num at hρ
  have hcov := cap_seededWhole_mixed_covariance h A hA hdiag hε ht.1 ht.2 f₁ f₂
  have hband' : 2*(2*δ) ≤ s.bandwidth := by nlinarith [h.delta_nonneg]
  have hVm : Measurable (capSeededWholeValue (n := n) A x ε t) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)
  have hD (i : Fin n) : Measurable (fun z : ((Fin n → Vector p) × Vector r) × (Ω × Ω) => capOriginalCopy ξ false i z.2) :=
    (capOriginalCopy_measurable ξ h.measurable false i).comp measurable_snd
  have hDb (i : Fin n) : ∀ᵐ z ∂((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ),
      ‖capOriginalCopy ξ false i z.2‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h false i)
  have ht' := cap_small_angle_complementary_remainder
    (cap_seeded_projection_hypotheses h t ht.1 ht.2 f₁ f₂)
    (Real.sqrt (t+ε) • capSignedFactor A f₁ f₂) s hband' f₁ f₂ hfg
    (capSeededWholeValue A x ε t) hVm (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)
    hu hv hρ' (by linarith : (1/2 : ℝ) ≤ 1+ε) hcov (normalDot f₁ x) (normalDot f₂ x)
    (fun z => cap_signed_mixed_projection_zero (fun i (b : Fin n → Vector p) => b i)
      A (Real.sqrt (t+ε)) f₁ f₂ x z)
    (fun z => cap_signed_mixed_projection_one (fun i (b : Fin n → Vector p) => b i)
      A (Real.sqrt (t+ε)) f₁ f₂ x z)
    (μ.prod μ) (capWhitenedSlot A ξ freshY) (capWhitenedSlot A ξ freshW)
    (capWhitenedSlot_measurable h A freshY) (capWhitenedSlot_measurable h A freshW)
    (capWhitenedSlot_integrable_coordinate_pair h A freshY) (capWhitenedSlot_integrable_coordinate_pair h A freshW)
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const)
    (fun i z => capOriginalCopy ξ false i z.2) (capSeededCopyShift ξ freshShift t θ)
    hD (capSeededCopyShift_measurable ξ h.measurable freshShift t θ)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) h.delta_nonneg
    (mul_nonneg (by norm_num) h.delta_nonneg) (fun _ => ae_of_all _ (fun _ => by norm_num))
    hDb (capSeededCopyShift_bounded h freshShift ht hθ)
    (fun e => by simpa only [one_mul] using capWhitenedSlot_quadratic_budget h A hA freshY e)
    (fun e => by simpa only [one_mul] using capWhitenedSlot_quadratic_budget h A hA freshW e)
    (by nlinarith [h.delta_nonneg] : 4*δ ≤ s.bandwidth)
  have he (ω : (Fin n → Vector p) × Vector r) :
      (∑ i, ∫ z, capRectangularPairCoefficient A f₁ f₂ (capOriginalCopy ξ freshY i z) (capOriginalCopy ξ freshW i z)*
        capSoftFaceSecond s {f₁,f₂} (capOriginalCopy ξ false i z)
          (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ) =
      ∑ i, ∫ z, capPairCoefficient (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)
        (capWhitenedSlot A ξ freshY i z) (capWhitenedSlot A ξ freshW i z)*
        capSoftFaceSecond s {f₁,f₂} (capOriginalCopy ξ false i z)
          (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [capOriginalCopy_pair_eq_factor_ae h A hA freshY freshW f₁ f₂ i] with z hz
    rw [hz]
  simp_rw [he]
  simpa only [one_mul,mul_one] using ht'

end
end RectangleCLTArxivV1
