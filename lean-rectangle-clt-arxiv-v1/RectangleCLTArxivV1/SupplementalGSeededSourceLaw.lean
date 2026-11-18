import RectangleCLTArxivV1.SupplementalGSourceLaw

/-! The new rank-dimensional copy pattern is exactly the archived actual
seeded array experiment, rather than a replacement remainder definition. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_seededFourthArrayExperiment_eq_rectangular_pattern
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t θ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    seededFourthArrayExperiment s μ ξ C x ε t θ freshY freshW freshShift =
      capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift := by
  let β := bernoulliArrayLaw μ ξ t
  let κ := μ.prod μ
  let ν := β.prod (standardGaussian r)
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hgram : A*A.transpose=C*C.transpose := hA.trans hC.symm
  let B : Fin n → (Fin n → Vector p) × (Ω × Ω) → Vector p := fun i ba =>
    x+arraySum ba.1+((θ*(1+t)) • capOriginalCopy ξ freshShift i ba.2-ba.1 i)
  let O := capOriginalCopy ξ
  have hB (i : Fin n) : Measurable (B i) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      ((measurable_const.smul ((capOriginalCopy_measurable ξ h.measurable freshShift i).comp measurable_snd)).sub
        ((measurable_pi_apply i).comp measurable_fst))
  have hO (b : Bool) (i : Fin n) : Measurable (O b i) := capOriginalCopy_measurable ξ h.measurable b i
  have hb (b : Bool) (i : Fin n) : ∀ᵐ a ∂κ, ‖O b i a‖ ≤ δ := capOriginalCopy_bounded h b i
  have hs := cap_seeded_integral_fourthTensor_gaussian_split_rectangular s β κ A C hgram (t+ε)
    B (O false) (O false) (O freshY) (O freshW) hB (hO false) (hO false) (hO freshY) (hO freshW)
    h.delta_nonneg (hb false) (hb false) (hb freshY) (hb freshW)
  change seededFourthArrayExperiment s μ ξ C x ε t θ freshY freshW freshShift = _ at hs
  rw [hs]
  let K : Fin n → (((Fin n → Vector p) × Vector r) × (Ω × Ω)) → ℝ := fun i z =>
    s.convolutionFourthTensor (gaussianLaw (seededSplitGaussianScale ε t • C))
      (capSeededBaseValue A x ε t z.1+capSeededCopyShift ξ freshShift t θ i z)
      (capOriginalCopy ξ false i z.2) (capOriginalCopy ξ false i z.2)
      (capOriginalCopy ξ freshY i z.2) (capOriginalCopy ξ freshW i z.2)
  have hshift (i : Fin n) := capSeededCopyShift_measurable (r := r) ξ h.measurable freshShift t θ i
  have hKm (i : Fin n) : Measurable (K i) := measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
    (((capSeededBaseValue_measurable A x ε t).comp measurable_fst).add (hshift i))
    ((hO false i).comp measurable_snd) ((hO false i).comp measurable_snd)
    ((hO freshY i).comp measurable_snd) ((hO freshW i).comp measurable_snd)
  have hKb (i : Fin n) : ∀ᵐ a ∂κ, ∀ bg, ‖K i (bg,a)‖ ≤ seededFourthTensorEnvelope s δ := by
    filter_upwards [hb false i,hb freshY i,hb freshW i] with a hf hy hw
    exact fun _ => seeded_fourthTensor_norm_le s _ _ _ _ _ _ h.delta_nonneg hf hf hy hw
  have he : (∫ bg, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale (t+ε) • C))
      (B i (bg.1,a)+(splitGaussianScale (t+ε) • A).mulVec bg.2)
      (O false i a) (O false i a) (O freshY i a) (O freshW i a) ∂κ ∂ν) =
      ∫ bg, ∑ i, ∫ a, K i (bg,a) ∂κ ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ (fun bg => by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact ae_of_all _ (fun a => by
        have hp : B i (bg.1,a)+(splitGaussianScale (t+ε) • A).mulVec bg.2 =
            capSeededBaseValue A x ε t bg+capSeededCopyShift ξ freshShift t θ i (bg,a) := by
          dsimp only [B,capSeededBaseValue,capSeededCopyShift,splitGaussianScale,seededSplitGaussianScale]
          abel
        dsimp only [K]
        rw [hp]
        rfl))
  rw [he,seeded_integral_sum_inner_to_prod ν κ K hKm hKb]
  have hre (i : Fin n) : ∀ᵐ z ∂ν.prod κ,
      A.mulVec (capWhitenedCopy A ξ i z.2)=capOriginalCopy ξ false i z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (capWhitenedCopy_reconstruct h A hA i)
  have hraw : (∫ z, ∑ i, K i z ∂ν.prod κ) =
      ∫ z, ∑ i, s.convolutionFourthTensor (gaussianLaw (seededSplitGaussianScale ε t • C))
        (capSeededBaseValue A x ε t z.1+capSeededCopyShift ξ freshShift t θ i z)
        (A.mulVec (capWhitenedCopy A ξ i z.2)) (A.mulVec (capWhitenedCopy A ξ i z.2))
        (capOriginalCopy ξ freshY i z.2) (capOriginalCopy ξ freshW i z.2) ∂ν.prod κ := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hre] with z hz
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [K]
    rw [hz i]
  rw [hraw]
  apply cap_convolutionFourthExpectation_eq_product_rectangular s (ν.prod κ) A C hgram
    (fun z => capSeededBaseValue A x ε t z.1) ((capSeededBaseValue_measurable A x ε t).comp measurable_fst)
    (fun i z => capWhitenedCopy A ξ i z.2) (fun i => (capWhitenedCopy_measurable h A i).comp measurable_snd)
    (fun i j k => by simpa only [one_mul] using
      (integrable_const (1 : ℝ) (μ := ν)).mul_prod (capWhitenedCopy_integrable_coordinate_pair h A i j k))
    (fun i z => capOriginalCopy ξ freshY i z.2) (fun i z => capOriginalCopy ξ freshW i z.2)
    (capSeededCopyShift ξ freshShift t θ)
    (fun i => (hO freshY i).comp measurable_snd) (fun i => (hO freshW i).comp measurable_snd) hshift
    h.delta_nonneg (fun i => Measure.quasiMeasurePreserving_snd.ae (hb freshY i))
    (fun i => Measure.quasiMeasurePreserving_snd.ae (hb freshW i))
    (seededSplitGaussianScale_pos hpos).ne'

end
end RectangleCLTArxivV1
