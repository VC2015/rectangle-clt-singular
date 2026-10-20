import RectangleCLTCompanion.FourthIdentityCorrections
import RectangleCLTCompanion.SharpComparisonEarly

/-! Exact fourth-order identity for the actual finite Bernoulli--Gaussian
path. The three displayed terms are independently integrated fresh row terms,
and their base points use the actual row-deleted selector sum. -/

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 800000

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

private theorem integrable_commonPointCorrections_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ W : Ω → Vector p) (hξ : Measurable ξ) (hW : Measurable W) (a : ℝ) :
    Integrable (fun ω => s.secondCommonPointCorrection ν μ ξ (W ω) a) μ ∧
    Integrable (fun ω => s.thirdCommonPointCorrection ν μ ξ (W ω) a) μ := by
  constructor
  · unfold secondCommonPointCorrection
    apply integrable_finset_sum
    intro j _
    apply integrable_finset_sum
    intro k _
    exact ((integrable_shifted_bounded_test_mean μ W ξ hW hξ a _
      (s.continuous_convolutionSecondDerivative ν j k) _
      (fun z => s.norm_convolutionSecondDerivative_le ν z j k)).sub
      (integrable_bounded_test_comp μ W hW _ (s.continuous_convolutionSecondDerivative ν j k)
        _ (fun z => s.norm_convolutionSecondDerivative_le ν z j k))).const_mul _
  · unfold thirdCommonPointCorrection
    apply integrable_finset_sum
    intro j _
    apply integrable_finset_sum
    intro k _
    apply integrable_finset_sum
    intro l _
    exact ((integrable_shifted_bounded_test_mean μ W ξ hW hξ a _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun z => s.norm_convolutionThirdDerivative_le ν z j k l)).sub
      (integrable_bounded_test_comp μ W hW _
        (s.continuous_convolutionThirdDerivative_commonPoint ν j k l)
        _ (fun z => s.norm_convolutionThirdDerivative_le ν z j k l))).const_mul _

theorem integrable_fourthRows_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ W : Ω → Vector p) (hξ : Measurable ξ) (hW : Measurable W) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => s.fourthRowA ν μ ξ (W ω) t) μ ∧
    Integrable (fun ω => s.fourthRowB ν μ ξ (W ω) t) μ ∧
    Integrable (fun ω => s.fourthRowC ν μ ξ (W ω) t) μ := by
  have hi := s.integrable_commonPointCorrections_base ν μ ξ W hξ hW (thinningScale t)
  have hiB : Integrable (fun ω => s.fourthRowB ν μ ξ (W ω) t) μ := by
    convert hi.1.const_mul (thinningProbability t / 2) using 1
    ext ω
    exact (s.secondCommonPointCorrection_eq_fourthRowB ν μ ξ hξ hbound hcenter (W ω) ht).symm
  have hiC : Integrable (fun ω => s.fourthRowC ν μ ξ (W ω) t) μ := by
    convert hi.2.const_mul (t * thinningProbability t / 3) using 1
    ext ω
    exact (s.thirdCommonPointCorrection_eq_fourthRowC ν μ ξ hξ (W ω) ht).symm
  refine ⟨?_, hiB, hiC⟩
  have hiR := s.integrable_correctedOneObservationResidual_base ν μ ξ W hξ hW hδ hbound ht
  convert (hiR.sub hiB).sub hiC using 1
  ext ω
  dsimp only [Pi.sub_apply]
  rw [s.correctedOneObservationResidual_eq_fourthRows ν μ ξ hξ hbound hcenter (W ω) ht]
  ring

def selectorFourthA {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.fourthRowA ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ

def selectorFourthB {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.fourthRowB ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ

def selectorFourthC {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.fourthRowC ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ

theorem selectorCorrectedResidual_eq_fourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorCorrectedResidual ν μ ξ x t =
      s.selectorFourthA ν μ ξ x t + s.selectorFourthB ν μ ξ x t +
        s.selectorFourthC ν μ ξ x t := by
  unfold selectorCorrectedResidual selectorFourthA selectorFourthB selectorFourthC
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro mask _
  have hW : Measurable (fun ω => x + thinningScale t •
      maskObservationSum ξ (Function.update mask i false) ω) :=
    measurable_const.add (measurable_const.smul
      (measurable_maskObservationSum ξ h.measurable _))
  have hi := s.integrable_fourthRows_base ν μ (ξ i) _ (h.measurable i) hW h.delta_nonneg
    (h.bounded i) (h.centered i) ht
  rw [show (fun ω => s.correctedOneObservationResidual ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t) =
    (fun ω => s.fourthRowA ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t +
      s.fourthRowB ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t +
      s.fourthRowC ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t) by
      funext ω
      exact s.correctedOneObservationResidual_eq_fourthRows ν μ (ξ i) (h.measurable i)
        (h.bounded i) (h.centered i) _ ht]
  have hadd := integral_add (hi.1.add hi.2.1) hi.2.2
  have hab := integral_add hi.1 hi.2.1
  dsimp only [Pi.add_apply] at hadd hab
  rw [hadd, hab]
  ring

omit ν [IsProbabilityMeasure ν] in
/-- Exact fourth-order identity for the actual path derivative, with the
entire signed cubic tensor contracted only after summing observations. -/
theorem selectorHeatDerivative_eq_fourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorHeatDerivative μ ξ A x t = -(t / 3) * s.signedCubicPathTerm μ ξ A x t +
      (s.selectorFourthA (gaussianLaw (Real.sqrt t • A)) μ ξ x t +
       s.selectorFourthB (gaussianLaw (Real.sqrt t • A)) μ ξ x t +
       s.selectorFourthC (gaussianLaw (Real.sqrt t • A)) μ ξ x t) := by
  rw [s.selectorHeatDerivative_eq_signedCubic_add_residual μ ξ h A hA x ht,
    s.selectorCorrectedResidual_eq_fourthTerms _ μ ξ h x ht]

omit ν [IsProbabilityMeasure ν] in
theorem hasDerivAt_selectorHeatExpectation_fourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (s.selectorHeatExpectation μ ξ A x)
      (-(t / 3) * s.signedCubicPathTerm μ ξ A x t +
        (s.selectorFourthA (gaussianLaw (Real.sqrt t • A)) μ ξ x t +
         s.selectorFourthB (gaussianLaw (Real.sqrt t • A)) μ ξ x t +
         s.selectorFourthC (gaussianLaw (Real.sqrt t • A)) μ ξ x t)) t := by
  rw [← s.selectorHeatDerivative_eq_fourthTerms μ ξ h A hA x ht.le]
  exact s.hasDerivAt_selectorHeatExpectation μ ξ h.measurable h.delta_nonneg h.bounded A x ht

end
end RectangleCLT.FaceSmoother
