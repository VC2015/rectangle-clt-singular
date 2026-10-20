import RectangleCLT.BernoulliAggregate
import RectangleCLT.OneObservationBounds

/-! Fresh-copy Bernoulli averaging returns the actual common-point operator.
All integrability follows from bounded continuous tests under the genuine
independent product law. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

/-- Integrating a bounded measurable fresh-copy test gives an integrable
function of the original sample. No independence is required for this step. -/
theorem integrable_freshCopy_bounded_test
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V U : Ω → Vector p) (hV : Measurable V) (hU : Measurable U)
    (a : ℝ) (x : Vector p) (G : Vector p → ℝ) (hG : Continuous G)
    (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    Integrable (fun ω => ∫ ω', G (x + a • V ω + a • U ω') ∂μ) μ := by
  have hW : Measurable (fun z : Ω × Ω => x + a • V z.1 + a • U z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul (hU.comp measurable_snd))
  have hi : Integrable (fun z : Ω × Ω => G (x + a • V z.1 + a • U z.2)) (μ.prod μ) :=
    integrable_bounded_test_comp (μ.prod μ) _ hW G hG C hGbound
  exact hi.integral_prod_left

/-- Averaging the retained leave-one-out operator over selectors and the
original sample equals the full common-point expectation. -/
theorem sum_mask_freshCopy_average
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (i : Fin n) (q a : ℝ) (x : Vector p)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    (∑ mask, Kane.maskWeight q mask *
      ∫ ω, ((1 - q) * G (x + a • maskObservationSum ξ (Function.update mask i false) ω) +
        q * ∫ ω', G (x + a • maskObservationSum ξ (Function.update mask i false) ω +
          a • ξ i ω') ∂μ) ∂μ) =
      ∑ mask, Kane.maskWeight q mask *
        ∫ ω, G (x + a • maskObservationSum ξ mask ω) ∂μ := by
  let F : Kane.Cube n → ℝ := fun mask => ∫ ω, G (x + a • maskObservationSum ξ mask ω) ∂μ
  calc
    _ = ∑ mask, Kane.maskWeight q mask *
        ((1 - q) * F (Function.update mask i false) + q * F (Function.update mask i true)) := by
      apply Finset.sum_congr rfl
      intro mask _
      congr 1
      have hV := measurable_maskObservationSum ξ hξ (Function.update mask i false)
      have hi₀ : Integrable (fun ω => G
          (x + a • maskObservationSum ξ (Function.update mask i false) ω)) μ :=
        integrable_bounded_test_comp μ _ (measurable_const.add (measurable_const.smul hV))
          G hG C hGbound
      have hi₁ := integrable_freshCopy_bounded_test μ _ (ξ i) hV (hξ i) a x G hG C hGbound
      rw [integral_add (hi₀.const_mul (1 - q)) (hi₁.const_mul q),
        integral_const_mul, integral_const_mul]
      change (1 - q) * F (Function.update mask i false) + q * _ = _
      rw [← integral_mask_force_true_eq_double μ ξ hξ hind hbound mask i a x G hG C hGbound]
    _ = _ := BernoulliSelectorAlgebra.conditional_coordinate_average q i F

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- Continuity of the actual Gaussian/convolution third derivative. -/
theorem continuous_convolutionThirdDerivative_commonPoint (j k l : Fin p) :
    Continuous (fun x => s.convolutionThirdDerivative ν x j k l) := by
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν (fun x => s.mixedThirdDerivativeF x j k l)
    (s.continuous_thirdDerivative j k l) (13 / s.bandwidth ^ 3)
    (fun x => s.norm_thirdDerivative_le x j k l)

/-- The retained Hessian mean becomes the actual Hessian at the full
Bernoulli sum after averaging the independent selectors and observations. -/
theorem sum_mask_bernoulliMeanSecondDerivative
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (i : Fin n) (x : Vector p) (t : ℝ) (j k : Fin p) :
    (∑ mask, Kane.maskWeight (thinningProbability t) mask *
      ∫ ω, s.bernoulliMeanSecondDerivative ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t j k ∂μ) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, s.convolutionSecondDerivative ν (x + thinningScale t • maskObservationSum ξ mask ω) j k ∂μ := by
  simpa only [bernoulliMeanSecondDerivative] using
    sum_mask_freshCopy_average μ ξ hξ hind hbound i (thinningProbability t) (thinningScale t) x
      (fun y => s.convolutionSecondDerivative ν y j k)
      (s.continuous_convolutionSecondDerivative ν j k) (3 / s.bandwidth ^ 2)
      (fun y => s.norm_convolutionSecondDerivative_le ν y j k)

/-- The analogous exact common-point identity for the signed cubic operator. -/
theorem sum_mask_bernoulliMeanThirdDerivative
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (i : Fin n) (x : Vector p) (t : ℝ) (j k l : Fin p) :
    (∑ mask, Kane.maskWeight (thinningProbability t) mask *
      ∫ ω, s.bernoulliMeanThirdDerivative ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t j k l ∂μ) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, s.convolutionThirdDerivative ν (x + thinningScale t • maskObservationSum ξ mask ω) j k l ∂μ := by
  simpa only [bernoulliMeanThirdDerivative] using
    sum_mask_freshCopy_average μ ξ hξ hind hbound i (thinningProbability t) (thinningScale t) x
      (fun y => s.convolutionThirdDerivative ν y j k l)
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) (13 / s.bandwidth ^ 3)
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)

end FaceSmoother
end RectangleCLT
