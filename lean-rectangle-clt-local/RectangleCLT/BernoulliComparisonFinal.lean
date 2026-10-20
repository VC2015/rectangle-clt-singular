import RectangleCLT.BernoulliAggregate
import RectangleCLT.BernoulliCommonPoint

/-! Exact global common-point identity for the actual Bernoulli--Gaussian
path. This file proves the operator identity; no comparison estimate or CLT
is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

/-- A bounded test with an independently integrated translation remains
integrable as a function of its measurable base point. -/
theorem integrable_shifted_bounded_test_mean
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W U : Ω → Vector p) (hW : Measurable W) (hU : Measurable U)
    (a : ℝ) (G : Vector p → ℝ) (hG : Continuous G)
    (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    Integrable (fun ω => ∫ ω', G (W ω + a • U ω') ∂μ) μ := by
  have hZ : Measurable (fun z : Ω × Ω => W z.1 + a • U z.2) :=
    (hW.comp measurable_fst).add (measurable_const.smul (hU.comp measurable_snd))
  have hi : Integrable (fun z : Ω × Ω => G (W z.1 + a • U z.2)) (μ.prod μ) :=
    integrable_bounded_test_comp (μ.prod μ) _ hZ G hG C hGbound
  exact hi.integral_prod_left

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

noncomputable def selectorSecondDerivativeAverage
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p)
    (q a : ℝ) (j k : Fin p) : ℝ :=
  ∑ mask, Kane.maskWeight q mask *
    ∫ ω, s.convolutionSecondDerivative ν (x + a • maskObservationSum ξ mask ω) j k ∂μ

noncomputable def selectorThirdDerivativeAverage
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p)
    (q a : ℝ) (j k l : Fin p) : ℝ :=
  ∑ mask, Kane.maskWeight q mask *
    ∫ ω, s.convolutionThirdDerivative ν (x + a • maskObservationSum ξ mask ω) j k l ∂μ

noncomputable def selectorCorrectedResidual
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.correctedOneObservationResidual ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ

theorem integrable_bernoulliMeanSecondDerivative_base
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) (t : ℝ) (j k : Fin p) :
    Integrable (fun ω => s.bernoulliMeanSecondDerivative ν μ ξ (W ω) t j k) μ := by
  have h₀ := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionSecondDerivative ν j k) _
    (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  have h₁ := integrable_shifted_bounded_test_mean μ W ξ hW hξ (thinningScale t) _
    (s.continuous_convolutionSecondDerivative ν j k) _
    (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  exact (h₀.const_mul (1 - thinningProbability t)).add (h₁.const_mul (thinningProbability t))

theorem integrable_bernoulliMeanThirdDerivative_base
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) (t : ℝ) (j k l : Fin p) :
    Integrable (fun ω => s.bernoulliMeanThirdDerivative ν μ ξ (W ω) t j k l) μ := by
  have h₀ := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  have h₁ := integrable_shifted_bounded_test_mean μ W ξ hW hξ (thinningScale t) _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  exact (h₀.const_mul (1 - thinningProbability t)).add (h₁.const_mul (thinningProbability t))

/-- The concrete corrected residual is integrable at every measurable base
point; its integrability does not require a derivative-envelope estimate. -/
theorem integrable_correctedOneObservationResidual_base
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => s.correctedOneObservationResidual ν μ ξ (W ω) t) μ := by
  have h₂ := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (s.integrable_bernoulliMeanSecondDerivative_base ν μ ξ W hξ hW t j k).const_mul
        (∫ ω, ξ ω j * ξ ω k ∂μ)))
  have h₃ := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        (s.integrable_bernoulliMeanThirdDerivative_base ν μ ξ W hξ hW t j k l).const_mul
          (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ))))
  have hop := s.integrable_observationTranslationDerivative_base ν μ ξ W hξ hW hδ hbound t
  apply (hop.add ((h₂.div_const 2).add (h₃.const_mul (t / 3)))).congr
  refine ae_of_all _ (fun ω => ?_)
  have hi := s.oneObservation_operator_identity ν μ ξ hξ hbound (W ω) t
  rw [← s.observationTranslationDerivative_eq_taylor ν μ ξ (W ω) ht] at hi
  dsimp only [Pi.add_apply]
  linarith only [hi]

/-- Integrating the exact retained one-observation operator preserves its
finite signed moment contractions. -/
theorem integral_observationTranslationDerivative_eq_corrected
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, s.observationTranslationDerivative ν μ ξ (W ω) t ∂μ) =
      -(∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
        ∫ ω, s.bernoulliMeanSecondDerivative ν μ ξ (W ω) t j k ∂μ) / 2 -
      t / 3 * (∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
        ∫ ω, s.bernoulliMeanThirdDerivative ν μ ξ (W ω) t j k l ∂μ) +
      ∫ ω, s.correctedOneObservationResidual ν μ ξ (W ω) t ∂μ := by
  let B₂ : Ω → ℝ := fun ω => ∑ j, ∑ k, (∫ z, ξ z j * ξ z k ∂μ) *
    s.bernoulliMeanSecondDerivative ν μ ξ (W ω) t j k
  let B₃ : Ω → ℝ := fun ω => ∑ j, ∑ k, ∑ l, (∫ z, ξ z j * ξ z k * ξ z l ∂μ) *
    s.bernoulliMeanThirdDerivative ν μ ξ (W ω) t j k l
  have hi₂ (j k : Fin p) := s.integrable_bernoulliMeanSecondDerivative_base ν μ ξ W hξ hW t j k
  have hi₃ (j k l : Fin p) := s.integrable_bernoulliMeanThirdDerivative_base ν μ ξ W hξ hW t j k l
  have h₂ : Integrable B₂ μ := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (hi₂ j k).const_mul _))
  have h₃ : Integrable B₃ μ := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => (hi₃ j k l).const_mul _)))
  have hR := s.integrable_correctedOneObservationResidual_base ν μ ξ W hξ hW hδ hbound ht
  have heq (ω : Ω) : s.observationTranslationDerivative ν μ ξ (W ω) t =
      -B₂ ω / 2 - t / 3 * B₃ ω + s.correctedOneObservationResidual ν μ ξ (W ω) t := by
    rw [s.observationTranslationDerivative_eq_taylor ν μ ξ (W ω) ht]
    exact s.oneObservation_operator_identity ν μ ξ hξ hbound (W ω) t
  rw [integral_congr_ae (ae_of_all _ heq),
    integral_add (f := fun ω => -B₂ ω / 2 - t / 3 * B₃ ω)
      (g := fun ω => s.correctedOneObservationResidual ν μ ξ (W ω) t)
      (((h₂.neg).div_const 2).sub (h₃.const_mul (t / 3))) hR,
    integral_sub (f := fun ω => -B₂ ω / 2) (g := fun ω => t / 3 * B₃ ω)
      ((h₂.neg).div_const 2) (h₃.const_mul (t / 3)),
    integral_div, integral_neg, integral_const_mul]
  have e₂ : (∫ ω, B₂ ω ∂μ) = ∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
      ∫ ω, s.bernoulliMeanSecondDerivative ν μ ξ (W ω) t j k ∂μ := by
    unfold B₂
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (hi₂ j k).const_mul _))]
    simp_rw [integral_finset_sum Finset.univ (fun k _ => (hi₂ _ k).const_mul _), integral_const_mul]
  have e₃ : (∫ ω, B₃ ω ∂μ) = ∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
      ∫ ω, s.bernoulliMeanThirdDerivative ν μ ξ (W ω) t j k l ∂μ := by
    unfold B₃
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => (hi₃ j k l).const_mul _)))]
    simp_rw [integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => (hi₃ _ k l).const_mul _)),
      integral_finset_sum Finset.univ (fun l _ => (hi₃ _ _ l).const_mul _), integral_const_mul]
  rw [e₂, e₃]


private theorem weighted_sum_three {α : Type*} [Fintype α]
    (w f g r : α → ℝ) (c d : ℝ) :
    (∑ z, w z * (c * f z + d * g z + r z)) =
      c * (∑ z, w z * f z) + d * (∑ z, w z * g z) + ∑ z, w z * r z := by
  calc
    _ = ∑ z, (c * (w z * f z) + d * (w z * g z) + w z * r z) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem weighted_second_contraction {α : Type*} [Fintype α]
    (w : α → ℝ) (M : Fin p → Fin p → ℝ) (D : α → Fin p → Fin p → ℝ) :
    (∑ z, w z * ∑ j, ∑ k, M j k * D z j k) =
      ∑ j, ∑ k, M j k * ∑ z, w z * D z j k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem weighted_third_contraction {α : Type*} [Fintype α]
    (w : α → ℝ) (M : Fin p → Fin p → Fin p → ℝ)
    (D : α → Fin p → Fin p → Fin p → ℝ) :
    (∑ z, w z * ∑ j, ∑ k, ∑ l, M j k l * D z j k l) =
      ∑ j, ∑ k, ∑ l, M j k l * ∑ z, w z * D z j k l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- One fixed observation's exact retained operator, averaged over the
selectors and the original independent observations. -/
theorem sum_mask_integral_observationTranslationDerivative_eq_commonPoint
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (i : Fin n) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    (∑ mask, Kane.maskWeight (thinningProbability t) mask *
      ∫ ω, s.observationTranslationDerivative ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) =
      -(∑ j, ∑ k, (∫ ω, ξ i ω j * ξ i ω k ∂μ) *
        s.selectorSecondDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k) / 2 -
      t / 3 * (∑ j, ∑ k, ∑ l, (∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
        s.selectorThirdDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k l) +
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, s.correctedOneObservationResidual ν μ (ξ i)
          (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ := by
  let W : Kane.Cube n → Ω → Vector p := fun mask ω =>
    x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω
  let M₂ := fun j k => ∫ ω, ξ i ω j * ξ i ω k ∂μ
  let M₃ := fun j k l => ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ
  let D₂ := fun mask j k => ∫ ω, s.bernoulliMeanSecondDerivative ν μ (ξ i) (W mask ω) t j k ∂μ
  let D₃ := fun mask j k l => ∫ ω, s.bernoulliMeanThirdDerivative ν μ (ξ i) (W mask ω) t j k l ∂μ
  let R := fun mask => ∫ ω, s.correctedOneObservationResidual ν μ (ξ i) (W mask ω) t ∂μ
  have hw (mask : Kane.Cube n) : Measurable (W mask) := measurable_const.add
    (measurable_const.smul (measurable_maskObservationSum ξ hξ (Function.update mask i false)))
  have heq (mask : Kane.Cube n) :
      (∫ ω, s.observationTranslationDerivative ν μ (ξ i) (W mask ω) t ∂μ) =
        (-1 / 2 : ℝ) * (∑ j, ∑ k, M₂ j k * D₂ mask j k) +
          (-t / 3) * (∑ j, ∑ k, ∑ l, M₃ j k l * D₃ mask j k l) + R mask := by
    have hh := s.integral_observationTranslationDerivative_eq_corrected ν μ (ξ i) (W mask)
      (hξ i) (hw mask) hδ (hbound i) ht
    change _ = (-1 / 2 : ℝ) * _ + (-t / 3) * _ + _
    dsimp only [M₂, M₃, D₂, D₃, R]
    rw [hh]
    ring
  change (∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.observationTranslationDerivative ν μ (ξ i) (W mask ω) t ∂μ) = _
  simp_rw [heq]
  rw [weighted_sum_three]
  rw [weighted_second_contraction, weighted_third_contraction]
  have hc₂ (j k : Fin p) :
      (∑ mask, Kane.maskWeight (thinningProbability t) mask * D₂ mask j k) =
        s.selectorSecondDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k :=
    s.sum_mask_bernoulliMeanSecondDerivative ν μ ξ hξ hind hbound i x t j k
  have hc₃ (j k l : Fin p) :
      (∑ mask, Kane.maskWeight (thinningProbability t) mask * D₃ mask j k l) =
        s.selectorThirdDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k l :=
    s.sum_mask_bernoulliMeanThirdDerivative ν μ ξ hξ hind hbound i x t j k l
  simp_rw [hc₂, hc₃]
  dsimp only [M₂, M₃, R, W]
  ring


private theorem sum_second_contraction {n : ℕ}
    (M : Fin n → Fin p → Fin p → ℝ) (D : Fin p → Fin p → ℝ) :
    (∑ i, ∑ j, ∑ k, M i j k * D j k) =
      ∑ j, ∑ k, (∑ i, M i j k) * D j k := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem sum_third_contraction {n : ℕ}
    (M : Fin n → Fin p → Fin p → Fin p → ℝ) (D : Fin p → Fin p → Fin p → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, M i j k l * D j k l) =
      ∑ j, ∑ k, ∑ l, (∑ i, M i j k l) * D j k l := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

omit [IsProbabilityMeasure ν] in
/-- Weighted heat differentiation is the common full-point Hessian
contracted with the Gaussian covariance matrix. -/
theorem sum_mask_fixedSelectorHeat_eq
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q a : ℝ) :
    (∑ mask, Kane.maskWeight q mask * s.fixedSelectorHeat ν μ ξ Q x a mask) =
      (1 / 2 : ℝ) * ∑ j, ∑ k, Q j k *
        s.selectorSecondDerivativeAverage ν μ ξ x q a j k := by
  unfold fixedSelectorHeat selectorSecondDerivativeAverage
  calc
    _ = (1 / 2 : ℝ) * ∑ mask, Kane.maskWeight q mask *
        ∑ j, ∑ k, Q j k * ∫ ω,
          s.convolutionSecondDerivative ν (x + a • maskObservationSum ξ mask ω) j k ∂μ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by rw [weighted_second_contraction]

/-- Exact global common-point identity for the actual Bernoulli--Gaussian
path derivative. The third moments remain signed and are summed before any
absolute value. Centering is needed only for the later fourth-order bound. -/
theorem selectorHeatDerivative_eq_commonPoint
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorHeatDerivative μ ξ A x t =
      (1 / 2 : ℝ) * (∑ j, ∑ k,
        ((A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ)) *
          s.selectorSecondDerivativeAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
            (thinningProbability t) (thinningScale t) j k) -
      t / 3 * (∑ j, ∑ k, ∑ l,
        (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
          s.selectorThirdDerivativeAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
            (thinningProbability t) (thinningScale t) j k l) +
      s.selectorCorrectedResidual (gaussianLaw (Real.sqrt t • A)) μ ξ x t := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let q := thinningProbability t
  let a := thinningScale t
  let c := (t - 3) / (1 + t) ^ 3
  let V := fun mask => s.fixedSelectorValue ν μ ξ x a mask
  let G := fun i mask => s.fixedSelectorGradient ν μ ξ x a i mask
  let M₂ := fun i j k => ∫ ω, ξ i ω j * ξ i ω k ∂μ
  let M₃ := fun i j k l => ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ
  let D₂ := s.selectorSecondDerivativeAverage ν μ ξ x q a
  let D₃ := s.selectorThirdDerivativeAverage ν μ ξ x q a
  let R := fun i => ∑ mask, Kane.maskWeight q mask *
    ∫ ω, s.correctedOneObservationResidual ν μ (ξ i)
      (x + a • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ
  let heat := ∑ mask, Kane.maskWeight q mask *
    s.fixedSelectorHeat ν μ ξ (A * A.transpose) x a mask
  have hforced : s.selectorHeatDerivative μ ξ A x t =
      (∑ i, ∑ mask, Kane.maskWeight q mask *
        ∫ ω, s.observationTranslationDerivative ν μ (ξ i)
          (x + a • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) +
      ∑ mask, Kane.maskWeight q mask * s.fixedSelectorHeat ν μ ξ (A * A.transpose) x a mask := by
    rw [s.selectorHeatDerivative_eq_forced_increments μ ξ hξ hδ hbound A x t]
    change c * (∑ i, ∑ mask, Kane.maskWeight q mask *
        (V (Function.update mask i true) - V (Function.update mask i false))) +
      q * (∑ i, ∑ mask, Kane.maskWeight q mask * G i (Function.update mask i true)) + heat = _
    calc
      _ = (∑ i, ∑ mask,
          (c * (Kane.maskWeight q mask *
            (V (Function.update mask i true) - V (Function.update mask i false))) +
            q * (Kane.maskWeight q mask * G i (Function.update mask i true)))) + heat := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ i, ∑ mask, Kane.maskWeight q mask *
          (c * (V (Function.update mask i true) - V (Function.update mask i false)) +
            q * G i (Function.update mask i true))) + heat := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro mask _
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro mask _
        congr 1
        exact s.forced_increment_eq_integral_observationTranslationDerivative
          ν μ ξ hξ hind hδ hbound mask i x t
  have hone (i : Fin n) :
      (∑ mask, Kane.maskWeight q mask *
        ∫ ω, s.observationTranslationDerivative ν μ (ξ i)
          (x + a • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) =
        (-1 / 2 : ℝ) * (∑ j, ∑ k, M₂ i j k * D₂ j k) +
          (-t / 3) * (∑ j, ∑ k, ∑ l, M₃ i j k l * D₃ j k l) + R i := by
    have hh := s.sum_mask_integral_observationTranslationDerivative_eq_commonPoint
      ν μ ξ hξ hind hδ hbound i x ht
    change _ = (-1 / 2 : ℝ) * _ + (-t / 3) * _ + _
    dsimp only [M₂, M₃, D₂, D₃, R, q, a]
    rw [hh]
    ring
  rw [hforced]
  simp_rw [hone]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_second_contraction, sum_third_contraction,
    s.sum_mask_fixedSelectorHeat_eq ν μ ξ (A * A.transpose) x q a]
  change (-1 / 2 : ℝ) * (∑ j, ∑ k, (∑ i, M₂ i j k) * D₂ j k) +
      (-t / 3) * (∑ j, ∑ k, ∑ l, (∑ i, M₃ i j k l) * D₃ j k l) +
      (∑ i, R i) + (1 / 2 : ℝ) * (∑ j, ∑ k, (A * A.transpose) j k * D₂ j k) = _
  have hdiff : (∑ j, ∑ k, ((A * A.transpose) j k - (∑ i, M₂ i j k)) * D₂ j k) =
      (∑ j, ∑ k, (A * A.transpose) j k * D₂ j k) -
        ∑ j, ∑ k, (∑ i, M₂ i j k) * D₂ j k := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  change _ = (1 / 2 : ℝ) * (∑ j, ∑ k,
    ((A * A.transpose) j k - (∑ i, M₂ i j k)) * D₂ j k) -
    t / 3 * (∑ j, ∑ k, ∑ l, (∑ i, M₃ i j k l) * D₃ j k l) + ∑ i, R i
  rw [hdiff]
  ring

end FaceSmoother
end RectangleCLT
