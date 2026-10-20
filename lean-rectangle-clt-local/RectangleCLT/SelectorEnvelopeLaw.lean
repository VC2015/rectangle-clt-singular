import RectangleCLT.ConvolutionEnvelopes
import RectangleCLT.BernoulliComparisonBound

/-! The concrete full-point convolution envelope is the expectation under
the actual Bernoulli-array law and the actual independent convolution law. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

/-- The sum of the actual rescaled retained observations. -/
theorem arraySum_retainedArray_eq_maskObservationSum
    {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (t : ℝ) (mask : Kane.Cube n) (ω : Ω) :
    arraySum (retainedArray ξ t mask ω) = thinningScale t • maskObservationSum ξ mask ω := by
  unfold arraySum maskObservationSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : mask i <;> simp [retainedArray, hi]

private theorem integral_bernoulliArrayLaw_comp_eq_sum
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Vector p → ℝ) (hG : Measurable G)
    (hGi : ∀ mask : Kane.Cube n, Integrable (fun b : Fin n → Vector p => G (x + arraySum b))
      (μ.map (retainedArray ξ t mask))) :
    (∫ b, G (x + arraySum b) ∂bernoulliArrayLaw μ ξ t) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, G (x + thinningScale t • maskObservationSum ξ mask ω) ∂μ := by
  have hm : Measurable (fun b : Fin n → Vector p => G (x + arraySum b)) :=
    hG.comp (measurable_const.add (measurable_arraySum p n))
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _ hGi]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hm.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun ω => by
    change G (x + arraySum (retainedArray ξ t mask ω)) = _
    rw [arraySum_retainedArray_eq_maskObservationSum]))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- The `hHi` integrability premise of the common-point residual estimate
holds for the concrete convolution local majorant. -/
theorem integrable_sum_convolutionFourthLocalMajorant_mask
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (x : Vector p) (a : ℝ) (mask : Kane.Cube n) :
    Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      s.convolutionFourthLocalMajorant ν (x + a • maskObservationSum ξ mask ω) j k l m) μ := by
  have hW : Measurable (fun ω => x + a • maskObservationSum ξ mask ω) := measurable_const.add
    (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))
  exact integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_convolutionFourthLocalMajorant_comp ν μ _ hW j k l m))))

/-- Exact full-point law bridge. The selector-weighted fourth envelope is
the expectation of the positive actual smoother majorants under the genuine
Bernoulli-array law followed by the independent convolution law. -/
theorem selectorFourthEnvelopeAverage_eq_integral_bernoulliArrayLaw
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    selectorFourthEnvelopeAverage μ ξ x t (s.convolutionFourthLocalMajorant ν) =
      ∫ b, ∫ z, ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant (x + arraySum b + z) j k l m ∂ν ∂bernoulliArrayLaw μ ξ t := by
  let G : Vector p → ℝ := fun y => ∑ j, ∑ k, ∑ l, ∑ m,
    s.convolutionFourthLocalMajorant ν y j k l m
  have hG : Continuous G := continuous_finset_sum _ (fun j _ =>
    continuous_finset_sum _ (fun k _ => continuous_finset_sum _ (fun l _ =>
      continuous_finset_sum _ (fun m _ => s.continuous_convolutionFourthLocalMajorant ν j k l m))))
  have hGi (mask : Kane.Cube n) :
      Integrable (fun b : Fin n → Vector p => G (x + arraySum b)) (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_convolutionFourthLocalMajorant_comp ν _ _
              (measurable_const.add (measurable_arraySum p n)) j k l m))))
  calc
    _ = ∫ b, G (x + arraySum b) ∂bernoulliArrayLaw μ ξ t :=
      (integral_bernoulliArrayLaw_comp_eq_sum μ ξ hξ x ht ht1 G hG.measurable hGi).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun b =>
      s.sum_convolutionFourthLocalMajorant_eq_integral ν (x + arraySum b)))

/-- The same full-point identity as one actual product-law integral. -/
theorem selectorFourthEnvelopeAverage_eq_prod_integral
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    selectorFourthEnvelopeAverage μ ξ x t (s.convolutionFourthLocalMajorant ν) =
      ∫ w, ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant (x + arraySum w.1 + w.2) j k l m
        ∂(bernoulliArrayLaw μ ξ t).prod ν := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have hW : Measurable (fun w : (Fin n → Vector p) × Vector p => x + arraySum w.1 + w.2) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add measurable_snd
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_fourthLocalMajorant_comp ((bernoulliArrayLaw μ ξ t).prod ν) _ hW j k l m))))
  rw [s.selectorFourthEnvelopeAverage_eq_integral_bernoulliArrayLaw ν μ ξ hξ x ht ht1]
  exact (integral_prod _ hi).symm


/-- Actual full-point third derivatives are bounded by the positive third
majorants under the same genuine independent product law. -/
theorem selectorThirdAbsoluteAverage_le_prod_integral
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorThirdAbsoluteAverage ν μ ξ x (thinningProbability t) (thinningScale t) ≤
      ∫ w, ∑ j, ∑ k, ∑ l,
        s.thirdLocalMajorant (x + arraySum w.1 + w.2) j k l
        ∂(bernoulliArrayLaw μ ξ t).prod ν := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  let G : Vector p → ℝ := fun y => ∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative ν y j k l|
  have hG : Continuous G := continuous_finset_sum _ (fun j _ =>
    continuous_finset_sum _ (fun k _ => continuous_finset_sum _ (fun l _ =>
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l).abs)))
  have hentry (ρ : Measure (Fin n → Vector p)) [IsFiniteMeasure ρ] (j k l : Fin p) :
      Integrable (fun b => |s.convolutionThirdDerivative ν (x + arraySum b) j k l|) ρ :=
    (integrable_bounded_test_comp ρ _ (measurable_const.add (measurable_arraySum p n)) _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)).abs
  have hGi (mask : Kane.Cube n) :
      Integrable (fun b : Fin n → Vector p => G (x + arraySum b)) (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => hentry _ j k l)))
  have hiL : Integrable (fun b : Fin n → Vector p => G (x + arraySum b)) (bernoulliArrayLaw μ ξ t) :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => hentry _ j k l)))
  have hW : Measurable (fun w : (Fin n → Vector p) × Vector p => x + arraySum w.1 + w.2) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add measurable_snd
  have hiR := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        s.integrable_thirdLocalMajorant_comp ((bernoulliArrayLaw μ ξ t).prod ν) _ hW j k l)))
  calc
    _ = ∫ b, G (x + arraySum b) ∂bernoulliArrayLaw μ ξ t :=
      (integral_bernoulliArrayLaw_comp_eq_sum μ ξ hξ x ht ht1 G hG.measurable hGi).symm
    _ ≤ ∫ b, ∫ z, ∑ j, ∑ k, ∑ l,
        s.thirdLocalMajorant (x + arraySum b + z) j k l ∂ν ∂bernoulliArrayLaw μ ξ t :=
      integral_mono hiL hiR.integral_prod_left (fun b =>
        s.sum_abs_convolutionThirdDerivative_le_integral_majorant ν (x + arraySum b))
    _ = _ := (integral_prod _ hiR).symm

end FaceSmoother
end RectangleCLT
