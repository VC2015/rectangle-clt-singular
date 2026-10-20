import RectangleCLT.SharpMasterAssembly
import RectangleCLT.GaussianTubeFaceBounds
import RectangleCLT.ThinnedHypotheses

/-! Actual Bernoulli-selector law bridges for the localized fourth Gaussian
derivative estimates. The retained observations keep their genuine mixture
law; no interpolation distribution is replaced by a deterministic mask. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem integral_bernoulliArrayLaw_comp_arraySum_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Vector p → ℝ) (hG : Measurable G)
    (hGi : ∀ mask : Kane.Cube n,
      Integrable (fun b : Fin n → Vector p => G (arraySum b))
        (μ.map (retainedArray ξ t mask))) :
    (∫ b, G (arraySum b) ∂bernoulliArrayLaw μ ξ t) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, G (thinningScale t • maskObservationSum ξ mask ω) ∂μ := by
  have hm : Measurable (fun b : Fin n → Vector p => G (arraySum b)) :=
    hG.comp (measurable_arraySum p n)
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _ hGi]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hm.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun ω => by
    change G (arraySum (retainedArray ξ t mask ω)) = _
    rw [arraySum_retainedArray_eq_maskObservationSum]))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The expected sum of the genuine coordinatewise local fourth-derivative
suprema is exactly its integral under the actual retained-array law. -/
theorem sharpFourthAverage_eq_integral_bernoulliArrayLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.sharpFourthAverage μ ξ A δ t =
      ∫ b, ∑ j, ∑ k, ∑ l, ∑ m,
        s.localConvolutionFourthSup A (4 * δ) (arraySum b) t j k l m
        ∂bernoulliArrayLaw μ ξ t := by
  let G : Vector p → ℝ := fun y => ∑ j, ∑ k, ∑ l, ∑ m,
    s.localConvolutionFourthSup A (4 * δ) y t j k l m
  have hpair : Continuous (fun y : Vector p => (y, t)) :=
    continuous_id.prodMk continuous_const
  have hentry (j k l m : Fin p) :
      Measurable (fun y : Vector p => s.localConvolutionFourthSup A (4 * δ) y t j k l m) :=
    ((s.continuous_localConvolutionFourthSup A (4 * δ) j k l m).comp hpair).measurable
  have hG : Measurable G := by
    unfold G
    exact Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun k _ =>
      Finset.measurable_sum _ (fun l _ => Finset.measurable_sum _ (fun m _ => hentry j k l m))))
  have hGi (mask : Kane.Cube n) :
      Integrable (fun b : Fin n → Vector p => G (arraySum b))
        (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_localConvolutionFourthSup_comp A (by positivity) t
              (μ.map (retainedArray ξ t mask))
              arraySum (measurable_arraySum p n) j k l m))))
  have hi := integral_bernoulliArrayLaw_comp_arraySum_eq_sum μ ξ hξ ht ht1 G hG hGi
  change s.sharpFourthAverage μ ξ A δ t = ∫ b, G (arraySum b) ∂bernoulliArrayLaw μ ξ t
  calc
    _ = selectorFourthEnvelopeAverage μ ξ 0 t
        (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m) :=
      s.sharpFourthAverage_eq_selectorEnvelope μ ξ hξ A hδ t
    _ = ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, G (thinningScale t • maskObservationSum ξ mask ω) ∂μ := by
      unfold selectorFourthEnvelopeAverage
      simp only [zero_add]
      rfl
    _ = _ := hi.symm

end FaceSmoother
end
end RectangleCLT
