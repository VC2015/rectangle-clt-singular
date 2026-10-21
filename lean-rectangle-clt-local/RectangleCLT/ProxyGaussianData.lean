import RectangleCLT.ProxyStatement
import RectangleCLT.InterpolationCovariance
import RectangleCLT.BoundedMaximum

/-! Actual law and covariance of the bounded sum plus its independent
Gaussian component. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.ProxyHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {G : Ω → Vector p} {δ : ℝ}
  {B : Matrix (Fin p) (Fin p) ℝ}

theorem measurable_sumWithGaussian (h : ProxyHypotheses μ ξ G δ B) :
    Measurable (sumWithGaussian ξ G) :=
  h.boundedIndependent.measurable_sum.add h.measurableGaussian

theorem independent_sumVector_gaussian (h : ProxyHypotheses μ ξ G δ B) :
    IndepFun (sumVector ξ) G μ := by
  simpa only [Function.comp_def, arraySum, sumVector] using
    h.independentGaussian.comp (measurable_arraySum p n) measurable_id

/-- The complete vector has exactly the independent convolution law. -/
theorem sumWithGaussian_map (h : ProxyHypotheses μ ξ G δ B) :
    μ.map (sumWithGaussian ξ G) =
      ((μ.map (sumVector ξ)).prod (gaussianLaw B)).map
        (fun z : Vector p × Vector p => z.1 + z.2) := by
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map
    h.boundedIndependent.measurable_sum.aemeasurable h.measurableGaussian.aemeasurable).mp
      h.independent_sumVector_gaussian
  calc
    _ = (μ.map (fun ω => (sumVector ξ ω, G ω))).map
        (fun z : Vector p × Vector p => z.1 + z.2) := by
      rw [Measure.map_map (measurable_fst.add measurable_snd)
        (h.boundedIndependent.measurable_sum.prodMk h.measurableGaussian)]
      rfl
    _ = _ := by rw [hjoint, h.gaussianLaw_eq]

/-- The Gaussian component contributes its actual factor covariance to
the covariance of the bounded independent sum. -/
theorem covariance_sumWithGaussian (h : ProxyHypotheses μ ξ G δ B) :
    covariance μ (sumWithGaussian ξ G) =
      covariance μ (sumVector ξ) + B * B.transpose := by
  let V := sumVector ξ
  let ν := μ.map V
  let C : ℝ := (n : ℝ) * δ
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_map h.boundedIndependent.measurable_sum.aemeasurable
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n) h.boundedIndependent.delta_nonneg
  have hcoord (j : Fin p) : ∀ᵐ ω ∂μ, |V ω j| ≤ C := by
    filter_upwards [h.boundedIndependent.sum_norm_bound] with ω hω
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (V ω) j).trans hω
  have hIV (j : Fin p) : Integrable (fun ω => V ω j) μ := by
    apply (integrable_const C).mono'
      (((measurable_pi_apply j).comp h.boundedIndependent.measurable_sum).aestronglyMeasurable)
    simpa only [Real.norm_eq_abs] using hcoord j
  have hIVV (j k : Fin p) : Integrable (fun ω => V ω j * V ω k) μ := by
    apply (integrable_const (C ^ 2)).mono'
      ((((measurable_pi_apply j).comp h.boundedIndependent.measurable_sum).mul
        ((measurable_pi_apply k).comp h.boundedIndependent.measurable_sum)).aestronglyMeasurable)
    filter_upwards [hcoord j, hcoord k] with ω hj hk
    simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
      mul_le_mul hj hk (abs_nonneg _) hC
  have hIν (j : Fin p) : Integrable (fun x : Vector p => x j) ν :=
    (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
      h.boundedIndependent.measurable_sum.aemeasurable).mpr (hIV j)
  have hIνν (j k : Fin p) : Integrable (fun x : Vector p => x j * x k) ν :=
    (integrable_map_measure
      ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable
      h.boundedIndependent.measurable_sum.aemeasurable).mpr (hIVV j k)
  have hmean (j : Fin p) : (∫ x : Vector p, x j ∂ν) = 0 := by
    change (∫ x : Vector p, x j ∂μ.map (sumVector ξ)) = 0
    rw [integral_map h.boundedIndependent.measurable_sum.aemeasurable
      (measurable_pi_apply j).aestronglyMeasurable]
    have hobs (i : Fin n) : Integrable (fun ω => ξ i ω j) μ := by
      apply (integrable_const δ).mono'
        (((measurable_pi_apply j).comp (h.boundedIndependent.measurable i)).aestronglyMeasurable)
      simpa only [Real.norm_eq_abs] using h.boundedIndependent.abs_coordinate_le i j
    simp only [sumVector, Finset.sum_apply]
    rw [integral_finset_sum Finset.univ (fun i _ => hobs i)]
    simp only [h.boundedIndependent.centered, Finset.sum_const_zero]
  calc
    _ = covariance (μ.map (sumWithGaussian ξ G)) id :=
      (covariance_map μ _ h.measurable_sumWithGaussian).symm
    _ = covariance (ν.prod (gaussianLaw B))
        (fun z : Vector p × Vector p => z.1 + z.2) := by
      rw [h.sumWithGaussian_map, covariance_map _ _ (measurable_fst.add measurable_snd)]
    _ = covariance ν id + covariance (gaussianLaw B) id :=
      covariance_prod_add_of_centered ν (gaussianLaw B) id id
        hIν (gaussianLaw_integrable_coordinate B)
        hIνν (gaussianLaw_integrable_coordinate_product B)
        hmean (gaussianLaw_integral_coordinate B)
    _ = _ := by
      rw [covariance_map μ V h.boundedIndependent.measurable_sum, covariance_gaussianLaw]

end RectangleCLT.ProxyHypotheses
