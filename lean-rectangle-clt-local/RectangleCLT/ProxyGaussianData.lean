import RectangleCLT.ProxyStatement
import RectangleCLT.InterpolationCovariance
import RectangleCLT.BoundedMaximum
import RectangleCLT.IndependentCovariance
import Mathlib.Data.Real.StarOrdered

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

namespace RectangleCLT.BoundedIndependentHypotheses

/-- Positivity of the actual bounded-sum covariance, with no spectral or
local nondegeneracy hypothesis. -/
theorem covariance_posSemidef
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) :
    (covariance μ (sumVector ξ)).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact covariance_transpose μ (sumVector ξ)
  · intro v
    have hp (i : Fin n) (j k : Fin p) :
        Integrable (fun ω => ξ i ω j * ξ i ω k) μ := by
      apply (integrable_const (δ ^ 2)).mono'
        ((((measurable_pi_apply j).comp (h.measurable i)).mul
          ((measurable_pi_apply k).comp (h.measurable i))).aestronglyMeasurable)
      filter_upwards [h.abs_coordinate_le i j, h.abs_coordinate_le i k] with ω hj hk
      simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
        mul_le_mul hj hk (abs_nonneg _) h.delta_nonneg
    have hcontract (M : Fin n → Fin p → Fin p → ℝ) :
        (∑ i, ∑ j, ∑ k, M i j k * v j * v k) =
          ∑ j, ∑ k, (∑ i, M i j k) * v j * v k := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    have hquad : matrixQuadratic (covariance μ (sumVector ξ)) v =
        ∑ i, ∫ ω, (∑ j, v j * ξ i ω j) ^ 2 ∂μ := by
      calc
        _ = ∑ j, ∑ k, (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ) * v j * v k := by
          unfold matrixQuadratic
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [h.covariance_sum]
          ring
        _ = ∑ i, ∑ j, ∑ k, (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v j * v k :=
          (hcontract _).symm
        _ = ∑ i, ∫ ω, (∑ j, v j * ξ i ω j) ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          have hi (j k : Fin p) := ((hp i j k).mul_const (v j)).mul_const (v k)
          calc
            _ = ∑ j, ∑ k, ∫ ω, ξ i ω j * ξ i ω k * v j * v k ∂μ := by
              simp only [integral_mul_const]
            _ = ∫ ω, ∑ j, ∑ k, ξ i ω j * ξ i ω k * v j * v k ∂μ := by
              rw [integral_finset_sum Finset.univ (fun j _ =>
                integrable_finset_sum Finset.univ (fun k _ => hi j k))]
              apply Finset.sum_congr rfl
              intro j _
              rw [integral_finset_sum Finset.univ (fun k _ => hi j k)]
            _ = _ := by
              apply integral_congr_ae
              exact ae_of_all _ (fun ω => by
                change (∑ j, ∑ k, ξ i ω j * ξ i ω k * v j * v k) =
                  (∑ j, v j * ξ i ω j) ^ 2
                rw [pow_two, Finset.sum_mul]
                simp only [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                apply Finset.sum_congr rfl
                intro k _
                ring)
    have hnon : 0 ≤ matrixQuadratic (covariance μ (sumVector ξ)) v := by
      rw [hquad]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => sq_nonneg _))
    simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hnon

end RectangleCLT.BoundedIndependentHypotheses

namespace RectangleCLT.ProxyHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {G : Ω → Vector p} {δ : ℝ}
  {B : Matrix (Fin p) (Fin p) ℝ}

theorem covariance_posSemidef (h : ProxyHypotheses μ ξ G δ B) :
    (covariance μ (sumWithGaussian ξ G)).PosSemidef := by
  rw [h.covariance_sumWithGaussian]
  have hB : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  exact h.boundedIndependent.covariance_posSemidef.add hB

/-- The actual-covariance Gaussian target always exists, including when the
full covariance is singular. The public target quantifier is nonvacuous. -/
theorem gaussian_factor_exists (h : ProxyHypotheses μ ξ G δ B) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumWithGaussian ξ G) := by
  let hCov := h.covariance_posSemidef
  refine ⟨hCov.sqrt, ?_⟩
  have hsymmetric : hCov.sqrt.transpose = hCov.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hCov.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hCov.sqrt_mul_self

end RectangleCLT.ProxyHypotheses
