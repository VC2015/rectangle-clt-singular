import RectangleCLT.BernoulliComparison
import RectangleCLT.ThinningMoments
import RectangleCLT.LocalMoments

/-! The concrete thinned array satisfies the independent bounded-data
hypotheses used by short-scale envelope averaging. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.BoundedIndependentHypotheses

theorem thinned
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    BoundedIndependentHypotheses (bernoulliArrayLaw μ ξ t)
      (fun i (b : Fin n → Vector p) => b i) (2 * δ) := by
  refine ⟨fun i => measurable_pi_apply i,
    bernoulliArrayLaw_independent μ ξ h.measurable h.independent t ht ht1, ?_,
    bernoulliArrayLaw_bounded μ ξ h.measurable h.delta_nonneg h.bounded t ht ht1,
    mul_nonneg (by norm_num) h.delta_nonneg⟩
  apply bernoulliArrayLaw_centered μ ξ h.measurable t ht ht1 _ h.centered
  intro i j
  simpa only [pow_one] using
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1

theorem thinned_sum_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    covariance (bernoulliArrayLaw μ ξ t)
      (sumVector (fun i (b : Fin n → Vector p) => b i)) =
      (1 - t) • covariance μ (sumVector ξ) := by
  exact bernoulliArrayLaw_sum_covariance_of_bounded μ ξ h.measurable h.independent
    h.centered h.abs_coordinate_le t ht ht1

theorem thinned_sum_unit_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : Fin p) :
    covariance (bernoulliArrayLaw μ ξ t)
      (sumVector (fun i (b : Fin n → Vector p) => b i)) j j = 1 - t := by
  rw [h.thinned_sum_covariance t ht ht1]
  simp only [Matrix.smul_apply, smul_eq_mul, hunit, mul_one]

end RectangleCLT.BoundedIndependentHypotheses
