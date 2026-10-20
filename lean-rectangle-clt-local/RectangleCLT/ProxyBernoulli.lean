import RectangleCLT.BernoulliComparisonBound
import RectangleCLT.ProxyCovariance

/-!
# The unequal-covariance Bernoulli comparison

The Gaussian factor in this file is arbitrary. The exact common-point
identity leaves a quadratic covariance discrepancy, while the signed
aggregate third tensor and the genuine fourth-order residual retain their
matched-covariance bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The sum of absolute Hessian entries after averaging at the actual
full Bernoulli sum. -/
noncomputable def selectorSecondAbsoluteSum
    (ν : Measure (Vector p)) {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ j, ∑ k, |s.selectorSecondDerivativeAverage ν μ ξ x q a j k|

theorem selectorSecondAbsoluteSum_nonneg
    (ν : Measure (Vector p)) {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) :
    0 ≤ s.selectorSecondAbsoluteSum ν μ ξ x q a := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The covariance discrepancy contracts against the true common-point
Hessian. No covariance matching premise is used. -/
theorem abs_proxy_second_contraction_le
    (ν : Measure (Vector p)) {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q a : ℝ) :
    |∑ j, ∑ k,
      ((A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ)) *
        s.selectorSecondDerivativeAverage ν μ ξ x q a j k| ≤
      proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        s.selectorSecondAbsoluteSum ν μ ξ x q a := by
  have hentry (j k : Fin p) :
      |(A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ)| ≤
        proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) := by
    rw [← h.covariance_sum, abs_sub_comm]
    exact abs_entry_sub_le_proxyCovarianceDiscrepancy _ _ j k
  unfold selectorSecondAbsoluteSum
  simp only [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hentry j k) (abs_nonneg _)

/-- Actual path-derivative comparison with unequal covariances, preserving
the aggregate third-moment cancellation. -/
theorem abs_selectorHeatDerivative_le_proxy_cubic_add_residual
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      (1 / 2 : ℝ) *
        proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
      t / 3 * gamma3 μ ξ *
        s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
      |s.selectorCorrectedResidual (gaussianLaw (Real.sqrt t • A)) μ ξ x t| := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let Q := ∑ j, ∑ k,
      ((A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ)) *
        s.selectorSecondDerivativeAverage ν μ ξ x
          (thinningProbability t) (thinningScale t) j k
  let T := ∑ j, ∑ k, ∑ l,
      (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
        s.selectorThirdDerivativeAverage ν μ ξ x
          (thinningProbability t) (thinningScale t) j k l
  have hQ := s.abs_proxy_second_contraction_le ν μ ξ h A x
    (thinningProbability t) (thinningScale t)
  have hT := s.abs_aggregate_third_contraction_le ν μ ξ h.measurable x
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) (thinningScale t)
  rw [s.selectorHeatDerivative_eq_commonPoint μ ξ h.measurable h.independent
    h.delta_nonneg h.bounded A x ht]
  change |(1 / 2 : ℝ) * Q - t / 3 * T + _| ≤ _
  calc
    _ ≤ |(1 / 2 : ℝ) * Q - t / 3 * T| +
        |s.selectorCorrectedResidual ν μ ξ x t| := abs_add _ _
    _ ≤ (|(1 / 2 : ℝ) * Q| + |t / 3 * T|) +
        |s.selectorCorrectedResidual ν μ ξ x t| :=
      add_le_add_right (abs_sub _ _) _
    _ = (1 / 2 : ℝ) * |Q| + t / 3 * |T| +
        |s.selectorCorrectedResidual ν μ ξ x t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg ht (by norm_num))]
      norm_num
    _ ≤ (1 / 2 : ℝ) *
        (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
          s.selectorSecondAbsoluteSum ν μ ξ x (thinningProbability t) (thinningScale t)) +
        t / 3 * (gamma3 μ ξ *
          s.selectorThirdAbsoluteAverage ν μ ξ x (thinningProbability t) (thinningScale t)) +
        |s.selectorCorrectedResidual ν μ ξ x t| := by
      exact add_le_add_right
        (add_le_add (mul_le_mul_of_nonneg_left hQ (by norm_num))
          (mul_le_mul_of_nonneg_left hT (div_nonneg ht (by norm_num)))) _
    _ = _ := by ring

/-- The fourth-order term is the same actual local derivative envelope as
in the bounded matched theorem. The Gaussian covariance remains free. -/
theorem abs_selectorHeatDerivative_le_proxy_comparison
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ y z : Vector p, ‖z‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (y + z) j k l m| ≤
        H y j k l m)
    (hHi : ∀ mask : Kane.Cube n, Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m) μ) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      (1 / 2 : ℝ) *
        proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
      t / 3 * gamma3 μ ξ *
        s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
      6 * gamma4 μ ξ * selectorFourthEnvelopeAverage μ ξ x t H := by
  exact (s.abs_selectorHeatDerivative_le_proxy_cubic_add_residual μ ξ h A x ht ht1).trans
    (add_le_add_left (s.abs_selectorCorrectedResidual_le_gamma4
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable h.delta_nonneg h.bounded h.centered
      x ht ht1 H hH hHi) _)

end RectangleCLT.FaceSmoother
