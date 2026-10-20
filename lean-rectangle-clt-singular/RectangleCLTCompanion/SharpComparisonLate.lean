import RectangleCLTCompanion.FourthIdentitySelectorFubini
import RectangleCLTCompanion.SharpComparisonKernels

/-! Assembly of late-time comparison from restoration estimates on the
actual signed derivative integrands. The analytic restoration estimates are
explicit hypotheses here; this module alone does not prove the sharp CLT. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

theorem abs_selectorCorrectedResidual_le_of_fourthIntegrands
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (x : Vector p)
    {t K : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hA : ∀ r ∈ Set.Icc (0 : ℝ) 1, |s.fourthPathIntegrandA ν μ ξ x t r| ≤ K)
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) 1, |s.fourthPathIntegrandB ν μ ξ x t r| ≤ K)
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) 1, |s.fourthPathIntegrandC ν μ ξ x t r| ≤ K) :
    |s.selectorCorrectedResidual ν μ ξ x t| ≤ 2 * K := by
  rw [s.selectorCorrectedResidual_eq_fourthTerms ν μ ξ h x ht,
    s.selectorFourthA_eq_interval_integral ν μ ξ h x t,
    s.selectorFourthB_eq_interval_integral ν μ ξ h x ht,
    s.selectorFourthC_eq_interval_integral ν μ ξ h x ht]
  exact Companion.abs_fourthIntegralCombination_le _ _ _ ht ht1 hK hA hB hC

theorem abs_selectorFourthC_le_of_fourthIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (x : Vector p)
    {t K : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) 1, |s.fourthPathIntegrandC ν μ ξ x t r| ≤ K) :
    |s.selectorFourthC ν μ ξ x t| ≤ t / 3 * K := by
  rw [s.selectorFourthC_eq_interval_integral ν μ ξ h x ht]
  exact Companion.abs_thirdCorrection_integral_le _ ht ht1 hK hC

omit ν [IsProbabilityMeasure ν] in
/-- Late-time path estimate after genuine restoration bounds are supplied
for its actual signed cubic and actual fourth-order product expectations. -/
theorem abs_selectorHeatDerivative_late_le_of_restoration
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hcov : A * A.transpose = covariance μ (sumVector ξ)) (x : Vector p)
    {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hthree : |s.signedCubicPathTerm μ ξ A x t| ≤
      C * δ * dimensionLog p * Real.sqrt (dimensionLog p) / t)
    (hA : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandA (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth))
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandB (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth))
    (hD : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandC (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      (2 * C) * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ + δ ^ 2 / (t * s.bandwidth)) := by
  have hL : 0 ≤ dimensionLog p := (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)).le
  have hδ := h.delta_nonneg
  have hb := s.bandwidth_pos
  have hK : 0 ≤ C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) /
      (t * s.bandwidth) := by positivity
  have hR := s.abs_selectorCorrectedResidual_le_of_fourthIntegrands
    (gaussianLaw (Real.sqrt t • A)) μ ξ h x ht.le ht1 hK hA hB hD
  rw [s.selectorHeatDerivative_eq_signedCubic_add_residual μ ξ h A hcov x ht.le]
  have hh : |-(t / 3) * s.signedCubicPathTerm μ ξ A x t| ≤
      C * δ * dimensionLog p * Real.sqrt (dimensionLog p) / 3 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ t / 3)]
    apply (mul_le_mul_of_nonneg_left hthree (by positivity : 0 ≤ t / 3)).trans_eq
    field_simp
    ring
  apply ((abs_add _ _).trans (add_le_add hh hR)).trans
  have hbase : 0 ≤ C * δ * dimensionLog p * Real.sqrt (dimensionLog p) := by positivity
  have heq : C * δ * dimensionLog p * Real.sqrt (dimensionLog p) / 3 +
      2 * (C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) ≤
      (2 * C) * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ + δ ^ 2 / (t * s.bandwidth)) := by
    have hring : (2 * C) * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ + δ ^ 2 / (t * s.bandwidth)) =
        2 * (C * δ * dimensionLog p * Real.sqrt (dimensionLog p)) +
        2 * (C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) := by ring
    rw [hring]
    linarith
  exact heq

omit ν [IsProbabilityMeasure ν] in
/-- Under cancellation the same restoration estimate bounds only the
fourth-order remainder, preserving the zero-skewness improvement. -/
theorem abs_selectorHeatDerivative_late_le_of_cancellation_and_restoration
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hcov : A * A.transpose = covariance μ (sumVector ξ)) (x : Vector p)
    {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hA : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandA (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth))
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandB (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth))
    (hD : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |s.fourthPathIntegrandC (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
        C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      2 * (C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) := by
  have hL : 0 ≤ dimensionLog p := (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)).le
  have hb := s.bandwidth_pos
  have hK : 0 ≤ C * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) /
      (t * s.bandwidth) := by positivity
  rw [s.selectorHeatDerivative_eq_residual_of_cancellation μ ξ h hcancel A hcov x ht.le]
  exact s.abs_selectorCorrectedResidual_le_of_fourthIntegrands
    (gaussianLaw (Real.sqrt t • A)) μ ξ h x ht.le ht1 hK hA hB hD

end
end RectangleCLT.FaceSmoother
