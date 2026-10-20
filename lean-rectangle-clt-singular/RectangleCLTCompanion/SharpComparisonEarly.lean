import RectangleCLTCompanion.Cancellation
import RectangleCLT.InterpolationShortScale

/-! The early-time comparison uses the actual Bernoulli path. The signed
aggregate third tensor is retained in the exact identity before estimating it. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

/-- The full signed cubic contraction at the actual common-point law. -/
def signedCubicPathTerm {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
    s.selectorThirdDerivativeAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
      (thinningProbability t) (thinningScale t) j k l

theorem selectorHeatDerivative_eq_signedCubic_add_residual
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorHeatDerivative μ ξ A x t =
      -(t / 3) * s.signedCubicPathTerm μ ξ A x t +
        s.selectorCorrectedResidual (gaussianLaw (Real.sqrt t • A)) μ ξ x t := by
  have hzero (j k : Fin p) :
      (A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ) = 0 := by
    rw [hA, h.covariance_sum j k, sub_self]
  rw [s.selectorHeatDerivative_eq_commonPoint μ ξ h.measurable h.independent
    h.delta_nonneg h.bounded A x ht]
  simp_rw [hzero, zero_mul, Finset.sum_const_zero, mul_zero, zero_sub]
  unfold signedCubicPathTerm
  ring

theorem signedCubicPathTerm_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    s.signedCubicPathTerm μ ξ A x t = 0 := by
  unfold signedCubicPathTerm
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  rw [hcancel j k l, zero_mul]

theorem selectorHeatDerivative_eq_residual_of_cancellation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorHeatDerivative μ ξ A x t =
      s.selectorCorrectedResidual (gaussianLaw (Real.sqrt t • A)) μ ξ x t := by
  rw [s.selectorHeatDerivative_eq_signedCubic_add_residual μ ξ h A hA x ht,
    s.signedCubicPathTerm_eq_zero μ ξ hcancel A x t, mul_zero, zero_add]

/-- An absolute constant in the genuine early-time estimate. -/
def earlyComparisonConstant : ℝ :=
  6 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)

theorem abs_selectorHeatDerivative_early_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A 0 t| ≤
      earlyComparisonConstant * Real.sqrt (dimensionLog p) *
        (t * δ / s.bandwidth ^ 2 + δ ^ 2 / s.bandwidth ^ 3) := by
  have hC : 0 ≤ 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hδ := h.delta_nonneg
  have hb := s.bandwidth_pos
  have htδ : 0 ≤ t * δ / s.bandwidth ^ 2 := by positivity
  have hδ4 : 0 ≤ δ ^ 2 / s.bandwidth ^ 3 := by positivity
  apply (s.abs_selectorHeatDerivative_shortScale_le μ ξ h hp hunit A hA hband ht ht1).trans
  have hthree : t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) ≤
      t * δ / s.bandwidth ^ 2 := by
    have hh : t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) ≤ t * δ / (3 * s.bandwidth ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h.gamma3_le_delta hunit) ht) (by positivity)
    apply hh.trans
    have hn : 0 ≤ t * δ := mul_nonneg ht h.delta_nonneg
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos s.bandwidth_pos))
      (sq_pos_of_pos s.bandwidth_pos)).mpr
    nlinarith [mul_nonneg hn (sq_nonneg s.bandwidth)]
  have hfour : 6 * gamma4 μ ξ / s.bandwidth ^ 3 ≤ 6 * δ ^ 2 / s.bandwidth ^ 3 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (h.gamma4_le_delta_sq hunit) (by norm_num))
      (pow_pos s.bandwidth_pos 3).le
  have hin : t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) +
      6 * gamma4 μ ξ / s.bandwidth ^ 3 ≤
      6 * (t * δ / s.bandwidth ^ 2 + δ ^ 2 / s.bandwidth ^ 3) := by
    have hfour' : 6 * gamma4 μ ξ / s.bandwidth ^ 3 ≤ 6 * (δ ^ 2 / s.bandwidth ^ 3) := by
      simpa only [mul_div_assoc] using hfour
    linarith
  exact (mul_le_mul_of_nonneg_left hin
    (mul_nonneg hC (Real.sqrt_nonneg _))).trans_eq (by unfold earlyComparisonConstant; ring)

/-- Under full aggregate cancellation the early-time derivative has only the
fourth-order contribution. Marginal third-moment cancellation is insufficient. -/
theorem abs_selectorHeatDerivative_early_le_of_cancellation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A 0 t| ≤
      earlyComparisonConstant * Real.sqrt (dimensionLog p) *
        (δ ^ 2 / s.bandwidth ^ 3) := by
  have hc := s.abs_selectorHeatDerivative_shortScale_le μ ξ h hp hunit A hA hband ht ht1
  rw [(Companion.gamma3_eq_zero_iff μ ξ).mpr hcancel, mul_zero, zero_div, zero_add] at hc
  have hC : 0 ≤ 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hm : 6 * gamma4 μ ξ / s.bandwidth ^ 3 ≤ 6 * δ ^ 2 / s.bandwidth ^ 3 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (h.gamma4_le_delta_sq hunit) (by norm_num))
      (pow_pos s.bandwidth_pos 3).le
  exact hc.trans ((mul_le_mul_of_nonneg_left hm
    (mul_nonneg hC (Real.sqrt_nonneg _))).trans_eq (by unfold earlyComparisonConstant; ring))

end
end RectangleCLT.FaceSmoother
