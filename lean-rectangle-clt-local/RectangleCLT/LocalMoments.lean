import RectangleCLT.LocalStatement
import RectangleCLT.Normalization

/-! Moment consequences of the updated data hypotheses. None of these results
requires a positive minimum eigenvalue of the full covariance matrix. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

namespace BoundedIndependentHypotheses

variable {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem abs_coordinate_le (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (j : Fin p) : ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ := by
  filter_upwards [h.bounded i] with ω hω
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ i ω) j).trans hω

/-- Unit variance of the actual independent sum normalizes the sum of each
coordinate's second moments, including arrays with singular covariance. -/
theorem coordinate_second_moments [IsProbabilityMeasure μ]
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (j : Fin p) :
    ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1 :=
  coordinate_second_moments_eq_of_independent_bounded h.measurable h.independent
    h.centered h.abs_coordinate_le hunit j

theorem gamma4_le_delta_sq [IsProbabilityMeasure μ]
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    gamma4 μ ξ ≤ δ ^ 2 :=
  gamma4_le_delta_sq_of_independent_bounded h.measurable h.independent
    h.centered h.abs_coordinate_le hunit

theorem gamma3_le_delta [IsProbabilityMeasure μ]
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    gamma3 μ ξ ≤ δ :=
  gamma3_le_delta_of_independent_bounded h.measurable h.independent
    h.centered h.abs_coordinate_le h.delta_nonneg hunit

end BoundedIndependentHypotheses

namespace LocalCovarianceHypotheses

variable {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}

theorem a3_pos (h : LocalCovarianceHypotheses Q) (hp : 1 ≤ p) : 0 < a3 Q :=
  a3_pos_of_a4_pos (Nat.zero_lt_of_lt hp) h.posSemidef h.a4_pos

theorem pairGap_pos (h : LocalCovarianceHypotheses Q) (hp : 1 ≤ p) :
    0 < pairGap Q :=
  pairGap_pos_of_a4_pos (Nat.zero_lt_of_lt hp) h.posSemidef h.unit_diagonal h.a4_pos

end LocalCovarianceHypotheses

theorem localCovarianceRate_nonneg
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω)
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (hp : 1 ≤ p)
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hlocal : LocalCovarianceHypotheses (covariance μ (sumVector ξ))) :
    0 ≤ localCovarianceRate μ ξ δ :=
  localRateWithParameters_nonneg μ ξ hp hdata.delta_nonneg
    (hlocal.pairGap_pos hp) (hlocal.a3_pos hp) hlocal.a4_pos

end RectangleCLT
