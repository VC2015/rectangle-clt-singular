import RectangleCLT.Moments
import RectangleCLT.Optimization

/-!
# The final reduction from a rectangle master estimate

`BoundedMasterEstimate` is the still-unproved analytic estimate (27) in the
manuscript. Passing it as an explicit hypothesis proves the requested rate
with a constant independent of all dimensions and probability distributions.
This conditional reduction does not establish the master estimate or the CLT.
-/

open MeasureTheory

universe u

namespace RectangleCLT

/-- The analytic master estimate, uniformly over all data and bandwidths.
This proposition records an open proof obligation; it is not an external
result asserted by this library. -/
def BoundedMasterEstimate (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ b : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedHypotheses μ ξ δ b →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ (R : Rect p) (h : ℝ), 12 * δ ≤ h →
        rectangleError μ (sumVector ξ) A R ≤ C / b ^ 2 *
          (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
            gamma4 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) / h +
            h * Real.sqrt (dimensionLog p))

/-- Conditional final step: proving the open master estimate is sufficient
to prove bounded Theorem 1 with the explicit constant `max 1 (13*C)`. -/
theorem boundedRectangleCLT_of_master {C : ℝ} (hC : 0 ≤ C)
    (hmaster : BoundedMasterEstimate.{u} C) :
    BoundedRectangleCLT.{u} (max 1 (13 * C)) := by
  intro Ω _ μ _ p n hp hn ξ δ b A hdata hfactor R
  exact bounded_rate_of_master
    (hdata.delta_pos hp) (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ)
    (log_exp_mul_nat_ge_one hp) hdata.b_pos hC
    (rectangleError_le_one μ (sumVector ξ) A R)
    (hmaster μ p n hp hn ξ δ b A hdata hfactor R)

/-- The absolute constant stays outside all data quantifiers. The master
estimate remains an explicit assumption in this theorem's type. -/
theorem boundedRectangleCLTExists_of_master {C : ℝ} (hC : 0 ≤ C)
    (hmaster : BoundedMasterEstimate.{u} C) : BoundedRectangleCLTExists.{u} :=
  ⟨max 1 (13 * C), le_max_left _ _, boundedRectangleCLT_of_master hC hmaster⟩

end RectangleCLT
