import RectangleCLTCompanion.Cancellation

/-! Uniformity in Theorem 5 is over the entire probability class at each
sample size, before a law, covariance factor, or rectangle is selected. -/

open MeasureTheory Filter

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- An error bound uniform over all normalized observations in the
fixed-gap, envelope-at-most-B class at one sample size. -/
def FixedGapClassBound (c₀ B : ℝ) (p n : ℕ) (ε : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
    BoundedIndependentHypotheses μ ξ (B / Real.sqrt n) →
    (∀ j, covariance μ (sumVector ξ) j j = 1) →
    c₀ ≤ pairGap (covariance μ (sumVector ξ)) →
    A * A.transpose = covariance μ (sumVector ξ) →
    ∀ R : Rect p, rectangleError μ (sumVector ξ) A R < ε

/-- The same uniform class, restricted by cancellation of the full
aggregate mixed third-moment tensor. -/
def ZeroSkewFixedGapClassBound (c₀ B : ℝ) (p n : ℕ) (ε : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
    BoundedIndependentHypotheses μ ξ (B / Real.sqrt n) →
    (∀ j, covariance μ (sumVector ξ) j j = 1) →
    c₀ ≤ pairGap (covariance μ (sumVector ξ)) →
    A * A.transpose = covariance μ (sumVector ξ) →
    AggregateThirdMomentsVanish μ ξ →
    ∀ R : Rect p, rectangleError μ (sumVector ξ) A R < ε

/-- Equivalently, the supremum rectangle error of the full class tends
to zero. The sample-size threshold is uniform over all the models. -/
def FixedGapUniformConsistency (c₀ : ℝ) (B : ℕ → ℝ) (p : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, FixedGapClassBound.{u} c₀ (B n) (p n) n ε

def ZeroSkewFixedGapUniformConsistency (c₀ B : ℝ) (p : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ZeroSkewFixedGapClassBound.{u} c₀ B (p n) n ε

end

end RectangleCLT.Companion
