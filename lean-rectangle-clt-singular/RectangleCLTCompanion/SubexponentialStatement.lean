import RectangleCLTCompanion.Statement

/-! Probabilistic contracts for the sub-exponential extension.  The Gaussian
comparison has the exact covariance of the normalized sum, including when
that covariance is singular. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

/-- The normalized sum of observations, before imposing any envelope. -/
def normalizedObservationSum {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) : Ω → Vector p :=
  fun ω => (Real.sqrt (n : ℝ))⁻¹ • sumVector X ω

/-- The cutoff scale in the manuscript; its logarithm depends on `n`, not `np`. -/
def subexponentialScale (n : ℕ) (K : ℝ) : ℝ :=
  K * dimensionLog n / Real.sqrt (n : ℝ)

/-- The additional fixed-positive-gap rate in the tail corollary. -/
def fixedGapSubexponentialRate (b L : ℝ) : ℝ :=
  b * (L ^ (3 / 2 : ℝ) +
    L * Real.sqrt (1 + logPlus (1 / (b * L))))

/-- Independent centered observations with coordinate exponential moments
at scale `K`.  Integrability is explicit, so the totalized Bochner integral
cannot make the moment assumption vacuous. -/
structure SubexponentialIndependentHypotheses
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (K : ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X μ
  centered : ∀ i j, (∫ ω, X i ω j ∂μ) = 0
  integrable_exp : ∀ i j, Integrable (fun ω => Real.exp (|X i ω j| / K)) μ
  exponential_moment : ∀ i j, (∫ ω, Real.exp (|X i ω j| / K) ∂μ) ≤ 2
  one_le_scale : 1 ≤ K

/-- Uniform unrestricted-covariance tail CLT, with one constant fixed before
all dimensions, probability spaces, distributions and exponential scales. -/
def SubexponentialCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (X : Fin n → Ω → Vector p) (K : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      SubexponentialIndependentHypotheses μ X K →
      (∀ j, covariance μ (normalizedObservationSum X) j j = 1) →
      A * A.transpose = covariance μ (normalizedObservationSum X) →
      ∀ R : Rect p, rectangleError μ (normalizedObservationSum X) A R ≤
        C * min 1 (unrestrictedRate (subexponentialScale n K) (dimensionLog p))

/-- Tail CLT with a fixed positive correlation gap; the constant is allowed
to depend on the supplied lower bound for that gap. -/
def FixedGapSubexponentialCLT (c₀ C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (X : Fin n → Ω → Vector p) (K : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      SubexponentialIndependentHypotheses μ X K →
      (∀ j, covariance μ (normalizedObservationSum X) j j = 1) →
      A * A.transpose = covariance μ (normalizedObservationSum X) →
      c₀ ≤ pairGap (covariance μ (normalizedObservationSum X)) →
      ∀ R : Rect p, rectangleError μ (normalizedObservationSum X) A R ≤
        C * min 1 (fixedGapSubexponentialRate
          (subexponentialScale n K) (dimensionLog p))

end
end RectangleCLT.Companion
