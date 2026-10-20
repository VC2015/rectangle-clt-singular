import RectangleCLT.LocalStatement

/-! Statements and exact rates from the companion manuscript's main results.
This file defines the three Gaussian approximation propositions.
`SharpMain.lean` proves them with explicit universal constants. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

/-- The manuscript's positive logarithm. -/
def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

/-- The logarithmic correction for the unrestricted covariance rate. -/
def D_L (δ L : ℝ) : ℝ := 1 + logPlus (1 / (δ * Real.sqrt L))

/-- Optional correlation-gap improvement, with the zero-gap fallback `L`.
The manuscript applies this definition for `0 ≤ c ≤ 1`. -/
def kappa (L c : ℝ) : ℝ := if 0 < c then min L c⁻¹ else L

/-- The logarithmic correction at a supplied value of `κ`. -/
def gapLog (L δ κ : ℝ) : ℝ := 1 + logPlus (Real.sqrt κ / (δ * L))

/-- The notation `E_κ` used in the manuscript. -/
abbrev Eκ (L δ κ : ℝ) : ℝ := gapLog L δ κ

/-- Raw unrestricted rate, before saturation by one. -/
def unrestrictedRate (δ L : ℝ) : ℝ :=
  δ * L ^ (3 / 2 : ℝ) * Real.sqrt (D_L δ L)

/-- Raw gap-sensitive rate, including the aggregate cubic contribution. -/
def gapRate (δ L c : ℝ) : ℝ :=
  δ * (L ^ (3 / 2 : ℝ) + L * Real.sqrt (kappa L c * gapLog L δ (kappa L c)))

/-- Raw rate when the full aggregate third-moment tensor vanishes. -/
def zeroSkewRate (δ L c : ℝ) : ℝ :=
  δ * L * Real.sqrt (kappa L c * gapLog L δ (kappa L c))

/-- Cancellation includes every mixed third moment and permits cancellation
between different observations. -/
def AggregateThirdMomentsVanish
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : Prop :=
  ∀ j k l : Fin p, (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) = 0

/-- Unrestricted-covariance CLT target, uniformly over all rectangles.
Only marginal variance normalization is imposed on the covariance. -/
def UnrestrictedCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p, rectangleError μ (sumVector ξ) A R ≤
        C * min 1 (unrestrictedRate δ (dimensionLog p))

/-- Gap-sensitive target. A positive correlation gap is optional, and the
full covariance is allowed to be singular. -/
def GapSensitiveCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p, rectangleError μ (sumVector ξ) A R ≤
        C * min 1 (gapRate δ (dimensionLog p) (pairGap (covariance μ (sumVector ξ))))

/-- Zero-skewness target, requiring cancellation of the full mixed tensor. -/
def ZeroSkewCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      AggregateThirdMomentsVanish μ ξ →
      ∀ R : Rect p, rectangleError μ (sumVector ξ) A R ≤
        C * min 1 (zeroSkewRate δ (dimensionLog p) (pairGap (covariance μ (sumVector ξ))))

/-- Each existential constant is chosen before every probability model,
dimension, distribution, covariance, and envelope parameter. -/
def UnrestrictedCLTExists : Prop := ∃ C : ℝ, 1 ≤ C ∧ UnrestrictedCLT.{u} C

def GapSensitiveCLTExists : Prop := ∃ C : ℝ, 1 ≤ C ∧ GapSensitiveCLT.{u} C

def ZeroSkewCLTExists : Prop := ∃ C : ℝ, 1 ≤ C ∧ ZeroSkewCLT.{u} C

end

end RectangleCLT.Companion
