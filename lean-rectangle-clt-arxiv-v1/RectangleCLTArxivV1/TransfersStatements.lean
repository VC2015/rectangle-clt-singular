import RectangleCLTArxivV1.GaussianCalibration
import RectangleCLTCompanion.SubexponentialStatement
import RectangleCLTCompanion.RectangleDistance

/-!
# The width-dependent polynomial transfer statements of arXiv v1

These definitions specify the two assertions in Theorem 2 separately. They
are targets, not proofs of either transfer. In particular the envelope-only
class has no coordinate fourth-moment assumption. The width is the actual
Gaussian maximum of the covariance factor and is not a supplied parameter.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators

universe u

/-- The class `E_q(B,p)` from the paper, with finite moments interpreted by
integrability as well as inequalities for their actual integrals. -/
structure PolynomialEnvelopeHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (q B : ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X μ
  centered : ∀ i j, (∫ ω, X i ω j ∂μ) = 0
  envelope_integrable : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ
  average_second : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1
  envelope_moment : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q

/-- The class `C_q(B,p)` has both moment budgets, for every fixed `q>2`,
including `2<q<4`. The fourth budget is `B²`, rather than `B⁴`. -/
structure PolynomialFourthHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (q B : ℝ) : Prop
    extends PolynomialEnvelopeHypotheses μ X q B where
  fourth_integrable : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ
  average_fourth : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 4 ∂μ) ≤ B ^ 2

/-- Theorem 2(i), the displayed rate at frozen main lines 453--455. -/
noncomputable def polynomialEnvelopeWidthRate (n p : ℕ) (B q g : ℝ) : ℝ :=
  B * g * dimensionLog p ^ (1 - 1 / q) * dimensionLog n ^ (1 / 2 - 1 / q) /
    (n : ℝ) ^ (1 / 2 - 1 / q)

/-- Theorem 2(ii), the displayed rate at frozen main lines 462--465. -/
noncomputable def polynomialFourthWidthRate (n p : ℕ) (B q g : ℝ) : ℝ :=
  g * (B ^ (1 / 2 : ℝ) * dimensionLog p ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) +
    B * dimensionLog p ^ (1 - 1 / q) /
      ((n : ℝ) ^ (1 / 2 - 1 / q) *
        Real.log (Real.exp 1 + B * ((n : ℝ) / dimensionLog p) ^ (2 / q - 1 / 2)) ^ (1 - 1 / q)))

/-- A fixed constant bounds all actual arrays under the envelope condition alone. -/
def PolynomialEnvelopeBound (q C : ℝ) : Prop :=
  ∀ (p n : ℕ), 1 ≤ p → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialEnvelopeHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ),
    A * A.transpose = covariance μ (Companion.normalizedObservationSum X) →
    Companion.rectangleDistance μ (Companion.normalizedObservationSum X) A ≤
      C * min 1 (polynomialEnvelopeWidthRate n p B q (gaussianMaximumMean A))

/-- A fixed constant bounds all actual arrays under both moment conditions. -/
def PolynomialFourthBound (q C : ℝ) : Prop :=
  ∀ (p n : ℕ), 1 ≤ p → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialFourthHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ),
    A * A.transpose = covariance μ (Companion.normalizedObservationSum X) →
    Companion.rectangleDistance μ (Companion.normalizedObservationSum X) A ≤
      C * min 1 (polynomialFourthWidthRate n p B q (gaussianMaximumMean A))

/-- The exact universal-quantifier order of the new Theorem 2: the common
constant depends on the fixed `q`, before dimensions and probability models. -/
def PolynomialMomentTheorem (q : ℝ) : Prop :=
  2 < q → ∃ C : ℝ, 0 < C ∧ PolynomialEnvelopeBound.{u} q C ∧ PolynomialFourthBound.{u} q C

theorem polynomialEnvelopeWidthRate_nonneg {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B g : ℝ} (hB : 0 ≤ B) (hg : 0 ≤ g) (q : ℝ) :
    0 ≤ polynomialEnvelopeWidthRate n p B q g := by
  have hL : 0 ≤ dimensionLog p := le_trans (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hell : 0 ≤ dimensionLog n := le_trans (by norm_num) (log_exp_mul_nat_ge_one hn)
  unfold polynomialEnvelopeWidthRate
  positivity

theorem polynomialFourthWidthRate_nonneg {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B g : ℝ} (hB : 0 ≤ B) (hg : 0 ≤ g) (q : ℝ) :
    0 ≤ polynomialFourthWidthRate n p B q g := by
  have hL : 0 ≤ dimensionLog p := le_trans (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hK : 0 ≤ B * ((n : ℝ) / dimensionLog p) ^ (2 / q - 1 / 2) := by positivity
  have hl : 0 ≤ Real.log (Real.exp 1 + B * ((n : ℝ) / dimensionLog p) ^ (2 / q - 1 / 2)) := by
    apply Real.log_nonneg
    linarith [Real.add_one_le_exp (1 : ℝ)]
  unfold polynomialFourthWidthRate
  positivity

/-- Taking a minimum combines two established estimates; it does not supply
either of the missing probabilistic transfer estimates. -/
theorem le_common_capped_min_of_two {e C R S : ℝ}
    (hR : e ≤ C * min 1 R) (hS : e ≤ C * min 1 S) :
    e ≤ C * min 1 (min R S) := by
  by_cases hRS : R ≤ S
  · simpa only [min_eq_left hRS] using hR
  · simpa only [min_eq_right (le_of_not_ge hRS)] using hS

end RectangleCLTArxivV1
