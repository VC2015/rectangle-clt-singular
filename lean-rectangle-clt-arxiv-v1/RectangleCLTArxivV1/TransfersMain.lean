import RectangleCLTArxivV1.TransfersEnvelope
import RectangleCLTArxivV1.PairedIntrinsicBennett

/-! The two parts of the new width-dependent Theorem 2, with one common
constant fixed before all dimensions, probability spaces and arrays. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion
universe u

theorem PolynomialEnvelopeBound.mono {q C D : ℝ}
    (h : PolynomialEnvelopeBound.{u} q C) (hCD : C ≤ D) : PolynomialEnvelopeBound.{u} q D := by
  intro p n hp hn B hB Ω mΩ μ hprob X hX A hA
  exact (h p n hp hn B hB μ X hX A hA).trans (mul_le_mul_of_nonneg_right hCD
    (le_min zero_le_one (polynomialEnvelopeWidthRate_nonneg hn hp (zero_le_one.trans hB)
      (gaussianMaximumMean_nonneg A) q)))

theorem PolynomialFourthBound.mono {q C D : ℝ}
    (h : PolynomialFourthBound.{u} q C) (hCD : C ≤ D) : PolynomialFourthBound.{u} q D := by
  intro p n hp hn B hB Ω mΩ μ hprob X hX A hA
  exact (h p n hp hn B hB μ X hX A hA).trans (mul_le_mul_of_nonneg_right hCD
    (le_min zero_le_one (polynomialFourthWidthRate_nonneg hn hp (zero_le_one.trans hB)
      (gaussianMaximumMean_nonneg A) q)))

/-- Theorem 2 of arXiv v1: both polynomial classes, each with its printed
width-dependent capped rate, and a common coefficient depending only on q. -/
theorem theorem_2_intrinsic (q : ℝ) : PolynomialMomentTheorem.{u} q := by
  intro hq
  obtain ⟨C, hC, hEnv⟩ := theorem_2_i_intrinsic.{u} q hq
  obtain ⟨D, hD, hFourth⟩ := theorem_2_ii_intrinsic.{u} q hq
  exact ⟨max C D, hC.trans_le (le_max_left _ _),
    hEnv.mono (le_max_left _ _), hFourth.mono (le_max_right _ _)⟩

/-- The smaller printed rate when both moment budgets hold. -/
def PolynomialCombinedBound (q C : ℝ) : Prop :=
  ∀ (p n : ℕ), 1 ≤ p → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialFourthHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ),
    A * A.transpose = covariance μ (normalizedObservationSum X) →
    rectangleDistance μ (normalizedObservationSum X) A ≤ C * min 1
      (min (polynomialEnvelopeWidthRate n p B q (gaussianMaximumMean A))
        (polynomialFourthWidthRate n p B q (gaussianMaximumMean A)))

/-- One common positive coefficient proves both assertions and their
smaller-rate consequence. Its quantifier precedes every probability model. -/
theorem theorem_2_intrinsic_with_min (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ PolynomialEnvelopeBound.{u} q C ∧
      PolynomialFourthBound.{u} q C ∧ PolynomialCombinedBound.{u} q C := by
  obtain ⟨C, hC, hEnv, hFourth⟩ := theorem_2_intrinsic.{u} q hq
  refine ⟨C, hC, hEnv, hFourth, ?_⟩
  intro p n hp hn B hB Ω mΩ μ hprob X hX A hA
  exact le_common_capped_min_of_two
    (hEnv p n hp hn B hB μ X hX.toPolynomialEnvelopeHypotheses A hA)
    (hFourth p n hp hn B hB μ X hX A hA)

end RectangleCLTArxivV1
