import RectangleCLTCompanion.SplitV4.Printed.Polynomial
import RectangleCLTCompanion.SplitV4.Printed.Bennett
import RectangleCLTCompanion.SplitV4.PolynomialMain

/-! The printed Theorem 2 assembly with the two printed-route extensions:
class inclusion, one enlarged constant, the smaller of the two rates, and
the actual worst-case supremum. -/

open MeasureTheory
open scoped BigOperators ENNReal
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def polynomialUniversalConstant (q : ℝ) : ℝ :=
  max (bennettPolynomialConstant q) polynomialEnvelopeTransferConstant

theorem one_le_polynomialUniversalConstant (q : ℝ) : 1 ≤ polynomialUniversalConstant q :=
  (one_le_bennettPolynomialConstant q).trans (le_max_left _ _)

theorem polynomialMomentCLT
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (X : Fin n → Ω → Vector p) (h : PolynomialIndependentHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      polynomialUniversalConstant q * min 1 (polynomialCombinedRate n p B q) := by
  have hb := bennettPolynomialCLT_observations (μ := μ) hp hn X h.measurable h.independent
    h.centered h.fourth_integrable h.average_second A hA hB hq
    h.envelope_integrable h.envelope_moment h.average_fourth
  have he := polynomialEnvelopeTransfer μ X h.measurable h.independent hp hn hB hq
    h.envelope_integrable h.envelope_moment h.centered h.average_second A hA
  have hbC := hb.trans (mul_le_mul_of_nonneg_right
    (le_max_left (bennettPolynomialConstant q) polynomialEnvelopeTransferConstant)
    (le_min (by norm_num) (polynomialBennettObservationRate_nonneg hn hp
      (zero_le_one.trans hB) q)))
  have heC := he.trans (mul_le_mul_of_nonneg_right
    (le_max_right (bennettPolynomialConstant q) polynomialEnvelopeTransferConstant)
    (le_min (by norm_num) (polynomialEnvelopeTransferRate_nonneg hn hp
      (zero_le_one.trans hB) q)))
  unfold polynomialCombinedRate
  by_cases hrate : polynomialBennettObservationRate n p B q ≤ polynomialEnvelopeTransferRate n p B q
  · rw [min_eq_left hrate]
    exact hbC
  · rw [min_eq_right (le_of_not_ge hrate)]
    exact heC

theorem polynomialMomentWorstDistanceCLT
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B) :
    polynomialWorstDistance.{u} q B p n ≤
      polynomialUniversalConstant q * min 1 (polynomialCombinedRate n p B q) := by
  apply (polynomialWorstDistance_le_iff_modelBound q B p n (mul_nonneg
    (zero_le_one.trans (one_le_polynomialUniversalConstant q))
    (le_min (by norm_num) (polynomialCombinedRate_nonneg hn hp (zero_le_one.trans hB) q)))).mpr
  intro Ω mΩ μ hprob X A hdata hA
  exact polynomialMomentCLT μ hp hn hq hB X hdata A hA

theorem polynomialMomentCLTExists (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p n : ℕ), 1 ≤ p → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
      polynomialWorstDistance.{u} q B p n ≤ C * min 1 (polynomialCombinedRate n p B q) := by
  refine ⟨polynomialUniversalConstant q, one_le_polynomialUniversalConstant q, ?_⟩
  intro p n hp hn B hB
  exact polynomialMomentWorstDistanceCLT hp hn hq hB

end
end RectangleCLT.Companion.SplitV4.Printed
