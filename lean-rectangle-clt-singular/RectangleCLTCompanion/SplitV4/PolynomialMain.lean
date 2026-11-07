import RectangleCLTCompanion.SplitV4.PolynomialUniform
import RectangleCLTCompanion.SplitV4.BennettPolynomial
import RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization

/-! Theorem 2: both genuine polynomial moment budgets, the two proved
upper bounds, saturation, and the literal supremum over all admissible
probability models. Constants are fixed before dimensions and models. -/

open MeasureTheory
open scoped BigOperators ENNReal
universe u

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def polynomialBennettObservationRate (n p : ℕ) (B q : ℝ) : ℝ :=
  B^(1/2 : ℝ) * dimensionLog p ^ (5/4 : ℝ) / (n : ℝ)^(1/4 : ℝ) +
    (B * dimensionLog p ^ (3/2-1/q)) /
      ((n : ℝ)^(1/2-1/q) *
        Real.log (Real.exp 1 + B * ((n : ℝ)/dimensionLog p)^(2/q-1/2))^(1-1/q))

def polynomialCombinedRate (n p : ℕ) (B q : ℝ) : ℝ :=
  min (polynomialBennettObservationRate n p B q) (polynomialEnvelopeTransferRate n p B q)

def polynomialUniversalConstant (q : ℝ) : ℝ :=
  max (bennettPolynomialConstant q) polynomialEnvelopeTransferConstant

theorem one_le_polynomialUniversalConstant (q : ℝ) : 1 ≤ polynomialUniversalConstant q :=
  (one_le_bennettPolynomialConstant q).trans (le_max_left _ _)

theorem polynomialBennettObservationRate_nonneg {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) (q : ℝ) : 0 ≤ polynomialBennettObservationRate n p B q := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hK : 0 ≤ B * ((n : ℝ)/dimensionLog p)^(2/q-1/2) := by positivity
  have hlog : 0 ≤ Real.log (Real.exp 1 + B * ((n : ℝ)/dimensionLog p)^(2/q-1/2)) :=
    Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
  unfold polynomialBennettObservationRate
  positivity

theorem polynomialEnvelopeTransferRate_nonneg {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) (q : ℝ) : 0 ≤ polynomialEnvelopeTransferRate n p B q := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hD : 0 < dimensionLog n := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  unfold polynomialEnvelopeTransferRate polynomialEnvelopeV
  positivity

theorem polynomialCombinedRate_nonneg {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) (q : ℝ) : 0 ≤ polynomialCombinedRate n p B q :=
  le_min (polynomialBennettObservationRate_nonneg hn hp hB q)
    (polynomialEnvelopeTransferRate_nonneg hn hp hB q)

/-- The exact array class supplies a covariance factor from its genuine
coordinate moments. The factor parameter imposes no rank assumption. -/
theorem PolynomialIndependentHypotheses.gaussian_factor_exists
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {q B : ℝ}
    (h : PolynomialIndependentHypotheses μ X q B) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) := by
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _
      ((measurable_pi_apply j).comp (h.measurable i)) (h.fourth_integrable i j)
  obtain ⟨A, hA⟩ := normalizedSummands_gaussian_factor_exists hL2 h.centered
  exact ⟨A, by simpa only [sumVector_normalizedSummands] using hA⟩

/-- Theorem 2 for every actual admissible array. Coordinate fourth moments
remain part of the contract even for 2<q<4. -/
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

/-- The literal supremum in Theorem 2, ranging over all probability
spaces in the chosen universe, not a supplied approximation premise. -/
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

theorem polynomialBennettObservationRate_four (n p : ℕ) (B : ℝ) :
    polynomialBennettObservationRate n p B 4 =
      B^(1/2 : ℝ) * dimensionLog p ^ (5/4 : ℝ) / (n : ℝ)^(1/4 : ℝ) +
        (B * dimensionLog p ^ (5/4 : ℝ)) /
          ((n : ℝ)^(1/4 : ℝ) * Real.log (Real.exp 1 + B)^(3/4 : ℝ)) := by
  norm_num [polynomialBennettObservationRate]

end
end RectangleCLT.Companion.SplitV4
