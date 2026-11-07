import RectangleCLTCompanion.SplitV4.PolynomialMain

/-! The literal centrally symmetric polynomial class and the fourth-moment
uniform upper bound. The supremum ranges over actual probability models;
it retains each original moment condition and adds genuine sign invariance. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def polynomialSymmetricClassDistances (q B : ℝ) (p n : ℕ) : Set ℝ :=
  {e | e = 0 ∨ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (μ : Measure Ω), IsProbabilityMeasure μ ∧
    ∃ (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
      PolynomialIndependentHypotheses μ X q B ∧
      (∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) ∧
      A*A.transpose = covariance μ (normalizedObservationSum X) ∧
      e = rectangleDistance μ (normalizedObservationSum X) A}

def polynomialSymmetricWorstDistance (q B : ℝ) (p n : ℕ) : ℝ :=
  sSup (polynomialSymmetricClassDistances.{u} q B p n)

theorem zero_mem_polynomialSymmetricClassDistances (q B : ℝ) (p n : ℕ) :
    0 ∈ polynomialSymmetricClassDistances.{u} q B p n := Or.inl rfl

theorem polynomialSymmetricClassDistances_subset (q B : ℝ) (p n : ℕ) :
    polynomialSymmetricClassDistances.{u} q B p n ⊆ polynomialClassDistances.{u} q B p n := by
  intro e he
  rcases he with h0 | ⟨Ω, mΩ, hh⟩
  · exact Or.inl h0
  · letI := mΩ
    rcases hh with ⟨μ, hprob, X, A, hdata, _, hA, he⟩
    exact Or.inr ⟨Ω, mΩ, μ, hprob, X, A, hdata, hA, he⟩

theorem polynomialSymmetricClassDistances_bddAbove (q B : ℝ) (p n : ℕ) :
    BddAbove (polynomialSymmetricClassDistances.{u} q B p n) :=
  ⟨1, fun _ he => polynomialClassDistances_le_one (polynomialSymmetricClassDistances_subset q B p n he)⟩

theorem polynomialSymmetricWorstDistance_nonneg (q B : ℝ) (p n : ℕ) :
    0 ≤ polynomialSymmetricWorstDistance.{u} q B p n :=
  le_csSup (polynomialSymmetricClassDistances_bddAbove q B p n)
    (zero_mem_polynomialSymmetricClassDistances q B p n)

theorem polynomialSymmetricWorstDistance_le (q B : ℝ) (p n : ℕ) :
    polynomialSymmetricWorstDistance.{u} q B p n ≤ polynomialWorstDistance.{u} q B p n := by
  apply csSup_le ⟨0, zero_mem_polynomialSymmetricClassDistances q B p n⟩
  intro e he
  exact le_csSup (polynomialClassDistances_bddAbove q B p n)
    (polynomialSymmetricClassDistances_subset q B p n he)

theorem polynomialSymmetricWorstDistance_le_one (q B : ℝ) (p n : ℕ) :
    polynomialSymmetricWorstDistance.{u} q B p n ≤ 1 :=
  (polynomialSymmetricWorstDistance_le q B p n).trans (polynomialWorstDistance_le_one q B p n)

theorem rectangleDistance_mem_polynomialSymmetricClassDistances
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {q B : ℝ} (X : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : PolynomialIndependentHypotheses μ X q B)
    (hsym : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ∈
      polynomialSymmetricClassDistances.{u} q B p n :=
  Or.inr ⟨Ω, inferInstance, μ, inferInstance, X, A, h, hsym, hA, rfl⟩

theorem rectangleDistance_le_polynomialSymmetricWorstDistance
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {q B : ℝ} (X : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : PolynomialIndependentHypotheses μ X q B)
    (hsym : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      polynomialSymmetricWorstDistance.{u} q B p n :=
  le_csSup (polynomialSymmetricClassDistances_bddAbove q B p n)
    (rectangleDistance_mem_polynomialSymmetricClassDistances μ X A h hsym hA)

theorem PolynomialIndependentHypotheses.mono_envelope
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}
    {X : Fin n → Ω → Vector p} {q B B' : ℝ}
    (h : PolynomialIndependentHypotheses μ X q B) (hq : 0 ≤ q)
    (hB : 0 ≤ B) (hBB' : B ≤ B') : PolynomialIndependentHypotheses μ X q B' := by
  refine {h with envelope_moment := ?_, average_fourth := ?_}
  · intro i
    exact (h.envelope_moment i).trans (Real.rpow_le_rpow hB hBB' hq)
  · intro j
    exact (h.average_fourth j).trans (pow_le_pow_left₀ hB hBB' 2)

def polynomialFourthUniformConstant (B : ℝ) : ℝ :=
  polynomialUniversalConstant 4 *
    (B^(1/2 : ℝ)+B / Real.log (Real.exp 1+B)^(3/4 : ℝ))

theorem polynomialFourthUniformConstant_pos {B : ℝ} (hB : 1 ≤ B) :
    0 < polynomialFourthUniformConstant B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlog : 0 < Real.log (Real.exp 1+B) :=
    Real.log_pos (by linarith only [hB, Real.add_one_le_exp (1 : ℝ)])
  unfold polynomialFourthUniformConstant
  apply mul_pos (zero_lt_one.trans_le (one_le_polynomialUniversalConstant 4))
  exact add_pos (Real.rpow_pos_of_pos hB0 _) (div_pos hB0 (Real.rpow_pos_of_pos hlog _))

theorem polynomialBennettObservationRate_four_factor (n p : ℕ) (B : ℝ) :
    polynomialBennettObservationRate n p B 4 =
      (B^(1/2 : ℝ)+B / Real.log (Real.exp 1+B)^(3/4 : ℝ))*
        (dimensionLog p^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)) := by
  rw [polynomialBennettObservationRate_four]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Uniform fourth-moment upper rate over all actual polynomial models.
The coefficient is fixed once the envelope parameter is fixed. -/
theorem polynomialWorstDistance_four_le
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    polynomialWorstDistance.{u} 4 B p n ≤
      polynomialFourthUniformConstant B * dimensionLog p^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ) := by
  have hU : 0 ≤ polynomialUniversalConstant 4 := zero_le_one.trans (one_le_polynomialUniversalConstant 4)
  have hh := polynomialMomentWorstDistanceCLT.{u} hp hn (by norm_num : (2 : ℝ) < 4) hB
  calc
    _ ≤ polynomialUniversalConstant 4*min 1 (polynomialCombinedRate n p B 4) := hh
    _ ≤ polynomialUniversalConstant 4*polynomialBennettObservationRate n p B 4 :=
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hU
    _ = _ := by rw [polynomialBennettObservationRate_four_factor]; unfold polynomialFourthUniformConstant; ring

theorem polynomialSymmetricWorstDistance_four_le
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    polynomialSymmetricWorstDistance.{u} 4 B p n ≤
      polynomialFourthUniformConstant B * dimensionLog p^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ) :=
  (polynomialSymmetricWorstDistance_le 4 B p n).trans (polynomialWorstDistance_four_le hp hn hB)

end
end RectangleCLT.Companion.SplitV4
