import RectangleCLTCompanion.SplitV4.PairedNormalization
import RectangleCLTCompanion.RectangleDistance

/-! The literal polynomial array class and its uniform supremum. The
coordinate fourth-moment condition is retained for every q, including q<4.
The supremum ranges over all probability spaces in the selected universe;
zero is included as the usual bottom value of an empty admissible class. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u

namespace RectangleCLT.Companion.SplitV4
noncomputable section

structure PolynomialIndependentHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (q B : ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X μ
  centered : ∀ i j, (∫ ω, X i ω j ∂μ) = 0
  envelope_integrable : ∀ i, Integrable (fun ω => ‖X i ω‖^q) μ
  fourth_integrable : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ
  average_second : ∀ j, (1/(n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1
  envelope_moment : ∀ i, (∫ ω, ‖X i ω‖^q ∂μ) ≤ B^q
  average_fourth : ∀ j, (1/(n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 4 ∂μ) ≤ B^2

def polynomialClassDistances (q B : ℝ) (p n : ℕ) : Set ℝ :=
  {e | e = 0 ∨ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (μ : Measure Ω), IsProbabilityMeasure μ ∧
    ∃ (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
      PolynomialIndependentHypotheses μ X q B ∧
      A * A.transpose = covariance μ (normalizedObservationSum X) ∧
      e = rectangleDistance μ (normalizedObservationSum X) A}

def polynomialWorstDistance (q B : ℝ) (p n : ℕ) : ℝ :=
  sSup (polynomialClassDistances.{u} q B p n)

def PolynomialModelBound (q B : ℝ) (p n : ℕ) (R : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
    PolynomialIndependentHypotheses μ X q B →
    A * A.transpose = covariance μ (normalizedObservationSum X) →
    rectangleDistance μ (normalizedObservationSum X) A ≤ R

theorem zero_mem_polynomialClassDistances (q B : ℝ) (p n : ℕ) :
    0 ∈ polynomialClassDistances.{u} q B p n := Or.inl rfl

theorem polynomialClassDistances_le_one {q B e : ℝ} {p n : ℕ}
    (he : e ∈ polynomialClassDistances.{u} q B p n) : e ≤ 1 := by
  rcases he with rfl | ⟨Ω, mΩ, h⟩
  · norm_num
  · letI := mΩ
    rcases h with ⟨μ, hprob, X, A, _, _, rfl⟩
    letI := hprob
    exact rectangleDistance_le_one μ (normalizedObservationSum X) A

theorem polynomialClassDistances_bddAbove (q B : ℝ) (p n : ℕ) :
    BddAbove (polynomialClassDistances.{u} q B p n) :=
  ⟨1, fun _ he => polynomialClassDistances_le_one he⟩

theorem polynomialWorstDistance_nonneg (q B : ℝ) (p n : ℕ) :
    0 ≤ polynomialWorstDistance.{u} q B p n :=
  le_csSup (polynomialClassDistances_bddAbove _ _ _ _)
    (zero_mem_polynomialClassDistances _ _ _ _)

theorem polynomialWorstDistance_le_one (q B : ℝ) (p n : ℕ) :
    polynomialWorstDistance.{u} q B p n ≤ 1 :=
  csSup_le ⟨0, zero_mem_polynomialClassDistances _ _ _ _⟩
    (fun _ he => polynomialClassDistances_le_one he)

theorem rectangleDistance_mem_polynomialClassDistances
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {q B : ℝ} (X : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : PolynomialIndependentHypotheses μ X q B)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ∈
      polynomialClassDistances.{u} q B p n :=
  Or.inr ⟨Ω, inferInstance, μ, inferInstance, X, A, h, hA, rfl⟩

/-- Exact equivalence between a uniform bound on actual admissible arrays
and the literal supremum over the manuscript's class. -/
theorem polynomialWorstDistance_le_iff_modelBound
    (q B : ℝ) (p n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    polynomialWorstDistance.{u} q B p n ≤ R ↔ PolynomialModelBound.{u} q B p n R := by
  constructor
  · intro h Ω mΩ μ hprob X A hdata hA
    exact (le_csSup (polynomialClassDistances_bddAbove q B p n)
      (rectangleDistance_mem_polynomialClassDistances μ X A hdata hA)).trans h
  · intro h
    apply csSup_le ⟨0, zero_mem_polynomialClassDistances q B p n⟩
    intro e he
    rcases he with rfl | ⟨Ω, mΩ, hh⟩
    · exact hR
    · letI := mΩ
      rcases hh with ⟨μ, hprob, X, A, hdata, hA, rfl⟩
      letI := hprob
      exact h μ X A hdata hA

end
end RectangleCLT.Companion.SplitV4
