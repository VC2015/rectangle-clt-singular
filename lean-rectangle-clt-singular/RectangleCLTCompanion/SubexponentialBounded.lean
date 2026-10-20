import RectangleCLTCompanion.SharpMain
import RectangleCLTCompanion.SubexponentialScaling

/-! Applying the certified bounded CLTs after marginal standardization,
and returning to the original clipped coordinates exactly. -/

open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section

def standardizedRows {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (d : Vector p) : Fin n → Ω → Vector p :=
  fun i ω => diagonalScale (fun j => (d j)⁻¹) (ξ i ω)

theorem sumVector_standardizedRows {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (d : Vector p) :
    sumVector (standardizedRows ξ d) =
      fun ω => diagonalScale (fun j => (d j)⁻¹) (sumVector ξ ω) := by
  funext ω
  exact sumVector_diagonalScale ξ (fun j => (d j)⁻¹) ω

/-- Undo positive diagonal standardization without changing the uniform
rectangle bound. The public Gaussian factor is recovered exactly. -/
theorem rectangleError_undo_standardization_le
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (d : Vector p)
    (hd : ∀ j, 0 < d j) (A : Matrix (Fin p) (Fin p) ℝ) {B : ℝ}
    (hcompare : ∀ R : Rect p,
      rectangleError μ (fun ω => diagonalScale (fun j => (d j)⁻¹) (W ω))
        (scaledFactor (fun j => (d j)⁻¹) A) R ≤ B) (R : Rect p) :
    rectangleError μ W A R ≤ B := by
  have hh := rectangleError_diagonalScale_le μ
    (fun ω => diagonalScale (fun j => (d j)⁻¹) (W ω)) d (fun j => (hd j).le)
    (scaledFactor (fun j => (d j)⁻¹) A) hcompare R
  have hfun : (fun ω => diagonalScale d
      (diagonalScale (fun j => (d j)⁻¹) (W ω))) = W :=
    funext (fun ω => diagonalScale_inverse_right d (fun j => (hd j).ne') (W ω))
  rw [hfun, scaledFactor_inverse d (fun j => (hd j).ne') A] at hh
  exact hh

/-- All data required by the bounded theorem survive marginal
standardization when each standard deviation is at least one half. -/
theorem bounded_standardization_data
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (d : Vector p) (hd : ∀ j, (1 / 2 : ℝ) ≤ d j)
    (hvar : ∀ j, covariance μ (sumVector ξ) j j = (d j) ^ 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    BoundedIndependentHypotheses μ (standardizedRows ξ d) (2 * δ) ∧
      (∀ j, covariance μ (sumVector (standardizedRows ξ d)) j j = 1) ∧
      scaledFactor (fun j => (d j)⁻¹) A *
          (scaledFactor (fun j => (d j)⁻¹) A).transpose =
        covariance μ (sumVector (standardizedRows ξ d)) := by
  have hdpos (j : Fin p) : 0 < d j := lt_of_lt_of_le (by norm_num) (hd j)
  refine ⟨boundedIndependent_standardize h d hd, ?_, ?_⟩
  · intro j
    rw [sumVector_standardizedRows]
    exact covariance_standardize_diagonal μ (sumVector ξ) d (fun j => (hdpos j).ne') hvar j
  · ext j k
    rw [scaledFactor_gram, hA, sumVector_standardizedRows, covariance_diagonalScale]

theorem bounded_unrestrictedCLT_after_standardization
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (d : Vector p) (hd : ∀ j, (1 / 2 : ℝ) ≤ d j)
    (hvar : ∀ j, covariance μ (sumVector ξ) j j = (d j) ^ 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤
      (2 * companionUniversalConstant) * min 1 (unrestrictedRate (2 * δ) (dimensionLog p)) := by
  obtain ⟨hscaled, hunit, hfactor⟩ := bounded_standardization_data h d hd hvar A hA
  apply rectangleError_undo_standardization_le μ (sumVector ξ) d
    (fun j => lt_of_lt_of_le (by norm_num) (hd j)) A _ R
  intro Q
  have hh := unrestrictedCLT μ p n hp hn (standardizedRows ξ d) (2 * δ)
    (scaledFactor (fun j => (d j)⁻¹) A) hscaled hunit hfactor Q
  rw [sumVector_standardizedRows] at hh
  exact hh

theorem bounded_gapCLT_after_standardization
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (d : Vector p) (hd : ∀ j, (1 / 2 : ℝ) ≤ d j)
    (hvar : ∀ j, covariance μ (sumVector ξ) j j = (d j) ^ 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ companionUniversalConstant *
      min 1 (gapRate (2 * δ) (dimensionLog p)
        (pairGap (covariance μ
          (fun ω => diagonalScale (fun j => (d j)⁻¹) (sumVector ξ ω))))) := by
  obtain ⟨hscaled, hunit, hfactor⟩ := bounded_standardization_data h d hd hvar A hA
  apply rectangleError_undo_standardization_le μ (sumVector ξ) d
    (fun j => lt_of_lt_of_le (by norm_num) (hd j)) A _ R
  intro Q
  have hh := gapSensitiveCLT μ p n hp hn (standardizedRows ξ d) (2 * δ)
    (scaledFactor (fun j => (d j)⁻¹) A) hscaled hunit hfactor Q
  rw [sumVector_standardizedRows] at hh
  exact hh

end

end RectangleCLT.Companion
