import RectangleCLTCompanion.SplitV4.RelativeMain
import RectangleCLTCompanion.SplitV4.ObservationNormalization
import RectangleCLTCompanion.SubexponentialBounded

/-! The printed normalization argument for Corollary 1, with the current
relative theorem's envelope conclusion as its actual bounded input. -/

open MeasureTheory
open scoped BigOperators
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem normalized_observations_via_current_theorem
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) {B : ℝ}
    (h : BoundedIndependentHypotheses μ X B) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      relativeUniversalConstant * min 1
        (unrestrictedRate (B/Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  let ξ : Fin n → Ω → Vector p := fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω
  have hs : sumVector ξ = normalizedObservationSum X := by
    funext ω
    exact sumVector_smul X (Real.sqrt (n : ℝ))⁻¹ ω
  have hξ : BoundedIndependentHypotheses μ ξ (B/Real.sqrt (n : ℝ)) := by
    have hh := h.smul_of_nonneg (Real.sqrt (n : ℝ))⁻¹
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
    simpa only [ξ,div_eq_mul_inv,mul_comm] using hh
  have hu (j : Fin p) : covariance μ (sumVector ξ) j j = 1 := by
    rw [hs,bounded_normalizedObservationSum_covariance_diagonal h,haverage]
  have hfactor : A*A.transpose = covariance μ (sumVector ξ) := by rw [hs]; exact hA
  simpa only [hs] using relativeEnvelopeCLT μ hp ξ hξ hu A hfactor

/-- The bounded invocation inside the printed clipping proof, after the
actual marginal standardization and exact undoing of the diagonal map. -/
theorem bounded_after_standardization_via_current_theorem
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (d : Vector p) (hd : ∀ j, (1/2 : ℝ) ≤ d j)
    (hvar : ∀ j, covariance μ (sumVector ξ) j j = (d j)^2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤
      relativeUniversalConstant * min 1 (unrestrictedRate (2*δ) (dimensionLog p)) := by
  obtain ⟨hscaled,hunit,hfactor⟩ := bounded_standardization_data h d hd hvar A hA
  apply rectangleError_undo_standardization_le μ (sumVector ξ) d
    (fun j => lt_of_lt_of_le (by norm_num) (hd j)) A _ R
  intro Q
  have hh := relativeEnvelopeCLT μ hp (standardizedRows ξ d) hscaled hunit
    (scaledFactor (fun j => (d j)⁻¹) A) hfactor
  have he := (rectangleError_le_rectangleDistance μ (sumVector (standardizedRows ξ d))
    (scaledFactor (fun j => (d j)⁻¹) A) Q).trans hh
  rw [sumVector_standardizedRows] at he
  exact he

/-- The unequal-variance paragraph following Corollary 1, for any positive
lower bound on the marginal standard deviations. The diagonal map is
undone exactly, so this is the full distance in the original coordinates. -/
theorem positive_standardization_via_current_theorem
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (d : Vector p) {dmin : ℝ} (hmin : 0<dmin) (hd : ∀j,dmin≤d j)
    (hvar : ∀j,covariance μ (sumVector ξ) j j=(d j)^2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A≤relativeUniversalConstant*
      min 1 (unrestrictedRate (δ/dmin) (dimensionLog p)) := by
  have hdpos : ∀j,0<d j := fun j => hmin.trans_le (hd j)
  have hscaled : BoundedIndependentHypotheses μ (standardizedRows ξ d) (δ/dmin) := by
    have hh := boundedIndependent_diagonalScale h (fun j => (d j)⁻¹) (inv_pos.mpr hmin).le (by
      intro j
      rw [abs_of_pos (inv_pos.mpr (hdpos j))]
      exact inv_anti₀ hmin (hd j))
    simpa only [standardizedRows,div_eq_mul_inv,mul_comm] using hh
  have hunit : ∀j,covariance μ (sumVector (standardizedRows ξ d)) j j=1 := by
    intro j
    rw [sumVector_standardizedRows]
    exact covariance_standardize_diagonal μ (sumVector ξ) d (fun j => (hdpos j).ne') hvar j
  have hfactor : scaledFactor (fun j => (d j)⁻¹) A*
      (scaledFactor (fun j => (d j)⁻¹) A).transpose=covariance μ (sumVector (standardizedRows ξ d)) := by
    ext j k
    rw [scaledFactor_gram,hA,sumVector_standardizedRows,covariance_diagonalScale]
  have hh := relativeEnvelopeCLT μ hp (standardizedRows ξ d) hscaled hunit
    (scaledFactor (fun j => (d j)⁻¹) A) hfactor
  apply rectangleDistance_le
  intro R
  apply rectangleError_undo_standardization_le μ (sumVector ξ) d hdpos A _ R
  intro Q
  have he := (rectangleError_le_rectangleDistance μ (sumVector (standardizedRows ξ d))
    (scaledFactor (fun j => (d j)⁻¹) A) Q).trans hh
  rw [sumVector_standardizedRows] at he
  exact he

theorem normalized_observations_unequal_variance
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) {B : ℝ}
    (h : BoundedIndependentHypotheses μ X B) (hp : 1≤p)
    (d : Vector p) {dmin : ℝ} (hmin : 0<dmin) (hd : ∀j,dmin≤d j)
    (haverage : ∀j,(1/(n : ℝ))*(∑i,∫ω,X i ω j^2 ∂μ)=(d j)^2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A≤relativeUniversalConstant*
      min 1 (unrestrictedRate (B/(dmin*Real.sqrt n)) (dimensionLog p)) := by
  let ξ : Fin n → Ω → Vector p := fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω
  have hs : sumVector ξ=normalizedObservationSum X := funext (fun ω => sumVector_smul X _ ω)
  have hξ : BoundedIndependentHypotheses μ ξ (B/Real.sqrt n) := by
    have hh := h.smul_of_nonneg (Real.sqrt (n : ℝ))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    simpa only [ξ,div_eq_mul_inv,mul_comm] using hh
  have hv : ∀j,covariance μ (sumVector ξ) j j=(d j)^2 := by
    intro j
    rw [hs,bounded_normalizedObservationSum_covariance_diagonal h,haverage]
  have hf : A*A.transpose=covariance μ (sumVector ξ) := by rw [hs]; exact hA
  have hh := positive_standardization_via_current_theorem hξ hp d hmin hd hv A hf
  rw [hs] at hh
  simpa only [div_div,mul_comm] using hh

end
end RectangleCLT.Companion.SplitV4.Printed
