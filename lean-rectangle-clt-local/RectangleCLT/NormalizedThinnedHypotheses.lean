import RectangleCLT.BoundedIndependentScaling
import RectangleCLT.ThinnedHypotheses

/-! The actual normalized bounded array used at positive Gaussian variance.
Its coordinate variance and maximum-norm envelope are computed explicitly. -/

open MeasureTheory

namespace RectangleCLT.BoundedIndependentHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem normalized_thinned (h : BoundedIndependentHypotheses μ ξ δ)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    BoundedIndependentHypotheses (bernoulliArrayLaw μ ξ t)
      (fun i (b : Fin n → Vector p) => (Real.sqrt t)⁻¹ • b i)
      (2 * δ / Real.sqrt t) := by
  have he : (Real.sqrt t)⁻¹ * (2 * δ) = 2 * δ / Real.sqrt t := by ring
  simpa only [he] using (h.thinned t ht.le ht1).smul_of_nonneg
    (Real.sqrt t)⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg t))

theorem normalized_thinned_sum_unit_diagonal
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (j : Fin p) :
    covariance (bernoulliArrayLaw μ ξ t)
      (sumVector (fun i (b : Fin n → Vector p) => (Real.sqrt t)⁻¹ • b i)) j j =
      (1 - t) / t := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1
  have hh := (h.thinned t ht.le ht1).covariance_sum_smul_diagonal
    (Real.sqrt t)⁻¹ (1 - t) (h.thinned_sum_unit_diagonal hunit t ht.le ht1) j
  apply hh.trans
  rw [inv_pow, Real.sq_sqrt ht.le]
  ring

end RectangleCLT.BoundedIndependentHypotheses
