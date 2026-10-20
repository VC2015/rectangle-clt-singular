import RectangleCLT.IndependentCovariance

/-! Scalar normalization of the actual independent bounded observations.
This preserves independence and records the covariance of the actual sum. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

theorem sumVector_smul {Ω : Type*} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (a : ℝ) (ω : Ω) :
    sumVector (fun i ω => a • ξ i ω) ω = a • sumVector ξ ω := by
  simp only [sumVector, Finset.smul_sum]

namespace BoundedIndependentHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem smul (h : BoundedIndependentHypotheses μ ξ δ) (a : ℝ) :
    BoundedIndependentHypotheses μ (fun i ω => a • ξ i ω) (|a| * δ) := by
  refine ⟨fun i => measurable_const.smul (h.measurable i), ?_, ?_, ?_,
    mul_nonneg (abs_nonneg a) h.delta_nonneg⟩
  · exact h.independent.comp (fun _ (x : Vector p) => a • x)
      (fun _ => measurable_const.smul measurable_id)
  · intro i j
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, h.centered, mul_zero]
  · intro i
    filter_upwards [h.bounded i] with ω hω
    simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hω (abs_nonneg a)

theorem smul_of_nonneg (h : BoundedIndependentHypotheses μ ξ δ)
    (a : ℝ) (ha : 0 ≤ a) :
    BoundedIndependentHypotheses μ (fun i ω => a • ξ i ω) (a * δ) := by
  simpa only [abs_of_nonneg ha] using h.smul a

theorem covariance_sum_smul [IsProbabilityMeasure μ]
    (h : BoundedIndependentHypotheses μ ξ δ) (a : ℝ) :
    covariance μ (sumVector (fun i ω => a • ξ i ω)) =
      a ^ 2 • covariance μ (sumVector ξ) := by
  ext j k
  rw [(h.smul a).covariance_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
  rw [h.covariance_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ ω, a ^ 2 * (ξ i ω j * ξ i ω k) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun _ => by ring
    _ = _ := integral_const_mul _ _

theorem covariance_sum_smul_diagonal [IsProbabilityMeasure μ]
    (h : BoundedIndependentHypotheses μ ξ δ) (a v : ℝ)
    (hv : ∀ j, covariance μ (sumVector ξ) j j = v) (j : Fin p) :
    covariance μ (sumVector (fun i ω => a • ξ i ω)) j j = a ^ 2 * v := by
  rw [h.covariance_sum_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, hv]

end BoundedIndependentHypotheses
end RectangleCLT
