import RectangleCLTArxivV1.SignedCoordinates
import RectangleCLT.IndependentCovariance

/-!
# Signed contrasts of the actual bounded independent observations

These consequences use the paper's bounded-independent hypotheses and actual
sum covariance. They introduce no covariance nondegeneracy assumption.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ξ : Fin n → Ω → RectangleCLT.Vector p} {δ : ℝ}

omit [IsProbabilityMeasure μ] in
theorem signedObservation_measurable (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (t : SignedIndex p) : Measurable (fun ω => signedCoordinate t (ξ i ω)) :=
  (signedCoordinate_measurable t).comp (h.measurable i)

omit [IsProbabilityMeasure μ] in
theorem signedContrast_observation_measurable (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) : Measurable (signedContrast ξ s t i) :=
  (signedObservation_measurable h i t).sub (signedObservation_measurable h i s)

omit [IsProbabilityMeasure μ] in
theorem signedContrast_independent (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) : iIndepFun (signedContrast ξ s t) μ := by
  simpa only [signedContrast, Function.comp_apply] using h.independent.comp
    (fun _ x => signedCoordinate t x - signedCoordinate s x)
    (fun _ => signedContrast_measurable s t)

theorem signedObservation_integrable (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (t : SignedIndex p) : Integrable (fun ω => signedCoordinate t (ξ i ω)) μ := by
  apply integrable_signedCoordinate
  intro j
  simpa only [pow_one] using
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1

theorem signedContrast_integrable (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) : Integrable (signedContrast ξ s t i) μ :=
  (signedObservation_integrable h i t).sub (signedObservation_integrable h i s)

theorem integral_signedContrast_zero (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) : (∫ ω, signedContrast ξ s t i ω ∂μ) = 0 := by
  change (∫ ω, signedCoordinate t (ξ i ω) - signedCoordinate s (ξ i ω) ∂μ) = 0
  rw [integral_sub (signedObservation_integrable h i t) (signedObservation_integrable h i s),
    integral_signedCoordinate_zero (h.centered i), integral_signedCoordinate_zero (h.centered i), sub_self]

omit [IsProbabilityMeasure μ] in
theorem signedContrast_bound (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) : ∀ᵐ ω ∂μ, |signedContrast ξ s t i ω| ≤ 2 * δ := by
  filter_upwards [h.bounded i] with ω hω
  apply abs_signedCoordinate_sub_le s t (ξ i ω) h.delta_nonneg
  intro j
  have hj : |ξ i ω j| ≤ ‖ξ i ω‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ξ i ω) j
  exact hj.trans hω

omit [IsProbabilityMeasure μ] in
theorem signedContrast_discrete_bound (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) :
    ∀ᵐ ω ∂μ, |signedContrast ξ s t i ω| ≤
      2 * (signedDiscreteMetric ⟨δ, h.delta_nonneg⟩ s t : ℝ) := by
  by_cases hst : s = t
  · subst t
    simp [signedContrast, signedDiscreteMetric]
  · simpa only [signedDiscreteMetric, if_neg hst, NNReal.coe_mk] using signedContrast_bound h s t i

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The summed signed process is exactly the sum of the observation contrasts. -/
theorem signedProcess_sumVector_sub (ξ : Fin n → Ω → RectangleCLT.Vector p)
    (s t : SignedIndex p) (ω : Ω) :
    signedProcess (sumVector ξ) t ω - signedProcess (sumVector ξ) s ω =
      ∑ i, signedContrast ξ s t i ω := (signedContrast_sum ξ s t ω).symm

theorem signedContrast_sq_integrable (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) (i : Fin n) :
    Integrable (fun ω => signedContrast ξ s t i ω ^ 2) μ := by
  apply (integrable_const ((2 * δ) ^ 2)).mono'
    ((signedContrast_observation_measurable h s t i).pow_const 2).aestronglyMeasurable
  filter_upwards [signedContrast_bound h s t i] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 2

theorem integrable_sum_coordinate (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    Integrable (fun ω => sumVector ξ ω j) μ := by
  simp only [sumVector, Finset.sum_apply]
  apply integrable_finset_sum
  intro i hi
  simpa only [pow_one] using
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1

theorem integral_sum_coordinate_zero (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    (∫ ω, sumVector ξ ω j ∂μ) = 0 := by
  simp only [sumVector, Finset.sum_apply]
  rw [integral_finset_sum Finset.univ (fun i _ => by
    simpa only [pow_one] using
      integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1)]
  simp only [h.centered, Finset.sum_const_zero]

omit [IsProbabilityMeasure μ] in
theorem sum_coordinate_bound (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    ∀ᵐ ω ∂μ, |sumVector ξ ω j| ≤ (n : ℝ) * δ := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, |ξ i ω j| ≤ δ := ae_all_iff.mpr (fun i => h.abs_coordinate_le i j)
  filter_upwards [hall] with ω hω
  simp only [sumVector, Finset.sum_apply]
  calc
    _ ≤ ∑ i, |ξ i ω j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hω i
    _ = _ := by simp

theorem integrable_sum_coordinate_sq (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) :
    Integrable (fun ω => sumVector ξ ω j ^ 2) μ := by
  have hm : Measurable (fun ω => sumVector ξ ω j) := by
    simp only [sumVector, Finset.sum_apply]
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply j).comp (h.measurable i))
  apply (integrable_const (((n : ℝ) * δ) ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [sum_coordinate_bound h j] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 2

/-- The unit diagonal in the paper normalizes actual summed coordinate moments. -/
theorem integral_sum_coordinate_sq (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (j : Fin p) :
    (∫ ω, sumVector ξ ω j ^ 2 ∂μ) = 1 := by
  simpa only [covariance, integral_sum_coordinate_zero h j, mul_zero, sub_zero, pow_two] using hunit j

theorem signedProcess_integrable (h : BoundedIndependentHypotheses μ ξ δ) (t : SignedIndex p) :
    Integrable (signedProcess (sumVector ξ) t) μ :=
  integrable_signedCoordinate (integrable_sum_coordinate h) t

theorem signedProcess_increment_integrable (h : BoundedIndependentHypotheses μ ξ δ)
    (s t : SignedIndex p) : Integrable (fun ω =>
      signedProcess (sumVector ξ) s ω - signedProcess (sumVector ξ) t ω) μ :=
  (signedProcess_integrable h s).sub (signedProcess_integrable h t)

theorem signedProcess_sq_integrable (h : BoundedIndependentHypotheses μ ξ δ) (t : SignedIndex p) :
    Integrable (fun ω => signedProcess (sumVector ξ) t ω ^ 2) μ := by
  cases t with
  | none => simp [signedProcess]
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simpa only [signedProcess, signedCoordinate_pos, signedCoordinate_neg, neg_sq]
      using integrable_sum_coordinate_sq h j

theorem integral_signedProcess_sq_le_one (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (t : SignedIndex p) :
    (∫ ω, signedProcess (sumVector ξ) t ω ^ 2 ∂μ) ≤ 1 := by
  cases t with
  | none => simp [signedProcess]
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simpa only [signedProcess, signedCoordinate_pos, signedCoordinate_neg, neg_sq,
      integral_sum_coordinate_sq h hunit j] using (le_refl (1 : ℝ))



end RectangleCLTArxivV1
