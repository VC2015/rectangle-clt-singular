import RectangleCLTArxivV1.IntrinsicMain
import RectangleCLTCompanion.SplitV4.ObservationNormalization

/-! The actual normalization and rate identity in Corollary 1. -/
namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators

set_option autoImplicit false

noncomputable def normalizedObservationArray {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) : Fin n → Ω → Vector p :=
  fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω

theorem sum_normalizedObservationArray {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) :
    sumVector (normalizedObservationArray X) = normalizedObservationSum X := by
  funext ω
  exact sumVector_smul X (Real.sqrt (n : ℝ))⁻¹ ω

theorem boundedIndependent_normalizedObservationArray
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {B : ℝ}
    (h : BoundedIndependentHypotheses μ X B) :
    BoundedIndependentHypotheses μ (normalizedObservationArray X)
      (B / Real.sqrt (n : ℝ)) := by
  simpa only [normalizedObservationArray, div_eq_mul_inv, mul_comm] using
    h.smul_of_nonneg (Real.sqrt (n : ℝ))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem covariance_normalizedObservationArray_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {B : ℝ}
    (h : BoundedIndependentHypotheses μ X B)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (j : Fin p) : covariance μ (sumVector (normalizedObservationArray X)) j j = 1 := by
  rw [sum_normalizedObservationArray, bounded_normalizedObservationSum_covariance_diagonal h,
    haverage]

noncomputable def intrinsicObservationRate (B g : ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  (B * g * L / Real.sqrt (n : ℝ)) *
    Real.sqrt (1 + logPlus (Real.sqrt (n : ℝ) / (B * Real.sqrt L)))

theorem normalized_intrinsic_envelope_rate (B g L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (B / Real.sqrt (n : ℝ)) * g * L *
      Real.sqrt (D_L (B / Real.sqrt (n : ℝ)) L) = intrinsicObservationRate B g n L := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hid : 1 / ((B / Real.sqrt (n : ℝ)) * Real.sqrt L) =
      Real.sqrt (n : ℝ) / (B * Real.sqrt L) := by
    by_cases hB : B = 0
    · simp [hB]
    by_cases hL : Real.sqrt L = 0
    · simp [hL]
    field_simp
  unfold intrinsicObservationRate D_L
  rw [hid]
  ring

/-- Corollary 1 for the actual normalized independent observations. The
Gaussian factor represents their covariance, with no rank restriction. -/
theorem normalizedObservationsIntrinsicCLT
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {B : ℝ}
    (h : BoundedIndependentHypotheses μ X B) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      intrinsicUniversalConstant * min 1
        (intrinsicObservationRate B (gaussianMaximumMean A) n (dimensionLog p)) := by
  have hξ := boundedIndependent_normalizedObservationArray h
  have hunit := covariance_normalizedObservationArray_diagonal h haverage
  have hfactor : A * A.transpose =
      covariance μ (sumVector (normalizedObservationArray X)) := by
    simpa only [sum_normalizedObservationArray] using hA
  have hr := intrinsicEnvelopeCLT μ (normalizedObservationArray X) hξ hp hunit A hfactor
  simpa only [sum_normalizedObservationArray,
    normalized_intrinsic_envelope_rate B (gaussianMaximumMean A) (dimensionLog p) hn] using hr

universe u

/-- The printed quantifier order, with all probabilistic inputs given as
ordinary measurability, independence, centering and boundedness conditions. -/
theorem corollary_1_normalized_observations :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ), 1 ≤ p → 1 ≤ n →
      ∀ (X : Fin n → Ω → Vector p) (B : ℝ),
      (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i j, (∫ ω, X i ω j ∂μ) = 0) →
      (∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ B) →
      (∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) →
      rectangleDistance μ (normalizedObservationSum X) A ≤
        C * min 1 (intrinsicObservationRate B (gaussianMaximumMean A) n (dimensionLog p)) := by
  refine ⟨intrinsicUniversalConstant, intrinsicUniversalConstant_pos, ?_⟩
  intro Ω _ μ _ p n hp hn X B hmeas hind hcenter hbound haverage A hA
  exact normalizedObservationsIntrinsicCLT
    (boundedIndependent_of_raw hn X B hmeas hind hcenter hbound) hp hn haverage A hA

end RectangleCLTArxivV1
