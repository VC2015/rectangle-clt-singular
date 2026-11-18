import RectangleCLTArxivV1.ChainingComparison
import RectangleCLTArxivV1.GaussianCalibration

/-!
# Lemma C.2 of the frozen arXiv v1 manuscript

The inputs are the paper's independent centered bounded observations and unit
marginal variances. The Gaussian law uses an actual factor of their covariance;
its existence is proved separately, without a spectral lower bound.
-/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators NNReal ENNReal

/-- One fixed numerical constant for the expected-maximum comparison. -/
noncomputable def expectedMaximumConstant : ℝ :=
  max (96 * GenericChaining.gaussianMajorizingConstant + 2 / Real.sqrt (2 / Real.pi)) 1536

theorem expectedMaximumConstant_pos : 0 < expectedMaximumConstant :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1536) (le_max_right _ _)

/-- C2.1–C2.7 assembled from actual bounded-sum hypotheses. No Gaussian
comparison, mixed-tail inequality, or covariance factor existence is assumed
as an analytic input; the factor equality identifies the target Gaussian law. -/
theorem bounded_sum_expected_maximum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (sumVector ξ)) :
    (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
      expectedMaximumConstant * (gaussianMaximumMean A + δ * dimensionLog p) := by
  let d₂ := GenericChaining.canonicalDist (signedVectors (factorRows A))
  have htail := signedProcess_hasMixedTail h
  rw [signedVarianceMetric_eq_canonicalDist h A hfactor] at htail
  have hD := signed_dirksen_expectation_log hp (sumVector ξ) ⟨δ, h.delta_nonneg⟩ d₂
    (GenericChaining.canonicalDist_self _) (GenericChaining.canonicalDist_symm _)
    (GenericChaining.canonicalDist_triangle _) htail
    (integrable_sum_coordinate h) (integrable_sum_coordinate_sq h)
    (fun j => (integral_sum_coordinate_sq h hunit j).le)
  have hG := gamma2_signedFactorRows_le A
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hfactor]; exact hunit j
  have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
  have hpositive : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)
  have hbase : 2 ≤ (2 / Real.sqrt (2 / Real.pi)) * gaussianMaximumMean A := by
    calc
      (2 : ℝ) = (2 / Real.sqrt (2 / Real.pi)) * Real.sqrt (2 / Real.pi) := by
        rw [div_mul_cancel₀ _ hpositive.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hg0 := gaussianMaximumMean_nonneg A
  have hp_real : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hL : 0 ≤ dimensionLog p := by
    unfold dimensionLog
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity : (p : ℝ) ≠ 0), Real.log_exp]
    exact add_nonneg (by norm_num) (Real.log_nonneg hp_real)
  have hδL : 0 ≤ δ * dimensionLog p := mul_nonneg h.delta_nonneg hL
  calc
    (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
        96 * (GenericChaining.gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
          1536 * δ * dimensionLog p + 2 := hD
    _ ≤ 96 * (GenericChaining.gaussianMajorizingConstant * gaussianMaximumMean A) +
          1536 * δ * dimensionLog p + (2 / Real.sqrt (2 / Real.pi)) * gaussianMaximumMean A := by
      have hh := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 96)
      dsimp only [d₂] at hh ⊢
      linarith
    _ = (96 * GenericChaining.gaussianMajorizingConstant + 2 / Real.sqrt (2 / Real.pi)) *
        gaussianMaximumMean A + 1536 * (δ * dimensionLog p) := by ring
    _ ≤ expectedMaximumConstant * gaussianMaximumMean A +
        expectedMaximumConstant * (δ * dimensionLog p) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hδL)
    _ = _ := by ring

/-- The Gaussian representation is witnessed for every admissible bounded
array, including singular covariance; the factor quantifier is not vacuous. -/
theorem bounded_sum_expected_maximum_factor_exists {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector ξ) ∧
      (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
        expectedMaximumConstant * (gaussianMaximumMean A + δ * dimensionLog p) := by
  obtain ⟨A, hA⟩ := RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent h
  exact ⟨A, hA, bounded_sum_expected_maximum h hp hunit A hA⟩

/-- The nonnegative-envelope field in the archive follows from the paper's
raw boundedness assumptions in positive sample size. -/
theorem boundedIndependent_of_raw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ} (hn : 1 ≤ n)
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) : BoundedIndependentHypotheses μ ξ δ := by
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨ω, hω⟩ := (hbound i).exists
  exact ⟨hmeas, hind, hcenter, hbound, (norm_nonneg _).trans hω⟩

universe u
/-- Lemma C.2 with its universal constant chosen before the probability
space, dimensions, observations, envelope, and covariance factor. -/
theorem lemma_C2_expected_maximum :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ), 1 ≤ p → 1 ≤ n →
      ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ),
      (∀ i, Measurable (ξ i)) → iIndepFun ξ μ →
      (∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) →
      (∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector ξ) →
      (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤ C * (gaussianMaximumMean A + δ * dimensionLog p) := by
  refine ⟨expectedMaximumConstant, expectedMaximumConstant_pos, ?_⟩
  intro Ω _ μ _ p n hp hn ξ δ hmeas hind hcenter hbound hunit A hfactor
  exact bounded_sum_expected_maximum
    (boundedIndependent_of_raw hn ξ δ hmeas hind hcenter hbound) hp hunit A hfactor

end RectangleCLTArxivV1
