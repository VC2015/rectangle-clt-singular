import RectangleCLTCompanion.SplitV4.Printed.ObservationTransfer
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeMaximum
import RectangleCLTCompanion.SplitV4.Printed.PolynomialMoments
import RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization

/-!
# Printed conditional clipping route for Proposition 2

The preserved result proof invoked a historical bounded CLT.  These parallel
proofs instead invoke the current manuscript's relative theorem through its
proved envelope specialization, on the genuine conditional retained array.
The actual conditioning, exceptional shifts, covariance budgets, bad-tag
probabilities, averaging and optimization are retained.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
set_option autoImplicit false

theorem boundedRectangleDistanceCLT_of_marginal_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlower : ∀ j, (1 / 4 : ℝ) ≤ covariance μ (sumVector ξ) j j)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      (2 * relativeUniversalConstant) * min 1 (unrestrictedRate (2 * δ) (dimensionLog p)) := by
  let d : Vector p := fun j => Real.sqrt (covariance μ (sumVector ξ) j j)
  have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j := by
    have hs := Real.sqrt_le_sqrt (hlower j)
    have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
    simpa only [hquarter] using hs
  have hvar (j : Fin p) : covariance μ (sumVector ξ) j j = d j ^ 2 :=
    (Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (hlower j))).symm
  apply rectangleDistance_le μ (sumVector ξ) A
  intro R
  have hr := bounded_after_standardization_via_current_theorem h hp d hd hvar A hA R
  exact hr.trans (mul_le_mul_of_nonneg_right
    (by linarith [one_le_relativeUniversalConstant] :
      relativeUniversalConstant ≤ 2 * relativeUniversalConstant)
    (le_min zero_le_one (unrestrictedRate_nonneg (by linarith [h.delta_nonneg])
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))))

theorem conditionalRetained_marginal_half_lower_bound {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - S) ≤ 1 / 2)
    (j : Fin p) :
    (1 / 2 : ℝ) ≤ covariance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T mask)) j j := by
  have he : |conditionalCovarianceForMask μ T mask j j - S j j| ≤ 1 / 2 := by
    have he := ((norm_le_pi_norm (fun k =>
      (conditionalCovarianceForMask μ T mask - S) j k) j).trans
      (norm_le_pi_norm (fun j k => (conditionalCovarianceForMask μ T mask - S) j k) j)).trans hgood
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using he
  rw [hS j] at he
  rw [conditionalRetained_normalized_covariance μ hT mask]
  change (1 / 2 : ℝ) ≤ conditionalCovarianceForMask μ T mask j j
  linarith [(abs_le.mp he).1]

theorem conditionalRetainedRectangleDistanceCLT {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - S) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T mask) :
    rectangleDistance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T mask)) A ≤
      (2 * relativeUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  have hc : covariance (conditionalGoodProductLaw μ T)
      (sumVector (normalizedSummands (conditionalRetainedSummand μ T mask))) =
        conditionalCovarianceForMask μ T mask := by
    rw [sumVector_normalizedSummands]
    ext j k
    exact conditionalRetained_normalized_covariance μ hT mask j k
  have hl := conditionalRetained_marginal_lower_bound μ hT mask S hS hgood
  rw [← sumVector_normalizedSummands] at hl
  have hh := boundedRectangleDistanceCLT_of_marginal_lower_bound
    (conditionalRetained_normalized_boundedIndependent μ hT mask) hp hn hl A (hA.trans hc.symm)
  rw [sumVector_normalizedSummands] at hh
  convert hh using 1
  congr 3
  ring

theorem conditionalGoodKernel_shifted_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - S) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T tag.1) (R : Rect p) :
    |(conditionalTruncationKernel μ T tag).real
        ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier) -
      (gaussianLaw A).real ((fun x => x + conditionalNormalizedShift μ T tag) ⁻¹' R.carrier)| ≤
      (2 * relativeUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  rw [conditionalKernel_rectangle_error_eq]
  exact (rectangleError_le_rectangleDistance _ _ _ _).trans
    (conditionalRetainedRectangleDistanceCLT μ hT tag.1 hp hn S hS hgood A hA)

/-- Gaussian anti-concentration for the actual retained covariance: a
positive marginal lower bound suffices, including singular covariance. -/
theorem gaussian_translation_rectangle_error_le_of_marginal_lower_bound
    {p : ℕ} (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (1 / 4 : ℝ) ≤ (A * A.transpose) j j)
    (r : Vector p) (R : Rect p) :
    rectangleError (gaussianLaw A) (fun x => x + r) A R ≤
      24 * Real.exp (3 / 2 : ℝ) * ‖r‖ * Real.sqrt (dimensionLog p) := by
  let d : Vector p := fun j => Real.sqrt ((A * A.transpose) j j)
  have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j := by
    simpa only [show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by norm_num] using
      Real.sqrt_le_sqrt (hA j)
  have hdpos (j : Fin p) : 0 < d j := lt_of_lt_of_le (by norm_num) (hd j)
  let c : Vector p := fun j => (d j)⁻¹
  let A' := scaledFactor c A
  have hdiag (j : Fin p) : (A' * A'.transpose) j j = 1 := by
    rw [scaledFactor_gram]
    have hs : d j ^ 2 = (A * A.transpose) j j :=
      Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (hA j))
    dsimp only [c]
    rw [← hs]
    field_simp [(hdpos j).ne']
    <;> ring
  have hr : ‖diagonalScale c r‖ ≤ 2 * ‖r‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖r‖)).mpr
    intro j
    have hc : |c j| ≤ 2 := by
      dsimp [c]
      rw [abs_of_pos (inv_pos.mpr (hdpos j))]
      apply (inv_le_iff_one_le_mul₀ (hdpos j)).mpr
      linarith [hd j]
    simpa only [diagonalScale, Real.norm_eq_abs, abs_mul] using
      mul_le_mul hc (show |r j| ≤ ‖r‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm r j)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  apply rectangleError_undo_standardization_le (gaussianLaw A) (fun x => x + r) d hdpos A
  intro Q
  have heq : rectangleError (gaussianLaw A) (fun x => diagonalScale c (x + r)) A' Q =
      rectangleError (gaussianLaw A') (fun x => x + diagonalScale c r) A' Q := by
    have hm : MeasurableSet ((fun x : Vector p => x + diagonalScale c r) ⁻¹' Q.carrier) :=
      Q.measurableSet_carrier.preimage (measurable_id.add measurable_const)
    have hp : (gaussianLaw A).real ((fun x => diagonalScale c (x + r)) ⁻¹' Q.carrier) =
        (gaussianLaw A').real ((fun x => x + diagonalScale c r) ⁻¹' Q.carrier) := by
      rw [show gaussianLaw A' = (gaussianLaw A).map (diagonalScale c) by
        exact (gaussianLaw_map_diagonalScale c A).symm]
      simp only [Measure.real]
      rw [Measure.map_apply (measurable_diagonalScale c) hm]
      congr 2
      ext x
      change (diagonalScale c (x + r) ∈ Q.carrier) ↔
        (diagonalScale c x + diagonalScale c r ∈ Q.carrier)
      have hlin : diagonalScale c (x + r) = diagonalScale c x + diagonalScale c r := by
        ext j
        simp only [diagonalScale, Pi.add_apply, mul_add]
      rw [hlin]
    unfold rectangleError
    rw [hp]
  change rectangleError (gaussianLaw A) (fun x => diagonalScale c (x + r)) A' Q ≤ _
  rw [heq]
  have ht := gaussian_translation_rectangle_error_le hp A' hdiag (diagonalScale c r) Q
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 12 * Real.exp (3 / 2 : ℝ)))
    (Real.sqrt_nonneg (dimensionLog p))
  exact ht.trans (hm.trans_eq (by ring))

/-- The paper's conditional comparison with its own unshifted `G_Q`,
before comparison with the original reference Gaussian. -/
theorem conditionalGoodKernel_ownGaussian_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - S) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T tag.1) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤
      (2 * relativeUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
      24 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ *
        Real.sqrt (dimensionLog p) := by
  have hdiag (j : Fin p) : (1 / 4 : ℝ) ≤ (A * A.transpose) j j := by
    rw [hA]
    have hl := conditionalRetained_marginal_lower_bound μ hT tag.1 S hS hgood j
    rw [conditionalRetained_normalized_covariance μ hT tag.1] at hl
    exact hl
  have hb := conditionalGoodKernel_shifted_rectangle_error_le μ hT tag hp hn S hS hgood A hA R
  have hs := gaussian_translation_rectangle_error_le_of_marginal_lower_bound hp A hdiag
    (conditionalNormalizedShift μ T tag) R
  have ht := abs_sub_le
    ((conditionalTruncationKernel μ T tag).real
      ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier))
    ((gaussianLaw A).real ((fun x => x + conditionalNormalizedShift μ T tag) ⁻¹' R.carrier))
    ((gaussianLaw A).real R.carrier)
  exact ht.trans (add_le_add hb hs)

theorem conditionalGoodKernel_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1)
    (hgood : matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T tag.1 - B * B.transpose) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T tag.1) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ≤
      (2 * relativeUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant * min 1
          (dimensionLog p * Real.sqrt
            (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose))) +
        12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ * Real.sqrt (dimensionLog p) := by
  let r := conditionalNormalizedShift μ T tag
  have hc := conditionalGoodKernel_shifted_rectangle_error_le μ hT tag hp hn
    (B * B.transpose) hB hgood A hA R
  have hg := (rectangleError_le_rectangleDistance (gaussianLaw A) id B
    (R.pullbackAdd r)).trans (unrestrictedGaussianComparison hp A B hB)
  rw [hA, proxyCovarianceDiscrepancy_eq_matrixMaxEntryNorm] at hg
  have hs := gaussian_translation_rectangle_error_le hp B hB r R
  have ht := abs_sub_le
    ((conditionalTruncationKernel μ T tag).real
      ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier))
    ((gaussianLaw A).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw B).real R.carrier)
  have ht' := abs_sub_le ((gaussianLaw A).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw B).real ((fun x => x + r) ⁻¹' R.carrier)) ((gaussianLaw B).real R.carrier)
  simp only [rectangleError, Rect.carrier_pullbackAdd, Set.preimage_id] at hg hs ⊢
  exact ht.trans ((add_le_add hc (ht'.trans (add_le_add hg hs))).trans_eq (by ring))

theorem conditionalKernel_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ≤
      (2 * relativeUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant *
          (dimensionLog p * Real.sqrt
            (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose))) +
        12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ * Real.sqrt (dimensionLog p) +
        2 * matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose) := by
  let d := matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose)
  have hd : 0 ≤ d := norm_nonneg _
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hC : 0 ≤ unrestrictedGaussianComparisonConstant :=
    zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant
  by_cases hgood : d ≤ 1 / 2
  · obtain ⟨A, hA⟩ := conditionalRetained_gaussian_factor_exists μ hT tag.1
    have hc := conditionalGoodKernel_rectangle_error_le μ hT tag hp hn B hB hgood A hA R
    have hmin := mul_le_mul_of_nonneg_left
      (min_le_right (1 : ℝ) (dimensionLog p * Real.sqrt d)) hC
    dsimp only [d] at hmin
    exact (hc.trans (add_le_add_right (add_le_add_left hmin _) _)).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) hd))
  · have hbad : 1 ≤ 2 * d := by linarith [lt_of_not_ge hgood]
    have hbounded : 0 ≤ (2 * relativeUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (zero_le_one.trans one_le_relativeUniversalConstant))
        (le_min (by norm_num)
          (unrestrictedRate_nonneg (div_nonneg (mul_nonneg (by norm_num) hT)
            (Real.sqrt_nonneg _)) hL))
    have hcov := mul_nonneg hC (mul_nonneg hL (Real.sqrt_nonneg d))
    have hshift : 0 ≤ 12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ *
        Real.sqrt (dimensionLog p) := by positivity
    exact (rectangleError_le_one _ _ _ R).trans
      (hbad.trans (le_add_of_nonneg_left (add_nonneg (add_nonneg hbounded hcov) hshift)))

theorem conditionalPolynomial_raw_rectangleDistance_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1)
    (hR : Integrable (fun x => ‖conditionalNormalizedShift μ T
      (observedTruncationMask T x, observedExceptionalArray T x)‖) (Measure.pi μ)) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B ≤
      (2 * relativeUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant * dimensionLog p * Real.sqrt
          (∫ x, matrixMaxEntryNorm
            (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose) ∂Measure.pi μ) +
        12 * Real.exp (3 / 2 : ℝ) *
          (∫ x, ‖conditionalNormalizedShift μ T
            (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) *
              Real.sqrt (dimensionLog p) +
        2 * (∫ x, matrixMaxEntryNorm
          (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose) ∂Measure.pi μ) := by
  let d : (Fin n → Vector p) → ℝ := fun x => matrixMaxEntryNorm
    (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose)
  let r : (Fin n → Vector p) → ℝ := fun x => ‖conditionalNormalizedShift μ T
    (observedTruncationMask T x, observedExceptionalArray T x)‖
  let a := (2 * relativeUniversalConstant) *
    min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p))
  let c := unrestrictedGaussianComparisonConstant
  let k := 12 * Real.exp (3 / 2 : ℝ)
  let L := dimensionLog p
  have hiD := integrable_observedConditionalCovarianceDeviation μ T (B * B.transpose)
  have hiS := integrable_sqrt_of_integrable_nonneg (Measure.pi μ) d hiD (fun _ => norm_nonneg _)
  have hi1 : Integrable (fun x => a + c * (L * Real.sqrt (d x))) (Measure.pi μ) :=
    (integrable_const a).add ((hiS.const_mul L).const_mul c)
  have hi2 : Integrable (fun x => a + c * (L * Real.sqrt (d x)) + k * r x * Real.sqrt L)
      (Measure.pi μ) := hi1.add ((hR.const_mul k).mul_const (Real.sqrt L))
  have hi3 : Integrable (fun x => a + c * (L * Real.sqrt (d x)) + k * r x * Real.sqrt L + 2 * d x)
      (Measure.pi μ) := hi2.add (hiD.const_mul 2)
  have he1 := integral_add (integrable_const a) ((hiS.const_mul L).const_mul c)
  have he2 := integral_add hi1 ((hR.const_mul k).mul_const (Real.sqrt L))
  have he3 := integral_add hi2 (hiD.const_mul 2)
  simp only [Pi.add_apply, integral_const, measureReal_univ_eq_one, one_smul,
    integral_const_mul, integral_mul_const] at he1 he2 he3
  have hj := integral_sqrt_le_sqrt_integral (Measure.pi μ) d hiD (fun _ => norm_nonneg _)
  have hjc := mul_le_mul_of_nonneg_left hj
    (mul_nonneg (zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))
  apply rectangleDistance_le
  intro R
  have hiE : Integrable (fun x => rectangleError (conditionalTruncationKernel μ T
      (observedTruncationMask T x, observedExceptionalArray T x))
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R) (Measure.pi μ) := by
    let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
    have hW : Measurable W := by
      unfold W normalizedObservationSum sumVector
      exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
    have hm : Measurable (fun x : Fin n → Vector p =>
        |(conditionalTruncationKernel μ T (observedTruncationMask T x,
          observedExceptionalArray T x)).real (W ⁻¹' R.carrier) - (gaussianLaw B).real R.carrier|) :=
      (((conditionalTruncationKernel μ T).measurable_coe
      (R.measurableSet_carrier.preimage hW)).ennreal_toReal.comp
        ((measurable_observedTruncationMask T).prodMk (measurable_observedExceptionalArray T))).sub
      measurable_const |>.abs
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact rectangleError_le_one _ _ _ R
  have hb := integral_mono hiE hi3 (fun x => conditionalKernel_rectangle_error_le
    μ hT (observedTruncationMask T x, observedExceptionalArray T x) hp hn B hB R)
  rw [he3, he2, he1] at hb
  have hdist := (rectangleError_le_integral_conditionalKernel_rectangleError μ T B R).trans hb
  have hjc' : c * (L * ∫ x, Real.sqrt (d x) ∂Measure.pi μ) ≤
      c * L * Real.sqrt (∫ x, d x ∂Measure.pi μ) := by
    change c * L * (∫ x, Real.sqrt (d x) ∂Measure.pi μ) ≤
      c * L * Real.sqrt (∫ x, d x ∂Measure.pi μ) at hjc
    simpa only [mul_assoc] using hjc
  exact hdist.trans (add_le_add_right (add_le_add_right (add_le_add_left hjc' a) _) _)

def conditionalPolynomialConstant : ℝ :=
  1 + 8 * relativeUniversalConstant + 3 * unrestrictedGaussianComparisonConstant +
    24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12

theorem one_le_conditionalPolynomialConstant : 1 ≤ conditionalPolynomialConstant := by
  have hc := one_le_relativeUniversalConstant
  have hg := one_le_unrestrictedGaussianComparisonConstant
  have he := one_le_envelopeMaximumConstant
  have hep : 0 ≤ 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant := by positivity
  unfold conditionalPolynomialConstant
  linarith

theorem conditionalPolynomial_threshold {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (A : Matrix (Fin p) (Fin p) ℝ) (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hfactor : A * A.transpose = covariance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i))) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let i : Fin n := ⟨0, by omega⟩
  let v := truncationVarianceBudget B T q
  let L := dimensionLog p
  let t := T / Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ) * Real.sqrt (dimensionLog n)
  let z := L * Real.sqrt v
  let w := polynomialEnvelopeV n p B q
  have hv : 0 ≤ v := (h i).varianceBudget_nonneg
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hT : 0 ≤ T := (h i).threshold_pos.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hz : 0 ≤ z := mul_nonneg (zero_le_one.trans hL) (Real.sqrt_nonneg _)
  have hw : 0 ≤ w := by unfold w polynomialEnvelopeV; positivity
  have hTquarter : (1 / 4 : ℝ) ≤ T := by linarith [(h i).threshold]
  have hC : 1 ≤ conditionalPolynomialConstant := one_le_conditionalPolynomialConstant
  change rectangleDistance (Measure.pi μ)
    (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalPolynomialConstant * min 1 (t + z + w)
  by_cases hvone : v ≤ 1
  · have hiR : Integrable (fun x => ‖conditionalNormalizedShift μ T
        (observedTruncationMask T x, observedExceptionalArray T x)‖) (Measure.pi μ) := by
      simpa only [conditionalNormalizedShift] using observed_exceptional_shift_norm_integrable μ h
    have hraw := conditionalPolynomial_raw_rectangleDistance_le μ hT hp hn A hunit hiR
    have hd := expected_conditional_covariance_deviation_actual μ h hn
    rw [← hfactor] at hd
    have hds : Real.sqrt (∫ x, matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
        3 * Real.sqrt v := by
      apply (Real.sqrt_le_sqrt hd).trans
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt hv]
    have hvz : v ≤ z := by
      have hs : v ≤ Real.sqrt v := by
        nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
      exact hs.trans (by dsimp only [z]; nlinarith [Real.sqrt_nonneg v])
    have hbounded : (2 * relativeUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) L) ≤
        (8 * relativeUniversalConstant) * t := by
      have hb := (min_le_right (1 : ℝ) (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) L)).trans
        (conditionalBoundedRate_le hp hn hTquarter)
      have hm := mul_le_mul_of_nonneg_left hb
        (by linarith [one_le_relativeUniversalConstant] : 0 ≤ 2 * relativeUniversalConstant)
      convert hm using 1
      ring
    have hgaussian := mul_le_mul_of_nonneg_left hds
      (mul_nonneg (zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant) (zero_le_one.trans hL))
    have hshift := observed_exceptional_shift_maximum_le μ h hp hn
    have hshift' : 12 * Real.exp (3 / 2 : ℝ) *
        (∫ x, ‖conditionalNormalizedShift μ T
          (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) * Real.sqrt L ≤
        (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * (z + w) := by
      have hm := mul_le_mul_of_nonneg_left hshift
        (by positivity : 0 ≤ 12 * Real.exp (3 / 2 : ℝ))
      dsimp only [conditionalNormalizedShift, L, z, w, v]
      convert hm using 1 <;> ring
    have hbias1 : 2 * (∫ x, matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
        12 * v := by linarith [hd]
    have hbias := hbias1.trans (mul_le_mul_of_nonneg_left hvz (by norm_num : (0 : ℝ) ≤ 12))
    have hraw' : rectangleDistance (Measure.pi μ)
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
        (8 * relativeUniversalConstant) * t +
          (3 * unrestrictedGaussianComparisonConstant) * z +
          (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * (z + w) + 12 * z := by
      have hg : unrestrictedGaussianComparisonConstant * L *
          Real.sqrt (∫ x, matrixMaxEntryNorm
            (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
            (3 * unrestrictedGaussianComparisonConstant) * z := by
        convert hgaussian using 1
        ring
      exact hraw.trans (add_le_add (add_le_add (add_le_add hbounded hg) hshift') hbias)
    have hc1 : 8 * relativeUniversalConstant ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      have hg := one_le_unrestrictedGaussianComparisonConstant
      have he := one_le_envelopeMaximumConstant
      have hep : 0 ≤ 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant := by positivity
      linarith
    have hc2 : 3 * unrestrictedGaussianComparisonConstant +
        24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12 ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      linarith [one_le_relativeUniversalConstant]
    have hc3 : 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      linarith [one_le_relativeUniversalConstant, one_le_unrestrictedGaussianComparisonConstant]
    have hrho : rectangleDistance (Measure.pi μ)
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
        conditionalPolynomialConstant * (t + z + w) := by
      calc
        _ ≤ _ := hraw'
        _ = (8 * relativeUniversalConstant) * t +
            (3 * unrestrictedGaussianComparisonConstant +
              24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12) * z +
            (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * w := by ring
        _ ≤ conditionalPolynomialConstant * t + conditionalPolynomialConstant * z +
            conditionalPolynomialConstant * w := add_le_add
              (add_le_add (mul_le_mul_of_nonneg_right hc1 ht) (mul_le_mul_of_nonneg_right hc2 hz))
              (mul_le_mul_of_nonneg_right hc3 hw)
        _ = _ := by ring
    by_cases hs : 1 ≤ t + z + w
    · rw [min_eq_left hs, mul_one]
      exact (rectangleDistance_le_one _ _ _).trans hC
    · rw [min_eq_right (le_of_not_ge hs)]
      exact hrho
  · have hsqrt : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr (le_of_not_ge hvone)
    have hz1 : 1 ≤ z := by dsimp only [z]; nlinarith
    rw [min_eq_left (by linarith : 1 ≤ t + z + w), mul_one]
    exact (rectangleDistance_le_one _ _ _).trans hC

theorem polynomialEnvelope_threshold
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B T q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hT : 2 * B ≤ T) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hX i).aemeasurable
  have hm := conditionalTruncationMomentHypotheses_marginal μ X hX hB hT hq hmoment hbudget hcenter
  have htuple : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hind
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hW : Measurable W := by
    unfold W normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  have hcov : covariance (Measure.pi ν) W = covariance μ (normalizedObservationSum X) := by
    rw [← hmap, covariance_map_of_measurable μ _ htuple W hW]
    rfl
  have hh := conditionalPolynomial_threshold ν hm hp hn hB A hunit (hfactor.trans hcov.symm)
  rw [normalized_product_rectangleDistance_eq μ X hX hind] at hh
  exact hh

theorem polynomialEnvelope_threshold_of_average_variances
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B T q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hT : 2 * B ≤ T) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hX i).aemeasurable
  have hm := conditionalTruncationMomentHypotheses_marginal μ X hX hB hT hq hmoment hbudget hcenter
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ := by
    apply (memLp_two_iff_integrable_sq
      ((measurable_pi_apply j).comp (hX i)).aestronglyMeasurable).mpr
    exact (integrable_map_measure ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
      (hX i).aemeasurable).mp ((hm i).integrable_coordinate_sq j)
  have hunit (j : Fin p) : (A * A.transpose) j j = 1 := by
    rw [hfactor]
    have hh := normalizedSummands_unit_covariance hind hL2 hcenter haverage j
    rw [sumVector_normalizedSummands] at hh
    exact hh
  exact polynomialEnvelope_threshold μ X hX hind hp hn hB hT hq hmoment hbudget hcenter A hunit hfactor

def polynomialEnvelopeTransferConstant : ℝ := 4 * conditionalPolynomialConstant

theorem one_le_polynomialEnvelopeTransferConstant : 1 ≤ polynomialEnvelopeTransferConstant := by
  unfold polynomialEnvelopeTransferConstant
  linarith [one_le_conditionalPolynomialConstant]

/-- Proposition 2, on every original probability space and every genuine
independent centered envelope-moment array. The Gaussian covariance may be
singular and the observation laws need not coincide. -/
theorem polynomialEnvelopeTransfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      polynomialEnvelopeTransferConstant * min 1 (polynomialEnvelopeTransferRate n p B q) := by
  by_cases hlarge : dimensionLog p * dimensionLog n ≤ (n : ℝ)
  · have hT := polynomialTruncationThreshold_ge hp hn (zero_le_one.trans hB)
      (by linarith : 0 < q) hlarge
    have hh := polynomialEnvelope_threshold_of_average_variances μ X hX hind hp hn hB hT hq
      hmoment hbudget hcenter haverage A hfactor
    have hrate := min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4)
      (polynomialTruncation_threshold_rate_le hp hn (zero_lt_one.trans_le hB) hq)
    have hc := mul_le_mul_of_nonneg_left hrate
      (zero_le_one.trans one_le_conditionalPolynomialConstant)
    exact hh.trans (hc.trans_eq (by unfold polynomialEnvelopeTransferConstant; ring))
  · have hr := polynomialEnvelopeTransferRate_ge_one_of_small hp hn hB hq (le_of_not_ge hlarge)
    rw [min_eq_left hr, mul_one]
    exact (rectangleDistance_le_one _ _ _).trans one_le_polynomialEnvelopeTransferConstant


end
end RectangleCLT.Companion.SplitV4.Printed
