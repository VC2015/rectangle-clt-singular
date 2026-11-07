import RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds
import RectangleCLTCompanion.SplitV4.EnvelopeMaximum

/-!
# Expected maximum of the actual exceptional component

The residual observations are the actual Appendix E maps of the original
nonidentical independent product array. Their genuine second and q moments
are proved before applying the checked envelope-maximum theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def exceptionalArray {p n : ℕ} (μ : Fin n → Measure (Vector p)) (T : ℝ) :
    Fin n → (Fin n → Vector p) → Vector p :=
  fun i x => conditionalExceptionalPart (μ i) T (x i)

theorem integrable_vectorProduct_eval {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin n) (f : Vector p → ℝ) (hi : Integrable f (μ i)) :
    Integrable (fun x : Fin n → Vector p => f (x i)) (Measure.pi μ) := by
  have hs : Integrable f ((Measure.pi μ).map (fun x => x i)) := by rw [vectorProduct_map_eval]; exact hi
  exact (integrable_map_measure hs.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp hs

theorem integral_vectorProduct_eval {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin n) (f : Vector p → ℝ) (hi : Integrable f (μ i)) :
    (∫ x : Fin n → Vector p, f (x i) ∂Measure.pi μ) = ∫ x, f x ∂μ i := by
  have hs : Integrable f ((Measure.pi μ).map (fun x => x i)) := by rw [vectorProduct_map_eval]; exact hi
  have he := integral_map (μ := Measure.pi μ) (measurable_pi_apply i).aemeasurable hs.aestronglyMeasurable
  rw [vectorProduct_map_eval] at he
  exact he.symm

theorem exceptionalArray_measurable {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (i : Fin n) :
    Measurable (exceptionalArray μ T i) :=
  (measurable_conditionalExceptionalPart (μ i) T).comp (measurable_pi_apply i)

theorem exceptionalArray_independent {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    iIndepFun (exceptionalArray μ T) (Measure.pi μ) :=
  conditionalExceptionalPart_independent _ (vectorProduct_independent μ) μ T

theorem exceptionalArray_centered {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (i : Fin n) (j : Fin p) :
    (∫ x, exceptionalArray μ T i x j ∂Measure.pi μ) = 0 := by
  have hi : Integrable (fun x : Vector p => conditionalExceptionalPart (μ i) T x j) (μ i) := by
    have hgood : Integrable (fun x : Vector p => conditionalGoodPart (μ i) T x j) (μ i) := by
      apply (integrable_const (2 * T)).mono'
        ((measurable_pi_apply j).comp (measurable_conditionalGoodPart (μ i) T)).aestronglyMeasurable
      exact ae_of_all _ fun x => (norm_le_pi_norm _ j).trans (norm_conditionalGoodPart_le (μ i) (h i).threshold_pos.le x)
    have he (x : Vector p) : conditionalExceptionalPart (μ i) T x j = x j - conditionalGoodPart (μ i) T x j := by
      have hh := congrFun (conditional_decomposition (μ i) T x) j
      simp only [Pi.add_apply] at hh
      linarith
    simp_rw [he]
    exact ((h i).integrable_coordinate j).sub hgood
  rw [show (fun x => exceptionalArray μ T i x j) =
    (fun x : Fin n → Vector p => conditionalExceptionalPart (μ i) T (x i) j) from rfl,
    integral_vectorProduct_eval μ i _ hi]
  exact conditionalExceptionalPart_centered (μ i) (h i).threshold_pos.le j
    ((h i).integrable_coordinate j) ((h i).centered j)

theorem exceptionalArray_second_integrable {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (i : Fin n) (j : Fin p) :
    Integrable (fun x => exceptionalArray μ T i x j ^ 2) (Measure.pi μ) :=
  integrable_vectorProduct_eval μ i _ ((h i).integrable_exceptionalPart_coordinate_sq j)

theorem exceptionalArray_second_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (i : Fin n) (j : Fin p) :
    (∫ x, exceptionalArray μ T i x j ^ 2 ∂Measure.pi μ) ≤ 2 * truncationVarianceBudget B T q := by
  rw [show (fun x => exceptionalArray μ T i x j ^ 2) =
    (fun x : Fin n → Vector p => conditionalExceptionalPart (μ i) T (x i) j ^ 2) from rfl,
    integral_vectorProduct_eval μ i _ ((h i).integrable_exceptionalPart_coordinate_sq j)]
  exact (h i).integral_exceptionalPart_coordinate_sq_le j

theorem exceptionalArray_q_integrable {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (i : Fin n) :
    Integrable (fun x => ‖exceptionalArray μ T i x‖ ^ q) (Measure.pi μ) :=
  integrable_vectorProduct_eval μ i _ (h i).integrable_exceptionalPart_q

theorem exceptionalArray_q_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (i : Fin n) :
    (∫ x, ‖exceptionalArray μ T i x‖ ^ q ∂Measure.pi μ) ≤ 2 * B ^ q := by
  rw [show (fun x => ‖exceptionalArray μ T i x‖ ^ q) =
    (fun x : Fin n → Vector p => ‖conditionalExceptionalPart (μ i) T (x i)‖ ^ q) from rfl,
    integral_vectorProduct_eval μ i _ (h i).integrable_exceptionalPart_q]
  exact (h i).integral_exceptionalPart_q_le

def exceptionalMomentScale (n : ℕ) (B q : ℝ) : ℝ := 2 * B * (n : ℝ) ^ (1 / q)

theorem exceptionalMomentScale_q_power {n : ℕ} {B q : ℝ}
    (hn : 1 ≤ n) (hB : 0 ≤ B) (hq : 0 < q) :
    exceptionalMomentScale n B q ^ q = (2 : ℝ) ^ q * B ^ q * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (1 / q)) ^ q = (n : ℝ) := by
    rw [← Real.rpow_mul hnR.le, one_div_mul_cancel hq.ne', Real.rpow_one]
  unfold exceptionalMomentScale
  rw [Real.mul_rpow (mul_nonneg (by norm_num) hB) (Real.rpow_nonneg hnR.le _),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB, hp]

theorem exceptionalArray_raw_maximum_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (∫ x, ‖sumVector (exceptionalArray μ T) x‖ ∂Measure.pi μ) ≤
      envelopeMaximumConstant *
        (Real.sqrt ((2 * (n : ℝ) * truncationVarianceBudget B T q) * dimensionLog p) +
          exceptionalMomentScale n B q * dimensionLog p ^ (1 - 1 / q)) := by
  let i : Fin n := ⟨0, by omega⟩
  have hB := (h i).B_pos
  have hq := (h i).q_gt_two
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hvariance (j : Fin p) :
      (∑ i, ∫ x, exceptionalArray μ T i x j ^ 2 ∂Measure.pi μ) ≤ 2 * (n : ℝ) * truncationVarianceBudget B T q := by
    calc
      _ ≤ ∑ _i : Fin n, 2 * truncationVarianceBudget B T q :=
        Finset.sum_le_sum (fun i _ => exceptionalArray_second_le μ h i j)
      _ = _ := by simp; ring
  have hbudget : (∑ i, ∫ x, ‖exceptionalArray μ T i x‖ ^ q ∂Measure.pi μ) ≤
      exceptionalMomentScale n B q ^ q := by
    rw [exceptionalMomentScale_q_power hn hB.le (by linarith : 0 < q)]
    have ht : (2 : ℝ) ≤ 2 ^ q := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (1 : ℝ) ≤ q)
    calc
      _ ≤ ∑ _i : Fin n, 2 * B ^ q := Finset.sum_le_sum (fun i _ => exceptionalArray_q_le μ h i)
      _ = 2 * B ^ q * (n : ℝ) := by simp; ring
      _ ≤ 2 ^ q * B ^ q * (n : ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hB.le q)) hnR.le
  apply expected_maximum_under_envelope_moment _ hp (exceptionalArray_measurable μ T)
    (exceptionalArray_independent μ T) (exceptionalArray_centered μ h) hq
    (show 0 ≤ exceptionalMomentScale n B q by unfold exceptionalMomentScale; positivity)
    (exceptionalArray_second_integrable μ h) hvariance (exceptionalArray_q_integrable μ h) hbudget

/-- The paper's `V_q`, with all logarithms recomputed in the actual dimension. -/
def polynomialEnvelopeV (n p : ℕ) (B q : ℝ) : ℝ :=
  B * dimensionLog p ^ (3 / 2 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)

theorem scaled_exceptional_moment_term {n p : ℕ} {B q : ℝ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    Real.sqrt (dimensionLog p) * ((Real.sqrt (n : ℝ))⁻¹ *
      (exceptionalMomentScale n B q * dimensionLog p ^ (1 - 1 / q))) =
      2 * polynomialEnvelopeV n p B q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hLp : Real.sqrt (dimensionLog p) * dimensionLog p ^ (1 - 1 / q) =
      dimensionLog p ^ (3 / 2 - 1 / q) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (2 * B * (n : ℝ) ^ (1 / q) / Real.sqrt (n : ℝ)) *
        (Real.sqrt (dimensionLog p) * dimensionLog p ^ (1 - 1 / q)) := by
      unfold exceptionalMomentScale
      ring
    _ = 2 * polynomialEnvelopeV n p B q := by
      rw [hLp]
      unfold polynomialEnvelopeV
      rw [Real.rpow_sub hnR, ← Real.sqrt_eq_rpow]
      field_simp [(Real.sqrt_pos.mpr hnR).ne', (Real.rpow_pos_of_pos hnR (1 / q)).ne']
      ring

theorem scaled_exceptional_variance_term {n p : ℕ} {v : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hv : 0 ≤ v) :
    Real.sqrt (dimensionLog p) * ((Real.sqrt (n : ℝ))⁻¹ *
      Real.sqrt ((2 * (n : ℝ) * v) * dimensionLog p)) ≤
      2 * dimensionLog p * Real.sqrt v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have he : Real.sqrt ((2 * (n : ℝ) * v) * dimensionLog p) =
      Real.sqrt (n : ℝ) * Real.sqrt (2 * v * dimensionLog p) := by
    rw [← Real.sqrt_mul hnR.le]
    congr 1
    ring
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  calc
    _ = Real.sqrt (dimensionLog p) * Real.sqrt (2 * v * dimensionLog p) := by
      rw [he]
      field_simp [(Real.sqrt_pos.mpr hnR).ne']
    _ = Real.sqrt (2 : ℝ) * dimensionLog p * Real.sqrt v := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = Real.sqrt (2 : ℝ) * Real.sqrt v * (Real.sqrt (dimensionLog p)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hL]; ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hL (Real.sqrt_nonneg v))
      convert hh using 1 <;> ring

theorem exceptional_normalized_norm_integrable {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) :
    Integrable (fun x => ‖normalizedObservationSum (exceptionalArray μ T) x‖) (Measure.pi μ) := by
  have hi (i : Fin n) : Integrable (exceptionalArray μ T i) (Measure.pi μ) :=
    integrable_of_bennett_norm_moment (exceptionalArray_measurable μ T i)
      (by linarith [(h i).q_gt_two]) (exceptionalArray_q_integrable μ h i)
  have hs : Integrable (sumVector (exceptionalArray μ T)) (Measure.pi μ) :=
    integrable_finset_sum Finset.univ (fun i _ => hi i)
  exact (hs.smul ((Real.sqrt (n : ℝ))⁻¹)).norm

/-- The actual normalized exceptional sum has exactly the shift cost in
Appendix E. The constant is absolute, so in particular depends on no array,
dimension, covariance, or truncation threshold. -/
theorem exceptional_normalized_maximum_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    Real.sqrt (dimensionLog p) *
      (∫ x, ‖normalizedObservationSum (exceptionalArray μ T) x‖ ∂Measure.pi μ) ≤
      (2 * envelopeMaximumConstant) *
        (dimensionLog p * Real.sqrt (truncationVarianceBudget B T q) + polynomialEnvelopeV n p B q) := by
  let i : Fin n := ⟨0, by omega⟩
  have hv := (h i).varianceBudget_nonneg
  have hsqrt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hL : 0 ≤ Real.sqrt (dimensionLog p) := Real.sqrt_nonneg _
  have hC : 0 ≤ envelopeMaximumConstant := zero_le_one.trans one_le_envelopeMaximumConstant
  have hb := exceptionalArray_raw_maximum_le μ h hp hn
  have hnrm : (∫ x, ‖normalizedObservationSum (exceptionalArray μ T) x‖ ∂Measure.pi μ) =
      (Real.sqrt (n : ℝ))⁻¹ * ∫ x, ‖sumVector (exceptionalArray μ T) x‖ ∂Measure.pi μ := by
    simp only [normalizedObservationSum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt, integral_const_mul]
  rw [hnrm]
  calc
    _ ≤ Real.sqrt (dimensionLog p) * ((Real.sqrt (n : ℝ))⁻¹ *
        (envelopeMaximumConstant *
          (Real.sqrt ((2 * (n : ℝ) * truncationVarianceBudget B T q) * dimensionLog p) +
            exceptionalMomentScale n B q * dimensionLog p ^ (1 - 1 / q)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsqrt) hL
    _ = envelopeMaximumConstant *
        (Real.sqrt (dimensionLog p) * ((Real.sqrt (n : ℝ))⁻¹ *
          Real.sqrt ((2 * (n : ℝ) * truncationVarianceBudget B T q) * dimensionLog p)) +
        Real.sqrt (dimensionLog p) * ((Real.sqrt (n : ℝ))⁻¹ *
          (exceptionalMomentScale n B q * dimensionLog p ^ (1 - 1 / q)))) := by ring
    _ ≤ envelopeMaximumConstant *
        (2 * dimensionLog p * Real.sqrt (truncationVarianceBudget B T q) + 2 * polynomialEnvelopeV n p B q) := by
      rw [scaled_exceptional_moment_term hn hp]
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (scaled_exceptional_variance_term hn hp hv) _) hC
    _ = _ := by ring

theorem observed_exceptional_normalized_shift {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (x : Fin n → Vector p) :
    (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i, conditionalExceptionalShift μ T (observedTruncationMask T x) (observedExceptionalArray T x) i =
      normalizedObservationSum (exceptionalArray μ T) x := by
  have hh := congrArg (fun r : Fin n → Vector p => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, r i)
    (conditionalExceptionalShift_observed μ T x)
  exact hh

theorem observed_exceptional_shift_norm_integrable {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) :
    Integrable (fun x : Fin n → Vector p => ‖(Real.sqrt (n : ℝ))⁻¹ •
      ∑ i, conditionalExceptionalShift μ T (observedTruncationMask T x) (observedExceptionalArray T x) i‖)
      (Measure.pi μ) := by
  simp_rw [observed_exceptional_normalized_shift μ T]
  exact exceptional_normalized_norm_integrable μ h

theorem observed_exceptional_shift_maximum_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    Real.sqrt (dimensionLog p) *
      (∫ x : Fin n → Vector p, ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i, conditionalExceptionalShift μ T (observedTruncationMask T x) (observedExceptionalArray T x) i‖
        ∂Measure.pi μ) ≤
      (2 * envelopeMaximumConstant) *
        (dimensionLog p * Real.sqrt (truncationVarianceBudget B T q) + polynomialEnvelopeV n p B q) := by
  simp_rw [observed_exceptional_normalized_shift μ T]
  exact exceptional_normalized_maximum_le μ h hp hn

end

end RectangleCLT.Companion.SplitV4
