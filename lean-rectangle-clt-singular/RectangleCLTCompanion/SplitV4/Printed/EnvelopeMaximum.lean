import RectangleCLTCompanion.SplitV4.Printed.Bernstein
import RectangleCLTCompanion.SplitV4.ConditionalExceptionalMaximum

/-! The printed Appendix E.1 argument: genuine centered norm truncation,
classical Bernstein on both coordinate signs, literal layer-cake integration,
and the omitted envelope-moment tail.  The earlier certificate's Jensen-based
proof is retained under its original declaration. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem expected_maximum_under_envelope_moment {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (hp : 1 ≤ p)
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    {q A v : ℝ} (hq : 2 < q) (hA : 0 ≤ A)
    (hsecond : ∀ i j, Integrable (fun ω => Y i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 2 ∂μ) ≤ v)
    (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤
      envelopeMaximumConstant * (Real.sqrt (v * dimensionLog p) +
        A * dimensionLog p ^ (1 - 1 / q)) := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 < q := by linarith
  have hC : 0 ≤ envelopeMaximumConstant := zero_le_one.trans one_le_envelopeMaximumConstant
  by_cases hAzero : A = 0
  · subst A
    have hzbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ 0 := by
      simpa only [Real.zero_rpow hqpos.ne'] using hbudget
    have hz := sumVector_ae_zero_of_envelope_budget_zero Y hqpos hmoment hzbudget
    have hnormzero : (fun ω => ‖sumVector Y ω‖) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      simp only [hω, Pi.zero_apply, norm_zero]
    rw [integral_congr_ae hnormzero]
    simp only [Pi.zero_apply, integral_zero, zero_mul, add_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)
  have hApos : 0 < A := hA.lt_of_ne' hAzero
  let L := dimensionLog p
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let u := A / L ^ (1 / q)
  have hu : 0 < u := div_pos hApos (Real.rpow_pos_of_pos hL _)
  have hv : 0 ≤ v := by
    let j : Fin p := ⟨0, by omega⟩
    exact (Finset.sum_nonneg (fun i _ => integral_nonneg
      (fun ω => sq_nonneg (Y i ω j)))).trans (hvariance j)
  let Z := envelopeCenteredTruncation μ Y u
  have hZ : BoundedIndependentHypotheses μ Z (2 * u) :=
    envelopeCenteredTruncation_boundedHypotheses hY hind hu.le
  have hZvar (j : Fin p) : (∑ i, ∫ ω, Z i ω j ^ 2 ∂μ) ≤ v :=
    (envelopeCenteredTruncation_second_moment_sum_le hY hu.le hsecond j).trans (hvariance j)
  have hb := bounded_vector_bernstein_maximum_by_tail_integration hZ hp (by linarith : 0 < 2 * u) hv hZvar
  have ht := integral_norm_sum_le_centeredTruncation_add_tail hY hcenter hu hqone hmoment A hbudget
  have hid := envelope_cutoff_rate_identities hApos hL hqone
  have hul : u * L = A * L ^ (1 - 1 / q) := hid.1
  have hrest : A ^ q / u ^ (q - 1) = A * L ^ (1 - 1 / q) := hid.2
  calc
    _ ≤ (∫ ω, ‖sumVector Z ω‖ ∂μ) + 2 * A ^ q / u ^ (q - 1) := ht
    _ ≤ 3 * (Real.sqrt (v * L) + (2 * u) * L) +
        2 * A ^ q / u ^ (q - 1) := add_le_add_right hb _
    _ = 3 * (Real.sqrt (v * L) + 2 * (A * L ^ (1 - 1 / q))) +
        2 * (A * L ^ (1 - 1 / q)) := by
      rw [mul_assoc, hul, mul_div_assoc, hrest]
    _ ≤ _ := by
      unfold envelopeMaximumConstant
      change _ ≤ (4 + 2 * Real.exp 1) * (Real.sqrt (v * L) + A * L ^ (1 - 1 / q))
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have hAterm : 0 ≤ A * L ^ (1 - 1 / q) := by positivity
      nlinarith [Real.sqrt_nonneg (v * L),
        mul_nonneg (by linarith : 0 ≤ Real.exp 1 - 2) hAterm,
        mul_nonneg (by linarith : 0 ≤ 2 * Real.exp 1 + 1) (Real.sqrt_nonneg (v * L))]



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
end RectangleCLT.Companion.SplitV4.Printed
