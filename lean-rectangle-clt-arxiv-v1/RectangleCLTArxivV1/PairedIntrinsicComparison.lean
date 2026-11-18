import RectangleCLTArxivV1.PairedGaussianRemainder
import RectangleCLTArxivV1.PairedGaussianEndpointSmoothing
import RectangleCLTCompanion.SplitV4.LargeIncrementComparison

/-!
# Intrinsic paired interpolation of actual probability laws

The exact paired Slepian identity, conditional truncated covariance, drift,
and genuine fourth derivative remainder are reused. Each derivative term
is newly averaged using the actual Gaussian width before the integrable
time weights are applied. No logarithmic comparison theorem is wrapped.
-/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section

theorem intrinsic_abs_largeIncrementHessianTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (ht : t < 1) :
    |largeIncrementHessianTerm μ ξ A s h t| ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * (gaussianMaximumMean A / Real.sqrt (1-t))) *
        largeIncrementMatrixCost μ ξ A h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hM (j k : Fin p) : Measurable (fun ω =>
      (copyArrayTruncatedCovariance μ ξ ω h - A * A.transpose) j k) :=
    (measurable_copyArrayTruncatedCovariance_entry (μ := μ) ξ hξ hh j k).sub measurable_const
  have hMi := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    (μ := μ) ξ hξ hind hh (A * A.transpose)
  exact (abs_integral_le_integral_abs).trans
    (intrinsic_slepian_weighted_hessian_contraction hp s μ A hdiag (sumVector ξ)
      (fun ω => copyArrayTruncatedCovariance μ ξ ω h - A * A.transpose) hW hM hMi ht)

theorem intrinsic_abs_largeIncrementGradientTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hξi : ∀ i, Integrable (ξ i) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (ht : t < 1) :
    |largeIncrementGradientTerm μ ξ A s h t| ≤
      (Real.exp (3 / 2 : ℝ) * (gaussianMaximumMean A / Real.sqrt (1-t))) *
        largeIncrementMeanCost μ ξ h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hb := measurable_copyArrayLargeMean μ ξ hξ h
  have hbi := (integrable_copyArrayLargeMean μ ξ hξ hξi hh).norm
  exact (abs_integral_le_integral_abs).trans
    (intrinsic_slepian_weighted_gradient_contraction hp s μ A hdiag (sumVector ξ)
      (fun ω => copyArrayLargeMean μ ξ ω h) hW hb hbi ht)


theorem intrinsic_abs_largeIncrementRemainderTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (hband : h ≤ s.bandwidth) (ht : 0 < t) (ht1 : t < 1) :
    |largeIncrementRemainderTerm μ ξ A s h t| ≤
      (largeIncrementFourthConstant * (gaussianMaximumMean A / Real.sqrt (1-t)) / s.bandwidth ^ 3) *
        largeIncrementFourthCost μ ξ h := by
  exact intrinsic_pairedGaussianRemainder_le μ hp s A hdiag ξ hξ ht ht1 hh hband

/-- The actual smooth expectation comparison, before the conditional
large-increment mean is bounded by the expected maximum of the tail sum.
All three derivative estimates are proved inputs, rather than premises.
The endpoint passage uses the genuine Slepian expectation continuity. -/
theorem intrinsic_largeIncrement_smooth_expectation_comparison_conditional
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h : ℝ} (hh : 0 ≤ h) (hband : h ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ g, s.F g ∂gaussianLaw A)| ≤
      largeIncrementComparisonConstant * gaussianMaximumMean A *
        (largeIncrementMatrixCost μ ξ A h / s.bandwidth + largeIncrementMeanCost μ ξ h +
          largeIncrementFourthCost μ ξ h / s.bandwidth ^ 3) := by
  let f := smootherC4Test s
  let φ := f.slepianExpectation μ (sumVector ξ) A
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hWi : Integrable (sumVector ξ) μ := integrable_finset_sum _ (fun i _ => hξi i)
  have hφ : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    f.continuousOn_slepianExpectation μ (sumVector ξ) hW hWi.norm A
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    f.hasDerivAt_arraySlepian μ ξ hξ hind hξi hmean A h hh ht.1 ht.2
  let a := 3 * Real.exp (3 / 2 : ℝ) / (2 * s.bandwidth) * gaussianMaximumMean A *
    largeIncrementMatrixCost μ ξ A h
  let b := Real.exp (3 / 2 : ℝ) / 2 * gaussianMaximumMean A * largeIncrementMeanCost μ ξ h
  let c := largeIncrementFourthConstant / (8 * s.bandwidth ^ 3) * gaussianMaximumMean A *
    largeIncrementFourthCost μ ξ h
  have hg := gaussianMaximumMean_nonneg A
  have hL : 0 ≤ gaussianMaximumMean A ^ 2 := sq_nonneg _
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt φ (deriv φ t) t := by
    change HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      (deriv (f.slepianExpectation μ (sumVector ξ) A) t) t
    rw [(hd t ht).deriv]
    exact hd t ht
  have hbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      |deriv φ t| ≤ a * gaussianTimeWeight t + b * pairedTimeWeight t + c * fourthTimeWeight t := by
    rw [(hd t ht).deriv]
    change |(1 / 2 : ℝ) * largeIncrementHessianTerm μ ξ A s h t -
      (1 / (2 * Real.sqrt t)) * largeIncrementGradientTerm μ ξ A s h t -
      t / 8 * largeIncrementRemainderTerm μ ξ A s h t| ≤ _
    have hratio : Real.sqrt (gaussianMaximumMean A ^ 2 / (1-t)) =
        gaussianMaximumMean A / Real.sqrt (1-t) := by
      rw [Real.sqrt_div hL, Real.sqrt_sq hg]
    have hb := paired_derivative_three_weight_bound (L := gaussianMaximumMean A ^ 2)
      hL s.bandwidth_pos ht.1 ht.2
      (by simpa only [hratio] using intrinsic_abs_largeIncrementHessianTerm_le μ hp s ξ hξ hind A hdiag hh ht.2)
      (by simpa only [hratio] using intrinsic_abs_largeIncrementGradientTerm_le μ hp s ξ hξ hξi A hdiag hh ht.2)
      (by simpa only [hratio] using intrinsic_abs_largeIncrementRemainderTerm_le μ hp s ξ hξ A hdiag hh hband ht.1 ht.2)
    simpa only [Real.sqrt_sq hg] using hb
  have htime := abs_sub_le_three_time_weights hφ hderiv a b c hbound
  obtain ⟨hM, hB, hQ⟩ := largeIncrementCosts_nonneg μ ξ A h
  have hcost := integrated_three_costs_le hL s.bandwidth_pos hM hB hQ
  rw [Real.sqrt_sq hg] at hcost
  have hfinal := htime.trans hcost
  simpa only [φ, C4Test.slepianExpectation_one, C4Test.slepianExpectation_zero,
    f, smootherC4Test_value] using hfinal

/-- The raw smooth-comparison estimate in the proof of E.1, with the
paper's actual expected maximum of the summed large increments. Finite
fourth moments discharge all first/L2 and centering requirements.  The
Gaussian covariance is the exact covariance of the independent sum.
Singular covariance and dependent coordinates are retained. -/
theorem intrinsic_largeIncrement_smooth_expectation_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ g, s.F g ∂gaussianLaw A)| ≤
      largeIncrementComparisonConstant * gaussianMaximumMean A *
        (largeIncrementMatrixCost μ ξ A s.bandwidth / s.bandwidth +
          pairedTailExpectedMaximum μ ξ s.bandwidth +
          largeIncrementFourthCost μ ξ s.bandwidth / s.bandwidth ^ 3) := by
  have hξi (i : Fin n) : Integrable (ξ i) μ :=
    integrable_vector_of_coordinate_fourth_moments μ (ξ i) (hξ i) (hfourth i)
  have hm (i : Fin n) : (∫ ω, ξ i ω ∂μ) = 0 :=
    integral_vector_eq_zero_of_coordinate_centered μ (ξ i) (hξi i) (hcenter i)
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hraw := intrinsic_largeIncrement_smooth_expectation_comparison_conditional μ hp s ξ hξ hind hξi hm
    A hdiag s.bandwidth_pos.le le_rfl
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hξ i)) (hfourth i j)
  have hmean := expected_copyArrayLargeMean_norm_le_of_memLp_two μ ξ hξ hL2 s.bandwidth_pos.le
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_left hmean _) _)
    (mul_nonneg largeIncrementComparisonConstant_nonneg (gaussianMaximumMean_nonneg A))

private theorem paired_log_two_mul_nat_le_dimensionLog {p : ℕ} (hp : 1 ≤ p) :
    Real.log (2 * (p : ℝ)) ≤ dimensionLog p := by
  apply Real.log_le_log
  · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
    positivity
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)

theorem intrinsic_largeIncrementGaussianComparison_bandwidth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {D h : ℝ} (hD : 0 ≤ D)
    (hbudget : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (hh : 0 < h) :
    rectangleDistance μ (sumVector ξ) A ≤ largeIncrementMasterConstant *
      (gaussianMaximumMean A / Real.sqrt (dimensionLog p)) * largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hξ i)) (hfourth i j)
  have hT : largeIncrementMatrixCost μ ξ A h ≤ (2 * matrixFluctuationConstant) *
      (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) + pairedTailVariance μ ξ h / 2 := by
    unfold largeIncrementMatrixCost
    rw [hA]
    exact expected_copyArrayTruncatedCovariance_sub_covariance_le ξ hξ hind hp hh hD hfourth hbudget hL2 hcenter
  have hQ : largeIncrementFourthCost μ ξ h ≤ h ^ 4 * dimensionLog p +
      (16 * (Real.exp 1 - 1)) * D := by
    have hq := expected_pairedFourthBudget_le μ hp ξ hξ hind hh hD hfourth hbudget
    change largeIncrementFourthCost μ ξ h ≤ _ at hq
    apply hq.trans
    have hlog := mul_le_mul_of_nonneg_left (paired_log_two_mul_nat_le_dimensionLog hp) (pow_nonneg hh.le 4)
    nlinarith
  have hv := pairedTailVariance_nonneg μ ξ h
  have hM : 0 ≤ pairedTailExpectedMaximum μ ξ h := integral_nonneg (fun z => norm_nonneg _)
  have hraw : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      largeIncrementComparisonConstant * gaussianMaximumMean A *
        (largeIncrementMatrixCost μ ξ A h / h + pairedTailExpectedMaximum μ ξ h +
          largeIncrementFourthCost μ ξ h / h ^ 3) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) hW A h hh _).mpr
    intro lo hi
    exact intrinsic_largeIncrement_smooth_expectation_comparison μ hp (FaceSmoother.closedBox lo hi h hh)
      ξ hξ hind hcenter hfourth hunit A hA
  have hcoeff := coefficient_budgets_le_bandwidth_rate hL hD hv hM hh hT hQ
  let f := gaussianMaximumMean A / Real.sqrt (dimensionLog p)
  have hroot : 0 < Real.sqrt (dimensionLog p) := Real.sqrt_pos.mpr
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  have hf : 0 ≤ f := div_nonneg (gaussianMaximumMean_nonneg A) hroot.le
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hf
  have hgap : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      (largeIncrementComparisonConstant * largeIncrementBudgetConstant) * f *
        largeIncrementBandwidthRate (dimensionLog p) D
          (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    apply hraw.trans
    have hc := mul_le_mul_of_nonneg_left hscaled largeIncrementComparisonConstant_nonneg
    convert hc using 1 <;> dsimp [f] <;> field_simp [hroot.ne'] <;> ring
  have hfirst : h * Real.sqrt (dimensionLog p) * dimensionLog p ≤
      largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    have hn : 0 ≤ dimensionLog p * Real.sqrt D / h + Real.sqrt (dimensionLog p) * D / h ^ 3 +
        Real.sqrt (dimensionLog p) * pairedTailVariance μ ξ h / h +
        Real.sqrt (dimensionLog p) * pairedTailExpectedMaximum μ ξ h := by positivity
    unfold largeIncrementBandwidthRate
    linarith
  have hfirst' : h * gaussianMaximumMean A * dimensionLog p ≤ f *
      largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    convert mul_le_mul_of_nonneg_left hfirst hf using 1
    dsimp [f]
    field_simp [hroot.ne']
    ring
  have hs := gaussianEndpointSmoothing_intrinsic hp μ (sumVector ξ) hW A hdiag h hh
  have hG : 0 ≤ gaussianSmoothingConstant := by linarith [gaussianSmoothingConstant_ge_two]
  have hCG : intrinsicGaussianSmoothingConstant ≤ gaussianSmoothingConstant := by
    unfold intrinsicGaussianSmoothingConstant gaussianSmoothingConstant
    linarith [Real.add_one_le_exp (3 / 2 : ℝ)]
  have hcost0 : 0 ≤ smoothingDiscrepancy μ (sumVector ξ) A h hh +
      h * gaussianMaximumMean A * dimensionLog p :=
    add_nonneg (smoothingDiscrepancy_nonneg μ (sumVector ξ) hW A h hh)
      (mul_nonneg (mul_nonneg hh.le (gaussianMaximumMean_nonneg A)) hL)
  apply (hs.trans (mul_le_mul_of_nonneg_right hCG hcost0)).trans
  have hc := mul_le_mul_of_nonneg_left (add_le_add hgap hfirst') hG
  convert hc using 1
  unfold largeIncrementMasterConstant
  dsimp [f]
  ring

theorem intrinsic_largeIncrementGaussianComparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {D φ : ℝ} (hD : 0 ≤ D)
    (hbudget : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (hφ : 0 < φ) :
    rectangleDistance μ (sumVector ξ) A ≤ largeIncrementMasterConstant *
      (gaussianMaximumMean A / Real.sqrt (dimensionLog p)) * largeIncrementMasterRate (dimensionLog p) D
        (pairedTailVariance μ ξ (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ ξ (φ * dimensionLog p)⁻¹) φ := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hh : 0 < (φ * dimensionLog p)⁻¹ := inv_pos.mpr (mul_pos hφ hL)
  have hb := intrinsic_largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hfourth
    hunit A hA hD hbudget hh
  simpa only [bandwidthRate_inv_mul_eq_master hL hφ] using hb

/-- Lemma E.1 exactly in the manuscript's original-observation normalization.
The constant is fixed before dimensions and probability models. The actual
paired increments are `(X_i' - X_i)/sqrt n`, their `v_t` and `M_t` use the
strict norm cutoff, and `deltaOne` is the exact maximum of fourth-moment
sums divided by `n^2`. No identical-law, symmetry, coordinate-independence,
rank, eigenvalue or correlation-gap assumption is introduced. -/
theorem intrinsic_gaussianComparisonWithLargeIncrementRemainders
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (_hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : ProbabilityTheory.iIndepFun X μ)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    {φ : ℝ} (hφ : 0 < φ) :
    rectangleDistance μ (normalizedObservationSum X) A ≤ largeIncrementMasterConstant *
      (gaussianMaximumMean A / Real.sqrt (dimensionLog p)) * largeIncrementMasterRate (dimensionLog p) (deltaOne μ X)
        (pairedTailVariance μ (normalizedSummands X) (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ (normalizedSummands X) (φ * dimensionLog p)⁻¹) φ := by
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hX i)) (hfourth i j)
  have hA' : A * A.transpose = covariance μ (sumVector (normalizedSummands X)) := by
    simpa only [sumVector_normalizedSummands] using hA
  have hb := intrinsic_largeIncrementGaussianComparison μ hp (normalizedSummands X)
    (normalizedSummands_measurable hX) (normalizedSummands_independent hind)
    (normalizedSummands_centered hcenter) (normalizedSummands_fourth_integrable hfourth)
    (normalizedSummands_unit_covariance hind hL2 hcenter haverage)
    A hA' (deltaOne_nonneg (μ := μ) (X := X))
    (normalizedSummands_fourth_sums_le_deltaOne (μ := μ) (X := X)) hφ
  simpa only [sumVector_normalizedSummands] using hb


universe u

/-- Lemma E.1 with its universal constant chosen before every probability
model, dimension and cutoff, in the original observation normalization. -/
theorem lemma_E1_intrinsic_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ), 1 ≤ p → 1 ≤ n →
      ∀ (X : Fin n → Ω → Vector p), (∀ i, Measurable (X i)) →
      ProbabilityTheory.iIndepFun X μ →
      (∀ i j, (∫ ω, X i ω j ∂μ) = 0) →
      (∀ i j, Integrable (fun ω => X i ω j ^ 4) μ) →
      (∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) →
      ∀ φ : ℝ, 0 < φ →
      rectangleDistance μ (normalizedObservationSum X) A ≤ C *
        (gaussianMaximumMean A / Real.sqrt (dimensionLog p)) *
        largeIncrementMasterRate (dimensionLog p) (deltaOne μ X)
          (pairedTailVariance μ (normalizedSummands X) (φ * dimensionLog p)⁻¹)
          (pairedTailExpectedMaximum μ (normalizedSummands X) (φ * dimensionLog p)⁻¹) φ := by
  refine ⟨largeIncrementMasterConstant, zero_lt_one.trans_le one_le_largeIncrementMasterConstant, ?_⟩
  intro Ω _ μ _ p n hp hn X hX hind hcenter hfourth haverage A hA φ hφ
  exact intrinsic_gaussianComparisonWithLargeIncrementRemainders μ hp hn X hX hind hcenter hfourth
    haverage A hA hφ

open RectangleCLT.Companion.SplitV4.C4Test in
theorem lemma_E3_paired_slepian {p : ℕ} (f : C4Test p)
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 ≤ h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      ((1 / 2 : ℝ) * (∫ z : Ω × Vector p, f.hessianTrace
          (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
          (slepianPoint (sumVector ξ) t z) ∂μ.prod (gaussianLaw A)) -
        (1 / (2 * Real.sqrt t)) * (∫ z : Ω × Vector p,
          f.gradient (slepianPoint (sumVector ξ) t z) (copyArrayLargeMean μ ξ z.1 h)
            ∂μ.prod (gaussianLaw A)) -
        t / 8 * (∑ i, ∫ z, f.trapezoidalRemainder
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ))) t := by
  exact f.hasDerivAt_arraySlepian_of_coordinate_fourths μ ξ hξ hind hfourth hcenter A h hh ht ht1

end
end RectangleCLTArxivV1
