import RectangleCLTCompanion.SplitV4.Printed.Bernstein
import RectangleCLTCompanion.SplitV4.LargeIncrementComparison

/-!
# The printed G.1 coefficient route

The exact scalar Bernstein expansion is applied to the genuine centered
rank-one entries. Conditional Jensen, the actual paired-copy fourth budget,
and the discarded-variance bias then give the paper's matrix estimate.
The G.1 comparison is reassembled with that route; the original result proof
and its certificate are unchanged. The interpolation, trapezoidal identity,
common-point derivative contraction and endpoint integration are reused only
where their existing proofs follow the printed mathematical argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
set_option autoImplicit false
section MatrixRoute
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {h D : ℝ}

theorem expected_centeredRankOneSum_norm_le
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ D) :
    (∫ ω, matrixMaxEntryNorm (centeredRankOneSum μ Y ω) ∂μ) ≤
      matrixFluctuationConstant *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hp2 : 1 ≤ p * p := by simpa using Nat.mul_le_mul hp hp
  have hZ := centeredRankOneEntries_boundedHypotheses hY hind hbound hh.le
  have hbNew := bounded_vector_bernstein_maximum_by_tail_integration hZ hp2 (by positivity : 0 < 2 * h ^ 2) hD
    (centeredRankOneEntries_variance_budget hY hbound hh.le hfourth)
  have hLp2 : 0 ≤ dimensionLog (p * p) := zero_le_one.trans (log_exp_mul_nat_ge_one hp2)
  have hb : (∫ ω, ‖sumVector (centeredRankOneEntries μ Y) ω‖ ∂μ) ≤
      (1 + Real.exp 1) * (Real.sqrt (D * dimensionLog (p * p)) +
        (2 * h ^ 2) * dimensionLog (p * p)) := by
    have he : (3 : ℝ) ≤ 1 + Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact hbNew.trans (mul_le_mul_of_nonneg_right he
      (by positivity : 0 ≤ Real.sqrt (D * dimensionLog (p * p)) +
        (2 * h ^ 2) * dimensionLog (p * p)))
  have hnorm (ω : Ω) : ‖sumVector (centeredRankOneEntries μ Y) ω‖ =
      matrixMaxEntryNorm (centeredRankOneSum μ Y ω) := by
    rw [sum_centeredRankOneEntries_eq, norm_matrixEntriesVector]
  simp_rw [hnorm] at hb
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hL2 := dimensionLog_square_le hp
  have hsqrt : Real.sqrt (D * dimensionLog (p * p)) ≤ 2 * Real.sqrt (D * dimensionLog p) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hL2 hD
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hD hL)]
    nlinarith [mul_nonneg hD hL]
  have hm := mul_le_mul_of_nonneg_left hL2 (sq_nonneg h)
  have hC : 0 ≤ 1 + Real.exp 1 := by positivity
  unfold matrixFluctuationConstant
  apply hb.trans
  have hs := mul_le_mul_of_nonneg_left hsqrt hC
  have hl := mul_le_mul_of_nonneg_left hm hC
  have hpos := mul_nonneg hC (Real.sqrt_nonneg (D * dimensionLog p))
  nlinarith

theorem expected_copyAverage_centeredRankOneSum_norm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Fin n → α × β → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y (μ.prod ν))
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ z ∂μ.prod ν, ‖Y i z‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ z, Y i z j ^ 4 ∂μ.prod ν) ≤ D) :
    (∫ x, ‖copyAverage ν (centeredRankOnePiSum (μ.prod ν) Y) x‖ ∂μ) ≤
      matrixFluctuationConstant *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hi := integrable_centeredRankOnePiSum hY hind hbound hh.le
  have hj := integral_norm_copyAverage_le μ ν (centeredRankOnePiSum (μ.prod ν) Y) hi
  exact hj.trans (expected_centeredRankOneSum_norm_le hY hind hp hh hD hbound hfourth)

theorem expected_half_copyAverage_centeredRankOneSum_norm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Fin n → α × β → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y (μ.prod ν))
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ z ∂μ.prod ν, ‖Y i z‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ z, Y i z j ^ 4 ∂μ.prod ν) ≤ D) :
    (∫ x, ‖(1 / 2 : ℝ) • copyAverage ν (centeredRankOnePiSum (μ.prod ν) Y) x‖ ∂μ) ≤
      (matrixFluctuationConstant / 2) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hb := expected_copyAverage_centeredRankOneSum_norm_le μ ν hY hind hp hh hD hbound hfourth
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [integral_const_mul]
  nlinarith

theorem expected_copyArrayTruncatedCovariance_fluctuation_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) :
    (∫ x, ‖fun j k => copyArrayTruncatedCovariance μ ξ x h j k -
      ∫ w, copyArrayTruncatedCovariance μ ξ w h j k ∂μ‖ ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hY (i : Fin n) : Measurable (pairedTruncatedArray ξ h i) :=
    C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h
  have hbound (i : Fin n) : ∀ᵐ z ∂μ.prod μ, ‖pairedTruncatedArray ξ h i z‖ ≤ h :=
    ae_of_all _ (fun z => C4Test.norm_pairedTruncatedIncrement_le _ _ hh.le)
  have hb := expected_half_copyAverage_centeredRankOneSum_norm_le μ μ hY
    (iIndepFun_pairedTruncatedArray μ ξ hξ hind h) hp hh (by positivity : 0 ≤ 16 * D)
    hbound (pairedTruncatedArray_fourth_budget ξ hξ hh.le hi4 hfourth)
  have he := half_copyAverage_centeredRankOnePiSum_paired_ae_eq ξ hξ hind hh.le
  have henorm := he.fun_comp (fun M : Fin p → Fin p → ℝ => ‖M‖)
  simp only [Function.comp_def] at henorm
  rw [integral_congr_ae henorm] at hb
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hsqrt : Real.sqrt ((16 * D) * dimensionLog p) = 4 * Real.sqrt (D * dimensionLog p) := by
    have hs16 : Real.sqrt (16 : ℝ) = 4 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    rw [show (16 * D) * dimensionLog p = 16 * (D * dimensionLog p) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), hs16]
  rw [hsqrt] at hb
  have hC : 0 ≤ matrixFluctuationConstant := by unfold matrixFluctuationConstant; positivity
  have hn := mul_nonneg hC (mul_nonneg (sq_nonneg h) hL)
  nlinarith

theorem expected_copyArrayTruncatedCovariance_sub_covariance_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D)
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) :
    (∫ x, matrixMaxEntryNorm
      (copyArrayTruncatedCovariance μ ξ x h - covariance μ (sumVector ξ)) ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) +
          pairedTailVariance μ ξ h / 2 := by
  have hfl := expected_copyArrayTruncatedCovariance_fluctuation_le
    ξ hξ hind hp hh hD hi4 hfourth
  have hb := meanTruncatedCovariance_bias_norm_le μ ξ hξ hind hL2 hcenter hh.le
  have hi := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    ξ hξ hind hh.le (covariance μ (sumVector ξ))
  have hif := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    ξ hξ hind hh.le (meanTruncatedCovariance μ ξ h)
  have hle := integral_mono hi (hif.add (integrable_const
      (matrixMaxEntryNorm (meanTruncatedCovariance μ ξ h - covariance μ (sumVector ξ)))))
    (fun x => matrixMaxEntryNorm_sub_le (copyArrayTruncatedCovariance μ ξ x h)
      (meanTruncatedCovariance μ ξ h) (covariance μ (sumVector ξ)))
  simp only [Pi.add_apply] at hle
  rw [integral_add hif (integrable_const _), integral_const] at hle
  simp only [measureReal_univ_eq_one, one_smul] at hle
  have hfl' : (∫ x, matrixMaxEntryNorm
      (copyArrayTruncatedCovariance μ ξ x h - meanTruncatedCovariance μ ξ h) ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
    simpa only [matrixMaxEntryNorm, Matrix.sub_apply, meanTruncatedCovariance] using hfl
  exact hle.trans (add_le_add hfl' hb)

end MatrixRoute

private theorem log_two_mul_nat_le_dimensionLog {p : ℕ} (hp : 1 ≤ p) :
    Real.log (2 * (p : ℝ)) ≤ dimensionLog p := by
  apply Real.log_le_log
  · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
    positivity
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)

theorem largeIncrementGaussianComparison_bandwidth
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
      largeIncrementBandwidthRate (dimensionLog p) D
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
    have hlog := mul_le_mul_of_nonneg_left (log_two_mul_nat_le_dimensionLog hp) (pow_nonneg hh.le 4)
    nlinarith
  have hv := pairedTailVariance_nonneg μ ξ h
  have hM : 0 ≤ pairedTailExpectedMaximum μ ξ h := integral_nonneg (fun z => norm_nonneg _)
  have hraw : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      largeIncrementComparisonConstant * Real.sqrt (dimensionLog p) *
        (largeIncrementMatrixCost μ ξ A h / h + pairedTailExpectedMaximum μ ξ h +
          largeIncrementFourthCost μ ξ h / h ^ 3) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) hW A h hh _).mpr
    intro lo hi
    exact largeIncrement_smooth_expectation_comparison μ hp (FaceSmoother.closedBox lo hi h hh)
      ξ hξ hind hcenter hfourth hunit A hA
  have hcoeff := coefficient_budgets_le_bandwidth_rate hL hD hv hM hh hT hQ
  have hgap : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      (largeIncrementComparisonConstant * largeIncrementBudgetConstant) *
        largeIncrementBandwidthRate (dimensionLog p) D
          (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    apply hraw.trans
    have hc := mul_le_mul_of_nonneg_left hcoeff largeIncrementComparisonConstant_nonneg
    convert hc using 1 <;> ring
  have hfirst : h * Real.sqrt (dimensionLog p) * dimensionLog p ≤
      largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    have hn : 0 ≤ dimensionLog p * Real.sqrt D / h + Real.sqrt (dimensionLog p) * D / h ^ 3 +
        Real.sqrt (dimensionLog p) * pairedTailVariance μ ξ h / h +
        Real.sqrt (dimensionLog p) * pairedTailExpectedMaximum μ ξ h := by positivity
    unfold largeIncrementBandwidthRate
    linarith
  have hs := gaussianEndpointSmoothing hp μ (sumVector ξ) hW A hdiag h hh
  have hG : 0 ≤ gaussianSmoothingConstant := by linarith [gaussianSmoothingConstant_ge_two]
  apply hs.trans
  have hc := mul_le_mul_of_nonneg_left (add_le_add hgap hfirst) hG
  convert hc using 1 <;> unfold largeIncrementMasterConstant <;> ring

theorem largeIncrementGaussianComparison
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
      largeIncrementMasterRate (dimensionLog p) D
        (pairedTailVariance μ ξ (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ ξ (φ * dimensionLog p)⁻¹) φ := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hh : 0 < (φ * dimensionLog p)⁻¹ := inv_pos.mpr (mul_pos hφ hL)
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hfourth
    hunit A hA hD hbudget hh
  simpa only [bandwidthRate_inv_mul_eq_master hL hφ] using hb

theorem gaussianComparisonWithLargeIncrementRemainders
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
      largeIncrementMasterRate (dimensionLog p) (deltaOne μ X)
        (pairedTailVariance μ (normalizedSummands X) (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ (normalizedSummands X) (φ * dimensionLog p)⁻¹) φ := by
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hX i)) (hfourth i j)
  have hA' : A * A.transpose = covariance μ (sumVector (normalizedSummands X)) := by
    simpa only [sumVector_normalizedSummands] using hA
  have hb := largeIncrementGaussianComparison μ hp (normalizedSummands X)
    (normalizedSummands_measurable hX) (normalizedSummands_independent hind)
    (normalizedSummands_centered hcenter) (normalizedSummands_fourth_integrable hfourth)
    (normalizedSummands_unit_covariance hind hL2 hcenter haverage)
    A hA' (deltaOne_nonneg (μ := μ) (X := X))
    (normalizedSummands_fourth_sums_le_deltaOne (μ := μ) (X := X)) hφ
  simpa only [sumVector_normalizedSummands] using hb

end
end RectangleCLT.Companion.SplitV4.Printed
