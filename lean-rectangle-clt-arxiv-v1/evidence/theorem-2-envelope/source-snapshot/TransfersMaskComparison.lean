import RectangleCLTArxivV1.TransfersGaussianComparison
import RectangleCLTArxivV1.TransfersConditionalInput

/-! The first, mask-dependent, Gaussian covariance addition in Appendix E.1. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

theorem gaussianRectangleDistance_symm {p : ℕ} (A C : Matrix (Fin p) (Fin p) ℝ) :
    rectangleDistance (gaussianLaw A) id C = rectangleDistance (gaussianLaw C) id A := by
  unfold rectangleDistance
  congr 1
  apply congrArg Set.range
  funext R
  simp only [rectangleError, Set.preimage_id]
  exact abs_sub_comm _ _

/-- On the good covariance event, the Gaussian comparison from the
retained covariance `Q` to `Q₀` costs its actual omitted Gaussian maximum. -/
theorem conditionalMaskGaussian_rectangleDistance_intrinsic {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (mask : Fin n → Bool)
    (A C C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC : C * C.transpose = conditionalCovarianceForMask μ T mask)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - A * A.transpose) ≤ 1 / 2) :
    rectangleDistance (gaussianLaw C) id C₀ ≤
      16 * gaussianMaximumMean A * Real.sqrt
        (matrixMaxEntryNorm (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) *
          dimensionLog p) := by
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨J, hJ⟩ := conditionalMaskDifference_factor_exists μ (h i).threshold_pos.le mask
  have hcov : C₀ * C₀.transpose = C * C.transpose + J * J.transpose := by
    rw [hC₀, hC, hJ]
    abel
  have hCdiag (j : Fin p) : (1 / 2 : ℝ) ≤ (C * C.transpose) j j := by
    have he := ((norm_le_pi_norm
      (fun k => (conditionalCovarianceForMask μ T mask - A * A.transpose) j k) j).trans
      (norm_le_pi_norm (fun j k => (conditionalCovarianceForMask μ T mask - A * A.transpose) j k) j)).trans hgood
    simp only [Matrix.sub_apply, Real.norm_eq_abs, hunit j] at he
    rw [hC]
    linarith [(abs_le.mp he).1]
  have hb := gaussian_addition_factor_rectangleDistance_le hp C J C₀ hcov
    (by norm_num : (0 : ℝ) < 1 / 2) hCdiag
  norm_num at hb
  rw [← gaussianRectangleDistance_symm C C₀] at hb
  have hCwidth : gaussianMaximumMean C ≤ 2 * gaussianMaximumMean A := by
    have hh := conditionalCovarianceForMask_gaussianMaximumMean_le μ h mask A C hA hC
    have hs : Real.sqrt (4 / 3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.sqrt_nonneg (4 / 3 : ℝ)]
    exact hh.trans (mul_le_mul_of_nonneg_right hs (gaussianMaximumMean_nonneg A))
  have hJwidth : gaussianMaximumMean J ≤ 2 * Real.sqrt
      (matrixMaxEntryNorm (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) *
        dimensionLog p) := by
    apply gaussianMaximumMean_le_of_diagonal_le hp J (norm_nonneg _)
    intro j
    rw [hJ]
    have he := (norm_le_pi_norm
      (fun k => (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) j k) j).trans
      (norm_le_pi_norm (fun j k =>
        (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) j k) j)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using he)
  have hpD := mul_le_mul hCwidth hJwidth (gaussianMaximumMean_nonneg J)
    (mul_nonneg (by norm_num) (gaussianMaximumMean_nonneg A))
  apply hb.trans
  nlinarith only [hpD]

/-- The first addition cost can be expressed using the already-integrable
actual covariance deviation, without a measurable Gaussian factor choice. -/
theorem conditionalMaskGaussian_rectangleDistance_le_deviation {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (mask : Fin n → Bool)
    (A C C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC : C * C.transpose = conditionalCovarianceForMask μ T mask)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - A * A.transpose) ≤ 1 / 2) :
    rectangleDistance (gaussianLaw C) id C₀ ≤ 16 * gaussianMaximumMean A * Real.sqrt
      ((4 * truncationVarianceBudget B T q +
        matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - A * A.transpose)) * dimensionLog p) := by
  have hzero : matrixMaxEntryNorm (conditionalAllCovariance μ T - A * A.transpose) ≤
      4 * truncationVarianceBudget B T q := by
    have hh := conditional_covariance_max_deviation_le μ h hn (fun _ => false)
    simpa only [conditionalAllCovariance, hA, exceptionalCount, Bool.false_eq_true, if_false,
      Finset.sum_const_zero, mul_zero, add_zero] using hh
  have heq : conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask =
      (conditionalAllCovariance μ T - A * A.transpose) -
        (conditionalCovarianceForMask μ T mask - A * A.transpose) := by abel
  have hdiff : matrixMaxEntryNorm (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) ≤
      4 * truncationVarianceBudget B T q +
        matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - A * A.transpose) := by
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add_right hzero _)
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  exact (conditionalMaskGaussian_rectangleDistance_intrinsic μ h hp hn mask A C C₀ hA hunit hC hC₀ hgood).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hdiff hL))
      (mul_nonneg (by norm_num) (gaussianMaximumMean_nonneg A)))

end RectangleCLTArxivV1
