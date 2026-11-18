import RectangleCLTArxivV1.TransfersCovarianceRestoration
import RectangleCLTArxivV1.GaussianMaximumCap
import RectangleCLTArxivV1.GaussianAdditionWidth

/-! The width-preserving deterministic Gaussian comparison in the second
covariance-restoration stage of Appendix E.1. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The deterministic all-retained Gaussian has positive marginal
variances once the actual removed-variance budget is small. -/
theorem conditionalAllCovariance_diagonal_lower {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (hunit : ∀ j, originalAverageCovariance μ j j = 1)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4) (j : Fin p) :
    (1 / 2 : ℝ) ≤ conditionalAllCovariance μ T j j := by
  let i : Fin n := ⟨0, by omega⟩
  have hH := conditionalOmittedCovariance_quadratic_nonneg μ (h i).threshold_pos.le (Pi.single j 1)
  have hHjj : 0 ≤ conditionalOmittedCovariance μ T j j := by
    simpa [matrixQuadratic, Pi.single_apply] using hH
  have he := congrFun (congrFun (conditional_covariance_restoration μ h hn) j) j
  simp only [Matrix.add_apply, hunit j] at he
  linarith [conditionalResidualCovariance_diagonal_le μ h hn j]

/-- The second Gaussian comparison in Appendix E.1 preserves the original
Gaussian width. The two added Gaussian laws are constructed from the
actual residual and omitted covariances inside the proof. -/
theorem conditionalAllGaussian_rectangleDistance_intrinsic {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC : C * C.transpose = conditionalAllCovariance μ T)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4) :
    rectangleDistance (gaussianLaw C) id A ≤
      20 * gaussianMaximumMean A * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) := by
  let i : Fin n := ⟨0, by omega⟩
  have hv0 := (h i).varianceBudget_nonneg
  obtain ⟨D, hD⟩ := conditionalResidualCovariance_factor_exists μ h
  obtain ⟨H, hH⟩ := conditionalOmittedCovariance_factor_exists μ (h i).threshold_pos.le
  have hcov : C * C.transpose + D * D.transpose = A * A.transpose + H * H.transpose := by
    rw [hC, hD, hA, hH]
    exact conditional_covariance_restoration μ h hn
  have hCdiag (j : Fin p) : (1 / 2 : ℝ) ≤ (C * C.transpose) j j := by
    rw [hC]
    exact conditionalAllCovariance_diagonal_lower μ h hn (by intro k; rw [← hA, hunit k]) hv j
  have hb := gaussian_two_additions_rectangleDistance_le hp C D A H hcov
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1) hCdiag (by intro j; rw [hunit j])
  norm_num only [div_one, div_div, mul_one, OfNat.ofNat_ne_zero, div_self, one_div, inv_div] at hb
  have hDwidth : gaussianMaximumMean D ≤ 2 * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) := by
    apply gaussianMaximumMean_le_of_diagonal_le hp D (by positivity)
    intro j
    rw [hD]
    exact conditionalResidualCovariance_diagonal_le μ h hn j
  have hHwidth : gaussianMaximumMean H ≤ 2 * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) := by
    apply gaussianMaximumMean_le_of_diagonal_le hp H (by positivity)
    intro j
    rw [hH]
    exact conditionalOmittedCovariance_diagonal_le μ h hn j
  have hCwidth : gaussianMaximumMean C ≤ 2 * gaussianMaximumMean A := by
    have hh := conditionalCovarianceForMask_gaussianMaximumMean_le μ h (fun _ => false) A C hA hC
    have hs : Real.sqrt (4 / 3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.sqrt_nonneg (4 / 3 : ℝ)]
    exact hh.trans (mul_le_mul_of_nonneg_right hs (gaussianMaximumMean_nonneg A))
  have hprodD := mul_le_mul hCwidth hDwidth (gaussianMaximumMean_nonneg D)
    (mul_nonneg (by norm_num) (gaussianMaximumMean_nonneg A))
  have hprodH := mul_le_mul_of_nonneg_left hHwidth (gaussianMaximumMean_nonneg A)
  apply hb.trans
  nlinarith only [hprodD, hprodH]

end RectangleCLTArxivV1
