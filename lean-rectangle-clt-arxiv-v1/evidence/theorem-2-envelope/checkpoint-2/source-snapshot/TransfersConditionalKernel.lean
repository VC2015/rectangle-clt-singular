import RectangleCLTArxivV1.TransfersMaskComparison

/-! The genuine conditional-kernel comparison for the envelope-only route,
with the actual original Gaussian width in every boundary term. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable def conditionalIntrinsicBoundedCost (n p : ℕ) (T g : ℝ) : ℝ :=
  intrinsicUniversalConstant * (8 * Real.sqrt (4 / 3 : ℝ)) *
    (g * (T / Real.sqrt (n : ℝ)) * dimensionLog p * Real.sqrt (dimensionLog n))

noncomputable def conditionalIntrinsicKernelCost (n p : ℕ) (T g v d r : ℝ) : ℝ :=
  conditionalIntrinsicBoundedCost n p T g + 8 * g * r +
    16 * g * Real.sqrt ((4 * v + d) * dimensionLog p) +
    20 * g * Real.sqrt (2 * v * dimensionLog p)

/-- On the good covariance event, the actual conditional probability is
compared with the reference Gaussian using the new bounded theorem and
both constructed Gaussian covariance additions. -/
theorem conditionalGoodKernel_rectangle_error_intrinsic {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B) (tag : TruncationTag p n)
    (A C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) ≤ 1 / 2)
    (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤
      conditionalIntrinsicBoundedCost n p T (gaussianMaximumMean A) +
        8 * gaussianMaximumMean A * ‖conditionalNormalizedShift μ T tag‖ +
        16 * gaussianMaximumMean A * Real.sqrt
          ((4 * truncationVarianceBudget B T q +
            matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose)) * dimensionLog p) +
        20 * gaussianMaximumMean A * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) := by
  let i : Fin n := ⟨0, by omega⟩
  have hT : 0 ≤ T := (h i).threshold_pos.le
  obtain ⟨C, hC⟩ := conditionalRetained_gaussian_factor_exists μ hT tag.1
  let r := conditionalNormalizedShift μ T tag
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hbounded : |(conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier) -
      (gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier)| ≤
      conditionalIntrinsicBoundedCost n p T (gaussianMaximumMean A) := by
    rw [conditionalKernel_rectangle_error_eq]
    have hh := (rectangleError_le_rectangleDistance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T tag.1)) C (R.pullbackAdd r)).trans
      (conditionalRetained_intrinsicRectangleDistanceCLT μ h hp hn hB tag.1 A C hA hunit hgood hC)
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) intrinsicUniversalConstant_pos.le).trans_eq
    unfold conditionalIntrinsicBoundedCost
    ring
  have hCdiag (j : Fin p) : (1 / 2 : ℝ) ≤ (C * C.transpose) j j := by
    have he := ((norm_le_pi_norm
      (fun k => (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) j k) j).trans
      (norm_le_pi_norm (fun j k => (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) j k) j)).trans hgood
    simp only [Matrix.sub_apply, Real.norm_eq_abs, hunit j] at he
    rw [hC]
    linarith [(abs_le.mp he).1]
  have hCwidth : gaussianMaximumMean C ≤ 2 * gaussianMaximumMean A := by
    have hh := conditionalCovarianceForMask_gaussianMaximumMean_le μ h tag.1 A C hA hC
    have hs : Real.sqrt (4 / 3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.sqrt_nonneg (4 / 3 : ℝ)]
    exact hh.trans (mul_le_mul_of_nonneg_right hs (gaussianMaximumMean_nonneg A))
  have hshift : |(gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier) -
      (gaussianLaw C).real R.carrier| ≤ 8 * gaussianMaximumMean A * ‖r‖ := by
    have hh := gaussian_rectangle_shift_min_variance hp C
      (by norm_num : (0 : ℝ) < 1 / 2) hCdiag r R
    norm_num at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_right hCwidth (norm_nonneg r)
    nlinarith only [hmul]
  have hmask := conditionalMaskGaussian_rectangleDistance_le_deviation μ h hp hn tag.1 A C C₀ hA hunit hC hC₀ hgood
  have hdet := conditionalAllGaussian_rectangleDistance_intrinsic μ h hp hn A C₀ hA hunit hC₀ hv
  have hgauss := (rectangleError_le_rectangleDistance (gaussianLaw C) id A R).trans
    ((rectangleDistance_gaussian_triangle (gaussianLaw C) id C₀ A).trans (add_le_add hmask hdet))
  unfold rectangleError at hgauss ⊢
  simp only [Set.preimage_id] at hgauss
  have ht₁ := abs_sub_le ((conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier))
    ((gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier)) ((gaussianLaw A).real R.carrier)
  have ht₂ := abs_sub_le ((gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw C).real R.carrier) ((gaussianLaw A).real R.carrier)
  change |(conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier) - (gaussianLaw A).real R.carrier| ≤ _
  dsimp only [r] at hshift
  linarith only [ht₁, ht₂, hbounded, hshift, hgauss]

/-- Bad covariance tags are paid for by twice the actual covariance
deviation. This makes the genuine kernel comparison integrable uniformly
over every exceptional tag. -/
theorem conditionalKernel_rectangle_error_intrinsic {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B) (tag : TruncationTag p n)
    (A C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤
      conditionalIntrinsicKernelCost n p T (gaussianMaximumMean A) (truncationVarianceBudget B T q)
        (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose))
        ‖conditionalNormalizedShift μ T tag‖ +
      2 * matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) := by
  by_cases hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) ≤ 1 / 2
  · exact (conditionalGoodKernel_rectangle_error_intrinsic μ h hp hn hB tag A C₀ hA hunit hC₀ hv hgood R).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (norm_nonneg _)))
  · have hbad : (1 : ℝ) ≤ 2 * matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) := by linarith
    have hcost : 0 ≤ conditionalIntrinsicKernelCost n p T (gaussianMaximumMean A)
        (truncationVarianceBudget B T q)
        (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose))
        ‖conditionalNormalizedShift μ T tag‖ := by
      let i : Fin n := ⟨0, by omega⟩
      have hT := (h i).threshold_pos.le
      have hg := gaussianMaximumMean_nonneg A
      have hconst := intrinsicUniversalConstant_pos.le
      have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
      unfold conditionalIntrinsicKernelCost conditionalIntrinsicBoundedCost
      positivity
    exact (rectangleError_le_one _ _ _ R).trans
      (hbad.trans (le_add_of_nonneg_left hcost))

/-- Kernel cost retaining the printed omitted diagonal maximum. -/
noncomputable def conditionalIntrinsicKernelDiagonalCost (n p : ℕ) (T g v a r : ℝ) : ℝ :=
  conditionalIntrinsicBoundedCost n p T g + 8 * g * r +
    16 * g * Real.sqrt (a * dimensionLog p) + 20 * g * Real.sqrt (2 * v * dimensionLog p)

theorem conditionalGoodKernel_rectangle_error_intrinsic_diagonal {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B) (tag : TruncationTag p n)
    (A C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) ≤ 1 / 2)
    (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤
      conditionalIntrinsicBoundedCost n p T (gaussianMaximumMean A) +
        8 * gaussianMaximumMean A * ‖conditionalNormalizedShift μ T tag‖ +
        16 * gaussianMaximumMean A * Real.sqrt
          (matrixMaxDiagonal (conditionalAllCovariance μ T -
            conditionalCovarianceForMask μ T tag.1) * dimensionLog p) +
        20 * gaussianMaximumMean A * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) := by
  let i : Fin n := ⟨0, by omega⟩
  have hT : 0 ≤ T := (h i).threshold_pos.le
  obtain ⟨C, hC⟩ := conditionalRetained_gaussian_factor_exists μ hT tag.1
  let r := conditionalNormalizedShift μ T tag
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hbounded : |(conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier) -
      (gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier)| ≤
      conditionalIntrinsicBoundedCost n p T (gaussianMaximumMean A) := by
    rw [conditionalKernel_rectangle_error_eq]
    have hh := (rectangleError_le_rectangleDistance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T tag.1)) C (R.pullbackAdd r)).trans
      (conditionalRetained_intrinsicRectangleDistanceCLT μ h hp hn hB tag.1 A C hA hunit hgood hC)
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) intrinsicUniversalConstant_pos.le).trans_eq
    unfold conditionalIntrinsicBoundedCost
    ring
  have hCdiag (j : Fin p) : (1 / 2 : ℝ) ≤ (C * C.transpose) j j := by
    have he := ((norm_le_pi_norm
      (fun k => (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) j k) j).trans
      (norm_le_pi_norm (fun j k => (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) j k) j)).trans hgood
    simp only [Matrix.sub_apply, Real.norm_eq_abs, hunit j] at he
    rw [hC]
    linarith [(abs_le.mp he).1]
  have hCwidth : gaussianMaximumMean C ≤ 2 * gaussianMaximumMean A := by
    have hh := conditionalCovarianceForMask_gaussianMaximumMean_le μ h tag.1 A C hA hC
    have hs : Real.sqrt (4 / 3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.sqrt_nonneg (4 / 3 : ℝ)]
    exact hh.trans (mul_le_mul_of_nonneg_right hs (gaussianMaximumMean_nonneg A))
  have hshift : |(gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier) -
      (gaussianLaw C).real R.carrier| ≤ 8 * gaussianMaximumMean A * ‖r‖ := by
    have hh := gaussian_rectangle_shift_min_variance hp C
      (by norm_num : (0 : ℝ) < 1 / 2) hCdiag r R
    norm_num at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_right hCwidth (norm_nonneg r)
    nlinarith only [hmul]
  have hmask := conditionalMaskGaussian_rectangleDistance_diagonal μ h hp hn tag.1 A C C₀ hA hunit hC hC₀ hgood
  have hdet := conditionalAllGaussian_rectangleDistance_intrinsic μ h hp hn A C₀ hA hunit hC₀ hv
  have hgauss := (rectangleError_le_rectangleDistance (gaussianLaw C) id A R).trans
    ((rectangleDistance_gaussian_triangle (gaussianLaw C) id C₀ A).trans (add_le_add hmask hdet))
  unfold rectangleError at hgauss ⊢
  simp only [Set.preimage_id] at hgauss
  have ht₁ := abs_sub_le ((conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier))
    ((gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier)) ((gaussianLaw A).real R.carrier)
  have ht₂ := abs_sub_le ((gaussianLaw C).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw C).real R.carrier) ((gaussianLaw A).real R.carrier)
  change |(conditionalTruncationKernel μ T tag).real (W ⁻¹' R.carrier) - (gaussianLaw A).real R.carrier| ≤ _
  dsimp only [r] at hshift
  linarith only [ht₁, ht₂, hbounded, hshift, hgauss]


theorem conditionalKernel_rectangle_error_intrinsic_diagonal {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B) (tag : TruncationTag p n)
    (A C₀ : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hC₀ : C₀ * C₀.transpose = conditionalAllCovariance μ T)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤
      conditionalIntrinsicKernelDiagonalCost n p T (gaussianMaximumMean A) (truncationVarianceBudget B T q)
        (matrixMaxDiagonal (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T tag.1))
        ‖conditionalNormalizedShift μ T tag‖ +
      2 * matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) := by
  by_cases hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) ≤ 1 / 2
  · exact (conditionalGoodKernel_rectangle_error_intrinsic_diagonal μ h hp hn hB tag A C₀ hA hunit hC₀ hv hgood R).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (norm_nonneg _)))
  · have hbad : (1 : ℝ) ≤ 2 * matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T tag.1 - A * A.transpose) := by linarith
    have hcost : 0 ≤ conditionalIntrinsicKernelDiagonalCost n p T (gaussianMaximumMean A)
        (truncationVarianceBudget B T q)
        (matrixMaxDiagonal (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T tag.1))
        ‖conditionalNormalizedShift μ T tag‖ := by
      let i : Fin n := ⟨0, by omega⟩
      have hT := (h i).threshold_pos.le
      have hg := gaussianMaximumMean_nonneg A
      have hconst := intrinsicUniversalConstant_pos.le
      have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
      unfold conditionalIntrinsicKernelDiagonalCost conditionalIntrinsicBoundedCost
      positivity
    exact (rectangleError_le_one _ _ _ R).trans
      (hbad.trans (le_add_of_nonneg_left hcost))


end RectangleCLTArxivV1
