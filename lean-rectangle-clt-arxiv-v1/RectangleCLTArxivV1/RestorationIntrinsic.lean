import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SplitV4.SeededRestorationBounds

/-!
# Intrinsic coefficient in seeded restoration

These intermediate analytic estimates state their actual layer-concentration
input explicitly. The final bounded-array comparison must supply this input
from Lemma C.1; no comparison of probability laws is assumed here. Both the
same-copy and independent-copy fourth matrices are retained by the audited
conditional fourth-budget lemmas.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def intrinsicRestorationConstant (C₀ : ℝ) : ℝ :=
  restorationPairedConstant logisticMatrixConstant C₀

theorem intrinsicRestorationConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < intrinsicRestorationConstant C₀ :=
  restorationPairedConstant_pos logisticMatrixConstant_ge_one hC₀

/-- B.4 at the actual seeded base and its independent copies. -/
theorem intrinsic_seeded_matrix_estimate_with_copies
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t C₀ κ : ℝ}
    (_hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) (hδh : δ ≤ s.bandwidth)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t)
    (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration (seededSplitBaseDistribution μ ξ A x ε t) C₀ δ κ) :
    AveragedSelectorMatrixEstimate s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
      (seededSplitGaussianScale ε t • A) (fun z => seededSplitBaseValue A x ε t z.1)
      logisticMatrixConstant (C₀ * (s.bandwidth * dimensionLog p * κ)) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  exact averagedSelectorMatrixEstimate_intrinsic hp
    ((splitBaseLaw μ ξ t).prod (μ.prod μ)) (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp measurable_fst) s A
    (factor_coordinate_normSq_eq_one A hA hunit) hC₀ hκ h.delta_nonneg hδh
    (Real.sqrt_nonneg _) hscale (by rw [map_seededSplitBaseValue_fst]; exact hc)

theorem intrinsic_seeded_relative_cubic_product_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε)
    (ht : t ∈ Icc (0 : ℝ) 1) (hδh : δ ≤ s.bandwidth)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration (seededSplitBaseDistribution μ ξ A x ε t) C₀ δ κ) :
    |restorationThirdExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
      (seededCopyOriginal ξ) (fun _ _ => 0) (seededSplitGaussianScale ε t)| ≤
        intrinsicRestorationConstant C₀ / (seededSplitGaussianScale ε t) ^ 2 * M₃ *
          dimensionLog p * κ := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  have hroot : 0 < Real.sqrt (dimensionLog p) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  let C' := C₀ * κ / Real.sqrt (dimensionLog p)
  have hC' : 0 ≤ C' := (div_pos (mul_pos hC₀ hκ) hroot).le
  have hmatrix : AveragedSelectorMatrixEstimate s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
      (seededSplitGaussianScale ε t • A) (fun z => seededSplitBaseValue A x ε t z.1)
      logisticMatrixConstant (C' * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
    convert intrinsic_seeded_matrix_estimate_with_copies μ ξ h hp hunit A hA s x hε ht
      hδh hscale hC₀ hκ hc using 1
    dsimp only [C']
    field_simp [hroot.ne']
    ring
  have hn := restoration_third_relative_product hp s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
    originalSigma originalSigma_le A (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp (comap_measurable Prod.fst))
    hmatrix
    (seededCopyWhitened A ξ) (seededCopyWhitened_measurable μ ξ h A)
    (seededCopyWhitened_integrable_coordinate_pair (splitBaseLaw μ ξ t) μ ξ h A)
    (seededCopyOriginal ξ) (seededCopyOriginal_measurable ξ h.measurable)
    h.delta_nonneg hrel.s₃_nonneg (seededCopyOriginal_bounded (splitBaseLaw μ ξ t) μ ξ h)
    (seeded_copy_conditional_third_budget (splitBaseLaw μ ξ t) μ ξ h hrel A hA)
    logisticMatrixConstant_ge_one hC' hscale

  convert hn using 1
  by_cases hσ : seededSplitGaussianScale ε t = 0
  · simp [hσ]
  · unfold intrinsicRestorationConstant restorationPairedConstant
    dsimp only [C']
    field_simp [hroot.ne', hσ, s.bandwidth_pos.ne']
    ring


theorem intrinsic_seeded_relative_fourth_product_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t r : ℝ} (hε : 0 ≤ ε)
    (ht : t ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t)
    (hband : restorationPairedBandwidth logisticMatrixConstant 4 * δ ≤ s.bandwidth)
    (freshY freshW freshShift : Bool)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration (seededSplitBaseDistribution μ ξ A x ε t) C₀ δ κ) :
    |restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
      (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
      (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale ε t)| ≤
        intrinsicRestorationConstant C₀ / (seededSplitGaussianScale ε t) ^ 2 * M₄ / s.bandwidth *
          dimensionLog p * κ := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  have hδh : δ ≤ s.bandwidth :=
    (le_mul_of_one_le_left h.delta_nonneg (le_max_left _ _)).trans hband
  have hroot : 0 < Real.sqrt (dimensionLog p) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  let C' := C₀ * κ / Real.sqrt (dimensionLog p)
  have hC' : 0 ≤ C' := (div_pos (mul_pos hC₀ hκ) hroot).le
  have hmatrix : AveragedSelectorMatrixEstimate s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
      (seededSplitGaussianScale ε t • A) (fun z => seededSplitBaseValue A x ε t z.1)
      logisticMatrixConstant (C' * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
    convert intrinsic_seeded_matrix_estimate_with_copies μ ξ h hp hunit A hA s x hε ht
      hδh hscale hC₀ hκ hc using 1
    dsimp only [C']
    field_simp [hroot.ne']
    ring
  have hv (i : Fin n) : Measurable (seededCopyShift ξ freshShift t r i) := by
    unfold seededCopyShift
    exact (measurable_const.smul (seededCopyDirection_measurable ξ h.measurable freshShift i)).sub
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
  have hn := restoration_fourth_relative_product hp s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
    originalSigma originalSigma_le A (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp (comap_measurable Prod.fst))
    hmatrix
    (seededCopyWhitened A ξ) (seededCopyWhitened_measurable μ ξ h A)
    (seededCopyWhitened_integrable_coordinate_pair (splitBaseLaw μ ξ t) μ ξ h A)
    (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW) (seededCopyShift ξ freshShift t r)
    (seededCopyDirection_measurable ξ h.measurable freshY)
    (seededCopyDirection_measurable ξ h.measurable freshW) hv
    h.delta_nonneg (by norm_num : (0 : ℝ) ≤ 4) hrel.s₄_nonneg
    (seededCopyDirection_bounded (splitBaseLaw μ ξ t) μ ξ h freshY)
    (seededCopyDirection_bounded (splitBaseLaw μ ξ t) μ ξ h freshW)
    (seededCopyShift_bounded μ ξ h freshShift ht hr)
    (seededCopyDirection_conditional_fourth_budget (splitBaseLaw μ ξ t) μ ξ h hrel A hA freshY)
    (seededCopyDirection_conditional_fourth_budget (splitBaseLaw μ ξ t) μ ξ h hrel A hA freshW)
    logisticMatrixConstant_ge_one hC' hscale hband
  convert hn using 1
  by_cases hσ : seededSplitGaussianScale ε t = 0
  · simp [hσ]
  · unfold intrinsicRestorationConstant restorationPairedConstant
    dsimp only [C']
    field_simp [hroot.ne', hσ, s.bandwidth_pos.ne']
    ring


end
end RectangleCLTArxivV1
