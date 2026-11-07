import RectangleCLTCompanion.SplitV4.SeededGaussianSplit
import RectangleCLTCompanion.SplitV4.SeededRelativeCopyBudgets
import RectangleCLTCompanion.SplitV4.RestorationProductBounds

/-! Actual relative B.2 estimates on the seeded full-mixture base and its
two independent row copies. Signed cubic and both fourth budgets remain
distinct until they discharge the corresponding coefficient estimates. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededRestorationConstant : ℝ :=
  restorationPairedConstant logisticMatrixConstant seededBaseConcentrationConstant

def seededRestorationBandwidth : ℝ := max 2 (restorationPairedBandwidth logisticMatrixConstant 4)

theorem seededRestorationConstant_pos : 0 < seededRestorationConstant :=
  restorationPairedConstant_pos logisticMatrixConstant_ge_one seededBaseConcentrationConstant_pos

theorem seededRestorationBandwidth_ge_two : 2 ≤ seededRestorationBandwidth := le_max_left _ _

def seededCopyDirection {Β Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (fresh : Bool) : Fin n → Β × (Ω × Ω) → Vector p :=
  if fresh then seededCopyFresh ξ else seededCopyOriginal ξ

def seededCopyShift {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (fresh : Bool) (t r : ℝ)
    (i : Fin n) (z : ((Fin n → Vector p) × Vector p) × (Ω × Ω)) : Vector p :=
  (r * (1 + t)) • seededCopyDirection ξ fresh i z - z.1.1 i

theorem seededCopyDirection_measurable
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (fresh : Bool) (i : Fin n) :
    Measurable (seededCopyDirection (Β := Β) ξ fresh i) := by
  cases fresh
  · exact seededCopyOriginal_measurable ξ hξ i
  · exact seededCopyFresh_measurable ξ hξ i

theorem seededCopyDirection_bounded
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (fresh : Bool) (i : Fin n) :
    ∀ᵐ z ∂ρ.prod (μ.prod μ), ‖seededCopyDirection ξ fresh i z‖ ≤ δ := by
  cases fresh
  · exact seededCopyOriginal_bounded ρ μ ξ h i
  · exact seededCopyFresh_bounded ρ μ ξ h i

theorem seededCopyShift_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (fresh : Bool)
    {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    ∀ᵐ z ∂(splitBaseLaw μ ξ t).prod (μ.prod μ), ‖seededCopyShift ξ fresh t r i z‖ ≤ 4 * δ := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hrow : ∀ᵐ z ∂(splitBaseLaw μ ξ t).prod (μ.prod μ), ‖z.1.1 i‖ ≤ 2 * δ :=
    (Measure.quasiMeasurePreserving_fst (μ := splitBaseLaw μ ξ t) (ν := μ.prod μ)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := bernoulliArrayLaw μ ξ t) (ν := standardGaussian p)).ae
        ((h.thinned t ht.1 ht.2).bounded i))
  filter_upwards [seededCopyDirection_bounded (splitBaseLaw μ ξ t) μ ξ h fresh i, hrow] with z hz hzi
  have hra : 0 ≤ r * (1 + t) := mul_nonneg hr.1 (by linarith [ht.1])
  have hra2 : r * (1 + t) ≤ 2 := by nlinarith [ht.1, ht.2, hr.1, hr.2]
  calc
    _ ≤ ‖(r * (1 + t)) • seededCopyDirection ξ fresh i z‖ + ‖z.1.1 i‖ := norm_sub_le _ _
    _ = (r * (1 + t)) * ‖seededCopyDirection ξ fresh i z‖ + ‖z.1.1 i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hra]
    _ ≤ 4 * δ := by
      have hh := mul_le_mul hra2 hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith

theorem seeded_matrix_estimate_with_copies
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε)
    (ht : t ∈ Icc (0 : ℝ) 1) (hδh : δ ≤ s.bandwidth)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t) :
    AveragedSelectorMatrixEstimate s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
      (seededSplitGaussianScale ε t • A) (fun z => seededSplitBaseValue A x ε t z.1)
      logisticMatrixConstant
      (seededBaseConcentrationConstant * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  have hc := rectangleBaseConcentration_seededSplitBase h hp hunit A hA x hε ht.1 ht.2
  have hn := averagedSelectorMatrixEstimate_of_rectangle_concentration hp
    ((splitBaseLaw μ ξ t).prod (μ.prod μ)) (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp measurable_fst) s A
    (factor_coordinate_normSq_eq_one A hA hunit) seededBaseConcentrationConstant_pos
    h.delta_nonneg hδh (Real.sqrt_nonneg _) hscale
    (by rw [map_seededSplitBaseValue_fst]; exact hc)
  simpa only [mul_assoc] using hn

theorem seeded_relative_cubic_product_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε)
    (ht : t ∈ Icc (0 : ℝ) 1) (hδh : δ ≤ s.bandwidth)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t) :
    |restorationThirdExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
      (seededCopyOriginal ξ) (fun _ _ => 0) (seededSplitGaussianScale ε t)| ≤
        seededRestorationConstant / (seededSplitGaussianScale ε t) ^ 2 * M₃ *
          dimensionLog p * Real.sqrt (dimensionLog p) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  apply restoration_third_relative_product hp s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
    originalSigma originalSigma_le A (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp (comap_measurable Prod.fst))
    (seeded_matrix_estimate_with_copies μ ξ h hp hunit A hA s x hε ht hδh hscale)
    (seededCopyWhitened A ξ) (seededCopyWhitened_measurable μ ξ h A)
    (seededCopyWhitened_integrable_coordinate_pair (splitBaseLaw μ ξ t) μ ξ h A)
    (seededCopyOriginal ξ) (seededCopyOriginal_measurable ξ h.measurable)
    h.delta_nonneg hrel.s₃_nonneg (seededCopyOriginal_bounded (splitBaseLaw μ ξ t) μ ξ h)
    (seeded_copy_conditional_third_budget (splitBaseLaw μ ξ t) μ ξ h hrel A hA)
    logisticMatrixConstant_ge_one seededBaseConcentrationConstant_pos.le hscale

theorem seededCopyDirection_conditional_fourth_budget
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (fresh : Bool) (f : Face p) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
    matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
      (seededCopyWhitened A ξ) (fun i z =>
        FaceSmoother.normalDot f (seededCopyDirection ξ fresh i z) ^ 2) z) u ≤ M₄ * vectorNormSq u := by
  cases fresh
  · exact seeded_copy_conditional_fourth_budget ρ μ ξ h hrel A hA f
  · exact seeded_copy_conditional_fresh_fourth_budget ρ μ ξ h hrel A hA f

theorem seeded_relative_fourth_product_bound
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
    (freshY freshW freshShift : Bool) :
    |restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
      (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
      (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale ε t)| ≤
        seededRestorationConstant / (seededSplitGaussianScale ε t) ^ 2 * M₄ / s.bandwidth *
          dimensionLog p * Real.sqrt (dimensionLog p) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1 ht.2
  have hδh : δ ≤ s.bandwidth :=
    (le_mul_of_one_le_left h.delta_nonneg (le_max_left _ _)).trans hband
  have hv (i : Fin n) : Measurable (seededCopyShift ξ freshShift t r i) := by
    unfold seededCopyShift
    exact (measurable_const.smul (seededCopyDirection_measurable ξ h.measurable freshShift i)).sub
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
  exact restoration_fourth_relative_product hp s ((splitBaseLaw μ ξ t).prod (μ.prod μ))
    originalSigma originalSigma_le A (fun z => seededSplitBaseValue A x ε t z.1)
    ((measurable_seededSplitBaseValue A x ε t).comp (comap_measurable Prod.fst))
    (seeded_matrix_estimate_with_copies μ ξ h hp hunit A hA s x hε ht hδh hscale)
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
    logisticMatrixConstant_ge_one seededBaseConcentrationConstant_pos.le hscale hband

end

end RectangleCLT.Companion.SplitV4
