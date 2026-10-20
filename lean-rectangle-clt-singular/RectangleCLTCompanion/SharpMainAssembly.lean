import RectangleCLTCompanion.SharpSplitCubic
import RectangleCLTCompanion.RestorationScales
import RectangleCLTCompanion.SharpSplitFourthPath
import RectangleCLTCompanion.SharpComparisonLate
import RectangleCLTCompanion.SharpEndpoint
import RectangleCLTCompanion.Integration
import RectangleCLTCompanion.MasterReduction

/-! Actual sharp comparison and rectangle assembly. The only analytic
premise retained here is the actual averaged selector matrix estimate on the
concrete full Bernoulli/split-Gaussian base. No derivative-cap premise,
conditional mask concentration, or positive local eigenvalue is assumed. -/

open MeasureTheory Set
open scoped BigOperators Interval

universe u

set_option maxHeartbeats 1000000

namespace RectangleCLT.Companion

noncomputable section

def sharpBandwidthConstant (C : ℝ) : ℝ := 12 + 4 * restorationBandwidthConstant C

def sharpComparisonConstant (C : ℝ) : ℝ :=
  FaceSmoother.earlyComparisonConstant + 168 * C ^ 3

def sharpMasterConstant (C : ℝ) : ℝ := 1 + 3 * sharpComparisonConstant C + sharpEndpointConstant

theorem sharpBandwidthConstant_ge_twelve {C : ℝ} (hC : 1 ≤ C) :
    12 ≤ sharpBandwidthConstant C := by
  unfold sharpBandwidthConstant
  linarith [restorationBandwidthConstant_pos hC]

theorem sharpComparisonConstant_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ sharpComparisonConstant C := by
  unfold sharpComparisonConstant FaceSmoother.earlyComparisonConstant interpolationShortScaleConstant
  have hc : 0 ≤ C := zero_le_one.trans hC
  positivity

theorem sharpMasterConstant_ge_one {C : ℝ} (hC : 1 ≤ C) : 1 ≤ sharpMasterConstant C := by
  unfold sharpMasterConstant
  linarith [sharpComparisonConstant_nonneg hC, sharpEndpointConstant_nonneg]

/-- The sole analytic family consumed by the sharp master. It concerns
actual score matrices on the actual full retained-array/split-Gaussian law. -/
def SplitMatrixEstimateFamily (a C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ (s : FaceSmoother p), a * δ ≤ s.bandwidth →
      ∀ t ∈ Ioo (0 : ℝ) 1, s.bandwidth ^ 2 * dimensionLog p ≤ t →
        AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
          (splitGaussianScale t • A) (splitBaseValue A 0 t) C
          (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))

end
end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p n : ℕ} (s : FaceSmoother p)

private theorem fourth_integrands_normalized
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 1 ≤ C)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)))
    (hp : 1 ≤ p) :
    (∀ r ∈ Icc (0 : ℝ) 1, |s.fourthPathIntegrandA (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      (84 * C ^ 3) * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) ∧
    (∀ r ∈ Icc (0 : ℝ) 1, |s.fourthPathIntegrandB (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      (84 * C ^ 3) * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) ∧
    (∀ r ∈ Icc (0 : ℝ) 1, |s.fourthPathIntegrandC (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      (84 * C ^ 3) * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth)) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hT : 0 ≤ s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) := by
    exact mul_nonneg (mul_nonneg s.bandwidth_pos.le hL) (Real.sqrt_nonneg _)
  have heq : 84 * C ^ 3 * δ ^ 2 * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) /
      (s.bandwidth ^ 2 * t) =
      (84 * C ^ 3) * δ ^ 2 * dimensionLog p * Real.sqrt (dimensionLog p) / (t * s.bandwidth) := by
    field_simp [ne_of_gt s.bandwidth_pos, ne_of_gt ht]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (s.abs_fourthPathIntegrandA_le_of_split_matrix_estimate μ ξ h A hA x ht ht1 hr
      hmatrix hC hT hband).trans_eq heq
  · intro r hr
    exact (s.abs_fourthPathIntegrandB_le_of_split_matrix_estimate μ ξ h A hA x ht ht1 hr
      hmatrix hC hT hband).trans_eq heq
  · intro r hr
    exact (s.abs_fourthPathIntegrandC_le_of_split_matrix_estimate μ ξ h A hA x ht ht1 hr
      hmatrix hC hT hband).trans_eq heq

theorem abs_selectorHeatDerivative_late_le_of_split_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 1 ≤ C)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      (168 * C ^ 3) * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ + δ ^ 2 / (t * s.bandwidth)) := by
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hδ := h.delta_nonneg
  have hcost : 2 * C ^ 2 ≤ 84 * C ^ 3 := by
    have hh : C ^ 2 ≤ C ^ 3 := by nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
    nlinarith [pow_nonneg hc 3]
  have hthree := s.abs_signedCubicPathTerm_le_of_split_matrix_estimate μ ξ h A hA x ht ht1 hmatrix
  have hthree' : |s.signedCubicPathTerm μ ξ A x t| ≤
      (84 * C ^ 3) * δ * dimensionLog p * Real.sqrt (dimensionLog p) / t := by
    apply hthree.trans
    calc
      _ = (2 * C ^ 2) * δ * dimensionLog p * Real.sqrt (dimensionLog p) / t := by
        field_simp [ne_of_gt s.bandwidth_pos, ne_of_gt ht]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcost hδ) hL) (Real.sqrt_nonneg _)) ht.le
  have hfour := s.fourth_integrands_normalized μ ξ h A hA x ht ht1 hC hband hmatrix hp
  have hh := s.abs_selectorHeatDerivative_late_le_of_restoration μ ξ h hp A hA x ht ht1
    (by positivity : 0 ≤ 84 * C ^ 3) hthree' hfour.1 hfour.2.1 hfour.2.2
  exact hh.trans_eq (by ring)

theorem abs_selectorHeatDerivative_late_le_of_split_matrix_estimate_and_cancellation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 1 ≤ C)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      (168 * C ^ 3) * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ ^ 2 / (t * s.bandwidth)) := by
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hfour := s.fourth_integrands_normalized μ ξ h A hA x ht ht1 hC hband hmatrix hp
  have hh := s.abs_selectorHeatDerivative_late_le_of_cancellation_and_restoration μ ξ h hp
    hcancel A hA x ht ht1 (by positivity : 0 ≤ 84 * C ^ 3) hfour.1 hfour.2.1 hfour.2.2
  exact hh.trans_eq (by ring)

/-- Integrate the actual path estimates through both endpoints. The sole
analytic input is the averaged matrix estimate on the concrete split base. -/
theorem interpolation_smoother_gap_le_of_split_matrix_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ C : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hC : 1 ≤ C) (hband : Companion.sharpBandwidthConstant C * δ ≤ s.bandwidth)
    (hmatrix : ∀ t ∈ Ioo (0 : ℝ) 1, s.bandwidth ^ 2 * dimensionLog p ≤ t →
      Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
        (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A 0 t) C
        (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      3 * Companion.sharpComparisonConstant C * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ + (δ ^ 2 / s.bandwidth) * Companion.comparisonLog (dimensionLog p) s.bandwidth) := by
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hδ := h.delta_nonneg
  have hbpos := s.bandwidth_pos
  have hrest := (Companion.restorationBandwidthConstant_pos hC).le
  have hband12 : 12 * δ ≤ s.bandwidth := by
    unfold Companion.sharpBandwidthConstant at hband
    nlinarith [mul_nonneg hrest hδ]
  have hband4 : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth := by
    unfold Companion.sharpBandwidthConstant at hband
    nlinarith
  have hCearly : earlyComparisonConstant ≤ Companion.sharpComparisonConstant C := by
    unfold Companion.sharpComparisonConstant
    nlinarith [pow_nonneg hc 3]
  have hClate : 168 * C ^ 3 ≤ Companion.sharpComparisonConstant C := by
    have he : 0 ≤ earlyComparisonConstant := by unfold earlyComparisonConstant interpolationShortScaleConstant; positivity
    unfold Companion.sharpComparisonConstant
    linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hbound := Companion.smoothed_gap_le_of_early_late
    (Companion.sharpComparisonConstant_nonneg hC) hδ (log_exp_mul_nat_ge_one hp)
    s.bandwidth_pos (by linarith : δ ≤ s.bandwidth)
    (s.continuousOn_integral_interpolationLaw μ ξ h.measurable A)
    (fun t ht => s.hasDerivAt_integral_interpolationLaw μ ξ h.measurable hδ h.bounded A ht.1 ht.2)
    (fun t ht => (s.abs_selectorHeatDerivative_early_le μ ξ h hp hunit A hA hband12 ht.1.le ht.2.le).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCearly (Real.sqrt_nonneg _))
        (by have ht0 := ht.1.le; positivity)))
    (fun t ht hb => (s.abs_selectorHeatDerivative_late_le_of_split_matrix_estimate μ ξ h hp A hA 0
      ht.1 ht.2.le hC hband4 (hmatrix t ht (by rw [mul_comm (s.bandwidth ^ 2) (dimensionLog p)]; exact hb))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hClate hL) (Real.sqrt_nonneg _)) (by have ht0 := ht.1.le; positivity)))
  rw [interpolationLaw_one μ ξ A, interpolationLaw_zero μ ξ h.measurable A,
    integral_map h.measurable_sum.aemeasurable s.continuous_F.aestronglyMeasurable] at hbound
  simpa only [abs_sub_comm] using hbound

theorem interpolation_smoother_gap_le_of_split_matrix_estimates_and_cancellation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ C : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hcancel : Companion.AggregateThirdMomentsVanish μ ξ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hC : 1 ≤ C) (hband : Companion.sharpBandwidthConstant C * δ ≤ s.bandwidth)
    (hmatrix : ∀ t ∈ Ioo (0 : ℝ) 1, s.bandwidth ^ 2 * dimensionLog p ≤ t →
      Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
        (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A 0 t) C
        (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      Companion.sharpComparisonConstant C * dimensionLog p * Real.sqrt (dimensionLog p) *
        (δ ^ 2 / s.bandwidth) * (1 + Companion.comparisonLog (dimensionLog p) s.bandwidth) := by
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hδ := h.delta_nonneg
  have hbpos := s.bandwidth_pos
  have hrest := (Companion.restorationBandwidthConstant_pos hC).le
  have hband12 : 12 * δ ≤ s.bandwidth := by
    unfold Companion.sharpBandwidthConstant at hband
    nlinarith [mul_nonneg hrest hδ]
  have hband4 : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth := by
    unfold Companion.sharpBandwidthConstant at hband
    nlinarith
  have hCearly : earlyComparisonConstant ≤ Companion.sharpComparisonConstant C := by
    unfold Companion.sharpComparisonConstant
    nlinarith [pow_nonneg hc 3]
  have hClate : 168 * C ^ 3 ≤ Companion.sharpComparisonConstant C := by
    have he : 0 ≤ earlyComparisonConstant := by unfold earlyComparisonConstant interpolationShortScaleConstant; positivity
    unfold Companion.sharpComparisonConstant
    linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hbound := Companion.zero_cubic_gap_le_of_early_late
    (Companion.sharpComparisonConstant_nonneg hC) (lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp) : 0 < dimensionLog p)
    s.bandwidth_pos (s.continuousOn_integral_interpolationLaw μ ξ h.measurable A)
    (fun t ht => s.hasDerivAt_integral_interpolationLaw μ ξ h.measurable hδ h.bounded A ht.1 ht.2)
    (fun t ht => (s.abs_selectorHeatDerivative_early_le_of_cancellation μ ξ h hp hunit hcancel A hA
      hband12 ht.1.le ht.2.le).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCearly (Real.sqrt_nonneg _)) (by have ht0 := ht.1.le; positivity)))
    (fun t ht hb => (s.abs_selectorHeatDerivative_late_le_of_split_matrix_estimate_and_cancellation
      μ ξ h hp hcancel A hA 0 ht.1 ht.2.le hC hband4
      (hmatrix t ht (by rw [mul_comm (s.bandwidth ^ 2) (dimensionLog p)]; exact hb))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hClate hL) (Real.sqrt_nonneg _)) (by have ht0 := ht.1.le; positivity)))
  rw [interpolationLaw_one μ ξ A, interpolationLaw_zero μ ξ h.measurable A,
    integral_map h.measurable_sum.aemeasurable s.continuous_F.aestronglyMeasurable] at hbound
  simpa only [abs_sub_comm] using hbound

end
end RectangleCLT.FaceSmoother

namespace RectangleCLT.Companion

noncomputable section

/-- The genuine split-base matrix family implies the unrestricted
fourth-order variational estimate for all actual rectangles. -/
theorem variationalEstimate_of_splitMatrixEstimateFamily {C : ℝ} (hC : 1 ≤ C)
    (hmatrix : SplitMatrixEstimateFamily.{u} (sharpBandwidthConstant C) C) :
    VariationalEstimate.{u} (sharpBandwidthConstant C) (sharpMasterConstant C) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA R w hband
  have hδ := hdata.delta_pos hp hunit
  have hδ0 := hdata.delta_nonneg
  have ha := sharpBandwidthConstant_ge_twelve hC
  have hw : 0 < w := by nlinarith [mul_le_mul_of_nonneg_right ha hδ0]
  have hδw : δ ≤ w := by nlinarith [mul_le_mul_of_nonneg_right ha hδ0]
  let L := dimensionLog p
  let κ := kappa L (pairGap (covariance μ (sumVector ξ)))
  let E := 3 * sharpComparisonConstant C * L * Real.sqrt L *
    (δ + (δ ^ 2 / w) * comparisonLog L w)
  have hgap (lo hi : Vector p) : let s := FaceSmoother.closedBox lo hi w hw
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ E := by
    let s := FaceSmoother.closedBox lo hi w hw
    exact s.interpolation_smoother_gap_le_of_split_matrix_estimates μ ξ hdata hp hunit A hA hC hband
      (fun t ht hb => hmatrix μ p n hp hn ξ δ A hdata hunit hA s hband t ht hb)
  have hr := rectangleError_le_smoother_gap_add_sharp_endpoint hdata hp hunit A hA w hw hδw E hgap R
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp)
  have hκ : 0 ≤ κ := (kappa_pos hL).le
  have hlog : 0 ≤ comparisonLog L w := le_max_left _ _
  have hX : 0 ≤ δ * L * Real.sqrt L + δ ^ 2 * (L * Real.sqrt L) / w * comparisonLog L w := by positivity
  have hY : 0 ≤ w * Real.sqrt L * κ := by positivity
  have hcomp := sharpComparisonConstant_nonneg hC
  have hCm : 3 * sharpComparisonConstant C ≤ sharpMasterConstant C := by
    unfold sharpMasterConstant
    linarith [sharpEndpointConstant_nonneg]
  have hCe : sharpEndpointConstant ≤ sharpMasterConstant C := by
    unfold sharpMasterConstant
    linarith
  apply hr.trans
  calc
    _ = (3 * sharpComparisonConstant C) *
        (δ * L * Real.sqrt L + δ ^ 2 * (L * Real.sqrt L) / w * comparisonLog L w) +
        sharpEndpointConstant * (w * Real.sqrt L * κ) := by dsimp [E, L, κ]; ring
    _ ≤ sharpMasterConstant C *
        (δ * L * Real.sqrt L + δ ^ 2 * (L * Real.sqrt L) / w * comparisonLog L w) +
        sharpMasterConstant C * (w * Real.sqrt L * κ) :=
      add_le_add (mul_le_mul_of_nonneg_right hCm hX) (mul_le_mul_of_nonneg_right hCe hY)
    _ = _ := by dsimp [L, κ]; ring

/-- Full signed tensor cancellation removes the cubic term in the actual
comparison before optimization and probability saturation. -/
theorem zeroSkewVariationalEstimate_of_splitMatrixEstimateFamily {C : ℝ} (hC : 1 ≤ C)
    (hmatrix : SplitMatrixEstimateFamily.{u} (sharpBandwidthConstant C) C) :
    ZeroSkewVariationalEstimate.{u} (sharpBandwidthConstant C) (sharpMasterConstant C) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA hcancel R w hband
  have hδ := hdata.delta_pos hp hunit
  have hδ0 := hdata.delta_nonneg
  have ha := sharpBandwidthConstant_ge_twelve hC
  have hw : 0 < w := by nlinarith [mul_le_mul_of_nonneg_right ha hδ0]
  have hδw : δ ≤ w := by nlinarith [mul_le_mul_of_nonneg_right ha hδ0]
  let L := dimensionLog p
  let κ := kappa L (pairGap (covariance μ (sumVector ξ)))
  let E := sharpComparisonConstant C * L * Real.sqrt L *
    (δ ^ 2 / w) * (1 + comparisonLog L w)
  have hgap (lo hi : Vector p) : let s := FaceSmoother.closedBox lo hi w hw
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ E := by
    let s := FaceSmoother.closedBox lo hi w hw
    exact s.interpolation_smoother_gap_le_of_split_matrix_estimates_and_cancellation
      μ ξ hdata hp hunit hcancel A hA hC hband
      (fun t ht hb => hmatrix μ p n hp hn ξ δ A hdata hunit hA s hband t ht hb)
  have hr := rectangleError_le_smoother_gap_add_sharp_endpoint hdata hp hunit A hA w hw hδw E hgap R
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp)
  have hκ : 0 ≤ κ := (kappa_pos hL).le
  have hlog : 0 ≤ comparisonLog L w := le_max_left _ _
  have hX : 0 ≤ δ ^ 2 * (L * Real.sqrt L) / w * (1 + comparisonLog L w) := by positivity
  have hY : 0 ≤ w * Real.sqrt L * κ := by positivity
  have hcomp := sharpComparisonConstant_nonneg hC
  have hCm : sharpComparisonConstant C ≤ sharpMasterConstant C := by
    unfold sharpMasterConstant
    linarith [sharpEndpointConstant_nonneg]
  have hCe : sharpEndpointConstant ≤ sharpMasterConstant C := by
    unfold sharpMasterConstant
    linarith
  apply hr.trans
  calc
    _ = sharpComparisonConstant C * (δ ^ 2 * (L * Real.sqrt L) / w * (1 + comparisonLog L w)) +
        sharpEndpointConstant * (w * Real.sqrt L * κ) := by dsimp [E, L, κ]; ring
    _ ≤ sharpMasterConstant C * (δ ^ 2 * (L * Real.sqrt L) / w * (1 + comparisonLog L w)) +
        sharpMasterConstant C * (w * Real.sqrt L * κ) :=
      add_le_add (mul_le_mul_of_nonneg_right hCm hX) (mul_le_mul_of_nonneg_right hCe hY)
    _ = _ := by dsimp [L, κ]; ring

/-- The exact saturated companion rates follow from the single actual
split-base matrix family. This remains conditional until that family is
proved by the signed selector geometry. -/
theorem companion_rates_of_splitMatrixEstimateFamily {C : ℝ} (hC : 1 ≤ C)
    (hmatrix : SplitMatrixEstimateFamily.{u} (sharpBandwidthConstant C) C) :
    GapSensitiveCLT.{u} (max 1 (sharpMasterConstant C *
      (sharpBandwidthConstant C + 3 / sharpBandwidthConstant C))) ∧
    ZeroSkewCLT.{u} (max 1 (sharpMasterConstant C *
      (sharpBandwidthConstant C + 3 / sharpBandwidthConstant C))) := by
  have ha : 1 ≤ sharpBandwidthConstant C := le_trans (by norm_num) (sharpBandwidthConstant_ge_twelve hC)
  have hc : 0 ≤ sharpMasterConstant C := zero_le_one.trans (sharpMasterConstant_ge_one hC)
  exact ⟨gapSensitiveCLT_of_variational ha hc (variationalEstimate_of_splitMatrixEstimateFamily hC hmatrix),
    zeroSkewCLT_of_variational ha hc (zeroSkewVariationalEstimate_of_splitMatrixEstimateFamily hC hmatrix)⟩

/-- The unrestricted covariance rate follows from the same single actual
matrix family, with one additional universal factor two. -/
theorem unrestrictedCLT_of_splitMatrixEstimateFamily {C : ℝ} (hC : 1 ≤ C)
    (hmatrix : SplitMatrixEstimateFamily.{u} (sharpBandwidthConstant C) C) :
    UnrestrictedCLT.{u} (2 * max 1 (sharpMasterConstant C *
      (sharpBandwidthConstant C + 3 / sharpBandwidthConstant C))) :=
  GapSensitiveCLT.toUnrestrictedCLT (zero_le_one.trans (le_max_left _ _))
    (companion_rates_of_splitMatrixEstimateFamily hC hmatrix).1

end
end RectangleCLT.Companion
