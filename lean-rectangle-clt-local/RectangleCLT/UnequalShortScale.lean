import RectangleCLT.ProxySecondMoment
import RectangleCLT.ProxySmoothing

/-! Unit-diagonal short-scale cubic averaging and endpoint smoothing for
unequal covariance matrices. No sparse spectral positivity is assumed. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem interpolationThirdMajorantIntegral_le_unequal
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.interpolationThirdMajorantIntegral μ ξ A t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 2 := by
  let B := bernoulliArrayLaw μ ξ t
  let ν := gaussianLaw (Real.sqrt t • A)
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  let W : (Fin n → Vector p) × Vector p → Vector p := fun z => arraySum z.1 + z.2
  have hW : Measurable W := ((measurable_arraySum p n).comp measurable_fst).add measurable_snd
  have hi3 : Integrable (fun z => ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W z) j k l) (B.prod ν) :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          s.integrable_thirdLocalMajorant_comp (B.prod ν) W hW j k l)))
  have hi4 : Integrable (fun z => ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W z) j k l m)
      (B.prod ν) :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_fourthLocalMajorant_comp (B.prod ν) W hW j k l m))))
  have hh := integral_mono hi3 (hi4.const_mul s.bandwidth)
    (fun z => s.sum_thirdLocalMajorant_le_bandwidth_mul_fourth (W z))
  rw [integral_const_mul] at hh
  calc
    _ ≤ s.bandwidth * s.interpolationFourthMajorantIntegral μ ξ A t := hh
    _ ≤ s.bandwidth * ((75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3) :=
      mul_le_mul_of_nonneg_left
        (s.interpolationFourthMajorantIntegral_le_proxy μ ξ h hp hunit A hA hband ht ht1)
        s.bandwidth_pos.le
    _ = _ := by
      field_simp [ne_of_gt s.bandwidth_pos]
      ring

/-- Actual pointwise summed third derivatives have the uniform short-scale
bound, with the canonical thinned and independent Gaussian probability laws. -/
theorem selectorThirdAbsoluteAverage_shortScale_le_unequal
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 2 := by
  have hh := s.selectorThirdAbsoluteAverage_le_prod_integral
    (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht ht1
  simp only [zero_add] at hh
  exact hh.trans (s.interpolationThirdMajorantIntegral_le_unequal μ ξ h hp hunit A hA hband ht ht1)


theorem sharpThirdAverage_shortScale_le_unequal
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.sharpThirdAverage μ ξ A t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 2 := by
  exact s.selectorThirdAbsoluteAverage_shortScale_le_unequal μ ξ h hp hunit A hA hband ht ht1

end RectangleCLT.FaceSmoother

namespace RectangleCLT.BoundedIndependentHypotheses

/-- The endpoint error under exactly the two positive pair gaps of the
unequal-covariance master lemma. No discrepancy restriction is needed. -/
theorem smoother_rectangle_error_le_unequal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hcS : 0 < pairGap (covariance μ (sumVector ξ)))
    (hcA : 0 < pairGap (A * A.transpose))
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) :
    |μ.real {ω | s.Inside (sumVector ξ ω)} - (gaussianLaw A).real {z | s.Inside z}| ≤
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
        (8 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
          min (pairGap (covariance μ (sumVector ξ))) (pairGap (A * A.transpose)) := by
  let c := min (pairGap (covariance μ (sumVector ξ))) (pairGap (A * A.transpose))
  have hc : 0 < c := lt_min hcS hcA
  have hsmall := s.probability_gap_le_smoother_gap_add_kappa μ (gaussianLaw A)
    (sumVector ξ) h.measurable_sum id measurable_id
  have hb := h.integral_kappa_le s 0 hp hunit hcS hband
  have hg := s.gaussian_expected_kappa_le hp A 0 hA hcA
  simp only [add_zero] at hb hg
  have hT : 0 ≤ s.bandwidth * Real.sqrt (dimensionLog p) :=
    mul_nonneg s.bandwidth_pos.le (Real.sqrt_nonneg _)
  have hN4 : 0 ≤ 4 * Real.exp 4 * s.bandwidth * Real.sqrt (dimensionLog p) := by
    simpa only [mul_assoc] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg 4)) hT
  have hN2 : 0 ≤ 2 * s.bandwidth * Real.sqrt (dimensionLog p) := by
    simpa only [mul_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hT
  have hb' : (∫ ω, s.kappa (sumVector ξ ω) ∂μ) ≤
      4 * Real.exp 4 * s.bandwidth * Real.sqrt (dimensionLog p) / c :=
    hb.trans (div_le_div_of_nonneg_left hN4 hc (min_le_left _ _))
  have hg' : (∫ z, s.kappa z ∂gaussianLaw A) ≤
      2 * s.bandwidth * Real.sqrt (dimensionLog p) / c :=
    hg.trans (div_le_div_of_nonneg_left hN2 hc (min_le_right _ _))
  exact hsmall.trans ((add_le_add_left
    (mul_le_mul_of_nonneg_left (add_le_add hb' hg') (by norm_num : (0 : ℝ) ≤ 2))
      _).trans_eq (by dsimp [c]; ring))

theorem closedBox_error_le_unequal_smoother_gap
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ h : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    (hcS : 0 < pairGap (covariance μ (sumVector ξ)))
    (hcA : 0 < pairGap (A * A.transpose))
    (lo hi : Vector p) (hh : 0 < h) (hband : δ ≤ h) :
    rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
      |(∫ ω, (FaceSmoother.closedBox lo hi h hh).F (sumVector ξ ω) ∂μ) -
        (∫ z, (FaceSmoother.closedBox lo hi h hh).F z ∂gaussianLaw A)| +
        (8 * Real.exp 4 + 4) * h * Real.sqrt (dimensionLog p) /
          min (pairGap (covariance μ (sumVector ξ))) (pairGap (A * A.transpose)) := by
  have hh' := hdata.smoother_rectangle_error_le_unequal hp hunit A hA hcS hcA
    (FaceSmoother.closedBox lo hi h hh) hband
  have hμ : {ω | (FaceSmoother.closedBox lo hi h hh).Inside (sumVector ξ ω)} =
      sumVector ξ ⁻¹' (Rect.closedBox lo hi).carrier := by
    ext ω
    exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
  have hG : {z | (FaceSmoother.closedBox lo hi h hh).Inside z} =
      (Rect.closedBox lo hi).carrier := by
    ext z
    exact FaceSmoother.closedBox_Inside lo hi h hh z
  rw [hμ, hG] at hh'
  simpa only [rectangleError, FaceSmoother.closedBox] using hh'

end RectangleCLT.BoundedIndependentHypotheses
