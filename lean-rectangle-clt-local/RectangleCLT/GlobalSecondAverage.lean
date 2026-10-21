import RectangleCLT.GaussianComparisonGlobalHessian
import RectangleCLT.ProxySecondMoment

/-! The full-eigenvalue bound for the actual retained common-point Hessian.
The bounded base supplies the independent boundary estimate at early times;
an independent Gaussian half supplies it at late times. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def globalSecondTimeConstant : ℝ :=
  3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) +
    4 * gaussianSecondGlobalConstant

theorem globalSecondTimeConstant_pos : 0 < globalSecondTimeConstant := by
  unfold globalSecondTimeConstant gaussianSecondGlobalConstant interpolationShortScaleConstant
  positivity

namespace FaceSmoother

open GaussianTube

variable {p : ℕ} (s : FaceSmoother p)

theorem integral_sum_abs_second_normalized_global_bounded_base_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (∫ b, ∑ j, ∑ k,
      |(s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).convolutionSecondDerivative
        (gaussianLaw A) (normalizedThinnedShift t b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
      40 * Real.exp 10 *
        (1073741824 *
          (4 * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) + 2 * δ / Real.sqrt t) *
          Real.sqrt (dimensionLog p / ((1 - t) / t))) *
        (Real.sqrt (dimensionLog p)) ^ 2 / (Real.sqrt ν) ^ 2 := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  let W := normalizedThinnedShift (p := p) (n := n) t
  let w := Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))
  let B := 1073741824 * (4 * w + 2 * δ / Real.sqrt t) *
    Real.sqrt (dimensionLog p / ((1 - t) / t))
  have hδ := h.delta_nonneg
  have hw : 0 < w := div_pos (Real.sqrt_pos.mpr hν)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (log_exp_mul_nat_ge_one hp))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : Measurable W := measurable_const.smul (measurable_arraySum p n)
  have hboundary (q : ℕ) (hq : 0 < q) (hq2 : q ≤ 2)
      (R : FaceSmoother p) (r : Vector p) :
      (bernoulliArrayLaw μ ξ t).real {b | W b + r ∈ R.boundaryLayer ((q : ℝ) * w)} ≤ B := by
    have hv : 0 < (1 - t) / t := div_pos (sub_pos.mpr ht1) ht
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hh := (h.normalized_thinned t ht ht1.le).boundary_probability_le hp hv
      (h.normalized_thinned_sum_unit_diagonal hunit t ht ht1.le) R r (mul_pos hqR hw)
    rw [sumVector_normalizedThinned] at hh
    apply hh.trans
    dsimp only [B]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1073741824)
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show q ≤ 4 by omega)) hw.le) _
  exact sn.integral_sum_abs_convolutionSecond_fullDual_le_of_boundary
    (bernoulliArrayLaw μ ξ t) hp A hν hlower W hW hB hboundary

private theorem second_early_time_scale {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    (a / Real.sqrt ((1 - t) / t)) / t ≤ 2 * a / Real.sqrt t := by
  have ht1 : t < 1 := by linarith
  have htm : 0 < 1 - t := by linarith
  have hts := Real.sqrt_pos.mpr ht
  have hvs := Real.sqrt_pos.mpr (div_pos htm ht)
  have hm : (1 : ℝ) / 2 ≤ Real.sqrt (1 - t) := by
    nlinarith [Real.sq_sqrt htm.le, Real.sqrt_nonneg (1 - t)]
  have he : Real.sqrt ((1 - t) / t) * t = Real.sqrt (1 - t) * Real.sqrt t := by
    rw [Real.sqrt_div htm.le]
    field_simp [hts.ne']
    calc
      _ = Real.sqrt (1 - t) * (Real.sqrt t) ^ 2 := by rw [Real.sq_sqrt ht.le]
      _ = _ := by ring
  have hd : (1 : ℝ) / 2 * Real.sqrt t ≤ Real.sqrt ((1 - t) / t) * t := by
    rw [he]
    exact mul_le_mul_of_nonneg_right hm hts.le
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos hvs ht) hts).mpr
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
  convert hh using 1 <;> ring

theorem integral_sum_abs_second_bernoulli_global_largeTime_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hlarge : (1 / ν) * dimensionLog p * s.bandwidth ^ 2 ≤ t) :
    (∫ b, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A))
      (arraySum b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
      globalSecondTimeConstant * dimensionLog p / (Real.sqrt ν * Real.sqrt t) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  have ha := Real.sqrt_pos.mpr hν
  have hroot := Real.sqrt_pos.mpr ht
  have hshort : 0 ≤ 3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) := by
    unfold interpolationShortScaleConstant
    positivity
  by_cases hhalf : t ≤ 1 / 2
  · let a := 80 * 1073741824 * Real.exp 10 * dimensionLog p / Real.sqrt ν
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hb := global_early_boundary_scale_le hν hL s.bandwidth_pos h.delta_nonneg
      hband ht ht1 hlarge (by norm_num : (0 : ℝ) ≤ 1073741824) (by decide : 4 ≤ 4)
    have hn0 := s.integral_sum_abs_second_normalized_global_bounded_base_le
      h hp hunit A hν hlower ht ht1
    have hn : (∫ b, ∑ j, ∑ k,
        |(s.scaleDown (Real.sqrt t) hroot).convolutionSecondDerivative (gaussianLaw A)
          (normalizedThinnedShift t b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
        a / Real.sqrt ((1 - t) / t) := by
      apply hn0.trans
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
          (by positivity : 0 ≤ 40 * Real.exp 10))
            (sq_nonneg (Real.sqrt (dimensionLog p)))) (sq_nonneg (Real.sqrt ν))
      apply hh.trans_eq
      rw [Real.sq_sqrt hL0]
      have hc : Real.sqrt ν / (Real.sqrt ν) ^ 2 = 1 / Real.sqrt ν := by
        field_simp [ha.ne']
        <;> ring
      calc
        _ = (80 * 1073741824 * Real.exp 10 * dimensionLog p /
            Real.sqrt ((1 - t) / t)) * (Real.sqrt ν / (Real.sqrt ν) ^ 2) := by ring
        _ = _ := by rw [hc]; dsimp [a]; ring
    have hC : 160 * 1073741824 * Real.exp 10 ≤ globalSecondTimeConstant := by
      unfold globalSecondTimeConstant gaussianSecondGlobalConstant
      nlinarith [Real.exp_pos 10]
    rw [s.integral_sum_abs_second_bernoulli_scaling μ ξ A ht]
    calc
      _ ≤ (a / Real.sqrt ((1 - t) / t)) / t := div_le_div_of_nonneg_right hn ht.le
      _ ≤ 2 * a / Real.sqrt t := second_early_time_scale ha0 ht hhalf
      _ = (160 * 1073741824 * Real.exp 10) * dimensionLog p /
          (Real.sqrt ν * Real.sqrt t) := by dsimp [a]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hL0) (mul_nonneg ha.le hroot.le)
  · rw [s.integral_sum_abs_second_bernoulli_scaling μ ξ A ht]
    let sn := s.scaleDown (Real.sqrt t) hroot
    let a := gaussianSecondGlobalConstant * dimensionLog p / Real.sqrt ν
    have ha0 : 0 ≤ a :=
      div_nonneg (mul_nonneg gaussianSecondGlobalConstant_pos.le hL0) ha.le
    have hb := integral_mono_of_nonneg
      (ae_of_all (bernoulliArrayLaw μ ξ t) (fun b => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)))) (integrable_const a)
      (ae_of_all (bernoulliArrayLaw μ ξ t) (fun b =>
        sn.sum_abs_convolutionSecondDerivative_global_le hp A (normalizedThinnedShift t b)
          hA hν hlower))
    simp only [integral_const, measureReal_univ_eq_one, one_smul] at hb
    have htime : 1 / t ≤ 2 / Real.sqrt t := by
      apply (div_le_div_iff₀ ht hroot).mpr
      have hs : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1.le
      linarith [lt_of_not_ge hhalf]
    have hC : 2 * gaussianSecondGlobalConstant ≤ globalSecondTimeConstant := by
      unfold globalSecondTimeConstant
      linarith [gaussianSecondGlobalConstant_pos]
    calc
      _ ≤ a / t := div_le_div_of_nonneg_right hb ht.le
      _ ≤ a * (2 / Real.sqrt t) := by
        simpa only [mul_one, one_mul, div_eq_mul_inv] using mul_le_mul_of_nonneg_left htime ha0
      _ = (2 * gaussianSecondGlobalConstant) * dimensionLog p /
          (Real.sqrt ν * Real.sqrt t) := by dsimp [a]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hL0) (mul_nonneg ha.le hroot.le)

/-- The actual common-point Hessian has an integrable square-root time
singularity under the full-eigenvalue hypothesis, with unmatched covariance
allowed for the bounded observations. -/
theorem selectorSecondAbsoluteSum_time_le_full_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      globalSecondTimeConstant * dimensionLog p / (Real.sqrt ν * Real.sqrt t) := by
  let K := 3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  have hKC : K ≤ globalSecondTimeConstant := by
    change K ≤ K + 4 * gaussianSecondGlobalConstant
    linarith [gaussianSecondGlobalConstant_pos]
  have hL : 0 < dimensionLog p := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have ha := Real.sqrt_pos.mpr hν
  have htroot := Real.sqrt_pos.mpr ht
  by_cases hlarge : (1 / ν) * dimensionLog p * s.bandwidth ^ 2 ≤ t
  · have hh := s.selectorSecondAbsoluteSum_le_expected
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0
      (thinningProbability_nonneg ht1.le) (thinningProbability_le_one ht.le) (thinningScale t)
    rw [s.selectorSecondExpectedAbsolute_eq_integral_bernoulliArrayLaw
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht.le ht1.le] at hh
    simp only [zero_add] at hh
    exact hh.trans (s.integral_sum_abs_second_bernoulli_global_largeTime_le
      h hp hunit A hA hν hlower hband ht ht1 hlarge)
  · have hs := s.selectorSecondAbsoluteSum_shortScale_le_proxy μ ξ h hp hunit A hA
      hband ht.le ht1.le
    have hquad : ν * t ≤ dimensionLog p * s.bandwidth ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hlarge)) hν.le
      field_simp [hν.ne'] at hh
      nlinarith
    have htime : Real.sqrt ν * Real.sqrt t ≤ s.bandwidth * Real.sqrt (dimensionLog p) := by
      apply (sq_le_sq₀ (mul_nonneg ha.le htroot.le)
        (mul_nonneg s.bandwidth_pos.le (Real.sqrt_nonneg _))).mp
      simpa only [mul_pow, Real.sq_sqrt hν.le, Real.sq_sqrt ht.le,
        Real.sq_sqrt hL.le, mul_comm] using hquad
    have hsmall : K * Real.sqrt (dimensionLog p) / s.bandwidth ≤
        K * dimensionLog p / (Real.sqrt ν * Real.sqrt t) := by
      apply (div_le_div_iff₀ s.bandwidth_pos (mul_pos ha htroot)).mpr
      have hh := mul_le_mul_of_nonneg_left htime
        (mul_nonneg hK (Real.sqrt_nonneg (dimensionLog p)))
      calc
        _ ≤ (K * Real.sqrt (dimensionLog p)) *
            (s.bandwidth * Real.sqrt (dimensionLog p)) := hh
        _ = K * s.bandwidth * (Real.sqrt (dimensionLog p)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hL.le]; ring
    exact hs.trans (hsmall.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hL.le)
        (mul_nonneg ha.le htroot.le)))

end FaceSmoother

end

end RectangleCLT
