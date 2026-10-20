import RectangleCLT.ThinnedHypotheses
import RectangleCLT.GaussianEnvelope
import RectangleCLT.ConvolutionEnvelopes
import RectangleCLT.SelectorEnvelopeLaw

/-! Uniform short-scale derivative-majorant averaging along the actual
interpolation: bounded-base averaging before one half and Gaussian-base
averaging after one half. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable def interpolationShortScaleConstant : ℝ :=
  8589934592 + 2 * Real.exp (3 / 2 : ℝ)

theorem sqrt_dimensionLog_div_le_two_sqrt {p : ℕ} (hp : 1 ≤ p) {v : ℝ}
    (hv : 1 / 2 ≤ v) :
    Real.sqrt (dimensionLog p / v) ≤ 2 * Real.sqrt (dimensionLog p) := by
  have hvpos : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  calc
    _ ≤ Real.sqrt (2 * dimensionLog p) := by
      apply Real.sqrt_le_sqrt
      apply (div_le_iff₀ hvpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hv hL]
    _ = Real.sqrt 2 * Real.sqrt (dimensionLog p) := by rw [Real.sqrt_mul (by norm_num)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem sum_thirdLocalMajorant_le_bandwidth_mul_fourth (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.thirdLocalMajorant x j k l) ≤
      s.bandwidth * (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) := by
  let θ := (s.weights x).theta
  let c := (Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3)
  have hc : 0 ≤ c := mul_nonneg (pow_nonneg (Real.exp_nonneg _) _)
    (div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _))
  have hθ : 0 ≤ θ := (s.weights x).theta_nonneg
  have he : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp (by norm_num)
  have hpoly : 6 * θ ^ 3 + 6 * θ ^ 2 + θ ≤
      24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ := by
    nlinarith only [pow_nonneg hθ 4, pow_nonneg hθ 3, sq_nonneg θ]
  have hP4 : 0 ≤ 24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ := by positivity
  have h3 : (∑ j, ∑ k, ∑ l, s.thirdLocalMajorant x j k l) =
      c * (6 * θ ^ 3 + 6 * θ ^ 2 + θ) := by
    simp only [thirdLocalMajorant, ← Finset.mul_sum]
    rw [(s.weights x).sum_thirdMajorant]
  have h4 : s.bandwidth *
      (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) =
      c * Real.exp 2 * (24 * θ ^ 4 + 36 * θ ^ 3 + 14 * θ ^ 2 + θ) := by
    simp only [fourthLocalMajorant, ← Finset.mul_sum]
    rw [(s.weights x).sum_fourthMajorant]
    dsimp [c, θ]
    field_simp [ne_of_gt s.bandwidth_pos]
    ring
  rw [h3, h4]
  exact (mul_le_mul_of_nonneg_left hpoly hc).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left he hc]) hP4)

noncomputable def interpolationThirdMajorantIntegral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : ℝ :=
  ∫ z : (Fin n → Vector p) × Vector p, ∑ j, ∑ k, ∑ l,
    s.thirdLocalMajorant (arraySum z.1 + z.2) j k l
      ∂(bernoulliArrayLaw μ ξ t).prod (gaussianLaw (Real.sqrt t • A))

noncomputable def interpolationFourthMajorantIntegral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : ℝ :=
  ∫ z : (Fin n → Vector p) × Vector p, ∑ j, ∑ k, ∑ l, ∑ m,
    s.fourthLocalMajorant (arraySum z.1 + z.2) j k l m
      ∂(bernoulliArrayLaw μ ξ t).prod (gaussianLaw (Real.sqrt t • A))

theorem interpolationFourthMajorantIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.interpolationFourthMajorantIntegral μ ξ A t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let B := bernoulliArrayLaw μ ξ t
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hsqrt {v : ℝ} (hv : 1 / 2 ≤ v) := sqrt_dimensionLog_div_le_two_sqrt hp hv
  have hC0 : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 := by positivity
  by_cases hhalf : t ≤ 1 / 2
  · have hv : 0 < 1 - t := by linarith
    have hraw := (h.thinned t ht ht1).integral_sum_fourthLocalMajorant_independent_shift_le
      hp hv (h.thinned_sum_unit_diagonal hunit t ht ht1) s ν id measurable_id
    have hlen : s.bandwidth + 2 * δ ≤ 2 * s.bandwidth := by linarith [h.delta_nonneg]
    calc
      _ ≤ (75 * (Real.exp 2) ^ 5) *
          (2147483648 * (s.bandwidth + 2 * δ) * Real.sqrt (dimensionLog p / (1 - t))) /
            s.bandwidth ^ 4 := hraw
      _ ≤ (75 * (Real.exp 2) ^ 5) *
          (2147483648 * (2 * s.bandwidth) * (2 * Real.sqrt (dimensionLog p))) /
            s.bandwidth ^ 4 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlen (by norm_num))
          (hsqrt (by linarith)) (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) s.bandwidth_pos.le))
      _ = (75 * (Real.exp 2) ^ 5 * 8589934592) *
          Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
        field_simp [ne_of_gt s.bandwidth_pos]
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC0
        unfold interpolationShortScaleConstant
        linarith [Real.exp_pos (3 / 2 : ℝ)]
  · have hthalf : 1 / 2 ≤ t := le_of_lt (lt_of_not_ge hhalf)
    have htpos : 0 < t := by linarith
    have hdiag (j : Fin p) :
        ((Real.sqrt t • A) * (Real.sqrt t • A).transpose) j j = t := by
      have hh := congrArg (fun M : Matrix (Fin p) (Fin p) ℝ => M j j)
        (interpolatedGaussian_covariance A ht)
      rw [covariance_gaussianLaw] at hh
      change ((Real.sqrt t • A) * (Real.sqrt t • A).transpose) j j = t * (A * A.transpose) j j at hh
      simpa only [hA, hunit, mul_one] using hh
    have hraw := s.gaussian_integral_sum_fourthLocalMajorant_independent_shift_le hp
      (Real.sqrt t • A) htpos hdiag B arraySum (measurable_arraySum p n)
    have heq : s.interpolationFourthMajorantIntegral μ ξ A t =
        (∫ z : Vector p × (Fin n → Vector p), ∑ j, ∑ k, ∑ l, ∑ m,
          s.fourthLocalMajorant (z.1 + arraySum z.2) j k l m ∂ν.prod B) := by
      unfold interpolationFourthMajorantIntegral
      change (∫ z : (Fin n → Vector p) × Vector p, ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant (arraySum z.1 + z.2) j k l m ∂B.prod ν) = _
      rw [← integral_prod_swap (fun z : (Fin n → Vector p) × Vector p =>
        ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (arraySum z.1 + z.2) j k l m)]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        change (∑ j, ∑ k, ∑ l, ∑ m,
          s.fourthLocalMajorant (arraySum z.2 + z.1) j k l m) = _
        simp only [add_comm])
    rw [heq]
    calc
      _ ≤ (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
          Real.sqrt (dimensionLog p / t) / s.bandwidth ^ 3 := hraw
      _ ≤ (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
          (2 * Real.sqrt (dimensionLog p)) / s.bandwidth ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        exact mul_le_mul_of_nonneg_left (hsqrt hthalf) (by positivity)
      _ = (75 * (Real.exp 2) ^ 5 * (2 * Real.exp (3 / 2 : ℝ))) *
          Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC0
        unfold interpolationShortScaleConstant
        linarith

/-- The third-order positive majorants have the corresponding uniform
short-scale bound under the same actual interpolation law. -/
theorem interpolationThirdMajorantIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
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
        (s.interpolationFourthMajorantIntegral_le μ ξ h hp hunit A hA hband ht ht1)
        s.bandwidth_pos.le
    _ = _ := by
      field_simp [ne_of_gt s.bandwidth_pos]
      ring

/-- Actual pointwise summed third derivatives have the uniform short-scale
bound, with the canonical thinned and independent Gaussian probability laws. -/
theorem selectorThirdAbsoluteAverage_shortScale_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 2 := by
  have hh := s.selectorThirdAbsoluteAverage_le_prod_integral
    (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht ht1
  simp only [zero_add] at hh
  exact hh.trans (s.interpolationThirdMajorantIntegral_le μ ξ h hp hunit A hA hband ht ht1)

/-- The separate local fourth-derivative convolution majorants have a uniform
short-scale expected mass. -/
theorem selectorFourthEnvelopeAverage_shortScale_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    selectorFourthEnvelopeAverage μ ξ 0 t
      (s.convolutionFourthLocalMajorant (gaussianLaw (Real.sqrt t • A))) ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  rw [s.selectorFourthEnvelopeAverage_eq_prod_integral
    (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 ht ht1]
  simpa only [zero_add] using
    s.interpolationFourthMajorantIntegral_le μ ξ h hp hunit A hA hband ht ht1

/-- A fully instantiated short-scale bound for the actual path derivative.
The local derivative envelope and all probability/integrability premises of
the comparison have been discharged. -/
theorem abs_selectorHeatDerivative_shortScale_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A 0 t| ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) *
          (t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) +
            6 * gamma4 μ ξ / s.bandwidth ^ 3) := by
  let ν := gaussianLaw (Real.sqrt t • A)
  have hc := s.abs_selectorHeatDerivative_le_comparison μ ξ h A hA 0 ht ht1
    (s.convolutionFourthLocalMajorant ν)
    (fun y z hz j k l m => s.abs_convolutionFourthDerivative_shift_le ν y
      (hz.trans (by linarith [h.delta_nonneg])) j k l m)
    (s.integrable_sum_convolutionFourthLocalMajorant_mask ν μ ξ h.measurable 0 (thinningScale t))
  have h3 := s.selectorThirdAbsoluteAverage_shortScale_le μ ξ h hp hunit A hA hband ht ht1
  have h4 := s.selectorFourthEnvelopeAverage_shortScale_le μ ξ h hp hunit A hA hband ht ht1
  apply hc.trans
  apply (add_le_add
    (mul_le_mul_of_nonneg_left h3 (mul_nonneg (div_nonneg ht (by norm_num)) (gamma3_nonneg μ ξ)))
    (mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num) (gamma4_nonneg μ ξ)))).trans_eq
  ring

end FaceSmoother
end RectangleCLT
