import RectangleCLTArxivV1.TransfersConditionalAverage
import RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization

/-! Absorption and saturation of the width-dependent conditional cutoff
estimate. This is Appendix E.1's threshold bound on the actual product law. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable def conditionalIntrinsicTransferConstant : ℝ :=
  1 + intrinsicUniversalConstant * (8 * Real.sqrt (4 / 3 : ℝ)) +
    16 * envelopeMaximumConstant + 16 * Real.sqrt 10 + 20 * Real.sqrt 2 +
    24 / Real.sqrt (2 / Real.pi)

theorem one_le_conditionalIntrinsicTransferConstant : 1 ≤ conditionalIntrinsicTransferConstant := by
  have hu := intrinsicUniversalConstant_pos.le
  have he := zero_le_one.trans one_le_envelopeMaximumConstant
  unfold conditionalIntrinsicTransferConstant
  have hpos : 0 ≤ intrinsicUniversalConstant * (8 * Real.sqrt (4 / 3 : ℝ)) +
      16 * envelopeMaximumConstant + 16 * Real.sqrt 10 + 20 * Real.sqrt 2 +
      24 / Real.sqrt (2 / Real.pi) := by positivity
  linarith

private theorem weighted_threshold_sum_le {a b c t z w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    a * t + b * (z + w) + c * z ≤ (1 + a + b + c) * (t + z + w) := by
  nlinarith only [mul_nonneg ha (add_nonneg hz hw), mul_nonneg hb ht,
    mul_nonneg hc (add_nonneg ht hw), add_nonneg (add_nonneg ht hz) hw]

/-- The optimized quantity retains exactly `gΣ/√L` relative to the archived
cutoff algebra; every probabilistic estimate is proved in the new modules. -/
theorem conditionalPolynomial_intrinsic_threshold {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalIntrinsicTransferConstant * min 1
        ((gaussianMaximumMean A / Real.sqrt (dimensionLog p)) *
          conditionalPolynomialThresholdRate n p B T q) := by
  let i : Fin n := ⟨0, by omega⟩
  let g := gaussianMaximumMean A
  let L := dimensionLog p
  let v := truncationVarianceBudget B T q
  let k := Real.sqrt (2 / Real.pi)
  let a := intrinsicUniversalConstant * (8 * Real.sqrt (4 / 3 : ℝ))
  let b := 16 * envelopeMaximumConstant
  let c := 16 * Real.sqrt 10 + 20 * Real.sqrt 2 + 24 / k
  let s := Real.sqrt L
  let t := (g / s) * (T / Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ) * Real.sqrt (dimensionLog n))
  let z := (g / s) * (L * Real.sqrt v)
  let w := (g / s) * polynomialEnvelopeV n p B q
  have hk : 0 < k := by dsimp [k]; positivity
  have hg : 0 ≤ g := gaussianMaximumMean_nonneg A
  have hglow : k ≤ g := sqrt_two_div_pi_le_gaussianMaximumMean hp A hunit
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hs : 0 < s := Real.sqrt_pos.mpr hL
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hL1
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL.le
  have hv0 : 0 ≤ v := (h i).varianceBudget_nonneg
  have hT : 0 ≤ T := (h i).threshold_pos.le
  have hc0 : 0 ≤ g / s := div_nonneg hg hs.le
  have ha : 0 ≤ a := by dsimp [a]; exact mul_nonneg intrinsicUniversalConstant_pos.le (by positivity)
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (zero_le_one.trans one_le_envelopeMaximumConstant)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw : 0 ≤ w := by dsimp [w, polynomialEnvelopeV]; positivity
  have hsum : (g / s) * conditionalPolynomialThresholdRate n p B T q = t + z + w := by
    dsimp [conditionalPolynomialThresholdRate, t, z, w, L, v]
    ring
  have hzEq : z = g * s * Real.sqrt v := by
    dsimp [z]
    calc
      _ = (g * (L * Real.sqrt v)) / s := by ring
      _ = _ := by
        apply (div_eq_iff hs.ne').mpr
        nlinarith only [congrArg (fun x => g * Real.sqrt v * x) hs2]
  have hzlow : k * Real.sqrt v ≤ z := by
    rw [hzEq]
    have h₁ := mul_le_mul_of_nonneg_right hglow (Real.sqrt_nonneg v)
    have h₂ := mul_le_mul_of_nonneg_right hs1 (mul_nonneg hg (Real.sqrt_nonneg v))
    nlinarith only [h₁, h₂]
  have hcoef : 24 / k ≤ conditionalIntrinsicTransferConstant := by
    change 24 / k ≤ 1 + a + b + 16 * Real.sqrt 10 + 20 * Real.sqrt 2 + 24 / k
    have hpos : 0 ≤ 1 + a + b + 16 * Real.sqrt 10 + 20 * Real.sqrt 2 := by positivity
    linarith
  have hraw : rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
        conditionalIntrinsicTransferConstant * (t + z + w) := by
    by_cases hv : v ≤ 1 / 4
    · have hcut := conditionalPolynomial_intrinsic_raw μ h hp hn hB A hA hunit hv
      have hshift := observed_exceptional_shift_maximum_le μ h hp hn
      change s * (∫ x, ‖conditionalNormalizedShift μ T
        (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) ≤
        (2 * envelopeMaximumConstant) * (L * Real.sqrt v + polynomialEnvelopeV n p B q) at hshift
      have hshift' : 8 * g * (∫ x, ‖conditionalNormalizedShift μ T
          (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) ≤ b * (z + w) := by
        have hh := mul_le_mul_of_nonneg_left hshift (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hc0)
        convert hh using 1 <;> dsimp [b, z, w] <;> field_simp [hs.ne'] <;> ring
      have hbounded : conditionalIntrinsicBoundedCost n p T g = a * t := by
        dsimp [conditionalIntrinsicBoundedCost, a, t]
        rw [rpow_three_halves_eq_mul_sqrt hL]
        change _ = intrinsicUniversalConstant * (8 * Real.sqrt (4 / 3 : ℝ)) *
          ((g / s) * (T / Real.sqrt (n : ℝ) * (L * s) * Real.sqrt (dimensionLog n)))
        dsimp only [L, s]
        field_simp [hs.ne']
        ring
      have hgauss₁ : 16 * g * s * Real.sqrt (10 * v) = (16 * Real.sqrt 10) * z := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10), hzEq]
        ring
      have hgauss₂ : 20 * g * Real.sqrt (2 * v * L) = (20 * Real.sqrt 2) * z := by
        rw [Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv0),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hzEq]
        dsimp only [s]
        ring
      have hvs : v ≤ Real.sqrt v := by
        nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg v]
      have hvariance : 12 * v ≤ (24 / k) * z := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hk).mpr
        have hh := mul_le_mul_of_nonneg_left hvs (show 0 ≤ 12 * k by positivity)
        nlinarith only [hh, hzlow, hz]
      rw [hbounded, hgauss₁, hgauss₂] at hcut
      have hwgt := weighted_threshold_sum_le ha hb hc ht hz hw
      change rectangleDistance (Measure.pi μ)
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
          a * t + 8 * g * (∫ x, ‖conditionalNormalizedShift μ T
            (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) +
          (16 * Real.sqrt 10) * z + (20 * Real.sqrt 2) * z + 12 * v at hcut
      calc
        _ ≤ a * t + b * (z + w) + c * z := by
          dsimp only [c]
          linarith only [hcut, hshift', hvariance]
        _ ≤ (1 + a + b + c) * (t + z + w) := hwgt
        _ = _ := by dsimp [conditionalIntrinsicTransferConstant, a, b, c, k]; ring
    · have hsv : (1 / 2 : ℝ) ≤ Real.sqrt v := by
        nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg v]
      have hlow : 1 ≤ (24 / k) * z := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hk).mpr
        have hh := mul_le_mul_of_nonneg_left hsv hk.le
        nlinarith only [hzlow, hh, hk.le]
      exact (rectangleDistance_le_one _ _ _).trans (hlow.trans
        (mul_le_mul hcoef (by linarith : z ≤ t + z + w) hz
          (zero_le_one.trans one_le_conditionalIntrinsicTransferConstant)))
  have hcap := intrinsic_capped_of_le_one_and_mul (add_nonneg (add_nonneg ht hz) hw)
    (rectangleDistance_le_one (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A) hraw
  rw [max_eq_right one_le_conditionalIntrinsicTransferConstant] at hcap
  change _ ≤ conditionalIntrinsicTransferConstant * min 1
    ((g / s) * conditionalPolynomialThresholdRate n p B T q)
  rw [hsum]
  exact hcap

end RectangleCLTArxivV1
