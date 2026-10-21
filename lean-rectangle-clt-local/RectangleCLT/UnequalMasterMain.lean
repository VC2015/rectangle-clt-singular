import RectangleCLT.UnequalMasterSecondBounds
import RectangleCLT.UnequalMasterIntegralBounds
import RectangleCLT.UnequalMasterGap

/-! The complete unequal-covariance master bound. Every analytic branch
is supplied by actual common-point derivative estimates and the actual
fourth-order local suprema. The public theorem assumes no analytic cap. -/

open MeasureTheory Set

universe u

namespace RectangleCLT

noncomputable section

def unequalMasterConstant : ℝ :=
  1 + unequalSecondIntegralConstant + unequalThirdIntegralConstant +
    6 * unequalFourthIntegralConstant + (8 * Real.exp 4 + 4)

theorem unequalMasterConstant_ge_one : 1 ≤ unequalMasterConstant := by
  unfold unequalMasterConstant
  have h2 := unequalSecondIntegralConstant_pos
  have h3 := unequalThirdIntegralConstant_pos
  have h4 := unequalFourthIntegralConstant_pos
  have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
  linarith

/-- Lemma 10 with precisely its two positive endpoint gaps, unit
diagonals, bounded independent observations, all covariance alternatives,
and zero-denominator omission conventions. -/
theorem unequalMasterEstimate : UnequalMasterEstimate.{u} unequalMasterConstant := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hdiag hcs R h hband
  let Q := A * A.transpose
  let L := dimensionLog p
  let c := pairGap Q
  let cstar := min (pairGap (covariance μ (sumVector ξ))) c
  let b := fullCovarianceScale Q
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q
  let β₂ := masterSecondCoefficient L b c h
  let β₃ := masterThirdCoefficient L b c (a3 Q) h
  let β₄ := masterFourthCoefficient L b c (a3 Q) (a4 Q) h
  let T₂ := Δ * β₂
  let T₃ := gamma3 μ ξ * β₃
  let T₄ := gamma4 μ ξ * β₄
  let T₀ := h / cstar
  have hcS : 0 < pairGap (covariance μ (sumVector ξ)) :=
    lt_of_lt_of_le hcs (min_le_left _ _)
  have hc : 0 < c := lt_of_lt_of_le hcs (min_le_right _ _)
  have hδ : 0 < δ := hdata.delta_pos hp hunit
  have hh : 0 < h := by linarith only [hband, hδ]
  have hδh : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hT₂ : 0 ≤ T₂ := mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
    (masterSecondCoefficient_nonneg hc hh)
  have hT₃ : 0 ≤ T₃ := mul_nonneg (gamma3_nonneg μ ξ)
    (masterThirdCoefficient_nonneg hL hc hh)
  have hT₄ : 0 ≤ T₄ := mul_nonneg (gamma4_nonneg μ ξ)
    (masterFourthCoefficient_nonneg hL hc hh)
  have hT₀ : 0 ≤ T₀ := div_nonneg hh.le hcs.le
  change rectangleError μ (sumVector ξ) A R ≤
    unequalMasterConstant * (Real.sqrt L * (T₂ + T₃ + T₄ + T₀))
  apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
  intro lo hi
  let s := FaceSmoother.closedBox lo hi h hh
  let B₂ := unequalSecondIntegralConstant * Real.sqrt L * β₂
  have hsecond (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
        (thinningProbability t) (thinningScale t) ≤ B₂ * t ^ (-(1 / 2 : ℝ)) := by
    have hb := s.selectorSecondAbsoluteSum_time_le_unequal_min hdata hp hunit A hdiag
      hc hband ht.1 ht.2
    rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
    convert hb using 1 <;> dsimp [B₂, β₂, b, c, Q, L, s, FaceSmoother.closedBox] <;> ring
  have hgap := s.interpolation_smoother_gap_le_unequal_integrals μ ξ hdata A B₂ hsecond
  have h3 := s.integral_time_mul_sharpThirdAverage_le_unequal_min hdata hp hunit A hdiag hc hband
  have h4 := s.integral_sharpFourthAverage_le_unequal_min hdata hp hunit A hdiag hc hband
  have hI := add_le_add
    (add_le_add_left
      (mul_le_mul_of_nonneg_left h3 (div_nonneg (gamma3_nonneg μ ξ) (by norm_num : (0 : ℝ) ≤ 3)))
      (Δ * B₂))
    (mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (gamma4_nonneg μ ξ)))
  have herr := hdata.closedBox_error_le_unequal_smoother_gap hp hunit A hdiag hcS hc
    lo hi hh hδh
  have hraw := herr.trans (add_le_add_right (hgap.trans hI) _)
  have hraw' : rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
      Real.sqrt L * (unequalSecondIntegralConstant * T₂ +
        (unequalThirdIntegralConstant / 3) * T₃ +
        (6 * unequalFourthIntegralConstant) * T₄ + (8 * Real.exp 4 + 4) * T₀) := by
    convert hraw using 1 <;>
      dsimp [T₂, T₃, T₄, T₀, B₂, β₂, β₃, β₄, b, c, cstar, Q, L,
        Δ, s, FaceSmoother.closedBox] <;> ring
  have hC2 : unequalSecondIntegralConstant ≤ unequalMasterConstant := by
    unfold unequalMasterConstant
    have h3 := unequalThirdIntegralConstant_pos
    have h4 := unequalFourthIntegralConstant_pos
    have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
    linarith
  have hC3 : unequalThirdIntegralConstant / 3 ≤ unequalMasterConstant := by
    unfold unequalMasterConstant
    have h2 := unequalSecondIntegralConstant_pos
    have h3 := unequalThirdIntegralConstant_pos
    have h4 := unequalFourthIntegralConstant_pos
    have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
    linarith
  have hC4 : 6 * unequalFourthIntegralConstant ≤ unequalMasterConstant := by
    unfold unequalMasterConstant
    have h2 := unequalSecondIntegralConstant_pos
    have h3 := unequalThirdIntegralConstant_pos
    have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
    linarith
  have hC0 : 8 * Real.exp 4 + 4 ≤ unequalMasterConstant := by
    unfold unequalMasterConstant
    have h2 := unequalSecondIntegralConstant_pos
    have h3 := unequalThirdIntegralConstant_pos
    have h4 := unequalFourthIntegralConstant_pos
    linarith
  apply hraw'.trans
  have hlinear := add_le_add
    (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hC2 hT₂)
        (mul_le_mul_of_nonneg_right hC3 hT₃))
      (mul_le_mul_of_nonneg_right hC4 hT₄))
    (mul_le_mul_of_nonneg_right hC0 hT₀)
  exact (mul_le_mul_of_nonneg_left hlinear (Real.sqrt_nonneg L)).trans_eq (by ring)

theorem unequalMasterEstimateExists :
    ∃ C : ℝ, 1 ≤ C ∧ UnequalMasterEstimate.{u} C :=
  ⟨unequalMasterConstant, unequalMasterConstant_ge_one, unequalMasterEstimate⟩

end

end RectangleCLT
