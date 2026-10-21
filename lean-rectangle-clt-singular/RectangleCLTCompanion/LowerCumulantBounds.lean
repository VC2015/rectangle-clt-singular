import RectangleCLTCompanion.LowerScalarTilt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Quantitative cumulant control for the actual tilted two-point law.
These estimates are uniform in the endpoint parameter B. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

theorem lowerTwoPointTilt_zero (B : ℝ) : lowerTwoPointTilt B 0 = lowerTwoPointLaw B := by
  simp [lowerTwoPointTilt]

theorem lowerTiltMean_zero {B : ℝ} (hB : B ≠ 0) : lowerTiltMean B 0 = 0 := by
  rw [← lowerTwoPointTilt_mean, lowerTwoPointTilt_zero]
  exact lowerTwoPointLaw_centered hB

theorem lowerTiltVariance_zero {B : ℝ} (hB : B ≠ 0) : lowerTiltVariance B 0 = 1 := by
  rw [← lowerTwoPointTilt_variance, lowerTiltMean_zero hB, lowerTwoPointTilt_zero]
  simpa only [sub_zero] using lowerTwoPointLaw_second hB

theorem lowerTiltThird_zero {B : ℝ} (hB : B ≠ 0) :
    lowerTiltThird B 0 = B - B⁻¹ := by
  rw [← lowerTwoPointTilt_third, lowerTiltMean_zero hB, lowerTwoPointTilt_zero]
  simpa only [sub_zero] using lowerTwoPointLaw_third hB

theorem lowerTiltThird_abs_le {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    |lowerTiltThird B t| ≤ 2 * B * lowerTiltVariance B t := by
  have hBp : 0 < B := by linarith
  have hv := (lowerTiltVariance_pos hBp t).le
  have hd : 0 ≤ B + B⁻¹ := by positivity
  have hd2 : B + B⁻¹ ≤ 2 * B := by
    linarith [(inv_le_one_of_one_le₀ hB).trans hB]
  have hq0 := (lowerTiltProbability_pos B t).le
  have hq1 := lowerTiltProbability_le_one B t
  have hqabs : |1 - 2 * lowerTiltProbability B t| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hfactor : lowerTiltThird B t =
      ((B + B⁻¹) * lowerTiltVariance B t) * (1 - 2 * lowerTiltProbability B t) := by
    unfold lowerTiltThird lowerTiltVariance
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg hd hv)]
  calc
    _ ≤ ((B + B⁻¹) * lowerTiltVariance B t) * 1 :=
      mul_le_mul_of_nonneg_left hqabs (mul_nonneg hd hv)
    _ ≤ 2 * B * lowerTiltVariance B t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hd2 hv

theorem lowerTilt_logVariance_lipschitz {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    |Real.log (lowerTiltVariance B t)| ≤ 2 * B * |t| := by
  have hBp : 0 < B := by linarith
  have hd (u : ℝ) : HasDerivAt (fun u => Real.log (lowerTiltVariance B u))
      (lowerTiltThird B u / lowerTiltVariance B u) u :=
    (hasDerivAt_lowerTiltVariance B u).log (lowerTiltVariance_pos hBp u).ne'
  have hbound (u : ℝ) : ‖lowerTiltThird B u / lowerTiltVariance B u‖ ≤ 2 * B := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (lowerTiltVariance_pos hBp u)]
    apply (div_le_iff₀ (lowerTiltVariance_pos hBp u)).mpr
    exact lowerTiltThird_abs_le hB u
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ (Set.univ : Set ℝ)) => (hd u).hasDerivWithinAt)
    (fun u _ => hbound u) convex_univ (mem_univ (0 : ℝ)) (mem_univ t)
  simpa only [lowerTiltVariance_zero hBp.ne', Real.log_one, sub_zero, Real.norm_eq_abs] using hh

theorem lowerTiltVariance_exp_bounds {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    Real.exp (- (2 * B * |t|)) ≤ lowerTiltVariance B t ∧
      lowerTiltVariance B t ≤ Real.exp (2 * B * |t|) := by
  have hBp : 0 < B := by linarith
  have hh := abs_le.mp (lowerTilt_logVariance_lipschitz hB t)
  constructor
  · simpa only [Real.exp_log (lowerTiltVariance_pos hBp t)] using Real.exp_le_exp.mpr hh.1
  · simpa only [Real.exp_log (lowerTiltVariance_pos hBp t)] using Real.exp_le_exp.mpr hh.2

theorem lowerTiltFourthCumulant_abs_le {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    |lowerTiltFourthCumulant B t| ≤ 4 * B ^ 2 * lowerTiltVariance B t := by
  have hBp : 0 < B := by linarith
  have hq0 := (lowerTiltProbability_pos B t).le
  have hq1 := lowerTiltProbability_le_one B t
  have hqprod0 : 0 ≤ lowerTiltProbability B t * (1 - lowerTiltProbability B t) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hqprod1 : lowerTiltProbability B t * (1 - lowerTiltProbability B t) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (lowerTiltProbability B t - 1 / 2)]
  have hfabs : |1 - 6 * lowerTiltProbability B t * (1 - lowerTiltProbability B t)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hd0 : 0 ≤ B + B⁻¹ := by positivity
  have hd2 : (B + B⁻¹) ^ 2 ≤ 4 * B ^ 2 := by
    have hh := (inv_le_one_of_one_le₀ hB).trans hB
    nlinarith [sq_nonneg (B - B⁻¹)]
  have hv := (lowerTiltVariance_pos hBp t).le
  have hfactor : lowerTiltFourthCumulant B t =
      ((B + B⁻¹) ^ 2 * lowerTiltVariance B t) *
        (1 - 6 * lowerTiltProbability B t * (1 - lowerTiltProbability B t)) := by
    unfold lowerTiltFourthCumulant lowerTiltVariance
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hv)]
  calc
    _ ≤ ((B + B⁻¹) ^ 2 * lowerTiltVariance B t) * 1 :=
      mul_le_mul_of_nonneg_left hfabs (mul_nonneg (sq_nonneg _) hv)
    _ ≤ 4 * B ^ 2 * lowerTiltVariance B t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hd2 hv

end

end RectangleCLT.Companion
