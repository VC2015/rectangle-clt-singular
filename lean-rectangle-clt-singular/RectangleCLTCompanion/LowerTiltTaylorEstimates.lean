import RectangleCLTCompanion.LowerTiltTaylor

/-! Derivative-level Taylor bounds needed to solve the actual tilt
equation. The dependence on the envelope parameter is explicit. -/

open Set

namespace RectangleCLT.Companion

noncomputable section

def lowerTiltFourthBound (B T : ℝ) : ℝ := 4 * B ^ 2 * Real.exp (2 * B * T)

theorem lowerTiltThird_local_difference {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |lowerTiltThird B T - (B - B⁻¹)| ≤ lowerTiltFourthBound B T * T := by
  have hBp : 0 < B := by linarith
  have hh := lower_meanvalue_bound hT (hasDerivAt_lowerTiltThird B)
    (fun u hu => lowerTiltFourthCumulant_local_bound hB hT hu)
  simpa only [lowerTiltThird_zero hBp.ne'] using hh

theorem lowerTiltFourthBound_mono {B T u : ℝ} (hB : 0 ≤ B) (hu : u ≤ T) :
    lowerTiltFourthBound B u ≤ lowerTiltFourthBound B T := by
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (by positivity)))
  positivity

theorem lowerTiltVariance_linear {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |lowerTiltVariance B T - 1 - (B - B⁻¹) * T| ≤ lowerTiltFourthBound B T * T ^ 2 := by
  have hBp : 0 < B := by linarith
  have hM : 0 ≤ lowerTiltFourthBound B T := by unfold lowerTiltFourthBound; positivity
  have hd (u : ℝ) : HasDerivAt
      (fun u => lowerTiltVariance B u - 1 - (B - B⁻¹) * u)
      (lowerTiltThird B u - (B - B⁻¹)) u := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_lowerTiltVariance B u).sub_const 1).sub
        ((hasDerivAt_id u).const_mul (B - B⁻¹))
  have hh := lower_meanvalue_bound hT hd (fun u hu =>
    (lowerTiltThird_local_difference hB hu.1).trans
      (mul_le_mul (lowerTiltFourthBound_mono hBp.le hu.2) hu.2 hu.1 hM))
  simp only [lowerTiltVariance_zero hBp.ne', sub_self, mul_zero, sub_zero] at hh
  convert hh using 1 <;> ring

theorem lowerTiltMean_quadratic {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |lowerTiltMean B T - T - (B - B⁻¹) * T ^ 2 / 2| ≤ lowerTiltFourthBound B T * T ^ 3 := by
  have hBp : 0 < B := by linarith
  have hM : 0 ≤ lowerTiltFourthBound B T := by unfold lowerTiltFourthBound; positivity
  have hd (u : ℝ) : HasDerivAt
      (fun u => lowerTiltMean B u - u - (B - B⁻¹) * u ^ 2 / 2)
      (lowerTiltVariance B u - 1 - (B - B⁻¹) * u) u := by
    have hh := ((hasDerivAt_lowerTiltMean B u).sub (hasDerivAt_id u)).sub
      (((hasDerivAt_id u).pow 2).const_mul (B - B⁻¹) |>.div_const 2)
    simp only [id_eq] at hh
    convert hh using 1 <;> ring
  have hh := lower_meanvalue_bound hT hd (fun u hu =>
    (lowerTiltVariance_linear hB hu.1).trans
      (mul_le_mul (lowerTiltFourthBound_mono hBp.le hu.2)
        (pow_le_pow_left₀ hu.1 hu.2 2) (sq_nonneg u) hM))
  simp only [lowerTiltMean_zero hBp.ne', sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, sub_self] at hh
  convert hh using 1 <;> ring

theorem lowerTiltVariance_sub_one {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |lowerTiltVariance B T - 1| ≤ (2 * B * Real.exp (2 * B * T)) * T := by
  have hBp : 0 < B := by linarith
  have hh := lower_meanvalue_bound hT (hasDerivAt_lowerTiltVariance B) (fun u hu =>
    (lowerTiltThird_abs_le hB u).trans (mul_le_mul_of_nonneg_left
      (((lowerTiltVariance_exp_bounds hB u).2).trans (by
        rw [abs_of_nonneg hu.1]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 (by positivity))))
      (by positivity)))
  simpa only [lowerTiltVariance_zero hBp.ne'] using hh

theorem lowerTiltMean_sub_self {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |lowerTiltMean B T - T| ≤ (2 * B * Real.exp (2 * B * T)) * T ^ 2 := by
  have hBp : 0 < B := by linarith
  have hd (u : ℝ) : HasDerivAt (fun u => lowerTiltMean B u - u)
      (lowerTiltVariance B u - 1) u :=
    (hasDerivAt_lowerTiltMean B u).sub (hasDerivAt_id u)
  have hh := lower_meanvalue_bound hT hd (fun u hu =>
    (lowerTiltVariance_sub_one hB hu.1).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 (by positivity))) (by positivity))
      hu.2 hu.1 (by positivity)))
  simp only [lowerTiltMean_zero hBp.ne', sub_zero] at hh
  convert hh using 1 <;> ring

end

end RectangleCLT.Companion
