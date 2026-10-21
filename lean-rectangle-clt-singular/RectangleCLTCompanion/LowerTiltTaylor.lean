import RectangleCLTCompanion.LowerCumulantBounds
import RectangleCLTCompanion.LowerTaylorChain

/-! Cubic cumulant approximation with explicit dependence on B, derived
from the actual Esscher moments and their derivative chain. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

theorem lowerTwoPointLaw_integrableExpSet (B : ℝ) :
    integrableExpSet id (lowerTwoPointLaw B) = univ :=
  eq_univ_of_forall (fun _ => integrable_lowerTwoPointLaw B _)

theorem hasDerivAt_lowerTwoPointLaw_cgf (B t : ℝ) :
    HasDerivAt (cgf id (lowerTwoPointLaw B)) (lowerTiltMean B t) t := by
  have ht : t ∈ interior (integrableExpSet id (lowerTwoPointLaw B)) := by
    rw [lowerTwoPointLaw_integrableExpSet, interior_univ]
    exact mem_univ _
  have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
  have hm : lowerTiltMean B t = deriv (cgf id (lowerTwoPointLaw B)) t := by
    rw [← lowerTwoPointTilt_mean]
    exact integral_tilted_mul_self ht
  rw [← hm] at hd
  exact hd

theorem lowerTiltFourthCumulant_local_bound {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    |lowerTiltFourthCumulant B u| ≤ 4 * B ^ 2 * Real.exp (2 * B * T) := by
  have hBp : 0 < B := by linarith
  have hv := (lowerTiltVariance_exp_bounds hB u).2
  rw [abs_of_nonneg hu.1] at hv
  have hmon : Real.exp (2 * B * u) ≤ Real.exp (2 * B * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 (by positivity))
  exact (lowerTiltFourthCumulant_abs_le hB u).trans
    (mul_le_mul_of_nonneg_left (hv.trans hmon) (by positivity))

/-- The cubic coefficient is exactly `(B-B⁻¹)/6`; the remainder is
bounded by an absolute exponential factor times `B² T⁴`. -/
theorem lowerTwoPointLaw_cgf_cubic {B T : ℝ} (hB : 1 ≤ B) (hT : 0 ≤ T) :
    |cgf id (lowerTwoPointLaw B) T - T ^ 2 / 2 - (B - B⁻¹) * T ^ 3 / 6| ≤
      (4 * B ^ 2 * Real.exp (2 * B * T)) * T ^ 4 := by
  have hBp : 0 < B := by linarith
  have hh := lower_taylor_chain_cubic hT
    (by positivity : 0 ≤ 4 * B ^ 2 * Real.exp (2 * B * T))
    (hasDerivAt_lowerTwoPointLaw_cgf B) (hasDerivAt_lowerTiltMean B)
    (hasDerivAt_lowerTiltVariance B) (hasDerivAt_lowerTiltThird B)
    (fun u hu => lowerTiltFourthCumulant_local_bound hB hT hu)
  simpa only [cgf_zero, lowerTiltMean_zero hBp.ne', lowerTiltVariance_zero hBp.ne',
    lowerTiltThird_zero hBp.ne', mul_zero, zero_mul, sub_zero, one_mul] using hh

end

end RectangleCLT.Companion
