import RectangleCLTCompanion.SplitV4.Printed.PolarPlane
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes

/-! The exact rank-two radial Gaussian tail, obtained by integrating the
normal density in polar coordinates, as in the printed radius argument. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem measurable_planeRadius : Measurable planeRadius := by
  unfold planeRadius
  fun_prop

theorem normalPair_density_radial (z : ℝ × ℝ) :
    gaussianPDFReal 0 1 z.1 * gaussianPDFReal 0 1 z.2 =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * Real.exp (-(planeRadius z ^ 2) / 2) := by
  have hs : planeRadius z ^ 2 = z.1 ^ 2 + z.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hs]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 1
  · ring
  · congr 1
    ring

theorem normalPair_radius_tail {s : ℝ} (hs : 0 ≤ s) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {z : ℝ × ℝ | s < planeRadius z} = Real.exp (-(s ^ 2) / 2) := by
  let c := (Real.sqrt (2 * Real.pi))⁻¹ ^ 2
  let f : ℝ → ℝ := (Ioi s).indicator (fun r => c * Real.exp (-(r ^ 2) / 2))
  have hS : MeasurableSet {z : ℝ × ℝ | s < planeRadius z} :=
    measurableSet_lt measurable_const measurable_planeRadius
  have hrad : (∫ r in Ioi (0 : ℝ), r * f r) =
      c * ∫ r in Ioi s, r * Real.exp (-(r ^ 2) / 2) := by
    have he : (fun r : ℝ => r * f r) =
        (Ioi s).indicator (fun r => c * (r * Real.exp (-(r ^ 2) / 2))) := by
      funext r
      by_cases hr : s < r <;> simp [f, hr] <;> ring
    rw [he, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi s ∩ Ioi (0 : ℝ) = Ioi s :=
      inter_eq_left.mpr (fun r hr => lt_of_le_of_lt hs hr)
    rw [hset, integral_const_mul]
  calc
    _ = ∫ z : ℝ × ℝ, ({z : ℝ × ℝ | s < planeRadius z}).indicator
        (fun _ => (1 : ℝ)) z ∂(gaussianReal 0 1).prod (gaussianReal 0 1) :=
      (integral_indicator_one hS).symm
    _ = ∫ z : ℝ × ℝ, f (planeRadius z) := by
      rw [normalPair_integral_density]
      apply integral_congr_ae
      filter_upwards with z
      rw [normalPair_density_radial]
      change c * Real.exp (-(planeRadius z ^ 2) / 2) *
        (if s < planeRadius z then 1 else 0) =
          if s < planeRadius z then c * Real.exp (-(planeRadius z ^ 2) / 2) else 0
      split_ifs <;> simp
    _ = (2 * Real.pi) * (c * Real.exp (-(s ^ 2) / 2)) := by
      rw [integral_plane_radial, hrad, integral_radial_gaussian_tail]
    _ = _ := by
      have hpi : 2 * Real.pi ≠ 0 := by positivity
      dsimp only [c]
      rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      field_simp

end
end RectangleCLT.Companion.SplitV4.Printed
