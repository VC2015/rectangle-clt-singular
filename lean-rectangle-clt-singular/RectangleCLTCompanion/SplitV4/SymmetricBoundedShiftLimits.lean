import RectangleCLTCompanion.SplitV4.SymmetricBoundedParameters
import RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster

/-! Actual first-order mean-shift calibration for the bounded symmetric lower family. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def boundedShiftScale (n m : ℕ) : ℝ := Real.log (m : ℝ) / (2 * Real.sqrt n)
def boundedLowerScale (n m : ℕ) : ℝ := Real.log (m : ℝ) ^ (3 / 2 : ℝ) / (2 * Real.sqrt n)

theorem lower_rpow_three_halves {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]

theorem sqrt_activation_extreme_scale {ell N : ℝ} (hL : 0 < ell) (hN : 0 < N) :
    Real.sqrt (ell / (2 * N)) * Real.sqrt (2 * ell) = ell / Real.sqrt N := by
  have hA0 : 0 ≤ Real.sqrt (ell / (2 * N)) * Real.sqrt (2 * ell) := by positivity
  have hB0 : 0 ≤ ell / Real.sqrt N := by positivity
  have hA2 : (Real.sqrt (ell / (2 * N)) * Real.sqrt (2 * ell)) ^ 2 = ell ^ 2 / N := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hB2 : (ell / Real.sqrt N) ^ 2 = ell ^ 2 / N := by rw [div_pow, Real.sq_sqrt hN.le]
  nlinarith only [hA0, hB0, hA2, hB2]

theorem gaussianShift_ratio_identity {s ell N M : ℝ} (hs : s ≠ 0) (hL : 0 < ell) (hN : 0 < N) :
    ((Real.sqrt (ell / (2 * N)) / s) * M) / (ell / (2 * Real.sqrt N)) =
      (2 / s) * (M / Real.sqrt (2 * ell)) := by
  have hprod := sqrt_activation_extreme_scale hL hN
  have hw : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hq : Real.sqrt (2 * ell) ≠ 0 := (Real.sqrt_pos.mpr (show 0 < 2 * ell by positivity)).ne'
  have hden : ell / (2 * Real.sqrt N) ≠ 0 := div_ne_zero hL.ne' (mul_ne_zero (by norm_num) hw)
  have heq : ((Real.sqrt (ell / (2 * N)) / s) * M) / (ell / (2 * Real.sqrt N)) =
      ((2 / s) * M) / Real.sqrt (2 * ell) := by
    apply (div_eq_div_iff hden hq).mpr
    calc
      _ = (Real.sqrt (ell / (2 * N)) * Real.sqrt (2 * ell)) * (M / s) := by ring
      _ = (ell / Real.sqrt N) * (M / s) := by rw [hprod]
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; norm_num <;> ring
  exact heq.trans (by ring)

theorem observationShift_ratio_identity {s ell w Q : ℝ} (hs : s ≠ 0) (hL : ell ≠ 0) (hw : w ≠ 0) :
    (Q / (ell / 2)) / s = ((1 / (s * w)) * Q) / (ell / (2 * w)) := by
  field_simp
  ring

theorem tendsto_boundedFamily_observationShift_mean_ratio {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyObservationShift (boundedFamilyParameters n (m n)) z
      ∂familyRestArrayLaw (boundedFamilyParameters n (m n)) n (m n)) / boundedShiftScale n (m n)) atTop (𝓝 1) := by
  let P := fun n => boundedFamilyParameters n (m n)
  have hcount := boundedFamilyParameters_eventually_count hm hmTop hsmall
  have hπ : ∀ᶠ n : ℕ in atTop, (P n).pi = 1 := Eventually.of_forall (fun n => boundedFamilyParameters_pi n (m n))
  have hQ := tendsto_familyUnmasked_maximum_mean_ratio P m hmTop hcount hπ
  have hs := tendsto_boundedFamily_scale hm hmTop hsmall
  have hh := hQ.div hs (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [hcount, eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  dsimp only [P, Pi.div_apply]
  rw [familyObservationShift_integral, boundedFamilyParameters_amplitude, hn]
  exact observationShift_ratio_identity (boundedFamilyParameters n (m n)).scale_pos.ne' hL.ne' (Real.sqrt_pos.mpr hnp).ne'

theorem tendsto_boundedFamily_gaussianShift_mean_ratio {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyGaussianShift (boundedFamilyParameters n (m n)) z ∂standardGaussian (m n)) /
      boundedShiftScale n (m n)) atTop (𝓝 2) := by
  have hs := tendsto_boundedFamily_scale hm hmTop hsmall
  have hG := tendsto_gaussianMaximumMean_div_sqrt_log.comp hmTop
  have hh := ((tendsto_const_nhds (x := (2 : ℝ))).div hs (by norm_num : (1 : ℝ) ≠ 0)).mul hG
  norm_num only [div_one, mul_one] at hh
  apply hh.congr'
  filter_upwards [boundedFamilyParameters_eventually_theta hm hmTop hsmall, eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  rw [familyGaussianShift_integral, boundedFamilyParameters_variance, hn]
  exact (gaussianShift_ratio_identity (boundedFamilyParameters n (m n)).scale_pos.ne' hL hnp).symm


theorem tendsto_boundedFamily_shiftMean_difference_ratio {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftMeanDifference (boundedFamilyParameters n (m n)) n (m n) /
      boundedShiftScale n (m n)) atTop (𝓝 1) := by
  have hh := (tendsto_boundedFamily_gaussianShift_mean_ratio hm hmTop hsmall).sub
    (tendsto_boundedFamily_observationShift_mean_ratio hm hmTop hsmall)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num] at hh
  simpa only [familyShiftMeanDifference, sub_div] using hh

theorem boundedLowerScale_eq_shift_mul_sqrt {n m : ℕ} (hL : 0 < Real.log (m : ℝ)) :
    boundedLowerScale n m = boundedShiftScale n m * Real.sqrt (Real.log (m : ℝ)) := by
  unfold boundedLowerScale boundedShiftScale
  rw [lower_rpow_three_halves hL]
  ring

theorem tendsto_boundedFamily_leading_comparison_ratio {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => normalMaximumDensity (m n) (normalMaxThreshold (m n)) *
      familyShiftMeanDifference (boundedFamilyParameters n (m n)) n (m n) / boundedLowerScale n (m n))
      atTop (𝓝 (Real.sqrt 2 * Real.exp (-1))) := by
  have hD := tendsto_normalMaximumDensity_at_threshold_div_sqrt_log.comp hmTop
  have hM := tendsto_boundedFamily_shiftMean_difference_ratio hm hmTop hsmall
  have hh := (hD.mul hM).const_mul (Real.sqrt 2)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  dsimp only [Function.comp_apply]
  rw [boundedLowerScale_eq_shift_mul_sqrt hL, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold boundedShiftScale
  field_simp [(Real.sqrt_pos.mpr hnp).ne', (Real.sqrt_pos.mpr hL).ne', hL.ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

end
end RectangleCLT.Companion.SplitV4
