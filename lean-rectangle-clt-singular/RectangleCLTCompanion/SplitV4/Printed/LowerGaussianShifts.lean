import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile
import RectangleCLTCompanion.SplitV4.SymmetricBoundedMoments
import RectangleCLTCompanion.SplitV4.RareFamilyShifts

/-! Actual Gaussian shifts using the printed uniform-integrability mean
argument and the integrated union-tail second-moment bound. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem integral_finiteGaussianMaximum_sq_printed {m : ℕ} (hm : 1≤m) [NeZero m] :
    (∫z : Vector m,finiteMaximum z^2 ∂standardGaussian m)≤4*dimensionLog m := by
  apply (integral_mono (integrable_finiteGaussianMaximum_sq_direct m)
    (integrable_gaussian_norm_sq_direct m) (fun z => ?_)).trans
      (integral_gaussian_norm_sq_le_four_dimensionLog hm)
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_finiteMaximum_le_norm z) 2
  simpa only [sq_abs] using hh

theorem familyGaussianShift_sq_integral_le_printed (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    (∫z,familyGaussianShift P z^2 ∂standardGaussian m)≤
      (Real.sqrt P.variance/P.scale)^2*(Real.exp (11/2)*dimensionLog m) := by
  simp_rw [familyGaussianShift,mul_pow]
  rw [integral_const_mul]
  have hm : 1≤m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hc : 4≤Real.exp (11/2:ℝ) := by linarith [Real.add_one_le_exp (11/2:ℝ)]
  have hdim : 0≤dimensionLog m := zero_le_one.trans (log_exp_mul_nat_ge_one hm)
  exact mul_le_mul_of_nonneg_left
    ((integral_finiteGaussianMaximum_sq_printed hm).trans (mul_le_mul_of_nonneg_right hc hdim)) (sq_nonneg _)

theorem tendsto_boundedFamily_gaussianShift_mean_ratio_printed_ui {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyGaussianShift (boundedFamilyParameters n (m n)) z ∂standardGaussian (m n)) /
      boundedShiftScale n (m n)) atTop (𝓝 2) := by
  have hs := tendsto_boundedFamily_scale hm hmTop hsmall
  have hG := tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability.comp hmTop
  have hh := ((tendsto_const_nhds (x := (2 : ℝ))).div hs (by norm_num : (1 : ℝ) ≠ 0)).mul hG
  norm_num only [div_one, mul_one] at hh
  apply hh.congr'
  filter_upwards [boundedFamilyParameters_eventually_theta hm hmTop hsmall, eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  rw [familyGaussianShift_integral, boundedFamilyParameters_variance, hn]
  exact (gaussianShift_ratio_identity (boundedFamilyParameters n (m n)).scale_pos.ne' hL hnp).symm


theorem tendsto_boundedFamily_shiftMean_difference_ratio_printed_ui {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftMeanDifference (boundedFamilyParameters n (m n)) n (m n) /
      boundedShiftScale n (m n)) atTop (𝓝 1) := by
  have hh := (tendsto_boundedFamily_gaussianShift_mean_ratio_printed_ui hm hmTop hsmall).sub
    (tendsto_boundedFamily_observationShift_mean_ratio hm hmTop hsmall)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num] at hh
  simpa only [familyShiftMeanDifference, sub_div] using hh

theorem tendsto_boundedFamily_leading_comparison_ratio_printed_ui {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => normalMaximumDensity (m n) (printedNormalMaxThreshold (m n)) *
      familyShiftMeanDifference (boundedFamilyParameters n (m n)) n (m n) / boundedLowerScale n (m n))
      atTop (𝓝 (Real.sqrt 2 * Real.exp (-1))) := by
  have hD := tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log.comp hmTop
  have hM := tendsto_boundedFamily_shiftMean_difference_ratio_printed_ui hm hmTop hsmall
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

theorem tendsto_familyRare_gaussian_mean_ratio_printed_ui {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyGaussianShift (P n) z ∂standardGaussian (m n)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0) := by
  have hh := (hcoef.mul (tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability.comp hmTop)).div
    (familyScale_tendsto_one hv) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_mul, zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply, Function.comp_apply]
  rw [familyGaussianShift_integral]
  have hL : 0 < 2*Real.log (m n : ℝ) := by
    have hh := Real.log_pos (show (1 : ℝ) < m n by exact_mod_cast hm n)
    linarith
  exact (rare_gaussian_ratio_identity (P n).scale_pos.ne' (familyRareShiftScale_pos (P n) hn).ne'
    (Real.sqrt_pos.mpr hL).ne').symm

theorem tendsto_familyRare_leading_comparison_ratio_printed_ui {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => normalMaximumDensity (m n) (printedNormalMaxThreshold (m n))*
      familyShiftMeanDifference (P n) n (m n)/familyRareLowerScale (P n) n (m n))
      atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  have hMean := (tendsto_familyRare_gaussian_mean_ratio_printed_ui hm hmTop hv hcoef).sub
    (tendsto_familyRare_observation_mean_ratio hk hcover hv)
  simp only [zero_sub] at hMean
  have hMean' : Tendsto (fun n => familyShiftMeanDifference (P n) n (m n)/familyRareShiftScale (P n) n)
      atTop (𝓝 (-1)) := by
    simpa only [familyShiftMeanDifference, sub_div] using hMean
  have hh := ((tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log.comp hmTop).mul hMean').const_mul (Real.sqrt 2)
  convert hh.congr' ?_ using 1
  · ring
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  unfold familyRareLowerScale
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  field_simp [(familyRareShiftScale_pos (P n) hn).ne', (Real.sqrt_pos.mpr hL).ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

theorem eventually_boundedFamily_shift_second_moment_budget_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n) ≤
        (3 + 4 * Real.exp (11 / 2)) * Real.log (m n : ℝ) ^ 2 / n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [boundedFamilyParameters_eventually_count hm hmTop hsmall,
    (tendsto_boundedFamily_scale hm hmTop hsmall).eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with n hncount hns hnL hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have hU := familyObservationShift_sq_integral_le (boundedFamilyParameters n (m n)) n (m n)
  rw [boundedFamilyParameters_amplitude] at hU
  have hV := familyGaussianShift_sq_integral_le_printed (boundedFamilyParameters n (m n)) (m n)
  rw [boundedFamilyParameters_variance, dimensionLog_eq_one_add_log (by have := hm n; omega)] at hV
  exact bounded_shift_second_moment_budget hns hnp hnL (boundedFamilyParameters n (m n)).theta_pos.le
    (Real.exp_pos _).le hncount hU hV

end
end RectangleCLT.Companion.SplitV4.Printed
