import RectangleCLTCompanion.SplitV4.SymmetricBoundedMoments

/-! The actual local signed-shift Taylor cost is negligible at the
bounded symmetric lower family's extreme-value scale. -/

open MeasureTheory Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def boundedLocalDensityConstant : ℝ := Real.sqrt 2 * (Real.exp (-1)+1)

def boundedLocalShiftCostConstant (C : ℝ) : ℝ := C/2+2+boundedLocalDensityConstant

theorem boundedLocalDensityConstant_pos : 0 < boundedLocalDensityConstant := by
  unfold boundedLocalDensityConstant
  positivity

theorem boundedLocalShiftCostConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ boundedLocalShiftCostConstant C := by
  unfold boundedLocalShiftCostConstant
  have := boundedLocalDensityConstant_pos
  positivity

theorem eventually_normalMaximumDensity_at_threshold_abs_le_sqrt_log :
    ∀ᶠ m : ℕ in atTop,
      |normalMaximumDensity m (normalMaxThreshold m)| ≤
        boundedLocalDensityConstant * Real.sqrt (Real.log (m : ℝ)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    tendsto_normalMaximumDensity_at_threshold_div_sqrt_log.eventually
      (eventually_lt_nhds (lt_add_one (Real.exp (-1))))] with m hL hD
  have hL0 : 0 < Real.log (m : ℝ) := by linarith
  have hd0 : 0 ≤ normalMaximumDensity m (normalMaxThreshold m) := by
    unfold normalMaximumDensity
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (standardNormalCDF_nonneg _) _))
      (standardNormalPDF_nonneg _)
  have hh := (div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < 2*Real.log (m : ℝ)))).mp hD
  rw [abs_of_nonneg hd0]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
  exact hh.le.trans_eq (by unfold boundedLocalDensityConstant; ring)

theorem localShiftComparisonCost_le_log {C D ell d : ℝ}
    (hL : 0 < ell) (hd : |d| ≤ D * Real.sqrt ell) :
    localShiftComparisonCost (C*ell) (1/Real.sqrt ell) d ≤ (C/2+2+D)*ell := by
  have hs : Real.sqrt ell ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have he : localShiftComparisonCost (C*ell) (1/Real.sqrt ell) d =
      C/2*ell+2*ell+|d| * Real.sqrt ell := by
    unfold localShiftComparisonCost
    simp only [div_pow, one_pow, div_div, div_one]
    rw [Real.sq_sqrt hL.le]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg ell)
  rw [mul_assoc, Real.mul_self_sqrt hL.le] at hh
  nlinarith

theorem eventually_localShiftComparisonCost_le_log (C : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      localShiftComparisonCost (C*Real.log (m : ℝ)) (1/Real.sqrt (Real.log (m : ℝ)))
        (normalMaximumDensity m (normalMaxThreshold m)) ≤
          boundedLocalShiftCostConstant C * Real.log (m : ℝ) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_normalMaximumDensity_at_threshold_abs_le_sqrt_log,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with m hd hL
  exact localShiftComparisonCost_le_log hL hd

theorem familyShiftSecondMoments_nonneg (P : SymmetricFamilyParameters)
    (n m : ℕ) [NeZero m] : 0 ≤ familyShiftSecondMoments P n m := by
  unfold familyShiftSecondMoments
  exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

theorem lower_cubic_remainder_ratio_identity {ell N : ℝ} (hL : 0 < ell) (hN : 0 < N) :
    (ell^3/N)/(ell^(3/2 : ℝ)/(2*Real.sqrt N)) = 2*Real.sqrt (ell^3/N) := by
  have hsL : Real.sqrt ell ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hsN : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have hroot : Real.sqrt (ell^3/N) = ell*Real.sqrt ell/Real.sqrt N := by
    rw [Real.sqrt_div (pow_nonneg hL.le 3), show ell^3 = ell^2*ell by ring,
      Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hL.le]
  rw [lower_rpow_three_halves hL, hroot]
  apply (div_eq_iff (div_ne_zero (mul_ne_zero hL.ne' hsL) (mul_ne_zero (by norm_num) hsN))).mpr
  field_simp [hN.ne', hsN]
  ring_nf
  rw [Real.sq_sqrt hL.le, Real.sq_sqrt hN.le]
  ring

/-- The actual second moments and the actual Gaussian maximum density
make the local Taylor remainder negligible relative to the lower scale. -/
theorem tendsto_boundedFamily_local_shift_remainder_ratio
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
        (normalMaximumDensity (m n) (normalMaxThreshold (m n))) *
        familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n) /
          boundedLowerScale n (m n)) atTop (𝓝 0) := by
  let K := boundedLocalShiftCostConstant C
  let M := 3+4*Real.exp (11/2)
  have hK : 0 ≤ K := boundedLocalShiftCostConstant_nonneg hC
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hup : Tendsto (fun n : ℕ => 2*K*M*Real.sqrt (Real.log (m n : ℝ)^3/n)) atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hsmall).const_mul (2*K*M)
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
    have hr : 0 ≤ localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
        (normalMaximumDensity (m n) (normalMaxThreshold (m n))) := by
      unfold localShiftComparisonCost
      positivity
    exact div_nonneg (mul_nonneg hr (familyShiftSecondMoments_nonneg _ _ _)) (by
      unfold boundedLowerScale
      positivity)
  · filter_upwards [hmTop.eventually (eventually_localShiftComparisonCost_le_log C),
      eventually_boundedFamily_shift_second_moment_budget hm hmTop hsmall,
      eventually_ge_atTop 1] with n hcost hmoment hn
    have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : 0 < boundedLowerScale n (m n) := by unfold boundedLowerScale; positivity
    have hprod := mul_le_mul hcost hmoment (familyShiftSecondMoments_nonneg _ _ _)
      (mul_nonneg hK hL.le)
    have hh := div_le_div_of_nonneg_right hprod hden.le
    apply hh.trans_eq
    change (K*Real.log (m n : ℝ))*(M*Real.log (m n : ℝ)^2/n)/boundedLowerScale n (m n) = _
    calc
      _ = K*M*((Real.log (m n : ℝ)^3/n)/
          (Real.log (m n : ℝ)^(3/2 : ℝ)/(2*Real.sqrt n))) := by unfold boundedLowerScale; ring
      _ = _ := by rw [lower_cubic_remainder_ratio_identity hL hN]; ring

end
end RectangleCLT.Companion.SplitV4
