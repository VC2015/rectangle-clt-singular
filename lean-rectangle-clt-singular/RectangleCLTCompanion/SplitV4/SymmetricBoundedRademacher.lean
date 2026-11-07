import RectangleCLTCompanion.SplitV4.SymmetricBoundedShiftLimits
import RectangleCLTCompanion.SplitV4.RademacherLocalComparison

/-! Actual local Rademacher error is negligible on the bounded symmetric lower scale. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem sqrt_cube_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 3) = x * Real.sqrt x := by
  rw [show x ^ 3 = x ^ 2 * x by ring, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx]

theorem tendsto_boundedLowerScale_zero {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => boundedLowerScale n (m n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hsmall).div_const 2
  simp only [Real.sqrt_zero, zero_div] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
  dsimp only [Function.comp_apply]
  unfold boundedLowerScale
  rw [Real.sqrt_div (pow_nonneg hn.le 3), sqrt_cube_eq_mul_sqrt hn.le, lower_rpow_three_halves hn]
  ring

theorem eventually_boundedLowerScale_pos {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < boundedLowerScale n (m n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hlog.eventually (eventually_gt_atTop 0), eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  unfold boundedLowerScale
  exact div_pos (Real.rpow_pos_of_pos hn _) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hnp))

theorem tendsto_rademacherLocalError_div_boundedLowerScale {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => rademacherLocalError n (m n) / boundedLowerScale n (m n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hratio := tendsto_lower_comparison_remainder_div_rate hlog hsmall
  have hupper := hratio.const_mul (162 * moderateTailRemainderConstant)
  simp only [mul_zero] at hupper
  have hC := moderateTailRemainderConstant_bounds.1
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rademacherLocalError n (m n) / boundedLowerScale n (m n) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop 0), eventually_boundedLowerScale_pos hmTop] with n hn hd
    unfold rademacherLocalError
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      rademacherLocalError n (m n) / boundedLowerScale n (m n) ≤ 162 * moderateTailRemainderConstant *
        ((Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n + Real.log (m n : ℝ) ^ 2 / n) /
          (Real.log (m n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt n)) := by
    filter_upwards [hlog.eventually (eventually_gt_atTop 0), eventually_ge_atTop 1] with n hn hn1
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsqrt := Real.sqrt_pos.mpr hnp
    have hR : 0 < Real.log (m n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt n :=
      div_pos (Real.rpow_pos_of_pos hn _) hsqrt
    have hE : rademacherLocalError n (m n) ≤ 81 * moderateTailRemainderConstant *
        (Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n + Real.log (m n : ℝ) ^ 2 / n) := by
      unfold rademacherLocalError
      have ha : 0 ≤ Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n := by positivity
      have hh := mul_le_mul_of_nonneg_left
        (show 4 * (Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n) + 81 * (Real.log (m n : ℝ) ^ 2 / n) ≤
          81 * (Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n + Real.log (m n : ℝ) ^ 2 / n) by nlinarith only [ha]) hC.le
      convert hh using 1 <;> ring
    have hd : boundedLowerScale n (m n) = (Real.log (m n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt n) / 2 := by
      unfold boundedLowerScale
      ring
    rw [hd]
    have hfrac : rademacherLocalError n (m n) / ((Real.log (m n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt n) / 2) ≤
        (162 * moderateTailRemainderConstant *
          (Real.sqrt (Real.log (m n : ℝ)) / Real.sqrt n + Real.log (m n : ℝ) ^ 2 / n)) /
            (Real.log (m n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt n) := by
      apply (div_le_div_iff₀ (half_pos hR) hR).mpr
      have hh := mul_le_mul_of_nonneg_right hE hR.le
      nlinarith only [hh]
    exact hfrac.trans_eq (by ring)
  exact squeeze_zero' hnonneg hbound hupper

theorem eventually_boundedFamily_rademacher_conditions {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      moderateTailSmallConstant * ((1/Real.sqrt n)*(1+3*Real.sqrt (Real.log (m n : ℝ)))) ≤ 1 ∧
        rademacherLocalError n (m n) ≤ 1 := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hsqrtNat : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((max b 0) ^ 2))] with n hn
    exact (le_max_left b 0).trans (Real.le_sqrt_of_sq_le hn)
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtNat
  have hsqrt := tendsto_lower_sqrt_ell_div_sqrt_n hlog hsmall
  have hdelta := (hinv.add (hsqrt.const_mul 3)).const_mul moderateTailSmallConstant
  simp only [mul_zero, add_zero] at hdelta
  have hdelta' : Tendsto (fun n : ℕ => moderateTailSmallConstant * ((1/Real.sqrt n)*(1+3*Real.sqrt (Real.log (m n : ℝ)))))
      atTop (𝓝 0) := by
    convert hdelta using 1
    funext n
    ring
  have he := (tendsto_rademacherLocalError_div_boundedLowerScale hmTop hsmall).mul (tendsto_boundedLowerScale_zero hmTop hsmall)
  simp only [mul_zero] at he
  have he' : Tendsto (fun n : ℕ => rademacherLocalError n (m n)) atTop (𝓝 0) := by
    apply he.congr'
    filter_upwards [eventually_boundedLowerScale_pos hmTop] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  filter_upwards [hdelta'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    he'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn he
  exact ⟨hn, he⟩

end
end RectangleCLT.Companion.SplitV4
