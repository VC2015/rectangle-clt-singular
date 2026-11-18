import RectangleCLTArxivV1.LowerMaskedMoments

/-! Width-sensitive remainder calibration for the actual masked model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerFamilyMaskedMasterRemainder_width_bound (P : SymmetricFamilyParameters) {n r m : ℕ}
    [NeZero m] {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (hr : 1 ≤ r) (hm : 2 ≤ m) (hrm : r ≤ m)
    (hL : 1 ≤ Real.log (m : ℝ)) (ha : 1 ≤ lowerFamilyEffectiveAmplitude P n m)
    (hg : c*Real.sqrt (dimensionLog r) ≤ independentAbsGaussianMean r)
    (hk : 1 ≤ (n : ℝ)*P.theta) (hpi : P.pi*Real.log (m : ℝ) ≤ (n : ℝ)*P.theta) :
    lowerFamilyMasterRemainder P n r m ≤
      ((lowerRademacherMaximumConstant/c)/Real.log (m : ℝ)+
        (2*lowerRademacherMaximumConstant+lowerGaussianCurvatureConstant*(12+8*Real.exp (11/2))/2)*
          (lowerFamilyRareWidthScale P n r/c^2))*lowerFamilyRareWidthScale P n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ dimensionLog r := zero_le_one.trans (log_exp_mul_nat_ge_one hr)
  have hMom := lowerFamily_masked_shift_second_moment_budget P hn hL hk hpi
  rw [mul_assoc,lowerFamilyEffectiveAmplitude_square P (n := n) hm] at hMom
  have hAll := lowerWidthBudget_combined ha hL hn0 hR
    (lower_dimensionLog_le_twice_rare_log hr hrm hL) hc hg
    lowerRademacherMaximumConstant_pos.le lowerGaussianCurvatureConstant_pos.le
    (show 0 ≤ 12+8*Real.exp (11/2) by positivity)
  rw [lowerFamilyEffectiveAmplitude_widthScale P hm] at hAll
  have hScaled := mul_le_mul_of_nonneg_left hMom
    (show 0 ≤ lowerGaussianCurvatureConstant*dimensionLog r/2 from
      div_nonneg (mul_nonneg lowerGaussianCurvatureConstant_pos.le hR) (by norm_num))
  have hTotal := add_le_add_left hScaled
    (lowerRademacherMaximumConstant*Printed.rademacherGlobalError n r)
  unfold lowerFamilyMasterRemainder
  apply hTotal.trans
  convert hAll using 1 <;> (try simp only [Printed.rademacherGlobalError]) <;> ring

theorem tendsto_lowerFamilyMaskedMasterRemainder_div_width
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ lowerFamilyEffectiveAmplitude (P n) n (m n))
    (hk : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ)*(P n).theta)
    (hpi : ∀ᶠ n : ℕ in atTop, (P n).pi*Real.log (m n : ℝ) ≤ (n : ℝ)*(P n).theta)
    (hsmall : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0)) :
    Tendsto (fun n => lowerFamilyMasterRemainder (P n) n (r n) (m n)/
      lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hwidth⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  let A := 2*lowerRademacherMaximumConstant+
    lowerGaussianCurvatureConstant*(12+8*Real.exp (11/2))/2
  have hbound : Tendsto (fun n => (lowerRademacherMaximumConstant/c)/Real.log (m n : ℝ)+
      A*(lowerFamilyRareWidthScale (P n) n (r n)/c^2)) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := lowerRademacherMaximumConstant/c)).div_atTop hlog).add
      ((hsmall.div_const (c^2)).const_mul A)
    simpa only [zero_div,mul_zero,zero_add] using hh
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (lowerFamilyMasterRemainder_nonneg (P n) (hr n))
      (lowerFamilyRareWidthScale_pos (P n) hn (hr n)).le
  · filter_upwards [ha,hk,hpi,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
      with n hna hnk hnpi hnL hn
    apply (div_le_iff₀ (lowerFamilyRareWidthScale_pos (P n) hn (hr n))).mpr
    exact lowerFamilyMaskedMasterRemainder_width_bound (P n) hc hn (hr n) (hm n) (hrm n) hnL hna
      (hwidth (r n) (hr n)) hnk hnpi

theorem eventually_lowerFamily_masked_leading_range
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hrm : ∀ n, r n ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ lowerFamilyEffectiveAmplitude (P n) n (m n))
    (hsmall : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, dimensionLog (r n) ≤ Printed.rademacherGlobalSmallConstant*Real.sqrt n := by
  obtain ⟨c,hc,hwidth⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hbound : Tendsto (fun n => (2/c)*lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (2/c)
  have hratio : Tendsto (fun n : ℕ => dimensionLog (r n)/Real.sqrt n) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · exact Eventually.of_forall (fun n => div_nonneg
        (zero_le_one.trans (log_exp_mul_nat_ge_one (hr n))) (Real.sqrt_nonneg _))
    · filter_upwards [ha,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
        with n hna hnL hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hh := lowerWidthBudget_range hna hnL hn0 (log_exp_mul_nat_ge_one (hr n))
        (lower_dimensionLog_le_twice_rare_log (hr n) (hrm n) hnL) hc (hwidth (r n) (hr n))
      rwa [lowerFamilyEffectiveAmplitude_widthScale (P n) (hm n)] at hh
  have hh := hratio.eventually (eventually_le_nhds Printed.rademacherGlobalSmallConstant_pos)
  filter_upwards [hh,eventually_ge_atTop 1] with n hnL hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hn0)).mp hnL

end
end RectangleCLTArxivV1
