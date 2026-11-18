import RectangleCLTArxivV1.LowerRectangularDetection
import RectangleCLTArxivV1.LowerWidthBudget

/-! Discharging the actual signed comparison from the width-small regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lower_dimensionLog_le_twice_rare_log {r m : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m)
    (hmL : 1 ≤ Real.log (m : ℝ)) : dimensionLog r ≤ 2*Real.log (m : ℝ) := by
  rw [dimensionLog_eq_one_add_log hr]
  have hh := Real.log_le_log (by exact_mod_cast hr : (0 : ℝ) < r) (by exact_mod_cast hrm : (r : ℝ) ≤ m)
  linarith

theorem lowerFamilyMasterRemainder_nonneg (P : SymmetricFamilyParameters) {r m n : ℕ}
    [NeZero m] (hr : 1 ≤ r) : 0 ≤ lowerFamilyMasterRemainder P n r m := by
  have hdim : 0 ≤ dimensionLog r := zero_le_one.trans (log_exp_mul_nat_ge_one hr)
  have hMom : 0 ≤ familyShiftSecondMoments P n m := by
    exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))
  unfold lowerFamilyMasterRemainder Printed.rademacherGlobalError
  exact add_nonneg
    (mul_nonneg lowerRademacherMaximumConstant_pos.le (by positivity))
    (mul_nonneg (div_nonneg (mul_nonneg lowerGaussianCurvatureConstant_pos.le hdim) (by norm_num)) hMom)

theorem lowerFamilyMasterRemainder_width_bound (P : SymmetricFamilyParameters) {n r m : ℕ}
    [NeZero m] {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (hr : 1 ≤ r) (hrm : r ≤ m)
    (hL : 1 ≤ Real.log (m : ℝ)) (ha : 1 ≤ P.amplitude)
    (hg : c*Real.sqrt (dimensionLog r) ≤ independentAbsGaussianMean r)
    (hπ : P.pi = 1) (hcount : (n : ℝ)*P.theta = Real.log (m : ℝ)/2) :
    lowerFamilyMasterRemainder P n r m ≤
      ((lowerRademacherMaximumConstant/c)/Real.log (m : ℝ)+
        (2*lowerRademacherMaximumConstant+lowerGaussianCurvatureConstant*(3+4*Real.exp (11/2))/2)*
          (lowerFamilyWidthScale P n r m/c^2))*lowerFamilyWidthScale P n r m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ dimensionLog r := zero_le_one.trans (log_exp_mul_nat_ge_one hr)
  have hMom := lowerFamily_unmasked_shift_second_moment_budget P hn hL hπ hcount
  have hAll := lowerWidthBudget_combined ha hL hn0 hR
    (lower_dimensionLog_le_twice_rare_log hr hrm hL) hc hg
    lowerRademacherMaximumConstant_pos.le lowerGaussianCurvatureConstant_pos.le
    (show 0 ≤ 3+4*Real.exp (11/2) by positivity)
  have hScaled := mul_le_mul_of_nonneg_left hMom
    (show 0 ≤ lowerGaussianCurvatureConstant*dimensionLog r/2 from
      div_nonneg (mul_nonneg lowerGaussianCurvatureConstant_pos.le hR) (by norm_num))
  have hTotal := add_le_add_left hScaled
    (lowerRademacherMaximumConstant*Printed.rademacherGlobalError n r)
  unfold lowerFamilyMasterRemainder
  apply hTotal.trans
  convert hAll using 1 <;> simp only [Printed.rademacherGlobalError,lowerWidthScale,lowerFamilyWidthScale] <;> ring

theorem tendsto_lowerFamilyMasterRemainder_div_width
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ (P n).amplitude)
    (hπ : ∀ᶠ n in atTop, (P n).pi = 1)
    (hcount : ∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2)
    (hsmall : Tendsto (fun n => lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => lowerFamilyMasterRemainder (P n) n (r n) (m n)/
      lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hwidth⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  let A := 2*lowerRademacherMaximumConstant+
    lowerGaussianCurvatureConstant*(3+4*Real.exp (11/2))/2
  have hbound : Tendsto (fun n => (lowerRademacherMaximumConstant/c)/Real.log (m n : ℝ)+
      A*(lowerFamilyWidthScale (P n) n (r n) (m n)/c^2)) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := lowerRademacherMaximumConstant/c)).div_atTop hlog).add
      ((hsmall.div_const (c^2)).const_mul A)
    simpa only [zero_div,mul_zero,zero_add] using hh
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (lowerFamilyMasterRemainder_nonneg (P n) (hr n))
      (lowerFamilyWidthScale_pos (P n) hn (hr n) (hm n)).le
  · filter_upwards [ha,hπ,hcount,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
      with n hna hnπ hnc hnL hn
    apply (div_le_iff₀ (lowerFamilyWidthScale_pos (P n) hn (hr n) (hm n))).mpr
    exact lowerFamilyMasterRemainder_width_bound (P n) hc hn (hr n) (hrm n) hnL hna
      (hwidth (r n) (hr n)) hnπ hnc

theorem tendsto_lowerFamily_dimensionLog_div_sqrt
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ (P n).amplitude)
    (hsmall : Tendsto (fun n => lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => dimensionLog (r n)/Real.sqrt n) atTop (𝓝 0) := by
  obtain ⟨c,hc,hwidth⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hbound : Tendsto (fun n => (2/c)*lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (2/c)
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall (fun n => div_nonneg
      (zero_le_one.trans (log_exp_mul_nat_ge_one (hr n))) (Real.sqrt_nonneg _))
  · filter_upwards [ha,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
      with n hna hnL hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact lowerWidthBudget_range hna hnL hn0 (log_exp_mul_nat_ge_one (hr n))
      (lower_dimensionLog_le_twice_rare_log (hr n) (hrm n) hnL) hc (hwidth (r n) (hr n))

theorem eventually_lowerFamily_leading_range
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ (P n).amplitude)
    (hsmall : Tendsto (fun n => lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, dimensionLog (r n) ≤ Printed.rademacherGlobalSmallConstant*Real.sqrt n := by
  have hh := (tendsto_lowerFamily_dimensionLog_div_sqrt hr hrm hmTop ha hsmall).eventually
    (eventually_le_nhds Printed.rademacherGlobalSmallConstant_pos)
  filter_upwards [hh,eventually_ge_atTop 1] with n hnL hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hn0)).mp hnL

/-- The signed orthant discrepancy and the rectangle distance are derived
from the actual laws. The only smallness assumption is the prescribed
width-sensitive rare-shift scale. -/
theorem exists_lowerFamily_unmasked_width_detection_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ → SymmetricFamilyParameters) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      (∀ᶠ n : ℕ in atTop, 1 ≤ (P n).amplitude) →
      (∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2) →
      (∀ᶠ n : ℕ in atTop, (P n).pi = 1) →
      Tendsto (fun n => (P n).variance) atTop (𝓝 0) →
      Tendsto (fun n => lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop,
        c*lowerFamilyWidthScale (P n) n (r n) (m n) ≤
          lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerFamilyWidthScale (P n) n (r n) (m n) ≤ lowerFamilyComparisonDistance (P n) n (r n) (m n) := by
  obtain ⟨c,hc,hDetect⟩ := exists_lowerFamily_unmasked_signed_detection_constant
  refine ⟨c,hc,?_⟩
  intro P r m _ _ hr hm hrm hmTop ha hcount hπ hv hsmall
  have hh := hDetect P r m hr hm hmTop hcount hπ hv
    (eventually_lowerFamily_leading_range hr hrm hmTop ha hsmall)
    (tendsto_lowerFamilyMasterRemainder_div_width hr hm hrm hmTop ha hπ hcount hsmall)
  filter_upwards [hh] with n hn
  refine ⟨hn,hn.trans ((le_abs_self _).trans ?_)⟩
  exact abs_lowerFamilyShiftedCDFDifference_le_distance (P n) n (r n) (m n) (lowerLeadingThreshold (r n))

end
end RectangleCLTArxivV1
