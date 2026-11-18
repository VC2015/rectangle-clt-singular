import RectangleCLTArxivV1.LowerLeadingCalibration
import RectangleCLTArxivV1.LowerWidthCalibration
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence

/-! Uniform leading-density/width calibration, including bounded counts. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem positive_global_lower_of_eventual {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ n, 1 ≤ n → 0 < f n) (he : ∀ᶠ n in atTop, c ≤ f n) :
    ∃ a : ℝ, 0 < a ∧ ∀ n, 1 ≤ n → a ≤ f n := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let S := Finset.Icc 1 (max N 1)
  have hS : S.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩⟩
  let b := S.inf' hS f
  have hb : 0 < b := by
    apply (Finset.lt_inf'_iff hS).mpr
    intro n hn
    exact hf n (Finset.mem_Icc.mp hn).1
  refine ⟨min c b, lt_min hc hb, ?_⟩
  intro n hn
  by_cases hnS : n ≤ max N 1
  · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hn,hnS⟩))
  · exact (min_le_left _ _).trans (hN n (by omega))

theorem gaussianMaximumMean_le_absolute {r : ℕ} (hr : 1 ≤ r) :
    RectangleCLT.Companion.SplitV4.gaussianMaximumMean r ≤ independentAbsGaussianMean r := by
  letI : NeZero r := ⟨by omega⟩
  rw [gaussianMaximumMean_eq_integral]
  unfold independentAbsGaussianMean
  apply integral_mono (integrable_finiteGaussianMaximum r) (standardGaussian_integrable_norm r)
  intro g
  change finiteMaximum g ≤ ‖g‖
  obtain ⟨j,hj⟩ := finiteMaximum_attains g
  rw [← hj]
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j)

theorem eventually_absoluteGaussianMean_sqrt_lower :
    ∀ᶠ r : ℕ in atTop, (1/2 : ℝ)*Real.sqrt (dimensionLog r) ≤ independentAbsGaussianMean r := by
  have hmean := Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability.eventually
    (eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hmean,hlog,eventually_ge_atTop 2] with r hr hL hr2
  change 1 ≤ Real.log (r : ℝ) at hL
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hdim : dimensionLog r ≤ 2*Real.log (r : ℝ) := by
    rw [dimensionLog,Real.log_mul (Real.exp_ne_zero _) hr0.ne',Real.log_exp]
    linarith
  have hs : 0 < Real.sqrt (2*Real.log (r : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hb := (le_div_iff₀ hs).mp hr.le
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdim) (by norm_num : (0 : ℝ) ≤ 1/2)
  exact hh.trans (hb.trans (gaussianMaximumMean_le_absolute hr1))

theorem exists_absoluteGaussianMean_sqrt_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ r, 1 ≤ r → c*Real.sqrt (dimensionLog r) ≤ independentAbsGaussianMean r := by
  have hpos (r : ℕ) (hr : 1 ≤ r) :
      0 < independentAbsGaussianMean r/Real.sqrt (dimensionLog r) := by
    apply div_pos ((by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower hr))
    exact Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr))
  have he : ∀ᶠ r : ℕ in atTop, (1/2 : ℝ) ≤ independentAbsGaussianMean r/Real.sqrt (dimensionLog r) := by
    filter_upwards [eventually_absoluteGaussianMean_sqrt_lower,eventually_ge_atTop 1] with r hr hr1
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr1)))).mpr hr
  obtain ⟨c,hc,hbound⟩ := positive_global_lower_of_eventual (by norm_num : (0 : ℝ) < 1/2) hpos he
  refine ⟨c,hc,?_⟩
  intro r hr
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr)))).mp (hbound r hr)

def lowerLeadingThreshold (r : ℕ) : ℝ := if r=1 then 0 else Printed.printedNormalMaxThreshold r

theorem normalMaximumDensity_pos_positive_count {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    0 < normalMaximumDensity r t := by
  unfold normalMaximumDensity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  exact mul_pos (mul_pos hr0 (pow_pos (standardNormalCDF_pos _) _)) (standardNormalPDF_pos _)

theorem eventually_leadingDensity_sqrt_lower :
    ∀ᶠ r : ℕ in atTop, (Real.exp (-1)/2)*Real.sqrt (dimensionLog r) ≤
      normalMaximumDensity r (lowerLeadingThreshold r) := by
  have hd := Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log.eventually
    (eventually_gt_nhds (by linarith [Real.exp_pos (-1)] : Real.exp (-1)/2 < Real.exp (-1)))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hd,hlog,eventually_ge_atTop 2] with r hr hL hr2
  change 1 ≤ Real.log (r : ℝ) at hL
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 1 ≤ r)
  have hdim : dimensionLog r ≤ 2*Real.log (r : ℝ) := by
    rw [dimensionLog,Real.log_mul (Real.exp_ne_zero _) hr0.ne',Real.log_exp]
    linarith
  have hs : 0 < Real.sqrt (2*Real.log (r : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hb := (le_div_iff₀ hs).mp hr.le
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdim) (by positivity : 0 ≤ Real.exp (-1)/2)
  simpa only [lowerLeadingThreshold,if_neg (by omega : r≠1)] using hh.trans hb

theorem exists_leadingDensity_sqrt_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ r, 1 ≤ r →
      c*Real.sqrt (dimensionLog r) ≤ normalMaximumDensity r (lowerLeadingThreshold r) := by
  have hpos (r : ℕ) (hr : 1 ≤ r) :
      0 < normalMaximumDensity r (lowerLeadingThreshold r)/Real.sqrt (dimensionLog r) :=
    div_pos (normalMaximumDensity_pos_positive_count hr _)
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr)))
  have he : ∀ᶠ r : ℕ in atTop, Real.exp (-1)/2 ≤
      normalMaximumDensity r (lowerLeadingThreshold r)/Real.sqrt (dimensionLog r) := by
    filter_upwards [eventually_leadingDensity_sqrt_lower,eventually_ge_atTop 1] with r hr hr1
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr1)))).mpr hr
  obtain ⟨c,hc,hbound⟩ := positive_global_lower_of_eventual (by positivity : 0 < Real.exp (-1)/2) hpos he
  refine ⟨c,hc,?_⟩
  intro r hr
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr)))).mp (hbound r hr)

theorem exists_leadingDensity_width_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ r, 1 ≤ r →
      c*independentAbsGaussianMean r ≤ normalMaximumDensity r (lowerLeadingThreshold r) := by
  obtain ⟨c,hc,hbound⟩ := exists_leadingDensity_sqrt_lower
  refine ⟨c/2,by positivity,?_⟩
  intro r hr
  have hh := mul_le_mul_of_nonneg_left (independentAbsGaussianMean_upper hr) (by positivity : 0 ≤ c/2)
  exact hh.trans ((by ring : c/2*(2*Real.sqrt (dimensionLog r)) = c*Real.sqrt (dimensionLog r)).le.trans (hbound r hr))

end
end RectangleCLTArxivV1
