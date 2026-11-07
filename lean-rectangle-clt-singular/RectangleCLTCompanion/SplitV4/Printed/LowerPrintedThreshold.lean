import RectangleCLTCompanion.SplitV4.Printed.LowerGlobalComparison
import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumGlobal
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile

/-! The global maximum comparison at the paper's literal m*tail=1
threshold, with the global Kolmogorov input discharged. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem eventually_lowerMaximum_global_CDF
    {m : ℕ→ℕ} [∀n,NeZero (m n)] (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤
        rademacherGlobalConstant*lowerMaximumApproximationRate n (m n) := by
  filter_upwards [eventually_familyRademacherMaximum_global_error,eventually_ge_atTop 1,
    (tendsto_lowerDimensionLog_div_sqrt hmTop hsmall).eventually
      (eventually_lt_nhds rademacherGlobalSmallConstant_pos)] with n hn hn1 hsmalln
  have hN : (0:ℝ)<n := by exact_mod_cast hn1
  have hcondition : dimensionLog (m n)≤rademacherGlobalSmallConstant*Real.sqrt n :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mp hsmalln.le
  intro x
  simpa only [lowerMaximumApproximationRate,rademacherGlobalError] using hn (m n) (hm n) hcondition x

theorem tendsto_printed_density_ratio :
    Tendsto (fun m => normalMaximumDensity m (printedNormalMaxThreshold m)/
      normalMaximumDensity m (normalMaxThreshold m)) atTop (𝓝 (1:ℝ)) := by
  have hn := tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log
  have ho := tendsto_normalMaximumDensity_at_threshold_div_sqrt_log
  have he := hn.div ho (Real.exp_pos (-1)).ne'
  rw [div_self (Real.exp_pos (-1)).ne'] at he
  have hold := ho.eventually (eventually_ne_nhds (Real.exp_pos (-1)).ne')
  apply he.congr'
  filter_upwards [hold,eventually_ge_atTop 2] with m hm hm2
  have hlog : 0<Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hs : Real.sqrt (2*Real.log (m:ℝ))≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hs]

theorem printed_threshold_leading_tendsto
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hmTop : Tendsto m atTop atTop) (d : ℕ→ℝ) {c : ℝ}
    (hLead : Tendsto (fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n))*
      familyShiftMeanDifference (P n) n (m n)/d n) atTop (𝓝 c)) :
    Tendsto (fun n => normalMaximumDensity (m n) (printedNormalMaxThreshold (m n))*
      familyShiftMeanDifference (P n) n (m n)/d n) atTop (𝓝 c) := by
  have hr := tendsto_printed_density_ratio.comp hmTop
  have he := hr.mul hLead
  rw [one_mul] at he
  have ho := (tendsto_normalMaximumDensity_at_threshold_div_sqrt_log.comp hmTop).eventually
    (eventually_ne_nhds (Real.exp_pos (-1)).ne')
  apply he.congr'
  filter_upwards [ho] with n hn
  have hd : normalMaximumDensity (m n) (normalMaxThreshold (m n))≠0 :=
    (div_ne_zero_iff.mp hn).1
  dsimp only [Function.comp_apply]
  simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,hd]

theorem boundedFamily_printed_discrepancy_div_scale
    {m : ℕ→ℕ} [∀n,NeZero (m n)] (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0)) :
    Tendsto (fun n => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
      (printedNormalMaxThreshold (m n))/boundedLowerScale n (m n)) atTop (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
  apply familyGlobal_discrepancy_div_scale_at hm (fun n => printedNormalMaxThreshold (m n))
    (fun n => rademacherGlobalConstant*lowerMaximumApproximationRate n (m n))
    (fun n => boundedLowerScale n (m n)) (eventually_boundedLowerScale_pos hmTop)
    (Eventually.of_forall (fun _ => mul_nonneg rademacherGlobalConstant_pos.le (lowerMaximumApproximationRate_nonneg _ _)))
    (eventually_lowerMaximum_global_CDF hm hmTop hsmall)
  · simpa only [mul_div_assoc,mul_zero] using
      (tendsto_lowerMaximumApproximationRate_div_boundedScale hmTop hsmall).const_mul rademacherGlobalConstant
  · exact boundedFamily_global_remainder_tendsto hm hmTop hsmall
  · exact tendsto_boundedFamily_leading_comparison_ratio_printed_ui hm hmTop hsmall

theorem tendsto_amplifiedFamily_discrepancy_printed
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0))
    (hθ : ∀ᶠ n in atTop,(P n).theta=(boundedFamilyParameters n (m n)).theta)
    (hπ : ∀ᶠ n in atTop,(P n).pi=(boundedFamilyParameters n (m n)).pi)
    (hk : ∀ᶠ n in atTop,1≤familyShiftAmplification (P n) (boundedFamilyParameters n (m n)))
    (hksmall : Tendsto (fun n => familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*
      Real.sqrt (Real.log (m n:ℝ)^3/n)) atTop (𝓝 0)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (printedNormalMaxThreshold (m n))/
      amplifiedSymmetricLowerScale (P n) n (m n)) atTop (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
  have hC := rademacherGlobalConstant_pos.le
  have hCDF := eventually_lowerMaximum_global_CDF hm hmTop hsmall
  let C := rademacherGlobalConstant
  have hd : ∀ᶠ n in atTop,0<amplifiedSymmetricLowerScale (P n) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact amplifiedSymmetricLowerScale_pos (P n) hn (hm n)
  apply familyGlobal_discrepancy_div_scale_at hm (fun n => printedNormalMaxThreshold (m n)) (fun n => C*lowerMaximumApproximationRate n (m n))
    (fun n => amplifiedSymmetricLowerScale (P n) n (m n)) hd
    (Eventually.of_forall (fun n => mul_nonneg hC (lowerMaximumApproximationRate_nonneg _ _))) hCDF
  · have he := (tendsto_lowerMaximumApproximationRate_div_boundedScale hmTop hsmall).const_mul C
    simp only [mul_zero] at he
    apply squeeze_zero' _ _ he
    · filter_upwards [hd] with n hn
      exact div_nonneg (mul_nonneg hC (lowerMaximumApproximationRate_nonneg _ _)) hn.le
    · filter_upwards [hk,eventually_boundedLowerScale_pos hmTop] with n hn hd
      have hden : boundedLowerScale n (m n)≤amplifiedSymmetricLowerScale (P n) n (m n) := by
        unfold amplifiedSymmetricLowerScale; nlinarith [mul_nonneg (sub_nonneg.mpr hn) hd.le]
      exact (div_le_div_of_nonneg_left (mul_nonneg hC (lowerMaximumApproximationRate_nonneg _ _)) hd hden).trans_eq (by ring)
  · have hu := hksmall.const_mul (2*gaussianMaximumCurvatureConstant*(3+4*Real.exp (11/2)))
    simp only [mul_zero] at hu
    apply squeeze_zero' _ (amplifiedFamily_global_remainder_bound hm hmTop hsmall hθ hπ) hu
    filter_upwards [hd] with n hn
    exact div_nonneg (mul_nonneg (by
      have hdim : 0≤dimensionLog (m n) := zero_le_one.trans (log_exp_mul_nat_ge_one (by have := hm n; omega))
      have hCurv := gaussianMaximumCurvatureConstant_pos
      positivity) (familyShiftSecondMoments_nonneg _ _ _)) hn.le
  · apply (tendsto_boundedFamily_leading_comparison_ratio_printed_ui hm hmTop hsmall).congr'
    filter_upwards [hθ,hπ,eventually_boundedLowerScale_pos hmTop] with n hnθ hnπ hd
    rw [familyShiftMeanDifference_amplification _ _ hnθ hnπ]
    unfold amplifiedSymmetricLowerScale
    field_simp [hd.ne',(familyShiftAmplification_pos (P n) (boundedFamilyParameters n (m n))).ne']
    ring


theorem tendsto_rareFamily_discrepancy_printed
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hk : Tendsto (fun n : ℕ => (n:ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n => (m n:ℝ)*((P n).pi/2)^Nat.ceil (2*((n:ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n:ℝ))/familyRareShiftScale (P n) n) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0))
    (hScale : Tendsto (fun n => familyRareLowerScale (P n) n (m n)/boundedLowerScale n (m n)) atTop atTop)
    (hU : Tendsto (fun n => Real.log (m n:ℝ)*(P n).amplitude^2*
      (((n:ℝ)*(P n).theta)^2+(n:ℝ)*(P n).theta)/n/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0))
    (hV : Tendsto (fun n => Real.log (m n:ℝ)*(P n).variance*(1+Real.log (m n:ℝ))/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (printedNormalMaxThreshold (m n))/
      familyRareLowerScale (P n) n (m n)) atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  have hC := rademacherGlobalConstant_pos.le
  have hCDF := eventually_lowerMaximum_global_CDF hm hmTop hsmall
  let C := rademacherGlobalConstant
  have hd : ∀ᶠ n in atTop,0<familyRareLowerScale (P n) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact familyRareLowerScale_pos (P n) hn (hm n)
  apply familyGlobal_discrepancy_div_scale_at hm (fun n => printedNormalMaxThreshold (m n)) (fun n => C*lowerMaximumApproximationRate n (m n))
    (fun n => familyRareLowerScale (P n) n (m n)) hd
    (Eventually.of_forall (fun n => mul_nonneg hC (lowerMaximumApproximationRate_nonneg _ _))) hCDF
  · have he := ((tendsto_lowerMaximumApproximationRate_div_boundedScale hmTop hsmall).const_mul C).mul
      (tendsto_inv_atTop_zero.comp hScale)
    simp only [mul_zero] at he
    apply he.congr'
    filter_upwards [hd,eventually_boundedLowerScale_pos hmTop] with n hn hd
    dsimp only [Function.comp_apply]
    field_simp [hn.ne',hd.ne']
  · exact familyGlobal_remainder_tendsto hm hmTop _ hd hv hU hV
  · exact tendsto_familyRare_leading_comparison_ratio_printed_ui hm hmTop hk hcover hv hcoef

end
end RectangleCLT.Companion.SplitV4.Printed
