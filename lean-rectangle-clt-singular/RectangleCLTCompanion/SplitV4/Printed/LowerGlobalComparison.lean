import RectangleCLTCompanion.SplitV4.Printed.LowerGlobalRates
import RectangleCLTCompanion.SplitV4.AmplifiedSymmetricLower
import RectangleCLTCompanion.SplitV4.RareFamilyShifts

/-! The printed global comparison route at the actual lower families.
The common global Kolmogorov estimate is an explicit intermediate input;
the final wrappers discharge it from the global maximum theorem. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem boundedFamily_global_discrepancy_from_CDF
    {m : ℕ→ℕ} [∀n,NeZero (m n)] (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hCDF : ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤
        C*lowerMaximumApproximationRate n (m n)) :
    Tendsto (fun n => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
      (normalMaxThreshold (m n))/boundedLowerScale n (m n)) atTop (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
  apply familyGlobal_discrepancy_div_scale hm (fun n => C*lowerMaximumApproximationRate n (m n))
    (fun n => boundedLowerScale n (m n)) (eventually_boundedLowerScale_pos hmTop)
    (Eventually.of_forall (fun n => mul_nonneg hC (lowerMaximumApproximationRate_nonneg _ _))) hCDF
  · simpa only [mul_div_assoc,mul_zero] using
      (tendsto_lowerMaximumApproximationRate_div_boundedScale hmTop hsmall).const_mul C
  · exact boundedFamily_global_remainder_tendsto hm hmTop hsmall
  · exact tendsto_boundedFamily_leading_comparison_ratio hm hmTop hsmall

theorem amplifiedFamily_global_remainder_bound
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0))
    (hθ : ∀ᶠ n in atTop,(P n).theta=(boundedFamilyParameters n (m n)).theta)
    (hπ : ∀ᶠ n in atTop,(P n).pi=(boundedFamilyParameters n (m n)).pi) :
    ∀ᶠ n in atTop,
      (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*familyShiftSecondMoments (P n) n (m n)/
        amplifiedSymmetricLowerScale (P n) n (m n)≤
      (2*gaussianMaximumCurvatureConstant*(3+4*Real.exp (11/2)))*
        (familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*Real.sqrt (Real.log (m n:ℝ)^3/n)) := by
  let C := gaussianMaximumCurvatureConstant
  let M := 3+4*Real.exp (11/2)
  have hC : 0≤C := gaussianMaximumCurvatureConstant_pos.le
  have hlog : Tendsto (fun n => Real.log (m n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),hθ,hπ,
    eventually_boundedFamily_shift_second_moment_budget_printed hm hmTop hsmall,eventually_ge_atTop 1] with n hL hnθ hnπ hMom hn
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hd : 0<boundedLowerScale n (m n) := by unfold boundedLowerScale; positivity
  have hk := familyShiftAmplification_pos (P n) (boundedFamilyParameters n (m n))
  have hDim : dimensionLog (m n)≤2*Real.log (m n:ℝ) := by
    rw [dimensionLog_eq_one_add_log (by have := hm n; omega)]
    linarith
  have hCost : gaussianMaximumCurvatureConstant*dimensionLog (m n)/2≤C*Real.log (m n:ℝ) := by
    dsimp only [C]; nlinarith [mul_le_mul_of_nonneg_left hDim hC]
  have hprod := mul_le_mul hCost hMom (familyShiftSecondMoments_nonneg _ _ _) (by positivity : 0≤C*Real.log (m n:ℝ))
  have hb := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod hd.le) hk.le
  rw [familyShiftSecondMoments_amplification _ _ hnθ hnπ]
  unfold amplifiedSymmetricLowerScale
  calc
    _=familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*
        ((gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*
          familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n)/boundedLowerScale n (m n)) := by
      field_simp [hd.ne',hk.ne']; ring
    _≤familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*
        ((C*Real.log (m n:ℝ))*(M*Real.log (m n:ℝ)^2/n)/boundedLowerScale n (m n)) := hb
    _=_ := by
      rw [show (C*Real.log (m n:ℝ))*(M*Real.log (m n:ℝ)^2/n)/boundedLowerScale n (m n)=
        C*M*((Real.log (m n:ℝ)^3/n)/(Real.log (m n:ℝ)^(3/2:ℝ)/(2*Real.sqrt n))) by unfold boundedLowerScale; ring]
      rw [lower_cubic_remainder_ratio_identity (by linarith) hN]
      dsimp only [C,M]
      ring

theorem amplifiedFamily_global_discrepancy_from_CDF
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0))
    (hθ : ∀ᶠ n in atTop,(P n).theta=(boundedFamilyParameters n (m n)).theta)
    (hπ : ∀ᶠ n in atTop,(P n).pi=(boundedFamilyParameters n (m n)).pi)
    (hk : ∀ᶠ n in atTop,1≤familyShiftAmplification (P n) (boundedFamilyParameters n (m n)))
    (hksmall : Tendsto (fun n => familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*
      Real.sqrt (Real.log (m n:ℝ)^3/n)) atTop (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hCDF : ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤
        C*lowerMaximumApproximationRate n (m n)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))/
      amplifiedSymmetricLowerScale (P n) n (m n)) atTop (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
  have hd : ∀ᶠ n in atTop,0<amplifiedSymmetricLowerScale (P n) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact amplifiedSymmetricLowerScale_pos (P n) hn (hm n)
  apply familyGlobal_discrepancy_div_scale hm (fun n => C*lowerMaximumApproximationRate n (m n))
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
  · apply (tendsto_boundedFamily_leading_comparison_ratio hm hmTop hsmall).congr'
    filter_upwards [hθ,hπ,eventually_boundedLowerScale_pos hmTop] with n hnθ hnπ hd
    rw [familyShiftMeanDifference_amplification _ _ hnθ hnπ]
    unfold amplifiedSymmetricLowerScale
    field_simp [hd.ne',(familyShiftAmplification_pos (P n) (boundedFamilyParameters n (m n))).ne']
    ring

theorem rareFamily_global_discrepancy_from_CDF
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
    (hV : Tendsto (fun n => Real.log (m n:ℝ)*(P n).variance*(1+Real.log (m n:ℝ))/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hCDF : ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤
        C*lowerMaximumApproximationRate n (m n)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))/
      familyRareLowerScale (P n) n (m n)) atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  have hd : ∀ᶠ n in atTop,0<familyRareLowerScale (P n) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact familyRareLowerScale_pos (P n) hn (hm n)
  apply familyGlobal_discrepancy_div_scale hm (fun n => C*lowerMaximumApproximationRate n (m n))
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
  · exact tendsto_familyRare_leading_comparison_ratio hm hmTop hk hcover hv hcoef

end
end RectangleCLT.Companion.SplitV4.Printed
