import RectangleCLTCompanion.SplitV4.Printed.LowerMaster
import RectangleCLTCompanion.SplitV4.SymmetricBoundedRademacher

/-! Explicit numerical remainders in the printed global maximum route.
These contain no actual probability discrepancies as assumptions. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def lowerMaximumApproximationRate (n m : ℕ) : ℝ :=
  Real.sqrt (dimensionLog m)/Real.sqrt n+(dimensionLog m)^2/n

theorem lowerMaximumApproximationRate_nonneg (n m : ℕ) : 0≤lowerMaximumApproximationRate n m := by
  unfold lowerMaximumApproximationRate
  positivity

theorem lowerMaximumApproximationRate_le {n m : ℕ} (hL : 1≤Real.log (m:ℝ)) :
    lowerMaximumApproximationRate n m≤4*(Real.sqrt (Real.log (m:ℝ))/Real.sqrt n+Real.log (m:ℝ)^2/n) := by
  have hm : 1≤m := by
    by_contra hn
    have he : m=0 := by omega
    norm_num [he] at hL
  have hdim : dimensionLog m≤2*Real.log (m:ℝ) := by
    rw [dimensionLog_eq_one_add_log hm]
    linarith
  have hs : Real.sqrt (dimensionLog m)≤2*Real.sqrt (Real.log (m:ℝ)) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt (by linarith : 0≤Real.log (m:ℝ))]
      linarith
  have hd0 : 0≤dimensionLog m := zero_le_one.trans (log_exp_mul_nat_ge_one hm)
  have hp := pow_le_pow_left₀ hd0 hdim 2
  norm_num only [mul_pow] at hp
  have h₁ := div_le_div_of_nonneg_right hs (Real.sqrt_nonneg (n:ℝ))
  have h₂ := div_le_div_of_nonneg_right hp (Nat.cast_nonneg n : (0:ℝ)≤n)
  rw [mul_div_assoc] at h₁ h₂
  unfold lowerMaximumApproximationRate
  have hr : 0≤Real.sqrt (Real.log (m:ℝ))/Real.sqrt n := by positivity
  nlinarith

theorem tendsto_lowerMaximumApproximationRate_div_boundedScale
    {m : ℕ→ℕ} (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0)) :
    Tendsto (fun n => lowerMaximumApproximationRate n (m n)/boundedLowerScale n (m n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (m n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hbase := (tendsto_lower_comparison_remainder_div_rate hlog hsmall).const_mul 8
  simp only [mul_zero] at hbase
  apply squeeze_zero' _ _ hbase
  · filter_upwards [eventually_boundedLowerScale_pos hmTop] with n hn
    exact div_nonneg (lowerMaximumApproximationRate_nonneg _ _) hn.le
  · filter_upwards [hlog.eventually (eventually_ge_atTop 1),eventually_boundedLowerScale_pos hmTop] with n hL hd
    have hh := div_le_div_of_nonneg_right (lowerMaximumApproximationRate_le (n:=n) hL) hd.le
    exact hh.trans_eq (by unfold boundedLowerScale; ring)

theorem tendsto_lowerDimensionLog_div_sqrt {m : ℕ→ℕ} (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0)) :
    Tendsto (fun n => dimensionLog (m n)/Real.sqrt n) atTop (𝓝 0) := by
  have he := (tendsto_lowerMaximumApproximationRate_div_boundedScale hmTop hsmall).mul
    (tendsto_boundedLowerScale_zero hmTop hsmall)
  simp only [mul_zero] at he
  have hRate : Tendsto (fun n => lowerMaximumApproximationRate n (m n)) atTop (𝓝 0) := by
    apply he.congr'
    filter_upwards [eventually_boundedLowerScale_pos hmTop] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  have hsq : Tendsto (fun n => (dimensionLog (m n))^2/n) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => by positivity) _ hRate
    intro n
    unfold lowerMaximumApproximationRate
    have hn : 0≤Real.sqrt (dimensionLog (m n))/Real.sqrt n := by positivity
    linarith
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [hmTop.eventually (eventually_ge_atTop 1)] with n hm
  change Real.sqrt ((dimensionLog (m n))^2/n)=dimensionLog (m n)/Real.sqrt n
  have hdim : 0≤dimensionLog (m n) := zero_le_one.trans (log_exp_mul_nat_ge_one hm)
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hdim]

theorem boundedFamily_global_remainder_tendsto
    {m : ℕ→ℕ} [∀n,NeZero (m n)] (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (m n:ℝ)^3/n) atTop (𝓝 0)) :
    Tendsto (fun n => (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*
      familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n)/boundedLowerScale n (m n)) atTop (𝓝 0) := by
  let C := gaussianMaximumCurvatureConstant
  let M := 3+4*Real.exp (11/2)
  have hC : 0≤C := gaussianMaximumCurvatureConstant_pos.le
  have hup : Tendsto (fun n => 2*C*M*Real.sqrt (Real.log (m n:ℝ)^3/n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero,Function.comp_apply] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsmall).const_mul (2*C*M)
  have hlog : Tendsto (fun n => Real.log (m n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply squeeze_zero' _ _ hup
  · filter_upwards [eventually_boundedLowerScale_pos hmTop] with n hd
    exact div_nonneg (mul_nonneg (by
      have hd0 := zero_le_one.trans (log_exp_mul_nat_ge_one (show 1≤m n by have := hm n; omega))
      positivity) (familyShiftSecondMoments_nonneg _ _ _)) hd.le
  · filter_upwards [hlog.eventually (eventually_ge_atTop 1),
      eventually_boundedFamily_shift_second_moment_budget_printed hm hmTop hsmall,
      eventually_boundedLowerScale_pos hmTop,eventually_ge_atTop 1] with n hL hMom hd hn
    have hN : (0:ℝ)<n := by exact_mod_cast hn
    have hDim : dimensionLog (m n)≤2*Real.log (m n:ℝ) := by
      rw [dimensionLog_eq_one_add_log (by have := hm n; omega)]
      linarith
    have hCost : gaussianMaximumCurvatureConstant*dimensionLog (m n)/2≤C*Real.log (m n:ℝ) := by
      dsimp only [C]; nlinarith [mul_le_mul_of_nonneg_left hDim hC]
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul hCost hMom (familyShiftSecondMoments_nonneg _ _ _) (by positivity : 0≤C*Real.log (m n:ℝ))) hd.le
    apply hh.trans_eq
    change (C*Real.log (m n:ℝ))*(M*Real.log (m n:ℝ)^2/n)/boundedLowerScale n (m n)=_
    rw [show (C*Real.log (m n:ℝ))*(M*Real.log (m n:ℝ)^2/n)/boundedLowerScale n (m n)=
      C*M*((Real.log (m n:ℝ)^3/n)/(Real.log (m n:ℝ)^(3/2:ℝ)/(2*Real.sqrt n))) by unfold boundedLowerScale; ring]
    rw [lower_cubic_remainder_ratio_identity (by linarith) hN]
    ring

end
end RectangleCLT.Companion.SplitV4.Printed
