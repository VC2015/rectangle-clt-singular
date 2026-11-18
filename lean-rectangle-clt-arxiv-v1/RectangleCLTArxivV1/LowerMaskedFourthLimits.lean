import RectangleCLTArxivV1.LowerMaskedFourthScales

/-! Primitive numerical limits for Theorem 6 under its stated width regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem tendsto_lowerMaskedFourthRawWidth {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hsmall : Tendsto (fun n => lowerMaskedFourthIntrinsicRate n (dimensionLog (r n*m n))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hsmall
  · filter_upwards [eventually_ge_atTop 1] with n hn
    unfold lowerMaskedFourthRawWidth
    have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
    exact div_nonneg (mul_nonneg (mul_nonneg (maskedFourthAmplitude_pos (by omega) hL (hB n)).le
      (maskedFourthCount_pos hL (hB n)).le) (independentAbsGaussianMean_nonneg _)) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact lowerMaskedFourthRawWidth_le_intrinsicRate (by omega)
      (Real.log_pos (by exact_mod_cast hm n)) (lower_rareLog_le_dimensionLog (hr n) (by have := hm n; omega))
      (hB n) (independentAbsGaussianMean_nonneg _)

theorem tendsto_lowerMaskedFourthLog_div_rareLog {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hlogSmall : Tendsto (fun n => Real.log (B n)/dimensionLog (r n*m n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hlogB : Tendsto (fun n => Real.log (B n)/Real.log (m n : ℝ)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => 3*(Real.log (B n)/dimensionLog (r n*m n))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlogSmall.const_mul 3
    apply squeeze_zero' _ _ hupper
    · filter_upwards [hlog.eventually (eventually_ge_atTop 1)] with n hnL
      exact div_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ B n by linarith [hB n])) (by linarith)
    · filter_upwards [hlog.eventually (eventually_ge_atTop 1)] with n hnL
      have hdim := lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL
      have hdimpos : 0 < dimensionLog (r n*m n) := zero_lt_one.trans_le
        (log_exp_mul_nat_ge_one (by nlinarith [hr n,hrm n] : 1 ≤ r n*m n))
      have hh := div_le_div_of_nonneg_left (Real.log_nonneg (show (1 : ℝ) ≤ B n by linarith [hB n]))
        (div_pos hdimpos (by norm_num)) (show dimensionLog (r n*m n)/3 ≤ Real.log (m n : ℝ) by linarith)
      convert hh using 1 <;> ring
  have hh := ((tendsto_const_nhds (x := Real.log (2 : ℝ))).div_atTop hlog).add (hlogB.const_mul 2)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    unfold maskedFourthLog
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by have := hB n; positivity : (B n)^2 ≠ 0),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring)

theorem tendsto_lowerMaskedFourthTheta {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hBTop : Tendsto B atTop atTop) (hr : ∀ n, 1 ≤ r n)
    (hmTop : Tendsto m atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthTheta n (Real.log (m n : ℝ)) (B n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hk := tendsto_maskedFourthCount (fun n => Real.log (m n : ℝ)) B hlog hBTop hΛ
  let c := Real.sqrt (2/Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound : Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))^4/c^4) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 4 ≠ 0),zero_div] using (hsmall.pow 4).div_const (c^4)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop 1,hlog.eventually (eventually_gt_atTop 0)] with n hn hnL
    exact (maskedFourthTheta_pos (n := n) (by omega) hnL (hB n)).le
  · filter_upwards [eventually_ge_atTop 1,hlog.eventually (eventually_gt_atTop 0),hk.eventually (eventually_ge_atTop 1)]
      with n hn hnL hnk
    exact lowerMaskedFourthTheta_le_raw_fourth (by omega) hnL (hB n) hc (independentAbsGaussianMean_lower (hr n)) hnk

theorem tendsto_lowerMaskedFourthVariance {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hBTop : Tendsto B atTop atTop) (hr : ∀ n, 1 ≤ r n)
    (hmTop : Tendsto m atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthVariance n (Real.log (m n : ℝ)) (B n)) atTop (𝓝 0) := by
  have hθ := tendsto_lowerMaskedFourthTheta hB hBTop hr hmTop hΛ hsmall
  have hh : Tendsto (fun n => Real.sqrt (maskedFourthTheta n (Real.log (m n : ℝ)) (B n))/4) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_div] using hθ.sqrt.div_const 4
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1,hmTop.eventually (eventually_ge_atTop 2)] with n hn hnm
  exact (maskedFourth_variance_identity (by omega) (Real.log_pos (by exact_mod_cast hnm)) (hB n)).symm

theorem tendsto_lowerMaskedFourthEffectiveAmplitude {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hθ : Tendsto (fun n => maskedFourthTheta n (Real.log (m n : ℝ)) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n)*
      maskedFourthCount (Real.log (m n : ℝ)) (B n)/Real.log (m n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hθgt : Tendsto (fun n => maskedFourthTheta n (Real.log (m n : ℝ)) (B n)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hθ,?_⟩
    filter_upwards [eventually_ge_atTop 1,hlog.eventually (eventually_gt_atTop 0)] with n hn hnL
    exact maskedFourthTheta_pos (n := n) (by omega) hnL (hB n)
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hθgt.inv_tendsto_nhdsGT_zero
  have hp' : Tendsto (fun n => (maskedFourthTheta n (Real.log (m n : ℝ)) (B n))^(-1/4 : ℝ)/16) atTop atTop := by
    have hh := hp.atTop_div_const (by norm_num : (0 : ℝ) < 16)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1,hlog.eventually (eventually_gt_atTop 0)] with n hn hnL
    change ((maskedFourthTheta n (Real.log (m n : ℝ)) (B n))⁻¹)^(1/4 : ℝ)/16 = _
    rw [Real.inv_rpow (maskedFourthTheta_pos (n := n) (by omega) hnL (hB n)).le]
    simp only [neg_div,Real.rpow_neg (maskedFourthTheta_pos (n := n) (by omega) hnL (hB n)).le]
  apply tendsto_atTop_mono' atTop _ hp'
  filter_upwards [eventually_ge_atTop 1,hlog.eventually (eventually_gt_atTop 0)] with n hn hnL
  have hΛ : 0 < maskedFourthLog (B n) := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds (hB n)).1
  have hcoef : (1/16 : ℝ) ≤ B n/(8*maskedFourthLog (B n)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hΛ)).mpr
    linarith [(maskedFourthLog_bounds (hB n)).2]
  have hfactor : maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n)*
      maskedFourthCount (Real.log (m n : ℝ)) (B n)/Real.log (m n : ℝ) =
      (B n/(8*maskedFourthLog (B n)))*(maskedFourthTheta n (Real.log (m n : ℝ)) (B n))^(-1/4 : ℝ) := by
    unfold maskedFourthAmplitude maskedFourthCount
    field_simp
    ring
  rw [hfactor]
  have hh := mul_le_mul_of_nonneg_right hcoef
    (Real.rpow_nonneg (maskedFourthTheta_pos (n := n) (by omega) hnL (hB n)).le (-1/4 : ℝ))
  convert hh using 1 <;> ring

end
end RectangleCLTArxivV1
