import RectangleCLTArxivV1.LowerSparseWidthScales

/-! Primitive sparse calibration under the actual two-count width regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem eventually_lowerSparse_logKhat_sub_bound {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop,
      |Real.log (sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) -
        Real.log (lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n))| ≤ lowerSparseLogSlack q := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hnL hn
  exact lowerSparse_logKhat_sub_bound (by omega) (zero_lt_one.trans_le hnL)
    (by linarith [hB n]) (lower_rareLog_le_dimensionLog (hr n) (by have := hrm n; have := hr n; omega))
    (lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL)

theorem tendsto_lowerSparseKhat {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hlogK := Real.tendsto_log_atTop.comp hK
  have hb := eventually_lowerSparse_logKhat_sub_bound hB hr hrm hmTop (q := q)
  have hlogKh : Tendsto (fun n => Real.log (sparseLowerKhat n (Real.log (m n : ℝ)) q (B n))) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [hb,hlogK.eventually (eventually_ge_atTop (a + lowerSparseLogSlack q))] with n hn hna
    simp only [Function.comp_apply] at hna
    linarith [(abs_le.mp hn).1]
  apply (Real.tendsto_exp_atTop.comp hlogKh).congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop 0),eventually_ge_atTop 1] with n hnL hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hBn : 0 < B n := by linarith [hB n]
  apply Real.exp_log
  unfold sparseLowerKhat
  positivity

theorem eventually_lowerSparseLog_bounds {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) atTop atTop) :
    ∀ᶠ n in atTop,
      Real.log (Real.exp 1 + lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) ≤
        sparseLowerLog n (Real.log (m n : ℝ)) q (B n) ∧
      sparseLowerLog n (Real.log (m n : ℝ)) q (B n) ≤
        3 * Real.log (Real.exp 1 + lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) := by
  let K := fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)
  let Kh := fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)
  let C := lowerSparseLogSlack q
  have hKh := tendsto_lowerSparseKhat hB hr hrm hmTop hK
  have hd := (tendsto_log_exp_add_sub_log K hK).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlogK := Real.tendsto_log_atTop.comp hK
  filter_upwards [eventually_lowerSparse_logKhat_sub_bound hB hr hrm hmTop (q := q),hd,
    hlogK.eventually (eventually_ge_atTop (2 * C + 1 + |Real.log 2|)),
    hK.eventually (eventually_ge_atTop 2),hKh.eventually (eventually_ge_atTop 2)]
    with n hn hdn hlogn hkn hkhn
  have hΛ : sparseLowerLog n (Real.log (m n : ℝ)) q (B n) = Real.log 2 + 2 * Real.log (Kh n) := by
    unfold sparseLowerLog maskedFourthLog
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 (by dsimp [Kh]; linarith)),Real.log_pow]
    norm_num [Kh]
  have hpaper : Real.log (K n) ≤ Real.log (Real.exp 1 + K n) :=
    Real.log_le_log (by change 2 ≤ K n at hkn; linarith) (by linarith [Real.exp_pos (1 : ℝ)])
  change |Real.log (Kh n) - Real.log (K n)| ≤ C at hn
  change Real.log (Real.exp 1 + K n) - Real.log (K n) ≤ 1 at hdn
  change 2 * C + 1 + |Real.log 2| ≤ Real.log (K n) at hlogn
  rw [hΛ]
  exact ⟨by linarith [(abs_le.mp hn).1, neg_abs_le (Real.log 2)],
    by linarith [(abs_le.mp hn).2, le_abs_self (Real.log 2)]⟩

theorem tendsto_lowerSparseLog_div_rareLog {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) /
      dimensionLog (r n * m n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerLog n (Real.log (m n : ℝ)) q (B n) / Real.log (m n : ℝ)) atTop (𝓝 0) := by
  let K := fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hKell : Tendsto (fun n => Real.log (K n) / Real.log (m n : ℝ)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => 3 * (Real.log (K n) / dimensionLog (r n * m n))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hsmall.const_mul 3
    apply squeeze_zero' _ _ hupper
    · filter_upwards [hell.eventually (eventually_ge_atTop 1),hK.eventually (eventually_ge_atTop 1)] with n hnL hnK
      exact div_nonneg (Real.log_nonneg hnK) (zero_le_one.trans hnL)
    · filter_upwards [hell.eventually (eventually_ge_atTop 1),hK.eventually (eventually_ge_atTop 1)] with n hnL hnK
      have hd := lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL
      have hdpos : 0 < dimensionLog (r n * m n) := zero_lt_one.trans_le
        (log_exp_mul_nat_ge_one (by nlinarith [hr n,hrm n] : 1 ≤ r n * m n))
      have hh := div_le_div_of_nonneg_left (Real.log_nonneg hnK)
        (div_pos hdpos (by norm_num : (0 : ℝ) < 3)) (show dimensionLog (r n * m n) / 3 ≤ Real.log (m n : ℝ) by linarith)
      convert hh using 1
      ring
  have hdiff := (tendsto_log_exp_add_sub_log K hK).div_atTop hell
  have hpaper : Tendsto (fun n => Real.log (Real.exp 1 + K n) / Real.log (m n : ℝ)) atTop (𝓝 0) := by
    have hh := hKell.add hdiff
    simp only [add_zero] at hh
    apply hh.congr
    intro n
    dsimp
    ring
  have hupper : Tendsto (fun n => 3 * (Real.log (Real.exp 1 + K n) / Real.log (m n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpaper.const_mul 3
  have hKh := tendsto_lowerSparseKhat hB hr hrm hmTop hK
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hell.eventually (eventually_gt_atTop 0),hKh.eventually (eventually_ge_atTop 2)] with n hnL hnK
    have hh := (maskedFourthLog_bounds hnK).1
    change 1 / 2 ≤ sparseLowerLog n (Real.log (m n : ℝ)) q (B n) at hh
    exact div_nonneg (by linarith only [hh]) hnL.le
  · filter_upwards [hell.eventually (eventually_gt_atTop 0),eventually_lowerSparseLog_bounds hB hr hrm hmTop hK]
      with n hnL hnLog
    have hh := div_le_div_of_nonneg_right hnLog.2 hnL.le
    convert hh using 1
    dsimp only [K, Function.comp_apply]
    ring

theorem tendsto_lowerSparseCoordinateWidth {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (_hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => lowerSparseCoordinateWidth n (Real.log (m n : ℝ)) (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0) := by
  let ell := fun n => Real.log (m n : ℝ)
  have hell : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hratio := tendsto_sparseLowerCoordinateRate_div_scale ell B q hell hB hK
  have hh := hratio.mul hsmall
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
    hK.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
  have hpos := sparseLowerScale_pos (by omega : 0 < n) hnL (by linarith [hB n]) hnK
  rw [lowerSparseRawWidth_eq n hnL]
  unfold lowerSparseCoordinateWidth
  dsimp only [ell]
  field_simp [hpos.ne']
  ring

theorem tendsto_lowerSparseEll_cube_div {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0) := by
  let c := Real.sqrt (2 / Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hU := tendsto_lowerSparseCoordinateWidth hB hr hmTop hK hsmall
  have hbound : Tendsto (fun n => lowerSparseCoordinateWidth n (Real.log (m n : ℝ)) (B n)
      (independentAbsGaussianMean (r n)) ^ 4 / (4 * c ^ 4)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0),zero_div] using (hU.pow 4).div_const (4 * c ^ 4)
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [hell.eventually (eventually_gt_atTop 0)] with n hnL
    exact div_nonneg (pow_nonneg hnL.le 3) (Nat.cast_nonneg n)
  · filter_upwards [hell.eventually (eventually_gt_atTop 0)] with n hnL
    exact lowerSparse_cube_div_le_coordinateWidth_fourth hnL (hB n) hc (independentAbsGaussianMean_lower (hr n))

theorem tendsto_lowerSparseTheta {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerTheta n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0) := by
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hEn := tendsto_lower_ell_div_n hell (tendsto_lowerSparseEll_cube_div hB hr hmTop hK hsmall)
  apply squeeze_zero' _ _ hEn
  · filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hK.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
    exact (sparseLowerTheta_pos (by omega) hnL hnK).le
  · filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hK.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
    simp only [Function.comp_apply] at hnL ⊢
    unfold sparseLowerTheta
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    unfold sparseLowerCount
    have hΛ := (maskedFourthLog_bounds hnK).1
    change 1 / 2 ≤ sparseLowerLog n (Real.log (m n : ℝ)) q (B n) at hΛ
    apply (div_le_iff₀ (by linarith : 0 < 4 * sparseLowerLog n (Real.log (m n : ℝ)) q (B n))).mpr
    nlinarith only [hΛ,hnL,mul_nonneg hnL.le (show 0 ≤ 4 * sparseLowerLog n (Real.log (m n : ℝ)) q (B n) - 1 by linarith)]

theorem tendsto_lowerSparseVariance {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerVariance n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0) := by
  have hp : 0 < 2 / q := by positivity
  have htheta := (tendsto_lowerSparseTheta hB hr hmTop hK hsmall).rpow_const (Or.inr hp.le)
  have hh := htheta.div_const 4
  rw [Real.zero_rpow hp.ne',zero_div] at hh
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
    hK.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
  exact (sparseLower_variance_identity (by omega) hnL (by linarith [hB n]) hnK).symm

theorem tendsto_lowerSparseEffectiveAmplitude {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n) *
      sparseLowerCount n (Real.log (m n : ℝ)) q (B n) / Real.log (m n : ℝ)) atTop atTop := by
  let ell := fun n => Real.log (m n : ℝ)
  have hell : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hRatio : Tendsto (fun n => sparseLowerCoordinateRate n (ell n) (B n) / sparseLowerScale n (ell n) q (B n))
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_sparseLowerCoordinateRate_div_scale ell B q hell hB hK, ?_⟩
    filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hK.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
    have hU : 0 < sparseLowerCoordinateRate n (ell n) (B n) := by
      unfold sparseLowerCoordinateRate
      have hBn : 0 < B n := by linarith [hB n]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    exact div_pos hU (sparseLowerScale_pos (by omega) hnL (by linarith [hB n]) hnK)
  have hInverse : Tendsto (fun n => sparseLowerScale n (ell n) q (B n) / sparseLowerCoordinateRate n (ell n) (B n))
      atTop atTop := by
    apply hRatio.inv_tendsto_nhdsGT_zero.congr
    intro n
    exact inv_div _ _
  have hEn := tendsto_lower_ell_div_n hell (tendsto_lowerSparseEll_cube_div hB hr hmTop hK hsmall)
  have hBounded : Tendsto (fun n => sparseLowerScale n (ell n) q (B n) / maskedFourthBoundedScale n (ell n))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hInverse
    filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hK.eventually (eventually_ge_atTop 2),hEn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn hnL hnK hnEn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : ell n ≤ n := (div_le_one hn0).mp hnEn
    have hpos : 0 < maskedFourthBoundedScale n (ell n) := by
      unfold maskedFourthBoundedScale
      positivity
    exact div_le_div_of_nonneg_left (sparseLowerScale_pos (by omega) hnL (by linarith [hB n]) hnK).le hpos
      (sparseLowerCoordinateRate_ge_bounded (by omega) hnL (hB n) hle)
  apply (hBounded.atTop_div_const (by norm_num : (0 : ℝ) < 2)).congr'
  filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0)] with n hn hnL
  have hpow : ell n ^ (3 / 2 : ℝ) = ell n * Real.sqrt (ell n) := by
    rw [Real.sqrt_eq_rpow]
    have hh := Real.rpow_add hnL (1 : ℝ) (1 / 2 : ℝ)
    norm_num at hh
    exact hh
  unfold sparseLowerScale maskedFourthBoundedScale
  rw [hpow]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [(Real.sqrt_pos.mpr hn0).ne',(Real.sqrt_pos.mpr hnL).ne',hnL.ne']
  ring

theorem tendsto_lowerSparseRawWidth {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n * m n)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseIntrinsicRate n (dimensionLog (r n * m n)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0) := by
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hKh := tendsto_lowerSparseKhat hB hr hrm hmTop hK
  have hLogs := eventually_lowerSparseLog_bounds hB hr hrm hmTop hK
  apply squeeze_zero' _ _ hsmall
  · filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hKh.eventually (eventually_ge_atTop 2)] with n hn hnL hnK
    exact (lowerSparseRawWidth_pos (by omega) hnL (by linarith [hB n])
      ((by positivity : 0 < Real.sqrt (2 / Real.pi)).trans_le (independentAbsGaussianMean_lower (hr n))) hnK).le
  · filter_upwards [eventually_ge_atTop 1,hell.eventually (eventually_gt_atTop 0),
      hKh.eventually (eventually_ge_atTop 2),hLogs] with n hn hnL hnK hnLogs
    exact lowerSparseRawWidth_le_intrinsicRate hq (by omega) hnL
      (lower_rareLog_le_dimensionLog (hr n) (by have := hr n; have := hrm n; omega))
      (by linarith [hB n]) (independentAbsGaussianMean_nonneg _) hnK hnLogs.1

end
end RectangleCLTArxivV1
