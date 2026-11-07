import RectangleCLTCompanion.SplitV4.MaskedFourthLowerCalibrationScales

/-! Deterministic logarithmic mask asymptotics and genuine rounded-count
coverage. The sparse mask probability is an actual positive scalar formula. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseMaskPi (K r : ℝ) : ℝ := (1/K^2)*(4*maskedFourthLog K)^r

theorem tendsto_sparseMaskLog (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => maskedFourthLog (K n)) atTop atTop := by
  have hh : Tendsto (fun n => 2*(K n)^2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hK).const_mul_atTop (by norm_num)
  exact Real.tendsto_log_atTop.comp hh

theorem tendsto_sparseMaskLog_rpow_div_rpow (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (r s : ℝ) (hs : 0 < s) :
    Tendsto (fun n => maskedFourthLog (K n)^r/(K n)^s) atTop (𝓝 0) := by
  have hY : Tendsto (fun n => 2*(K n)^2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hK).const_mul_atTop (by norm_num)
  have hh := (isLittleO_log_rpow_rpow_atTop r (half_pos hs)).tendsto_div_nhds_zero.comp hY
  have hh' : Tendsto (fun n => 2^(s/2)*(maskedFourthLog (K n)^r/(2*(K n)^2)^(s/2))) atTop (𝓝 0) := by
    simpa only [maskedFourthLog, mul_zero] using (tendsto_const_nhds (x := (2 : ℝ)^(s/2))).mul hh
  apply hh'.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  have hpow : (2*(K n)^2)^(s/2) = 2^(s/2)*(K n)^s := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 2
    ring
  rw [hpow]
  have h2NZ := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (s/2)).ne'
  field_simp
  <;> ring

theorem tendsto_sparseMask_loglog_ratio (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => Real.log (4*maskedFourthLog (K n))/maskedFourthLog (K n)) atTop (𝓝 0) := by
  have hΛ := tendsto_sparseMaskLog K hK
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hΛ
  have hc : Tendsto (fun n => Real.log 4/maskedFourthLog (K n)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hΛ
  have hh : Tendsto (fun n => Real.log 4/maskedFourthLog (K n)+Real.log (maskedFourthLog (K n))/maskedFourthLog (K n)) atTop (𝓝 0) := by
    simpa using hc.add hlog
  apply hh.congr'
  filter_upwards [hΛ.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hn.ne', add_div]

theorem sparseMaskPi_pos {K : ℝ} (hK : 2 ≤ K) (r : ℝ) : 0 < sparseMaskPi K r := by
  unfold sparseMaskPi
  have hΛ : 0 < maskedFourthLog K := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos (mul_pos (by norm_num) hΛ) _)

theorem sparseMaskPi_log_identity {K : ℝ} (hK : 2 ≤ K) (r : ℝ) :
    sparseMaskPi K r*maskedFourthLog K =
      4^r*(maskedFourthLog K^(r+1)/K^2) := by
  have hΛ : 0 < maskedFourthLog K := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  unfold sparseMaskPi
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hΛ.le,
    Real.rpow_add hΛ, Real.rpow_one]
  ring

theorem tendsto_sparseMaskPi_log (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) (r : ℝ) :
    Tendsto (fun n => sparseMaskPi (K n) r*maskedFourthLog (K n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 4^r*(maskedFourthLog (K n)^(r+1)/(K n)^2)) atTop (𝓝 0) := by
    have hp := tendsto_sparseMaskLog_rpow_div_rpow K hK (r+1) 2 (by norm_num)
    simpa only [Real.rpow_two, mul_zero] using (tendsto_const_nhds (x := (4 : ℝ)^r)).mul hp
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
  exact (sparseMaskPi_log_identity hn r).symm

theorem tendsto_sparseMaskPi (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) (r : ℝ) :
    Tendsto (fun n => sparseMaskPi (K n) r) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_sparseMaskPi_log K hK r)
  · filter_upwards [hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    exact (sparseMaskPi_pos hn r).le
  · filter_upwards [hK.eventually (eventually_ge_atTop (2 : ℝ)),
      (tendsto_sparseMaskLog K hK).eventually (eventually_ge_atTop (1 : ℝ))] with n hn hnΛ
    exact le_mul_of_one_le_right (sparseMaskPi_pos hn r).le hnΛ

theorem sparseMask_log_inverse_identity {K : ℝ} (hK : 2 ≤ K) (r : ℝ) :
    Real.log (2/sparseMaskPi K r) = maskedFourthLog K-r*Real.log (4*maskedFourthLog K) := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hΛ : 0 < maskedFourthLog K := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (sparseMaskPi_pos hK r).ne']
  unfold sparseMaskPi
  rw [Real.log_mul (div_ne_zero one_ne_zero (pow_pos hK0 2).ne')
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hΛ) r).ne',
    Real.log_div one_ne_zero (pow_pos hK0 2).ne', Real.log_one,
    Real.log_rpow (mul_pos (by norm_num) hΛ)]
  unfold maskedFourthLog
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hK0 2).ne', Real.log_pow]
  norm_num
  <;> ring

theorem tendsto_sparseMask_log_inverse_ratio (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) (r : ℝ) :
    Tendsto (fun n => Real.log (2/sparseMaskPi (K n) r)/maskedFourthLog (K n)) atTop (𝓝 1) := by
  have hh : Tendsto (fun n => 1-r*(Real.log (4*maskedFourthLog (K n))/maskedFourthLog (K n))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := r)).mul (tendsto_sparseMask_loglog_ratio K hK))
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
  rw [sparseMask_log_inverse_identity hn]
  have hΛNZ : maskedFourthLog (K n) ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hn).1).ne'
  field_simp

end
end RectangleCLT.Companion.SplitV4
