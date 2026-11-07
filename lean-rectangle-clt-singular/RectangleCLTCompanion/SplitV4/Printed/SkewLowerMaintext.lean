import RectangleCLTCompanion.SplitV4.Printed.SkewLowerMeanValue
import RectangleCLTCompanion.SplitV4.Printed.ObservationRates

/-! The main-text sharpness consequence at frozen lines 207--217,
including the harmless replacement of log p by log(ep). -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def skewMaintextScale (B : ℝ) (p n : ℕ) : ℝ := (B/Real.sqrt n)*dimensionLog p^(3/2:ℝ)

theorem skewMaintextScale_div_rate {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀n,2≤B n) (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => skewMaintextScale (B n) (p n) n/lowerSkewRate (B n) (p n) n)
      atTop (𝓝 1) := by
  have hh := (dimensionLog_nat_log_ratio.comp hp).rpow_const (p:=(3/2:ℝ)) (Or.inl (by norm_num : (1:ℝ)≠0))
  rw [Real.one_rpow] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with n hpn hn
  have hlog : 0<Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hpn)
  have hL : 0<dimensionLog (p n) := zero_lt_one.trans_le (log_exp_mul_nat_ge_one (by omega))
  have hBn : B n≠0 := by have := hB n; linarith
  have hN : Real.sqrt (n : ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
  simp only [Function.comp_apply]
  rw [Real.div_rpow hL.le hlog.le]
  unfold skewMaintextScale lowerSkewRate
  field_simp [hBn,hN,(Real.rpow_pos_of_pos hlog (3/2:ℝ)).ne']
  <;> ring

theorem skew_rate_tendsto_zero_of_maintext_scale {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀n,2≤B n) (hp : Tendsto p atTop atTop)
    (hs : Tendsto (fun n => skewMaintextScale (B n) (p n) n) atTop (𝓝 0)) :
    Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0) := by
  have hh := hs.div (skewMaintextScale_div_rate hB hp) (by norm_num : (1:ℝ)≠0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with n hpn hn
  have hsp : 0<skewMaintextScale (B n) (p n) n := by
    unfold skewMaintextScale
    exact mul_pos (div_pos (by have := hB n; linarith)
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))))
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_exp_mul_nat_ge_one (by omega))) _)
  simp only [Pi.div_apply]
  rw [div_div_cancel₀ hsp.ne']

/-- A concrete positive lower constant in the `B L^(3/2)/sqrt n` scale
used in the introduction. Its probability input is the new F.1 route. -/
theorem skew_maintext_sharpness_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀n,2≤B n) (hp : Tendsto p atTop atTop)
    (hs : Tendsto (fun n => skewMaintextScale (B n) (p n) n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,(Real.sqrt 2/(16*Real.exp 1))*skewMaintextScale (B n) (p n) n≤
      lowerConstructionDistance (B n) n (p n) := by
  have hr := skew_rate_tendsto_zero_of_maintext_scale hB hp hs
  have hratio := (tendsto_const_nhds (x:=(1:ℝ))).div (skewMaintextScale_div_rate hB hp) (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at hratio
  have hD := skew_full_distance_eventual_lower_from_F1 hB hp hr
    (c:=Real.sqrt 2/(8*Real.exp 1)) (by
      exact div_lt_div_of_pos_left (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
        (by positivity : (0:ℝ)<4*Real.exp 1) (by have := Real.exp_pos 1; linarith))
  filter_upwards [hD,hratio.eventually (eventually_ge_nhds (by norm_num : (1/2:ℝ)<1)),
    lowerSkewRate_eventually_pos hB hp,hp.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1]
    with n hDn hrat hrn hpn hn
  have hsp : 0<skewMaintextScale (B n) (p n) n := by
    unfold skewMaintextScale
    exact mul_pos (div_pos (by have := hB n; linarith)
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))))
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le (log_exp_mul_nat_ge_one (by omega))) _)
  simp only [Pi.div_apply] at hrat
  rw [one_div_div] at hrat
  have hm := mul_le_mul hDn.le hrat (by norm_num : (0:ℝ)≤1/2)
    (div_nonneg (lowerConstructionDistance_nonneg _ _ _) hrn.le)
  rw [div_mul_div_cancel₀ hrn.ne'] at hm
  have hh : Real.sqrt 2/(16*Real.exp 1)≤lowerConstructionDistance (B n) n (p n)/skewMaintextScale (B n) (p n) n := by
    convert hm using 1 <;> ring
  exact (le_div_iff₀ hsp).mp hh

end
end RectangleCLT.Companion.SplitV4.Printed
