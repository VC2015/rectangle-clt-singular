import RectangleCLTCompanion.SplitV4.Printed.OrliczTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Main-text arithmetic following Corollaries 1 and 2. Polynomial
dimension growth means two-sided comparison with `n^a`; no convergence
of the multiplicative dimension factor is required. -/

open Filter Asymptotics
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def PolynomialDimensionGrowth (p : ℕ → ℕ) (a : ℝ) : Prop :=
  ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
    c*(n : ℝ)^a≤(p n : ℝ) ∧ (p n : ℝ)≤C*(n : ℝ)^a

private theorem log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem polynomial_dimension_log_ratio {p : ℕ → ℕ} {a : ℝ}
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => Real.log (p n : ℝ)/Real.log (n : ℝ)) atTop (𝓝 a) := by
  obtain ⟨c,C,hc,hC,hg⟩ := hg
  have hlo := ((tendsto_const_nhds (x:=Real.log c)).div_atTop log_nat_atTop).add_const a
  have hhi := ((tendsto_const_nhds (x:=Real.log C)).div_atTop log_nat_atTop).add_const a
  simp only [zero_add] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hg,eventually_ge_atTop 2] with n hn hnn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
    have hh := Real.log_le_log (mul_pos hc (Real.rpow_pos_of_pos hn0 _)) hn.1
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hn0 _).ne',Real.log_rpow hn0] at hh
    have hh' := div_le_div_of_nonneg_right hh hln.le
    convert hh' using 1 <;> field_simp [hln.ne'] <;> ring
  · filter_upwards [hg,eventually_ge_atTop 2] with n hn hnn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
    have hp0 : (0:ℝ)<p n := (mul_pos hc (Real.rpow_pos_of_pos hn0 _)).trans_le hn.1
    have hh := Real.log_le_log hp0 hn.2
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn0 _).ne',Real.log_rpow hn0] at hh
    have hh' := div_le_div_of_nonneg_right hh hln.le
    convert hh' using 1 <;> field_simp [hln.ne'] <;> ring

theorem polynomial_dimension_dimensionLog_ratio {p : ℕ → ℕ} {a : ℝ}
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => dimensionLog (p n)/Real.log (n : ℝ)) atTop (𝓝 a) := by
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop log_nat_atTop).add
    (polynomial_dimension_log_ratio hg)
  simp only [zero_add] at hh
  apply hh.congr'
  obtain ⟨c,C,hc,hC,hg⟩ := hg
  filter_upwards [hg,eventually_ge_atTop 1] with n hn hnn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp0 : (0:ℝ)<p n := (mul_pos hc (Real.rpow_pos_of_pos hn0 _)).trans_le hn.1
  have hp : 1≤p n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hp0.ne'))
  rw [dimensionLog_eq_one_add_log hp,add_div]

theorem dimensionLog_nat_log_ratio :
    Tendsto (fun n : ℕ => dimensionLog n/Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hh := (((tendsto_const_nhds (x:=(1:ℝ))).div_atTop log_nat_atTop).add_const 1)
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [dimensionLog_eq_one_add_log (by omega),add_div,div_self (Real.log_pos (by exact_mod_cast hn)).ne']

/-- A quantity comparable with log n has a logarithm negligible relative
to log n. This is the log-log calculation used in both corollaries. -/
theorem log_ratio_negligible_of_log_scale {L : ℕ → ℝ} {a : ℝ} (ha : 0<a)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => Real.log (L n)/Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hl := (Real.continuousAt_log ha.ne').tendsto.comp hL
  have hl0 := hl.div_atTop log_nat_atTop
  have hll := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp log_nat_atTop
  have hh := hl0.add hll
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hnn
  have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
  have hLn0 : 0<L n := (div_pos_iff_of_pos_right hln).mp ((half_pos ha).trans hLn)
  simp only [Function.comp_apply,id_eq]
  rw [Real.log_div hLn0.ne' hln.ne',sub_div]
  ring

def observationLogEnvelope (K : ℝ) (k n : ℕ) : ℝ :=
  K*(dimensionLog n)^k/Real.sqrt n
def observationLogTemplate (k n : ℕ) : ℝ :=
  (Real.log (n : ℝ))^(k+2)/Real.sqrt n

private theorem correction_log_identity {K L : ℝ} (hK : 0<K) (hL : 0<L)
    {n : ℕ} (hn : 1≤n) (k : ℕ) :
    Real.log (1/(observationLogEnvelope K k n*Real.sqrt L))=
      Real.log (n : ℝ)/2-Real.log K-(k : ℝ)*Real.log (dimensionLog n)-Real.log L/2 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he0 : 0<dimensionLog n := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  unfold observationLogEnvelope
  rw [Real.log_div one_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero hK.ne' (pow_ne_zero _ he0.ne'))
    (Real.sqrt_pos.mpr hn0).ne') (Real.sqrt_pos.mpr hL).ne'),Real.log_one,
    Real.log_mul (div_ne_zero (mul_ne_zero hK.ne' (pow_ne_zero _ he0.ne')) (Real.sqrt_pos.mpr hn0).ne')
      (Real.sqrt_pos.mpr hL).ne',
    Real.log_div (mul_ne_zero hK.ne' (pow_ne_zero _ he0.ne')) (Real.sqrt_pos.mpr hn0).ne',
    Real.log_mul hK.ne' (pow_ne_zero _ he0.ne'),Real.log_pow,Real.log_sqrt hn0.le,Real.log_sqrt hL.le]
  ring

theorem observation_correction_log_ratio {L : ℕ → ℝ} {a K : ℝ} (ha : 0<a) (hK : 0<K)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => Real.log (1/(observationLogEnvelope K k n*Real.sqrt (L n)))/Real.log (n : ℝ))
      atTop (𝓝 (1/2 : ℝ)) := by
  have hlogL := log_ratio_negligible_of_log_scale ha hL
  have hloge := log_ratio_negligible_of_log_scale (by norm_num : (0:ℝ)<1) dimensionLog_nat_log_ratio
  have hh := (((tendsto_const_nhds (x:=(1/2:ℝ))).sub
    ((tendsto_const_nhds (x:=Real.log K)).div_atTop log_nat_atTop)).sub
      (hloge.const_mul (k : ℝ))).sub (hlogL.div_const 2)
  simp only [sub_zero,mul_zero,zero_div] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hnn
  have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
  have hLn0 : 0<L n := (div_pos_iff_of_pos_right hln).mp ((half_pos ha).trans hLn)
  rw [correction_log_identity hK hLn0 (by omega) k]
  field_simp [hln.ne']
  <;> ring

theorem observation_D_log_ratio {L : ℕ → ℝ} {a K : ℝ} (ha : 0<a) (hK : 0<K)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => D_L (observationLogEnvelope K k n) (L n)/Real.log (n : ℝ))
      atTop (𝓝 (1/2 : ℝ)) := by
  have hl := observation_correction_log_ratio ha hK hL k
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop log_nat_atTop).add hl
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hl.eventually (eventually_gt_nhds (by norm_num : (1/4:ℝ)<1/2)),eventually_ge_atTop 2] with n hLn hnn
  have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
  have hpos : 0<Real.log (1/(observationLogEnvelope K k n*Real.sqrt (L n))) :=
    (div_pos_iff_of_pos_right hln).mp ((by norm_num : (0:ℝ)<1/4).trans hLn)
  simp only [D_L,logPlus,max_eq_right hpos.le,add_div]

/-- The bounded (`k=0`) and clipped sub-exponential (`k=1`) raw rates,
with their exact nonzero leading constants. -/
theorem observation_rate_log_asymptotic {L : ℕ → ℝ} {a K : ℝ} (ha : 0<a) (hK : 0<K)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => unrestrictedRate (observationLogEnvelope K k n) (L n)/
      observationLogTemplate k n) atTop (𝓝 (K*a^(3/2:ℝ)*Real.sqrt (1/2:ℝ))) := by
  have hD := (Real.continuous_sqrt.continuousAt.tendsto.comp (observation_D_log_ratio ha hK hL k))
  have hh := ((((dimensionLog_nat_log_ratio.pow k).mul
    (hL.rpow_const (p:=(3/2:ℝ)) (Or.inl ha.ne'))).mul hD).const_mul K)
  simp only [one_pow,one_mul] at hh
  rw [←mul_assoc] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hnn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnn)
  have hLn0 : 0<L n := (div_pos_iff_of_pos_right hln).mp ((half_pos ha).trans hLn)
  have hlnR : (Real.log (n : ℝ))^(3/2:ℝ)≠0 := (Real.rpow_pos_of_pos hln _).ne'
  have hlnS : Real.sqrt (Real.log (n : ℝ))≠0 := (Real.sqrt_pos.mpr hln).ne'
  have hp : (Real.log (n : ℝ))^(3/2:ℝ)*Real.sqrt (Real.log (n : ℝ))=(Real.log (n : ℝ))^2 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hln]
    norm_num only [show (3/2:ℝ)+1/2=2 by norm_num,Real.rpow_two]
  have hpk : (Real.log (n : ℝ))^k*(Real.log (n : ℝ))^(3/2:ℝ)*Real.sqrt (Real.log (n : ℝ))=
      (Real.log (n : ℝ))^(k+2) := by rw [mul_assoc,hp,pow_add]
  dsimp only [Function.comp_apply]
  rw [div_pow,Real.div_rpow hLn0.le hln.le,Real.sqrt_div (D_L_nonneg _ _)]
  unfold unrestrictedRate observationLogEnvelope observationLogTemplate
  rw [←hpk]
  field_simp [(Real.sqrt_pos.mpr hn0).ne',pow_ne_zero k hln.ne',hlnR,hlnS]
  <;> ring

theorem observation_log_template_tendsto_zero (k : ℕ) :
    Tendsto (observationLogTemplate k) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop ((k+2 : ℕ) : ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  simpa only [observationLogTemplate,Function.comp_def,
    Real.rpow_natCast,←Real.sqrt_eq_rpow] using hh

theorem observation_saturated_rate_log_asymptotic {L : ℕ → ℝ} {a K : ℝ} (ha : 0<a) (hK : 0<K)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => min 1 (unrestrictedRate (observationLogEnvelope K k n) (L n))/
      observationLogTemplate k n) atTop (𝓝 (K*a^(3/2:ℝ)*Real.sqrt (1/2:ℝ))) := by
  have hr := observation_rate_log_asymptotic ha hK hL k
  have hz := hr.mul (observation_log_template_tendsto_zero k)
  simp only [mul_zero] at hz
  have hz' : Tendsto (fun n => unrestrictedRate (observationLogEnvelope K k n) (L n)) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have ht : observationLogTemplate k n≠0 := by
      unfold observationLogTemplate
      exact div_ne_zero (pow_ne_zero _ (Real.log_pos (by exact_mod_cast hn)).ne')
        (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
    exact div_mul_cancel₀ _ ht
  apply hr.congr'
  filter_upwards [hz'.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn
  rw [min_eq_right hn]

theorem bounded_polynomial_dimension_rate {p : ℕ → ℕ} {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n : ℕ => min 1 (unrestrictedRate (B/Real.sqrt n) (dimensionLog (p n)))/
      ((Real.log (n : ℝ))^2/Real.sqrt n)) atTop
      (𝓝 (B*a^(3/2:ℝ)*Real.sqrt (1/2:ℝ))) := by
  simpa only [observationLogEnvelope,observationLogTemplate,pow_zero,mul_one,zero_add] using
    observation_saturated_rate_log_asymptotic ha hB (polynomial_dimension_dimensionLog_ratio hg) 0

theorem subexponential_polynomial_dimension_rate {p : ℕ → ℕ} {a K : ℝ} (ha : 0<a) (hK : 0<K)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => min 1 (unrestrictedRate (K*dimensionLog n/Real.sqrt n) (dimensionLog (p n)))/
      ((Real.log (n : ℝ))^3/Real.sqrt n)) atTop
      (𝓝 (K*a^(3/2:ℝ)*Real.sqrt (1/2:ℝ))) := by
  simpa only [observationLogEnvelope,observationLogTemplate,pow_one] using
    observation_saturated_rate_log_asymptotic ha hK (polynomial_dimension_dimensionLog_ratio hg) 1

theorem polynomial_dimension_log_factor {p : ℕ → ℕ} {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n : ℕ => Real.sqrt (D_L (B/Real.sqrt n) (dimensionLog (p n)))/Real.sqrt (Real.log (n : ℝ)))
      atTop (𝓝 (Real.sqrt (1/2:ℝ))) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    (observation_D_log_ratio ha hB (polynomial_dimension_dimensionLog_ratio hg) 0)
  apply hh.congr
  intro n
  simp only [Function.comp_apply,observationLogEnvelope,pow_zero,mul_one]
  rw [Real.sqrt_div (D_L_nonneg _ _)]

end
end RectangleCLT.Companion.SplitV4.Printed
