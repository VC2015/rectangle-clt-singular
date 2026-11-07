import RectangleCLTCompanion.SplitV4.Printed.WeightedSignExample

/-! Exact asymptotic calibration of the exceptional sqrt(log n) weight
and of the resulting relative-moment gain. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

private theorem w_log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem exceptional_denominator_ratio :
    Tendsto (fun n => exceptionalSignDenominator n/(n : ℝ)) atTop (𝓝 1) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hInv := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop tendsto_natCast_atTop_atTop
  have hh := (hlog.add_const 1).sub hInv
  simp only [zero_add,sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  simp only [Function.comp_apply,id_eq,Pi.div_apply]
  unfold exceptionalSignDenominator
  field_simp [hn0]
  <;> ring

theorem exceptional_envelope_asymptotic :
    Tendsto (fun n => exceptionalSignEnvelope n/Real.sqrt (Real.log (n : ℝ)/n)) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x:=(1:ℝ))).div exceptional_denominator_ratio (by norm_num : (1:ℝ)≠0))
  norm_num only [div_one,Real.sqrt_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  simp only [Function.comp_apply,Pi.div_apply]
  rw [one_div_div,Real.sqrt_div hn0.le,exceptionalSignEnvelope,Real.sqrt_div hlog.le]
  field_simp [(Real.sqrt_pos.mpr hn0).ne',(Real.sqrt_pos.mpr hlog).ne',(Real.sqrt_pos.mpr hden).ne']
  <;> ring

theorem exceptional_envelope_squared_scale :
    Tendsto (fun n : ℕ => (n : ℝ)*(exceptionalSignEnvelope n)^2/Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).div exceptional_denominator_ratio (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  simp only [Pi.div_apply]
  rw [one_div_div]
  unfold exceptionalSignEnvelope
  rw [div_pow,Real.sq_sqrt hlog.le,Real.sq_sqrt hden.le]
  field_simp [hlog.ne']
  <;> ring

theorem exceptional_fourth_asymptotic :
    Tendsto (fun n : ℕ => (n : ℝ)*exceptionalSignFourth n) atTop (𝓝 1) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hInv := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop tendsto_natCast_atTop_atTop
  have hnumer := (hlog.add_const 1).sub hInv
  simp only [zero_add,sub_zero] at hnumer
  have hh := hnumer.div (exceptional_denominator_ratio.pow 2) (by norm_num : (1:ℝ)^2≠0)
  norm_num only [one_pow,div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  simp only [Function.comp_apply,Pi.div_apply]
  rw [Real.rpow_two,Real.rpow_one]
  unfold exceptionalSignFourth
  field_simp [hn0,hden.ne']
  <;> ring

theorem exceptional_log_denominator_ratio :
    Tendsto (fun n => Real.log (exceptionalSignDenominator n)/Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp exceptional_denominator_ratio
  have hh := (hl.div_atTop w_log_nat_atTop).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  simp only [Function.comp_apply,Pi.div_apply]
  rw [Real.log_div hden.ne' hn0.ne']
  field_simp [hlog.ne']
  <;> ring

theorem exceptional_correction_log_ratio {L : ℕ → ℝ} {a : ℝ} (ha : 0<a)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => Real.log (1/(exceptionalSignEnvelope n*Real.sqrt (L n)))/Real.log (n : ℝ))
      atTop (𝓝 (1/2:ℝ)) := by
  have hll := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp w_log_nat_atTop
  have hlogL := log_ratio_negligible_of_log_scale ha hL
  have hh := ((exceptional_log_denominator_ratio.div_const 2).sub (hll.div_const 2)).sub (hlogL.div_const 2)
  norm_num only [zero_div,sub_zero] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  have hLp : 0<L n := (div_pos_iff_of_pos_right hlog).mp ((half_pos ha).trans hLn)
  simp only [Function.comp_apply,id_eq,Pi.div_apply]
  unfold exceptionalSignEnvelope
  rw [Real.log_div one_ne_zero (mul_ne_zero (div_ne_zero (Real.sqrt_pos.mpr hlog).ne' (Real.sqrt_pos.mpr hden).ne')
      (Real.sqrt_pos.mpr hLp).ne'),Real.log_one,
    Real.log_mul (div_ne_zero (Real.sqrt_pos.mpr hlog).ne' (Real.sqrt_pos.mpr hden).ne') (Real.sqrt_pos.mpr hLp).ne',
    Real.log_div (Real.sqrt_pos.mpr hlog).ne' (Real.sqrt_pos.mpr hden).ne',
    Real.log_sqrt hlog.le,Real.log_sqrt hden.le,Real.log_sqrt hLp.le]
  ring

theorem exceptional_D_log_ratio {L : ℕ → ℝ} {a : ℝ} (ha : 0<a)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => D_L (exceptionalSignEnvelope n) (L n)/Real.log (n : ℝ)) atTop (𝓝 (1/2:ℝ)) := by
  have hl := exceptional_correction_log_ratio ha hL
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop w_log_nat_atTop).add hl
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hl.eventually (eventually_gt_nhds (by norm_num : (1/4:ℝ)<1/2)),eventually_ge_atTop 2] with n hln hn
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hpos : 0<Real.log (1/(exceptionalSignEnvelope n*Real.sqrt (L n))) :=
    (div_pos_iff_of_pos_right hlog).mp ((by norm_num : (0:ℝ)<1/4).trans hln)
  simp only [D_L,logPlus,max_eq_right hpos.le,add_div]

theorem exceptional_fourth_correction_ratio {L : ℕ → ℝ} {a : ℝ} (ha : 0<a)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => exceptionalSignFourth n*D_L (exceptionalSignEnvelope n) (L n)/
      (exceptionalSignEnvelope n)^2) atTop (𝓝 (1/2:ℝ)) := by
  have hinv := (tendsto_const_nhds (x:=(1:ℝ))).div exceptional_envelope_squared_scale (by norm_num : (1:ℝ)≠0)
  norm_num only [div_one] at hinv
  have hh := (exceptional_fourth_asymptotic.mul (exceptional_D_log_ratio ha hL)).mul hinv
  norm_num only [one_mul,mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hlog : Real.log (n : ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  have hδ : exceptionalSignEnvelope n≠0 := by
    unfold exceptionalSignEnvelope
    exact div_ne_zero (Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hn))).ne'
      (Real.sqrt_pos.mpr (exceptional_denominator_pos hn)).ne'
  simp only [Pi.div_apply]
  field_simp [hn0,hlog,hδ]
  <;> ring

theorem exceptional_relative_sqrt_ratio {L : ℕ → ℝ} {a : ℝ} (ha : 0<a)
    (hL : Tendsto (fun n => L n/Real.log (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => Real.sqrt (exceptionalSignFourth n*D_L (exceptionalSignEnvelope n) (L n))/
      exceptionalSignEnvelope n) atTop (𝓝 (Real.sqrt (1/2:ℝ))) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (exceptional_fourth_correction_ratio ha hL)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  have hδ : 0<exceptionalSignEnvelope n := div_pos (Real.sqrt_pos.mpr hlog) (Real.sqrt_pos.mpr hden)
  have hs4 : 0≤exceptionalSignFourth n := exceptional_fourth_nonneg (by omega)
  simp only [Function.comp_apply,Pi.div_apply]
  rw [Real.sqrt_div (mul_nonneg hs4 (D_L_nonneg _ _)),Real.sqrt_sq_eq_abs,abs_of_pos hδ]

/-- Exact positive constant in the printed sqrt(log n) improvement. -/
theorem exceptional_logarithmic_gain {p : ℕ → ℕ} {a : ℝ} (ha : 0<a)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => (unrestrictedRate (exceptionalSignEnvelope n) (dimensionLog (p n))/
      relativeRate (exceptionalSignEnvelope n) (exceptionalSignFourth n) (dimensionLog (p n)))/
        Real.sqrt (Real.log (n : ℝ))) atTop
      (𝓝 (Real.sqrt (1/2:ℝ)/(1+Real.sqrt (1/2:ℝ)))) := by
  have hL := polynomial_dimension_dimensionLog_ratio hg
  have hD := Real.continuous_sqrt.continuousAt.tendsto.comp (exceptional_D_log_ratio ha hL)
  have hden := (exceptional_relative_sqrt_ratio ha hL).const_add 1
  have hh := hD.div hden (by positivity : (1:ℝ)+Real.sqrt (1/2:ℝ)≠0)
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hn
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden0 : 0<exceptionalSignDenominator n := exceptional_denominator_pos hn
  have hδ : 0<exceptionalSignEnvelope n := div_pos (Real.sqrt_pos.mpr hlog) (Real.sqrt_pos.mpr hden0)
  have hLp : 0<dimensionLog (p n) := (div_pos_iff_of_pos_right hlog).mp ((half_pos ha).trans hLn)
  have hcost : 0<exceptionalSignEnvelope n+Real.sqrt (exceptionalSignFourth n*D_L (exceptionalSignEnvelope n) (dimensionLog (p n))) :=
    add_pos_of_pos_of_nonneg hδ (Real.sqrt_nonneg _)
  simp only [Function.comp_apply,Pi.div_apply]
  rw [Real.sqrt_div (D_L_nonneg _ _)]
  unfold unrestrictedRate relativeRate
  field_simp [hδ.ne',(Real.rpow_pos_of_pos hLp (3/2:ℝ)).ne',hcost.ne',(Real.sqrt_pos.mpr hlog).ne']
  <;> ring

def exceptionalEnvelopeRateTemplate (n : ℕ) : ℝ :=
  (Real.log (n : ℝ))^(5/2:ℝ)/Real.sqrt n

theorem exceptional_envelope_rate_asymptotic {p : ℕ → ℕ} {a : ℝ} (ha : 0<a)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => unrestrictedRate (exceptionalSignEnvelope n) (dimensionLog (p n))/
      exceptionalEnvelopeRateTemplate n) atTop (𝓝 (a^(3/2:ℝ)*Real.sqrt (1/2:ℝ))) := by
  have hL := polynomial_dimension_dimensionLog_ratio hg
  have hD := Real.continuous_sqrt.continuousAt.tendsto.comp (exceptional_D_log_ratio ha hL)
  have hh := (exceptional_envelope_asymptotic.mul (hL.rpow_const (p:=(3/2:ℝ)) (Or.inl ha.ne'))).mul hD
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_nhds (half_lt_self ha)),eventually_ge_atTop 2] with n hLn hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hLp : 0<dimensionLog (p n) := (div_pos_iff_of_pos_right hlog).mp ((half_pos ha).trans hLn)
  have hp : Real.sqrt (Real.log (n : ℝ))*(Real.log (n : ℝ))^(3/2:ℝ)*Real.sqrt (Real.log (n : ℝ))=
      (Real.log (n : ℝ))^(5/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hlog,←Real.rpow_add hlog]
    congr 1
    norm_num
  simp only [Function.comp_apply,Pi.div_apply]
  rw [Real.sqrt_div hlog.le,Real.div_rpow hLp.le hlog.le,Real.sqrt_div (D_L_nonneg _ _)]
  unfold unrestrictedRate exceptionalEnvelopeRateTemplate
  rw [←hp]
  field_simp [(Real.sqrt_pos.mpr hn0).ne',(Real.sqrt_pos.mpr hlog).ne',
    (Real.rpow_pos_of_pos hlog (3/2:ℝ)).ne']
  <;> ring

theorem exceptional_rates_tendsto_zero {p : ℕ → ℕ} {a : ℝ} (ha : 0<a)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => unrestrictedRate (exceptionalSignEnvelope n) (dimensionLog (p n))) atTop (𝓝 0) ∧
    Tendsto (fun n => relativeRate (exceptionalSignEnvelope n) (exceptionalSignFourth n) (dimensionLog (p n))) atTop (𝓝 0) := by
  have ht : Tendsto exceptionalEnvelopeRateTemplate atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (5/2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
    simpa only [exceptionalEnvelopeRateTemplate,Function.comp_def,←Real.sqrt_eq_rpow] using hh
  have hz := (exceptional_envelope_rate_asymptotic ha hg).mul ht
  simp only [mul_zero] at hz
  have hraw : Tendsto (fun n => unrestrictedRate (exceptionalSignEnvelope n) (dimensionLog (p n))) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have htne : exceptionalEnvelopeRateTemplate n≠0 := by
      unfold exceptionalEnvelopeRateTemplate
      exact div_ne_zero (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hn)) _).ne'
        (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
    exact div_mul_cancel₀ _ htne
  refine ⟨hraw,?_⟩
  let d := fun n => Real.sqrt (D_L (exceptionalSignEnvelope n) (dimensionLog (p n)))
  have hd : ∀n,1≤d n := fun n => Real.one_le_sqrt.mpr (one_le_D_L _ _)
  have hb := bdd_le_mul_tendsto_zero (f:=fun n => (d n)⁻¹)
    (Eventually.of_forall (fun n => inv_nonneg.mpr (zero_le_one.trans (hd n))))
    (Eventually.of_forall (fun n => inv_le_one_of_one_le₀ (hd n))) hraw
  have hbase : Tendsto (fun n => exceptionalSignEnvelope n*(dimensionLog (p n))^(3/2:ℝ)) atTop (𝓝 0) := by
    apply hb.congr
    intro n
    unfold unrestrictedRate
    change (d n)⁻¹*(exceptionalSignEnvelope n*dimensionLog (p n)^(3/2:ℝ)*d n)=_
    have hdne : d n≠0 := (zero_lt_one.trans_le (hd n)).ne'
    field_simp
  have hh := hbase.mul ((exceptional_relative_sqrt_ratio ha (polynomial_dimension_dimensionLog_ratio hg)).const_add 1)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hδ : exceptionalSignEnvelope n≠0 := by
    unfold exceptionalSignEnvelope
    exact div_ne_zero (Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hn))).ne'
      (Real.sqrt_pos.mpr (exceptional_denominator_pos hn)).ne'
  unfold relativeRate
  field_simp [hδ]
  <;> ring

/-- Saturation by one is inactive eventually, so the literal displayed
upper bounds have the same sqrt(log n) gain as their raw rates. -/
theorem exceptional_capped_logarithmic_gain {p : ℕ → ℕ} {a : ℝ} (ha : 0<a)
    (hg : PolynomialDimensionGrowth p a) :
    Tendsto (fun n => (min 1 (unrestrictedRate (exceptionalSignEnvelope n) (dimensionLog (p n)))/
      min 1 (relativeRate (exceptionalSignEnvelope n) (exceptionalSignFourth n) (dimensionLog (p n))))/
        Real.sqrt (Real.log (n : ℝ))) atTop
      (𝓝 (Real.sqrt (1/2:ℝ)/(1+Real.sqrt (1/2:ℝ)))) := by
  obtain ⟨hr,hrel⟩ := exceptional_rates_tendsto_zero ha hg
  apply (exceptional_logarithmic_gain ha hg).congr'
  filter_upwards [hr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    hrel.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn hn'
  rw [min_eq_right hn,min_eq_right hn']

end
end RectangleCLT.Companion.SplitV4.Printed
