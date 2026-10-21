import RectangleCLTCompanion.NormalTailAsymptotics

/-! # The logarithmic standard normal tail asymptotic -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

lemma standardNormalPDF_div_two_mul_le_tail {x : ℝ} (hx : 1 ≤ x) :
    standardNormalPDF x / (2*x) ≤ standardNormalUpperTail x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  apply le_trans _ (mills_le_standardNormalUpperTail hx0)
  apply (div_le_div_iff₀ (by positivity : 0 < 2*x) (by positivity : 0 < x^2+1)).mpr
  have hp := standardNormalPDF_nonneg x
  have hs : x^2+1 ≤ 2*x*x := by nlinarith
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hs)]

lemma log_standardNormalPDF (x : ℝ) :
    Real.log (standardNormalPDF x) = -Real.log (Real.sqrt (2*Real.pi)) - x^2/2 := by
  rw [standardNormalPDF_eq, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

lemma tendsto_log_normalPDF_div_mul_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (standardNormalPDF x / (c*x)) / x^2)
      atTop (𝓝 (-1/2 : ℝ)) := by
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hlog : Tendsto (fun x : ℝ => Real.log x / x^2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
  have hconst : Tendsto (fun x : ℝ =>
      (-Real.log (Real.sqrt (2*Real.pi)) - Real.log c) / x^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hlim := (hconst.sub hlog).sub_const (1/2 : ℝ)
  have hlim' : Tendsto (fun x : ℝ =>
      (-Real.log (Real.sqrt (2*Real.pi)) - Real.log c) / x^2 - Real.log x / x^2 - 1/2)
      atTop (𝓝 (-1/2 : ℝ)) := by
    convert hlim using 1 <;> norm_num
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.log_div (ne_of_gt (standardNormalPDF_pos x)) (by positivity),
    Real.log_mul (ne_of_gt hc) (ne_of_gt hx), log_standardNormalPDF]
  field_simp
  ring

lemma tendsto_log_standardNormalUpperTail_div_sq :
    Tendsto (fun x : ℝ => Real.log (standardNormalUpperTail x) / x^2)
      atTop (𝓝 (-1/2 : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_log_normalPDF_div_mul_sq (by norm_num : (0 : ℝ) < 2))
    (tendsto_log_normalPDF_div_mul_sq (by norm_num : (0 : ℝ) < 1))
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    apply div_le_div_of_nonneg_right _ (sq_nonneg x)
    exact Real.log_le_log (div_pos (standardNormalPDF_pos x) (by positivity))
      (standardNormalPDF_div_two_mul_le_tail hx)
  · filter_upwards [eventually_ge_atTop 1] with x hx
    apply div_le_div_of_nonneg_right _ (sq_nonneg x)
    apply Real.log_le_log (standardNormalUpperTail_pos x)
    simpa using standardNormalUpperTail_le_mills (lt_of_lt_of_le zero_lt_one hx)

end RectangleCLT.Companion
