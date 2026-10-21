import RectangleCLTCompanion.NormalQuantile
import RectangleCLTCompanion.NormalTailLog

/-! # The sharp scale of the Gaussian maximum threshold -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

lemma standardNormalUpperTail_lt_one (x : ℝ) : standardNormalUpperTail x < 1 := by
  rw [standardNormalUpperTail_eq_one_sub]
  linarith [standardNormalCDF_pos x]

lemma log_standardNormalUpperTail_ne_zero (x : ℝ) :
    Real.log (standardNormalUpperTail x) ≠ 0 :=
  ne_of_lt (Real.log_neg (standardNormalUpperTail_pos x) (standardNormalUpperTail_lt_one x))

lemma tendsto_log_normalMaxTail_div_log :
    Tendsto (fun p : ℕ => Real.log (standardNormalUpperTail (normalMaxThreshold p)) /
      Real.log (p : ℝ)) atTop (𝓝 (-1 : ℝ)) := by
  have hlogmul : Tendsto (fun p : ℕ => Real.log
      ((p : ℝ) * standardNormalUpperTail (normalMaxThreshold p))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      tendsto_mul_standardNormalUpperTail_normalMaxThreshold
  have hlogp : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (hlogmul.div_atTop hlogp).sub_const (1 : ℝ)
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
  have hlog0 : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
  rw [Real.log_mul hp0 (ne_of_gt (standardNormalUpperTail_pos _))]
  field_simp

lemma tendsto_normalMaxThreshold_sq_div_log :
    Tendsto (fun p : ℕ => (normalMaxThreshold p)^2 / Real.log (p : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
  have htail := tendsto_log_standardNormalUpperTail_div_sq.comp tendsto_normalMaxThreshold_atTop
  have hlim := tendsto_log_normalMaxTail_div_log.div htail (by norm_num : (-1/2 : ℝ) ≠ 0)
  have hlim' : Tendsto (fun p : ℕ =>
      (Real.log (standardNormalUpperTail (normalMaxThreshold p)) / Real.log (p : ℝ)) /
      (Real.log (standardNormalUpperTail (normalMaxThreshold p)) / (normalMaxThreshold p)^2))
      atTop (𝓝 (2 : ℝ)) := by convert hlim using 1 <;> norm_num
  apply hlim'.congr'
  filter_upwards [tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop 2] with p hp hp2
  have hlog0 : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp2))
  have hx : normalMaxThreshold p ≠ 0 := ne_of_gt hp
  have ht := log_standardNormalUpperTail_ne_zero (normalMaxThreshold p)
  field_simp [ht, hx, hlog0]
  ring

lemma tendsto_normalMaxThreshold_sq_div_two_log :
    Tendsto (fun p : ℕ => (normalMaxThreshold p)^2 / (2 * Real.log (p : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_normalMaxThreshold_sq_div_log.div_const (2 : ℝ)
  convert h using 1
  · funext p
    rw [div_div, mul_comm]
  · norm_num

lemma tendsto_normalMaxThreshold_div_sqrt_two_log :
    Tendsto (fun p : ℕ => normalMaxThreshold p / Real.sqrt (2 * Real.log (p : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have h := Real.continuous_sqrt.tendsto 1 |>.comp tendsto_normalMaxThreshold_sq_div_two_log
  have h' : Tendsto (fun p : ℕ => Real.sqrt
      ((normalMaxThreshold p)^2 / (2 * Real.log (p : ℝ)))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.sqrt_one] using h
  apply h'.congr'
  filter_upwards [tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop 0)] with p hp
  rw [Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq_eq_abs, abs_of_pos hp]

end RectangleCLT.Companion
