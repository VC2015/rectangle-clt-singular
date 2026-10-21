import RectangleCLTCompanion.NormalTailAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Thresholds for Gaussian maxima

The threshold is chosen from the actual standard Gaussian distribution, rather
than supplied as an asymptotic premise.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

lemma exists_standardNormalCDF_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x : ℝ, standardNormalCDF x = u := by
  obtain ⟨a, ha⟩ := (tendsto_standardNormalCDF_atBot.eventually
    (eventually_lt_nhds hu0)).exists
  obtain ⟨b, hb⟩ := (tendsto_standardNormalCDF_atTop.eventually
    (eventually_gt_nhds hu1)).exists
  exact intermediate_value_univ a b continuous_standardNormalCDF ⟨ha.le, hb.le⟩

lemma normalMaxLevel_mem_Ioo {p : ℕ} (hp : 1 ≤ p) :
    Real.exp (-1 / (p : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) (by exact_mod_cast hp)

noncomputable def normalMaxThreshold (p : ℕ) : ℝ :=
  if hp : 1 ≤ p then
    Classical.choose (exists_standardNormalCDF_eq
      (normalMaxLevel_mem_Ioo hp).1 (normalMaxLevel_mem_Ioo hp).2)
  else 0

lemma standardNormalCDF_normalMaxThreshold {p : ℕ} (hp : 1 ≤ p) :
    standardNormalCDF (normalMaxThreshold p) = Real.exp (-1 / (p : ℝ)) := by
  rw [normalMaxThreshold, dif_pos hp]
  exact Classical.choose_spec (exists_standardNormalCDF_eq
    (normalMaxLevel_mem_Ioo hp).1 (normalMaxLevel_mem_Ioo hp).2)

lemma standardNormalCDF_normalMaxThreshold_pow {p : ℕ} (hp : 1 ≤ p) :
    standardNormalCDF (normalMaxThreshold p)^p = Real.exp (-1) := by
  rw [standardNormalCDF_normalMaxThreshold hp, ← Real.exp_nat_mul]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  field_simp

lemma tendsto_normalMaxLevel :
    Tendsto (fun p : ℕ => Real.exp (-1 / (p : ℝ))) atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℕ => (p : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [neg_div, one_div, neg_zero, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hi.neg

lemma tendsto_standardNormalCDF_normalMaxThreshold :
    Tendsto (fun p : ℕ => standardNormalCDF (normalMaxThreshold p)) atTop (𝓝 1) := by
  apply tendsto_normalMaxLevel.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact (standardNormalCDF_normalMaxThreshold hp).symm

lemma tendsto_normalMaxThreshold_atTop : Tendsto normalMaxThreshold atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [tendsto_standardNormalCDF_normalMaxThreshold.eventually
    (eventually_gt_nhds (standardNormalCDF_lt_one r))] with p hp
  exact (strictMono_standardNormalCDF.lt_iff_lt.mp hp).le

lemma tendsto_mul_standardNormalUpperTail_normalMaxThreshold :
    Tendsto (fun p : ℕ => (p : ℝ) * standardNormalUpperTail (normalMaxThreshold p))
      atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℕ => -((p : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop).neg
  have hine : Tendsto (fun p : ℕ => -((p : ℝ)⁻¹)) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hi, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
    simpa only [mem_compl_iff, mem_singleton_iff, neg_eq_zero, inv_eq_zero] using hp0
  have hs := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hine
  simp only [Real.exp_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  rw [standardNormalUpperTail_eq_one_sub, standardNormalCDF_normalMaxThreshold hp]
  simp only [Function.comp_def, zero_add, smul_eq_mul, inv_neg, inv_inv, neg_div, one_div]
  ring

end RectangleCLT.Companion
