import RectangleCLTCompanion.RademacherCriticalScale
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Integer dimensions at the zero-skew critical scale -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def rademacherCriticalDimension (a : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (a * Real.sqrt n)⌋₊

lemma rademacherCriticalDimension_pos {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    1 ≤ rademacherCriticalDimension a n := by
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_exp (mul_nonneg ha (Real.sqrt_nonneg _))

lemma tendsto_rademacherCriticalDimension {a : ℝ} (ha : 0 < a) :
    Tendsto (rademacherCriticalDimension a) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
    (rademacher_sqrt_nat_atTop.const_mul_atTop ha))

lemma tendsto_log_rademacherCriticalDimension_div_sqrt {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (rademacherCriticalDimension a n : ℝ) / Real.sqrt n)
      atTop (𝓝 a) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (a*Real.sqrt n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (rademacher_sqrt_nat_atTop.const_mul_atTop ha)
  have hratio : Tendsto (fun n : ℕ =>
      (rademacherCriticalDimension a n : ℝ) / Real.exp (a*Real.sqrt n)) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hexp
  have hlogratio : Tendsto (fun n : ℕ => Real.log
      ((rademacherCriticalDimension a n : ℝ) / Real.exp (a*Real.sqrt n))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlim := (hlogratio.div_atTop rademacher_sqrt_nat_atTop).add_const a
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq : (rademacherCriticalDimension a n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (rademacherCriticalDimension_pos ha.le n)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  rw [Real.log_div hq (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  <;> ring

lemma log_dimension_div_sqrt_le_of_le_critical {a : ℝ} {n p : ℕ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hpq : p ≤ rademacherCriticalDimension a n) :
    Real.log (p : ℝ) / Real.sqrt n ≤ a := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  apply (div_le_iff₀ hs).mpr
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hle : (p : ℝ) ≤ Real.exp (a*Real.sqrt n) :=
    (by exact_mod_cast hpq : (p : ℝ) ≤ rademacherCriticalDimension a n).trans
      (Nat.floor_le (Real.exp_pos _).le)
  simpa only [Real.log_exp] using Real.log_le_log hp0 hle

/-- Being eventually below each positive critical dimension is precisely
what is needed for the arbitrary-dimension necessity argument. -/
lemma tendsto_log_dimension_div_sqrt_of_eventually_le_critical
    {p : ℕ → ℕ} (hp : ∀ n, 1 ≤ p n)
    (h : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, p n ≤ rademacherCriticalDimension a n) :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha : 0 < ε/2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((h (ε/2) ha).and (eventually_ge_atTop 1))
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hpn, hn1⟩ := hN n hn
  have hlo : 0 ≤ Real.log (p n : ℝ) / Real.sqrt n :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hp n)) (Real.sqrt_nonneg _)
  have hhi := log_dimension_div_sqrt_le_of_le_critical hn1 (hp n) hpn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using (lt_of_le_of_lt hhi (by linarith : ε/2 < ε))

end

end RectangleCLT.Companion
