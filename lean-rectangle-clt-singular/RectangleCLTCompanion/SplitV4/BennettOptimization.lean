import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Global scalar inequalities for the Bennett polynomial optimizer.
Every constant is chosen before the varying parameter K. The proofs use
explicit real inequalities; no probabilistic conclusion is a premise. -/

open Set

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def bennettParameterLog (K : ℝ) : ℝ := Real.log (Real.exp 1 + K)

theorem bennettParameterLog_ge_one {K : ℝ} (hK : 1 ≤ K) : 1 ≤ bennettParameterLog K := by
  have he := Real.log_le_log (Real.exp_pos (1 : ℝ))
    (show Real.exp 1 ≤ Real.exp 1 + K by linarith)
  simpa only [Real.log_exp, bennettParameterLog] using he

private theorem exp_add_parameter_le {K : ℝ} (hK : 1 ≤ K) :
    Real.exp 1 + K ≤ (Real.exp 1 + 1) * K := by
  nlinarith [mul_nonneg (Real.exp_pos (1 : ℝ)).le (sub_nonneg.mpr hK)]

/-- A fixed power of log(e+K) divided by any fixed positive power of K is
uniformly bounded on K≥1. The exponent of the logarithm may be negative. -/
theorem exists_log_power_div_rpow_bound (a b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (bennettParameterLog K) ^ a / K ^ b ≤ C := by
  let c := max a 1
  let r := b / c
  let D := (Real.exp 1 + 1) ^ r / r
  have hc : 0 < c := lt_max_iff.mpr (Or.inr (by norm_num))
  have hr : 0 < r := div_pos hb hc
  have hD : 0 < D := div_pos (Real.rpow_pos_of_pos (by positivity) _) hr
  refine ⟨D ^ c, Real.rpow_pos_of_pos hD _, ?_⟩
  intro K hK
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL1 := bennettParameterLog_ge_one hK
  have hL0 : 0 ≤ bennettParameterLog K := zero_le_one.trans hL1
  have hlog := Real.log_le_rpow_div (show 0 ≤ Real.exp 1 + K by positivity) hr
  have hx := Real.rpow_le_rpow (show 0 ≤ Real.exp 1 + K by positivity)
    (exp_add_parameter_le hK) hr.le
  rw [Real.mul_rpow (by positivity : 0 ≤ Real.exp 1 + 1) hK0.le] at hx
  have hLcap : bennettParameterLog K ≤ D * K ^ r := by
    apply hlog.trans
    convert div_le_div_of_nonneg_right hx hr.le using 1 <;> dsimp only [D] <;> ring
  have hpow := Real.rpow_le_rpow hL0 hLcap hc.le
  rw [Real.mul_rpow hD.le (Real.rpow_nonneg hK0.le _),
    ← Real.rpow_mul hK0.le] at hpow
  have hrc : r * c = b := div_mul_cancel₀ b hc.ne'
  rw [hrc] at hpow
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hK0 b)).mpr
  exact (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left a 1)).trans hpow

/-- The logarithmic Bennett denominator remains comparable to log(e+K),
including an arbitrary fixed negative logarithmic exponent. -/
theorem exists_bennett_log_denominator_lower (c c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, 1 ≤ K →
      a * bennettParameterLog K ≤
        Real.log (1 + c₀ * K * (bennettParameterLog K) ^ c) := by
  obtain ⟨C, hC, hpow⟩ := exists_log_power_div_rpow_bound (-c) (1 / 2) (by norm_num)
  let d := c₀ / C
  let m := Real.log (1 + d)
  let B := Real.log (Real.exp 1 + 1) + 2 * |Real.log d|
  let D := 2 + B / m
  have hd : 0 < d := div_pos hc₀ hC
  have hm : 0 < m := Real.log_pos (by linarith : 1 < 1 + d)
  have hB : 0 ≤ B := by
    have hlog : 0 ≤ Real.log (Real.exp 1 + 1) :=
      Real.log_nonneg (by linarith [Real.exp_pos (1 : ℝ)])
    dsimp only [B]
    positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨1 / D, one_div_pos.mpr hD, ?_⟩
  intro K hK
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hroot : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hroot1 : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK
  have hL1 := bennettParameterLog_ge_one hK
  have hL : 0 < bennettParameterLog K := zero_lt_one.trans_le hL1
  have hLc : 0 < (bennettParameterLog K) ^ c := Real.rpow_pos_of_pos hL c
  have hp := hpow K hK
  rw [Real.rpow_neg hL.le, ← Real.sqrt_eq_rpow] at hp
  have hrecip := mul_le_mul_of_nonneg_right ((div_le_iff₀ hroot).mp hp) hLc.le
  rw [inv_mul_cancel₀ hLc.ne'] at hrecip
  have hpower : Real.sqrt K ≤ C * (K * (bennettParameterLog K) ^ c) := by
    calc
      _ = Real.sqrt K * 1 := by ring
      _ ≤ Real.sqrt K * (C * Real.sqrt K * (bennettParameterLog K) ^ c) :=
        mul_le_mul_of_nonneg_left hrecip hroot.le
      _ = C * ((Real.sqrt K) ^ 2 * (bennettParameterLog K) ^ c) := by ring
      _ = _ := by rw [Real.sq_sqrt hK0.le]
  have hGlower : d * Real.sqrt K ≤ c₀ * K * (bennettParameterLog K) ^ c := by
    have hh := mul_le_mul_of_nonneg_left hpower hd.le
    convert hh using 1 <;> dsimp only [d] <;> field_simp [hC.ne'] <;> ring
  let T := Real.log (1 + c₀ * K * (bennettParameterLog K) ^ c)
  have hbase : m ≤ T := by
    apply Real.log_le_log (by linarith : 0 < 1 + d)
    have hlow : d ≤ d * Real.sqrt K := by nlinarith [hroot1, hd]
    linarith
  have hlogroot : Real.log (d * Real.sqrt K) ≤ T :=
    Real.log_le_log (mul_pos hd hroot) (by linarith [hGlower])
  rw [Real.log_mul hd.ne' hroot.ne', Real.log_sqrt hK0.le] at hlogroot
  have hlogK : Real.log K ≤ 2 * T + 2 * |Real.log d| := by
    linarith [neg_le_abs (Real.log d)]
  have hLupper : bennettParameterLog K ≤ Real.log (Real.exp 1 + 1) + Real.log K := by
    have he := Real.log_le_log (show 0 < Real.exp 1 + K by positivity) (exp_add_parameter_le hK)
    rw [Real.log_mul (by positivity : Real.exp 1 + 1 ≠ 0) hK0.ne'] at he
    exact he
  have hBcost : B ≤ B / m * T := by
    have hh := mul_le_mul_of_nonneg_left hbase (div_nonneg hB hm.le)
    rwa [div_mul_cancel₀ B hm.ne'] at hh
  have htotal : bennettParameterLog K ≤ D * T := by
    dsimp only [D, B] at *
    nlinarith
  calc
    _ = bennettParameterLog K / D := by ring
    _ ≤ T := (div_le_iff₀ hD).mpr (htotal.trans_eq (by ring))

/-- The three ratios in the large-K Bennett calibration share one fixed
constant, depending only on q. -/
theorem bennett_large_regime_ratio_bounds (q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (bennettParameterLog K) ^ (2 * (1 - 1 / q)) / K ≤ C ∧
      (bennettParameterLog K) ^ (4 * (1 - 1 / q)) / K ^ (2 : ℝ) ≤ C ∧
      (bennettParameterLog K) ^ (2 * (1 - 1 / q) + (q - 1) / 2) / K ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_log_power_div_rpow_bound (2 * (1 - 1 / q)) 1 (by norm_num)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_log_power_div_rpow_bound (4 * (1 - 1 / q)) 2 (by norm_num)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_log_power_div_rpow_bound
    (2 * (1 - 1 / q) + (q - 1) / 2) 1 (by norm_num)
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro K hK
  have hh₁ := h₁ K hK
  have hh₂ := h₂ K hK
  have hh₃ := h₃ K hK
  simp only [Real.rpow_one] at hh₁ hh₃
  exact ⟨by linarith, by linarith, by linarith⟩

end
end RectangleCLT.Companion.SplitV4
