import RectangleCLTCompanion.NormalQuantileRate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact quantile and remainder scales for the skewed lower construction.
These statements are scalar limits derived from the actual Gaussian
maximum threshold; no moderate-deviation estimate is assumed. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def lowerSkewRate (B : ℝ) (p n : ℕ) : ℝ :=
  B * (Real.log (p : ℝ)) ^ (3 / 2 : ℝ) / Real.sqrt (n : ℝ)

theorem lower_log_power_three_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  by_cases hz : x = 0
  · simp [hz]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem lower_log_power_three_half_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
  rw [lower_log_power_three_half hx, mul_pow, Real.sq_sqrt hx]
  ring

theorem lower_quantile_div_sqrt_log {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => normalMaxThreshold (p n) / Real.sqrt (Real.log (p n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hh := (tendsto_normalMaxThreshold_div_sqrt_two_log.comp hp).mul_const (Real.sqrt 2)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2)] with n hn
  have hlog : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  change (normalMaxThreshold (p n) / Real.sqrt (2 * Real.log (p n : ℝ))) * Real.sqrt 2 = _
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [(Real.sqrt_pos.mpr hlog).ne', (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

theorem lower_quantile_div_log_power {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => normalMaxThreshold (p n) / (Real.log (p n : ℝ)) ^ (3 / 2 : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (p n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hp)
  have hh := (lower_quantile_div_sqrt_log hp).div_atTop hlog
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2)] with n hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [lower_log_power_three_half hl.le]
  ring

theorem lower_quantile_fourth_div_log_power_sq {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => (normalMaxThreshold (p n)) ^ 4 /
      ((Real.log (p n : ℝ)) ^ (3 / 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (p n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hp)
  have hh := ((tendsto_normalMaxThreshold_sq_div_log.comp hp).pow 2).div_atTop hlog
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2)] with n hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [lower_log_power_three_half_sq hl.le]
  field_simp [hl.ne']
  ring

theorem lower_quantile_cubic_coefficient {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => (normalMaxThreshold (p n)) ^ 3 /
      (6 * (Real.log (p n : ℝ)) ^ (3 / 2 : ℝ))) atTop (𝓝 (Real.sqrt 2 / 3)) := by
  have hh := ((lower_quantile_div_sqrt_log hp).pow 3).div_const 6
  have hlim : (Real.sqrt 2) ^ 3 / (6 : ℝ) = Real.sqrt 2 / 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2)] with n hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hroot : ((Real.log (p n : ℝ)) ^ (3 / 2 : ℝ)) =
      (Real.sqrt (Real.log (p n : ℝ))) ^ 3 := by
    rw [lower_log_power_three_half hl.le, pow_succ, Real.sq_sqrt hl.le]
  rw [hroot]
  ring

theorem lower_skew_linear_scale {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => B n * normalMaxThreshold (p n) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hh := hr.mul (lower_quantile_div_log_power hp)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hn hn'
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn'
  unfold lowerSkewRate
  field_simp [(Real.rpow_pos_of_pos hl (3 / 2 : ℝ)).ne', (Real.sqrt_pos.mpr hnR).ne']
  ring

theorem lower_skew_tilt_scale {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => normalMaxThreshold (p n) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hh := bdd_le_mul_tendsto_zero (f := fun n => (B n)⁻¹)
    (Filter.Eventually.of_forall (fun n => inv_nonneg.mpr (by linarith only [hB n])))
    (Filter.Eventually.of_forall (fun n => inv_le_one_of_one_le₀ (by linarith only [hB n])))
    (lower_skew_linear_scale hp hr)
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hBn : B n ≠ 0 := by linarith only [hB n]
  field_simp [hBn] <;> ring

theorem lower_skew_linear_remainder_ratio {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => (B n * normalMaxThreshold (p n) / Real.sqrt (n : ℝ)) /
      lowerSkewRate (B n) (p n) n) atTop (𝓝 0) := by
  apply (lower_quantile_div_log_power hp).congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp' hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hp')
  have hBn : B n ≠ 0 := by linarith only [hB n]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold lowerSkewRate
  field_simp [hBn, (Real.sqrt_pos.mpr hnR).ne', (Real.rpow_pos_of_pos hl (3 / 2 : ℝ)).ne']
  ring

theorem lower_skew_quartic_remainder_ratio {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => ((B n) ^ 2 * (normalMaxThreshold (p n)) ^ 4 / (n : ℝ)) /
      lowerSkewRate (B n) (p n) n) atTop (𝓝 0) := by
  have hh := hr.mul (lower_quantile_fourth_div_log_power_sq hp)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp' hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hp')
  have hBn : B n ≠ 0 := by linarith only [hB n]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  unfold lowerSkewRate
  field_simp [hBn, (Real.sqrt_pos.mpr hnR).ne', (Real.rpow_pos_of_pos hl (3 / 2 : ℝ)).ne']
  ring_nf
  rw [hs]

theorem lower_skew_quartic_remainder {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => (B n) ^ 2 * (normalMaxThreshold (p n)) ^ 4 / (n : ℝ))
      atTop (𝓝 0) := by
  have hh := (hr.pow 2).mul (lower_quantile_fourth_div_log_power_sq hp)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp' hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hp')
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  unfold lowerSkewRate
  field_simp [(Real.sqrt_pos.mpr hnR).ne', (Real.rpow_pos_of_pos hl (3 / 2 : ℝ)).ne']
  nlinarith only [hs]

theorem lower_skew_cubic_coefficient_difference {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => (((B n - (B n)⁻¹) * (normalMaxThreshold (p n)) ^ 3 /
      (6 * Real.sqrt (n : ℝ))) / lowerSkewRate (B n) (p n) n) -
        (1 - 1 / (B n) ^ 2) * Real.sqrt 2 / 3) atTop (𝓝 0) := by
  have hcoeff := (lower_quantile_cubic_coefficient hp).sub_const (Real.sqrt 2 / 3)
  simp only [sub_self] at hcoeff
  have hb0 : ∀ᶠ n in atTop, 0 ≤ 1 - 1 / (B n) ^ 2 := by
    apply Filter.Eventually.of_forall
    intro n
    have hBn : 0 < B n := by linarith only [hB n]
    have hsq : 1 ≤ (B n) ^ 2 := by nlinarith only [hB n]
    exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hBn)).mpr hsq)
  have hb1 : ∀ᶠ n in atTop, 1 - 1 / (B n) ^ 2 ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by linarith only [one_div_nonneg.mpr (sq_nonneg (B n))])
  have hh := bdd_le_mul_tendsto_zero hb0 hb1 hcoeff
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp' hn
  have hl : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hp')
  have hBn : B n ≠ 0 := by linarith only [hB n]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold lowerSkewRate
  field_simp [hBn, (Real.sqrt_pos.mpr hnR).ne', (Real.rpow_pos_of_pos hl (3 / 2 : ℝ)).ne']
  ring

end

end RectangleCLT.Companion
