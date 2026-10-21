import RectangleCLT.DerivativeIntegration
import Mathlib.Tactic.FieldSimp

/-! Scalar integration with the exact full-dual threshold.
The pointwise and interval-integrability assumptions are explicit; the
random-vector application is assembled in `GlobalBoundedAssembly`.
-/

open MeasureTheory Set

namespace RectangleCLT

private theorem global_integral_rpow_neg_three_halves_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (∫ t in τ..1, t ^ (-(3 / 2 : ℝ))) ≤ 2 / Real.sqrt τ := by
  have hn : (0 : ℝ) ∉ Set.uIcc τ 1 := by
    rw [uIcc_of_le hτ1]
    intro hh
    linarith [hh.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hn⟩)]
  norm_num
  rw [show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) by rfl,
    Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow]
  have hs := Real.sqrt_pos.mpr hτ
  calc
    _ = 2 / Real.sqrt τ - 2 := by field_simp [ne_of_gt hs]; ring
    _ ≤ 2 / Real.sqrt τ := by linarith

/-- Split the fourth-derivative integral at `R² L h²`. The coefficient `R³`
in the Gaussian cap therefore costs only `R²` after integration. -/
theorem integral_fourth_time_le_dual_scale
    {D : ℝ → ℝ} {C R L h : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, R ^ 2 * L * h ^ 2 ≤ t →
      D t ≤ C * R ^ 3 * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤ 3 * C * R ^ 2 * L * Real.sqrt L / h := by
  let a := Real.sqrt L
  let τ := R ^ 2 * L * h ^ 2
  let A := C * a / h ^ 3
  let B := C * R ^ 3 * L ^ 2
  change (∫ t in (0 : ℝ)..1, D t) ≤ 3 * C * R ^ 2 * L * a / h
  have hR0 : 0 < R := hR
  have hL0 : 0 < L := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr hL0
  have ha2 : a ^ 2 = L := Real.sq_sqrt hL0.le
  have hτ : 0 < τ := mul_pos (mul_pos (sq_pos_of_pos hR0) hL0) (sq_pos_of_pos hh)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC ha.le) (pow_nonneg hh.le _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC (pow_nonneg hR0.le _)) (sq_nonneg L)
  have hbalance : A * τ = C * R ^ 2 * L * a / h := by
    dsimp [A, τ]
    field_simp
    ring
  have hcap : (∫ t in (0 : ℝ)..1, D t) ≤ A := integral_fourth_small_cap hD hsmall
  by_cases hτ1 : τ ≤ 1
  · have hD0 : IntervalIntegrable D volume 0 τ := hD.mono_set (by
      simpa only [uIcc_of_le hτ.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Icc_subset_Icc le_rfl hτ1)
    have hD1 : IntervalIntegrable D volume τ 1 := hD.mono_set (by
      simpa only [uIcc_of_le hτ1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Icc_subset_Icc hτ.le le_rfl)
    have hleft : (∫ t in (0 : ℝ)..τ, D t) ≤ A * τ := by
      have ht := intervalIntegral.integral_mono_on_of_le_Ioo hτ.le hD0 intervalIntegrable_const
        (fun t ht => hsmall t ⟨ht.1, ht.2.trans_le hτ1⟩)
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using ht
    have hn : (0 : ℝ) ∉ Set.uIcc τ 1 := by
      rw [uIcc_of_le hτ1]
      intro ht
      linarith [ht.1]
    have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) volume τ 1 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hn)
    have hright : (∫ t in τ..1, D t) ≤ B * (2 / Real.sqrt τ) := by
      have ht := intervalIntegral.integral_mono_on_of_le_Ioo hτ1 hD1 (hp.const_mul B)
        (fun t ht => hlarge t ⟨hτ.trans ht.1, ht.2⟩ ht.1.le)
      rw [intervalIntegral.integral_const_mul] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left (global_integral_rpow_neg_three_halves_le hτ hτ1) hB)
    have hsqrt : Real.sqrt τ = R * a * h := by
      dsimp [τ]
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg R) hL0.le),
        Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_pos hR0, abs_of_pos hh]
    have halgebra : A * τ + B * (2 / Real.sqrt τ) = 3 * C * R ^ 2 * L * a / h := by
      rw [hbalance, hsqrt]
      dsimp [B]
      rw [← ha2]
      field_simp
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals hD0 hD1]
    exact (add_le_add hleft hright).trans_eq halgebra
  · have hτge : 1 ≤ τ := le_of_lt (lt_of_not_ge hτ1)
    have hmul := mul_le_mul_of_nonneg_left hτge hA
    rw [mul_one, hbalance] at hmul
    have htarget : 0 ≤ C * R ^ 2 * L * a / h := by positivity
    have hthree := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) htarget
    calc
      _ ≤ A := hcap
      _ ≤ C * R ^ 2 * L * a / h := hmul
      _ ≤ 3 * (C * R ^ 2 * L * a / h) := by simpa only [one_mul] using hthree
      _ = _ := by ring

/-- A cubic cap proportional to reciprocal time cancels its actual
signed-third-moment time coefficient exactly. -/
theorem integral_time_mul_third_le_inv_time {D : ℝ → ℝ} {B : ℝ}
    (hD : IntervalIntegrable (fun t => t * D t) volume 0 1)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ B / t) :
    (∫ t in (0 : ℝ)..1, t * D t) ≤ B := by
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) hD intervalIntegrable_const (fun t ht => by
      have hb := mul_le_mul_of_nonneg_left (hlarge t ht) ht.1.le
      simpa only [mul_div_cancel₀ _ ht.1.ne', mul_comm t] using hb)
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hh

/-- The full-eigenvalue fourth time coefficient is exactly reciprocal `ν`.
The large-time estimate is required only when `L*h²/ν ≤ t`. -/
theorem integral_fourth_time_le_full_eigenvalue
    {D : ℝ → ℝ} {C ν L h : ℝ} (hC : 0 ≤ C) (hν : 0 < ν)
    (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, (1 / ν) * L * h ^ 2 ≤ t →
      D t ≤ C * (1 / Real.sqrt ν) ^ 3 * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤ 3 * C * L * Real.sqrt L / (ν * h) := by
  have hR : 0 < 1 / Real.sqrt ν := one_div_pos.mpr (Real.sqrt_pos.mpr hν)
  have hR2 : (1 / Real.sqrt ν) ^ 2 = 1 / ν := by
    rw [div_pow, one_pow, Real.sq_sqrt hν.le]
  have hb := integral_fourth_time_le_dual_scale hC hR hL hh hD hsmall
    (fun t ht htime => hlarge t ht (by simpa only [hR2] using htime))
  rw [hR2] at hb
  convert hb using 1 <;> ring

end RectangleCLT
