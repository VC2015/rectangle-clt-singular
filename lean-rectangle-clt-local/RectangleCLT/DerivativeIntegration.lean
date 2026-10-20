import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual time integration of the short-scale and Gaussian derivative caps.
These scalar lemmas retain the two-thirds power of the fourth-face covariance
cost. Their pointwise bounds and integrability hypotheses are explicit. -/

open MeasureTheory Set

namespace RectangleCLT

private theorem integral_rpow_neg_three_halves_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
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

/-- The third-derivative singularity becomes integrable after multiplying by
the time coefficient appearing in the signed third-moment correction. -/
theorem integral_time_mul_third_le {D : ℝ → ℝ} {B : ℝ}
    (hD : IntervalIntegrable (fun t => t * D t) volume 0 1)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ B * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, t * D t) ≤ 2 * B := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hD (hp.const_mul B) (fun t ht => by
      have hpow : t * t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
        calc
          _ = t ^ (1 : ℝ) * t ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
          _ = t ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := (Real.rpow_add ht.1 _ _).symm
          _ = _ := by norm_num
      calc
        _ ≤ t * (B * t ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hlarge t ht) ht.1.le
        _ = B * t ^ (-(1 / 2 : ℝ)) := by rw [mul_left_comm, hpow])
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))] at hh
  norm_num at hh
  linarith

/-- Integrating the uniform short-scale cap on the full unit interval. -/
theorem integral_fourth_small_cap {D : ℝ → ℝ} {C L h : ℝ}
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3) :
    (∫ t in (0 : ℝ)..1, D t) ≤ C * Real.sqrt L / h ^ 3 := by
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hD intervalIntegrable_const hsmall
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hh

/-- Split the fourth-derivative integral at `R² L h²`. The coefficient `R³`
in the Gaussian cap therefore costs only `R²` after integration. -/
theorem integral_fourth_time_le_cube_root_scale
    {D : ℝ → ℝ} {C R L h : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R) (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, h ^ 2 * L ≤ t →
      D t ≤ C * R ^ 3 * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤ 3 * C * R ^ 2 * L * Real.sqrt L / h := by
  let a := Real.sqrt L
  let τ := R ^ 2 * L * h ^ 2
  let A := C * a / h ^ 3
  let B := C * R ^ 3 * L ^ 2
  change (∫ t in (0 : ℝ)..1, D t) ≤ 3 * C * R ^ 2 * L * a / h
  have hR0 : 0 < R := by linarith
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
    have hbase : h ^ 2 * L ≤ τ := by
      have hR2 : 1 ≤ R ^ 2 := by nlinarith
      have hx := mul_le_mul_of_nonneg_right hR2 (mul_nonneg hL0.le (sq_nonneg h))
      dsimp [τ]
      nlinarith
    have hn : (0 : ℝ) ∉ Set.uIcc τ 1 := by
      rw [uIcc_of_le hτ1]
      intro ht
      linarith [ht.1]
    have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) volume τ 1 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hn)
    have hright : (∫ t in τ..1, D t) ≤ B * (2 / Real.sqrt τ) := by
      have ht := intervalIntegral.integral_mono_on_of_le_Ioo hτ1 hD1 (hp.const_mul B)
        (fun t ht => hlarge t ⟨hτ.trans ht.1, ht.2⟩ (hbase.trans ht.1.le))
      rw [intervalIntegral.integral_const_mul] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left (integral_rpow_neg_three_halves_le hτ hτ1) hB)
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

/-- The optimized fourth-derivative cap, with the exact two-thirds power of
its Gaussian coefficient. -/
theorem integral_fourth_time_le
    {D : ℝ → ℝ} {C K L h : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, h ^ 2 * L ≤ t →
      D t ≤ C * K * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤
      3 * C * K ^ (2 / 3 : ℝ) * L ^ (3 / 2 : ℝ) / h := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hR : 1 ≤ K ^ (1 / 3 : ℝ) := Real.one_le_rpow hK (by norm_num)
  have hR3 : (K ^ (1 / 3 : ℝ)) ^ 3 = K := by
    rw [← Real.rpow_mul_natCast hK0 (1 / 3 : ℝ) 3]
    norm_num
  have hR2 : (K ^ (1 / 3 : ℝ)) ^ 2 = K ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hK0 (1 / 3 : ℝ) 2]
    norm_num
  have hLpow : L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
    calc
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = L ^ ((1 : ℝ) + (1 / 2 : ℝ)) := (Real.rpow_add hL0 _ _).symm
      _ = _ := by norm_num
  have hmain := integral_fourth_time_le_cube_root_scale hC hR hL hh hD hsmall
    (fun t ht hb => by simpa only [hR3] using hlarge t ht hb)
  rw [hR2] at hmain
  convert hmain using 1
  rw [← hLpow]
  ring

/-- Both actual time-integral caps are retained. -/
theorem integral_fourth_time_le_min
    {D : ℝ → ℝ} {C K L h : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, h ^ 2 * L ≤ t →
      D t ≤ C * K * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤
      min (C * Real.sqrt L / h ^ 3)
        (3 * C * K ^ (2 / 3 : ℝ) * L ^ (3 / 2 : ℝ) / h) :=
  le_min (integral_fourth_small_cap hD hsmall)
    (integral_fourth_time_le hC hK hL hh hD hsmall hlarge)

/-- Writing the Gaussian coefficient as a reciprocal covariance cost places
its two-thirds power in the denominator, as in the fourth-face time integral. -/
theorem integral_fourth_time_le_of_covariance_cost
    {D : ℝ → ℝ} {C cost L h : ℝ} (hC : 0 ≤ C)
    (hcost : 0 < cost) (hcost1 : cost ≤ 1) (hL : 1 ≤ L) (hh : 0 < h)
    (hD : IntervalIntegrable D volume 0 1)
    (hsmall : ∀ t ∈ Ioo (0 : ℝ) 1, D t ≤ C * Real.sqrt L / h ^ 3)
    (hlarge : ∀ t ∈ Ioo (0 : ℝ) 1, h ^ 2 * L ≤ t →
      D t ≤ C / cost * L ^ 2 * t ^ (-(3 / 2 : ℝ))) :
    (∫ t in (0 : ℝ)..1, D t) ≤
      3 * C * L ^ (3 / 2 : ℝ) / (h * cost ^ (2 / 3 : ℝ)) := by
  have hK : 1 ≤ cost⁻¹ := (one_le_inv₀ hcost).mpr hcost1
  have hmain := integral_fourth_time_le hC hK hL hh hD hsmall
    (fun t ht hb => by simpa only [div_eq_mul_inv] using hlarge t ht hb)
  rw [Real.inv_rpow hcost.le] at hmain
  convert hmain using 1
  ring

end RectangleCLT
