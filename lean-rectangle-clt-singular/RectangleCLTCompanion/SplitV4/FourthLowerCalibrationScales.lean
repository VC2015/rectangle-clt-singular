import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact fourth-moment amplitude calibration and its numerical asymptotics.
No probability estimate is a premise of these deterministic statements. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def fourthLowerTheta (n : ℕ) (ell : ℝ) : ℝ := ell / (2 * (n : ℝ))
def fourthLowerAmplitude (n : ℕ) (ell : ℝ) : ℝ := (fourthLowerTheta n ell) ^ (-1/4 : ℝ)
def fourthLowerScale (n : ℕ) (ell : ℝ) : ℝ :=
  fourthLowerAmplitude n ell * ell ^ (3/2 : ℝ) / (2 * Real.sqrt n)
def fourthLowerRate (n : ℕ) (ell : ℝ) : ℝ :=
  (1+2*ell) ^ (5/4 : ℝ) / (n : ℝ) ^ (1/4 : ℝ)

theorem fourthLowerTheta_pos {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    0 < fourthLowerTheta n ell := by
  unfold fourthLowerTheta
  positivity

theorem fourthLowerAmplitude_pos {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    0 < fourthLowerAmplitude n ell := Real.rpow_pos_of_pos (fourthLowerTheta_pos hn he) _

theorem fourthLowerScale_pos {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    0 < fourthLowerScale n ell := by
  unfold fourthLowerScale
  exact div_pos (mul_pos (fourthLowerAmplitude_pos hn he) (Real.rpow_pos_of_pos he _))
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by exact_mod_cast hn)))

theorem fourthLowerRate_pos {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    0 < fourthLowerRate n ell := by
  unfold fourthLowerRate
  apply div_pos (Real.rpow_pos_of_pos (by linarith only [he]) _)
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem fourth_power_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x ^ a) ^ 4 = x ^ (a*4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem fourthLowerAmplitude_fourth {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    fourthLowerTheta n ell * fourthLowerAmplitude n ell ^ 4 = 1 := by
  have ht := fourthLowerTheta_pos hn he
  unfold fourthLowerAmplitude
  rw [fourth_power_rpow ht.le]
  norm_num [Real.rpow_neg_one]
  exact mul_inv_cancel₀ ht.ne'

theorem fourthLowerScale_fourth {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    fourthLowerScale n ell ^ 4 = ell ^ 5 / (8*(n : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : fourthLowerAmplitude n ell ^ 4 = 2*(n : ℝ)/ell := by
    have hh := fourthLowerAmplitude_fourth hn he
    unfold fourthLowerTheta at hh
    apply (eq_div_iff he.ne').2
    field_simp at hh
    nlinarith only [hh]
  have he6 : (ell ^ (3/2 : ℝ)) ^ 4 = ell ^ 6 := by
    rw [fourth_power_rpow he.le]
    convert Real.rpow_natCast ell 6 using 1 <;> norm_num
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hN.le
  have hs4 : (2*Real.sqrt (n : ℝ))^4 = 16*(n : ℝ)^2 := by
    calc
      _ = 16*((Real.sqrt (n : ℝ))^2)^2 := by ring
      _ = _ := by rw [hs]
  unfold fourthLowerScale
  rw [div_pow, mul_pow, ha, he6, hs4]
  field_simp
  <;> ring

theorem fourthLowerRate_fourth {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    fourthLowerRate n ell ^ 4 = (1+2*ell)^5/(n : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  unfold fourthLowerRate
  rw [div_pow, fourth_power_rpow (by linarith only [he]), fourth_power_rpow hN.le]
  norm_num [← Real.rpow_natCast]

theorem fourthLowerRate_scale_ratio_fourth {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    (fourthLowerRate n ell / fourthLowerScale n ell)^4 = 8*(2+ell⁻¹)^5 := by
  rw [div_pow, fourthLowerRate_fourth hn he, fourthLowerScale_fourth hn he]
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

private theorem fourth_root_fourth {x : ℝ} (hx : 0 ≤ x) :
    (x^4) ^ (1/4 : ℝ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem tendsto_fourthLowerRate_div_scale (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) :
    Tendsto (fun n => fourthLowerRate n (ell n) / fourthLowerScale n (ell n)) atTop (𝓝 4) := by
  have hpow : Tendsto (fun n => (fourthLowerRate n (ell n) / fourthLowerScale n (ell n))^4)
      atTop (𝓝 (256 : ℝ)) := by
    have hh : Tendsto (fun n => (2+(ell n)⁻¹)^5) atTop (𝓝 (32 : ℝ)) := by
      convert ((tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_inv_atTop_zero.comp he)).pow 5 using 1 <;> norm_num
    have hh' : Tendsto (fun n => 8*(2+(ell n)⁻¹)^5) atTop (𝓝 (256 : ℝ)) := by
      convert (tendsto_const_nhds (x := (8 : ℝ))).mul hh using 1 <;> norm_num
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
    simpa using (fourthLowerRate_scale_ratio_fourth hn hne).symm
  have hh := hpow.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1/4))
  have h256 : (256 : ℝ) ^ (1/4 : ℝ) = 4 := by
    convert fourth_root_fourth (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> norm_num
  rw [h256] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  exact fourth_root_fourth (div_nonneg (fourthLowerRate_pos hn hne).le (fourthLowerScale_pos hn hne).le)


theorem fourthLower_cube_div_le_rate_fourth {n : ℕ} (hn : 0 < n)
    {ell : ℝ} (he : 1 ≤ ell) :
    ell^3/(n : ℝ) ≤ fourthLowerRate n ell ^ 4 := by
  have he0 : 0 ≤ ell := le_trans (by norm_num) he
  rw [fourthLowerRate_fourth hn (lt_of_lt_of_le (by norm_num) he)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ell^3 ≤ ell^3*ell^2 := le_mul_of_one_le_right (pow_nonneg he0 3) (one_le_pow₀ he)
    _ = ell^5 := by ring
    _ ≤ (1+2*ell)^5 := pow_le_pow_left₀ he0 (by linarith only [he0]) 5

theorem tendsto_fourthLower_cube_div (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^3/(n : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n => fourthLowerRate n (ell n)^4) atTop (𝓝 0) := by
    simpa using hr.pow 4
  apply squeeze_zero' _ _ hpow
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 3) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hne
    exact fourthLower_cube_div_le_rate_fourth hn hne

theorem tendsto_fourthLowerTheta (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerTheta n (ell n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_fourthLower_cube_div ell he hr)
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg hn (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hne
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    unfold fourthLowerTheta
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hN) hN).2
    have he0 : 0 ≤ ell n := le_trans (by norm_num) hne
    have hp : ell n ≤ (ell n)^3 := by
      calc
        _ ≤ ell n*(ell n)^2 := le_mul_of_one_le_right he0 (one_le_pow₀ hne)
        _ = _ := by ring
    nlinarith only [mul_le_mul_of_nonneg_right hp hN.le, mul_nonneg hN.le (pow_nonneg he0 3)]

theorem fourthLowerScale_le_rate {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    fourthLowerScale n ell ≤ fourthLowerRate n ell := by
  apply (pow_le_pow_iff_left₀ (fourthLowerScale_pos hn he).le (fourthLowerRate_pos hn he).le (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [fourthLowerScale_fourth hn he, fourthLowerRate_fourth hn he]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have h5 : ell^5 ≤ (1+2*ell)^5 := pow_le_pow_left₀ he.le (by linarith only [he]) 5
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hN) hN).2
  nlinarith only [mul_le_mul_of_nonneg_right h5 hN.le,
    mul_nonneg hN.le (pow_nonneg (by linarith only [he] : 0 ≤ 1+2*ell) 5)]

theorem tendsto_fourthLowerScale (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerScale n (ell n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hr
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
    exact (fourthLowerScale_pos hn hne).le
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
    exact fourthLowerScale_le_rate hn hne


theorem fourth_amplitude_square_identity {θ : ℝ} (hθ : 0 < θ) :
    θ * (θ ^ (-1/4 : ℝ))^2 = Real.sqrt θ := by
  have hp : (θ ^ (-1/4 : ℝ))^2 = θ ^ (-1/2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]
    congr 1
    norm_num
  calc
    _ = θ^(1 : ℝ)*θ^(-1/2 : ℝ) := by rw [hp, Real.rpow_one]
    _ = θ^((1 : ℝ)+(-1/2 : ℝ)) := (Real.rpow_add hθ _ _).symm
    _ = Real.sqrt θ := by norm_num [Real.sqrt_eq_rpow]

theorem fourth_amplitude_fourth_identity {θ : ℝ} (hθ : 0 < θ) :
    θ * (θ ^ (-1/4 : ℝ))^4 = 1 := by
  rw [fourth_power_rpow hθ.le]
  norm_num [Real.rpow_neg_one]
  exact mul_inv_cancel₀ hθ.ne'

theorem fourth_amplitude_inverse_identity {θ : ℝ} (hθ : 0 < θ) :
    θ^(-1/4 : ℝ)*θ^(1/4 : ℝ) = 1 := by
  rw [← Real.rpow_add hθ]
  norm_num

theorem fourthLowerAmplitude_square {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell) :
    fourthLowerTheta n ell * fourthLowerAmplitude n ell ^ 2 = Real.sqrt (fourthLowerTheta n ell) :=
  fourth_amplitude_square_identity (fourthLowerTheta_pos hn he)

theorem fourthLowerAmplitude_sqrt_cube_identity {n : ℕ} {ell : ℝ} (he : 0 < ell) :
    fourthLowerAmplitude n ell * Real.sqrt (ell^3/(n : ℝ)) = 2*fourthLowerScale n ell := by
  have hs : Real.sqrt (ell^3) = ell^(3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1
    norm_num
  rw [Real.sqrt_div (pow_nonneg he.le 3), hs]
  unfold fourthLowerScale
  ring

theorem tendsto_fourthLowerAmplitude_sqrt_cube (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerAmplitude n (ell n)*Real.sqrt ((ell n)^3/(n : ℝ))) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 2*fourthLowerScale n (ell n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_fourthLowerScale ell he hr)
  apply hh.congr'
  filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ))] with n hne
  exact (fourthLowerAmplitude_sqrt_cube_identity hne).symm

theorem tendsto_fourthLowerAmplitude_square_theta (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerTheta n (ell n)*fourthLowerAmplitude n (ell n)^2) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.sqrt (fourthLowerTheta n (ell n))) atTop (𝓝 0) := by
    simpa using (tendsto_fourthLowerTheta ell he hr).sqrt
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  exact (fourthLowerAmplitude_square hn hne).symm

theorem tendsto_fourthLowerAmplitude (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerAmplitude n (ell n)) atTop atTop := by
  have ht : Tendsto (fun n => fourthLowerTheta n (ell n)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_fourthLowerTheta ell he hr, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
    exact fourthLowerTheta_pos hn hne
  have hh := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp ht.inv_tendsto_nhdsGT_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  change (fourthLowerTheta n (ell n))⁻¹ ^ (1/4 : ℝ) = fourthLowerAmplitude n (ell n)
  rw [Real.inv_rpow (fourthLowerTheta_pos hn hne).le]
  simpa only [fourthLowerAmplitude, neg_div] using
    (Real.rpow_neg (fourthLowerTheta_pos hn hne).le (1/4 : ℝ)).symm

theorem eventually_fourthLowerAmplitude_ge_one (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ fourthLowerAmplitude n (ell n) :=
  (tendsto_fourthLowerAmplitude ell he hr).eventually (eventually_ge_atTop 1)


theorem tendsto_fourthLowerAmplitude_inv (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    Tendsto (fun n => (fourthLowerAmplitude n (ell n))⁻¹) atTop (𝓝 0) :=
  (tendsto_fourthLowerAmplitude ell he hr).inv_tendsto_atTop

theorem eventually_fourthLowerTheta_lt_quarter (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop)
    (hr : Tendsto (fun n => fourthLowerRate n (ell n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, fourthLowerTheta n (ell n) < 1/4 :=
  (tendsto_fourthLowerTheta ell he hr).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))

end
end RectangleCLT.Companion.SplitV4
