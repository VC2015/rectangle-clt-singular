import RectangleCLTCompanion.SplitV4.FourthLowerCalibrationScales
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exact deterministic masked fourth-moment calibration for Theorem 6.
The logarithmic mask penalty, actual rounded coverage cutoff, and both
moment costs are functions of the stated parameters. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def maskedFourthLog (B : ℝ) : ℝ := Real.log (2*B^2)
def maskedFourthCount (ell B : ℝ) : ℝ := ell/(4*maskedFourthLog B)
def maskedFourthTheta (n : ℕ) (ell B : ℝ) : ℝ := maskedFourthCount ell B/(n : ℝ)
def maskedFourthPi (B : ℝ) : ℝ := 1/B^2
def maskedFourthAmplitude (n : ℕ) (ell B : ℝ) : ℝ :=
  (B/2)*(maskedFourthTheta n ell B)^(-1/4 : ℝ)
def maskedFourthVariance (n : ℕ) (ell B : ℝ) : ℝ :=
  maskedFourthTheta n ell B*maskedFourthPi B*maskedFourthAmplitude n ell B^2
def maskedFourthScale (n : ℕ) (ell B : ℝ) : ℝ :=
  maskedFourthAmplitude n ell B*maskedFourthCount ell B*Real.sqrt ell/Real.sqrt n
def maskedFourthRate (n : ℕ) (ell B : ℝ) : ℝ :=
  B*ell^(5/4 : ℝ)/((n : ℝ)^(1/4 : ℝ)*maskedFourthLog B^(3/4 : ℝ))
def maskedFourthCutoff (n : ℕ) (ell B : ℝ) : ℕ :=
  Nat.ceil (2*((n : ℝ)*maskedFourthTheta n ell B))
def maskedFourthBoundedScale (n : ℕ) (ell : ℝ) : ℝ := ell^(3/2 : ℝ)/(2*Real.sqrt n)

theorem maskedFourthLog_bounds {B : ℝ} (hB : 2 ≤ B) :
    1/2 ≤ maskedFourthLog B ∧ maskedFourthLog B ≤ 2*B := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hlog : maskedFourthLog B = Real.log 2+2*Real.log B := by
    rw [maskedFourthLog, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hB0 2).ne', Real.log_pow]
    norm_num
  have hlo2 : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hhi2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith only [hB])
  have hlogB := Real.log_le_sub_one_of_pos hB0
  rw [hlog]
  constructor <;> linarith only [hlo2, hhi2, hlogB0, hlogB]

theorem maskedFourthCount_pos {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    0 < maskedFourthCount ell B :=
  div_pos he (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1))

theorem maskedFourthTheta_pos {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    0 < maskedFourthTheta n ell B :=
  div_pos (maskedFourthCount_pos he hB) (by exact_mod_cast hn)

theorem maskedFourthAmplitude_pos {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    0 < maskedFourthAmplitude n ell B :=
  mul_pos (by linarith only [hB]) (Real.rpow_pos_of_pos (maskedFourthTheta_pos hn he hB) _)

theorem maskedFourthScale_pos {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    0 < maskedFourthScale n ell B := by
  unfold maskedFourthScale
  exact div_pos (mul_pos (mul_pos (maskedFourthAmplitude_pos hn he hB) (maskedFourthCount_pos he hB))
    (Real.sqrt_pos.mpr he)) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem maskedFourthTheta_count {n : ℕ} (hn : 0 < n) (ell B : ℝ) :
    (n : ℝ)*maskedFourthTheta n ell B = maskedFourthCount ell B := by
  unfold maskedFourthTheta
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem maskedFourth_envelope_identity {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthAmplitude n ell B*(maskedFourthTheta n ell B)^(1/4 : ℝ) = B/2 := by
  unfold maskedFourthAmplitude
  rw [mul_assoc, fourth_amplitude_inverse_identity (maskedFourthTheta_pos hn he hB), mul_one]

theorem maskedFourth_variance_identity {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthVariance n ell B = Real.sqrt (maskedFourthTheta n ell B)/4 := by
  have hh := fourth_amplitude_square_identity (maskedFourthTheta_pos hn he hB)
  have hBNZ : B ≠ 0 := (lt_of_lt_of_le (by norm_num) hB).ne'
  unfold maskedFourthVariance maskedFourthAmplitude maskedFourthPi
  rw [mul_pow, div_pow]
  field_simp
  nlinarith only [hh]

theorem maskedFourth_fourth_identity {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthTheta n ell B*maskedFourthPi B*maskedFourthAmplitude n ell B^4 = B^2/16 := by
  have hh := fourth_amplitude_fourth_identity (maskedFourthTheta_pos hn he hB)
  have hBNZ : B ≠ 0 := (lt_of_lt_of_le (by norm_num) hB).ne'
  unfold maskedFourthAmplitude maskedFourthPi
  calc
    _ = (B^2/16)*(maskedFourthTheta n ell B*(maskedFourthTheta n ell B^(-1/4 : ℝ))^4) := by
      field_simp
      <;> ring
    _ = _ := by rw [hh]; ring

private theorem pow_four_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x^a)^4 = x^(a*4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem maskedFourthRate_fourth {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthRate n ell B^4 = B^4*ell^5/((n : ℝ)*maskedFourthLog B^3) := by
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ : 0 ≤ maskedFourthLog B := le_trans (by norm_num) (maskedFourthLog_bounds hB).1
  unfold maskedFourthRate
  rw [div_pow, mul_pow, mul_pow, pow_four_rpow he.le, pow_four_rpow hN, pow_four_rpow hΛ]
  norm_num [← Real.rpow_natCast]

theorem maskedFourthScale_square {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) :
    maskedFourthScale n ell B^2 = ell*maskedFourthAmplitude n ell B^2*maskedFourthCount ell B^2/(n : ℝ) := by
  unfold maskedFourthScale
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt he.le, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem maskedFourthScale_fourth {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthScale n ell B^4 = B^4*ell^5/(1024*(n : ℝ)*maskedFourthLog B^3) := by
  have hθ := maskedFourthTheta_pos hn he hB
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hθ4 := fourth_amplitude_fourth_identity hθ
  have ha : maskedFourthAmplitude n ell B^4 = B^4/(16*maskedFourthTheta n ell B) := by
    have hp : (maskedFourthTheta n ell B^(-1/4 : ℝ))^4 = 1/maskedFourthTheta n ell B := by
      apply (eq_div_iff hθ.ne').2
      nlinarith only [hθ4]
    unfold maskedFourthAmplitude
    rw [mul_pow, div_pow, hp]
    ring
  calc
    _ = (maskedFourthScale n ell B^2)^2 := by ring
    _ = _ := by
      rw [maskedFourthScale_square hn he]
      have hpow : (maskedFourthAmplitude n ell B^2)^2 = maskedFourthAmplitude n ell B^4 := by ring
      simp only [div_pow, mul_pow]
      rw [hpow, ha]
      unfold maskedFourthTheta maskedFourthCount
      field_simp
      <;> ring

theorem maskedFourth_rate_conversion {n : ℕ} (hn : 0 < n) {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthRate n ell B = (4*Real.sqrt 2)*maskedFourthScale n ell B := by
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hR : 0 ≤ maskedFourthRate n ell B := by unfold maskedFourthRate; positivity
  have hd := (maskedFourthScale_pos hn he hB).le
  apply (pow_left_inj₀ hR (mul_nonneg (by positivity) hd) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow, maskedFourthRate_fourth hn he hB, maskedFourthScale_fourth hn he hB]
  have hs : (4*Real.sqrt 2)^4 = (1024 : ℝ) := by
    calc
      _ = 256*((Real.sqrt 2)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [hs]
  ring

theorem maskedFourthPi_log_bound {B : ℝ} (hB : 2 ≤ B) :
    0 ≤ maskedFourthPi B*maskedFourthLog B ∧ maskedFourthPi B*maskedFourthLog B ≤ 2/B := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hΛ := maskedFourthLog_bounds hB
  constructor
  · exact mul_nonneg (by unfold maskedFourthPi; positivity) (le_trans (by norm_num) hΛ.1)
  · unfold maskedFourthPi
    have heq : 1/B^2*maskedFourthLog B = maskedFourthLog B/B^2 := by ring
    rw [heq]
    apply (div_le_div_iff₀ (pow_pos hB0 2) hB0).2
    have hh := mul_le_mul_of_nonneg_right hΛ.2 hB0.le
    nlinarith only [hh]

theorem maskedFourth_fifth_div_le_rate_fourth {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 8 ≤ B) :
    ell^5/(n : ℝ) ≤ maskedFourthRate n ell B^4 := by
  have hB2 : 2 ≤ B := le_trans (by norm_num) hB
  have hΛ := maskedFourthLog_bounds hB2
  have hΛ0 : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) hΛ.1
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hpow : maskedFourthLog B^3 ≤ B^4 := by
    calc
      _ ≤ (2*B)^3 := pow_le_pow_left₀ hΛ0.le hΛ.2 3
      _ = 8*B^3 := by ring
      _ ≤ B*B^3 := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 3)
      _ = _ := by ring
  rw [maskedFourthRate_fourth hn he hB2]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff₀ hN (mul_pos hN (pow_pos hΛ0 3))).2
  nlinarith only [mul_le_mul_of_nonneg_left hpow (mul_nonneg (pow_nonneg he.le 5) hN.le)]


theorem maskedFourthTheta_le_ell_div {n : ℕ} {ell B : ℝ} (he : 0 ≤ ell) (hB : 2 ≤ B) :
    maskedFourthTheta n ell B ≤ ell/(n : ℝ) := by
  have hΛ := (maskedFourthLog_bounds hB).1
  have hk : maskedFourthCount ell B ≤ ell := by
    unfold maskedFourthCount
    apply (div_le_iff₀ (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hΛ))).2
    nlinarith only [mul_le_mul_of_nonneg_right hΛ he, he]
  exact div_le_div_of_nonneg_right hk (Nat.cast_nonneg n)

theorem tendsto_maskedFourth_fifth_div (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^5/(n : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => maskedFourthRate n (ell n) (B n)^4) atTop (𝓝 0) := by simpa using hr.pow 4
  apply squeeze_zero' _ _ hh
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 5) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (8 : ℝ))] with n hn hne hnB
    exact maskedFourth_fifth_div_le_rate_fourth hn hne hnB

theorem tendsto_maskedFourth_cube_div (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^3/(n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_maskedFourth_fifth_div ell B he hB hr)
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 3) (Nat.cast_nonneg n)
  · filter_upwards [he.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      _ ≤ (ell n)^3*(ell n)^2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn)
      _ = _ := by ring

theorem tendsto_maskedFourthTheta (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthTheta n (ell n) (B n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_maskedFourth_cube_div ell B he hB hr)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
    exact (maskedFourthTheta_pos hn hne hnB).le
  · filter_upwards [he.eventually (eventually_ge_atTop (1 : ℝ)), hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hne hnB
    apply (maskedFourthTheta_le_ell_div (le_trans (by norm_num) hne) hnB).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      _ ≤ ell n*(ell n)^2 := le_mul_of_one_le_right (by linarith only [hne]) (one_le_pow₀ hne)
      _ = _ := by ring

theorem tendsto_maskedFourthPi_log (B : ℕ → ℝ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun n => maskedFourthPi (B n)*maskedFourthLog (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => (2 : ℝ)/B n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hB
  apply squeeze_zero' _ _ hh
  · filter_upwards [hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    exact (maskedFourthPi_log_bound hn).1
  · filter_upwards [hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    exact (maskedFourthPi_log_bound hn).2

theorem tendsto_maskedFourthScale (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthScale n (ell n) (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => maskedFourthRate n (ell n) (B n)/(4*Real.sqrt 2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hr.div_const (4*Real.sqrt 2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  rw [maskedFourth_rate_conversion hn hne hnB]
  field_simp

theorem tendsto_maskedFourthVariance (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthVariance n (ell n) (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.sqrt (maskedFourthTheta n (ell n) (B n))/4) atTop (𝓝 0) := by
    simpa using (tendsto_maskedFourthTheta ell B he hB hr).sqrt.div_const 4
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  exact (maskedFourth_variance_identity hn hne hnB).symm

theorem tendsto_maskedFourthCount (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/ell n) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthCount (ell n) (B n)) atTop atTop := by
  have ht : Tendsto (fun n => maskedFourthLog (B n)/ell n) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hΛ, ?_⟩
    filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ)), hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hne hnB
    exact div_pos (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hnB).1) hne
  have hh : Tendsto (fun n => (1/4 : ℝ)*(maskedFourthLog (B n)/ell n)⁻¹) atTop atTop :=
    ht.inv_tendsto_nhdsGT_zero.const_mul_atTop (by norm_num)
  apply hh.congr'
  filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ)), hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hne hnB
  unfold maskedFourthCount
  field_simp
  <;> ring

theorem maskedFourth_variance_scale_identity {n : ℕ} (hn : 0 < n)
    {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    ell^2*maskedFourthVariance n ell B =
      4*maskedFourthPi B*maskedFourthLog B*maskedFourthScale n ell B^2 := by
  rw [maskedFourthScale_square hn he]
  have hΛNZ : maskedFourthLog B ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1).ne'
  unfold maskedFourthVariance maskedFourthTheta maskedFourthCount
  field_simp
  <;> ring

theorem maskedFourth_count_cost_identity {n : ℕ} (hn : 0 < n)
    {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    (ell*maskedFourthAmplitude n ell B^2*(maskedFourthCount ell B^2+maskedFourthCount ell B)/(n : ℝ))/
      maskedFourthScale n ell B = maskedFourthScale n ell B*(1+1/maskedFourthCount ell B) := by
  have hkNZ := (maskedFourthCount_pos he hB).ne'
  apply (div_eq_iff (maskedFourthScale_pos hn he hB).ne').2
  have hh : maskedFourthScale n ell B*(1+1/maskedFourthCount ell B)*maskedFourthScale n ell B =
      maskedFourthScale n ell B^2*(1+1/maskedFourthCount ell B) := by ring
  rw [hh, maskedFourthScale_square hn he]
  field_simp
  <;> ring

theorem maskedFourth_gaussian_cost_identity {n : ℕ} (hn : 0 < n)
    {ell B : ℝ} (he : 0 < ell) (hB : 2 ≤ B) :
    (ell*maskedFourthVariance n ell B*(1+ell))/maskedFourthScale n ell B =
      4*(maskedFourthPi B*maskedFourthLog B)*maskedFourthScale n ell B*(1+1/ell) := by
  apply (div_eq_iff (maskedFourthScale_pos hn he hB).ne').2
  have hh := maskedFourth_variance_scale_identity hn he hB
  have heNZ := he.ne'
  apply (mul_left_cancel₀ heNZ)
  field_simp
  have hm := congrArg (fun z : ℝ => z*(1+ell)) hh
  convert hm using 1 <;> ring

theorem tendsto_maskedFourth_count_cost (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/ell n) atTop (𝓝 0))
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n*maskedFourthAmplitude n (ell n) (B n)^2*
      (maskedFourthCount (ell n) (B n)^2+maskedFourthCount (ell n) (B n))/(n : ℝ))/
        maskedFourthScale n (ell n) (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => maskedFourthScale n (ell n) (B n)*(1+1/maskedFourthCount (ell n) (B n))) atTop (𝓝 0) := by
    have hk := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_maskedFourthCount ell B he hB hΛ)
    simpa using (tendsto_maskedFourthScale ell B he hB hr).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hk)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  exact (maskedFourth_count_cost_identity hn hne hnB).symm

theorem tendsto_maskedFourth_gaussian_cost (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n*maskedFourthVariance n (ell n) (B n)*(1+ell n))/
      maskedFourthScale n (ell n) (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 4*(maskedFourthPi (B n)*maskedFourthLog (B n))*
      maskedFourthScale n (ell n) (B n)*(1+1/ell n)) atTop (𝓝 0) := by
    have heInv := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop he
    simpa using (((tendsto_const_nhds (x := (4 : ℝ))).mul (tendsto_maskedFourthPi_log B hB)).mul
      (tendsto_maskedFourthScale ell B he hB hr)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add heInv)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  exact (maskedFourth_gaussian_cost_identity hn hne hnB).symm


theorem maskedFourth_log_half_pi {B : ℝ} (hB : 2 ≤ B) :
    Real.log (maskedFourthPi B/2) = -maskedFourthLog B := by
  have hBNZ : B ≠ 0 := (lt_of_lt_of_le (by norm_num) hB).ne'
  have hh : maskedFourthPi B/2 = (2*B^2)⁻¹ := by unfold maskedFourthPi; field_simp; ring
  rw [hh, Real.log_inv]
  rfl

theorem maskedFourth_coverage_lower {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 2 ≤ B) (hΛ : maskedFourthLog B ≤ ell/4) :
    Real.exp (ell/4) ≤ Real.exp ell*(maskedFourthPi B/2)^maskedFourthCutoff n ell B := by
  have hΛ0 : 0 ≤ maskedFourthLog B := le_trans (by norm_num) (maskedFourthLog_bounds hB).1
  have hk := (maskedFourthCount_pos he hB).le
  have hc : (maskedFourthCutoff n ell B : ℝ) ≤ 2*maskedFourthCount ell B+1 := by
    unfold maskedFourthCutoff
    rw [maskedFourthTheta_count hn]
    exact (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hk)).le
  have hcΛ := mul_le_mul_of_nonneg_right hc hΛ0
  have hkΛ : maskedFourthCount ell B*maskedFourthLog B = ell/4 := by
    have hΛNZ : maskedFourthLog B ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1).ne'
    unfold maskedFourthCount
    field_simp
    <;> ring
  have hbase : 0 < maskedFourthPi B/2 := by unfold maskedFourthPi; positivity
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase, maskedFourth_log_half_pi hB,
    ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [hcΛ, hkΛ, hΛ]

theorem tendsto_maskedFourth_coverage (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/ell n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.exp (ell n)*(maskedFourthPi (B n)/2)^maskedFourthCutoff n (ell n) (B n)) atTop atTop := by
  have hh : Tendsto (fun n => Real.exp (ell n/4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (he.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ)),
      hΛ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with n hn hne hnB hnΛ
  apply maskedFourth_coverage_lower hn hne hnB
  linarith only [(div_le_iff₀ hne).mp hnΛ.le]

theorem maskedFourth_scale_bounded_ratio {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 2 ≤ B) :
    maskedFourthScale n ell B/maskedFourthBoundedScale n ell =
      (B/(4*maskedFourthLog B))*(maskedFourthTheta n ell B)^(-1/4 : ℝ) := by
  have hsqrtN := (Real.sqrt_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n)).ne'
  have hsqrtE := (Real.sqrt_pos.mpr he).ne'
  have hΛNZ : maskedFourthLog B ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1).ne'
  have hePow : ell^(3/2 : ℝ) = ell*Real.sqrt ell := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add he, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold maskedFourthScale maskedFourthBoundedScale maskedFourthAmplitude maskedFourthCount
  rw [hePow]
  field_simp
  <;> ring

theorem maskedFourth_scale_bounded_ratio_lower {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 2 ≤ B) :
    (maskedFourthTheta n ell B)^(-1/4 : ℝ)/8 ≤
      maskedFourthScale n ell B/maskedFourthBoundedScale n ell := by
  rw [maskedFourth_scale_bounded_ratio hn he hB]
  have hΛ := maskedFourthLog_bounds hB
  have hΛ0 : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) hΛ.1
  have hc : (1/8 : ℝ) ≤ B/(4*maskedFourthLog B) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hΛ0)).2
    linarith only [hΛ.2]
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (maskedFourthTheta_pos hn he hB).le (-1/4 : ℝ))
  linarith only [hh]

theorem tendsto_maskedFourth_scale_bounded_ratio (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => maskedFourthScale n (ell n) (B n)/maskedFourthBoundedScale n (ell n)) atTop atTop := by
  have ht : Tendsto (fun n => maskedFourthTheta n (ell n) (B n)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_maskedFourthTheta ell B he hB hr, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
    exact maskedFourthTheta_pos hn hne hnB
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp ht.inv_tendsto_nhdsGT_zero
  have hpow' : Tendsto (fun n => (maskedFourthTheta n (ell n) (B n))^(-1/4 : ℝ)/8) atTop atTop := by
    have hh := hpow.atTop_div_const (by norm_num : (0 : ℝ) < 8)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
    change ((maskedFourthTheta n (ell n) (B n))⁻¹)^(1/4 : ℝ)/8 = _
    rw [Real.inv_rpow (maskedFourthTheta_pos hn hne hnB).le]
    simp only [neg_div, Real.rpow_neg (maskedFourthTheta_pos hn hne hnB).le]
  apply tendsto_atTop_mono' atTop _ hpow'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  exact maskedFourth_scale_bounded_ratio_lower hn hne hnB

theorem maskedFourth_gaussian_coefficient_identity {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 2 ≤ B) :
    Real.sqrt (maskedFourthVariance n ell B)*Real.sqrt (2*ell)/
      (maskedFourthAmplitude n ell B*maskedFourthCount ell B/Real.sqrt n) =
        Real.sqrt (8*(maskedFourthPi B*maskedFourthLog B)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := maskedFourthAmplitude_pos hn he hB
  have hk := maskedFourthCount_pos he hB
  have hV : 0 ≤ maskedFourthVariance n ell B := by
    rw [maskedFourth_variance_identity hn he hB]
    positivity
  have hπ : 0 ≤ maskedFourthPi B := by unfold maskedFourthPi; positivity
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hd := div_pos (mul_pos hA hk) (Real.sqrt_pos.mpr hN)
  apply (sq_eq_sq₀ (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hd.le) (Real.sqrt_nonneg _)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hV, Real.sq_sqrt (by linarith only [he] : 0 ≤ 2*ell),
    Real.sq_sqrt (mul_nonneg (by norm_num) (mul_nonneg hπ hΛ.le)), div_pow, mul_pow, Real.sq_sqrt hN.le]
  unfold maskedFourthVariance maskedFourthTheta maskedFourthCount
  have haNZ := hA.ne'
  field_simp
  <;> ring

theorem tendsto_maskedFourth_gaussian_coefficient (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop) :
    Tendsto (fun n => Real.sqrt (maskedFourthVariance n (ell n) (B n))*Real.sqrt (2*ell n)/
      (maskedFourthAmplitude n (ell n) (B n)*maskedFourthCount (ell n) (B n)/Real.sqrt n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.sqrt (8*(maskedFourthPi (B n)*maskedFourthLog (B n)))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (8 : ℝ))).mul (tendsto_maskedFourthPi_log B hB)).sqrt
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnB
  exact (maskedFourth_gaussian_coefficient_identity hn hne hnB).symm

theorem eventually_maskedFourth_probabilities (ell B : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (hB : Tendsto B atTop atTop)
    (hr : Tendsto (fun n => maskedFourthRate n (ell n) (B n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      0 < maskedFourthTheta n (ell n) (B n) ∧ maskedFourthTheta n (ell n) (B n) < 1 ∧
      0 < maskedFourthPi (B n) ∧ maskedFourthPi (B n) < 1 ∧
      0 < maskedFourthVariance n (ell n) (B n) ∧ maskedFourthVariance n (ell n) (B n) < 1/2 := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_ge_atTop (2 : ℝ)),
      (tendsto_maskedFourthTheta ell B he hB hr).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      (tendsto_maskedFourthVariance ell B he hB hr).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
    with n hn hne hnB hnθ hnv
  have hθ := maskedFourthTheta_pos hn hne hnB
  refine ⟨hθ, hnθ, ?_, ?_, ?_, hnv⟩
  · unfold maskedFourthPi
    positivity
  · unfold maskedFourthPi
    exact (div_lt_one (by nlinarith only [hnB] : (0 : ℝ) < B n^2)).mpr (by nlinarith only [hnB])
  · rw [maskedFourth_variance_identity hn hne hnB]
    exact div_pos (Real.sqrt_pos.mpr hθ) (by norm_num)

end
end RectangleCLT.Companion.SplitV4
