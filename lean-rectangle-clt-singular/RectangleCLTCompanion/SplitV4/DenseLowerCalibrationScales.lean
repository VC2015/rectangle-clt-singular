import RectangleCLTCompanion.SplitV4.FourthLowerCalibrationScales

/-! Numerical calibration of the dense polynomial lower family for q>4.
All parameters are deterministic, and every limiting premise concerns the
actual specified envelope rate rather than a probability estimate. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def denseLowerAmplitude (n : ℕ) (ell q B : ℝ) : ℝ :=
  (B-1)*(fourthLowerTheta n ell)^(-1/q)
def denseLowerScale (n : ℕ) (ell q B : ℝ) : ℝ :=
  denseLowerAmplitude n ell q B*ell^(3/2 : ℝ)/(2*Real.sqrt n)
def denseLowerEnvelopeRate (n : ℕ) (ell q B : ℝ) : ℝ :=
  B*(1+2*ell)^(3/2-1/q)/(n : ℝ)^(1/2-1/q)

theorem dense_amplitude_inverse_identity {θ : ℝ} (hθ : 0 < θ) (q B : ℝ) :
    ((B-1)*θ^(-1/q))*θ^(1/q) = B-1 := by
  rw [mul_assoc, ← Real.rpow_add hθ]
  have hh : -1/q+1/q = (0 : ℝ) := by ring
  rw [hh, Real.rpow_zero, mul_one]

theorem dense_amplitude_moment_identity {θ : ℝ} (hθ : 0 < θ) (q B : ℝ) (k : ℕ) :
    θ*((B-1)*θ^(-1/q))^k = (B-1)^k*θ^(1-(k : ℝ)/q) := by
  have hp : (θ^(-1/q))^k = θ^((-1/q)*(k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]
  rw [mul_pow, hp]
  calc
    _ = (B-1)^k*(θ^(1 : ℝ)*θ^((-1/q)*(k : ℝ))) := by rw [Real.rpow_one]; ring
    _ = (B-1)^k*θ^((1 : ℝ)+(-1/q)*(k : ℝ)) := by rw [Real.rpow_add hθ]
    _ = _ := by congr 2; ring

theorem dense_amplitude_square_identity {θ : ℝ} (hθ : 0 < θ) (q B : ℝ) :
    θ*((B-1)*θ^(-1/q))^2 = (B-1)^2*θ^(1-2/q) := by
  simpa using dense_amplitude_moment_identity hθ q B 2

theorem dense_amplitude_fourth_identity {θ : ℝ} (hθ : 0 < θ) (q B : ℝ) :
    θ*((B-1)*θ^(-1/q))^4 = (B-1)^4*θ^(1-4/q) := by
  simpa using dense_amplitude_moment_identity hθ q B 4

theorem denseLowerAmplitude_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 1 < B) : 0 < denseLowerAmplitude n ell q B :=
  mul_pos (sub_pos.mpr hB) (Real.rpow_pos_of_pos (fourthLowerTheta_pos hn he) _)

theorem denseLowerScale_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 1 < B) : 0 < denseLowerScale n ell q B := by
  unfold denseLowerScale
  exact div_pos (mul_pos (denseLowerAmplitude_pos hn he hB) (Real.rpow_pos_of_pos he _))
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by exact_mod_cast hn)))

theorem denseLowerEnvelopeRate_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) : 0 < denseLowerEnvelopeRate n ell q B := by
  unfold denseLowerEnvelopeRate
  exact div_pos (mul_pos hB (Real.rpow_pos_of_pos (by linarith only [he]) _))
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

theorem denseLowerScale_factor {n : ℕ} (hn : 0 < n) {ell q B : ℝ} (he : 0 < ell) :
    denseLowerScale n ell q B =
      ((B-1)*2^(1/q)/2)*ell^(3/2-1/q)/(n : ℝ)^(1/2-1/q) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := fourthLowerTheta_pos hn he
  have ha : (fourthLowerTheta n ell)^(-1/q) = 2^(1/q)*(n : ℝ)^(1/q)/ell^(1/q) := by
    calc
      _ = ((fourthLowerTheta n ell)^(1/q))⁻¹ := by
        convert Real.rpow_neg ht.le (1/q) using 1 <;> congr 1 <;> ring
      _ = ((fourthLowerTheta n ell)⁻¹)^(1/q) := (Real.inv_rpow ht.le _).symm
      _ = (2*(n : ℝ)/ell)^(1/q) := by congr 1; unfold fourthLowerTheta; field_simp
      _ = _ := by rw [Real.div_rpow (mul_nonneg (by norm_num) hN.le) he.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN.le]
  have hePow : ell^(3/2-1/q)*ell^(1/q) = ell^(3/2 : ℝ) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hnPow : (n : ℝ)^(1/2-1/q)*(n : ℝ)^(1/q) = Real.sqrt (n : ℝ) := by
    rw [← Real.rpow_add hN]
    have hh : (1/2 : ℝ)-1/q+1/q = 1/2 := by ring
    rw [hh, ← Real.sqrt_eq_rpow]
  unfold denseLowerScale denseLowerAmplitude
  rw [ha, ← hePow, ← hnPow]
  have heNZ := (Real.rpow_pos_of_pos he (1/q)).ne'
  have hnNZ := (Real.rpow_pos_of_pos hN (1/q)).ne'
  have hnNZ' := (Real.rpow_pos_of_pos hN (1/2-1/q)).ne'
  field_simp
  <;> ring

theorem denseLowerEnvelopeRate_div_scale {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 1 < B) :
    denseLowerEnvelopeRate n ell q B/denseLowerScale n ell q B =
      (B/(B-1))*2^(1-1/q)*((1+2*ell)/ell)^(3/2-1/q) := by
  rw [denseLowerScale_factor hn he]
  unfold denseLowerEnvelopeRate
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.div_rpow (by linarith only [he] : 0 ≤ 1+2*ell) he.le]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hBNZ : B-1 ≠ 0 := (sub_pos.mpr hB).ne'
  have hnNZ := (Real.rpow_pos_of_pos hN (1/2-1/q)).ne'
  have heNZ := (Real.rpow_pos_of_pos he (3/2-1/q)).ne'
  have h2NZ := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1/q)).ne'
  field_simp
  <;> ring

theorem tendsto_denseLowerEnvelopeRate_div_scale (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) (q : ℝ) {B : ℝ} (hB : 1 < B) :
    Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B/denseLowerScale n (ell n) q B)
      atTop (𝓝 ((B/(B-1))*2^(5/2-2/q))) := by
  have hbase : Tendsto (fun n => (1+2*ell n)/ell n) atTop (𝓝 (2 : ℝ)) := by
    have hh : Tendsto (fun n => 2+(ell n)⁻¹) atTop (𝓝 (2 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_inv_atTop_zero.comp he)
    apply hh.congr'
    filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ))] with n hne
    field_simp
    <;> ring
  have hh := (tendsto_const_nhds (x := (B/(B-1))*2^(1-1/q))).mul
    (hbase.rpow_const (p := (3/2 : ℝ)-1/q) (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hc : (B/(B-1))*2^(1-1/q)*2^(3/2-1/q) = (B/(B-1))*2^(5/2-2/q) := by
    rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  exact (denseLowerEnvelopeRate_div_scale hn hne hB).symm

theorem denseLowerEnvelopeRate_root {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hq : 2 < q) (hB : 0 < B) :
    (denseLowerEnvelopeRate n ell q B/B)^(1/(1/2-1/q)) =
      (1+2*ell)^((3/2-1/q)/(1/2-1/q))/(n : ℝ) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have ha : 0 < (1/2 : ℝ)-1/q := by
    have hh : 1/q < (1/2 : ℝ) := (div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hq])
    linarith only [hh]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < 1+2*ell := by linarith only [he]
  have hh : denseLowerEnvelopeRate n ell q B/B = (1+2*ell)^(3/2-1/q)/(n : ℝ)^(1/2-1/q) := by
    unfold denseLowerEnvelopeRate
    field_simp
    <;> ring
  rw [hh, Real.div_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul hL.le, ← Real.rpow_mul hN.le]
  have hcancel : ((1/2 : ℝ)-1/q)*(1/(1/2-1/q)) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ ha.ne'
  rw [hcancel, Real.rpow_one]
  congr 2
  ring

theorem denseLower_cube_div_le_rate_root {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 1 ≤ ell) (hq : 4 < q) (hB : 0 < B) :
    ell^3/(n : ℝ) ≤ (denseLowerEnvelopeRate n ell q B/B)^(1/(1/2-1/q)) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have ht : 0 < 1/q := one_div_pos.mpr hq0
  have ha : 0 < (1/2 : ℝ)-1/q := by
    have hh : 1/q < (1/2 : ℝ) := (div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hq])
    linarith only [hh]
  have hpower : (3 : ℝ) ≤ (3/2-1/q)/(1/2-1/q) := by
    apply (le_div_iff₀ ha).2
    linarith only [ht]
  rw [denseLowerEnvelopeRate_root hn (lt_of_lt_of_le (by norm_num) he) (by linarith only [hq]) hB]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ell^3 ≤ (1+2*ell)^3 := pow_le_pow_left₀ (by linarith only [he]) (by linarith only [he]) 3
    _ = (1+2*ell)^(3 : ℝ) := (Real.rpow_natCast _ 3).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith only [he]) hpower

theorem tendsto_denseLower_cube_div (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^3/(n : ℝ)) atTop (𝓝 0) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have ha : 0 < (1/2 : ℝ)-1/q := by
    have hh : 1/q < (1/2 : ℝ) := (div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hq])
    linarith only [hh]
  have hh : Tendsto (fun n => (denseLowerEnvelopeRate n (ell n) q B/B)^(1/(1/2-1/q))) atTop (𝓝 0) := by
    have hd := hV.div_const B
    have hr := hd.rpow_const (Or.inr (one_div_pos.mpr ha).le)
    simpa only [zero_div, Real.zero_rpow (one_div_pos.mpr ha).ne'] using hr
  apply squeeze_zero' _ _ hh
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 3) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hne
    exact denseLower_cube_div_le_rate_root hn hne hq (lt_trans (by norm_num) hB)


theorem tendsto_denseLowerTheta (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerTheta n (ell n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_denseLower_cube_div ell he hq hB hV)
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

theorem tendsto_denseLowerScale (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => denseLowerScale n (ell n) q B) atTop (𝓝 0) := by
  have hc : (B/(B-1))*2^(5/2-2/q) ≠ 0 := by
    exact (mul_pos (div_pos (lt_trans (by norm_num) hB) (sub_pos.mpr hB))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).ne'
  have hh := hV.div (tendsto_denseLowerEnvelopeRate_div_scale ell he q hB) hc
  have hh' : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B/
      (denseLowerEnvelopeRate n (ell n) q B/denseLowerScale n (ell n) q B)) atTop (𝓝 0) := by
    simpa only [zero_div] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  have hvNZ := (denseLowerEnvelopeRate_pos hn hne (lt_trans (by norm_num) hB) (q := q)).ne'
  have hdNZ := (denseLowerScale_pos hn hne hB (q := q)).ne'
  field_simp

theorem denseLowerAmplitude_sqrt_cube_identity {n : ℕ} {ell q B : ℝ} (he : 0 < ell) :
    denseLowerAmplitude n ell q B*Real.sqrt (ell^3/(n : ℝ)) = 2*denseLowerScale n ell q B := by
  have hs : Real.sqrt (ell^3) = ell^(3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1
    norm_num
  rw [Real.sqrt_div (pow_nonneg he.le 3), hs]
  unfold denseLowerScale
  ring

theorem tendsto_denseLowerAmplitude_sqrt_cube (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => denseLowerAmplitude n (ell n) q B*Real.sqrt ((ell n)^3/(n : ℝ))) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 2*denseLowerScale n (ell n) q B) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_denseLowerScale ell he hq hB hV)
  apply hh.congr'
  filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ))] with n hne
  exact (denseLowerAmplitude_sqrt_cube_identity hne).symm

theorem tendsto_denseLowerAmplitude_moment_theta (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0))
    (k : ℕ) (hk : 0 < 1-(k : ℝ)/q) :
    Tendsto (fun n => fourthLowerTheta n (ell n)*denseLowerAmplitude n (ell n) q B^k) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => (B-1)^k*(fourthLowerTheta n (ell n))^(1-(k : ℝ)/q)) atTop (𝓝 0) := by
    have ht := (tendsto_denseLowerTheta ell he hq hB hV).rpow_const (Or.inr hk.le)
    simpa only [Real.zero_rpow hk.ne', mul_zero] using (tendsto_const_nhds (x := (B-1)^k)).mul ht
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  exact (dense_amplitude_moment_identity (fourthLowerTheta_pos hn hne) q B k).symm

theorem tendsto_denseLowerAmplitude_square_theta (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerTheta n (ell n)*denseLowerAmplitude n (ell n) q B^2) atTop (𝓝 0) := by
  apply tendsto_denseLowerAmplitude_moment_theta ell he hq hB hV 2
  norm_num only [Nat.cast_ofNat]
  have hh : (2 : ℝ)/q < 1 := (div_lt_one (lt_trans (by norm_num) hq)).mpr (by linarith only [hq])
  linarith only [hh]

theorem tendsto_denseLowerAmplitude_fourth_theta (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => fourthLowerTheta n (ell n)*denseLowerAmplitude n (ell n) q B^4) atTop (𝓝 0) := by
  apply tendsto_denseLowerAmplitude_moment_theta ell he hq hB hV 4
  norm_num only [Nat.cast_ofNat]
  exact sub_pos.mpr ((div_lt_one (lt_trans (by norm_num) hq)).mpr hq)

theorem tendsto_denseLowerAmplitude (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => denseLowerAmplitude n (ell n) q B) atTop atTop := by
  have ht : Tendsto (fun n => fourthLowerTheta n (ell n)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_denseLowerTheta ell he hq hB hV, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
    exact fourthLowerTheta_pos hn hne
  have hp := (tendsto_rpow_atTop (one_div_pos.mpr (lt_trans (by norm_num) hq))).comp ht.inv_tendsto_nhdsGT_zero
  have hp' : Tendsto (fun n => (B-1)*((fourthLowerTheta n (ell n))⁻¹)^(1/q)) atTop atTop :=
    hp.const_mul_atTop (sub_pos.mpr hB)
  apply hp'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  rw [Real.inv_rpow (fourthLowerTheta_pos hn hne).le]
  simp only [denseLowerAmplitude, neg_div, Real.rpow_neg (fourthLowerTheta_pos hn hne).le]

theorem tendsto_denseLowerAmplitude_inv (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => (denseLowerAmplitude n (ell n) q B)⁻¹) atTop (𝓝 0) :=
  (tendsto_denseLowerAmplitude ell he hq hB hV).inv_tendsto_atTop

theorem eventually_denseLowerAmplitude_ge_one (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ denseLowerAmplitude n (ell n) q B :=
  (tendsto_denseLowerAmplitude ell he hq hB hV).eventually (eventually_ge_atTop 1)

theorem eventually_denseLowerVariance_lt_half (ell : ℕ → ℝ) (he : Tendsto ell atTop atTop)
    {q B : ℝ} (hq : 4 < q) (hB : 1 < B)
    (hV : Tendsto (fun n => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, fourthLowerTheta n (ell n)*denseLowerAmplitude n (ell n) q B^2 < 1/2 :=
  (tendsto_denseLowerAmplitude_square_theta ell he hq hB hV).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))

end
end RectangleCLT.Companion.SplitV4
