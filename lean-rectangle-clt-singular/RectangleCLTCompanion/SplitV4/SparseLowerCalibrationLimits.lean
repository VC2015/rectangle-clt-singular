import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationScales
import RectangleCLTCompanion.SplitV4.LowerCalibrationScales

/-! Primitive deterministic limits for the actual sparse lower parameters.
The internal scalar regime is subsequently supplied by the paper's exact
K and R assumptions; no probabilistic comparison is assumed here. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem sparseLowerCoordinateRate_div_scale {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerCoordinateRate n ell B/sparseLowerScale n ell q B =
      2*(4*sparseLowerLog n ell q B)^(1-1/q)/Real.sqrt (sparseLowerKhat n ell q B) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 < sparseLowerLog n ell q B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  let f : ℝ := 1/q-1/4
  have hroot : Real.sqrt (sparseLowerKhat n ell q B) = Real.sqrt B*(n : ℝ)^f/ell^f := by
    rw [Real.sqrt_eq_rpow, sparseLowerKhat, Real.mul_rpow hB.le (Real.rpow_nonneg (div_pos hN he).le _),
      ← Real.rpow_mul (div_pos hN he).le]
    have hf : ((2/q-1/2 : ℝ)*(1/2)) = f := by dsimp [f]; ring
    rw [hf, Real.div_rpow hN.le he.le, ← Real.sqrt_eq_rpow]
    ring
  have hePow : ell^(3/2-1/q) = ell^(5/4 : ℝ)/ell^f := by
    rw [← Real.rpow_sub he]
    congr 1
    dsimp [f]
    ring
  have hnPow : (n : ℝ)^(1/2-1/q) = (n : ℝ)^(1/4 : ℝ)/(n : ℝ)^f := by
    rw [← Real.rpow_sub hN]
    congr 1
    dsimp [f]
    ring
  rw [sparseLowerScale_factor hn he hK, hroot, hePow, hnPow]
  unfold sparseLowerCoordinateRate
  have hNf := (Real.rpow_pos_of_pos hN f).ne'
  have hNq := (Real.rpow_pos_of_pos hN (1/4 : ℝ)).ne'
  have hef := (Real.rpow_pos_of_pos he f).ne'
  have heq := (Real.rpow_pos_of_pos he (5/4 : ℝ)).ne'
  have hw := (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ) (1-1/q)).ne'
  have hs := (Real.sqrt_pos.mpr hB).ne'
  have hBNZ := hB.ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt hB.le]
  ring

theorem tendsto_sparseLowerCoordinateRate_div_scale (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerCoordinateRate n (ell n) (B n)/sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0) := by
  let K := fun n => sparseLowerKhat n (ell n) q (B n)
  have hh : Tendsto (fun n => (2*4^(1-1/q))*(maskedFourthLog (K n)^(1-1/q)/(K n)^(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ)*4^(1-1/q))).mul
      (tendsto_sparseMaskLog_rpow_div_rpow K hK (1-1/q) (1/2) (by norm_num))
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  rw [sparseLowerCoordinateRate_div_scale hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK]
  have hΛ : 0 ≤ maskedFourthLog (K n) := le_trans (by norm_num) (maskedFourthLog_bounds hnK).1
  change (2*4^(1-1/q))*(maskedFourthLog (K n)^(1-1/q)/(K n)^(1/2 : ℝ)) =
    2*(4*maskedFourthLog (K n))^(1-1/q)/Real.sqrt (K n)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hΛ, Real.sqrt_eq_rpow]
  ring

theorem tendsto_sparseLowerCoordinateRate (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerCoordinateRate n (ell n) (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => (sparseLowerCoordinateRate n (ell n) (B n)/sparseLowerScale n (ell n) q (B n))*
      sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0) := by
    simpa using (tendsto_sparseLowerCoordinateRate_div_scale ell B q he hB hK).mul hd
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact div_mul_cancel₀ _ (sparseLowerScale_pos hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).ne'

theorem sparseLowerCoordinateRate_fourth {n : ℕ} {ell B : ℝ} (he : 0 ≤ ell) (hB : 0 ≤ B) :
    sparseLowerCoordinateRate n ell B^4 = B^2*ell^5/(n : ℝ) := by
  have hp (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : (x^a)^4 = x^(a*4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hs : (Real.sqrt B)^4 = B^2 := by
    calc
      _ = ((Real.sqrt B)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hB]
  have he5 : (ell^(5/4 : ℝ))^4 = ell^5 := by
    rw [hp ell he]
    convert Real.rpow_natCast ell 5 using 1 <;> norm_num
  have hn1 : ((n : ℝ)^(1/4 : ℝ))^4 = n := by
    rw [hp (n : ℝ) (Nat.cast_nonneg n)]
    norm_num
  unfold sparseLowerCoordinateRate
  rw [div_pow, mul_pow, hs, he5, hn1]

theorem tendsto_sparseLower_fifth_div (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^5/(n : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => sparseLowerCoordinateRate n (ell n) (B n)^4) atTop (𝓝 0) := by
    simpa using (tendsto_sparseLowerCoordinateRate ell B q he hB hK hd).pow 4
  apply squeeze_zero' _ _ hh
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 5) (Nat.cast_nonneg n)
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    rw [sparseLowerCoordinateRate_fourth hn (le_trans (by norm_num) (hB n))]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hb : 1 ≤ (B n)^2 := by nlinarith only [hB n]
    exact le_mul_of_one_le_left (pow_nonneg hn 5) hb

theorem tendsto_sparseLower_cube_div (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n)^3/(n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_sparseLower_fifth_div ell B q he hB hK hd)
  · filter_upwards [he.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    exact div_nonneg (pow_nonneg hn 3) (Nat.cast_nonneg n)
  · filter_upwards [he.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      _ ≤ (ell n)^3*(ell n)^2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn)
      _ = _ := by ring

theorem tendsto_sparseLowerTheta (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerTheta n (ell n) q (B n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_sparseLower_cube_div ell B q he hB hK hd)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
    exact (sparseLowerTheta_pos hn hne hnK).le
  · filter_upwards [he.eventually (eventually_ge_atTop (1 : ℝ)), hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hne hnK
    apply (maskedFourthTheta_le_ell_div (le_trans (by norm_num) hne) hnK).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      _ ≤ ell n*(ell n)^2 := le_mul_of_one_le_right (by linarith only [hne]) (one_le_pow₀ hne)
      _ = _ := by ring

theorem tendsto_sparseLowerPi_log (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerPi n (ell n) q (B n)*sparseLowerLog n (ell n) q (B n)) atTop (𝓝 0) := by
  have hh := tendsto_sparseMaskPi_log _ hK (1-4/q)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  rw [sparseLowerPi_eq_mask hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK]
  rfl

theorem tendsto_sparseLowerPi (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerPi n (ell n) q (B n)) atTop (𝓝 0) := by
  have hh := tendsto_sparseMaskPi _ hK (1-4/q)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact (sparseLowerPi_eq_mask hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).symm

theorem tendsto_sparseLowerVariance (ell B : ℕ → ℝ) {q : ℝ} (hq : 2 < q)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerVariance n (ell n) q (B n)) atTop (𝓝 0) := by
  have hp : 0 < 2/q := div_pos (by norm_num) (lt_trans (by norm_num) hq)
  have hh : Tendsto (fun n => sparseLowerTheta n (ell n) q (B n)^(2/q)/4) atTop (𝓝 0) := by
    have ht := (tendsto_sparseLowerTheta ell B q he hB hK hd).rpow_const (Or.inr hp.le)
    simpa only [Real.zero_rpow hp.ne', zero_div] using ht.div_const 4
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact (sparseLower_variance_identity hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).symm

theorem tendsto_sparseLowerCount (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/ell n) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerCount n (ell n) q (B n)) atTop atTop :=
  tendsto_maskedFourthCount ell _ he hK hΛ


theorem sparseLowerScale_square {n : ℕ} {ell q B : ℝ} (he : 0 ≤ ell) :
    sparseLowerScale n ell q B^2 = ell*sparseLowerAmplitude n ell q B^2*sparseLowerCount n ell q B^2/(n : ℝ) := by
  unfold sparseLowerScale
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt he, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem sparseLower_variance_scale_identity {n : ℕ} {ell q B : ℝ}
    (he : 0 ≤ ell) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    ell^2*sparseLowerVariance n ell q B =
      4*sparseLowerPi n ell q B*sparseLowerLog n ell q B*sparseLowerScale n ell q B^2 := by
  rw [sparseLowerScale_square he]
  have hΛNZ : sparseLowerLog n ell q B ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1).ne'
  unfold sparseLowerVariance sparseLowerTheta sparseLowerCount
  generalize hl : sparseLowerLog n ell q B = l at *
  field_simp [hΛNZ]
  ring_nf
  have hi : l*l⁻¹^2 = l⁻¹ := by
    calc
      _ = (l*l⁻¹)*l⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hΛNZ, one_mul]
  have hm := congrArg (fun z : ℝ => ell^3*sparseLowerPi n ell q B*sparseLowerAmplitude n ell q B^2*z*(n : ℝ)⁻¹*(1/4)) hi
  convert hm.symm using 1 <;> ring

theorem sparseLower_count_cost_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    (ell*sparseLowerAmplitude n ell q B^2*(sparseLowerCount n ell q B^2+sparseLowerCount n ell q B)/(n : ℝ))/
      sparseLowerScale n ell q B = sparseLowerScale n ell q B*(1+1/sparseLowerCount n ell q B) := by
  have hkNZ := (sparseLowerCount_pos he hK).ne'
  apply (div_eq_iff (sparseLowerScale_pos hn he hB hK).ne').2
  have hh : sparseLowerScale n ell q B*(1+1/sparseLowerCount n ell q B)*sparseLowerScale n ell q B =
      sparseLowerScale n ell q B^2*(1+1/sparseLowerCount n ell q B) := by ring
  rw [hh, sparseLowerScale_square he.le]
  field_simp
  <;> ring

theorem sparseLower_gaussian_cost_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    (ell*sparseLowerVariance n ell q B*(1+ell))/sparseLowerScale n ell q B =
      4*(sparseLowerPi n ell q B*sparseLowerLog n ell q B)*sparseLowerScale n ell q B*(1+1/ell) := by
  apply (div_eq_iff (sparseLowerScale_pos hn he hB hK).ne').2
  have hh := sparseLower_variance_scale_identity he.le hK
  have heNZ := he.ne'
  apply (mul_left_cancel₀ heNZ)
  field_simp
  have hm := congrArg (fun z : ℝ => z*(1+ell)) hh
  convert hm using 1 <;> ring

theorem tendsto_sparseLower_count_cost (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/ell n) atTop (𝓝 0))
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n*sparseLowerAmplitude n (ell n) q (B n)^2*
      (sparseLowerCount n (ell n) q (B n)^2+sparseLowerCount n (ell n) q (B n))/(n : ℝ))/
        sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)*(1+1/sparseLowerCount n (ell n) q (B n))) atTop (𝓝 0) := by
    have hk := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_sparseLowerCount ell B q he hK hΛ)
    simpa using hd.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hk)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact (sparseLower_count_cost_identity hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).symm

theorem tendsto_sparseLower_gaussian_cost (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ell n*sparseLowerVariance n (ell n) q (B n)*(1+ell n))/
      sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 4*(sparseLowerPi n (ell n) q (B n)*sparseLowerLog n (ell n) q (B n))*
      sparseLowerScale n (ell n) q (B n)*(1+1/ell n)) atTop (𝓝 0) := by
    have heInv := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop he
    simpa using (((tendsto_const_nhds (x := (4 : ℝ))).mul (tendsto_sparseLowerPi_log ell B q he hB hK)).mul
      hd).mul ((tendsto_const_nhds (x := (1 : ℝ))).add heInv)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact (sparseLower_gaussian_cost_identity hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).symm

theorem sparseLower_gaussian_coefficient_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    Real.sqrt (sparseLowerVariance n ell q B)*Real.sqrt (2*ell)/
      (sparseLowerAmplitude n ell q B*sparseLowerCount n ell q B/Real.sqrt n) =
        Real.sqrt (8*(sparseLowerPi n ell q B*sparseLowerLog n ell q B)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := sparseLowerAmplitude_pos hn he hB hK
  have hk := sparseLowerCount_pos he hK
  have hV : 0 ≤ sparseLowerVariance n ell q B := by
    rw [sparseLower_variance_identity hn he hB hK]
    exact div_nonneg (Real.rpow_nonneg (sparseLowerTheta_pos hn he hK).le _) (by norm_num)
  have hπ : 0 ≤ sparseLowerPi n ell q B := by
    rw [sparseLowerPi_eq_mask hn he hB hK]
    exact (sparseMaskPi_pos hK _).le
  have hΛ : 0 < sparseLowerLog n ell q B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  have hden := div_pos (mul_pos hA hk) (Real.sqrt_pos.mpr hN)
  apply (sq_eq_sq₀ (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hden.le) (Real.sqrt_nonneg _)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hV, Real.sq_sqrt (by linarith only [he] : 0 ≤ 2*ell),
    Real.sq_sqrt (mul_nonneg (by norm_num) (mul_nonneg hπ hΛ.le)), div_pow, mul_pow, Real.sq_sqrt hN.le]
  unfold sparseLowerVariance sparseLowerTheta sparseLowerCount
  have haNZ := hA.ne'
  field_simp
  <;> ring

theorem tendsto_sparseLower_gaussian_coefficient (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => Real.sqrt (sparseLowerVariance n (ell n) q (B n))*Real.sqrt (2*ell n)/
      (sparseLowerAmplitude n (ell n) q (B n)*sparseLowerCount n (ell n) q (B n)/Real.sqrt n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.sqrt (8*(sparseLowerPi n (ell n) q (B n)*sparseLowerLog n (ell n) q (B n)))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (8 : ℝ))).mul (tendsto_sparseLowerPi_log ell B q he hB hK)).sqrt
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
  exact (sparseLower_gaussian_coefficient_identity hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).symm

theorem sparseLower_coverage_lower {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B)
    (hΛ : sparseLowerLog n ell q B ≤ ell/10)
    (hlog : Real.log (2/sparseLowerPi n ell q B) ≤ (5/4)*sparseLowerLog n ell q B) :
    Real.exp (ell/4) ≤ Real.exp ell*(sparseLowerPi n ell q B/2)^sparseLowerCutoff n ell q B := by
  have hΛ0 : 0 ≤ sparseLowerLog n ell q B := le_trans (by norm_num) (maskedFourthLog_bounds hK).1
  have hk := (sparseLowerCount_pos he hK).le
  have hc : (sparseLowerCutoff n ell q B : ℝ) ≤ 2*sparseLowerCount n ell q B+1 := by
    unfold sparseLowerCutoff
    rw [sparseLowerTheta_count hn]
    exact (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hk)).le
  have hclog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (sparseLowerCutoff n ell q B))
  have hcΛ := mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5/4) hΛ0)
  have hkΛ : sparseLowerCount n ell q B*sparseLowerLog n ell q B = ell/4 := by
    have hΛNZ : sparseLowerLog n ell q B ≠ 0 := (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1).ne'
    unfold sparseLowerCount
    field_simp
    <;> ring
  have hπ : 0 < sparseLowerPi n ell q B := by rw [sparseLowerPi_eq_mask hn he hB hK]; exact sparseMaskPi_pos hK _
  have heq : sparseLowerPi n ell q B/2 = (2/sparseLowerPi n ell q B)⁻¹ := by field_simp
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hπ (by norm_num)),
    heq, Real.log_inv, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [hclog, hcΛ, hkΛ, hΛ]

theorem tendsto_sparseLower_coverage (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/ell n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.exp (ell n)*(sparseLowerPi n (ell n) q (B n)/2)^sparseLowerCutoff n (ell n) q (B n)) atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (2/sparseLowerPi n (ell n) q (B n))/sparseLowerLog n (ell n) q (B n)) atTop (𝓝 1) := by
    have hh := tendsto_sparseMask_log_inverse_ratio _ hK (1-4/q)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
    rw [sparseLowerPi_eq_mask hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK]
    rfl
  have hh : Tendsto (fun n => Real.exp (ell n/4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (he.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ)),
      hΛ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/10)),
      hlog.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 5/4))] with n hn hne hnK hnΛ hnlog
  apply sparseLower_coverage_lower hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK
  · linarith only [(div_le_iff₀ hne).mp hnΛ.le]
  · exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hnK).1)).mp hnlog.le


theorem sparseLowerCoordinateRate_ge_bounded {n : ℕ} (hn : 0 < n) {ell B : ℝ}
    (he : 0 < ell) (hB : 2 ≤ B) (hen : ell ≤ (n : ℝ)) :
    maskedFourthBoundedScale n ell ≤ sparseLowerCoordinateRate n ell B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hdb0 : 0 ≤ maskedFourthBoundedScale n ell := by unfold maskedFourthBoundedScale; positivity
  have hU0 : 0 ≤ sparseLowerCoordinateRate n ell B := by unfold sparseLowerCoordinateRate; positivity
  have hdb4 : maskedFourthBoundedScale n ell^4 = ell^6/(16*(n : ℝ)^2) := by
    have he6 : (ell^(3/2 : ℝ))^4 = ell^6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
      convert Real.rpow_natCast ell 6 using 1 <;> norm_num
    have hs4 : (2*Real.sqrt (n : ℝ))^4 = 16*(n : ℝ)^2 := by
      calc
        _ = 16*((Real.sqrt (n : ℝ))^2)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hN.le]
    unfold maskedFourthBoundedScale
    rw [div_pow, he6, hs4]
  apply (pow_le_pow_iff_left₀ hdb0 hU0 (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [hdb4, sparseLowerCoordinateRate_fourth he.le hB0.le]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hN 2)) hN).2
  have hh1 := mul_le_mul_of_nonneg_right hen (mul_nonneg (pow_nonneg he.le 5) hN.le)
  have hbb : (1 : ℝ) ≤ 16*B^2 := by nlinarith only [hB]
  have hh2 := mul_le_mul_of_nonneg_right hbb (mul_nonneg (pow_nonneg he.le 5) (pow_nonneg hN.le 2))
  nlinarith only [hh1, hh2]

theorem tendsto_sparseLower_scale_bounded_ratio (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerScale n (ell n) q (B n)/maskedFourthBoundedScale n (ell n)) atTop atTop := by
  have hRatio : Tendsto (fun n => sparseLowerCoordinateRate n (ell n) (B n)/sparseLowerScale n (ell n) q (B n))
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_sparseLowerCoordinateRate_div_scale ell B q he hB hK, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hne hnK
    have hU : 0 < sparseLowerCoordinateRate n (ell n) (B n) := by
      unfold sparseLowerCoordinateRate
      exact div_pos (mul_pos (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (hB n)))
        (Real.rpow_pos_of_pos hne _)) (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
    exact div_pos hU (sparseLowerScale_pos hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK)
  have hh : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)/sparseLowerCoordinateRate n (ell n) (B n)) atTop atTop := by
    have hi := hRatio.inv_tendsto_nhdsGT_zero
    apply hi.congr'
    filter_upwards [] with n
    change (sparseLowerCoordinateRate n (ell n) (B n)/sparseLowerScale n (ell n) q (B n))⁻¹ = _
    exact inv_div _ _
  have hEn : Tendsto (fun n => ell n/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_lower_ell_div_n he (tendsto_sparseLower_cube_div ell B q he hB hK hd)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ)), hEn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn hne hnK hneN
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ell n ≤ (n : ℝ) := by linarith only [(div_le_iff₀ hN).mp hneN.le]
  have hdb : 0 < maskedFourthBoundedScale n (ell n) := by
    unfold maskedFourthBoundedScale
    exact div_pos (Real.rpow_pos_of_pos hne _) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hN))
  exact div_le_div_of_nonneg_left (sparseLowerScale_pos hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK).le hdb
    (sparseLowerCoordinateRate_ge_bounded hn hne (hB n) hle)

theorem eventually_sparseLower_probabilities (ell B : ℕ → ℝ) {q : ℝ} (hq : 2 < q)
    (he : Tendsto ell atTop atTop) (hB : ∀ n, 2 ≤ B n)
    (hK : Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      0 < sparseLowerTheta n (ell n) q (B n) ∧ sparseLowerTheta n (ell n) q (B n) < 1 ∧
      0 < sparseLowerPi n (ell n) q (B n) ∧ sparseLowerPi n (ell n) q (B n) < 1 ∧
      0 < sparseLowerVariance n (ell n) q (B n) ∧ sparseLowerVariance n (ell n) q (B n) < 1/2 := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), he.eventually (eventually_gt_atTop (0 : ℝ)),
      hK.eventually (eventually_ge_atTop (2 : ℝ)),
      (tendsto_sparseLowerTheta ell B q he hB hK hd).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      (tendsto_sparseLowerPi ell B q he hB hK).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      (tendsto_sparseLowerVariance ell B hq he hB hK hd).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
    with n hn hne hnK hnθ hnπ hnv
  have hθ := sparseLowerTheta_pos hn hne hnK
  refine ⟨hθ, hnθ, ?_, hnπ, ?_, hnv⟩
  · rw [sparseLowerPi_eq_mask hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK]
    exact sparseMaskPi_pos hnK _
  · rw [sparseLower_variance_identity hn hne (lt_of_lt_of_le (by norm_num) (hB n)) hnK]
    exact div_pos (Real.rpow_pos_of_pos hθ _) (by norm_num)

end
end RectangleCLT.Companion.SplitV4
