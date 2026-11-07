import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationScales

/-! Conversion between the paper's sparse logarithmic scale and the actual
mask parameters. All limits use only eventual positivity from the stated
divergence assumptions. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem tendsto_sparse_dimension_ratio (ell : ℕ → ℝ)
    (he : Tendsto ell atTop atTop) :
    Tendsto (fun n => (1+2*ell n)/ell n) atTop (𝓝 (2 : ℝ)) := by
  have hh : Tendsto (fun n => 2+(ell n)⁻¹) atTop (𝓝 (2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_inv_atTop_zero.comp he)
  apply hh.congr'
  filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  field_simp
  <;> ring

theorem sparseLowerKhat_factor {n : ℕ} {ell q B : ℝ} (he : 0 < ell) :
    sparseLowerKhat n ell q B =
      sparseLowerK n ell q B*((1+2*ell)/ell)^(2/q-1/2) := by
  have hL : 0 < 1+2*ell := by linarith only [he]
  unfold sparseLowerKhat sparseLowerK
  rw [mul_assoc, ← Real.mul_rpow (div_nonneg (Nat.cast_nonneg n) hL.le)
    (div_nonneg hL.le he.le)]
  congr 2
  field_simp

theorem tendsto_sparseLowerKhat_div_K (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)/sparseLowerK n (ell n) q (B n))
      atTop (𝓝 ((2 : ℝ)^(2/q-1/2))) := by
  apply ((tendsto_sparse_dimension_ratio ell he).rpow_const
    (p := 2/q-1/2) (Or.inl (by norm_num : (2 : ℝ) ≠ 0))).congr'
  filter_upwards [he.eventually (eventually_gt_atTop (0 : ℝ)),
    hK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hkn
  rw [sparseLowerKhat_factor hn]
  field_simp

theorem tendsto_sparseLowerKhat (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerKhat n (ell n) q (B n)) atTop atTop := by
  have hh := hK.atTop_mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2/q-1/2))
    (tendsto_sparseLowerKhat_div_K ell B q he hK)
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  field_simp

theorem tendsto_log_exp_add_sub_log (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => Real.log (Real.exp 1+K n)-Real.log (K n)) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => 1+Real.exp 1/K n) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_nhds.div_atTop hK : Tendsto (fun n => Real.exp 1/K n) atTop (𝓝 0))
  have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hsmall
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  change Real.log (1+Real.exp 1/K n) = Real.log (Real.exp 1+K n)-Real.log (K n)
  rw [← Real.log_div (add_pos (Real.exp_pos 1) hn).ne' hn.ne']
  congr 1
  field_simp [hn.ne']
  <;> ring

theorem tendsto_log_exp_add_div_log (K : ℕ → ℝ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => Real.log (Real.exp 1+K n)/Real.log (K n)) atTop (𝓝 (1 : ℝ)) := by
  have hh : Tendsto (fun n => 1+(Real.log (Real.exp 1+K n)-Real.log (K n))/Real.log (K n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_log_exp_add_sub_log K hK).div_atTop (Real.tendsto_log_atTop.comp hK))
  apply hh.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp hK).eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  change 0 < Real.log (K n) at hn
  field_simp [hn.ne']
  <;> ring

theorem tendsto_sparse_log_Khat_sub_K (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => Real.log (sparseLowerKhat n (ell n) q (B n))-
      Real.log (sparseLowerK n (ell n) q (B n))) atTop
        (𝓝 (Real.log ((2 : ℝ)^(2/q-1/2)))) := by
  have hh := (Real.continuousAt_log
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2/q-1/2)).ne').tendsto.comp
      (tendsto_sparseLowerKhat_div_K ell B q he hK)
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_sparseLowerKhat ell B q he hK).eventually (eventually_gt_atTop (0 : ℝ))] with n hn hhn
  change Real.log (sparseLowerKhat n (ell n) q (B n)/sparseLowerK n (ell n) q (B n)) = _
  rw [Real.log_div hhn.ne' hn.ne']

theorem tendsto_sparseLowerLog_div_logK (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/
      Real.log (sparseLowerK n (ell n) q (B n))) atTop (𝓝 (2 : ℝ)) := by
  let K := fun n => sparseLowerK n (ell n) q (B n)
  let Kh := fun n => sparseLowerKhat n (ell n) q (B n)
  have hlogK := Real.tendsto_log_atTop.comp hK
  have hratio : Tendsto (fun n => Real.log (Kh n)/Real.log (K n)) atTop (𝓝 (1 : ℝ)) := by
    have hh : Tendsto (fun n => 1+(Real.log (Kh n)-Real.log (K n))/Real.log (K n)) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_sparse_log_Khat_sub_K ell B q he hK).div_atTop hlogK)
    apply hh.congr'
    filter_upwards [hlogK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    dsimp [K] at hn ⊢
    field_simp
    <;> ring
  have hh : Tendsto (fun n => Real.log 2/Real.log (K n)+2*(Real.log (Kh n)/Real.log (K n))) atTop (𝓝 (2 : ℝ)) := by
    simpa using (tendsto_const_nhds.div_atTop hlogK :
      Tendsto (fun n => Real.log 2/Real.log (K n)) atTop (𝓝 0)).add
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio)
  apply hh.congr'
  filter_upwards [(tendsto_sparseLowerKhat ell B q he hK).eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  change _ = Real.log (2*(Kh n)^2)/Real.log (K n)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hn 2).ne', Real.log_pow]
  push_cast
  ring

theorem tendsto_sparseLowerLog_div_paperLog (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/
      Real.log (Real.exp 1+sparseLowerK n (ell n) q (B n))) atTop (𝓝 (2 : ℝ)) := by
  have hh := (tendsto_sparseLowerLog_div_logK ell B q he hK).div
    (tendsto_log_exp_add_div_log _ hK) (by norm_num : (1 : ℝ) ≠ 0)
  norm_num only [div_one] at hh
  apply hh.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp hK).eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  change 0 < Real.log (sparseLowerK n (ell n) q (B n)) at hn
  simp only [Pi.div_apply]
  field_simp [hn.ne']

theorem tendsto_sparseLowerLog_div_ell (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => Real.log (sparseLowerK n (ell n) q (B n))/(1+2*ell n))
      atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerLog n (ell n) q (B n)/ell n) atTop (𝓝 0) := by
  have hh := ((tendsto_sparseLowerLog_div_logK ell B q he hK).mul hsmall).mul
    (tendsto_sparse_dimension_ratio ell he)
  norm_num only [mul_zero, zero_mul] at hh
  apply hh.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp hK).eventually (eventually_gt_atTop (0 : ℝ)),
    he.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hne
  change 0 < Real.log (sparseLowerK n (ell n) q (B n)) at hn
  have hL : 1+2*ell n ≠ 0 := (by linarith only [hne] : 0 < 1+2*ell n).ne'
  field_simp [hn.ne', hne.ne', hL]

end
end RectangleCLT.Companion.SplitV4
