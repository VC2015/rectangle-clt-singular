import RectangleCLTCompanion.SplitV4.SparseLowerLogScales

/-! Exact conversion of the calibrated sparse discrepancy to the paper's
rate, and disappearance of the coordinate fourth-moment contribution. -/
open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem sparseLowerB_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hK : 0 < sparseLowerK n ell q B) : 0 < B := by
  have hbase : 0 < ((n : ℝ)/(1+2*ell))^(2/q-1/2) :=
    Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hn) (by linarith only [he])) _
  exact (mul_pos_iff_of_pos_right hbase).mp hK

theorem sparseLowerRate_div_scale {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerRate n ell q B/sparseLowerScale n ell q B =
      2*4^(1-1/q)*((1+2*ell)/ell)^(3/2-1/q)*
        (sparseLowerLog n ell q B/Real.log (Real.exp 1+sparseLowerK n ell q B))^(1-1/q) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < 1+2*ell := by linarith only [he]
  have hΛ : 0 < sparseLowerLog n ell q B :=
    lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  have hkp := mul_pos hB (Real.rpow_pos_of_pos (div_pos hN hL) (2/q-1/2))
  change 0 < sparseLowerK n ell q B at hkp
  have hlog : 0 < Real.log (Real.exp 1+sparseLowerK n ell q B) := by
    apply Real.log_pos
    have hh : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith only [hh, hkp]
  rw [sparseLowerScale_factor hn he hK]
  unfold sparseLowerRate
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hΛ.le,
    Real.div_rpow hL.le he.le, Real.div_rpow hΛ.le hlog.le]
  have heNZ := (Real.rpow_pos_of_pos he (3/2-1/q)).ne'
  have hnNZ := (Real.rpow_pos_of_pos hN (1/2-1/q)).ne'
  have hlNZ := (Real.rpow_pos_of_pos hlog (1-1/q)).ne'
  field_simp [hB.ne', heNZ, hnNZ, hlNZ]
  <;> ring

theorem tendsto_sparseLowerRate_div_scale (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => sparseLowerRate n (ell n) q (B n)/sparseLowerScale n (ell n) q (B n))
      atTop (𝓝 ((2 : ℝ)^(11/2-4/q))) := by
  let a : ℝ := 1-1/q
  let b : ℝ := 3/2-1/q
  have hh := ((tendsto_const_nhds (x := (2 : ℝ)*4^a)).mul
    ((tendsto_sparse_dimension_ratio ell he).rpow_const (p := b)
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))).mul
    ((tendsto_sparseLowerLog_div_paperLog ell B q he hK).rpow_const (p := a)
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have h4 : (4 : ℝ)^a = (2 : ℝ)^(2*a) := by
    rw [show (4 : ℝ) = (2 : ℝ)^(2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hc : (2 : ℝ)*4^a*2^b*2^a = (2 : ℝ)^(11/2-4/q) := by
    calc
      _ = (2 : ℝ)^(1 : ℝ)*2^(2*a)*2^b*2^a := by rw [Real.rpow_one, h4]
      _ = (2 : ℝ)^(((1 : ℝ)+2*a)+b+a) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by congr 1; dsimp [a, b]; ring
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    he.eventually (eventually_gt_atTop (0 : ℝ)),
    hK.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_sparseLowerKhat ell B q he hK).eventually (eventually_ge_atTop (2 : ℝ))]
      with n hn hen hkn hkhn
  exact (sparseLowerRate_div_scale hn hen (sparseLowerB_pos hn hen hkn) hkhn).symm

theorem tendsto_sparseLowerScale_of_paperRate (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop)
    (hR : Tendsto (fun n => sparseLowerRate n (ell n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => sparseLowerScale n (ell n) q (B n)) atTop (𝓝 0) := by
  have hh := hR.div (tendsto_sparseLowerRate_div_scale ell B q he hK)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (11/2-4/q)).ne'
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    he.eventually (eventually_gt_atTop (0 : ℝ)),
    hK.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_sparseLowerKhat ell B q he hK).eventually (eventually_ge_atTop (2 : ℝ))]
      with n hn hen hkn hkhn
  have hb := sparseLowerB_pos hn hen hkn
  have hd := sparseLowerScale_pos hn hen hb hkhn
  have hr : 0 < sparseLowerRate n (ell n) q (B n) := by
    unfold sparseLowerRate
    have hL : 0 < 1+2*ell n := by linarith only [hen]
    have hlog : 0 < Real.log (Real.exp 1+sparseLowerK n (ell n) q (B n)) := by
      apply Real.log_pos
      have hh : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith only [hh, hkn]
    exact div_pos (mul_pos hb (Real.rpow_pos_of_pos hL _))
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) (Real.rpow_pos_of_pos hlog _))
  simp only [Pi.div_apply]
  field_simp [hd.ne', hr.ne']

theorem tendsto_log_exp_add_rpow_div_rpow (K : ℕ → ℝ)
    (hK : Tendsto K atTop atTop) (r s : ℝ) (hs : 0 < s) :
    Tendsto (fun n => Real.log (Real.exp 1+K n)^r/(K n)^s) atTop (𝓝 0) := by
  have hbase := (tendsto_log_exp_add_div_log K hK).rpow_const (p := r)
    (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hsmall := (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero.comp hK
  have hh := hbase.mul hsmall
  simp only [Real.one_rpow, one_mul] at hh
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
  have hlog : 0 < Real.log (K n) := Real.log_pos hn
  have hloge : 0 < Real.log (Real.exp 1+K n) := Real.log_pos (by linarith only [Real.exp_pos (1 : ℝ), hn])
  rw [Real.div_rpow hloge.le hlog.le]
  field_simp [(Real.rpow_pos_of_pos hlog r).ne']

end
end RectangleCLT.Companion.SplitV4
