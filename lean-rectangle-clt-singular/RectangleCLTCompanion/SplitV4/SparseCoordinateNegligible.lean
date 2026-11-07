import RectangleCLTCompanion.SplitV4.SparseLowerPaperRate
import RectangleCLTCompanion.SplitV4.SparseUniformBounds

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem sparseLower_coordinate_div_rate {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) :
    (B^(1/2 : ℝ)*(1+2*ell)^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ))/sparseLowerRate n ell q B =
      Real.log (Real.exp 1+sparseLowerK n ell q B)^(1-1/q)/
        sparseLowerK n ell q B^(1/2 : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < 1+2*ell := by linarith only [he]
  have hkp : 0 < sparseLowerK n ell q B :=
    mul_pos hB (Real.rpow_pos_of_pos (div_pos hN hL) _)
  have hlog : 0 < Real.log (Real.exp 1+sparseLowerK n ell q B) := by
    apply Real.log_pos
    have hh : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith only [hh, hkp]
  have hkpow : sparseLowerK n ell q B^(1/2 : ℝ) =
      B^(1/2 : ℝ)*(n : ℝ)^(1/q-1/4)/(1+2*ell)^(1/q-1/4) := by
    unfold sparseLowerK
    rw [Real.mul_rpow hB.le (Real.rpow_nonneg (div_nonneg hN.le hL.le) _),
      ← Real.rpow_mul (div_nonneg hN.le hL.le), Real.div_rpow hN.le hL.le]
    have hh : (2/q-(1/2 : ℝ))*(1/2) = 1/q-1/4 := by ring
    rw [hh]
    ring
  have hLp : (1+2*ell)^(5/4 : ℝ) = (1+2*ell)^(3/2-1/q)*(1+2*ell)^(1/q-1/4) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hnp : (n : ℝ)^(1/4 : ℝ) = (n : ℝ)^(1/2-1/q)*(n : ℝ)^(1/q-1/4) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hBsquare : (B^(1/2 : ℝ))^2 = B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  rw [hkpow, hLp, hnp]
  unfold sparseLowerRate
  have hn1 := (Real.rpow_pos_of_pos hN (1/2-1/q)).ne'
  have hn2 := (Real.rpow_pos_of_pos hN (1/q-1/4)).ne'
  have hL1 := (Real.rpow_pos_of_pos hL (3/2-1/q)).ne'
  have hL2 := (Real.rpow_pos_of_pos hL (1/q-1/4)).ne'
  have hB1 := (Real.rpow_pos_of_pos hB (1/2 : ℝ)).ne'
  have hlog1 := (Real.rpow_pos_of_pos hlog (1-1/q)).ne'
  field_simp [hn1, hn2, hL1, hL2, hB1, hlog1, hB.ne']
  ring_nf
  rw [hBsquare]
  ring

theorem tendsto_sparseLower_coordinate_div_rate (ell B : ℕ → ℝ) (q : ℝ)
    (he : Tendsto ell atTop atTop)
    (hK : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop) :
    Tendsto (fun n => (B n^(1/2 : ℝ)*(1+2*ell n)^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ))/
      sparseLowerRate n (ell n) q (B n)) atTop (𝓝 0) := by
  apply (tendsto_log_exp_add_rpow_div_rpow _ hK (1-1/q) (1/2) (by norm_num)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    he.eventually (eventually_gt_atTop (0 : ℝ)),
    hK.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hen hkn
  exact (sparseLower_coordinate_div_rate hn hen (sparseLowerB_pos hn hen hkn)).symm

end
end RectangleCLT.Companion.SplitV4
