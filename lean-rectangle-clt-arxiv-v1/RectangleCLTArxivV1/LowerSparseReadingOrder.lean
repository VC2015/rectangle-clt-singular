import RectangleCLTArxivV1.LowerSparseFourSpecialization

/-! Explicit numerical consequences used in the reading-order proof of F.6. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerSparse_cube_dimension_sq_le_coordinateWidth_fourth {n : ℕ} {ell B g c R : ℝ}
    (hell : 0 < ell) (hB : 2 ≤ B) (hc : 0 < c) (hR : 0 ≤ R) (hg : c*Real.sqrt R ≤ g) :
    ell^3*R^2/(n : ℝ) ≤ lowerSparseCoordinateWidth n ell B g^4/(4*c^4) := by
  have hB2 : (4 : ℝ) ≤ B^2 := by nlinarith
  have hg4 := pow_le_pow_left₀ (mul_nonneg hc.le (Real.sqrt_nonneg R)) hg 4
  have hs4 : (Real.sqrt R)^4 = R^2 := by
    calc
      _ = ((Real.sqrt R)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hR]
  rw [mul_pow,hs4] at hg4
  have hcoef : 4*(c^4*R^2) ≤ B^2*g^4 :=
    mul_le_mul hB2 hg4 (mul_nonneg (pow_nonneg hc.le 4) (sq_nonneg R)) (sq_nonneg B)
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hc 4))).mpr
  rw [lowerSparseCoordinateWidth_fourth hell (by linarith : 0 ≤ B)]
  have hh := mul_le_mul_of_nonneg_right hcoef
    (div_nonneg (pow_nonneg hell.le 3) (Nat.cast_nonneg n))
  convert hh using 1 <;> ring

theorem tendsto_lowerSparseEll_cube_dimensionLog_sq_div {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3*dimensionLog (r n)^2/n) atTop (𝓝 0) := by
  obtain ⟨c,hc,hwidth⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hU := tendsto_lowerSparseCoordinateWidth hB hr hmTop hK hsmall
  have hbound : Tendsto (fun n => lowerSparseCoordinateWidth n (Real.log (m n : ℝ)) (B n)
      (independentAbsGaussianMean (r n))^4/(4*c^4)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0),zero_div] using (hU.pow 4).div_const (4*c^4)
  have hell := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [hell.eventually (eventually_gt_atTop 0)] with n hnL
    exact div_nonneg (mul_nonneg (pow_nonneg hnL.le 3) (sq_nonneg _)) (Nat.cast_nonneg n)
  · filter_upwards [hell.eventually (eventually_gt_atTop 0)] with n hnL
    exact lowerSparse_cube_dimension_sq_le_coordinateWidth_fourth hnL (hB n) hc
      (zero_le_one.trans (log_exp_mul_nat_ge_one (hr n))) (hwidth (r n) (hr n))

theorem lowerSparseCalibration_from_headline {q : ℝ} (hq : 2 < q) {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hrm : ∀ n, r n ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n)) atTop atTop)
    (hlogSmall : Tendsto (fun n => Real.log (lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n))/
      dimensionLog (r n*m n)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) : LowerSparseCalibration q B r m := by
  have hKh := tendsto_lowerSparseKhat hB hr hrm hmTop hK
  have hΛ := tendsto_lowerSparseLog_div_rareLog hB hr hrm hmTop hK hlogSmall
  have hraw := tendsto_lowerSparseRawWidth hq hB hr hrm hmTop hK hsmall
  exact lowerSparseCalibration_of_scalar_limits q hB hmTop hKh hΛ
    (tendsto_lowerSparseTheta hB hr hmTop hKh hraw)
    (tendsto_lowerSparseVariance hq hB hr hmTop hKh hraw)
    (tendsto_lowerSparseEffectiveAmplitude hB hr hmTop hKh hraw) hraw

end
end RectangleCLTArxivV1
