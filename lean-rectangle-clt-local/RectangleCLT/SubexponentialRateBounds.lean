import RectangleCLT.SubexponentialStatement
import RectangleCLT.LocalMoments

/-! The nontrivial branch of the sub-exponential rate implies the sample
size bounds used in the truncation argument. -/

namespace RectangleCLT

theorem subexponentialRate_small_scales
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {B4 K : ℝ}
    (hB : 0 ≤ B4) (hK : 0 ≤ K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q)
    (hH : 1 ≤ truncationLog n p) (hrate : subexponentialRate n B4 K Q < 1) :
    B4 < Real.sqrt (n : ℝ) ∧ K * truncationLog n p < Real.sqrt (n : ℝ) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  have hH0 : 0 ≤ truncationLog n p := zero_le_one.trans hH
  have hLs : 1 ≤ Real.sqrt (dimensionLog p) := by
    apply Real.le_sqrt_of_sq_le
    simpa using hL
  have hLprod : 1 ≤ dimensionLog p * Real.sqrt (dimensionLog p) :=
    one_le_mul_of_one_le_of_one_le hL hLs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hc : 0 < pairGap Q := hQ.pairGap_pos hp
  have ha3 : 0 < a3 Q := hQ.a3_pos hp
  have hc1 : pairGap Q ≤ 1 := pairGap_le_one Q
  have ha31 : a3 Q ≤ 1 :=
    (a3_le_pairGap (lt_of_lt_of_le Nat.zero_lt_one hp) hQ.posSemidef hQ.unit_diagonal).trans hc1
  have hca : pairGap Q * a3 Q ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hc1 ha31 ha3.le (zero_le_one : (0 : ℝ) ≤ 1)
  have hD3 : 0 < pairGap Q * a3 Q * Real.sqrt (n : ℝ) := mul_pos (mul_pos hc ha3) hsqrt
  have hD4 : 0 < Real.rpow (pairGap Q) (5 / 6 : ℝ) *
      Real.rpow (a3 Q * a4 Q) (1 / 3 : ℝ) * Real.sqrt (n : ℝ) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hc _)
      (Real.rpow_pos_of_pos (mul_pos ha3 hQ.a4_pos) _)) hsqrt
  have hD0 : 0 < pairGap Q * Real.sqrt (n : ℝ) := mul_pos hc hsqrt
  have hT3 : 0 ≤ B4 * dimensionLog p * Real.sqrt (dimensionLog p) /
      (pairGap Q * a3 Q * Real.sqrt (n : ℝ)) := by positivity
  have hT4 : 0 ≤ B4 * dimensionLog p /
      (Real.rpow (pairGap Q) (5 / 6 : ℝ) *
        Real.rpow (a3 Q * a4 Q) (1 / 3 : ℝ) * Real.sqrt (n : ℝ)) := by positivity
  have hT0 : 0 ≤ K * truncationLog n p * Real.sqrt (dimensionLog p) /
      (pairGap Q * Real.sqrt (n : ℝ)) := by positivity
  unfold subexponentialRate at hrate
  have h3 : B4 * dimensionLog p * Real.sqrt (dimensionLog p) <
      pairGap Q * a3 Q * Real.sqrt (n : ℝ) :=
    (div_lt_one hD3).mp (by linarith)
  have h0 : K * truncationLog n p * Real.sqrt (dimensionLog p) <
      pairGap Q * Real.sqrt (n : ℝ) :=
    (div_lt_one hD0).mp (by linarith)
  constructor
  · have hnum : B4 ≤ B4 * dimensionLog p * Real.sqrt (dimensionLog p) := by
      nlinarith [mul_le_mul_of_nonneg_left hLprod hB]
    have hden : pairGap Q * a3 Q * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hca hsqrt.le
    linarith
  · have hKH : 0 ≤ K * truncationLog n p := mul_nonneg hK hH0
    have hnum : K * truncationLog n p ≤ K * truncationLog n p * Real.sqrt (dimensionLog p) := by
      nlinarith [mul_le_mul_of_nonneg_left hLs hKH]
    have hden : pairGap Q * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hsqrt.le
    linarith

end RectangleCLT
