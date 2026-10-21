import RectangleCLT.SubexponentialAssembly
import RectangleCLT.RefinedProxyStatement

/-! The exact combined sub-exponential rate, with separate moment and tail
scales and independently selected covariance coefficients. -/

namespace RectangleCLT

noncomputable section

def refinedSubexponentialRate {p : ℕ} (n : ℕ) (B4 K : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  B4 * dimensionLog p * Real.sqrt (dimensionLog p) *
      combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) /
        Real.sqrt (n : ℝ) +
    B4 * dimensionLog p / Real.sqrt (pairGap Q) *
      combinedFourthCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q) /
        Real.sqrt (n : ℝ) +
    K * truncationLog n p * Real.sqrt (dimensionLog p) /
      (pairGap Q * Real.sqrt (n : ℝ))

theorem refinedSubexponentialRate_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : MeasureTheory.Measure Ω} {Y : Fin n → Ω → Vector p} {B4 K : ℝ}
    (h : SubexponentialHypotheses μ Y B4 K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q) :
    0 ≤ refinedSubexponentialRate n B4 K Q := by
  have hβ3 := combinedThirdCoefficient_nonneg (b := fullCovarianceScale Q)
    (hQ.pairGap_pos h.dimension_pos) (hQ.a3_pos h.dimension_pos)
  have hβ4 := combinedFourthCoefficient_nonneg (b := fullCovarianceScale Q)
    (hQ.pairGap_pos h.dimension_pos) (hQ.a3_pos h.dimension_pos) hQ.a4_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.sample_size_pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.dimension_pos
  have hH : 0 ≤ truncationLog n p :=
    zero_le_one.trans (subexponentialCutoffHeight_bounds hn1 hp1).1
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)
  have hB : 0 ≤ B4 := zero_le_one.trans h.fourth_scale_ge_one
  have hK : 0 ≤ K := zero_le_one.trans h.tail_scale_ge_one
  have hc := hQ.pairGap_pos h.dimension_pos
  unfold refinedSubexponentialRate
  positivity

theorem combinedThirdCoefficient_ge_one {p : ℕ} (hp : 1 ≤ p)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q) :
    1 ≤ combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) := by
  have hc := hQ.pairGap_pos hp
  have ha := hQ.a3_pos hp
  have hc1 := pairGap_le_one Q
  have ha1 := (a3_le_pairGap (by omega) hQ.posSemidef hQ.unit_diagonal).trans hc1
  have hca : pairGap Q * a3 Q ≤ 1 := by
    exact (mul_le_mul hc1 ha1 ha.le zero_le_one).trans_eq (by ring)
  have hlocal : (1 : ℝ) ≤ 1 / (pairGap Q * a3 Q) :=
    (le_div_iff₀ (mul_pos hc ha)).mpr (by simpa using hca)
  unfold combinedThirdCoefficient
  split_ifs with hb
  · have hsq : fullCovarianceScale Q ^ 2 ≤ 1 := by
      rw [fullCovarianceScale_sq (by omega) hQ.posSemidef]
      exact (fullEigenvalue_le_pairGap (by omega) hQ.posSemidef hQ.unit_diagonal).trans hc1
    exact le_min ((le_div_iff₀ (sq_pos_of_pos hb)).mpr (by simpa using hsq)) hlocal
  · exact hlocal

theorem refinedSubexponentialRate_small_scales
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {B4 K : ℝ}
    (hB : 0 ≤ B4) (hK : 0 ≤ K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q)
    (hH : 1 ≤ truncationLog n p)
    (hrate : refinedSubexponentialRate n B4 K Q < 1) :
    B4 < Real.sqrt (n : ℝ) ∧ K * truncationLog n p < Real.sqrt (n : ℝ) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  have hLs : 1 ≤ Real.sqrt (dimensionLog p) := Real.one_le_sqrt.mpr hL
  have hLprod := one_le_mul_of_one_le_of_one_le hL hLs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hc := hQ.pairGap_pos hp
  have hβ3 := combinedThirdCoefficient_ge_one hp hQ
  have hβ4 := combinedFourthCoefficient_nonneg (b := fullCovarianceScale Q)
    hc (hQ.a3_pos hp) hQ.a4_pos
  have h3 : 0 ≤ B4 * dimensionLog p * Real.sqrt (dimensionLog p) *
      combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) /
        Real.sqrt (n : ℝ) := by positivity
  have h4 : 0 ≤ B4 * dimensionLog p / Real.sqrt (pairGap Q) *
      combinedFourthCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q) /
        Real.sqrt (n : ℝ) := by positivity
  have h0 : 0 ≤ K * truncationLog n p * Real.sqrt (dimensionLog p) /
      (pairGap Q * Real.sqrt (n : ℝ)) := by positivity
  unfold refinedSubexponentialRate at hrate
  have hc3 : B4 * dimensionLog p * Real.sqrt (dimensionLog p) *
      combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) <
        Real.sqrt (n : ℝ) := (div_lt_one hs).mp (by linarith only [hrate, h4, h0])
  have hc0 : K * truncationLog n p * Real.sqrt (dimensionLog p) <
      pairGap Q * Real.sqrt (n : ℝ) :=
    (div_lt_one (mul_pos hc hs)).mp (by linarith only [hrate, h3, h4])
  constructor
  · have hprod : 1 ≤ dimensionLog p * Real.sqrt (dimensionLog p) *
        combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) :=
      one_le_mul_of_one_le_of_one_le hLprod hβ3
    have hh := mul_le_mul_of_nonneg_left hprod hB
    nlinarith only [hh, hc3]
  · have hKH : 0 ≤ K * truncationLog n p := mul_nonneg hK (zero_le_one.trans hH)
    have hnum := mul_le_mul_of_nonneg_left hLs hKH
    have hden := mul_le_mul_of_nonneg_right (pairGap_le_one Q) hs.le
    nlinarith only [hnum, hden, hc0]

end

end RectangleCLT
