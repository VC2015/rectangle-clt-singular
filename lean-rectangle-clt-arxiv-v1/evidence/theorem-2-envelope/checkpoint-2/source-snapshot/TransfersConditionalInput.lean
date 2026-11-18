import RectangleCLTArxivV1.TransfersWidth
import RectangleCLTArxivV1.TransfersBounded
import RectangleCLTCompanion.SplitV4.ConditionalPolynomial

/-!
# The actual conditional bounded input in Appendix E.1

The bounded theorem is invoked on the archive's constructed product of
conditional good laws. Its width is controlled from the actual original
marginal distributions, rather than supplied as a comparison premise.
-/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The logarithmic correction is bounded by `log(en)` at every admissible
conditional cutoff. -/
theorem conditional_D_L_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {T : ℝ} (hT : (1 / 4 : ℝ) ≤ T) :
    D_L (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p) ≤ dimensionLog n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hsL : 1 ≤ Real.sqrt (dimensionLog p) := Real.one_le_sqrt.mpr hL
  have hTp : 0 < T := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hT
  have hden : 0 < (4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p) := by positivity
  have hprod : 1 ≤ ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) *
      Real.sqrt (n : ℝ) := by
    have he : ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) *
        Real.sqrt (n : ℝ) = (4 * T) * Real.sqrt (dimensionLog p) := by field_simp
    rw [he]
    nlinarith
  have hrecip : 1 / ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) ≤ n := by
    have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnR
    have hs2 := Real.sq_sqrt hnpos.le
    have hsle : Real.sqrt (n : ℝ) ≤ n := by nlinarith
    exact ((div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hprod)).trans hsle
  rw [dimensionLog_eq_one_add_log hn]
  unfold D_L
  have hl := logPlus_mono (one_div_pos.mpr hden) hrecip
  have hlog : logPlus (n : ℝ) = Real.log (n : ℝ) := max_eq_right (Real.log_nonneg hnR)
  rw [hlog] at hl
  exact add_le_add_left hl 1

/-- The Appendix E.1 bounded input for each actual retained mask. The only
mask condition is the printed good covariance event. -/
theorem conditionalRetained_intrinsicRectangleDistanceCLT {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B) (mask : Fin n → Bool)
    (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - A * A.transpose) ≤ 1 / 2)
    (hC : C * C.transpose = conditionalCovarianceForMask μ T mask) :
    rectangleDistance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T mask)) C ≤
      intrinsicUniversalConstant * min 1
        ((8 * Real.sqrt (4 / 3 : ℝ)) *
          (gaussianMaximumMean A * (T / Real.sqrt (n : ℝ)) * dimensionLog p *
            Real.sqrt (dimensionLog n))) := by
  let i : Fin n := ⟨0, by omega⟩
  have hT : 0 ≤ T := (h i).threshold_pos.le
  have hTquarter : (1 / 4 : ℝ) ≤ T := by linarith [(h i).threshold]
  have hc : covariance (conditionalGoodProductLaw μ T)
      (sumVector (normalizedSummands (conditionalRetainedSummand μ T mask))) =
        conditionalCovarianceForMask μ T mask := by
    rw [sumVector_normalizedSummands]
    ext j k
    exact conditionalRetained_normalized_covariance μ hT mask j k
  have hl := conditionalRetained_marginal_lower_bound μ hT mask (A * A.transpose) hunit hgood
  rw [← sumVector_normalizedSummands] at hl
  have hb := intrinsicEnvelopeCLT_of_marginal_lower_bound (conditionalGoodProductLaw μ T)
    (normalizedSummands (conditionalRetainedSummand μ T mask))
    (conditionalRetained_normalized_boundedIndependent μ hT mask) hp hl C (hC.trans hc.symm)
  rw [sumVector_normalizedSummands] at hb
  have hg := conditionalCovarianceForMask_gaussianMaximumMean_le μ h mask A C hA hC
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hD := Real.sqrt_le_sqrt (conditional_D_L_le hp hn hTquarter)
  have hga := gaussianMaximumMean_nonneg A
  have hrate : 4 * ((2 * T / Real.sqrt (n : ℝ)) * gaussianMaximumMean C * dimensionLog p *
      Real.sqrt (D_L (2 * (2 * T / Real.sqrt (n : ℝ))) (dimensionLog p))) ≤
      (8 * Real.sqrt (4 / 3 : ℝ)) *
        (gaussianMaximumMean A * (T / Real.sqrt (n : ℝ)) * dimensionLog p * Real.sqrt (dimensionLog n)) := by
    have hD' : Real.sqrt (D_L (2 * (2 * T / Real.sqrt (n : ℝ))) (dimensionLog p)) ≤
        Real.sqrt (dimensionLog n) := by
      rw [show 2 * (2 * T / Real.sqrt (n : ℝ)) = 4 * T / Real.sqrt (n : ℝ) by ring]
      exact hD
    have hfirst := mul_le_mul_of_nonneg_right hg
      (show 0 ≤ (2 * T / Real.sqrt (n : ℝ)) * dimensionLog p *
        Real.sqrt (D_L (2 * (2 * T / Real.sqrt (n : ℝ))) (dimensionLog p)) by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hD'
      (show 0 ≤ (2 * T / Real.sqrt (n : ℝ)) *
        (Real.sqrt (4 / 3 : ℝ) * gaussianMaximumMean A) * dimensionLog p by
          positivity)
    calc
      _ ≤ 4 * ((2 * T / Real.sqrt (n : ℝ)) *
          (Real.sqrt (4 / 3 : ℝ) * gaussianMaximumMean A) * dimensionLog p *
          Real.sqrt (D_L (2 * (2 * T / Real.sqrt (n : ℝ))) (dimensionLog p))) := by
        convert mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
      _ ≤ 4 * ((2 * T / Real.sqrt (n : ℝ)) *
          (Real.sqrt (4 / 3 : ℝ) * gaussianMaximumMean A) * dimensionLog p *
          Real.sqrt (dimensionLog n)) := mul_le_mul_of_nonneg_left hsecond (by norm_num)
      _ = _ := by ring
  exact hb.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate)
    intrinsicUniversalConstant_pos.le)

end RectangleCLTArxivV1
