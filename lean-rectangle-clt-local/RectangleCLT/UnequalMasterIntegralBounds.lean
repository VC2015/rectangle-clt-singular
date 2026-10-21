import RectangleCLT.UnequalMasterDerivativeCaps
import RectangleCLT.UnequalMasterStatement
import RectangleCLT.UnequalShortScale

/-! All cubic and fourth-order master integral entries, with their exact
zero-parameter conventions. Each available entry is supplied by an actual
derivative estimate for the unequal-covariance Bernoulli path. -/

open MeasureTheory Set

namespace RectangleCLT

noncomputable section

def unequalThirdIntegralConstant : ℝ :=
  1 + (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) +
    2 * FaceSmoother.gaussianThirdConstant + 2 * globalThirdAverageConstant

def unequalFourthIntegralConstant : ℝ :=
  1 + (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) +
    3 * gaussianFourthConstant + 3 * globalFourthAverageConstant

theorem unequalThirdIntegralConstant_pos : 0 < unequalThirdIntegralConstant := by
  have hK : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  unfold unequalThirdIntegralConstant
  linarith [FaceSmoother.gaussianThirdConstant_pos, globalThirdAverageConstant_pos]

theorem unequalFourthIntegralConstant_pos : 0 < unequalFourthIntegralConstant := by
  have hK : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  unfold unequalFourthIntegralConstant
  linarith [gaussianFourthConstant_pos, globalFourthAverageConstant_pos]

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem integral_time_mul_sharpThirdAverage_le_unequal_min
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth) :
    (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
      unequalThirdIntegralConstant * Real.sqrt (dimensionLog p) *
        masterThirdCoefficient (dimensionLog p) (fullCovarianceScale (A * A.transpose))
          (pairGap (A * A.transpose)) (a3 (A * A.transpose)) s.bandwidth := by
  let Q := A * A.transpose
  let L := dimensionLog p
  let C := unequalThirdIntegralConstant
  let K := 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  dsimp only [K] at hK
  have hC : 0 ≤ C := unequalThirdIntegralConstant_pos.le
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hPSD : Q.PosSemidef := by
    simpa only [Q, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hK0 : K ≤ C := by
    dsimp [C, unequalThirdIntegralConstant, K]
    linarith [gaussianThirdConstant_pos, globalThirdAverageConstant_pos]
  have hK1 : 2 * gaussianThirdConstant ≤ C := by
    dsimp [C, unequalThirdIntegralConstant]
    linarith [hK, globalThirdAverageConstant_pos]
  have hK2 : 2 * globalThirdAverageConstant ≤ C := by
    dsimp [C, unequalThirdIntegralConstant]
    linarith [hK, gaussianThirdConstant_pos]
  have hD : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    (continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ hdata.measurable A)).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hshort : (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
      C * Real.sqrt L * (1 / s.bandwidth ^ 2) := by
    have hB : 0 ≤ K * Real.sqrt L / s.bandwidth ^ 2 := by positivity
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
      hD intervalIntegrable_const (fun t ht =>
        (mul_le_mul_of_nonneg_left
          (s.sharpThirdAverage_shortScale_le_unequal μ ξ hdata hp hunit A hdiag hband ht.1.le ht.2.le)
          ht.1.le).trans (mul_le_of_le_one_left hB ht.2.le))
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hh
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_right hK0
      (div_nonneg (Real.sqrt_nonneg L) (sq_nonneg s.bandwidth))
    convert hm using 1 <;> ring
  change _ ≤ (C * Real.sqrt L) * optionalMin (fullCovarianceScale Q)
    (L / fullCovarianceScale Q ^ 2)
    (optionalMin (a3 Q) (L / (pairGap Q * a3 Q)) (1 / s.bandwidth ^ 2))
  apply le_mul_optionalMin (mul_nonneg hC (Real.sqrt_nonneg L))
  · apply le_mul_optionalMin (mul_nonneg hC (Real.sqrt_nonneg L)) hshort
    intro ha3
    have hh := s.integral_time_mul_sharpThirdAverage_le_of_a3 μ ξ hdata.measurable hp A
      (localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hPSD)) ha3
      hdiag hc (a3_le_pairGap hp hPSD hdiag)
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_right hK1
      (div_nonneg (mul_nonneg hL (Real.sqrt_nonneg L)) (mul_nonneg hc.le ha3.le))
    convert hm using 1 <;> dsimp [Q, L, a3, a4] <;> ring
  · intro hb
    have hsq := fullCovarianceScale_sq hp hPSD
    have hν : 0 < fullEigenvalue Q := by rw [← hsq]; exact sq_pos_of_pos hb
    have hh := s.integral_time_mul_sharpThirdAverage_le_full μ ξ hdata.measurable hp A
      hdiag hν (fullEigenvalue_lower hPSD)
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_right hK2
      (div_nonneg (mul_nonneg hL (Real.sqrt_nonneg L)) hν.le)
    rw [hsq]
    convert hm using 1 <;> dsimp [Q, L, a3, a4] <;> ring

theorem integral_sharpFourthAverage_le_unequal_min
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth) :
    (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
      unequalFourthIntegralConstant * Real.sqrt (dimensionLog p) *
        masterFourthCoefficient (dimensionLog p) (fullCovarianceScale (A * A.transpose))
          (pairGap (A * A.transpose)) (a3 (A * A.transpose))
          (a4 (A * A.transpose)) s.bandwidth := by
  let Q := A * A.transpose
  let L := dimensionLog p
  let C := unequalFourthIntegralConstant
  let K := 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  dsimp only [K] at hK
  have hC : 0 ≤ C := unequalFourthIntegralConstant_pos.le
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hPSD : Q.PosSemidef := by
    simpa only [Q, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hK0 : K ≤ C := by
    dsimp [C, unequalFourthIntegralConstant, K]
    linarith [gaussianFourthConstant_pos, globalFourthAverageConstant_pos]
  have hK1 : 3 * gaussianFourthConstant ≤ C := by
    dsimp [C, unequalFourthIntegralConstant]
    linarith [hK, globalFourthAverageConstant_pos]
  have hK2 : 3 * globalFourthAverageConstant ≤ C := by
    dsimp [C, unequalFourthIntegralConstant]
    linarith [hK, gaussianFourthConstant_pos]
  have hD : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    (s.continuousOn_sharpFourthAverage μ ξ hdata.measurable A hdata.delta_nonneg).intervalIntegrable_of_Icc
      (by norm_num)
  have hshort : (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
      C * Real.sqrt L * (1 / s.bandwidth ^ 3) := by
    have hh := integral_fourth_small_cap hD (fun t ht =>
      s.sharpFourthAverage_shortScale_le_proxy μ ξ hdata hp hunit A hdiag hband ht.1.le ht.2.le)
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_right hK0
      (div_nonneg (Real.sqrt_nonneg L) (pow_nonneg s.bandwidth_pos.le 3))
    convert hm using 1 <;> ring
  change _ ≤ (C * Real.sqrt L) * optionalMin (fullCovarianceScale Q)
    (L / (fullCovarianceScale Q ^ 2 * s.bandwidth))
    (optionalMin (a3 Q * a4 Q)
      (L / ((pairGap Q * a3 Q * a4 Q) ^ (2 / 3 : ℝ) * s.bandwidth))
      (1 / s.bandwidth ^ 3))
  apply le_mul_optionalMin (mul_nonneg hC (Real.sqrt_nonneg L))
  · apply le_mul_optionalMin (mul_nonneg hC (Real.sqrt_nonneg L)) hshort
    intro ha34
    have ha4non := localEigenvalue_nonneg hp (by norm_num : 0 < (4 : ℕ))
      (matrixQuadratic_nonneg_of_posSemidef hPSD)
    have ha4 : 0 < a4 Q := by
      rcases mul_pos_iff.mp ha34 with hpos | hneg
      · exact hpos.2
      · exact False.elim ((not_lt_of_ge ha4non) hneg.2)
    have hlocal : LocalCovarianceHypotheses Q := ⟨hPSD, hdiag, ha4⟩
    have hh := s.integral_sharpFourthAverage_le_proxy μ ξ hdata hp hunit A hlocal hband
    apply hh.trans
    have hcost : 0 ≤ pairGap Q * a3 Q * a4 Q :=
      mul_nonneg (mul_nonneg hc.le (hlocal.a3_pos hp).le) ha4.le
    have hm := mul_le_mul_of_nonneg_right hK1
      (div_nonneg (mul_nonneg hL (Real.sqrt_nonneg L))
        (mul_nonneg s.bandwidth_pos.le (Real.rpow_nonneg hcost (2 / 3 : ℝ))))
    convert hm using 1 <;> dsimp [Q, L, a3, a4] <;> ring
  · intro hb
    have hsq := fullCovarianceScale_sq hp hPSD
    have hν : 0 < fullEigenvalue Q := by rw [← hsq]; exact sq_pos_of_pos hb
    have hh := s.integral_sharpFourthAverage_le_full_proxy hdata hp hunit A hdiag
      hν (fullEigenvalue_lower hPSD) hband
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_right hK2
      (div_nonneg (mul_nonneg hL (Real.sqrt_nonneg L))
        (mul_nonneg hν.le s.bandwidth_pos.le))
    rw [hsq]
    convert hm using 1 <;> dsimp [Q, L, a3, a4] <;> ring

end FaceSmoother

end

end RectangleCLT
