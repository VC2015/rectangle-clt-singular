import RectangleCLT.RectangleSmoothing
import RectangleCLT.GaussianComparisonCovariance

/-! Endpoint smoothing for a covariance proxy. The true bounded sum and
Gaussian target have separate pairwise gaps. Small entrywise discrepancy
controls the true gap using only the proxy's gap. -/

open MeasureTheory ProbabilityTheory

namespace RectangleCLT.BoundedIndependentHypotheses

theorem smoother_rectangle_error_le_proxy
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (hsmall : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ))
      (A * A.transpose) ≤ pairGap (A * A.transpose) / 2)
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) :
    |μ.real {ω | s.Inside (sumVector ξ ω)} - (gaussianLaw A).real {z | s.Inside z}| ≤
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
        (16 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
          pairGap (A * A.transpose) := by
  let S := covariance μ (sumVector ξ)
  let Q := A * A.transpose
  have hgap : pairGap Q / 2 ≤ pairGap S := by
    have hh := gaussianComparisonCovariance_pairGap_ge_half S Q hsmall
      (t := 0) (by norm_num) (by norm_num)
    simpa only [gaussianComparisonCovariance_zero] using hh
  have hcS : 0 < pairGap S := lt_of_lt_of_le (half_pos hc) hgap
  have hW : Measurable (sumVector ξ) := h.measurable_sum
  have hh := s.probability_gap_le_smoother_gap_add_kappa μ (gaussianLaw A)
    (sumVector ξ) hW id measurable_id
  have hb := h.integral_kappa_le s 0 hp hunit hcS hband
  simp only [add_zero] at hb
  have hg := s.gaussian_expected_kappa_le hp A 0 hA hc
  simp only [add_zero] at hg
  dsimp only [id_eq] at hh
  have hn : 0 ≤ (4 * Real.exp 4) * s.bandwidth * Real.sqrt (dimensionLog p) := by
    have hs := s.bandwidth_pos
    positivity
  have hden : 1 / pairGap S ≤ 2 / pairGap Q := by
    apply (div_le_div_iff₀ hcS hc).mpr
    linarith
  have hb' : (∫ ω, s.kappa (sumVector ξ ω) ∂μ) ≤
      8 * Real.exp 4 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap Q := by
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left hden hn
    convert hm using 1 <;> ring
  change |μ.real {ω | s.Inside (sumVector ξ ω)} - (gaussianLaw A).real {z | s.Inside z}| ≤
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
      (16 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap Q
  calc
    _ ≤ |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
        2 * ((∫ ω, s.kappa (sumVector ξ ω) ∂μ) +
          (∫ z, s.kappa z ∂gaussianLaw A)) := hh
    _ ≤ |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
        2 * (8 * Real.exp 4 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap Q +
          2 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap Q) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add hb' hg) (by norm_num)) _
    _ = _ := by ring

theorem closedBox_error_le_smoother_gap_proxy
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ h : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (hsmall : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ))
      (A * A.transpose) ≤ pairGap (A * A.transpose) / 2)
    (lo hi : Vector p) (hh : 0 < h) (hband : δ ≤ h) :
    rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
      |(∫ ω, (FaceSmoother.closedBox lo hi h hh).F (sumVector ξ ω) ∂μ) -
        (∫ z, (FaceSmoother.closedBox lo hi h hh).F z ∂gaussianLaw A)| +
      (16 * Real.exp 4 + 4) * h * Real.sqrt (dimensionLog p) /
        pairGap (A * A.transpose) := by
  have hh' := hdata.smoother_rectangle_error_le_proxy hp hunit A hA hc hsmall
    (FaceSmoother.closedBox lo hi h hh) hband
  have hμ : {ω | (FaceSmoother.closedBox lo hi h hh).Inside (sumVector ξ ω)} =
      sumVector ξ ⁻¹' (Rect.closedBox lo hi).carrier := by
    ext ω
    exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
  have hG : {z | (FaceSmoother.closedBox lo hi h hh).Inside z} =
      (Rect.closedBox lo hi).carrier := by
    ext z
    exact FaceSmoother.closedBox_Inside lo hi h hh z
  rw [hμ, hG] at hh'
  simpa only [rectangleError, FaceSmoother.closedBox] using hh'

end RectangleCLT.BoundedIndependentHypotheses
