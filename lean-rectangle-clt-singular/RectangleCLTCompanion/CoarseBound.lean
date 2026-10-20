import RectangleCLTCompanion.Statement
import RectangleCLTCompanion.Endpoint
import RectangleCLT.BoundedSmoothingEstimate

/-! An unconditional covariance-free bandwidth bound for actual rectangle
probabilities. This coarse bound is weaker than the companion manuscript's
optimized rates; no optimized companion CLT assertion is made here. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

/-- The actual rectangle probability differs from its smoothed expectation
by at most the corresponding integrable pointwise endpoint error. -/
theorem integral_endpoint_error_le_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) :
    |(∫ ω, s.F (W ω) ∂μ) - μ.real {ω | s.Inside (W ω)}| ≤
      ∫ ω, |s.F (W ω) - s.indicator (W ω)| ∂μ := by
  classical
  have hs : MeasurableSet {ω | s.Inside (W ω)} := s.measurableSet_Inside.preimage hW
  have hI : Integrable (fun ω => s.indicator (W ω)) μ := by
    have hh := (integrable_const (1 : ℝ) (μ := μ)).indicator hs
    simpa only [indicator, Set.indicator, mem_setOf_eq] using hh
  have hF : Integrable (fun ω => s.F (W ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.measurable.comp hW).aestronglyMeasurable
    exact ae_of_all _ (fun ω => s.norm_F_le_one _)
  rw [← s.integral_indicator_eq_probability μ W hW, ← integral_sub hF hI]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun ω => s.F (W ω) - s.indicator (W ω)) (μ := μ)

theorem probability_gap_le_smoother_gap_add_endpoint_errors
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure E) [IsFiniteMeasure ν]
    (W : Ω → Vector p) (hW : Measurable W) (Z : E → Vector p) (hZ : Measurable Z) :
    |μ.real {ω | s.Inside (W ω)} - ν.real {z | s.Inside (Z z)}| ≤
      |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F (Z z) ∂ν)| +
        (∫ ω, |s.F (W ω) - s.indicator (W ω)| ∂μ) +
        (∫ z, |s.F (Z z) - s.indicator (Z z)| ∂ν) := by
  have hμ := s.integral_endpoint_error_le_integral_abs μ W hW
  have hν := s.integral_endpoint_error_le_integral_abs ν Z hZ
  have hm := abs_le.mp (le_refl |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F (Z z) ∂ν)|)
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hμ).1, (abs_le.mp hμ).2,
    (abs_le.mp hν).1, (abs_le.mp hν).2, hm.1, hm.2]

end
end RectangleCLT.FaceSmoother

namespace RectangleCLT.Companion

noncomputable section

def coarseComparisonConstant : ℝ :=
  6 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)

theorem coarseComparisonConstant_nonneg : 0 ≤ coarseComparisonConstant := by
  unfold coarseComparisonConstant interpolationShortScaleConstant
  positivity

/-- A fixed explicit constant, independent of the dimension, probability
space, covariance, observations, rectangle, and chosen bandwidth. -/
def coarseBandwidthConstant : ℝ := 1 + coarseComparisonConstant + endpointConstant

theorem coarseBandwidthConstant_ge_one : 1 ≤ coarseBandwidthConstant := by
  unfold coarseBandwidthConstant
  linarith [coarseComparisonConstant_nonneg, endpointConstant_nonneg]

/-- An actual covariance-free rectangle estimate at every bandwidth
`h ≥ 12δ`. It is a coarse short-scale estimate, weaker than the optimized
rates stated in the companion manuscript. The covariance may be singular,
and the rectangle may have any endpoint conventions and atomic boundaries. -/
theorem rectangleError_le_coarse_bandwidth
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (R : Rect p) (h : ℝ) (hband : 12 * δ ≤ h) :
    rectangleError μ (sumVector ξ) A R ≤
      coarseBandwidthConstant * Real.sqrt (dimensionLog p) *
        (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3 + h * dimensionLog p) := by
  have hδ : 0 < δ := hdata.delta_pos hp hunit
  have hh : 0 < h := by linarith only [hband, hδ]
  have hb : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
  have hdiag : ∀ j, (A * A.transpose) j j = 1 := by
    intro j
    rw [hA]
    exact hunit j
  have hCcmp : coarseComparisonConstant ≤ coarseBandwidthConstant := by
    unfold coarseBandwidthConstant
    linarith [endpointConstant_nonneg]
  have hCend : endpointConstant ≤ coarseBandwidthConstant := by
    unfold coarseBandwidthConstant
    linarith [coarseComparisonConstant_nonneg]
  have hsqrt : 0 ≤ Real.sqrt (dimensionLog p) := Real.sqrt_nonneg _
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hM : 0 ≤ gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3 :=
    add_nonneg (div_nonneg (gamma3_nonneg μ ξ) (sq_nonneg _))
      (div_nonneg (gamma4_nonneg μ ξ) (pow_nonneg hh.le _))
  have hS : 0 ≤ h * dimensionLog p := mul_nonneg hh.le hL
  apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
  intro lo hi
  let s := FaceSmoother.closedBox lo hi h hh
  have hgap := s.interpolation_smoother_gap_shortScale_le μ ξ hdata hp hunit A hA hband
  have hends := s.bounded_gaussian_endpoint_error_le hdata hp hunit A hdiag hb 0
  simp only [add_zero] at hends
  have hprob := s.probability_gap_le_smoother_gap_add_endpoint_errors μ (gaussianLaw A)
    (sumVector ξ) hdata.measurable_sum id measurable_id
  simp only [id_eq] at hprob
  rw [add_assoc] at hprob
  have hclosed := hprob.trans (add_le_add hgap hends)
  have hμ : {ω | s.Inside (sumVector ξ ω)} =
      sumVector ξ ⁻¹' (Rect.closedBox lo hi).carrier := by
    ext ω
    exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
  have hG : {z | s.Inside z} = (Rect.closedBox lo hi).carrier := by
    ext z
    exact FaceSmoother.closedBox_Inside lo hi h hh z
  rw [hμ, hG] at hclosed
  change rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
    coarseComparisonConstant * Real.sqrt (dimensionLog p) *
      (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3) +
    endpointConstant * h * Real.sqrt (dimensionLog p) * dimensionLog p at hclosed
  apply hclosed.trans
  calc
    _ = coarseComparisonConstant * (Real.sqrt (dimensionLog p) *
          (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3)) +
        endpointConstant * (Real.sqrt (dimensionLog p) * (h * dimensionLog p)) := by ring
    _ ≤ coarseBandwidthConstant * (Real.sqrt (dimensionLog p) *
          (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3)) +
        coarseBandwidthConstant * (Real.sqrt (dimensionLog p) * (h * dimensionLog p)) :=
      add_le_add (mul_le_mul_of_nonneg_right hCcmp (mul_nonneg hsqrt hM))
        (mul_le_mul_of_nonneg_right hCend (mul_nonneg hsqrt hS))
    _ = _ := by ring

end
end RectangleCLT.Companion
