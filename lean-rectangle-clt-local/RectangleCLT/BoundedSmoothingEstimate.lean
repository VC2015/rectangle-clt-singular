import RectangleCLT.InterpolationShortScale
import RectangleCLT.InterpolationIntegration
import RectangleCLT.RectangleSmoothing

/-! A fully proved coarse bandwidth estimate for actual rectangle
probabilities. The sharper local-covariance CLT rate remains a separate
analytic target. No derivative-envelope or comparison premise occurs here. -/

open MeasureTheory Set
open scoped BigOperators Interval

namespace RectangleCLT

noncomputable def boundedSmoothingConstant : ℝ :=
  1 + 6 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) + (8 * Real.exp 4 + 4)

theorem boundedSmoothingConstant_ge_one : 1 ≤ boundedSmoothingConstant := by
  have hK : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hE : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
  unfold boundedSmoothingConstant
  linarith

namespace FaceSmoother

/-- Integrating the fully instantiated actual path derivative gives a
coarse short-scale bound for the actual smoothed endpoint expectations. -/
theorem interpolation_smoother_gap_shortScale_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      6 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) *
          (gamma3 μ ξ / s.bandwidth ^ 2 + gamma4 μ ξ / s.bandwidth ^ 3) := by
  let K : ℝ := 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant
  let B : ℝ := 6 * K * Real.sqrt (dimensionLog p) *
    (gamma3 μ ξ / s.bandwidth ^ 2 + gamma4 μ ξ / s.bandwidth ^ 3)
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  have hg : IntegrableOn (fun _ : ℝ => B) (Icc 0 1) := by
    simp only [integrableOn_const, Real.volume_Icc, ENNReal.ofReal_lt_top, or_true]
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |s.selectorHeatDerivative μ ξ A 0 t| ≤ B := by
    have hh := s.abs_selectorHeatDerivative_shortScale_le μ ξ h hp hunit A hA hband ht.1.le ht.2.le
    have hγ : 0 ≤ gamma3 μ ξ / s.bandwidth ^ 2 :=
      div_nonneg (gamma3_nonneg μ ξ) (sq_nonneg _)
    have hterm : t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) +
        6 * gamma4 μ ξ / s.bandwidth ^ 3 ≤
        6 * (gamma3 μ ξ / s.bandwidth ^ 2 + gamma4 μ ξ / s.bandwidth ^ 3) := by
      have hc : t / 3 ≤ (6 : ℝ) := by linarith only [ht.2]
      have hm := mul_le_mul_of_nonneg_right hc hγ
      convert add_le_add_right hm (6 * gamma4 μ ξ / s.bandwidth ^ 3) using 1 <;> ring
    calc
      _ ≤ K * Real.sqrt (dimensionLog p) *
          (t * gamma3 μ ξ / (3 * s.bandwidth ^ 2) + 6 * gamma4 μ ξ / s.bandwidth ^ 3) := hh
      _ ≤ K * Real.sqrt (dimensionLog p) *
          (6 * (gamma3 μ ξ / s.bandwidth ^ 2 + gamma4 μ ξ / s.bandwidth ^ 3)) :=
        mul_le_mul_of_nonneg_left hterm (mul_nonneg hK (Real.sqrt_nonneg _))
      _ = B := by dsimp [B]; ring
  have hgap := s.interpolation_smoother_gap_le_integral μ h A hg hb
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hgap

end FaceSmoother

namespace BoundedIndependentHypotheses

/-- An unconditional coarse smoothing estimate for every measurable
coordinate rectangle, including arbitrary endpoint choices and atomic laws.
The full covariance may be singular. -/
theorem rectangleError_le_shortScale_bandwidth
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hc : 0 < pairGap (covariance μ (sumVector ξ)))
    (R : Rect p) (h : ℝ) (hband : 12 * δ ≤ h) :
    rectangleError μ (sumVector ξ) A R ≤
      boundedSmoothingConstant * Real.sqrt (dimensionLog p) *
        (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3 +
          h / pairGap (covariance μ (sumVector ξ))) := by
  have hδ : 0 < δ := hdata.delta_pos hp hunit
  have hh : 0 < h := by linarith only [hband, hδ]
  have hb : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
  let K : ℝ := 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant
  let E : ℝ := 8 * Real.exp 4 + 4
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCK : 6 * K ≤ boundedSmoothingConstant := by
    change 6 * K ≤ 1 + 6 * K + E
    linarith only [hE]
  have hCE : E ≤ boundedSmoothingConstant := by
    change E ≤ 1 + 6 * K + E
    linarith only [hK]
  have hL : 0 ≤ Real.sqrt (dimensionLog p) := Real.sqrt_nonneg _
  have hM : 0 ≤ gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3 :=
    add_nonneg (div_nonneg (gamma3_nonneg μ ξ) (sq_nonneg _))
      (div_nonneg (gamma4_nonneg μ ξ) (pow_nonneg hh.le _))
  have hS : 0 ≤ h / pairGap (covariance μ (sumVector ξ)) := div_nonneg hh.le hc.le
  apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
  intro lo hi
  let s := FaceSmoother.closedBox lo hi h hh
  have hgap := s.interpolation_smoother_gap_shortScale_le μ ξ hdata hp hunit A hA hband
  have herr := hdata.closedBox_error_le_smoother_gap hp hunit A hA hc lo hi hh hb
  apply (herr.trans (add_le_add_right hgap _)).trans
  change 6 * K * Real.sqrt (dimensionLog p) *
      (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3) +
      E * h * Real.sqrt (dimensionLog p) / pairGap (covariance μ (sumVector ξ)) ≤ _
  calc
    _ = (6 * K) * (Real.sqrt (dimensionLog p) *
        (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3)) +
      E * (Real.sqrt (dimensionLog p) * (h / pairGap (covariance μ (sumVector ξ)))) := by ring
    _ ≤ boundedSmoothingConstant * (Real.sqrt (dimensionLog p) *
        (gamma3 μ ξ / h ^ 2 + gamma4 μ ξ / h ^ 3)) +
      boundedSmoothingConstant * (Real.sqrt (dimensionLog p) *
        (h / pairGap (covariance μ (sumVector ξ)))) :=
      add_le_add (mul_le_mul_of_nonneg_right hCK (mul_nonneg hL hM))
        (mul_le_mul_of_nonneg_right hCE (mul_nonneg hL hS))
    _ = _ := by ring

end BoundedIndependentHypotheses
end RectangleCLT
