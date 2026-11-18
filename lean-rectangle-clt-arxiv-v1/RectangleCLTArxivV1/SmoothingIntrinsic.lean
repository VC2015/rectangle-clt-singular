import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SplitV4.Printed.EndpointMixture

/-!+# Intrinsic smoothing error through the actual random threshold radius

This is the proof of Lemma 2 in the frozen source, lines 2920–2991.
The radius is the maximum of the actual exponential-clock threshold
shifts. Its expectation is estimated only after the deterministic-radius
concentration inequality has been integrated. The endpoint concentration
premises here are intermediate analytic inputs; Lemma 1 supplies them for
the bounded and Gaussian endpoints.
-/

namespace RectangleCLTArxivV1

set_option autoImplicit false

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SplitV4.Printed

/-- A zero-width layer is empty. Extending a positive-width concentration
bound to zero therefore introduces no continuity or atom assumption. -/
theorem intrinsicRectangleConcentration_nonneg_radius {p : ℕ}
    (μ : Measure (Vector p)) {C₀ δ κ : ℝ}
    (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hc : IntrinsicRectangleConcentration μ C₀ δ κ)
    (s : FaceSmoother p) {r : ℝ} (hr : 0 ≤ r) :
    μ.real (s.boundaryLayer r) ≤ C₀ * κ * (r + δ) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp only [FaceSmoother.boundaryLayer, neg_zero, Set.diff_self, measureReal_empty, zero_add]
    positivity
  · simpa only [add_zero] using hc s 0 r hr

/-- The literal radius-averaging step for an intrinsic layer coefficient. -/
theorem endpoint_error_le_intrinsic_average_radius {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hc : IntrinsicRectangleConcentration ν C₀ δ κ) :
    |ν.real {x | s.Inside x} - (∫ x, s.F x ∂ν)| ≤
      C₀ * κ * ((∫ e, randomThresholdRadius p s.bandwidth e
        ∂exponentialRectangleLaw p) + δ) := by
  simpa only [Real.sqrt_one, mul_one] using
    Printed.endpoint_error_le_average_radius hp s ν (C₀ * κ) δ 1
      (fun r hr => by
        simpa only [Real.sqrt_one, mul_one] using
          intrinsicRectangleConcentration_nonneg_radius ν hC₀ hδ hκ hc s hr)

/-- Actual all-rectangle smoothing reduction with the intrinsic coefficient.
The only analytic inputs concern the two actual endpoint laws; no smooth
comparison or rectangle approximation estimate is assumed. -/
theorem rectangleDistance_le_smoothingDiscrepancy_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) {C₀ δ κ h : ℝ}
    (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hh : 0 < h) (hδh : δ ≤ h)
    (hb : IntrinsicRectangleConcentration (μ.map W) C₀ δ κ)
    (hg : IntrinsicRectangleConcentration (gaussianLaw A) C₀ 0 κ) :
    rectangleDistance μ W A ≤ smoothingDiscrepancy μ W A h hh +
      9 * C₀ * h * κ * dimensionLog p := by
  letI : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hR := Printed.integral_randomThresholdRadius_le_log hp hh.le
  have hδL : δ ≤ h * dimensionLog p := hδh.trans (by nlinarith)
  have hCκ : 0 ≤ C₀ * κ := mul_nonneg hC₀ hκ
  have hboxes (lo hi : Vector p) : rectangleError μ W A (Rect.closedBox lo hi) ≤
      smoothingDiscrepancy μ W A h hh + 9 * C₀ * h * κ * dimensionLog p := by
    let s := FaceSmoother.closedBox lo hi h hh
    have hb' := endpoint_error_le_intrinsic_average_radius hp s (μ.map W) hC₀ hδ hκ hb
    have hg' := endpoint_error_le_intrinsic_average_radius hp s (gaussianLaw A)
      hC₀ (le_refl 0) hκ hg
    rw [integral_map hW.aemeasurable s.continuous_F.aestronglyMeasurable] at hb'
    have hinside : {x | s.Inside x} = (Rect.closedBox lo hi).carrier := by
      ext x; exact FaceSmoother.closedBox_Inside lo hi h hh x
    rw [Measure.real, Measure.map_apply hW s.measurableSet_Inside] at hb'
    rw [hinside] at hb' hg'
    have hgap := closedBoxSmoothingGap_le_smoothingDiscrepancy μ W hW A h hh (lo, hi)
    change |(∫ ω, s.F (W ω) ∂μ) - (∫ x, s.F x ∂gaussianLaw A)| ≤ _ at hgap
    have ht := abs_add_three
      (μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) - ∫ ω, s.F (W ω) ∂μ)
      ((∫ ω, s.F (W ω) ∂μ) - ∫ x, s.F x ∂gaussianLaw A)
      ((∫ x, s.F x ∂gaussianLaw A) - (gaussianLaw A).real (Rect.closedBox lo hi).carrier)
    have hsum :
        (μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) - ∫ ω, s.F (W ω) ∂μ) +
        ((∫ ω, s.F (W ω) ∂μ) - ∫ x, s.F x ∂gaussianLaw A) +
        ((∫ x, s.F x ∂gaussianLaw A) - (gaussianLaw A).real (Rect.closedBox lo hi).carrier) =
        μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) -
          (gaussianLaw A).real (Rect.closedBox lo hi).carrier := by ring
    rw [hsum, abs_sub_comm (∫ x, s.F x ∂gaussianLaw A)] at ht
    have hR' : (∫ e, randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p) =
        (∫ e, randomThresholdRadius p h e ∂exponentialRectangleLaw p) := rfl
    rw [hR'] at hb' hg'
    simp only [add_zero] at hg'
    have hrate := mul_le_mul_of_nonneg_left hR hCκ
    have hdeltarate := mul_le_mul_of_nonneg_left hδL hCκ
    change |μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) -
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
    change |μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) - ∫ ω, s.F (W ω) ∂μ| ≤ _ at hb'
    nlinarith only [ht, hb', hg', hgap, hrate, hdeltarate]
  apply rectangleDistance_le
  intro R
  exact rectangleError_le_of_closedBox hp μ W hW A hboxes R

end RectangleCLTArxivV1
