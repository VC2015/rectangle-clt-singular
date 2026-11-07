import RectangleCLTCompanion.SplitV4.RelativeUniform
import RectangleCLTCompanion.SplitV4.Smoothing

/-! Conditional smoothing/algebra reduction for the relative CLT.
This helper explicitly assumes a smooth-comparison input. The terminal
Theorem 1 must supply that input from the proved two actual path estimates. -/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem relativeComparisonLog_one_le {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    1 ≤ relativeComparisonLog L h := by
  have hd : 0 ≤ 1/(L*h^2) := by positivity
  have hl := Real.log_nonneg (show 1 ≤ 1+1/(L*h^2) by linarith)
  unfold relativeComparisonLog
  linarith

theorem relativeCLT_of_uniform_smooth_comparison
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : RelativeIndependentHypotheses μ ξ δ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hgap : ∀ (b : ℝ) (hb : 0 < b), K*δ ≤ b → dimensionLog p*b^2 < 1/4 →
      ∀ lo hi : Vector p, let s := FaceSmoother.closedBox lo hi b hb
        |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
          C*dimensionLog p^(3/2 : ℝ)*(δ+s₄/b*relativeComparisonLog (dimensionLog p) b)) :
    rectangleDistance μ (sumVector ξ) A ≤
      relativeOptimizationConstant K (C+sharpEndpointConstant)*
        min 1 (relativeRate δ s₄ (dimensionLog p)) := by
  let L := dimensionLog p
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hδ : 0 < δ := h.toBoundedIndependentHypotheses.delta_pos hp h.unit_variance
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let b := relativeBandwidth K δ s₄ L
  have hb : 0 < b := relativeBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hK) hδ
  have hband : K*δ ≤ b := relativeBandwidth_admissible hK0
  have hdeltaband : δ ≤ b := (le_mul_of_one_le_left hδ.le hK).trans hband
  apply relative_rate_of_small_bandwidth_estimate hK (add_nonneg hC sharpEndpointConstant_nonneg)
    hδ hL h.toRelativeFourthAdmissible.nonneg (rectangleDistance_le_one μ (sumVector ξ) A)
  intro hsmall
  have hF := hgap b hb hband hsmall
  have hDisc := (smoothingDiscrepancy_le_iff μ (sumVector ξ) h.toBoundedIndependentHypotheses.measurable_sum A b hb
    (C*L^(3/2 : ℝ)*(δ+s₄/b*relativeComparisonLog L b))).mpr hF
  have hrho := (rectangleDistance_le_smoothingDiscrepancy_add_endpoint
    h.toBoundedIndependentHypotheses hp h.unit_variance A hA b hb hdeltaband).trans
      (add_le_add_right hDisc _)
  have hlog := relativeComparisonLog_one_le hLp hb
  have hF0 : 0 ≤ δ+s₄/b*relativeComparisonLog L b := by
    exact add_nonneg hδ.le (mul_nonneg (div_nonneg h.toRelativeFourthAdmissible.nonneg hb.le)
      (zero_le_one.trans hlog))
  have hR := Real.rpow_nonneg hLp.le (3/2 : ℝ)
  have heq : sharpEndpointConstant*b*Real.sqrt L*L = sharpEndpointConstant*L^(3/2 : ℝ)*b := by
    rw [rpow_three_halves_eq_mul_sqrt hLp]
    ring
  change rectangleDistance μ (sumVector ξ) A ≤
    (C+sharpEndpointConstant)*L^(3/2 : ℝ)*(b+δ+s₄/b*relativeComparisonLog L b)
  apply hrho.trans
  change C*L^(3/2 : ℝ)*(δ+s₄/b*relativeComparisonLog L b)+
    sharpEndpointConstant*b*Real.sqrt L*L ≤ _
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hC hR) hb.le,
    mul_nonneg (mul_nonneg sharpEndpointConstant_nonneg hR) hF0]

end
end RectangleCLT.Companion.SplitV4
