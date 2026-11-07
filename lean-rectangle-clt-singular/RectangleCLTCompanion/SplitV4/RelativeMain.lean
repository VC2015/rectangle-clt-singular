import RectangleCLTCompanion.SplitV4.RelativeSmoothingReduction
import RectangleCLTCompanion.SplitV4.RelativePathJoin
import RectangleCLTCompanion.SplitV4.DirectInitialization
import RectangleCLTCompanion.SplitV4.SeededRestorationRates
import RectangleCLTCompanion.SplitV4.RelativeDerivativeProposition

/-! Constants for the actual relative CLT are fixed before every dimension,
array and probability model. The final comparison consumes the proved
direct initialization and normalized seeded path estimates. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def relativeBandwidthConstant : ℝ := max 4 seededRestorationBandwidth

def relativeSmoothComparisonConstant : ℝ :=
  directInitializationConstant+seededDerivativeConstant

def relativeCoreConstant : ℝ := relativeOptimizationConstant relativeBandwidthConstant
  (relativeSmoothComparisonConstant+sharpEndpointConstant)

def relativeUniversalConstant : ℝ := 2*relativeCoreConstant

theorem relativeBandwidthConstant_ge_four : 4 ≤ relativeBandwidthConstant := le_max_left _ _

theorem relativeBandwidthConstant_ge_seeded : seededRestorationBandwidth ≤ relativeBandwidthConstant :=
  le_max_right _ _

theorem relativeSmoothComparisonConstant_pos : 0 < relativeSmoothComparisonConstant :=
  add_pos directInitializationConstant_pos seededDerivativeConstant_pos

theorem one_le_relativeCoreConstant : 1 ≤ relativeCoreConstant := by
  have hA := relativeBandwidthConstant_ge_four
  have hC := add_nonneg relativeSmoothComparisonConstant_pos.le sharpEndpointConstant_nonneg
  unfold relativeCoreConstant relativeOptimizationConstant
  nlinarith [mul_nonneg hC (show 0 ≤ relativeBandwidthConstant+3 by linarith)]

theorem one_le_relativeUniversalConstant : 1 ≤ relativeUniversalConstant := by
  unfold relativeUniversalConstant
  linarith [one_le_relativeCoreConstant]

theorem relativeMomentCLT_core
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : RelativeIndependentHypotheses μ ξ δ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      relativeCoreConstant*min 1 (relativeRate δ s₄ (dimensionLog p)) := by
  letI : NeZero p := ⟨by omega⟩
  apply relativeCLT_of_uniform_smooth_comparison μ hp ξ h A hA relativeBandwidthConstant
    relativeSmoothComparisonConstant (by linarith [relativeBandwidthConstant_ge_four])
    relativeSmoothComparisonConstant_pos.le
  intro b hb hband _ lo hi
  let s := FaceSmoother.closedBox lo hi b hb
  have he := relative_smooth_comparison_bound μ ξ h.toBoundedIndependentHypotheses
    h.relativeMomentBounds hp h.unit_variance A hA s rfl hband
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  simpa only [rpow_three_halves_eq_mul_sqrt hL,relativeComparisonLog,
    relativeSmoothComparisonConstant,relativeDerivativeConstant] using he

/-- Theorem 1 for the actual independent array and every admissible
same-copy/independent-copy fourth budget. The constant is fixed above the
probability model; singular covariance and all measurable rectangles remain. -/
theorem relativeMomentCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : RelativeIndependentHypotheses μ ξ δ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      relativeUniversalConstant*min 1 (relativeRate δ s₄ (dimensionLog p)) := by
  have he := relativeMomentCLT_core μ hp ξ h A hA
  have hm : 0 ≤ min 1 (relativeRate δ s₄ (dimensionLog p)) :=
    le_min zero_le_one (relativeRate_nonneg h.delta_nonneg
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hm
  unfold relativeUniversalConstant
  linarith [one_le_relativeCoreConstant]

/-- The public fourth-only contract of Theorem 1, with the two actual
Loewner comparisons supplied separately and no third-budget premise. -/
theorem relativeFourthMomentCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hs₄ : 0 ≤ s₄)
    (hQ : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ)))
    (hQfresh : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ)))
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      relativeUniversalConstant*min 1 (relativeRate δ s₄ (dimensionLog p)) :=
  relativeMomentCLT μ hp ξ
    { toBoundedIndependentHypotheses := h
      toRelativeFourthAdmissible := ⟨hs₄,hQ,hQfresh⟩
      unit_variance := hunit } A hA

theorem relativeEnvelopeCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      relativeUniversalConstant*min 1 (unrestrictedRate δ (dimensionLog p)) := by
  have he := relativeMomentCLT_core μ hp ξ (RelativeIndependentHypotheses.of_bounded h hunit) A hA
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hc := mul_le_mul_of_nonneg_left (relativeRate_envelope_capped_le h.delta_nonneg hL)
    (zero_le_one.trans one_le_relativeCoreConstant)
  exact (he.trans hc).trans_eq (by unfold relativeUniversalConstant; ring)

end
end RectangleCLT.Companion.SplitV4
