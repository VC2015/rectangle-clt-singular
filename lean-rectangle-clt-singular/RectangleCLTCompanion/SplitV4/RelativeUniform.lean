import RectangleCLTCompanion.SplitV4.RelativeFourthRefinement
import RectangleCLTCompanion.SplitV4.RelativeMomentTransfer
import RectangleCLTCompanion.SplitV4.RelativeOptimization
import RectangleCLTCompanion.RectangleDistance

/-! Exact fourth-only admissibility for the relative CLT. The signed third
budget required by the interpolation proof is derived from the actual
bounded summands, rather than included in the public model assumptions. -/

open MeasureTheory
open scoped BigOperators
universe u

namespace RectangleCLT.Companion.SplitV4
noncomputable section

structure RelativeFourthAdmissible {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (s₄ : ℝ) : Prop where
  nonneg : 0 ≤ s₄
  fourth_upper : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))
  fresh_fourth_upper : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))

structure RelativeIndependentHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ s₄ : ℝ) : Prop
    extends BoundedIndependentHypotheses μ ξ δ, RelativeFourthAdmissible μ ξ s₄ where
  unit_variance : ∀ j, covariance μ (sumVector ξ) j j = 1

theorem relativeMomentBounds_of_fourth_admissible
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthAdmissible μ ξ s₄) :
    RelativeMomentBounds μ ξ δ s₄ where
  measurable := h.measurable
  second_integrable := h.integrable_coordinate_pair
  third_integrable := integrable_relativeThird_entry h
  fourth_integrable := integrable_relativeFourth_entry h
  s₃_nonneg := h.delta_nonneg
  s₄_nonneg := hr.nonneg
  third_lower := (relativeMomentBounds_of_envelope h).third_lower
  third_upper := (relativeMomentBounds_of_envelope h).third_upper
  fourth_upper := hr.fourth_upper
  fresh_fourth_upper := hr.fresh_fourth_upper

theorem RelativeIndependentHypotheses.relativeMomentBounds
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : RelativeIndependentHypotheses μ ξ δ s₄) : RelativeMomentBounds μ ξ δ s₄ :=
  relativeMomentBounds_of_fourth_admissible h.toBoundedIndependentHypotheses h.toRelativeFourthAdmissible

theorem relativeFourthAdmissible_of_envelope
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) :
    RelativeFourthAdmissible μ ξ (δ^2) where
  nonneg := sq_nonneg _
  fourth_upper := (relativeMomentBounds_of_envelope h).fourth_upper
  fresh_fourth_upper := (relativeMomentBounds_of_envelope h).fresh_fourth_upper

theorem RelativeIndependentHypotheses.of_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    RelativeIndependentHypotheses μ ξ δ (δ^2) where
  toBoundedIndependentHypotheses := h
  toRelativeFourthAdmissible := relativeFourthAdmissible_of_envelope h
  unit_variance := hunit

theorem relativeFourthAdmissible_projected
    {Ω : Type u} [MeasurableSpace Ω] {p m n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthAdmissible μ ξ s₄)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    RelativeFourthAdmissible μ (fun i ω => M.mulVec (ξ i ω)) (J^2*s₄) := by
  have hh := relativeMomentBounds_projected h (relativeMomentBounds_of_fourth_admissible h hr) M J hJ hM
  exact ⟨hh.s₄_nonneg, hh.fourth_upper, hh.fresh_fourth_upper⟩

end
end RectangleCLT.Companion.SplitV4
