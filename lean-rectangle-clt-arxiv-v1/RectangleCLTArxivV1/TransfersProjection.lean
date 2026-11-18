import RectangleCLTArxivV1.GaussianCalibration
import RectangleCLTCompanion.SplitV4.GaussianFaceTransfer
import RectangleCLTCompanion.SplitV4.RelativeMomentTransfer

/-!
# Exact projection inputs for the v1 polyhedral transfer

This file supplies Appendix D.2's transformation of actual random arrays,
both relative fourth-moment matrices, the actual Gaussian width, and the
polyhedral probability events. It does not invoke the archive's older CLT
rate in place of the new width-dependent Theorem 1.
-/

namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The two fourth-moment inequalities in the printed v1 theorem. The
independent-copy matrix is an additional genuine moment, not a renamed copy
of the same-observation matrix. -/
structure RelativeFourthBudgets {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (s₄ : ℝ) : Prop where
  nonneg : 0 ≤ s₄
  same_copy : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))
  independent_copy : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))

/-- The third-moment bounds needed by the archive's projection algebra are
derived from the actual envelope; they are not extra public assumptions. -/
theorem RelativeFourthBudgets.toRelativeMomentBounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthBudgets μ ξ s₄) :
    RelativeMomentBounds μ ξ δ s₄ := by
  have hb := relativeMomentBounds_of_envelope h
  exact
    { measurable := hb.measurable
      second_integrable := hb.second_integrable
      third_integrable := hb.third_integrable
      fourth_integrable := hb.fourth_integrable
      s₃_nonneg := h.delta_nonneg
      s₄_nonneg := hr.nonneg
      third_lower := hb.third_lower
      third_upper := hb.third_upper
      fourth_upper := hr.same_copy
      fresh_fourth_upper := hr.independent_copy }

/-- Both printed fourth budgets undergo precisely the substitution `s₄ ↦ J²s₄`. -/
theorem relativeFourthBudgets_projected {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p m n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthBudgets μ ξ s₄)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    RelativeFourthBudgets μ (fun i ω => M.mulVec (ξ i ω)) (J ^ 2 * s₄) := by
  have hp := relativeMomentBounds_projected h (hr.toRelativeMomentBounds h) M J hJ hM
  exact ⟨hp.s₄_nonneg, hp.fourth_upper, hp.fresh_fourth_upper⟩

/-- Standardizing the positive-variance faces gives exactly the bounded
array, both fourth budgets, and unit marginal variances required by the new
Theorem 1. No covariance rank condition is introduced. -/
theorem standardizedProjection_inputs {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p m n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hr : RelativeFourthBudgets μ ξ s₄)
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 0 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = (σ α) ^ 2) :
    let η := fun i ω => (standardizedFaceMap ν σ).mulVec (ξ i ω)
    BoundedIndependentHypotheses μ η (J * δ) ∧
      RelativeFourthBudgets μ η (J ^ 2 * s₄) ∧
      (∀ α, covariance μ (sumVector η) α α = 1) := by
  let M := standardizedFaceMap ν σ
  have hM := standardizedFaceMap_row_l1_le ν σ J hσ hν
  refine ⟨boundedIndependent_projected h M J hJ hM,
    relativeFourthBudgets_projected h hr M J hJ hM, ?_⟩
  intro α
  rw [covariance_projected_sum h M J hJ hM]
  exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α

/-- The actual Gaussian width of an arbitrary projected factor law. -/
noncomputable def projectedGaussianMean {p m : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (M : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∫ z : Vector p, ‖M.mulVec z‖ ∂gaussianLaw A

/-- The projected width `g_P` is exactly the width of any square factor of
the projected covariance. This is an equality of actual integrals. -/
theorem gaussianMaximumMean_projected {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ)
    (hgram : C * C.transpose = M * (A * A.transpose) * M.transpose) :
    gaussianMaximumMean C = projectedGaussianMean A M := by
  unfold gaussianMaximumMean projectedGaussianMean
  rw [← gaussianLaw_map_mulVec_eq_of_gram M A C hgram]
  rw [integral_map (measurable_rectangular_mulVec M).aemeasurable measurable_norm.aestronglyMeasurable]

/-- The standardized projected width has the stated worst-case dimension
bound, independently of singularity of its covariance. -/
theorem projectedGaussianMean_le_sqrt_dimension {p m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ)
    (hgram : C * C.transpose = M * (A * A.transpose) * M.transpose)
    (hdiag : ∀ α, (C * C.transpose) α α = 1) :
    projectedGaussianMean A M ≤ 2 * Real.sqrt (dimensionLog m) := by
  rw [← gaussianMaximumMean_projected M A C hgram]
  exact gaussianLaw_integral_norm_le hm C hdiag

/-- Exact lower-orthant reduction, before any Gaussian approximation rate
is applied. Thus the new width-dependent bound can be transported once its
bounded theorem has been proved. -/
theorem polyhedralDistance_le_standardizedRectangleDistance {Ω : Type*} [MeasurableSpace Ω]
    {p m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (hσ : ∀ α, 0 < σ α)
    (hgram : C * C.transpose = standardizedFaceMap ν σ * (A * A.transpose) *
      (standardizedFaceMap ν σ).transpose) :
    polyhedralDistance μ W A ν ≤
      rectangleDistance μ (fun ω => (standardizedFaceMap ν σ).mulVec (W ω)) C :=
  polyhedralDistance_le_projected_rectangleDistance μ W A C ν σ hσ hgram

end RectangleCLTArxivV1
