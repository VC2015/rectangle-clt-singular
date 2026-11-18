import RectangleCLTArxivV1.ExpectedMaximum
import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.Rates

/-!
# Inputs and intrinsic coefficient in the printed Theorem 1

The two fourth-moment matrices are kept separate. The boundary coefficient
is exactly the minimum in the frozen manuscript, rather than a new
concentration or interpolation assumption.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The same-copy and independent-copy fourth bounds in the printed setup. -/
structure IntrinsicFourthBounds {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (s₄ : ℝ) : Prop where
  nonneg : 0 ≤ s₄
  fourth_upper : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))
  fresh_fourth_upper : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))

/-- The archived same-copy matrix is the actual matrix `Q_j` in the paper. -/
theorem relativeFourthMatrix_eq_printed {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j k l : Fin p) :
    relativeFourthMatrix μ ξ j k l =
      ∑ i, ∫ ω, ξ i ω j ^ 2 * (ξ i ω k * ξ i ω l) ∂μ := rfl

/-- The fresh matrix is `Qtilde_j`, a product of actual second moments. -/
theorem relativeFreshFourthMatrix_eq_printed {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j k l : Fin p) :
    relativeFreshFourthMatrix μ ξ j k l =
      ∑ i, (∫ ω, ξ i ω j ^ 2 ∂μ) * (∫ ω, ξ i ω k * ξ i ω l ∂μ) := rfl

/-- The third budget needed by interpolation is derived from the envelope;
it is not a further premise of the fourth-only theorem. -/
theorem IntrinsicFourthBounds.relativeMomentBounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ s₄ : ℝ}
    (hr : IntrinsicFourthBounds μ ξ s₄) (h : BoundedIndependentHypotheses μ ξ δ) :
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

/-- The exact intrinsic boundary coefficient in Section 2. -/
noncomputable def intrinsicBoundaryCoefficient {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  min (Real.sqrt (dimensionLog p))
    (1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A))

theorem intrinsicBoundaryCoefficient_le_logarithmic {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    intrinsicBoundaryCoefficient μ ξ A ≤ Real.sqrt (dimensionLog p) := min_le_left _ _

theorem intrinsicBoundaryCoefficient_le_maximum {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    intrinsicBoundaryCoefficient μ ξ A ≤
      1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A) := min_le_right _ _

theorem one_le_intrinsicBoundaryCoefficient {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hp : 1 ≤ p) :
    1 ≤ intrinsicBoundaryCoefficient μ ξ A := by
  apply le_min (Real.one_le_sqrt.mpr (log_exp_mul_nat_ge_one hp))
  have hmean : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  linarith [le_max_left (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]

/-- The intrinsic rate displayed in the first conclusion of Theorem 1. -/
noncomputable def intrinsicRelativeRate (g δ s₄ L : ℝ) : ℝ :=
  g * L * (δ + Real.sqrt (s₄ * D_L δ L))

theorem intrinsicRelativeRate_nonneg {g δ s₄ L : ℝ} (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hL : 0 ≤ L) : 0 ≤ intrinsicRelativeRate g δ s₄ L := by
  unfold intrinsicRelativeRate
  positivity

/-- A numerical factor that absorbs the unit constant in the definition of
the intrinsic boundary coefficient. -/
noncomputable def intrinsicGaussianCoefficientConstant : ℝ :=
  1 / Real.sqrt (2 / Real.pi) + 2 * expectedMaximumConstant

theorem intrinsicGaussianCoefficientConstant_pos : 0 < intrinsicGaussianCoefficientConstant := by
  unfold intrinsicGaussianCoefficientConstant
  have hc := expectedMaximumConstant_pos
  positivity

/-- Lemma C.2 supplies the Gaussian width in the nontrivial envelope regime. -/
theorem intrinsicBoundaryCoefficient_le_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hsmall : δ * dimensionLog p ≤ gaussianMaximumMean A) :
    intrinsicBoundaryCoefficient μ ξ A ≤
      intrinsicGaussianCoefficientConstant * gaussianMaximumMean A := by
  have hC : 1 ≤ expectedMaximumConstant :=
    (by norm_num : (1 : ℝ) ≤ 1536).trans (le_max_right _ _)
  have hg := gaussianMaximumMean_nonneg A
  have hE := bounded_sum_expected_maximum h hp hunit A hA
  have hEs : (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
      2 * expectedMaximumConstant * gaussianMaximumMean A := by
    have hh := mul_le_mul_of_nonneg_left hsmall expectedMaximumConstant_pos.le
    nlinarith
  have hgg : gaussianMaximumMean A ≤ 2 * expectedMaximumConstant * gaussianMaximumMean A := by
    nlinarith
  have hmax := max_le hEs hgg
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
  have hc : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hquot : 1 ≤ gaussianMaximumMean A / Real.sqrt (2 / Real.pi) := by
    apply (le_div_iff₀ hc).mpr
    simpa using hlow
  have hk := intrinsicBoundaryCoefficient_le_maximum μ ξ A
  unfold intrinsicGaussianCoefficientConstant
  simp only [one_div]
  rw [div_eq_mul_inv] at hquot
  nlinarith

end RectangleCLTArxivV1
