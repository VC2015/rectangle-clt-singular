import RectangleCLTArxivV1.IntrinsicComparison
import RectangleCLTArxivV1.SeededIntrinsicConcentration
import RectangleCLTArxivV1.DirectIntrinsicEnvelope

/-!
# The Gaussian-width refinement of Theorem 1

All layer and envelope suppliers are discharged from the actual independent
bounded array. Constants are fixed before dimensions, probability models,
and either fourth-moment matrix. No covariance inverse or positive spectral
lower bound is used. The proof retains the intrinsic coefficient until the
split at `δ L ≤ g_Σ`, and uses the elementary probability bound in the other
regime.
-/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def intrinsicBoundaryRateConstant : ℝ :=
  intrinsicOptimizationConstant relativeDerivativeBandwidth
    (intrinsicComparisonConstant intrinsicBoundaryConstant + 9 * intrinsicBoundaryConstant)

theorem one_le_intrinsicBoundaryRateConstant : 1 ≤ intrinsicBoundaryRateConstant := by
  have hA := relativeDerivativeBandwidth_ge_one
  have hC : 0 ≤ intrinsicComparisonConstant intrinsicBoundaryConstant + 9 * intrinsicBoundaryConstant := by
    linarith [intrinsicComparisonConstant_pos intrinsicBoundaryConstant_pos, intrinsicBoundaryConstant_pos]
  unfold intrinsicBoundaryRateConstant intrinsicOptimizationConstant
  nlinarith [mul_nonneg hC (show 0 ≤ relativeDerivativeBandwidth + 3 by linarith)]

def intrinsicCoreConstant : ℝ :=
  max (intrinsicBoundaryRateConstant * max 1 intrinsicGaussianCoefficientConstant)
    (max 1 (Real.pi / 2))

def intrinsicUniversalConstant : ℝ := 2 * intrinsicCoreConstant

theorem one_le_intrinsicCoreConstant : 1 ≤ intrinsicCoreConstant :=
  (le_max_left 1 (Real.pi / 2)).trans (le_max_right _ _)

theorem intrinsicUniversalConstant_pos : 0 < intrinsicUniversalConstant := by
  unfold intrinsicUniversalConstant
  linarith [one_le_intrinsicCoreConstant]

/-- The actual bounded-array comparison with the printed intrinsic
coefficient retained, before invoking the expected-maximum lemma. -/
theorem intrinsicBoundaryCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hr : IntrinsicFourthBounds μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicBoundaryRateConstant *
      min 1 (intrinsicRelativeRate (intrinsicBoundaryCoefficient μ ξ A) δ s₄ (dimensionLog p)) := by
  letI : NeZero p := ⟨by omega⟩
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA, hunit j]
  exact intrinsicCLT_of_uniform_boundary_suppliers μ ξ h hp hunit hr A hA
    intrinsicBoundaryConstant_pos (one_le_intrinsicBoundaryCoefficient μ ξ A hp)
    (intrinsicRectangleConcentration_bounded_endpoint h hp hunit A)
    (intrinsicRectangleConcentration_gaussian_endpoint μ ξ hp A hdiag)
    (fun s hfaces hband v hv0 hv1 =>
      integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA s hfaces hband hv0 hv1)
    (fun ε hε t ht =>
      intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0 hε ht.1 ht.2)

/-- Core Gaussian-width estimate, with both actual fourth matrices. -/
theorem intrinsicFourthMomentCLT_core
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hr : IntrinsicFourthBounds μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicCoreConstant *
      min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p)) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hg := gaussianMaximumMean_nonneg A
  have hr0 := intrinsicRelativeRate_nonneg hg h.delta_nonneg (zero_le_one.trans hL) (s₄ := s₄)
  have hone := rectangleDistance_le_one μ (sumVector ξ) A
  have hK : 0 ≤ intrinsicBoundaryRateConstant := zero_le_one.trans one_le_intrinsicBoundaryRateConstant
  by_cases hsmall : δ * dimensionLog p ≤ gaussianMaximumMean A
  · have hcoef := intrinsicBoundaryCoefficient_le_gaussian h hp hunit A hA hsmall
    have hcap := intrinsicRelativeRate_capped_le_coefficient hcoef
      intrinsicGaussianCoefficientConstant_pos.le hg h.delta_nonneg (zero_le_one.trans hL) (s₄ := s₄)
    have hh := (intrinsicBoundaryCLT μ ξ h hp hunit hr A hA).trans
      (mul_le_mul_of_nonneg_left hcap hK)
    apply hh.trans
    have hfin := mul_le_mul_of_nonneg_right
      (le_max_left (intrinsicBoundaryRateConstant * max 1 intrinsicGaussianCoefficientConstant)
        (max 1 (Real.pi / 2))) (le_min zero_le_one hr0)
    convert hfin using 1
    ring
  · have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA, hunit j]
    have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
    have hraw := intrinsic_trivial_large_envelope (s₄ := s₄) hone hlow h.delta_nonneg hL (lt_of_not_ge hsmall)
    have hc := intrinsic_capped_of_le_one_and_mul hr0 hone hraw
    exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_min zero_le_one hr0))

/-- Theorem 1: a universal coefficient times the capped Gaussian-width
rate, for arbitrary positive dimension and possibly singular covariance. -/
theorem intrinsicFourthMomentCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hr : IntrinsicFourthBounds μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
      min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p)) := by
  apply (intrinsicFourthMomentCLT_core μ ξ h hp hunit hr A hA).trans
  apply mul_le_mul_of_nonneg_right _ (le_min zero_le_one
    (intrinsicRelativeRate_nonneg (gaussianMaximumMean_nonneg A) h.delta_nonneg
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp))))
  unfold intrinsicUniversalConstant
  linarith [one_le_intrinsicCoreConstant]

/-- The two Loewner comparisons are separately visible in the public
fourth-only form of Theorem 1. -/
theorem intrinsicFourthMomentCLT_of_quadratic_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hs₄ : 0 ≤ s₄)
    (hQ : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ)))
    (hQfresh : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ)))
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
      min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p)) :=
  intrinsicFourthMomentCLT μ ξ h hp hunit ⟨hs₄, hQ, hQfresh⟩ A hA

/-- The envelope alone supplies the second, simpler rate in Theorem 1. -/
theorem intrinsicEnvelopeCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
      min 1 (δ * gaussianMaximumMean A * dimensionLog p * Real.sqrt (D_L δ (dimensionLog p))) := by
  have hmom := relativeMomentBounds_of_envelope h
  have hr : IntrinsicFourthBounds μ ξ (δ ^ 2) :=
    ⟨sq_nonneg δ, hmom.fourth_upper, hmom.fresh_fourth_upper⟩
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hg := gaussianMaximumMean_nonneg A
  have hrate := intrinsicRelativeRate_envelope_le hg h.delta_nonneg hL
  have hr0 : 0 ≤ δ * gaussianMaximumMean A * dimensionLog p * Real.sqrt (D_L δ (dimensionLog p)) :=
    mul_nonneg (mul_nonneg (mul_nonneg h.delta_nonneg hg) hL) (Real.sqrt_nonneg _)
  have hcap := (min_le_min_left 1 hrate).trans
    (intrinsic_min_one_mul_le (by norm_num : (0 : ℝ) ≤ 2) hr0)
  norm_num only [show max (1 : ℝ) 2 = 2 by norm_num] at hcap
  have hh := (intrinsicFourthMomentCLT_core μ ξ h hp hunit hr A hA).trans
    (mul_le_mul_of_nonneg_left hcap (zero_le_one.trans one_le_intrinsicCoreConstant))
  exact hh.trans_eq (by unfold intrinsicUniversalConstant; ring)

/-- A factor satisfying the two conclusions exists for every admissible
array, including singular covariance; the factor quantifier is substantive. -/
theorem intrinsicFourthMomentCLT_factor_exists
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hr : IntrinsicFourthBounds μ ξ s₄) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector ξ) ∧
      rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
        min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p)) ∧
      rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
        min 1 (δ * gaussianMaximumMean A * dimensionLog p * Real.sqrt (D_L δ (dimensionLog p))) := by
  obtain ⟨A, hA⟩ := gaussian_factor_exists_of_boundedIndependent h
  exact ⟨A, hA, intrinsicFourthMomentCLT μ ξ h hp hunit hr A hA,
    intrinsicEnvelopeCLT μ ξ h hp hunit A hA⟩

universe u

/-- The printed universal quantifiers for both conclusions of Theorem 1. -/
def IntrinsicTheoremOneContract (C : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ) (ξ : Fin n → Ω → Vector p) (δ : ℝ),
    BoundedIndependentHypotheses μ ξ δ → 1 ≤ p →
    (∀ j, covariance μ (sumVector ξ) j j = 1) →
    ∀ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = covariance μ (sumVector ξ) →
    (∀ s₄ : ℝ, IntrinsicFourthBounds μ ξ s₄ →
      rectangleDistance μ (sumVector ξ) A ≤ C *
        min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p))) ∧
    rectangleDistance μ (sumVector ξ) A ≤ C *
      min 1 (δ * gaussianMaximumMean A * dimensionLog p * Real.sqrt (D_L δ (dimensionLog p)))

/-- One constant is chosen before every model, dimension, and moment budget. -/
theorem theorem_1_intrinsic : ∃ C : ℝ, 0 < C ∧ IntrinsicTheoremOneContract.{u} C := by
  refine ⟨intrinsicUniversalConstant, intrinsicUniversalConstant_pos, ?_⟩
  intro Ω _ μ _ p n ξ δ h hp hunit A hA
  exact ⟨fun s₄ hr => intrinsicFourthMomentCLT μ ξ h hp hunit hr A hA,
    intrinsicEnvelopeCLT μ ξ h hp hunit A hA⟩

/-- Theorem 1 with raw observations and both fourth comparisons visible.
The envelope's nonnegativity is derived, rather than postulated separately. -/
theorem theorem_1_intrinsic_clt :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ), 1 ≤ p → 1 ≤ n →
      ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ),
      (∀ i, Measurable (ξ i)) → iIndepFun ξ μ →
      (∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) →
      (∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      ∀ s₄ : ℝ, 0 ≤ s₄ →
      (∀ j, QuadraticLE (relativeFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ))) →
      (∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ))) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = covariance μ (sumVector ξ) →
      (rectangleDistance μ (sumVector ξ) A ≤ C *
        min 1 (intrinsicRelativeRate (gaussianMaximumMean A) δ s₄ (dimensionLog p))) ∧
      rectangleDistance μ (sumVector ξ) A ≤ C *
        min 1 (δ * gaussianMaximumMean A * dimensionLog p * Real.sqrt (D_L δ (dimensionLog p))) := by
  refine ⟨intrinsicUniversalConstant, intrinsicUniversalConstant_pos, ?_⟩
  intro Ω _ μ _ p n hp hn ξ δ hmeas hind hcenter hbound hunit s₄ hs₄ hQ hQfresh A hA
  let h := boundedIndependent_of_raw hn ξ δ hmeas hind hcenter hbound
  exact ⟨intrinsicFourthMomentCLT_of_quadratic_bounds μ ξ h hp hunit hs₄ hQ hQfresh A hA,
    intrinsicEnvelopeCLT μ ξ h hp hunit A hA⟩

end
end RectangleCLTArxivV1
