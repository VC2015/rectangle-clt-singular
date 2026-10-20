import RectangleCLT.Moments
import RectangleCLT.GaussianFactor
import RectangleCLT.Optimization
import RectangleCLT.LocalCovariance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The bounded rectangle CLT under local covariance nondegeneracy

This file defines the statement from the local-covariance manuscript. The
observations have a concrete probability model, and the comparison law is
the linear image of independent standard Gaussian coordinates. The local
CLT proposition is proved by `localRectangleCLT` in `Main.lean`.
No global lower eigenvalue bound is imposed on the covariance.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

/-- Independent centered bounded vector observations. This structure contains
no covariance nondegeneracy or Gaussian-approximation assumption. -/
structure BoundedIndependentHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ : ℝ) : Prop where
  measurable : ∀ i, Measurable (ξ i)
  independent : iIndepFun ξ μ
  centered : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0
  bounded : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ
  delta_nonneg : 0 ≤ δ

/-- The older globally nondegenerate data satisfy the bounded-independent
part of the new statement. This is only a bridge between data hypotheses. -/
theorem BoundedHypotheses.toBoundedIndependentHypotheses
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {δ b : ℝ}
    (h : BoundedHypotheses μ ξ δ b) : BoundedIndependentHypotheses μ ξ δ :=
  ⟨h.measurable, h.independent, h.centered, h.bounded, h.delta_nonneg⟩

/-- Unit coordinate variance in positive dimension rules out a zero envelope,
without any global spectral lower bound. -/
theorem BoundedIndependentHypotheses.delta_pos
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) : 0 < δ := by
  by_contra hnot
  have hδ : δ = 0 := le_antisymm (le_of_not_gt hnot) h.delta_nonneg
  have hξ : ∀ i, ξ i =ᵐ[μ] 0 := by
    intro i
    filter_upwards [h.bounded i] with ω hω
    exact norm_eq_zero.mp (le_antisymm (by simpa only [hδ] using hω) (norm_nonneg _))
  have hall : ∀ᵐ ω ∂μ, ∀ i, ξ i ω = 0 := ae_all_iff.mpr hξ
  have hsum : sumVector ξ =ᵐ[μ] 0 := by
    filter_upwards [hall] with ω hω
    simp [sumVector, hω]
  let j : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hp⟩
  have hvariance := hunit j
  rw [covariance_eq_zero_of_ae_eq_zero hsum] at hvariance
  norm_num at hvariance

/-- The exact three-term rate with covariance parameters supplied explicitly.
The powers are real powers: the local eigenvalues are not square roots.
The intrinsic parameters are inserted by `localCovarianceRate` below. -/
def localRateWithParameters {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ c a₃ a₄ : ℝ) : ℝ :=
  gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) / (c * a₃) +
    Real.sqrt (gamma4 μ ξ) * dimensionLog p /
      (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ)) +
    δ * Real.sqrt (dimensionLog p) / c

/-- Nonnegativity of the exact rate under its substantive positivity range. -/
theorem localRateWithParameters_nonneg
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {δ c a₃ a₄ : ℝ}
    (hp : 1 ≤ p) (hδ : 0 ≤ δ) (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    0 ≤ localRateWithParameters μ ξ δ c a₃ a₄ := by
  have hL := log_exp_mul_nat_ge_one hp
  have hL₀ : 0 ≤ dimensionLog p := by
    simpa only [dimensionLog] using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL)
  have hγ₃ := gamma3_nonneg μ ξ
  unfold localRateWithParameters
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact div_nonneg
      (mul_nonneg (mul_nonneg hγ₃ hL₀) (Real.sqrt_nonneg _))
      (mul_nonneg hc.le ha₃.le)
  · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL₀)
      (mul_nonneg (Real.rpow_pos_of_pos hc _).le
        (Real.rpow_pos_of_pos (mul_pos ha₃ ha₄) _).le)
  · exact div_nonneg (mul_nonneg hδ (Real.sqrt_nonneg _)) hc.le

/-- The covariance assumptions in the new theorem. Positive semidefiniteness
permits a singular full matrix. Only the intrinsic minimum for coordinate
groups of order at most four is required to be strictly positive. -/
structure LocalCovarianceHypotheses {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) : Prop where
  posSemidef : Q.PosSemidef
  unit_diagonal : ∀ j, Q j j = 1
  a4_pos : 0 < a4 Q

/-- The Gaussian factor demanded by the target exists under its actual
covariance hypotheses, including when the full covariance is singular. -/
theorem LocalCovarianceHypotheses.gaussian_factor_exists {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (h : LocalCovarianceHypotheses Q) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = Q := by
  refine ⟨h.posSemidef.sqrt, ?_⟩
  have hsymmetric : h.posSemidef.sqrt.transpose = h.posSemidef.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using h.posSemidef.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact h.posSemidef.sqrt_mul_self

/-- The exact local-covariance rate, with the intrinsic pair gap and local
three- and four-coordinate eigenvalues of the actual sum covariance. -/
def localCovarianceRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ : ℝ) : ℝ :=
  localRateWithParameters μ ξ δ
    (pairGap (covariance μ (sumVector ξ)))
    (a3 (covariance μ (sumVector ξ)))
    (a4 (covariance μ (sumVector ξ)))

/-- Only the saturated regime follows from the elementary probability bound.
This theorem makes no assertion about the unsaturated CLT rate. -/
theorem rectangleError_le_local_saturated
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) {C : ℝ}
    (hC : 1 ≤ C) (hrate : 1 ≤ localCovarianceRate μ ξ δ) :
    rectangleError μ (sumVector ξ) A R ≤ C * min 1 (localCovarianceRate μ ξ δ) := by
  rw [min_eq_left hrate, mul_one]
  exact (rectangleError_le_one μ (sumVector ξ) A R).trans hC

/-- Main local-covariance CLT statement for one universal constant.
Its proof for an explicit constant is `localRectangleCLT` in `Main.lean`.
The model allows atomic observations and singular full covariance matrices.
Rectangles include all measurable coordinate intervals and endpoint choices. -/
def LocalRectangleCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p, rectangleError μ (sumVector ξ) A R ≤
        C * min 1 (localCovarianceRate μ ξ δ)

/-- The absolute-constant statement from the updated manuscript, proved by
`localRectangleCLTExists` in `Main.lean`. Its constant is chosen before all probability spaces,
dimensions, laws, envelope parameters, and covariance parameters. -/
def LocalRectangleCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ LocalRectangleCLT.{u} C

end

end RectangleCLT
