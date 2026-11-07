import RectangleCLTCompanion.SharpMain
import RectangleCLTCompanion.SubexponentialStatement
import RectangleCLTCompanion.RectangleDistance
import RectangleCLT.BoundedIndependentScaling

/-!
The normalized-observation form of the unrestricted envelope bound, matching
`cor:observations` in the pinned split-V4 manuscript.  The unit marginal
variance of the normalized sum is proved from the average second moments.
-/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {p n : ℕ} {X : Fin n → Ω → Vector p} {B : ℝ}

/-- Scalar normalization retains the actual covariance, including all cross
covariances, without a rank or eigenvalue assumption. -/
theorem bounded_normalizedObservationSum_covariance
    (h : BoundedIndependentHypotheses μ X B) :
    covariance μ (normalizedObservationSum X) =
      (1 / (n : ℝ)) • covariance μ (sumVector X) := by
  have hs : sumVector (fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω) =
      normalizedObservationSum X := by
    funext ω
    exact sumVector_smul X (Real.sqrt (n : ℝ))⁻¹ ω
  have hc := h.covariance_sum_smul (Real.sqrt (n : ℝ))⁻¹
  rw [hs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hc
  simpa only [one_div] using hc

/-- The manuscript's average marginal second moments are exactly the
normalized-sum marginal variances for independent centered summands. -/
theorem bounded_normalizedObservationSum_covariance_diagonal
    (h : BoundedIndependentHypotheses μ X B) (j : Fin p) :
    covariance μ (normalizedObservationSum X) j j =
      (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) := by
  rw [bounded_normalizedObservationSum_covariance h]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [h.covariance_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_two]

/-- Corollary 1 of split-V4, uniformly over the full measurable rectangle
class.  Its constant is fixed before every dimension and probability model.
The proof uses the existing envelope theorem; it does not certify the new
relative-moment theorem or the manuscript's revised Appendix B argument. -/
theorem normalizedObservationsCLT
    (h : BoundedIndependentHypotheses μ X B) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (R : Rect p) :
    rectangleError μ (normalizedObservationSum X) A R ≤
      (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (B / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  let ξ : Fin n → Ω → Vector p := fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω
  have hs : sumVector ξ = normalizedObservationSum X := by
    funext ω
    exact sumVector_smul X (Real.sqrt (n : ℝ))⁻¹ ω
  have hξ : BoundedIndependentHypotheses μ ξ (B / Real.sqrt (n : ℝ)) := by
    have hh := h.smul_of_nonneg (Real.sqrt (n : ℝ))⁻¹
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
    simpa only [ξ, div_eq_mul_inv, mul_comm] using hh
  have hunit (j : Fin p) : covariance μ (sumVector ξ) j j = 1 := by
    rw [hs, bounded_normalizedObservationSum_covariance_diagonal h, haverage]
  have hA' : A * A.transpose = covariance μ (sumVector ξ) := by
    rw [hs]
    exact hA
  simpa only [hs] using
    unrestrictedCLT μ p n hp hn ξ (B / Real.sqrt (n : ℝ)) A hξ hunit hA' R

/-- The same normalized-observation bound for the actual supremum over
the full measurable rectangle class used by the manuscript. -/
theorem normalizedObservationsRectangleDistanceCLT
    (h : BoundedIndependentHypotheses μ X B) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (B / Real.sqrt (n : ℝ)) (dimensionLog p)) :=
  rectangleDistance_le μ (normalizedObservationSum X) A
    (normalizedObservationsCLT h hp hn haverage A hA)

/-- A universal constant is chosen before all dimensions and probability
models in the actual rectangle-distance formulation of Corollary 1. -/
theorem normalizedObservationsCLTExists :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω' : Type u} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
        (p' n' : ℕ), 1 ≤ p' → 1 ≤ n' →
        ∀ (X' : Fin n' → Ω' → Vector p') (B' : ℝ)
          (A' : Matrix (Fin p') (Fin p') ℝ),
          BoundedIndependentHypotheses μ' X' B' →
          (∀ j, (1 / (n' : ℝ)) * (∑ i, ∫ ω, X' i ω j ^ 2 ∂μ') = 1) →
          A' * A'.transpose = covariance μ' (normalizedObservationSum X') →
          rectangleDistance μ' (normalizedObservationSum X') A' ≤
            C * min 1 (unrestrictedRate (B' / Real.sqrt (n' : ℝ)) (dimensionLog p')) := by
  refine ⟨2 * companionUniversalConstant, by linarith [one_le_companionUniversalConstant], ?_⟩
  intro Ω' _ μ' _ p' n' hp hn X' B' A' h haverage hA
  exact normalizedObservationsRectangleDistanceCLT h hp hn haverage A' hA

end

end RectangleCLT.Companion.SplitV4
