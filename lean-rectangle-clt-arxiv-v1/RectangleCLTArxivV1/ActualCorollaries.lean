import RectangleCLTArxivV1.ActualNormalizedMatrices
import RectangleCLTArxivV1.ExceptionalMain
import RectangleCLTArxivV1.GapMain

/-! Supplier-free Corollaries 4 and 5. The two actual geometric matrix
families are instantiated from their proved native propositions; every
remaining hypothesis concerns only the original bounded array/covariance. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def corollary4Constant : ℝ := positiveGapCoreConstant (actualMatrixConstant intrinsicBoundaryConstant)

theorem corollary4Constant_ge_one : 1≤corollary4Constant := positiveGapCoreConstant_ge_one _

theorem corollary4Constant_pos : 0<corollary4Constant := zero_lt_one.trans_le corollary4Constant_ge_one

def corollary5Constant : ℝ := exceptionalCoreConstant (actualMatrixConstant intrinsicBoundaryConstant)

theorem corollary5Constant_ge_one : 1≤corollary5Constant := exceptionalCoreConstant_ge_one _

theorem corollary5Constant_pos : 0<corollary5Constant := zero_lt_one.trans_le corollary5Constant_ge_one

/-- Corollary 4 for the actual bounded original array and Gaussian law.
The positive coordinate gap is the only additional geometric hypothesis. -/
theorem corollary4_positive_correlation_gap
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hgap : ∀ j k : Fin p,j≠k → c≤1-|covariance μ (sumVector ξ) j k|) :
    rectangleDistance μ (sumVector ξ) A≤corollary4Constant*
      min 1 (positiveGapRate (gaussianMaximumMean A) δ (dimensionLog p) c) := by
  let C := actualMatrixConstant intrinsicBoundaryConstant
  apply positiveGap_CLT_of_matrix_suppliers μ ξ h hp hunit A hA hc hc1 hgap (actualMatrixConstant_ge_one _)
  intro s _ hband hsmall t ht
  have hrelative : relativeDerivativeBandwidth≤positiveGapBandwidthConstant C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have htwo : 2≤positiveGapBandwidthConstant C :=
    ((by norm_num : (2:ℝ)≤4).trans relativeDerivativeBandwidth_ge_four).trans hrelative
  have hband2 : 2*δ≤s.bandwidth := (mul_le_mul_of_nonneg_right htwo h.delta_nonneg).trans hband
  exact actual_normalized_gap_matrix_estimates h hp hunit A hA s intrinsicBoundaryConstant_pos
    (zero_lt_one.trans_le (one_le_intrinsicBoundaryCoefficient μ ξ A hp)) hband2 hsmall.le
    ⟨ht.1.le,ht.2.le⟩ hc hc1
    (intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
      (mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)) ht.1.le ht.2.le)

/-- Corollary 5 in its literal two-thirds-power form. No lower bound on
the positive coordinate gaps is assumed, and perfectly correlated pairs
contribute zero to the original j<k exceptional budget. -/
theorem corollary5_exceptional_correlation_budget
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c : ℝ} (hc : 0<c) (hc1 : c≤1) :
    rectangleDistance μ (sumVector ξ) A≤corollary5Constant*
      min 1 (δ*(gaussianMaximumMean A*dimensionLog p)*Real.sqrt (exceptionalCutoffLog c)+
        δ^((2:ℝ)/3)*(gaussianMaximumMean A*dimensionLog p)^((2:ℝ)/3)*
          (exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c)^((1:ℝ)/3)) := by
  let C := actualMatrixConstant intrinsicBoundaryConstant
  apply exceptional_CLT_printed_of_matrix_suppliers μ ξ h hp hunit A hA hc hc1 (actualMatrixConstant_ge_one _)
  intro s _ hband hsmall t ht
  have htwo : 2≤exceptionalBandwidthConstant C :=
    (by norm_num : (2:ℝ)≤16).trans (le_max_left _ _)
  have hband2 : 2*δ≤s.bandwidth := (mul_le_mul_of_nonneg_right htwo h.delta_nonneg).trans hband
  exact actual_normalized_matrix_estimates h hp hunit A hA s intrinsicBoundaryConstant_pos
    (zero_lt_one.trans_le (one_le_intrinsicBoundaryCoefficient μ ξ A hp)) hband2 hsmall.le
    ⟨ht.1.le,ht.2.le⟩
    (intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
      (mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)) ht.1.le ht.2.le)

end
end RectangleCLTArxivV1
