import RectangleCLTArxivV1.ActualCorollaries
import RectangleCLTArxivV1.ExceptionalTimeIntegral

/-! Actual source time-L1 and the sharp separated/exceptional integrated
budget, with the geometric matrices and original concentration supplied
internally from the proved native results. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def corollary5RemainderConstant : ℝ :=
  2*exceptionalComparisonConstant intrinsicBoundaryConstant (actualMatrixConstant intrinsicBoundaryConstant)

theorem corollary5RemainderConstant_pos : 0<corollary5RemainderConstant :=
  mul_pos (by norm_num) (exceptionalComparisonConstant_pos intrinsicBoundaryConstant_pos)

theorem corollary5_normalized_remainder_abs_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : 16*δ≤s.bandwidth) :
    let ε := dimensionLog p*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    IntervalIntegrable (fun t => |normalizedSeededFourthRemainder s μ ξ A ε hε t|) volume 0 1 :=
  exceptional_normalized_remainder_abs_intervalIntegrable h hp hunit A hA s hband

/-- The actual integrated source R4 bound in Appendix I, with no
concentration, matrix, derivative, remainder or time-L1 supplier premise. -/
theorem corollary5_normalized_remainder_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p)
    (hband : exceptionalBandwidthConstant (actualMatrixConstant intrinsicBoundaryConstant)*δ≤s.bandwidth)
    (hsmall : dimensionLog p*s.bandwidth^2≤1/4)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1) :
    let ε := dimensionLog p*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    (∫ t in (0:ℝ)..1,|normalizedSeededFourthRemainder s μ ξ A ε hε t|)≤
      corollary5RemainderConstant*
        (δ^2*intrinsicBoundaryCoefficient μ ξ A*dimensionLog p*exceptionalCutoffLog c/s.bandwidth+
          δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2) := by
  let C := actualMatrixConstant intrinsicBoundaryConstant
  let κ := intrinsicBoundaryCoefficient μ ξ A
  have hδ := h.delta_nonneg
  have hκ : 0<κ := zero_lt_one.trans_le (one_le_intrinsicBoundaryCoefficient μ ξ A hp)
  have hC : 1≤C := actualMatrixConstant_ge_one _
  have hBW : positiveGapBandwidthConstant C≤exceptionalBandwidthConstant C := le_max_right _ _
  have hrelative : relativeDerivativeBandwidth≤exceptionalBandwidthConstant C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hBW
  have hseed : seededRestorationBandwidth*δ≤s.bandwidth :=
    (relative_derivative_bandwidth_conditions hδ
      ((mul_le_mul_of_nonneg_right hrelative hδ).trans hband)).2
  have hrest : 4*restorationBandwidthConstant C≤exceptionalBandwidthConstant C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hBW
  have hrestband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth := by
    have hh := (mul_le_mul_of_nonneg_right hrest hδ).trans hband
    convert hh using 1 <;> ring
  have h16 : 16*δ≤s.bandwidth :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ).trans hband
  have h2 : 2*δ≤s.bandwidth := (by nlinarith : 2*δ≤16*δ).trans h16
  have hconc (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) intrinsicBoundaryConstant δ κ :=
    intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
      (mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)) ht.1.le ht.2.le
  have hmatrix (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t :=
    actual_normalized_matrix_estimates h hp hunit A hA s intrinsicBoundaryConstant_pos hκ h2 hsmall
      ⟨ht.1.le,ht.2.le⟩ (hconc t ht)
  have hb := exceptional_normalized_remainder_integral_of_matrix_suppliers μ ξ h hp hunit A hA s hseed
    hc hc1 hC intrinsicBoundaryConstant_pos hκ hrestband h16 hconc hmatrix
  have hE : 0≤exceptionalComparisonConstant intrinsicBoundaryConstant C*δ^2*
      exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg (exceptionalComparisonConstant_pos intrinsicBoundaryConstant_pos).le
      (sq_nonneg _)) (exceptionalCorrelationBudget_nonneg _ _)) (sq_nonneg _)
  apply hb.trans
  unfold corollary5RemainderConstant
  dsimp only [κ,C] at hE ⊢
  ring_nf at hE ⊢
  nlinarith only [hE]

end
end RectangleCLTArxivV1
