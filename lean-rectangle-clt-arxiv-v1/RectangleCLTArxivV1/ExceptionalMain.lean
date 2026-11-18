import RectangleCLTArxivV1.ExceptionalSeededComparison
import RectangleCLTArxivV1.SupplementalIOptimization
import RectangleCLTArxivV1.GapMain

/-! Corollary 5 from the actual source split and original-array comparison.
Only genuine cubic/full-angle nuclear matrix sums remain explicit. No
remainder, derivative, or CLT estimate is assumed by these endpoints. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def exceptionalSmoothComparisonConstant (C₀ C : ℝ) : ℝ :=
  directInitializationConstant+2*exceptionalComparisonConstant C₀ C

theorem exceptionalSmoothComparisonConstant_pos {C₀ C : ℝ} (hC₀ : 0 < C₀) :
    0 < exceptionalSmoothComparisonConstant C₀ C :=
  add_pos directInitializationConstant_pos (mul_pos (by norm_num) (exceptionalComparisonConstant_pos hC₀))

theorem exceptional_smooth_comparison_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces=Finset.univ)
    (hband : relativeDerivativeBandwidth*δ ≤ s.bandwidth)
    {c C C₀ κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 1 ≤ C) (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hgapband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth) (hsmallband : 16*δ≤s.bandwidth)
    (henv : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z)*
        (1-s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
          derivativeEnvelopeSignedAverageConstant*s.bandwidth*κ)
    (hconcentration : ∀ t ∈ Ioo (0:ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ∀ t ∈ Ioo (0:ℝ) 1, ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      exceptionalSmoothComparisonConstant C₀ C*((κ*dimensionLog p)*
        (δ+δ^2*exceptionalCutoffLog c/s.bandwidth)+δ^2*
          exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hε : 0 < ε := mul_pos (zero_lt_one.trans_le hL) (sq_pos_of_pos s.bandwidth_pos)
  have hJ : 1 ≤ exceptionalCutoffLog c := one_le_exceptionalCutoffLog hc hc1
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hi := direct_initialization_intrinsic_of_envelope μ ξ h (relativeMomentBounds_of_envelope h)
    hunit A hA s hfaces hb.1 (zero_le_one.trans hκ) henv
  have hs := exceptional_normalized_time_comparison_of_matrix_suppliers μ ξ h (h.delta_pos hp hunit)
    hp hunit A hA s hb.2 hc hc1 hC hC₀ (zero_lt_one.trans_le hκ) hgapband hsmallband hconcentration hmatrix
  have ht := smoother_gap_le_actual_two_stage_gaps s μ ξ h.measurable A hε.le
  have hh := ht.trans (add_le_add hi hs)
  change _ ≤ directInitializationConstant*δ*(L*κ)+directInitializationConstant*δ^2*(L*κ)/s.bandwidth+
    (2*exceptionalComparisonConstant C₀ C)*((κ*L)*(δ+δ^2*exceptionalCutoffLog c/s.bandwidth)+
      δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2) at hh
  apply hh.trans
  have hn : 0 ≤ directInitializationConstant*(κ*L)*(δ^2/s.bandwidth) := by
    exact mul_nonneg (mul_nonneg directInitializationConstant_pos.le
      (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL)))
      (div_nonneg (sq_nonneg δ) s.bandwidth_pos.le)
  have hj := mul_le_mul_of_nonneg_left hJ hn
  have hexc : 0≤directInitializationConstant*(δ^2*
      exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2) :=
    mul_nonneg directInitializationConstant_pos.le
      (div_nonneg (mul_nonneg (sq_nonneg _) (exceptionalCorrelationBudget_nonneg _ _)) (sq_nonneg _))
  unfold exceptionalSmoothComparisonConstant
  dsimp only [L] at hj hexc ⊢
  ring_nf at hj hexc ⊢
  nlinarith only [hj,hexc]

def exceptionalBandwidthConstant (C : ℝ) : ℝ := max 16 (positiveGapBandwidthConstant C)

theorem exceptionalBandwidthConstant_ge_one (C : ℝ) : 1≤exceptionalBandwidthConstant C :=
  (by norm_num : (1:ℝ)≤16).trans (le_max_left _ _)

def exceptionalBoundaryConstant (C : ℝ) : ℝ :=
  exceptionalBudgetOptimizationConstant (exceptionalBandwidthConstant C)
    (exceptionalSmoothComparisonConstant intrinsicBoundaryConstant C+9*intrinsicBoundaryConstant)

theorem exceptionalBoundaryConstant_ge_one (C : ℝ) : 1≤exceptionalBoundaryConstant C := by
  have hA := exceptionalBandwidthConstant_ge_one C
  have hD := exceptionalSmoothComparisonConstant_pos (C := C) intrinsicBoundaryConstant_pos
  have hB := intrinsicBoundaryConstant_pos
  unfold exceptionalBoundaryConstant exceptionalBudgetOptimizationConstant
  nlinarith [mul_nonneg (show 0≤exceptionalBandwidthConstant C by linarith)
    (show 0≤exceptionalSmoothComparisonConstant intrinsicBoundaryConstant C+9*intrinsicBoundaryConstant by linarith)]

/-- The optimized intrinsic boundary form of Corollary 5. Concentration,
initialization, source split, smoothing, both width branches and the cap
by one are proved from the bounded original array. -/
theorem exceptional_boundary_CLT_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c C : ℝ} (hc : 0<c) (hc1 : c≤1) (hC : 1≤C)
    (hmatrix : ∀ s : FaceSmoother p,s.faces=Finset.univ →
      exceptionalBandwidthConstant C*δ≤s.bandwidth → dimensionLog p*s.bandwidth^2<1/4 →
      ∀ t ∈ Ioo (0:ℝ) 1,
        ExceptionalNormalizedMatrixEstimates hp s μ ξ A C (intrinsicBoundaryCoefficient μ ξ A) t) :
    rectangleDistance μ (sumVector ξ) A≤exceptionalBoundaryConstant C*
      min 1 (exceptionalBudgetRate δ (intrinsicBoundaryCoefficient μ ξ A*dimensionLog p) c
        (exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c)) := by
  letI : NeZero p := ⟨by omega⟩
  let L := dimensionLog p
  let κ := intrinsicBoundaryCoefficient μ ξ A
  let B := exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c
  let b := exceptionalBudgetBandwidth (exceptionalBandwidthConstant C) δ (κ*L) c B
  have hL : 1≤L := log_exp_mul_nat_ge_one hp
  have hδ : 0<δ := h.delta_pos hp hunit
  have hκ : 1≤κ := one_le_intrinsicBoundaryCoefficient μ ξ A hp
  have hB : 0≤B := exceptionalCorrelationBudget_nonneg _ _
  have hBW := exceptionalBandwidthConstant_ge_one C
  have hbpos : 0<b := exceptionalBudgetBandwidth_pos (zero_lt_one.trans_le hBW) hδ hc hc1
  have hb : exceptionalBandwidthConstant C*δ≤b :=
    exceptionalBudgetBandwidth_admissible (zero_le_one.trans hBW) hδ.le hc hc1
  have hpg : positiveGapBandwidthConstant C≤exceptionalBandwidthConstant C := le_max_right _ _
  have hrelative : relativeDerivativeBandwidth≤exceptionalBandwidthConstant C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hpg
  have hrest : 4*restorationBandwidthConstant C≤exceptionalBandwidthConstant C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hpg
  have hband : relativeDerivativeBandwidth*δ≤b :=
    (mul_le_mul_of_nonneg_right hrelative hδ.le).trans hb
  have hgapband : restorationBandwidthConstant C*(4*δ)≤b := by
    have hh := (mul_le_mul_of_nonneg_right hrest hδ.le).trans hb
    convert hh using 1 <;> ring
  have hsmallband : 16*δ≤b :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le).trans hb
  have hδb : δ≤b := (le_mul_of_one_le_left hδ.le hBW).trans hb
  let D := exceptionalSmoothComparisonConstant intrinsicBoundaryConstant C
  have hD : 0<D := exceptionalSmoothComparisonConstant_pos intrinsicBoundaryConstant_pos
  have hK : 0≤D+9*intrinsicBoundaryConstant := by linarith [intrinsicBoundaryConstant_pos]
  apply exceptionalBudget_rate_of_small_bandwidth_estimate hBW hK hκ hδ hL hB hc hc1
    (rectangleDistance_le_one μ (sumVector ξ) A)
  intro hsmall
  have hsmooth : smoothingDiscrepancy μ (sumVector ξ) A b hbpos≤
      D*((κ*L)*(δ+δ^2*exceptionalCutoffLog c/b)+δ^2*B/b^2) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) h.measurable_sum A b hbpos _).mpr
    intro lo hi
    let s := FaceSmoother.closedBox lo hi b hbpos
    have hband4 : 4*δ≤s.bandwidth :=
      (mul_le_mul_of_nonneg_right relativeDerivativeBandwidth_ge_four hδ.le).trans hband
    exact exceptional_smooth_comparison_of_matrix_suppliers μ ξ h hp hunit A hA s rfl hband
      hc hc1 hC intrinsicBoundaryConstant_pos hκ hgapband hsmallband
      (fun v hv0 hv1 => integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA s rfl hband4 hv0 hv1)
      (fun t ht => intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
        (by positivity) ht.1.le ht.2.le)
      (hmatrix s rfl hb hsmall)
  have hrho := (rectangleDistance_le_smoothingDiscrepancy_intrinsic hp μ (sumVector ξ)
    h.measurable_sum A intrinsicBoundaryConstant_pos.le hδ.le (zero_le_one.trans hκ) hbpos hδb
    (intrinsicRectangleConcentration_bounded_endpoint h hp hunit A)
    (intrinsicRectangleConcentration_gaussian_endpoint μ ξ hp A (fun j => by rw [hA,hunit j]))).trans
      (add_le_add_right hsmooth _)
  have hJ : 0≤exceptionalCutoffLog c := zero_le_one.trans (one_le_exceptionalCutoffLog hc hc1)
  have hBC : 0 < intrinsicBoundaryConstant := intrinsicBoundaryConstant_pos
  have hlinear := mul_le_mul_of_nonneg_left hδb
    (show 0≤D*(κ*L) by positivity)
  have hextra : 0≤(9*intrinsicBoundaryConstant)*
      (δ^2*(κ*L)*exceptionalCutoffLog c/b+δ^2*B/b^2) := by positivity
  change rectangleDistance μ (sumVector ξ) A≤
    (D+9*intrinsicBoundaryConstant)*(κ*L*b+δ^2*(κ*L)*exceptionalCutoffLog c/b+δ^2*B/b^2)
  apply hrho.trans
  change D*((κ*L)*(δ+δ^2*exceptionalCutoffLog c/b)+δ^2*B/b^2)+9*intrinsicBoundaryConstant*b*κ*L≤_
  ring_nf at hlinear hextra ⊢
  nlinarith only [hlinear,hextra]

def exceptionalCoreConstant (C : ℝ) : ℝ :=
  max (exceptionalBoundaryConstant C*max 1 intrinsicGaussianCoefficientConstant) (max 1 (Real.pi/2))

theorem exceptionalCoreConstant_ge_one (C : ℝ) : 1≤exceptionalCoreConstant C :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- Corollary 5 with the actual Gaussian maximum coefficient, conditional
only on the two stated geometric matrix families. Perfectly correlated
pairs contribute zero to the original j<k exceptional budget. -/
theorem exceptional_CLT_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c C : ℝ} (hc : 0<c) (hc1 : c≤1) (hC : 1≤C)
    (hmatrix : ∀ s : FaceSmoother p,s.faces=Finset.univ →
      exceptionalBandwidthConstant C*δ≤s.bandwidth → dimensionLog p*s.bandwidth^2<1/4 →
      ∀ t ∈ Ioo (0:ℝ) 1,
        ExceptionalNormalizedMatrixEstimates hp s μ ξ A C (intrinsicBoundaryCoefficient μ ξ A) t) :
    rectangleDistance μ (sumVector ξ) A≤exceptionalCoreConstant C*
      min 1 (exceptionalBudgetRate δ (gaussianMaximumMean A*dimensionLog p) c
        (exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c)) := by
  have hL : 1≤dimensionLog p := log_exp_mul_nat_ge_one hp
  have hδ := h.delta_nonneg
  have hdiag (j : Fin p) : (A*A.transpose) j j=1 := by rw [hA,hunit j]
  have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
  have hg : 0<gaussianMaximumMean A := (by positivity : (0:ℝ)<Real.sqrt (2/Real.pi)).trans_le hlow
  have hB := exceptionalCorrelationBudget_nonneg (covariance μ (sumVector ξ)) c
  have hr : 0≤exceptionalBudgetRate δ (gaussianMaximumMean A*dimensionLog p) c
      (exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c) := by
    unfold exceptionalBudgetRate
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (exceptionalBudgetRoot_nonneg (by positivity) hB))
  have hone := rectangleDistance_le_one μ (sumVector ξ) A
  have hK : 0≤exceptionalBoundaryConstant C := zero_le_one.trans (exceptionalBoundaryConstant_ge_one C)
  by_cases hsmall : δ*dimensionLog p≤gaussianMaximumMean A
  · have hcoef := intrinsicBoundaryCoefficient_le_gaussian h hp hunit A hA hsmall
    have hcoef' : intrinsicBoundaryCoefficient μ ξ A≤max 1 intrinsicGaussianCoefficientConstant*gaussianMaximumMean A :=
      hcoef.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg.le)
    have hrate := exceptionalBudgetRate_le_coefficient (c := c)
      (zero_lt_one.trans_le (one_le_intrinsicBoundaryCoefficient μ ξ A hp)) hg (le_max_left _ _) hcoef'
      h.delta_nonneg (zero_lt_one.trans_le hL) hB
    have hcap := (min_le_min_left 1 hrate).trans
      (intrinsic_min_one_mul_le (by positivity : 0≤max 1 intrinsicGaussianCoefficientConstant) hr)
    rw [max_eq_right (le_max_left 1 intrinsicGaussianCoefficientConstant)] at hcap
    have hh := (exceptional_boundary_CLT_of_matrix_suppliers μ ξ h hp hunit A hA hc hc1 hC hmatrix).trans
      (mul_le_mul_of_nonneg_left hcap hK)
    apply hh.trans
    have hfin := mul_le_mul_of_nonneg_right (le_max_left
      (exceptionalBoundaryConstant C*max 1 intrinsicGaussianCoefficientConstant) (max 1 (Real.pi/2)))
      (le_min zero_le_one hr)
    convert hfin using 1 <;> ring
  · have hraw := exceptionalBudget_trivial_large_envelope hone hlow h.delta_nonneg hL hB hc hc1
      (lt_of_not_ge hsmall)
    have hcap := intrinsic_capped_of_le_one_and_mul hr hone hraw
    exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_min zero_le_one hr))

/-- The literal two-thirds-power form printed in Corollary 5. -/
theorem exceptional_CLT_printed_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c C : ℝ} (hc : 0<c) (hc1 : c≤1) (hC : 1≤C)
    (hmatrix : ∀ s : FaceSmoother p,s.faces=Finset.univ →
      exceptionalBandwidthConstant C*δ≤s.bandwidth → dimensionLog p*s.bandwidth^2<1/4 →
      ∀ t ∈ Ioo (0:ℝ) 1,
        ExceptionalNormalizedMatrixEstimates hp s μ ξ A C (intrinsicBoundaryCoefficient μ ξ A) t) :
    rectangleDistance μ (sumVector ξ) A≤exceptionalCoreConstant C*
      min 1 (δ*(gaussianMaximumMean A*dimensionLog p)*Real.sqrt (exceptionalCutoffLog c)+
        δ^((2:ℝ)/3)*(gaussianMaximumMean A*dimensionLog p)^((2:ℝ)/3)*
          (exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c)^((1:ℝ)/3)) := by
  have hdiag (j : Fin p) : (A*A.transpose) j j=1 := by rw [hA,hunit j]
  have hg : 0<gaussianMaximumMean A :=
    (by positivity : (0:ℝ)<Real.sqrt (2/Real.pi)).trans_le
      (sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag)
  have hL : 0<dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  simpa only [exceptionalBudgetRate_eq_printed h.delta_nonneg (mul_pos hg hL)
    (exceptionalCorrelationBudget_nonneg _ _)] using
      exceptional_CLT_of_matrix_suppliers μ ξ h hp hunit A hA hc hc1 hC hmatrix

end
end RectangleCLTArxivV1
