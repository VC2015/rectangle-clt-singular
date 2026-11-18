import RectangleCLTArxivV1.GapSeededComparison
import RectangleCLTArxivV1.GapOptimization
import RectangleCLTArxivV1.IntrinsicMain

/-! Corollary 4 assembly with its only open geometric obligation stated
as uniform, actual cubic/pair matrix sums. These intermediate theorems do
not claim that the H geometric suppliers have already been proved. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def positiveGapSmoothComparisonConstant (C₀ C : ℝ) : ℝ :=
  directInitializationConstant+2*positiveGapComparisonConstant C₀ C

theorem positiveGapSmoothComparisonConstant_pos {C₀ C : ℝ} (hC₀ : 0 < C₀) :
    0 < positiveGapSmoothComparisonConstant C₀ C :=
  add_pos directInitializationConstant_pos (mul_pos (by norm_num) (positiveGapComparisonConstant_pos hC₀))

theorem positiveGap_smooth_comparison_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces=Finset.univ)
    (hband : relativeDerivativeBandwidth*δ ≤ s.bandwidth)
    {c C C₀ κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hgapband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (henv : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z)*
        (1-s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
          derivativeEnvelopeSignedAverageConstant*s.bandwidth*κ)
    (hconcentration : ∀ t ∈ Ioo (0:ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ∀ t ∈ Ioo (0:ℝ) 1, GapNormalizedMatrixEstimates hp s μ ξ A c C κ t) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      positiveGapSmoothComparisonConstant C₀ C*(κ*dimensionLog p)*
        (δ+δ^2*positiveGapGain c/s.bandwidth) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hε : 0 < ε := mul_pos (zero_lt_one.trans_le hL) (sq_pos_of_pos s.bandwidth_pos)
  have hJ : 1 ≤ positiveGapGain c := one_le_positiveGapGain hc hc1
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hi := direct_initialization_intrinsic_of_envelope μ ξ h (relativeMomentBounds_of_envelope h)
    hunit A hA s hfaces hb.1 (zero_le_one.trans hκ) henv
  have hs := positiveGap_normalized_time_comparison_of_matrix_suppliers μ ξ h (h.delta_pos hp hunit)
    hp hunit A hA s hb.2 hc hc1 hgap hC hC₀ (zero_lt_one.trans_le hκ) hgapband hconcentration hmatrix
  have ht := smoother_gap_le_actual_two_stage_gaps s μ ξ h.measurable A hε.le
  have hh := ht.trans (add_le_add hi hs)
  change _ ≤ directInitializationConstant*δ*(L*κ)+directInitializationConstant*δ^2*(L*κ)/s.bandwidth+
    (2*positiveGapComparisonConstant C₀ C)*(κ*L)*(δ+δ^2*positiveGapGain c/s.bandwidth) at hh
  apply hh.trans
  have hn : 0 ≤ directInitializationConstant*(κ*L)*(δ^2/s.bandwidth) := by
    exact mul_nonneg (mul_nonneg directInitializationConstant_pos.le
      (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL)))
      (div_nonneg (sq_nonneg δ) s.bandwidth_pos.le)
  have hj := mul_le_mul_of_nonneg_left hJ hn
  unfold positiveGapSmoothComparisonConstant
  ring_nf at hj ⊢
  nlinarith only [hj]

def positiveGapBandwidthConstant (C : ℝ) : ℝ :=
  max 1 (max relativeDerivativeBandwidth (4*restorationBandwidthConstant C))

theorem positiveGapBandwidthConstant_ge_one (C : ℝ) : 1 ≤ positiveGapBandwidthConstant C := le_max_left _ _

def positiveGapBoundaryConstant (C : ℝ) : ℝ :=
  intrinsicOptimizationConstant (positiveGapBandwidthConstant C)
    (positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C+9*intrinsicBoundaryConstant)

theorem positiveGapBoundaryConstant_ge_one (C : ℝ) : 1 ≤ positiveGapBoundaryConstant C := by
  have hA := positiveGapBandwidthConstant_ge_one C
  have hC := positiveGapSmoothComparisonConstant_pos (C := C) intrinsicBoundaryConstant_pos
  have hB := intrinsicBoundaryConstant_pos
  unfold positiveGapBoundaryConstant intrinsicOptimizationConstant
  nlinarith [mul_nonneg (show 0 ≤ positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C+
    9*intrinsicBoundaryConstant by linarith) (show 0 ≤ positiveGapBandwidthConstant C+3 by linarith)]

/-- Only actual matrix estimates are supplied here; the concentration,
initialization, smoothing, covariance, scalar integration and bandwidth
optimization are all constructed from the bounded original array. -/
theorem positiveGap_boundary_CLT_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|) (hC : 1 ≤ C)
    (hmatrix : ∀ s : FaceSmoother p, s.faces=Finset.univ →
      positiveGapBandwidthConstant C*δ ≤ s.bandwidth → dimensionLog p*s.bandwidth^2<1/4 →
      ∀ t ∈ Ioo (0:ℝ) 1,
        GapNormalizedMatrixEstimates hp s μ ξ A c C (intrinsicBoundaryCoefficient μ ξ A) t) :
    rectangleDistance μ (sumVector ξ) A ≤ positiveGapBoundaryConstant C*
      min 1 (positiveGapRate (intrinsicBoundaryCoefficient μ ξ A) δ (dimensionLog p) c) := by
  letI : NeZero p := ⟨by omega⟩
  let L := dimensionLog p
  let κ := intrinsicBoundaryCoefficient μ ξ A
  let b := positiveGapBandwidth (positiveGapBandwidthConstant C) δ c
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hδ : 0 < δ := h.delta_pos hp hunit
  have hκ : 1 ≤ κ := one_le_intrinsicBoundaryCoefficient μ ξ A hp
  have hBW := positiveGapBandwidthConstant_ge_one C
  have hbpos : 0 < b := positiveGapBandwidth_pos (zero_lt_one.trans_le hBW) hδ hc hc1
  have hb : positiveGapBandwidthConstant C*δ ≤ b :=
    positiveGapBandwidth_admissible (zero_le_one.trans hBW) hδ.le hc hc1
  have hrelative : relativeDerivativeBandwidth ≤ positiveGapBandwidthConstant C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hrest : 4*restorationBandwidthConstant C ≤ positiveGapBandwidthConstant C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hband : relativeDerivativeBandwidth*δ ≤ b :=
    (mul_le_mul_of_nonneg_right hrelative hδ.le).trans hb
  have hgapband : restorationBandwidthConstant C*(4*δ) ≤ b := by
    have hh := (mul_le_mul_of_nonneg_right hrest hδ.le).trans hb
    convert hh using 1 <;> ring
  have hδb : δ ≤ b := (le_mul_of_one_le_left hδ.le hBW).trans hb
  have hK : 0 ≤ positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C+9*intrinsicBoundaryConstant := by
    linarith [positiveGapSmoothComparisonConstant_pos (C := C) intrinsicBoundaryConstant_pos,intrinsicBoundaryConstant_pos]
  apply positiveGap_rate_of_small_bandwidth_estimate hBW hK hκ hδ hL hc hc1
    (rectangleDistance_le_one μ (sumVector ξ) A)
  intro hsmall
  have hsmooth : smoothingDiscrepancy μ (sumVector ξ) A b hbpos ≤
      positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C*(κ*L)*
        (δ+δ^2*positiveGapGain c/b) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) h.measurable_sum A b hbpos _).mpr
    intro lo hi
    let s := FaceSmoother.closedBox lo hi b hbpos
    have hband4 : 4*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right relativeDerivativeBandwidth_ge_four hδ.le).trans hband
    exact positiveGap_smooth_comparison_of_matrix_suppliers μ ξ h hp hunit A hA s rfl hband
      hc hc1 hgap hC intrinsicBoundaryConstant_pos hκ hgapband
      (fun v hv0 hv1 => integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA s rfl hband4 hv0 hv1)
      (fun t ht => intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
        (by positivity) ht.1.le ht.2.le)
      (hmatrix s rfl hb hsmall)
  have hrho := (rectangleDistance_le_smoothingDiscrepancy_intrinsic hp μ (sumVector ξ)
    h.measurable_sum A intrinsicBoundaryConstant_pos.le hδ.le (zero_le_one.trans hκ) hbpos hδb
    (intrinsicRectangleConcentration_bounded_endpoint h hp hunit A)
    (intrinsicRectangleConcentration_gaussian_endpoint μ ξ hp A (fun j => by rw [hA,hunit j]))).trans
      (add_le_add_right hsmooth _)
  let F := δ+δ^2*positiveGapGain c/b
  have hF : 0 ≤ F := by
    have hJ := one_le_positiveGapGain hc hc1
    dsimp only [F]
    positivity
  have hx := mul_nonneg (mul_nonneg (positiveGapSmoothComparisonConstant_pos (C := C) intrinsicBoundaryConstant_pos).le
    (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL))) hbpos.le
  have hy := mul_nonneg (mul_nonneg (show 0 ≤ 9*intrinsicBoundaryConstant from
    mul_nonneg (by norm_num) intrinsicBoundaryConstant_pos.le)
    (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL))) hF
  change rectangleDistance μ (sumVector ξ) A ≤
    (positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C+9*intrinsicBoundaryConstant)*κ*L*
      (b+δ+δ^2*positiveGapGain c/b)
  apply hrho.trans
  change positiveGapSmoothComparisonConstant intrinsicBoundaryConstant C*(κ*L)*F+9*intrinsicBoundaryConstant*b*κ*L ≤ _
  dsimp only [F] at hy ⊢
  ring_nf at hx hy ⊢
  nlinarith only [hx,hy]

def positiveGapCoreConstant (C : ℝ) : ℝ :=
  max (positiveGapBoundaryConstant C*max 1 intrinsicGaussianCoefficientConstant) (max 1 (Real.pi/2))

theorem positiveGapCoreConstant_ge_one (C : ℝ) : 1 ≤ positiveGapCoreConstant C :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem positiveGap_CLT_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|) (hC : 1 ≤ C)
    (hmatrix : ∀ s : FaceSmoother p, s.faces=Finset.univ →
      positiveGapBandwidthConstant C*δ ≤ s.bandwidth → dimensionLog p*s.bandwidth^2<1/4 →
      ∀ t ∈ Ioo (0:ℝ) 1,
        GapNormalizedMatrixEstimates hp s μ ξ A c C (intrinsicBoundaryCoefficient μ ξ A) t) :
    rectangleDistance μ (sumVector ξ) A ≤ positiveGapCoreConstant C*
      min 1 (positiveGapRate (gaussianMaximumMean A) δ (dimensionLog p) c) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hg := gaussianMaximumMean_nonneg A
  have hr : 0 ≤ positiveGapRate (gaussianMaximumMean A) δ (dimensionLog p) c := by
    unfold positiveGapRate
    exact mul_nonneg (mul_nonneg (mul_nonneg h.delta_nonneg hg) (zero_le_one.trans hL)) (Real.sqrt_nonneg _)
  have hone := rectangleDistance_le_one μ (sumVector ξ) A
  have hK : 0 ≤ positiveGapBoundaryConstant C := zero_le_one.trans (positiveGapBoundaryConstant_ge_one C)
  by_cases hsmall : δ*dimensionLog p ≤ gaussianMaximumMean A
  · have hcoef := intrinsicBoundaryCoefficient_le_gaussian h hp hunit A hA hsmall
    have hrate := positiveGapRate_le_coefficient (c := c) hcoef h.delta_nonneg (zero_le_one.trans hL)
    have hcap := (min_le_min_left 1 hrate).trans
      (intrinsic_min_one_mul_le intrinsicGaussianCoefficientConstant_pos.le hr)
    have hh := (positiveGap_boundary_CLT_of_matrix_suppliers μ ξ h hp hunit A hA hc hc1 hgap hC hmatrix).trans
      (mul_le_mul_of_nonneg_left hcap hK)
    apply hh.trans
    have hfin := mul_le_mul_of_nonneg_right
      (le_max_left (positiveGapBoundaryConstant C*max 1 intrinsicGaussianCoefficientConstant) (max 1 (Real.pi/2)))
      (le_min zero_le_one hr)
    convert hfin using 1
    ring
  · have hdiag (j : Fin p) : (A*A.transpose) j j=1 := by rw [hA,hunit j]
    have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
    have hraw := positiveGap_trivial_large_envelope hone hlow h.delta_nonneg hL hc hc1 (lt_of_not_ge hsmall)
    have hcap := intrinsic_capped_of_le_one_and_mul hr hone hraw
    exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_min zero_le_one hr))

end
end RectangleCLTArxivV1
