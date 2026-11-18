import RectangleCLTArxivV1.ActualSeededMatrixBase
import RectangleCLTArxivV1.ActualPairMatrixTransport
import RectangleCLTArxivV1.ExceptionalMatrixSuppliers
import RectangleCLTArxivV1.GapSeededComparison

/-! Both actual geometric matrix propositions on the genuine normalized
half-base. Every support, concentration, scaling and length obligation is
discharged before any remainder or rectangle comparison is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_normalized_matrix_estimates
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) {C₀ κ t : ℝ} (hC₀ : 0<C₀) (hκ : 0<κ)
    (hband : 2*δ≤s.bandwidth) (hsmall : dimensionLog p*s.bandwidth^2≤1/4)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    ExceptionalNormalizedMatrixEstimates hp s μ ξ A (actualMatrixConstant C₀) κ t := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  change ExceptionalSeededAngleMatrixEstimates f μ ξ A 0 ε t (actualMatrixConstant C₀)
    (κ*dimensionLog p*Real.sqrt (dimensionLog p))
  refine ⟨actual_normalized_cubic_supplier h hp hunit A hA s hC₀ hκ hband hsmall ht hc
    (actualMatrixConstant_ge_cubic C₀),?_⟩
  have hδ := h.delta_nonneg
  have hscale := hFourth_normalized_seed_scale_range hp s hδ hband ht hsmall
  have hrows (j : Fin p) : vectorNormSq (A j)=1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,vectorNormSq,pow_two] using
      (show (A*A.transpose) j j=1 by rw [hA,hunit j])
  have hδh : δ≤f.bandwidth :=
    (by linarith : δ≤s.bandwidth).trans (seededRescaledSmoother_bandwidth_ge s hε)
  exact actualMatrix_pair_supplier_of_physical hp
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)) f A 0
    (hFourthPhysicalSeededBase A ε t) (hFourthPhysicalSeededBase_continuous A ε t).measurable
    (capSeededBaseValue A 0 ε t) (hFourth_seeded_base_eq_physical h A hA 0 ε ht)
    hC₀.le hδ hκ.le hscale.1 hrows hδh
    (by simpa only [actual_seededSplitBase_map_eq] using hc) hscale.2.1
    (actualMatrixConstant_ge_pair C₀)

/-- Restriction of the proved full-angle estimate to a cutoff changes
only the first two labels and leaves every original smoother factor. -/
theorem actual_normalized_gap_matrix_estimates
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) {C₀ κ t c : ℝ} (hC₀ : 0<C₀) (hκ : 0<κ)
    (hband : 2*δ≤s.bandwidth) (hsmall : dimensionLog p*s.bandwidth^2≤1/4)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hc : 0<c) (hc1 : c≤1)
    (hconcentration : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    GapNormalizedMatrixEstimates hp s μ ξ A c (actualMatrixConstant C₀) κ t := by
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  exact exceptional_seeded_matrix_estimates_of_angle h (seededRescaledSmoother s ε hε) A 0 ht hc hc1
    (actual_normalized_matrix_estimates h hp hunit A hA s hC₀ hκ hband hsmall ht hconcentration)

end
end RectangleCLTArxivV1
