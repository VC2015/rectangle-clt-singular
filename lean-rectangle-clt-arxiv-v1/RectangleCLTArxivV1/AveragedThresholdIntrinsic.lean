import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SplitV4.AveragedThresholdBound

/-! Lemma B.5 with the actual intrinsic concentrated-base coefficient. -/
namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4

set_option autoImplicit false

theorem intrinsic_concentratedThresholdBase_rescale {m r : ℕ}
    (μ : Measure (Vector r)) (u : Fin m → Vector r) {C₀ δ κ L : ℝ}
    (hL : 0 < L) (hc : IntrinsicPolyhedralConcentration μ u C₀ δ κ) :
    ConcentratedThresholdBase μ u (C₀ * κ / Real.sqrt L) δ L := by
  have hroot : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  intro a s hs
  have hh := hc a s hs
  change μ.real (gaussianPolyhedronLayer u a s) ≤ _
  convert hh using 1
  field_simp [hroot]

/-- The actual averaged common-threshold derivative. All dimension and
Gaussian-scale parameters retain their original meanings under rescaling. -/
theorem lemma_B5_intrinsic_threshold {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C₀ δ κ L σ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hδ : 0 ≤ δ) (hσ : 0 < σ) (hL : dimensionLog m ≤ 2 * L)
    (hc : IntrinsicPolyhedralConcentration μ u C₀ δ κ) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      averagedThresholdPaperConstant * C₀ * κ * (σ * L + δ * L * Real.sqrt L) := by
  have hLm : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hLp : 0 < L := by linarith
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hb := averagedGaussianThresholdDerivative_bound_of_log_le_two hm μ u a hu hi
    (div_nonneg (mul_nonneg hC₀ hκ) hroot.le) hδ hσ hL
    (intrinsic_concentratedThresholdBase_rescale μ u hLp hc)
  convert hb using 1
  field_simp [hroot.ne']
  ring_nf
  rw [Real.sq_sqrt hLp.le]
  ring

end RectangleCLTArxivV1
