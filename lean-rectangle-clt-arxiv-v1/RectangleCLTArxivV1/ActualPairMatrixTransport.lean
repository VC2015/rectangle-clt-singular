import RectangleCLTArxivV1.ActualMatrixTransport
import RectangleCLTArxivV1.ActualMatrixConstant
import RectangleCLTArxivV1.SupplementalHPairRectangular

/-! The complete actual angle-weighted pair proposition on the original
base, transported through its physical representation. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actualMatrix_pair_supplier_of_physical
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (hp : 1≤p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (B : Ω → Vector r) (hB : Measurable B) (V : Ω → Vector p)
    (hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω)) {C₀ δ κ σ C : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ)
    (hC : supplementalHPairPhysicalMatrixConstant C₀≤C) :
    ∀ ℓ : ℕ,(∫ ω,∑ γ : Fin (ℓ+2) → Face p,
      correlationAngleWeight (faceDot (capRectangularFactorNormal A (γ 0))
        (capRectangularFactorNormal A (γ 1)))*
        symmetricNuclearNorm (selectorGaussianScore s (σ•A) V γ ω) ∂μ)≤
      C^(ℓ+3)*(s.bandwidth^2*(κ*dimensionLog p*Real.sqrt (dimensionLog p))/σ) := by
  letI : IsProbabilityMeasure (μ.map B) := isProbabilityMeasure_map hB.aemeasurable
  have hcB : IntrinsicRectangleConcentration ((μ.map B).map (fun b => x+A.mulVec b)) C₀ δ κ := by
    rwa [←actualMatrix_physical_pushforward μ A x B hB V hrec]
  intro ℓ
  have hraw := proposition_H2_pair_matrix_shifted (K := ℓ) hp (μ.map B) s A x
    hC₀ hδ hκ hσ hunit hδh hcB hδσ
  rw [hFourth_pair_matrix_sum_physical_transport μ s A (σ•A) x B hB V hrec
    (fun γ : Fin (ℓ+2) → Face p => correlationAngleWeight
      (faceDot (capRectangularFactorNormal A (γ 0)) (capRectangularFactorNormal A (γ 1))))]
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hscale : 0≤s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p) := by positivity
  have hpw := pow_le_pow_left₀
    ((by norm_num : (0:ℝ)≤4).trans (supplementalHPairPhysicalMatrixConstant_ge_four hC₀)) hC (ℓ+3)
  calc
    _≤supplementalHPairPhysicalMatrixConstant C₀^(ℓ+3)*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
      simpa only [actualMatrix_factorNormal_eq_selectorFaceNormal,supplementalHPairTupleAngle] using hraw
    _=supplementalHPairPhysicalMatrixConstant C₀^(ℓ+3)*
        (s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
    _≤C^(ℓ+3)*(s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_right hpw hscale
    _=_ := by ring

end
end RectangleCLTArxivV1
