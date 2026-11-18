import RectangleCLTArxivV1.SupplementalHCubicRectangular
import RectangleCLTArxivV1.HFourthPhysicalMatrixTransport

/-! Actual geometric matrix estimates transported to the original
unconditional base. The factor normal is kept unscaled while sigma*A
appears in the Gaussian evaluation point. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actualMatrix_factorNormal_eq_selectorFaceNormal {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (f : Face p) :
    capRectangularFactorNormal A f=selectorFaceNormal A f := by
  ext j
  unfold capRectangularFactorNormal selectorFaceNormal
  split_ifs <;> rfl

theorem actualMatrix_physical_pushforward
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (B : Ω → Vector r) (hB : Measurable B) (V : Ω → Vector p)
    (hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω)) :
    μ.map V=(μ.map B).map (fun b => x+A.mulVec b) := by
  have hR : Measurable (fun b : Vector r => x+A.mulVec b) :=
    measurable_const.add (continuous_const.matrix_mulVec continuous_id).measurable
  rw [Measure.map_map hR hB]
  exact Measure.map_congr hrec

/-- The native actual cubic proposition supplies every restoration
length, under the original base concentration and a genuine physical
representation. No matrix bound is an input. -/
theorem actualMatrix_cubic_supplier_of_physical
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (hp : 1≤p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (B : Ω → Vector r) (hB : Measurable B) (V : Ω → Vector p)
    (hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω)) {C₀ δ κ σ C : ℝ}
    (hC₀ : 0<C₀) (hδ : 0≤δ) (hκ : 0<κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ)
    (hC : supplementalHCubicMatrixConstant C₀≤C) :
    ∀ ℓ : ℕ,(∫ ω,∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (σ•A)
        (capRectangularFactorNormal A) V γ ω) ∂μ)≤
      C^(ℓ+2)*(s.bandwidth*(κ*dimensionLog p*Real.sqrt (dimensionLog p))) := by
  letI : IsProbabilityMeasure (μ.map B) := isProbabilityMeasure_map hB.aemeasurable
  have hcB : IntrinsicRectangleConcentration ((μ.map B).map (fun b => x+A.mulVec b)) C₀ δ κ := by
    rwa [←actualMatrix_physical_pushforward μ A x B hB V hrec]
  intro ℓ
  have hraw := proposition_H1_cubic_matrix_shifted (K := ℓ) hp (μ.map B) s A x
    hC₀ hδ hκ hσ hunit hδh hcB hδσ
  have htransport := hFourth_cubic_matrix_sum_physical_transport (K := ℓ) μ s A (σ•A)
    (capRectangularFactorNormal A) x B hB V hrec
  rw [htransport]
  simp only [hFourthCubicGaussianScore_eq_selectorScore,actualMatrix_factorNormal_eq_selectorFaceNormal]
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hscale : 0≤s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p) := by
    have hh := s.bandwidth_pos
    positivity
  have hpw := pow_le_pow_left₀ (supplementalHCubicMatrixConstant_pos hC₀.le).le hC (ℓ+2)
  calc
    _≤supplementalHCubicMatrixConstant C₀^(ℓ+2)*s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p) := hraw
    _=supplementalHCubicMatrixConstant C₀^(ℓ+2)*
        (s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
    _≤C^(ℓ+2)*(s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_right hpw hscale
    _=_ := by ring

end
end RectangleCLTArxivV1
