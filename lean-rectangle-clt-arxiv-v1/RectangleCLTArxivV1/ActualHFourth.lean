import RectangleCLTArxivV1.ActualPairMatrixTransport
import RectangleCLTArxivV1.HFourthAngleAssembly

/-! The actual finite expectation form of Appendix H's fourth-derivative
theorem. The native cubic and pair matrix propositions are fully consumed;
the remaining assumptions are the original conditional Gaussian model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def theoremH3Constant (C₀ : ℝ) : ℝ := 78*(actualMatrixConstant C₀)^3

theorem theoremH3Constant_pos (C₀ : ℝ) : 0<theoremH3Constant C₀ := by
  have hC := actualMatrixConstant_ge_one C₀
  unfold theoremH3Constant
  positivity

/-- Theorem H.3 on the actual conditional-independence model. B is the
physical base on Gaussian support, with original face-coordinate point
x+A B. All matrix estimates are proved from its actual concentration law. -/
theorem theorem_H3_fourth_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1≤p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H≤mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j,vectorNormSq (A j)=1)
    (x : Vector p) (B : Ω → Vector r) (hB : @Measurable Ω (Vector r) H inferInstance B)
    (Z Y W : Fin n → Ω → Vector r) (v : Fin n → Ω → Vector p)
    (hZm : ∀ i,@Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k,Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hY : ∀ i,@Measurable Ω (Vector r) mΩ inferInstance (Y i))
    (hW : ∀ i,@Measurable Ω (Vector r) mΩ inferInstance (W i))
    (hv : ∀ i,@Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ=standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z
        (fun i ω => A.mulVec (Y i ω)) (fun i ω => A.mulVec (W i ω)) v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    {δ σ R C₀ κ c : ℝ} (hδ : 0≤δ) (hσ : 0<σ) (hR : 0≤R)
    (hC₀ : 0<C₀) (hκ : 0<κ) (hc : 0<c) (hc1 : c≤1)
    (hgap : ∀ j k : Fin p,j≠k → c≤1-|(A*A.transpose) j k|)
    (hYb : ∀ i,∀ᵐ ω ∂μ,‖A.mulVec (Y i ω)‖≤δ)
    (hWb : ∀ i,∀ᵐ ω ∂μ,‖A.mulVec (W i ω)‖≤δ)
    (hvb : ∀ i,∀ᵐ ω ∂μ,‖v i ω‖≤R)
    (hbudget : ∀ᵐ ω ∂μ,∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u≤vectorNormSq u)
    (hδh : δ≤s.bandwidth) (hδσ : δ*Real.sqrt (dimensionLog p)≤σ)
    (hband : restorationBandwidthConstant (actualMatrixConstant C₀)*R≤s.bandwidth)
    (hconcentration : IntrinsicRectangleConcentration
      (@Measure.map Ω (Vector p) mΩ inferInstance (fun ω => x+A.mulVec (B ω)) μ) C₀ δ κ) :
    (∀ i,Integrable (fun ω => restorationFourthDerivative s
      ((σ•A).mulVec (G ω)+(x+A.mulVec (B ω))+v i ω)
      (A.mulVec (Z i ω)) (A.mulVec (Y i ω)) (A.mulVec (W i ω))) μ) ∧
    |∑ i,∫ ω,restorationFourthDerivative s ((σ•A).mulVec (G ω)+(x+A.mulVec (B ω))+v i ω)
      (A.mulVec (Z i ω)) (A.mulVec (Y i ω)) (A.mulVec (W i ω)) ∂μ|≤
      theoremH3Constant C₀*δ^2*(κ*dimensionLog p*Real.sqrt (dimensionLog p))/
        (exceptionalCutoffDet c*σ^3) := by
  letI : MeasurableSpace Ω := mΩ
  let V := fun ω => x+A.mulVec (B ω)
  have hBm : Measurable B := hB.mono hH le_rfl
  have hV : @Measurable Ω (Vector p) H inferInstance V :=
    measurable_const.add ((continuous_const.matrix_mulVec continuous_id).measurable.comp hB)
  have hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω) := ae_of_all _ (fun _ => rfl)
  have hdiag (j : Fin p) : (A*A.transpose) j j=1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,vectorNormSq,pow_two] using hunit j
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hQ : 0≤κ*dimensionLog p*Real.sqrt (dimensionLog p) := by positivity
  have hcub := actualMatrix_cubic_supplier_of_physical hp μ s A x B hBm V hrec
    hC₀ hδ hκ hσ hunit hδh hconcentration hδσ (actualMatrixConstant_ge_cubic C₀)
  have hpair := actualMatrix_pair_supplier_of_physical hp μ s A x B hBm V hrec
    hC₀.le hδ hκ.le hσ hunit hδh hconcentration hδσ (actualMatrixConstant_ge_pair C₀)
  have hb := hFourth_original_bound_of_angle_matrix_suppliers (mΩ := mΩ) s μ H hH A hdiag V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hσ hR hc hc1 hgap hYb hWb hvb hbudget
    (actualMatrixConstant_ge_one C₀) hQ hband hcub hpair
  exact ⟨hb.1,hb.2.trans_eq (by unfold theoremH3Constant;ring)⟩

end
end RectangleCLTArxivV1
