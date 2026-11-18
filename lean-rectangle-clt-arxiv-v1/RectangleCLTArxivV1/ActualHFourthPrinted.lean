import RectangleCLTArxivV1.ActualHFourth

/-! The fixed-b bandwidth quantifier in the printed statement of Lemma H.3.
The numerical width constant is chosen before all dimensions and random data. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The bandwidth constant for shifts of size at most bδ. -/
def theoremH3BandwidthConstant (C₀ b : ℝ) : ℝ :=
  max 1 (b*restorationBandwidthConstant (actualMatrixConstant C₀))

theorem theoremH3BandwidthConstant_ge_one (C₀ b : ℝ) :
    1≤theoremH3BandwidthConstant C₀ b := le_max_left _ _

theorem theoremH3BandwidthConstant_pos (C₀ b : ℝ) :
    0<theoremH3BandwidthConstant C₀ b :=
  zero_lt_one.trans_le (theoremH3BandwidthConstant_ge_one C₀ b)

/-- One printed width hypothesis supplies both widths in the general-radius
theorem. This argument has no random or dimension-dependent input. -/
theorem theoremH3BandwidthConstant_controls_width
    {C₀ b δ h : ℝ} (hb : 0≤b) (hδ : 0≤δ)
    (hband : theoremH3BandwidthConstant C₀ b*δ≤h) :
    0≤b*δ ∧ δ≤h ∧
      restorationBandwidthConstant (actualMatrixConstant C₀)*(b*δ)≤h := by
  have hδh : δ≤h := by
    calc
      δ=1*δ := by ring
      _≤theoremH3BandwidthConstant C₀ b*δ :=
        mul_le_mul_of_nonneg_right (theoremH3BandwidthConstant_ge_one C₀ b) hδ
      _≤h := hband
  have hRh : restorationBandwidthConstant (actualMatrixConstant C₀)*(b*δ)≤h := by
    calc
      restorationBandwidthConstant (actualMatrixConstant C₀)*(b*δ)=
          (b*restorationBandwidthConstant (actualMatrixConstant C₀))*δ := by ring
      _≤theoremH3BandwidthConstant C₀ b*δ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
      _≤h := hband
  exact ⟨mul_nonneg hb hδ,hδh,hRh⟩

/-- Lemma H.3 with its printed fixed-b shift condition. Both numerical
constants depend only on C₀ and b, before the conditional Gaussian model is
chosen. The actual cubic and pair estimates are discharged internally. -/
theorem lemma_H3_fourth_derivative
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
    {δ σ b C₀ κ c : ℝ} (hδ : 0≤δ) (hσ : 0<σ) (hb : 0≤b)
    (hC₀ : 0<C₀) (hκ : 0<κ) (hc : 0<c) (hc1 : c≤1)
    (hgap : ∀ j k : Fin p,j≠k → c≤1-|(A*A.transpose) j k|)
    (hYb : ∀ i,∀ᵐ ω ∂μ,‖A.mulVec (Y i ω)‖≤δ)
    (hWb : ∀ i,∀ᵐ ω ∂μ,‖A.mulVec (W i ω)‖≤δ)
    (hvb : ∀ i,∀ᵐ ω ∂μ,‖v i ω‖≤b*δ)
    (hbudget : ∀ᵐ ω ∂μ,∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u≤vectorNormSq u)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ)
    (hband : theoremH3BandwidthConstant C₀ b*δ≤s.bandwidth)
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
  obtain ⟨hR,hδh,hRh⟩ := theoremH3BandwidthConstant_controls_width hb hδ hband
  exact theorem_H3_fourth_derivative (mΩ := mΩ) hp s μ H hH A hunit x B hB
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hσ hR
    hC₀ hκ hc hc1 hgap hYb hWb hvb hbudget hδh hδσ hRh hconcentration

end
end RectangleCLTArxivV1
