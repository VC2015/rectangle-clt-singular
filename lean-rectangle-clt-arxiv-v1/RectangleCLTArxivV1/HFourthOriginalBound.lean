import RectangleCLTArxivV1.HFourthFromSuppliers
import RectangleCLTCompanion.SplitV4.RestorationConditionalTransport

/-! Actual finite expectation on the original conditional-independence
model in H.3. Matrix estimates remain explicit upstream suppliers. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem hFourth_original_expectation_bound_of_matrix_suppliers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j=1)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (Y W v : Fin n → Ω → Vector p)
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ=standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    (P : Face p → Face p → Prop) [DecidableRel P]
    (hzero : ∀ i f g, ¬P f g → ∀ᵐ ω ∂μ, capRectangularPairCoefficient A f g (Y i ω) (W i ω)=0)
    {δ σ R C Q d : ℝ} (hδ : 0 ≤ δ) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q) (hd : 0 < d) (hd1 : d ≤ 1)
    (hband : restorationBandwidthConstant C*R ≤ s.bandwidth)
    (hcubic : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (σ•A) (capRectangularFactorNormal A) V γ ω) ∂μ) ≤
        C^(ℓ+2)*(s.bandwidth*Q))
    (hpair : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s (σ•A) V γ ω) else 0 ∂μ) ≤
        C^(ℓ+3)*(s.bandwidth^2*Q/(d*σ))) :
    (∀ i, Integrable (fun ω => restorationFourthDerivative s
      ((σ•A).mulVec (G ω)+V ω+v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)) μ) ∧
    |∑ i, ∫ ω, restorationFourthDerivative s ((σ•A).mulVec (G ω)+V ω+v i ω)
      (A.mulVec (Z i ω)) (Y i ω) (W i ω) ∂μ| ≤ 78*C^3*δ^2*Q/(d*σ^3) := by
  have he := restorationFourthExpectation_conditional_transport (mΩ := mΩ) (σ := σ) s μ H hH A V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hYb hWb
  refine ⟨he.1, ?_⟩
  rw [he.2]
  exact hFourth_expectation_bound_of_matrix_suppliers (mΩ := mΩ) s μ H hH A hdiag V hV Z hZm hZ
    Y W v hY hW hv P hzero hδ hσ hR hYb hWb hvb hbudget hC hQ hd hd1 hband hcubic hpair

end
end RectangleCLTArxivV1
