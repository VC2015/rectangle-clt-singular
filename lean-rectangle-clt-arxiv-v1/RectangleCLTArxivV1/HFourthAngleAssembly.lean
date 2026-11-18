import RectangleCLTArxivV1.HFourthOriginalBound
import RectangleCLTArxivV1.HFourthPairIndexTransport
import RectangleCLTArxivV1.HFourthSeededModel

/-! Actual H.3 finite expectation from the cubic and full angle-weighted
matrix suppliers. The positive coordinate gap and support directions
discharge the pair restriction, including antipodal and repeated normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem hFourth_original_bound_of_angle_matrix_suppliers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j=1)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z Y W : Fin n → Ω → Vector r) (v : Fin n → Ω → Vector p)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hY : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ=standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z
        (fun i ω => A.mulVec (Y i ω)) (fun i ω => A.mulVec (W i ω)) v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    {δ σ R C Q c : ℝ} (hδ : 0 ≤ δ) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|(A*A.transpose) j k|)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖A.mulVec (Y i ω)‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖A.mulVec (W i ω)‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q)
    (hband : restorationBandwidthConstant C*R ≤ s.bandwidth)
    (hcubic : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (σ•A) (capRectangularFactorNormal A) V γ ω) ∂μ) ≤
        C^(ℓ+2)*(s.bandwidth*Q))
    (hpair : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+2) → Face p,
      correlationAngleWeight (faceDot (capRectangularFactorNormal A (γ 0)) (capRectangularFactorNormal A (γ 1)))*
        symmetricNuclearNorm (selectorGaussianScore s (σ•A) V γ ω) ∂μ) ≤
          C^(ℓ+3)*(s.bandwidth^2*Q/σ)) :
    (∀ i, Integrable (fun ω => restorationFourthDerivative s
      ((σ•A).mulVec (G ω)+V ω+v i ω) (A.mulVec (Z i ω)) (A.mulVec (Y i ω)) (A.mulVec (W i ω))) μ) ∧
    |∑ i, ∫ ω, restorationFourthDerivative s ((σ•A).mulVec (G ω)+V ω+v i ω)
      (A.mulVec (Z i ω)) (A.mulVec (Y i ω)) (A.mulVec (W i ω)) ∂μ| ≤
        78*C^3*δ^2*Q/(exceptionalCutoffDet c*σ^3) := by
  classical
  letI : MeasurableSpace Ω := mΩ
  let P := fun f g => c ≤ 1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|
  have hzero (i : Fin n) (f g : Face p) (hnot : ¬P f g) :
      ∀ᵐ ω ∂μ, capRectangularPairCoefficient A f g (A.mulVec (Y i ω)) (A.mulVec (W i ω))=0 := by
    have hpar := hFourth_gap_or_parallel A hdiag hgap f g hnot
    exact ae_of_all _ (fun ω => by
      rw [capRectangularPairCoefficient_factor]
      exact capPairCoefficient_parallel_zero _ _ _ _ (capRectangularFactorNormal_unit A hdiag f)
        (capRectangularFactorNormal_unit A hdiag g) hpar)
  have hpa := hFourth_pair_supplier_of_angle_weighted_front μ s (σ•A) (capRectangularFactorNormal A)
    V (hV.mono hH le_rfl) hc hc1 hpair
  have hp (ℓ : ℕ) : (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s (σ•A) V γ ω) else 0 ∂μ) ≤
        C^(ℓ+3)*(s.bandwidth^2*Q/(exceptionalCutoffDet c*σ)) := by
    exact (hpa ℓ).trans_eq (by ring)
  exact hFourth_original_expectation_bound_of_matrix_suppliers (mΩ := mΩ) s μ H hH A hdiag V hV
    Z hZm hZ (fun i ω => A.mulVec (Y i ω)) (fun i ω => A.mulVec (W i ω)) v
    (fun i => (continuous_const.matrix_mulVec continuous_id).measurable.comp (hY i))
    (fun i => (continuous_const.matrix_mulVec continuous_id).measurable.comp (hW i)) hv G hG hGlaw hHG hCI
    P hzero hδ hσ hR hYb hWb hvb hbudget hC hQ (exceptionalCutoffDet_bounds hc hc1).1
    (exceptionalCutoffDet_bounds hc hc1).2.2 hband hcubic hp

end
end RectangleCLTArxivV1
