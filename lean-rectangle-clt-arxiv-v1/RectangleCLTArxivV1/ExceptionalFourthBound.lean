import RectangleCLTArxivV1.HFourthFromSuppliers

/-! The actual single-H3 and first-pair-cutoff H2 product expectation.
Only the first two pair labels are restricted; later restoration labels
remain free. No global correlation-gap hypothesis is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def exceptionalFourthCutoffExpectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (Z : Fin n → Ω → Vector r)
    (Y W v : Fin n → Ω → Vector p) (σ : ℝ)
    (P : Face p → Face p → Prop) [DecidableRel P] : ℝ :=
  -(1/(s.bandwidth*σ^3))*(∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
    ((normalDot f (Y i z.1)*normalDot f (W i z.1))*
      capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r))+
  (1/(s.bandwidth^2*σ^2))*(∫ z : Ω × Vector r, ∑ i, ∑ α : Fin 2 → Face p,
    ((if P (α 0) (α 1) then capRectangularPairCoefficient A (α 0) (α 1) (Y i z.1) (W i z.1) else 0)*
      repeatedDirectionScore z.2 (Z i z.1))*
        selectorTupleWeight s α ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r))

theorem exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers
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
    (P : Face p → Face p → Prop) [DecidableRel P]
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
    |exceptionalFourthCutoffExpectation (mΩ := mΩ) s μ A V Z Y W v σ P| ≤
      78*C^3*δ^2*Q/(d*σ^3) := by
  letI : MeasurableSpace Ω := mΩ
  have hh := s.bandwidth_pos
  let c := fun i f ω => normalDot f (Y i ω)*normalDot f (W i ω)
  let B := fun i (α : Fin 2 → Face p) ω =>
    if P (α 0) (α 1) then capRectangularPairCoefficient A (α 0) (α 1) (Y i ω) (W i ω) else 0
  have hcm (i : Fin n) (f : Face p) : Measurable (c i f) :=
    ((continuous_normalDot f).measurable.comp (hY i)).mul ((continuous_normalDot f).measurable.comp (hW i))
  have hcb (i : Fin n) (f : Face p) : ∀ᵐ ω ∂μ, |c i f ω| ≤ δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    rw [abs_mul]
    exact (mul_le_mul (abs_normalDot_le_of_norm_le f hy) (abs_normalDot_le_of_norm_le f hw)
      (abs_nonneg _) hδ).trans_eq (by ring)
  have hBm (i : Fin n) (α : Fin 2 → Face p) : Measurable (B i α) := by
    unfold B
    split_ifs
    · unfold capRectangularPairCoefficient normalDot
      split <;> split <;> fun_prop
    · exact measurable_const
  have hBb (i : Fin n) (α : Fin 2 → Face p) : ∀ᵐ ω ∂μ, |B i α ω| ≤ 4*δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    dsimp only [B]
    split_ifs
    · exact cap_original_pair_coefficient_abs_le A hdiag _ _ _ _ hδ hy hw
    · simp only [abs_zero]; positivity
  have hs := hFourth_conditional_translated_cubic_bound_numeric (mΩ := mΩ) s μ H hH (σ•A)
    (capRectangularFactorNormal A) V hV Z hZm hZ c hcm v hv (sq_nonneg δ) hR hcb hvb hbudget
    hC (mul_nonneg s.bandwidth_pos.le hQ) hband hcubic
  have hp := hFourth_conditional_translated_pair_bound_numeric (mΩ := mΩ) s μ H hH (σ•A) V hV
    Z hZm hZ B hBm v hv P (fun i α hnot => ae_of_all _ (fun _ => by simp only [B,if_neg hnot]))
    (by positivity : 0 ≤ 4*δ^2) hR hBb hvb hbudget hC (by positivity : 0 ≤ s.bandwidth^2*Q/(d*σ)) hband hpair
  let S := ∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
    (c i f z.1*capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1) z.2)*
      selectorTupleWeight s ![f] ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)
  let T := ∫ z : Ω × Vector r, ∑ i, ∑ α : Fin 2 → Face p,
    (B i α z.1*repeatedDirectionScore z.2 (Z i z.1))*
      selectorTupleWeight s α ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)
  change |-(1/(s.bandwidth*σ^3))*S+(1/(s.bandwidth^2*σ^2))*T| ≤ _
  have hCpow : C^2 ≤ C^3 := by nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
  have hCd : C^2*d ≤ C^3 := (mul_le_of_le_one_right (sq_nonneg C) hd1).trans hCpow
  calc
    _ ≤ (1/(s.bandwidth*σ^3))*|S|+(1/(s.bandwidth^2*σ^2))*|T| := by
      have ht := abs_add (-(1/(s.bandwidth*σ^3))*S) ((1/(s.bandwidth^2*σ^2))*T)
      rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(s.bandwidth*σ^3)),
        abs_of_nonneg (by positivity : 0 ≤ 1/(s.bandwidth^2*σ^2))] at ht
      exact ht
    _ ≤ (1/(s.bandwidth*σ^3))*(6*δ^2*C^2*(s.bandwidth*Q))+
        (1/(s.bandwidth^2*σ^2))*(18*(4*δ^2)*C^3*(s.bandwidth^2*Q/(d*σ))) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by positivity)) (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = (6*C^2*d+72*C^3)*(δ^2*Q/(d*σ^3)) := by field_simp [hh.ne',hσ.ne',hd.ne']; ring
    _ ≤ (78*C^3)*(δ^2*Q/(d*σ^3)) := by gcongr; nlinarith only [hCd]
    _ = _ := by ring


end
end RectangleCLTArxivV1
