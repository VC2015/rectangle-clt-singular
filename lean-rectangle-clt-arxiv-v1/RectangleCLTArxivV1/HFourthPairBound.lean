import RectangleCLTArxivV1.HFourthPairRestoration

/-! The actual translated H2 pair expectation follows from a quantitative
matrix supplier on the first-pair restriction. Every extra restoration
index remains free; no mutual independence of array entries is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem hFourth_conditional_translated_pair_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → (Fin 2 → Face p) → Ω → ℝ)
    (hc : ∀ i α, @Measurable Ω ℝ mΩ inferInstance (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (P : Face p → Face p → Prop) [DecidableRel P]
    (hzero : ∀ i α, ¬P (α 0) (α 1) → ∀ᵐ ω ∂μ, c i α ω=0)
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C*(Real.exp (R/s.bandwidth)-1) < 1)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ) ≤ C^(ℓ+3)*T) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin 2 → Face p,
      (c i α z.1*repeatedDirectionScore z.2 (Z i z.1))*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i z.1))
          (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) ∧
    |∫ z : Ω × Vector r, ∑ i, ∑ α : Fin 2 → Face p,
      (c i α z.1*repeatedDirectionScore z.2 (Z i z.1))*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤
      restorationSelectorCap s b 1 R C T 2 := by
  letI : MeasurableSpace Ω := mΩ
  have hη : 0 ≤ Real.exp (R/s.bandwidth)-1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη1 : Real.exp (R/s.bandwidth)-1 < 1 :=
    (le_mul_of_one_le_left hη hC).trans_lt hsmall
  have hradius : R/s.bandwidth < Real.log 2 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
    linarith
  have he := translated_score_hasSum_expected_orders (mΩ := mΩ) s μ A V (hV.mono hH le_rfl)
    Z hZm hZ c hc v hv hb hR hcb hvb hradius
  have hord (ℓ : ℕ) := hFourth_pair_restoration_order_bound (mΩ := mΩ) s μ H hH A V hV Z c v hZ
    (fun i α => (hc i α).aestronglyMeasurable) (fun i => (hv i).aestronglyMeasurable)
    P hzero hb hR hcb hvb hbudget ℓ (hsupplier ℓ)
  have hbound := restoration_scalar_series_bound (k := 2)
    (hFourthPairRestorationOrder (mΩ := mΩ) s μ A V Z c v) hb hR s.bandwidth_pos hC hT hsmall
    (fun ℓ => by simpa only [Nat.cast_ofNat,show 2+ℓ+1=ℓ+3 by omega] using hord ℓ)
  refine ⟨he.1, ?_⟩
  rw [← he.2.tsum_eq]
  simpa only [conditionalRestorationTraceOrderIntegral,hFourthPairRestorationOrder,
    restorationSelectorCap,mul_one,Nat.cast_ofNat] using hbound.2

theorem hFourth_conditional_translated_pair_bound_numeric
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → (Fin 2 → Face p) → Ω → ℝ)
    (hc : ∀ i α, @Measurable Ω ℝ mΩ inferInstance (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (P : Face p → Face p → Prop) [DecidableRel P]
    (hzero : ∀ i α, ¬P (α 0) (α 1) → ∀ᵐ ω ∂μ, c i α ω=0)
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : restorationBandwidthConstant C*R ≤ s.bandwidth)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ) ≤ C^(ℓ+3)*T) :
    |∫ z : Ω × Vector r, ∑ i, ∑ α : Fin 2 → Face p,
      (c i α z.1*repeatedDirectionScore z.2 (Z i z.1))*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤ 18*b*C^3*T := by
  have hhalf := restoration_small_of_bandwidth s hC hR hband
  have hbnd := (hFourth_conditional_translated_pair_bound (mΩ := mΩ) s μ H hH A V hV
    Z hZm hZ c hc v hv P hzero hb hR hcb hvb hbudget hC hT (hhalf.trans_lt (by norm_num)) hsupplier).2
  have hcap := restorationSelectorCap_le s hb (by norm_num : (0:ℝ)≤1) hR hC hT hhalf 2
  norm_num at hcap
  exact hbnd.trans (hcap.trans_eq (by ring))

end
end RectangleCLTArxivV1
