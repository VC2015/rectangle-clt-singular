import RectangleCLTArxivV1.HFourthCubicInterchange

/-! Actual translated single-face H3 expectation from the explicit
arbitrary-length cubic matrix supplier. This is an intermediate analytic
bound, not a proof of the upstream geometric supplier. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hFourth_conditional_translated_cubic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → Face p → Ω → ℝ) (hc : ∀ i f, @Measurable Ω ℝ mΩ inferInstance (c i f))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C*(Real.exp (R/s.bandwidth)-1) < 1)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s A U V γ ω) ∂μ) ≤ C^(ℓ+2)*T) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1))
          (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) ∧
    |∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤
      restorationSelectorCap s b 1 R C T 1 := by
  letI : MeasurableSpace Ω := mΩ
  have hη : 0 ≤ Real.exp (R/s.bandwidth)-1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη1 : Real.exp (R/s.bandwidth)-1 < 1 :=
    (le_mul_of_one_le_left hη hC).trans_lt hsmall
  have hradius : R/s.bandwidth < Real.log 2 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
    linarith
  have he := hFourth_cubic_hasSum_expected_orders (mΩ := mΩ) s μ A U V (hV.mono hH le_rfl)
    Z hZm hZ c hc v hv hb hR hcb hvb hradius
  have hbound := hFourth_cubic_restoration_series_bound (mΩ := mΩ) s μ H hH A U V hV
    Z c v hZ (fun i f => (hc i f).aestronglyMeasurable) (fun i => (hv i).aestronglyMeasurable)
    hb hR hcb hvb hbudget hC hT hsmall hsupplier
  refine ⟨he.1, ?_⟩
  rw [← he.2.tsum_eq]
  simpa only [restorationSelectorCap,mul_one,Nat.cast_one,one_mul] using hbound.2

theorem hFourth_conditional_translated_cubic_bound_numeric
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → Face p → Ω → ℝ) (hc : ∀ i f, @Measurable Ω ℝ mΩ inferInstance (c i f))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : restorationBandwidthConstant C*R ≤ s.bandwidth)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s A U V γ ω) ∂μ) ≤ C^(ℓ+2)*T) :
    |∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤ 6*b*C^2*T := by
  have hhalf := restoration_small_of_bandwidth s hC hR hband
  have hbnd := (hFourth_conditional_translated_cubic_bound (mΩ := mΩ) s μ H hH A U V hV
    Z hZm hZ c hc v hv hb hR hcb hvb hbudget hC hT (hhalf.trans_lt (by norm_num)) hsupplier).2
  have hcap := restorationSelectorCap_le s hb (by norm_num : (0:ℝ)≤1) hR hC hT hhalf 1
  norm_num at hcap
  exact hbnd.trans (hcap.trans_eq (by ring))

end
end RectangleCLTArxivV1
