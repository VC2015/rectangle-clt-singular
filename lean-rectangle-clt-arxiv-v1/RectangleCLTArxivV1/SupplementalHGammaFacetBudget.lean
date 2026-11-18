import RectangleCLTArxivV1.SupplementalHGammaThresholdLaw
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged

/-! The actual hard weighted-facet budget under the Gamma mixture.
Auxiliary threshold absolute continuity removes geometric exceptional
configurations while allowing a singular physical base. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalH_gamma_weighted_facet_budget {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {C δ σ h : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j, vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤C*(s+δ)) (q : ℕ) :
    Integrable (fun z => hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (gammaAdjustedThreshold a h z.1 k-faceDot (U (f k)) z.2)/σ))
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, |hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (U (f k)) x)/σ)| ∂ν ∂gammaRectangleLaw m q) ≤
      (16384*Real.exp ((3:ℝ)/2))*Real.exp 128*C*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) =>
    hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (gammaAdjustedThreshold a h z.1 k-faceDot (U (f k)) z.2)/σ)
  let B := (16384*Real.exp ((3:ℝ)/2))*Real.exp 128*C*
    (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2)
  have hJ : Measurable J :=
    (measurable_hardGaussianWeightedFacetIntegral (fun k => U (f k)) hu).comp (by
      apply measurable_pi_lambda
      intro k
      exact (((measurable_pi_apply k).comp ((measurable_gammaAdjustedThreshold a h).comp measurable_fst)).sub
        ((continuous_faceDot_left (U (f k))).measurable.comp measurable_snd)).div_const σ)
  have hAe := ae_hardGaussianWeightedFacetIntegral_concentrated_base hp ν U f hC hδ hσ hu hbase
  have hg := (supplementalH_gammaThreshold_absolutelyContinuous a hh q).ae_le hAe
  have hs := ae_of_ae_map (measurable_gammaAdjustedThreshold a h).aemeasurable hg
  have hJi : Integrable J ((gammaRectangleLaw m q).prod ν) := by
    apply (integrable_prod_iff hJ.aestronglyMeasurable).mpr
    refine ⟨hs.mono (fun e he => he.1),?_⟩
    have hm : AEStronglyMeasurable (fun e => ∫ x, ‖J (e,x)‖ ∂ν) (gammaRectangleLaw m q) :=
      (hJ.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
    apply (integrable_const B).mono' hm
    filter_upwards [hs] with e he
    change ‖∫ x, ‖J (e,x)‖ ∂ν‖≤B
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using he.2
  refine ⟨hJi,?_⟩
  have hi := hJi.abs.integral_prod_left
  exact (integral_mono_ae hi (integrable_const B) (hs.mono (fun e he => he.2))).trans_eq (by simp [B])

/-- The bandwidth condition converts the actual Gamma-averaged hard
surface budget to its required intrinsic order. -/
theorem supplementalH_gamma_weighted_facet_budget_small_delta {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {C δ σ h : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j, vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤C*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    (∫ e, ∫ x, |hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (U (f k)) x)/σ)| ∂ν ∂gammaRectangleLaw m q) ≤
      (32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcost : δ*(dimensionLog p)^2≤σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
    have ht := mul_le_mul_of_nonneg_right hδσ (mul_nonneg hL (Real.sqrt_nonneg (dimensionLog p)))
    calc
      _ = δ*dimensionLog p*(Real.sqrt (dimensionLog p))^2 := by rw [Real.sq_sqrt hL]; ring
      _ = (δ*Real.sqrt (dimensionLog p))*(dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
      _ ≤ _ := ht
  have hb := supplementalH_gamma_weighted_facet_budget hp ν U f a hC hδ hσ hh hu hbase q
  exact hb.2.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hcost _) (by positivity :
    0≤(16384*Real.exp ((3:ℝ)/2))*Real.exp 128*C)).trans_eq (by ring))

end
end RectangleCLTArxivV1
