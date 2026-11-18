import RectangleCLTArxivV1.SupplementalHActualFacetTubeBound
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged

/-! All-threshold actual J_f after one fixed exact facet selection. The
base law may be singular, and its concentration is applied to the
original full-family layer, not an expanded selected presentation. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actualFacet_selected_weightedFacetIntegral_base_tube_bound {p m q n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤a (e i)) ↔
      ∀ k,faceDot (U (f k)) y≤a k)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hinterior : HasStrictFacetInterior (fun i => U (f (e i))) (fun i => a (e i)))
    (hwitness : HasIrredundantFacetWitnesses (fun i => U (f (e i))) (fun i => a (e i)))
    {σ : ℝ} (hσ : 0<σ) :
    Integrable (fun x => hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
      (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)) ν ∧
    (∫ x,|hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
      (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)| ∂ν)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ z,
        (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
          (fun z => supplementalHRadius U z.2^4) z ∂ν.prod (standardGaussian (n+1))) := by
  let C := 16384*Real.exp ((3:ℝ)/2)
  let J := fun x => hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
    (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)
  let I := (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
    (fun z => supplementalHRadius U z.2^4)
  have hIset := fourthTransport_measurableSet_gaussianOutwardVariableTube (fun k => U (f k)) a σ
    (supplementalHRadius U) (measurable_supplementalHRadius U)
  have hi : Integrable I (ν.prod (standardGaussian (n+1))) := by
    have hr : Integrable (fun z : Vector (n+1) × Vector (n+1) => supplementalHRadius U z.2^4)
        (ν.prod (standardGaussian (n+1))) := by
      simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod
        (supplementalHRadius_moment_le hp U 4).1
    exact hr.indicator hIset
  have hJ : Measurable J :=
    (measurable_hardGaussianWeightedFacetIntegral (fun i => U (f (e i))) (fun i => hu (e i))).comp
      (by apply measurable_pi_lambda; intro i; exact (measurable_const.sub (measurable_thresholdDot _)).div_const σ)
  have hb : ∀ᵐ x ∂ν,|J x|≤C*(∫ g,I (x,g) ∂standardGaussian (n+1)) := ae_of_all _
    (fun x => actualFacet_selected_weightedFacetIntegral_affine_le_original_tube hp U f a e
      hequiv hu hinterior hwitness x hσ)
  have hJi : Integrable J ν := (hi.integral_prod_left.const_mul C).mono' hJ.aestronglyMeasurable
    (hb.mono (fun _ h => by simpa only [Real.norm_eq_abs] using h))
  refine ⟨hJi,?_⟩
  have hh := integral_mono_ae hJi.abs (hi.integral_prod_left.const_mul C) hb
  rw [integral_const_mul,← integral_prod _ hi] at hh
  exact hh

theorem actualFacet_selected_weightedFacetIntegral_concentrated_base {p m q n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤a (e i)) ↔
      ∀ k,faceDot (U (f k)) y≤a k)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hinterior : HasStrictFacetInterior (fun i => U (f (e i))) (fun i => a (e i)))
    (hwitness : HasIrredundantFacetWitnesses (fun i => U (f (e i))) (fun i => a (e i)))
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    Integrable (fun x => hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
      (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)) ν ∧
    (∫ x,|hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
      (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)| ∂ν)≤
      (16384*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  have h := actualFacet_selected_weightedFacetIntegral_base_tube_bound hp ν U f a e
    hequiv hu hinterior hwitness hσ
  refine ⟨h.1,h.2.trans ?_⟩
  have ht := concentrated_base_threeFace_weighted_outward_tube hp ν (fun k => U (f k)) a U hK hδ hσ hbase
  exact (mul_le_mul_of_nonneg_left ht (by positivity : 0≤16384*Real.exp ((3:ℝ)/2))).trans_eq (by ring)

/-- The actual facet selection is fixed using only the original
polyhedron. It then works for every probability base, every positive
Gaussian scale, and every displayed concentration coefficient. -/
theorem exists_fixed_actualFacet_concentrated_base_bound {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hinterior : HasStrictFacetInterior (fun k => U (f k)) a) :
    ∃ (q : ℕ) (e : Fin q → Fin m),q≤m ∧ Function.Injective e ∧
      (∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤a (e i)) ↔
        ∀ k,faceDot (U (f k)) y≤a k) ∧
      ∀ (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν] (K δ σ : ℝ),
        0≤K → 0≤δ → 0<σ →
        (∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) →
        Integrable (fun x => hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
          (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)) ν ∧
        (∫ x,|hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
          (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)| ∂ν)≤
          (16384*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
            (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  obtain ⟨q,e,hq,he,hequiv,hint,hw⟩ := exists_actual_facet_presentation (fun k => U (f k)) a hinterior
  refine ⟨q,e,hq,he,hequiv,?_⟩
  intro ν _ K δ σ hK hδ hσ hbase
  exact actualFacet_selected_weightedFacetIntegral_concentrated_base hp ν U f a e hequiv hu hint hw
    hK hδ hσ hbase

end
end RectangleCLTArxivV1
