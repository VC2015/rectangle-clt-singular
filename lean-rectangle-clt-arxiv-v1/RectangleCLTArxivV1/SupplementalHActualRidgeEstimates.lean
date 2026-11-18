import RectangleCLTArxivV1.SupplementalHSurfaceFatou
import RectangleCLTArxivV1.SupplementalHSurfaceEstimates
import RectangleCLTArxivV1.SupplementalHActualFacetAveraged
import RectangleCLTArxivV1.SupplementalHSubsystemConcentration

/-! Actual all-threshold ridge expectations for a proper full-dimensional
polyhedron. One exact irredundant presentation is fixed before the base
law; nonsimple codimension-three intersections are allowed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- The AE native ridge bound extends to this exact irredundant
full-dimensional threshold by value continuity and genuine Fatou. The
base law may be singular; no pair-derivative regularity is assumed. -/
theorem actualFacet_weightedRidgeIntegral_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hinterior : HasStrictFacetInterior (fun k => U (f k)) a)
    (hwitness : HasIrredundantFacetWitnesses (fun k => U (f k)) a)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    Integrable (fun x => hardGaussianWeightedRidgeIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
    (∫ x,|hardGaussianWeightedRidgeIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
      ((3072*Real.pi+6144)*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  let u := fun k => U (f k)
  let J := fun b : Vector m => fun x => hardGaussianWeightedRidgeIntegral u
    (fun k => (b k-faceDot (u k) x)/σ)
  have hgood := ae_hardGaussianWeightedRidgeIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase
  have hcont : ∀ᵐ x ∂ν,ContinuousAt (fun b => J b x) a := ae_of_all _ (fun x => by
    have hr := actualFacet_residualThresholdRegularity_affine u a hinterior hwitness x hσ
    have hc := continuousAt_hardGaussianWeightedRidgeIntegral_of_residual_slack u _ hu hr
    have hmap : ContinuousAt (fun b : Vector m => fun k => (b k-faceDot (u k) x)/σ) a := by
      apply continuousAt_pi.mpr
      intro k
      exact (((continuous_apply k : Continuous (fun b : Vector m => b k)).continuousAt).sub_const (faceDot (u k) x)).div_const σ
    simpa only [J] using hc.comp hmap)
  have hJm : Measurable (J a) := (measurable_hardGaussianWeightedRidgeIntegral u).comp
    (by apply measurable_pi_lambda; intro k; exact (measurable_const.sub (measurable_thresholdDot _)).div_const σ)
  exact integrable_abs_bound_of_ae_parameter_continuity ν J a hgood hcont hJm.aestronglyMeasurable

/-- Actual J_f and J_e for one fixed exact facet presentation, chosen
using only the original polyhedron before all concentrated base laws and
scales. The displayed numerical constant precedes all model data. -/
theorem exists_fixed_actualFacet_surface_concentrated_base_bound {p m n : ℕ} (hp : 1≤p)
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
        Integrable (fun x => hardGaussianWeightedRidgeIntegral (fun i => U (f (e i)))
          (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)) ν ∧
        (∫ x,|hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
          (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)| ∂ν)+
        (∫ x,|hardGaussianWeightedRidgeIntegral (fun i => U (f (e i)))
          (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)| ∂ν)≤
          localizedGaussianSurfaceConstant*K*
            (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  obtain ⟨q,e,hq,he,hequiv,hint,hw⟩ := exists_actual_facet_presentation (fun k => U (f k)) a hinterior
  refine ⟨q,e,hq,he,hequiv,?_⟩
  intro ν _ K δ σ hK hδ hσ hbase
  have hf := actualFacet_selected_weightedFacetIntegral_concentrated_base hp ν U f a e hequiv hu hint hw
    hK hδ hσ hbase
  have hsub := faceLayer_concentration_subsystem ν (fun k => U (f k)) e he hbase
  have hr := actualFacet_weightedRidgeIntegral_concentrated_base hp ν U (fun i => f (e i))
    (fun i => a (e i)) (fun i => hu (e i)) hint hw hK hδ hσ hsub
  refine ⟨hf.1,hr.1,?_⟩
  exact (add_le_add hf.2 hr.2).trans_eq (by unfold localizedGaussianSurfaceConstant; ring)

end
end RectangleCLTArxivV1
