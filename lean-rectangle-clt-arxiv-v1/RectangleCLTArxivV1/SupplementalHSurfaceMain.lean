import RectangleCLTArxivV1.SupplementalHSurfaceEmpty

/-! The source empty-or-full-dimensional surface estimate, using one
fixed exact actual-facet presentation and a universal constant. Empty
sets have their actual native quantities proved equal to zero. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
noncomputable section

/-- Source H.1 surface estimate for empty or strictly full-dimensional
polyhedra. The facet selection is fixed before all probability models.
Nonsimple faces require no additional assumption. The surface convention
is the checked orthogonal-chart Lebesgue Gaussian surface measure. -/
theorem exists_fixed_surface_bound_of_empty_or_strictInterior {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hQ : gaussianFiniteThresholdEvent Finset.univ (fun k => U (f k)) a=∅ ∨
      HasStrictFacetInterior (fun k => U (f k)) a) :
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
  rcases hQ with hempty | hint
  · refine ⟨m,id,le_rfl,Function.injective_id,fun _ => Iff.rfl,?_⟩
    intro ν _ K δ σ hK hδ hσ _
    have hf (x : Vector (n+1)) : hardGaussianWeightedFacetIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)=0 :=
      hardGaussianWeightedFacetIntegral_zero_of_empty _ _
        (gaussianFiniteThresholdEvent_affine_empty _ a hempty x hσ)
    have he (x : Vector (n+1)) : hardGaussianWeightedRidgeIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)=0 :=
      hardGaussianWeightedRidgeIntegral_zero_of_empty _ _ hu
        (gaussianFiniteThresholdEvent_affine_empty _ a hempty x hσ)
    have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
    have hC := localizedGaussianSurfaceConstant_pos.le
    simpa only [id_eq,hf,he,abs_zero,integral_zero,zero_add] using
      (show Integrable (fun _ : Vector (n+1) => (0:ℝ)) ν ∧
        Integrable (fun _ : Vector (n+1) => (0:ℝ)) ν ∧
        (0:ℝ)≤localizedGaussianSurfaceConstant*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) from
        ⟨integrable_zero _ _ _,integrable_zero _ _ _,by positivity⟩)
  · exact exists_fixed_actualFacet_surface_concentrated_base_bound hp U f a hu hint

end
end RectangleCLTArxivV1
