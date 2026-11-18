import RectangleCLTArxivV1.SupplementalHSurfaceFullDimensional

/-! The literal empty-or-full-dimensional geometric surface headline.
The fixed numerical constant and exact facet presentation are chosen
before every concentrated base law, with no simplicity hypothesis. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
noncomputable section

theorem exists_fixed_surface_bound_of_empty_or_fullDimensional {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hQ : gaussianFiniteThresholdEvent Finset.univ (fun k => U (f k)) a=∅ ∨
      (interior (gaussianFiniteThresholdEvent Finset.univ (fun k => U (f k)) a)).Nonempty) :
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
  apply exists_fixed_surface_bound_of_empty_or_strictInterior hp U f a hu
  exact hQ.imp id (hasStrictFacetInterior_of_nonempty_interior _ a hu)

end
end RectangleCLTArxivV1
