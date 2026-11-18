import RectangleCLTArxivV1.SupplementalHRidgeMain

/-! The actual facet and ridge Gaussian section expectations, with one
universal numerical constant, at volume-almost every threshold list. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
noncomputable section

/-- Fixed before all dimensions, normals, thresholds and base laws. -/
def localizedGaussianSurfaceConstant : ℝ :=
  (22528+3072*Real.pi)*Real.exp ((3:ℝ)/2)*Real.exp 128

theorem localizedGaussianSurfaceConstant_pos : 0<localizedGaussianSurfaceConstant := by
  unfold localizedGaussianSurfaceConstant
  positivity

/-- The two actual localized Gaussian surface quantities satisfy their
joint expectation bound. All hard surface suppliers and radius moments
are discharged. This theorem retains the AE threshold qualification. -/
theorem ae_localizedGaussianSurfaceEstimates {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => hardGaussianWeightedFacetIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
      Integrable (fun x => hardGaussianWeightedRidgeIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
      (∫ x,|hardGaussianWeightedFacetIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)+
      (∫ x,|hardGaussianWeightedRidgeIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
        localizedGaussianSurfaceConstant*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_hardGaussianWeightedFacetIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase,
    ae_hardGaussianWeightedRidgeIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase] with a hf he
  refine ⟨hf.1,he.1,?_⟩
  exact (add_le_add hf.2 he.2).trans_eq (by unfold localizedGaussianSurfaceConstant; ring)

end
end RectangleCLTArxivV1
