import RectangleCLTArxivV1.SupplementalHRidgeAveraged
import RectangleCLTArxivV1.SupplementalHPositiveEdgeAveraged

/-! The actual angle-weighted signed Gaussian ridge quantity satisfies
its localized expectation estimate for arbitrary concentrated base laws.
The threshold qualification is volume-almost everywhere. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- Actual J_e expectation, combining the literal leading term with the
actual signed three-incidence spherical cancellation and conical tube
transport. Every supplier is proved for the genuine hard Gaussian
sections; the arbitrary base law may be singular. -/
theorem ae_hardGaussianWeightedRidgeIntegral_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => hardGaussianWeightedRidgeIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
      (∫ x,|hardGaussianWeightedRidgeIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
        ((3072*Real.pi+6144)*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_hardGaussianRidgeLeadingIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase,
    ae_hardGaussianRidgeThirdBoundaryIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase,
    ae_threshold_ae_base_pairResidualThresholdRegularity ν (fun k => U (f k)) hσ.ne'] with a hlead hthird hreg
  let B := fun x : Vector (n+1) => fun k => (a k-faceDot (U (f k)) x)/σ
  let S := fun x => hardGaussianWeightedRidgeIntegral (fun k => U (f k)) (B x)
  let L := fun x => hardGaussianRidgeLeadingIntegral (fun k => U (f k)) (B x)
  let T := fun x => hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k)) (B x)
  have heq : S=ᵐ[ν] fun x => L x-T x := by
    filter_upwards [hreg] with x hx
    exact hardGaussianWeightedRidgeIntegral_Green_of_slack _ (B x) hu hx
  have hS : Integrable S ν := (hlead.1.sub hthird.1).congr heq.symm
  refine ⟨hS,?_⟩
  have hb : ∀ᵐ x ∂ν,|S x|≤|L x|+|T x| := by
    filter_upwards [heq] with x hx
    rw [hx]
    exact abs_sub _ _
  have hh := integral_mono_ae hS.abs (hlead.1.abs.add hthird.1.abs) hb
  simp only [Pi.add_apply] at hh
  rw [integral_add hlead.1.abs hthird.1.abs] at hh
  exact hh.trans ((add_le_add hlead.2 hthird.2).trans_eq (by ring))

end
end RectangleCLTArxivV1
