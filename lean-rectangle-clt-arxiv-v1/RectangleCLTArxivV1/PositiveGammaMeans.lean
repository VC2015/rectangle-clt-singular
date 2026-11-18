import RectangleCLTArxivV1.SupplementalHGammaPositiveEdgeBudget
import RectangleCLTArxivV1.PositiveGammaPairSum

/-! Concentrated-base means of the actual positive ordered soft pair
mass and pair-plane moment, retaining their separate logarithmic powers. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

private theorem positiveGamma_mean_transfer {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (J : Ω × Ξ → ℝ) (hJ : Integrable J (μ.prod ν)) (S : Ξ → ℝ)
    {c B : ℝ} (hc : 0≤c) (hS : ∀ x,S x=c*(∫ e,J (e,x) ∂μ))
    (hbudget : (∫ e,∫ x,J (e,x) ∂ν ∂μ)≤B) :
    Integrable S ν ∧ (∫ x,S x ∂ν)≤c*B := by
  have hSi : Integrable S ν := (hJ.integral_prod_right.const_mul c).congr
    (ae_of_all _ (fun x => (hS x).symm))
  refine ⟨hSi,?_⟩
  have heq : (∫ x,S x ∂ν)=c*(∫ e,∫ x,J (e,x) ∂ν ∂μ) := by
    calc
      (∫ x,S x ∂ν)=(∫ x,c*(∫ e,J (e,x) ∂μ) ∂ν) := integral_congr_ae (ae_of_all _ hS)
      _=c*(∫ x,∫ e,J (e,x) ∂μ ∂ν) := integral_const_mul _ _
      _=c*(∫ e,∫ x,J (e,x) ∂ν ∂μ) := by
        rw [← integral_integral_swap (f := fun e x => J (e,x)) hJ]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hbudget hc

def positiveSoftPairMassConstant : ℝ :=
  (1024*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128

def positiveSoftPairProjectionConstant : ℝ :=
  (4096*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128

theorem positiveSoftPairMassConstant_pos : 0<positiveSoftPairMassConstant := by
  unfold positiveSoftPairMassConstant
  positivity

theorem positiveSoftPairProjectionConstant_pos : 0<positiveSoftPairProjectionConstant := by
  unfold positiveSoftPairProjectionConstant
  positivity

/-- Actual positive ordered-pair soft mass. The sharp bare-edge budget
retains sqrt(log p), and the original concentration coefficient is the
only source of the base-law dependence. -/
theorem positiveGammaSoftOrderedPairMass_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    Integrable (positiveGammaSoftOrderedPairMass (fun j => U (f j)) a h σ) ν ∧
    (∫ x,positiveGammaSoftOrderedPairMass (fun j => U (f j)) a h σ x ∂ν)≤
      positiveSoftPairMassConstant*h^2*K*Real.sqrt (dimensionLog p)/σ := by
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) =>
    ∑ e : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ) 0 e
  have hJ := supplementalH_gamma_positive_edge_mass_budget hp ν U f a hK hδ hσ hh hu hbase 0
  have hbudget := supplementalH_gamma_positive_edge_mass_budget_small_delta hp ν U f a hK hδ hσ hh hu hbase hδσ 0
  have hs (x : Vector (n+1)) : positiveGammaSoftOrderedPairMass (fun j => U (f j)) a h σ x=
      (h^2/(2*σ^2))*(∫ e,J (e,x) ∂gammaRectangleLaw m 0) :=
    positiveGammaSoftOrderedPairMass_eq_gamma (fun j => U (f j)) hu a hh hσ x
  have ht := positiveGamma_mean_transfer (gammaRectangleLaw m 0) ν J hJ.1
    (positiveGammaSoftOrderedPairMass (fun j => U (f j)) a h σ)
    (by positivity : 0≤h^2/(2*σ^2)) hs hbudget
  refine ⟨ht.1,ht.2.trans_eq ?_⟩
  unfold positiveSoftPairMassConstant
  field_simp [hσ.ne']
  ring

/-- Actual positive ordered-pair projected Gaussian moment. Its own R4
budget retains log(p)^(3/2); no bare-mass estimate loses an extra log. -/
theorem positiveGammaSoftOrderedPairProjection_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    Integrable (positiveGammaSoftOrderedPairProjection (fun j => U (f j)) a h σ) ν ∧
    (∫ x,positiveGammaSoftOrderedPairProjection (fun j => U (f j)) a h σ x ∂ν)≤
      positiveSoftPairProjectionConstant*h^2*K*(dimensionLog p*Real.sqrt (dimensionLog p))/σ := by
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) =>
    ∑ e : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ) 2 e
  have hJ := supplementalH_gamma_positive_edge_normSq_budget hp ν U f a hK hδ hσ hh hu hbase 0
  have hbudget := supplementalH_gamma_positive_edge_normSq_budget_small_delta hp ν U f a hK hδ hσ hh hu hbase hδσ 0
  have hs (x : Vector (n+1)) : positiveGammaSoftOrderedPairProjection (fun j => U (f j)) a h σ x=
      (h^2/(2*σ^2))*(∫ e,J (e,x) ∂gammaRectangleLaw m 0) :=
    positiveGammaSoftOrderedPairProjection_eq_gamma (fun j => U (f j)) hu a hh hσ x
  have ht := positiveGamma_mean_transfer (gammaRectangleLaw m 0) ν J hJ.1
    (positiveGammaSoftOrderedPairProjection (fun j => U (f j)) a h σ)
    (by positivity : 0≤h^2/(2*σ^2)) hs hbudget
  refine ⟨ht.1,ht.2.trans_eq ?_⟩
  unfold positiveSoftPairProjectionConstant
  field_simp [hσ.ne']
  ring

end
end RectangleCLTArxivV1
