import RectangleCLTArxivV1.SupplementalHFamilyKernelBounds
import RectangleCLTArxivV1.SupplementalHCubicMatrix
import RectangleCLTCompanion.SelectorMeanBound

/-! The actual unweighted mean terms in the cubic matrix decomposition.
The genuine selector mean proof is instantiated with the intrinsic mass
coefficient, before any matrix or probability comparison is concluded. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem intrinsicRectangleConcentration_cubicUnweightedCorrection
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hunit : ∀ j, vectorNormSq (A j)=1) :
    Integrable (fun ω => ∑ α : Fin (K+1) → Face p,
      supplementalHSelectorMass s (σ • A) (V ω) α*
        (1+vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α ((σ • A).mulVec g+V ω))))) μ ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      supplementalHSelectorMass s (σ • A) (V ω) α*
        (1+vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α ((σ • A).mulVec g+V ω)))) ∂μ) ≤
      4*C₀*s.bandwidth*κ+
        (Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*(4*C₀*s.bandwidth*κ)*dimensionLog p := by
  classical
  have hmass := intrinsicRectangleConcentration_selectorFamilyKernel (K := K) μ V hV s (σ • A)
    hC₀.le hκ.le hδh hc (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ => zero_le_one)
    (fun _ => 1) measurable_const (fun _ => zero_le_one) (integrable_const _) (fun _ _ => le_rfl)
  have hmi (α : Fin (K+1) → Face p) : Integrable (fun ω => supplementalHSelectorMass s (σ • A) (V ω) α) μ := by
    simpa only [supplementalHSelectorMass,weightMass,one_mul,add_comm] using (hmass.1 α).2
  have hmb : (∫ ω, ∑ α : Fin (K+1) → Face p, supplementalHSelectorMass s (σ • A) (V ω) α ∂μ) ≤
      4*C₀*s.bandwidth*κ := by
    simpa only [supplementalHSelectorMass,weightMass,one_mul,add_comm,integral_const,
      measureReal_univ_eq_one,one_smul,mul_one] using hmass.2
  have hEi := integrable_selectorFamilyMeanEnergy μ V hV s (Finset.univ : Finset (Fin (K+1) → Face p)) A σ
  have hM : 0<4*C₀*s.bandwidth*κ := by have hh := s.bandwidth_pos; positivity
  have htransition := intrinsicRectangleConcentration_transitionMassBound μ V hV hC₀.le hκ.le
    s.bandwidth_pos hδh hc
  have hEb := integral_selectorMeanEnergy_le (k := K) μ V hV hM htransition s rfl hp A hunit σ
  have he (ω : Ω) : (∑ α : Fin (K+1) → Face p,
      supplementalHSelectorMass s (σ • A) (V ω) α*
        (1+vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α ((σ • A).mulVec g+V ω))))) =
      (∑ α : Fin (K+1) → Face p, supplementalHSelectorMass s (σ • A) (V ω) α)+
        selectorFamilyMeanEnergy (k := K) s Finset.univ A σ (V ω) := by
    simp only [selectorFamilyMeanEnergy,supplementalHSelectorMass,mul_add,mul_one,
      Finset.sum_add_distrib]
  refine ⟨?_,?_⟩
  · simpa only [he] using (integrable_finset_sum _ (fun α _ => hmi α)).add hEi
  · simp_rw [he]
    rw [integral_add (integrable_finset_sum _ (fun α _ => hmi α)) hEi]
    exact add_le_add hmb hEb

end
end RectangleCLTArxivV1
