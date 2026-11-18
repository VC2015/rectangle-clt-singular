import RectangleCLTArxivV1.SupplementalHKernelMass
import RectangleCLTArxivV1.SupplementalHWeightedMass

/-! Outer averages of actual tuple kernels with a common Gaussian
majorant. The complete original selector face set is retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem intrinsicRectangleConcentration_selectorFamilyKernel
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (c : (Fin (K+1) → Face p) → Vector r → ℝ)
    (hcm : ∀ α, Measurable (c α)) (hc0 : ∀ α g, 0 ≤ c α g)
    (B : Vector r → ℝ) (hBm : Measurable B) (hB0 : ∀ g, 0 ≤ B g)
    (hBi : Integrable B (standardGaussian r)) (hdom : ∀ α g, c α g ≤ B g) :
    (∀ α, Measurable (fun ω => ∫ g, c α g*selectorWeight s α (V ω+M.mulVec g)
      ∂standardGaussian r) ∧
      Integrable (fun ω => ∫ g, c α g*selectorWeight s α (V ω+M.mulVec g)
        ∂standardGaussian r) μ) ∧
    (∫ ω, ∑ α, ∫ g, c α g*selectorWeight s α (V ω+M.mulVec g)
      ∂standardGaussian r ∂μ) ≤ (4*C₀*s.bandwidth*κ)*(∫ g, B g ∂standardGaussian r) := by
  classical
  let X := fun z : Ω × Vector r => V z.1+M.mulVec z.2
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hX : Measurable X := (hV.comp measurable_fst).add (hM.comp measurable_snd)
  let W := fun α (z : Ω × Vector r) => c α z.2*selectorWeight s α (X z)
  have hWm (α) : Measurable (W α) :=
    (hcm α |>.comp measurable_snd).mul ((continuous_selectorWeight s α).measurable.comp hX)
  have hW0 (α) (z) : 0 ≤ W α z := mul_nonneg (hc0 α z.2) (selectorWeight_nonneg s α _)
  have hWB (α) (z : Ω × Vector r) : W α z ≤ B z.2 := by
    exact (mul_le_of_le_one_right (hc0 α z.2) (selectorWeight_le_one s α _)).trans (hdom α z.2)
  have hWP (α) := supplementalH_dominated_kernel_mass_properties μ (standardGaussian r)
    (W α) (hWm α) (hW0 α) B hBm hBi (hWB α)
  let T := fun z : Ω × Vector r => B z.2*(∑ α : Fin (K+1) → Face p, selectorWeight s α (X z))
  have hT0 (z) : 0 ≤ T z := mul_nonneg (hB0 z.2)
    (Finset.sum_nonneg (fun α _ => selectorWeight_nonneg s α _))
  have hTm : Measurable T := (hBm.comp measurable_snd).mul
    (Finset.measurable_sum _ (fun α _ => (continuous_selectorWeight s α).measurable.comp hX))
  have hTB (z : Ω × Vector r) : T z ≤ B z.2 := by
    apply mul_le_of_le_one_right (hB0 z.2)
    rw [sum_selectorWeight_eq]
    exact (SignedSurface.smoother_selector_weight_bounds s (K+1) _).2
  have hTP := supplementalH_dominated_kernel_mass_properties μ (standardGaussian r)
    T hTm hT0 B hBm hBi hTB
  have hpoint (ω : Ω) : (∑ α, ∫ g, W α (ω,g) ∂standardGaussian r) ≤
      ∫ g, T (ω,g) ∂standardGaussian r := by
    rw [←integral_finset_sum _ (fun α _ => (hWP α).2.2.1 ω)]
    apply integral_mono
      (integrable_finset_sum _ (fun α _ => (hWP α).2.2.1 ω)) (hTP.2.2.1 ω)
    intro g
    dsimp only [W,T]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun α _ => mul_le_mul_of_nonneg_right (hdom α g)
      (selectorWeight_nonneg s α _))
  refine ⟨fun α => ⟨(hWP α).1,(hWP α).2.1⟩,?_⟩
  exact (integral_mono (integrable_finset_sum _ (fun α _ => (hWP α).2.1)) hTP.2.1 hpoint).trans
    (intrinsicRectangleConcentration_gaussianWeightedSelectorMass μ V hV s M
      hC₀ hκ hδh hc B hBm hB0 hBi K)

end
end RectangleCLTArxivV1
