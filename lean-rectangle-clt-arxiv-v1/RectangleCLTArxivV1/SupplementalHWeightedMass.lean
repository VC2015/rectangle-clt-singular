import RectangleCLTArxivV1.SupplementalHIntrinsicMass

/-! Actual Gaussian-weighted selector masses obtained by conditioning on
the Gaussian vector and retaining the intrinsic transition coefficient. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem intrinsicRectangleConcentration_gaussianWeightedSelectorMass
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (B : Vector r → ℝ) (hBm : Measurable B) (hB0 : ∀ g, 0 ≤ B g)
    (hBi : Integrable B (standardGaussian r)) (K : ℕ) :
    (∫ ω, ∫ g, B g*(∑ α : Fin (K+1) → Face p,
      selectorWeight s α (V ω+M.mulVec g)) ∂standardGaussian r ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*(∫ g, B g ∂standardGaussian r) := by
  classical
  let W := fun z : Ω × Vector r => ∑ α : Fin (K+1) → Face p,
    selectorWeight s α (V z.1+M.mulVec z.2)
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hX : Measurable (fun z : Ω × Vector r => V z.1+M.mulVec z.2) :=
    (hV.comp measurable_fst).add (hM.comp measurable_snd)
  have hWm : Measurable W := Finset.measurable_sum _
    (fun α _ => (continuous_selectorWeight s α).measurable.comp hX)
  have hWb (z : Ω × Vector r) : 0 ≤ W z ∧ W z ≤ 1 := by
    dsimp only [W]
    rw [sum_selectorWeight_eq]
    exact SignedSurface.smoother_selector_weight_bounds s (K+1) _
  have hBprod : Integrable (fun z : Ω × Vector r => B z.2) (μ.prod (standardGaussian r)) := by
    apply (integrable_prod_iff ((hBm.comp measurable_snd).aestronglyMeasurable)).mpr
    refine ⟨ae_of_all _ (fun _ => hBi),?_⟩
    change Integrable (fun _ : Ω => ∫ g, ‖B g‖ ∂standardGaussian r) μ
    exact integrable_const _
  have hi : Integrable (fun z : Ω × Vector r => B z.2*W z) (μ.prod (standardGaussian r)) := by
    apply hBprod.mono' (((hBm.comp measurable_snd).mul hWm).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change |B z.2*W z| ≤ B z.2
      rw [abs_of_nonneg (mul_nonneg (hB0 z.2) (hWb z).1)]
      exact mul_le_of_le_one_right (hB0 z.2) (hWb z).2)
  have hpoint (g : Vector r) : (∫ ω, B g*W (ω,g) ∂μ) ≤ (4*C₀*s.bandwidth*κ)*B g := by
    rw [integral_const_mul]
    have ht := intrinsicRectangleConcentration_selectorMass μ V hV s hC₀ hκ hδh hc K (M.mulVec g)
    exact (mul_le_mul_of_nonneg_left ht (hB0 g)).trans_eq (mul_comm _ _)
  change (∫ ω, ∫ g, B g*W (ω,g) ∂standardGaussian r ∂μ) ≤ _
  rw [integral_integral_swap hi]
  exact (integral_mono hi.integral_prod_right (hBi.const_mul _) hpoint).trans_eq (integral_const_mul _ _)

end
end RectangleCLTArxivV1
