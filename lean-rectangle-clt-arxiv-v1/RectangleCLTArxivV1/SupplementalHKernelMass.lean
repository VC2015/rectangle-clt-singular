import RectangleCLTArxivV1.SupplementalHOuterEntropy

/-! Measurability and integrability of actual Gaussian kernel masses,
including the unbounded directional references used in cubic entropy. -/
namespace RectangleCLTArxivV1
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem supplementalH_dominated_kernel_mass_properties
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (W : Ω × Γ → ℝ) (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z)
    (B : Γ → ℝ) (hBm : Measurable B)
    (hBi : Integrable B ν) (hdom : ∀ z, W z ≤ B z.2) :
    Measurable (fun ω => ∫ g, W (ω,g) ∂ν) ∧
      Integrable (fun ω => ∫ g, W (ω,g) ∂ν) μ ∧
      (∀ ω, Integrable (fun g => W (ω,g)) ν) ∧
      (∀ ω, 0 ≤ (∫ g, W (ω,g) ∂ν) ∧ (∫ g, W (ω,g) ∂ν) ≤ ∫ g, B g ∂ν) := by
  have hBiProd : Integrable (fun z : Ω × Γ => B z.2) (μ.prod ν) := by
    apply (integrable_prod_iff ((hBm.comp measurable_snd).aestronglyMeasurable)).mpr
    refine ⟨ae_of_all _ (fun _ => hBi),?_⟩
    change Integrable (fun _ : Ω => ∫ g, ‖B g‖ ∂ν) μ
    exact integrable_const _
  have hWiProd : Integrable W (μ.prod ν) := by
    apply hBiProd.mono' hWm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hW0 z)]
      exact hdom z)
  have hWi (ω : Ω) : Integrable (fun g => W (ω,g)) ν := by
    have hm : Measurable (fun g => W (ω,g)) := hWm.comp (measurable_const.prodMk measurable_id)
    apply hBi.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hW0 (ω,g))]
      exact hdom (ω,g))
  refine ⟨hWm.stronglyMeasurable.integral_prod_right'.measurable,hWiProd.integral_prod_left,hWi,?_⟩
  intro ω
  exact ⟨integral_nonneg (fun g => hW0 (ω,g)),integral_mono (hWi ω) hBi (fun g => hdom (ω,g))⟩

end
end RectangleCLTArxivV1
