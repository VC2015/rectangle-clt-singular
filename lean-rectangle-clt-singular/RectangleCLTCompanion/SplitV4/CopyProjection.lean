import Mathlib.MeasureTheory.Integral.Prod

/-! Projection of the actual Gaussian/original/copy product experiment to
the original/Gaussian path law, with genuine integral transport. -/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4
noncomputable section

variable {G Ω E : Type*} [MeasurableSpace G] [MeasurableSpace Ω]

theorem copyGaussianProjection_measurePreserving
    (γ : Measure G) [SFinite γ] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : G × (Ω × Ω) => (z.2.1, z.1))
      (γ.prod (μ.prod μ)) (μ.prod γ) := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hid : MeasurePreserving (id : G → G) γ γ := ⟨measurable_id, by simp⟩
  exact Measure.measurePreserving_swap.comp (hid.prod hfst)

theorem integrable_copyGaussianProjection_iff [NormedAddCommGroup E]
    [NormedSpace ℝ E] (γ : Measure G) [SFinite γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω × G → E)
    (hK : AEStronglyMeasurable K (μ.prod γ)) :
    Integrable (fun z : G × (Ω × Ω) => K (z.2.1, z.1)) (γ.prod (μ.prod μ)) ↔
      Integrable K (μ.prod γ) :=
  (copyGaussianProjection_measurePreserving γ μ).integrable_comp hK

theorem integral_copyGaussianProjection [NormedAddCommGroup E]
    [NormedSpace ℝ E] (γ : Measure G) [SFinite γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω × G → E)
    (hK : AEStronglyMeasurable K (μ.prod γ)) :
    (∫ z : G × (Ω × Ω), K (z.2.1, z.1) ∂γ.prod (μ.prod μ)) =
      ∫ z : Ω × G, K z ∂μ.prod γ := by
  have hmp := copyGaussianProjection_measurePreserving γ μ
  rw [← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable
    (hmp.map_eq.symm ▸ hK)).symm

end
end RectangleCLT.Companion.SplitV4
