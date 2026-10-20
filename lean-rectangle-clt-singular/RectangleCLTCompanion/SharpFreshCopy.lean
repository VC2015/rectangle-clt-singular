import RectangleCLTCompanion.SharpGaussianSplit

open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section

/-- Adding an unused independent fresh copy preserves an actual product expectation. -/
theorem integral_prod_drop_fresh_copy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω × Ω → ℝ) :
    (∫ z : Ω × (Ω × Ω), f (z.1, z.2.1) ∂μ.prod (μ.prod μ)) =
      ∫ z : Ω × Ω, f z ∂μ.prod μ := by
  have h := (measurePreserving_prodAssoc μ μ μ).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun z : Ω × (Ω × Ω) => f (z.1, z.2.1))
  change (∫ z : (Ω × Ω) × Ω, f z.1 ∂(μ.prod μ).prod μ) = _ at h
  rw [← h]
  simpa only [mul_one, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
    integral_prod_mul (μ := μ.prod μ) (ν := μ) f (fun _ : Ω => (1 : ℝ))

end
end RectangleCLT.Companion
