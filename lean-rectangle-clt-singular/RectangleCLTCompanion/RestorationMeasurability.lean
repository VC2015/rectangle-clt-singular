import RectangleCLTCompanion.RestorationTraceSeries

/-! Structural measurability of the actual fresh-array coefficient matrices.
This discharges the entry-measurability assumptions in the restoration cap
whenever the original arrays are jointly measurable. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

theorem measurable_translatedRestorationCoefficient
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p r n k ℓ : ℕ} (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p)
    (hZ : ∀ i, Measurable (fun wa : Ω × Ξ => Z wa.1 i wa.2))
    (hc : ∀ i α, Measurable (fun wa : Ω × Ξ => c i α wa.1 wa.2))
    (hv : ∀ i, Measurable (fun wa : Ω × Ξ => v i wa.1 wa.2))
    (α : Fin k → Face p) (β : Fin ℓ → Face p) (j l : Fin r) :
    Measurable (fun ω => translatedRestorationCoefficient s μ Z c v α β ω j l) := by
  unfold translatedRestorationCoefficient restorationCoefficient
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun wa : Ω × Ξ =>
      (c i α wa.1 wa.2 * restorationTranslationCoefficient s α β (v i wa.1 wa.2)) *
        (Z wa.1 i wa.2 j * Z wa.1 i wa.2 l)) :=
    ((hc i α).mul (measurable_restorationTranslationCoefficient_comp s α β _ (hv i))).mul
      (((measurable_pi_apply j).comp (hZ i)).mul ((measurable_pi_apply l).comp (hZ i)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end
end RectangleCLT.Companion
