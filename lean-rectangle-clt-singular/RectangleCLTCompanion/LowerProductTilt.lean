import RectangleCLTCompanion.LowerScalarTilt
import RectangleCLTCompanion.LowerProductArray
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact finite-product changes of measure. All measures in this file
are the genuine product and Esscher laws used in the lower construction. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

theorem lower_pi_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity
        (fun z => ENNReal.ofReal (∏ i : Fin n, f (z i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  let ms : (i : Fin n) → MeasureSpace ℝ := fun i => ⟨μ.restrict (s i)⟩
  have hσ : ∀ i, @SigmaFinite ℝ (ms i).toMeasurableSpace (ms i).volume :=
    fun i => inferInstanceAs (SigmaFinite (μ.restrict (s i)))
  have hi : ∀ i : Fin n, Integrable f ((ms i).volume) := fun i => hfi.restrict
  have hprod := @Integrable.fintype_prod_dep ℝ inferInstance (Fin n) inferInstance
    (fun _ => ℝ) (fun _ => f) ms hσ hi
  change Integrable (fun z : Fin n → ℝ => ∏ i, f (z i))
    (Measure.pi (fun i => μ.restrict (s i))) at hprod
  have hp := @integral_fintype_prod_eq_prod ℝ inferInstance (Fin n) inferInstance
    (fun _ => ℝ) (fun _ => f) ms hσ
  change (∫ z, ∏ i : Fin n, f (z i) ∂Measure.pi (fun i => μ.restrict (s i))) =
    ∏ i : Fin n, ∫ x, f x ∂μ.restrict (s i) at hp
  have hnonneg : ∀ z : Fin n → ℝ, 0 ≤ ∏ i, f (z i) :=
    fun z => Finset.prod_nonneg (fun i _ => hf0 (z i))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all _ hnonneg)]
  rw [hp]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0))]
  congr 1
  funext i
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ hf0)

def lowerScalarArrayLaw (B : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => lowerTwoPointLaw B)

instance lowerScalarArrayLaw_isProbability (B : ℝ) (n : ℕ) :
    IsProbabilityMeasure (lowerScalarArrayLaw B n) := by
  unfold lowerScalarArrayLaw
  infer_instance

def lowerScalarTiltedArrayLaw (B t : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => lowerTwoPointTilt B t)

instance lowerScalarTiltedArrayLaw_isProbability (B t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (lowerScalarTiltedArrayLaw B t n) := by
  unfold lowerScalarTiltedArrayLaw
  infer_instance

theorem lowerScalarTiltedArrayLaw_eq_withDensity (B t : ℝ) (n : ℕ) :
    lowerScalarTiltedArrayLaw B t n = (lowerScalarArrayLaw B n).withDensity
      (fun z => ENNReal.ofReal
        (∏ i : Fin n, Real.exp (t * z i) / mgf id (lowerTwoPointLaw B) t)) := by
  unfold lowerScalarTiltedArrayLaw lowerTwoPointTilt Measure.tilted lowerScalarArrayLaw
  apply lower_pi_withDensity (lowerTwoPointLaw B)
    ((measurable_const.mul measurable_id).exp.div_const _)
    (integrable_lowerTwoPointLaw B _) (fun x => by
      have hmgf : 0 < mgf id (lowerTwoPointLaw B) t := by
        rw [lowerTwoPointLaw_mgf]
        exact div_pos (lowerTiltNormalizer_pos B t) (lowerTwoPointDenominator_pos B)
      positivity)

end

end RectangleCLT.Companion
