import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverageBase
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuous

/-! The actual translated derivative supremum is measurable even when the
face projection is singular. It is a lower semicontinuous supremum of
continuous functions, with boundedness supplied by the derivative envelope. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def translatedFaceDerivativeSupremum {m r q : ℕ}
    (F : Vector r → ℝ) (U : Matrix (Fin m) (Fin r) ℝ) (ρ : ℝ)
    (z : Fin q → Vector r) (x : Vector r) : ℝ :=
  ⨆ v : {v : Vector r // faceProjectionNorm U v ≤ ρ},
    ‖iteratedFDeriv ℝ q F (x+v.val) z‖

theorem measurable_translatedFaceDerivativeSupremum {m r q : ℕ}
    (F : Vector r → ℝ) (U : Matrix (Fin m) (Fin r) ℝ) (ρ : ℝ)
    (z : Fin q → Vector r) (hcont : Continuous (iteratedFDeriv ℝ q F))
    (B : Vector r → ℝ)
    (hbound : ∀ x v, faceProjectionNorm U v ≤ ρ →
      ‖iteratedFDeriv ℝ q F (x+v) z‖ ≤ B x) :
    Measurable (translatedFaceDerivativeSupremum F U ρ z) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_ciSup
  · intro x
    refine ⟨B x, ?_⟩
    rintro y ⟨v, rfl⟩
    exact hbound x v v.property
  · intro v
    exact (((hcont.comp (continuous_id.add continuous_const)).eval continuous_const).norm).lowerSemicontinuous

theorem translatedFaceDerivativeSupremum_nonneg {m r q : ℕ}
    (F : Vector r → ℝ) (U : Matrix (Fin m) (Fin r) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (z : Fin q → Vector r) (B : Vector r → ℝ)
    (hbound : ∀ x v, faceProjectionNorm U v ≤ ρ →
      ‖iteratedFDeriv ℝ q F (x+v) z‖ ≤ B x) (x : Vector r) :
    0 ≤ translatedFaceDerivativeSupremum F U ρ z x := by
  have hzero : faceProjectionNorm U (0 : Vector r) ≤ ρ := by
    simpa only [faceProjectionNorm, Matrix.mulVec_zero, norm_zero] using hρ
  have hb : BddAbove (Set.range (fun v : {v : Vector r // faceProjectionNorm U v ≤ ρ} =>
      ‖iteratedFDeriv ℝ q F (x+v.val) z‖)) := by
    refine ⟨B x, ?_⟩
    rintro y ⟨v, rfl⟩
    exact hbound x v v.property
  exact (norm_nonneg _).trans (le_ciSup hb (⟨0, hzero⟩ : {v : Vector r // faceProjectionNorm U v ≤ ρ}))

theorem translatedFaceDerivativeSupremum_le {m r q : ℕ}
    (F : Vector r → ℝ) (U : Matrix (Fin m) (Fin r) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (z : Fin q → Vector r) (B : Vector r → ℝ)
    (hbound : ∀ x v, faceProjectionNorm U v ≤ ρ →
      ‖iteratedFDeriv ℝ q F (x+v) z‖ ≤ B x) (x : Vector r) :
    translatedFaceDerivativeSupremum F U ρ z x ≤ B x := by
  haveI : Nonempty {v : Vector r // faceProjectionNorm U v ≤ ρ} :=
    ⟨⟨0, by simpa only [faceProjectionNorm, Matrix.mulVec_zero, norm_zero] using hρ⟩⟩
  exact ciSup_le (fun v => hbound x v v.property)

/-- Genuine integrability of the supremum follows from a genuine
integrable envelope. No measurability of an uncountable supremum is assumed. -/
theorem integrable_translatedFaceDerivativeSupremum
    {Ω : Type*} [MeasurableSpace Ω] {m r q : ℕ}
    (μ : Measure Ω) (X : Ω → Vector r) (hX : Measurable X)
    (F : Vector r → ℝ) (U : Matrix (Fin m) (Fin r) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (z : Fin q → Vector r) (hcont : Continuous (iteratedFDeriv ℝ q F))
    (B : Vector r → ℝ) (hiB : Integrable (fun ω => B (X ω)) μ)
    (hbound : ∀ x v, faceProjectionNorm U v ≤ ρ →
      ‖iteratedFDeriv ℝ q F (x+v) z‖ ≤ B x) :
    Integrable (fun ω => translatedFaceDerivativeSupremum F U ρ z (X ω)) μ := by
  apply hiB.mono'
    ((measurable_translatedFaceDerivativeSupremum F U ρ z hcont B hbound).comp hX).aestronglyMeasurable
  filter_upwards [] with ω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (translatedFaceDerivativeSupremum_nonneg F U hρ z B hbound _)]
  exact translatedFaceDerivativeSupremum_le F U hρ z B hbound _

end
end RectangleCLT.Companion.SplitV4
