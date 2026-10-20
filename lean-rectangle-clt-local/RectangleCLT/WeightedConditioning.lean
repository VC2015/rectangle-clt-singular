import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Weighted conditioning on an actual independent product experiment. This
is used to integrate localized Gaussian tube bounds once their geometric
containment in a rectangle boundary layer has been proved. -/

open MeasureTheory Set

namespace RectangleCLT

theorem integral_weighted_indicator_le
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    {ν : Measure E} {μ : Measure Ω} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {A : Set (E × Ω)} (hA : MeasurableSet A)
    {w : E → ℝ} (hw : Integrable w ν) (hw0 : ∀ e, 0 ≤ w e) {B : ℝ}
    (hsections : ∀ e, μ.real {ω | (e, ω) ∈ A} ≤ B) :
    (∫ z, w z.1 * A.indicator (fun _ => (1 : ℝ)) z ∂ν.prod μ) ≤
      B * (∫ e, w e ∂ν) := by
  classical
  have hwi : Integrable (fun z : E × Ω => w z.1) (ν.prod μ) := by
    simpa only [mul_one] using hw.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have heq : (fun z : E × Ω => w z.1 * A.indicator (fun _ => (1 : ℝ)) z) =
      A.indicator (fun z => w z.1) := by
    funext z
    by_cases hz : z ∈ A <;> simp [hz]
  have hi : Integrable (fun z : E × Ω => w z.1 * A.indicator (fun _ => (1 : ℝ)) z)
      (ν.prod μ) := by rw [heq]; exact hwi.indicator hA
  have hsection (e : E) :
      (∫ ω, w e * A.indicator (fun _ => (1 : ℝ)) (e, ω) ∂μ) =
        w e * μ.real {ω | (e, ω) ∈ A} := by
    rw [integral_const_mul]
    have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) (e, ω)) =
        {ω | (e, ω) ∈ A}.indicator (fun _ => (1 : ℝ)) := by rfl
    have hs : MeasurableSet {ω | (e, ω) ∈ A} :=
      hA.preimage (measurable_const.prodMk measurable_id)
    rw [he, integral_indicator_const (1 : ℝ) hs]
    simp
  have his : Integrable (fun e => w e * μ.real {ω | (e, ω) ∈ A}) ν := by
    have hh := hi.integral_prod_left
    simpa only [hsection] using hh
  calc
    _ = ∫ e, w e * μ.real {ω | (e, ω) ∈ A} ∂ν := by
      rw [integral_prod _ hi]
      simp_rw [hsection]
    _ ≤ ∫ e, w e * B ∂ν := integral_mono his (hw.mul_const B)
      (fun e => mul_le_mul_of_nonneg_left (hsections e) (hw0 e))
    _ = _ := by rw [integral_mul_const]; ring

end RectangleCLT
