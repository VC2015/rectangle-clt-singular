import RectangleCLT.ConcentrationFinal
import RectangleCLT.ConcentrationShift

/-! The proved bounded-sum concentration estimate with an arbitrary
independent measurable shift. -/

open MeasureTheory ProbabilityTheory

namespace RectangleCLT.BoundedIndependentHypotheses

/-- Uniform rectangle boundary concentration in the genuine independent
product experiment; the shift has no moment or regularity restrictions. -/
theorem boundary_probability_independent_shift_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p}
    {η v d : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) (hd : 0 < d) :
    (μ.prod ν).real {z | sumVector ξ z.1 + R z.2 ∈ s.boundaryLayer d} ≤
      1073741824 * (d + η) * Real.sqrt (dimensionLog p / v) :=
  s.boundary_probability_independent_shift_le μ ν (sumVector ξ) h.measurable_sum R hR d _
    (fun r => h.boundary_probability_le hp hv hdiag s r hd)

/-- The same concentration estimate for a shift on the original probability
space that is independent of the actual sum. -/
theorem boundary_probability_of_independent_shift_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p}
    {η v d : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (R : Ω → Vector p) (hR : Measurable R)
    (hind : IndepFun (sumVector ξ) R μ) (hd : 0 < d) :
    μ.real {ω | sumVector ξ ω + R ω ∈ s.boundaryLayer d} ≤
      1073741824 * (d + η) * Real.sqrt (dimensionLog p / v) :=
  s.boundary_probability_of_independent_shift_le μ (sumVector ξ) R h.measurable_sum hR hind d _
    (fun r => h.boundary_probability_le hp hv hdiag s r hd)

end RectangleCLT.BoundedIndependentHypotheses
