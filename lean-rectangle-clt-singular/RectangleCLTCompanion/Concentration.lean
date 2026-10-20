import RectangleCLT.BoundedConcentrationShift
import RectangleCLTCompanion.MasterReduction

/-! The companion's bounded-sum concentration input is already supplied by
the proved Kane sensitivity chain. These interfaces add probability
saturation and require no eigenvalue or correlation-gap lower bound. -/

open MeasureTheory ProbabilityTheory

namespace RectangleCLT.Companion

/-- Appendix A/C concentration for a signed coordinate face system, with an
arbitrary independent shift in the same probability space. Empty and
inconsistent face systems are allowed by `FaceSmoother`. -/
theorem bounded_boundary_concentration
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {η v d : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (R : Ω → Vector p) (hR : Measurable R)
    (hind : IndepFun (sumVector ξ) R μ) (hd : 0 < d) :
    μ.real {ω | sumVector ξ ω + R ω ∈ s.boundaryLayer d} ≤
      1073741824 * min 1 ((d + η) * Real.sqrt (dimensionLog p / v)) := by
  have hraw := h.boundary_probability_of_independent_shift_le hp hv hdiag s R hR hind hd
  have hr : 0 ≤ (d + η) * Real.sqrt (dimensionLog p / v) :=
    mul_nonneg (add_nonneg hd.le h.delta_nonneg) (Real.sqrt_nonneg _)
  have hs := saturate_rate (measureReal_le_one (μ := μ)) hr
    (by simpa only [mul_assoc] using hraw)
  norm_num at hs ⊢
  exact hs

/-- The same actual experiment on a product with an arbitrary shift law;
the shift law needs no moment or tail assumptions. -/
theorem bounded_boundary_concentration_product
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {η v d : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) (hd : 0 < d) :
    (μ.prod ν).real {z | sumVector ξ z.1 + R z.2 ∈ s.boundaryLayer d} ≤
      1073741824 * min 1 ((d + η) * Real.sqrt (dimensionLog p / v)) := by
  have hraw := h.boundary_probability_independent_shift_le hp hv hdiag s ν R hR hd
  have hr : 0 ≤ (d + η) * Real.sqrt (dimensionLog p / v) :=
    mul_nonneg (add_nonneg hd.le h.delta_nonneg) (Real.sqrt_nonneg _)
  have hs := saturate_rate (measureReal_le_one (μ := μ.prod ν)) hr
    (by simpa only [mul_assoc] using hraw)
  norm_num at hs ⊢
  exact hs

end RectangleCLT.Companion
