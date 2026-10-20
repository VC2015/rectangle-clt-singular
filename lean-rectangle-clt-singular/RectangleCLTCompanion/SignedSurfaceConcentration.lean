import RectangleCLTCompanion.SignedSurfaceUnion

/-! The uniform concentration input for the signed-trace proof is supplied
by the actual bounded/Kane or Gaussian distributions, including independent
shifts. No conditional-on-mask concentration assertion is used. -/

open MeasureTheory RectangleCLT.GaussianTube

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

/-- Uniform rectangle-shell concentration for a genuine vector law. -/
def UniformBoundaryConcentration {p : ℕ} (μ : Measure (Vector p)) (C η v : ℝ) : Prop :=
  ∀ s : FaceSmoother p, ∀ r : Vector p, ∀ d : ℝ, 0 < d →
    μ.real {x | x + r ∈ s.boundaryLayer d} ≤
      C * (d + η) * Real.sqrt (dimensionLog p / v)

/-- The actual bounded independent-sum law satisfies the uniform input,
with the constant from the checked Kane sensitivity proof. -/
theorem uniformBoundaryConcentration_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) :
    UniformBoundaryConcentration (μ.map (sumVector ξ)) 1073741824 δ v := by
  intro s r d hd
  have hE : MeasurableSet {x : Vector p | x + r ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const r)
  rw [Measure.real, Measure.map_apply hdata.measurable_sum hE]
  exact hdata.boundary_probability_le hp hv hdiag s r hd

/-- Independent noise can be retained in the base law without any moment
or tail condition on that noise. -/
theorem uniformBoundaryConcentration_bounded_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    UniformBoundaryConcentration
      ((μ.prod ν).map (fun z : Ω × E => sumVector ξ z.1 + R z.2)) 1073741824 δ v := by
  intro s r d hd
  have hV : Measurable (fun z : Ω × E => sumVector ξ z.1 + R z.2) :=
    (hdata.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd)
  have hE : MeasurableSet {x : Vector p | x + r ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const r)
  rw [Measure.real, Measure.map_apply hV hE]
  change (μ.prod ν).real {z | (sumVector ξ z.1 + R z.2) + r ∈ s.boundaryLayer d} ≤ _
  simpa only [add_assoc] using
    hdata.boundary_probability_independent_shift_le hp hv hdiag s ν
      (fun z => R z + r) (hR.add_const r) hd

/-- A Gaussian base, singular or nonsingular, with any independent shift. -/
theorem uniformBoundaryConcentration_gaussian_shift
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    UniformBoundaryConcentration
      (((gaussianLaw A).prod ν).map (fun z : Vector p × E => z.1 + R z.2))
        (12 * Real.exp (3 / 2 : ℝ)) 0 v := by
  intro s r d hd
  have hV : Measurable (fun z : Vector p × E => z.1 + R z.2) :=
    measurable_fst.add (hR.comp measurable_snd)
  have hE : MeasurableSet {x : Vector p | x + r ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const r)
  rw [Measure.real, Measure.map_apply hV hE]
  change ((gaussianLaw A).prod ν).real {z | (z.1 + R z.2) + r ∈ s.boundaryLayer d} ≤ _
  simpa only [add_assoc, add_zero] using
    s.gaussian_boundary_probability_independent_shift_le hp A hv hdiag ν
      (fun z => R z + r) (hR.add_const r) hd

/-- Enlarging the numerical concentration constant or the bounded-row
envelope preserves the proved probability property. -/
theorem UniformBoundaryConcentration.mono {p : ℕ}
    {μ : Measure (Vector p)} {C C' η η' v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v)
    (hC0 : 0 ≤ C) (hη0 : 0 ≤ η) (hC : C ≤ C') (hη : η ≤ η') :
    UniformBoundaryConcentration μ C' η' v := by
  intro s r d hd
  apply (hconc s r d hd).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul hC (add_le_add_left hη d) (add_nonneg hd.le hη0) (hC0.trans hC)

/-- Replacing the variance lower parameter by a smaller positive value
weakens the same actual concentration bound. -/
theorem UniformBoundaryConcentration.weaken_variance {p : ℕ}
    {μ : Measure (Vector p)} {C η v v' : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hη : 0 ≤ η) (hv' : 0 < v') (hvv' : v' ≤ v) :
    UniformBoundaryConcentration μ C η v' := by
  intro s r d hd
  apply (hconc s r d hd).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (add_nonneg hd.le hη))
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) hv' hvv'

/-- The exact sections consumed by the finite disjoint image-union bound. -/
theorem UniformBoundaryConcentration.section_bound {p : ℕ}
    {μ : Measure (Vector p)} {C η v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) (e : CommonSamples p) :
    μ.real {x | x + A.mulVec e.1 ∈ (s.randomRectangle e.2).boundaryLayer (σ * ε)} ≤
      C * (σ * ε + η) * Real.sqrt (dimensionLog p / v) :=
  hconc (s.randomRectangle e.2) (A.mulVec e.1) (σ * ε) (mul_pos hσ hε)

end
end RectangleCLT.Companion.SignedSurface
