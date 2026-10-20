import RectangleCLTCompanion.SignedSurfaceLocalization
import RectangleCLTCompanion.GaussianConcentration
import RectangleCLT.WeightedConditioning

/-! Actual conditioning of localized tube unions. The Gaussian tail factor
is retained when integrating the bounded-base boundary concentration. -/

open MeasureTheory RectangleCLT.GaussianTube

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

/-- A measurable tube union inside both a boundary layer and a Gaussian
tail event retains the tail probability after conditioning on that Gaussian
and the auxiliary exponential samples. -/
theorem measure_subset_annulus_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (d : ℝ)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (K : Vector p → ℝ) (hK : Measurable K) (a B : ℝ)
    (hsections : ∀ e : CommonSamples p,
      μ.real {ω | V ω + A.mulVec e.1 ∈ (s.randomRectangle e.2).boundaryLayer d} ≤ B)
    (U : Set (CommonSamples p × Ω)) (hU : MeasurableSet U)
    (hsub : U ⊆ annulusEvent s A V d ∩ {z | a ≤ K z.1.1}) :
    (γ.prod μ).real U ≤ B * γ.real {e : CommonSamples p | a ≤ K e.1} := by
  classical
  let T : Set (CommonSamples p) := {e | a ≤ K e.1}
  have hT : MeasurableSet T := measurableSet_le measurable_const (hK.comp measurable_fst)
  let w : CommonSamples p → ℝ := T.indicator (fun _ => (1 : ℝ))
  have hw : Integrable w γ := (integrable_const (1 : ℝ)).indicator hT
  have hw0 (e : CommonSamples p) : 0 ≤ w e := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) e
  have hAnn := measurableSet_annulusEvent s A V hV d
  have hwp : Integrable (fun z : CommonSamples p × Ω => w z.1) (γ.prod μ) := by
    simpa only [mul_one] using hw.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hind : (fun z : CommonSamples p × Ω => w z.1 *
      (annulusEvent s A V d).indicator (fun _ => (1 : ℝ)) z) =
      (annulusEvent s A V d).indicator (fun z => w z.1) := by
    funext z
    by_cases hz : z ∈ annulusEvent s A V d <;> simp [hz]
  have hi : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (annulusEvent s A V d).indicator (fun _ => (1 : ℝ)) z) (γ.prod μ) := by
    rw [hind]
    exact hwp.indicator hAnn
  have hpoint (z : CommonSamples p × Ω) : U.indicator (fun _ => (1 : ℝ)) z ≤
      w z.1 * (annulusEvent s A V d).indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ U
    · have ha := hsub hz
      have ht : z.1 ∈ T := ha.2
      simp only [Set.indicator_of_mem hz, Set.indicator_of_mem ha.1,
        w, Set.indicator_of_mem ht, mul_one]
      exact le_rfl
    · rw [Set.indicator_of_not_mem hz]
      exact mul_nonneg (hw0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hs (e : CommonSamples p) :
      μ.real {ω | (e, ω) ∈ annulusEvent s A V d} ≤ B := by
    simpa only [annulusEvent, Set.mem_setOf_eq, add_comm] using hsections e
  have hh := integral_weighted_indicator_le hAnn hw hw0 hs
  rw [show (∫ e, w e ∂γ) = γ.real T from integral_indicator_one hT] at hh
  have hmono := integral_mono ((integrable_const (1 : ℝ)).indicator hU) hi hpoint
  have hprob : (∫ z, U.indicator (fun _ => (1 : ℝ)) z ∂γ.prod μ) = (γ.prod μ).real U := by
    exact integral_indicator_one hU
  rw [hprob] at hmono
  exact hmono.trans hh

/-- The common experiment's tail probability is exactly the Gaussian one;
the independent exponential variables contribute total mass one. -/
theorem common_gaussian_tail_probability {p : ℕ}
    (K : Vector p → ℝ) (_hK : Measurable K) (a : ℝ) :
    ((standardGaussian p).prod (exponentialRectangleLaw p)).real
      {e : CommonSamples p | a ≤ K e.1} =
      (standardGaussian p).real {g | a ≤ K g} := by
  have hset : {e : CommonSamples p | a ≤ K e.1} =
      {g : Vector p | a ≤ K g} ×ˢ Set.univ := by ext e; simp
  rw [hset, Measure.real, Measure.prod_prod, measure_univ, mul_one]
  rfl

/-- The same Gaussian tail identity for any independent law of the
threshold samples, including every positive Gamma clock. -/
theorem common_gaussian_tail_probability_of_law {p : ℕ}
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (K : Vector p → ℝ) (_hK : Measurable K) (a : ℝ) :
    ((standardGaussian p).prod τ).real {e : CommonSamples p | a ≤ K e.1} =
      (standardGaussian p).real {g | a ≤ K g} := by
  have hset : {e : CommonSamples p | a ≤ K e.1} =
      {g : Vector p | a ≤ K g} ×ˢ Set.univ := by ext e; simp
  rw [hset, Measure.real, Measure.prod_prod, measure_univ, mul_one]
  rfl

/-- Actual bounded independent rows instantiate the conditioning estimate
with the explicit Kane constant and no local-eigenvalue or gap hypothesis. -/
theorem bounded_measure_subset_annulus_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v d : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (hd : 0 < d)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (K : Vector p → ℝ) (hK : Measurable K) (a : ℝ)
    (U : Set (CommonSamples p × Ω)) (hU : MeasurableSet U)
    (hsub : U ⊆ annulusEvent s A (sumVector ξ) d ∩ {z | a ≤ K z.1.1}) :
    (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ).real U ≤
      (1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v)) *
        (standardGaussian p).real {g | a ≤ K g} := by
  have hh := measure_subset_annulus_tail_le μ s A (sumVector ξ) hdata.measurable_sum d
    ((standardGaussian p).prod (exponentialRectangleLaw p)) K hK a
    (1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v))
    (fun e => hdata.boundary_probability_le hp hv hdiag (s.randomRectangle e.2)
      (A.mulVec e.1) hd) U hU hsub
  rw [common_gaussian_tail_probability K hK a] at hh
  exact hh

/-- Arbitrary independent threshold law, with the same proved Kane cap. -/
theorem bounded_measure_subset_annulus_tail_le_of_law
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v d : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (hd : 0 < d)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (K : Vector p → ℝ) (hK : Measurable K) (a : ℝ)
    (U : Set (CommonSamples p × Ω)) (hU : MeasurableSet U)
    (hsub : U ⊆ annulusEvent s A (sumVector ξ) d ∩ {z | a ≤ K z.1.1}) :
    (((standardGaussian p).prod τ).prod μ).real U ≤
      (1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v)) *
        (standardGaussian p).real {g | a ≤ K g} := by
  have hh := measure_subset_annulus_tail_le μ s A (sumVector ξ) hdata.measurable_sum d
    ((standardGaussian p).prod τ) K hK a
    (1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v))
    (fun e => hdata.boundary_probability_le hp hv hdiag (s.randomRectangle e.2)
      (A.mulVec e.1) hd) U hU hsub
  rw [common_gaussian_tail_probability_of_law τ K hK a] at hh
  exact hh

/-- Bounded-base conditioning remains valid after adding any independent
measurable shift. No moment bound on that shift is required. -/
theorem bounded_shift_measure_subset_annulus_tail_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v d : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (hd : 0 < d)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (K : Vector p → ℝ) (hK : Measurable K) (a : ℝ)
    (U : Set (CommonSamples p × (Ω × E))) (hU : MeasurableSet U)
    (hsub : U ⊆ annulusEvent s A (fun z => sumVector ξ z.1 + R z.2) d ∩
      {z | a ≤ K z.1.1}) :
    (((standardGaussian p).prod τ).prod (μ.prod ν)).real U ≤
      (1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v)) *
        (standardGaussian p).real {g | a ≤ K g} := by
  have hV : Measurable (fun z : Ω × E => sumVector ξ z.1 + R z.2) :=
    (hdata.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd)
  have hsections (e : CommonSamples p) :
      (μ.prod ν).real {z | (sumVector ξ z.1 + R z.2) + A.mulVec e.1 ∈
        (s.randomRectangle e.2).boundaryLayer d} ≤
          1073741824 * (d + δ) * Real.sqrt (dimensionLog p / v) := by
    simpa only [add_assoc] using hdata.boundary_probability_independent_shift_le hp hv hdiag
      (s.randomRectangle e.2) ν (fun z => R z + A.mulVec e.1) (hR.add_const _) hd
  have hh := measure_subset_annulus_tail_le (μ.prod ν) s A _ hV d
    ((standardGaussian p).prod τ) K hK a _ hsections U hU hsub
  rw [common_gaussian_tail_probability_of_law τ K hK a] at hh
  exact hh

/-- Gaussian-base conditioning with an arbitrary independent shift and
threshold law. Singular Gaussian covariance is permitted. -/
theorem gaussian_shift_measure_subset_annulus_tail_le
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (G A : Matrix (Fin p) (Fin p) ℝ) {v d : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (G * G.transpose) j j = v) (hd : 0 < d)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R)
    (s : FaceSmoother p)
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (K : Vector p → ℝ) (hK : Measurable K) (a : ℝ)
    (U : Set (CommonSamples p × (Vector p × E))) (hU : MeasurableSet U)
    (hsub : U ⊆ annulusEvent s A (fun z => z.1 + R z.2) d ∩ {z | a ≤ K z.1.1}) :
    (((standardGaussian p).prod τ).prod ((gaussianLaw G).prod ν)).real U ≤
      (12 * Real.exp (3 / 2 : ℝ) * d * Real.sqrt (dimensionLog p / v)) *
        (standardGaussian p).real {g | a ≤ K g} := by
  have hV : Measurable (fun z : Vector p × E => z.1 + R z.2) :=
    measurable_fst.add (hR.comp measurable_snd)
  have hsections (e : CommonSamples p) :
      ((gaussianLaw G).prod ν).real {z | (z.1 + R z.2) + A.mulVec e.1 ∈
        (s.randomRectangle e.2).boundaryLayer d} ≤
          12 * Real.exp (3 / 2 : ℝ) * d * Real.sqrt (dimensionLog p / v) := by
    simpa only [add_assoc] using
      (s.randomRectangle e.2).gaussian_boundary_probability_independent_shift_le hp G hv hdiag
        ν (fun z => R z + A.mulVec e.1) (hR.add_const _) hd
  have hh := measure_subset_annulus_tail_le ((gaussianLaw G).prod ν) s A _ hV d
    ((standardGaussian p).prod τ) K hK a _ hsections U hU hsub
  rw [common_gaussian_tail_probability_of_law τ K hK a] at hh
  exact hh

end
end RectangleCLT.Companion.SignedSurface
