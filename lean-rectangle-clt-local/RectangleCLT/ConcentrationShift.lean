import RectangleCLT.RectangleConcentration
import Mathlib.MeasureTheory.Integral.Prod

/-! Integration of the actual rectangle concentration bound over an arbitrary
independent shift. The independent experiment is modeled by the product
measure; its probability is computed by Fubini. -/

open MeasureTheory ProbabilityTheory

universe u v

namespace RectangleCLT.FaceSmoother

noncomputable section

/-- The exact boundary probability in a product experiment is the expectation
of the original boundary probability at each realized shift. -/
theorem boundary_probability_independent_shift_eq_integral
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (W : Ω → Vector p) (hW : Measurable W)
    (R : E → Vector p) (hR : Measurable R) (d : ℝ) :
    (μ.prod ν).real {z | W z.1 + R z.2 ∈ s.boundaryLayer d} =
      ∫ r, μ.real {ω | W ω + R r ∈ s.boundaryLayer d} ∂ν := by
  classical
  let A : Set (Ω × E) := {z | W z.1 + R z.2 ∈ s.boundaryLayer d}
  have hA : MeasurableSet A := (s.measurableSet_boundaryLayer d).preimage
    ((hW.comp measurable_fst).add (hR.comp measurable_snd))
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hA
  calc
    _ = ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν := by
      rw [integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one]
    _ = ∫ r, ∫ ω, A.indicator (fun _ => (1 : ℝ)) (ω, r) ∂μ ∂ν :=
      integral_prod_symm _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      have hs : MeasurableSet {ω | W ω + R r ∈ s.boundaryLayer d} :=
        (s.measurableSet_boundaryLayer d).preimage (hW.add_const (R r))
      change (∫ ω, {ω | W ω + R r ∈ s.boundaryLayer d}.indicator
        (fun _ => (1 : ℝ)) ω ∂μ) = _
      rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]

/-- Boundary probabilities under the sum's pushforward law are the actual
probabilities in the original probability space. -/
theorem boundary_probability_map
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (W : Ω → Vector p) (hW : Measurable W) (r : Vector p) (d : ℝ) :
    (μ.map W).real {z | z + r ∈ s.boundaryLayer d} =
      μ.real {ω | W ω + r ∈ s.boundaryLayer d} := by
  have hs : MeasurableSet {z : Vector p | z + r ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const r)
  simp only [Measure.real, Measure.map_apply hW hs]
  rfl

/-- A uniform deterministic-shift bound integrates over every independent
shift distribution, without any assumptions on that distribution's moments. -/
theorem boundary_probability_independent_shift_le
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (W : Ω → Vector p) (hW : Measurable W)
    (R : E → Vector p) (hR : Measurable R) (d B : ℝ)
    (hfixed : ∀ r : Vector p, μ.real {ω | W ω + r ∈ s.boundaryLayer d} ≤ B) :
    (μ.prod ν).real {z | W z.1 + R z.2 ∈ s.boundaryLayer d} ≤ B := by
  classical
  let A : Set (Ω × E) := {z | W z.1 + R z.2 ∈ s.boundaryLayer d}
  have hA : MeasurableSet A := (s.measurableSet_boundaryLayer d).preimage
    ((hW.comp measurable_fst).add (hR.comp measurable_snd))
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hA
  have heq : (fun r => ∫ ω, A.indicator (fun _ => (1 : ℝ)) (ω, r) ∂μ) =
      (fun r => μ.real {ω | W ω + R r ∈ s.boundaryLayer d}) := by
    funext r
    have hs : MeasurableSet {ω | W ω + R r ∈ s.boundaryLayer d} :=
      (s.measurableSet_boundaryLayer d).preimage (hW.add_const (R r))
    change (∫ ω, {ω | W ω + R r ∈ s.boundaryLayer d}.indicator
      (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  have hsection : Integrable (fun r => μ.real {ω | W ω + R r ∈ s.boundaryLayer d}) ν := by
    rw [← heq]
    exact hi.integral_prod_right
  rw [s.boundary_probability_independent_shift_eq_integral μ ν W hW R hR d]
  calc
    _ ≤ ∫ _r, B ∂ν := integral_mono hsection (integrable_const B) (fun r => hfixed (R r))
    _ = B := by simp

/-- The product-space result also applies to independently distributed random
variables defined on a common probability space. -/
theorem boundary_probability_of_independent_shift_le
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W R : Ω → Vector p) (hW : Measurable W) (hR : Measurable R)
    (hind : IndepFun W R μ) (d B : ℝ)
    (hfixed : ∀ r : Vector p, μ.real {ω | W ω + r ∈ s.boundaryLayer d} ≤ B) :
    μ.real {ω | W ω + R ω ∈ s.boundaryLayer d} ≤ B := by
  letI := isProbabilityMeasure_map (μ := μ) hW.aemeasurable
  letI := isProbabilityMeasure_map (μ := μ) hR.aemeasurable
  have hfixedLaw : ∀ r : Vector p, (μ.map W).real {z | z + r ∈ s.boundaryLayer d} ≤ B := by
    intro r
    rw [s.boundary_probability_map μ W hW r d]
    exact hfixed r
  have hp := s.boundary_probability_independent_shift_le (μ.map W) (μ.map R)
    id measurable_id id measurable_id d B hfixedLaw
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hR.aemeasurable).mp hind
  have hs : MeasurableSet {z : Vector p × Vector p | z.1 + z.2 ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_fst.add measurable_snd)
  change ((μ.map W).prod (μ.map R)).real
    {z : Vector p × Vector p | z.1 + z.2 ∈ s.boundaryLayer d} ≤ B at hp
  rw [← hjoint] at hp
  simpa only [Measure.real, Measure.map_apply (hW.prodMk hR) hs, Set.preimage_setOf_eq] using hp

end

end RectangleCLT.FaceSmoother
