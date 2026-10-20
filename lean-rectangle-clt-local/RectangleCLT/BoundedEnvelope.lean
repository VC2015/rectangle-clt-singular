import RectangleCLT.ConcentrationFinal
import RectangleCLT.ConcentrationShift
import RectangleCLT.EnvelopeAveraging

/-! The smaller-envelope averaging estimate for actual independent bounded
sums, with all concentration and random-rectangle premises discharged. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT

namespace FaceSmoother

theorem mem_outerSet_iff_score {p : ℕ} (s : FaceSmoother p) (d : ℝ) (x : Vector p) :
    x ∈ s.outerSet d ↔ ∀ f ∈ s.faces, s.faceScore f x ≤ d := by
  simp only [outerSet, mem_setOf_eq, faceScore]
  constructor <;> intro h f hf <;> have hh := h f hf <;> linarith

theorem mem_boundaryLayer_iff_score {p : ℕ} (s : FaceSmoother p) (d : ℝ) (x : Vector p) :
    x ∈ s.boundaryLayer d ↔
      (∀ f ∈ s.faces, s.faceScore f x ≤ d) ∧
        ¬(∀ f ∈ s.faces, s.faceScore f x ≤ -d) := by
  simp only [boundaryLayer, mem_diff, mem_outerSet_iff_score]

end FaceSmoother

namespace BoundedIndependentHypotheses

theorem integral_smallerEnvelope_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (r : Vector p) :
    (∫ ω, s.F (sumVector ξ ω + r) * (1 - s.F (sumVector ξ ω + r)) ∂μ) ≤
      2147483648 * (s.bandwidth + η) * Real.sqrt (dimensionLog p / v) := by
  let W := fun ω => sumVector ξ ω + r
  have hW : Measurable W := h.measurable_sum.add_const r
  let ν := μ.map W
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hW.aemeasurable
  let a := s.bandwidth * Real.log 2
  have ha : 0 < a := mul_pos s.bandwidth_pos (Real.log_pos (by norm_num))
  have hbound (t : FaceSmoother p) :
      ν.real {x | (∀ f ∈ t.faces, t.faceScore f x ≤ a) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -a)} ≤
          1073741824 * (a + η) * Real.sqrt (dimensionLog p / v) := by
    have hset : {x | (∀ f ∈ t.faces, t.faceScore f x ≤ a) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -a)} = t.boundaryLayer a := by
      ext x
      exact (t.mem_boundaryLayer_iff_score a x).symm
    rw [hset]
    change (μ.map W).real (t.boundaryLayer a) ≤ _
    rw [Measure.real, Measure.map_apply hW (t.measurableSet_boundaryLayer a)]
    exact h.boundary_probability_le hp hv hdiag t r ha
  have hh := s.integral_smallerEnvelope_le_of_boundary ν hbound
  rw [integral_map hW.aemeasurable
    (s.continuous_F.mul (continuous_const.sub s.continuous_F)).measurable.aestronglyMeasurable] at hh
  have hal : a ≤ s.bandwidth := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_left hh s.bandwidth_pos.le]
  have hR : 0 ≤ Real.sqrt (dimensionLog p / v) := Real.sqrt_nonneg _
  change (∫ ω, s.F (sumVector ξ ω + r) * (1 - s.F (sumVector ξ ω + r)) ∂μ) ≤ _ at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hal) hR]

end BoundedIndependentHypotheses

end RectangleCLT
