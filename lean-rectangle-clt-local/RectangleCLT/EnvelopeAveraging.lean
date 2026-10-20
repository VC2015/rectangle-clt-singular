import RectangleCLT.ExponentialMixture
import RectangleCLT.RandomResampling

/-! The smaller envelope is controlled by a finite difference of two
actual rectangle smoothers. The exponential-mixture law then lets a boundary
concentration estimate be averaged without replacing it by an oracle. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- Add the same offset to each active face. -/
def shiftOffsets (t : ℝ) : FaceSmoother p where
  faces := s.faces
  offsets f := s.offsets f + t
  bandwidth := s.bandwidth
  bandwidth_pos := s.bandwidth_pos

theorem shiftOffsets_weight (t : ℝ) (x : Fin p → ℝ) (f : Face p) :
    ((s.shiftOffsets t).weights x).weight f =
      Real.exp (-t / s.bandwidth) * (s.weights x).weight f := by
  classical
  by_cases hf : f ∈ s.faces
  · simp only [weights, shiftOffsets, hf, ↓reduceIte, faceScore]
    rw [show (normalDot f x - (s.offsets f + t)) / s.bandwidth =
      -t / s.bandwidth + (normalDot f x - s.offsets f) / s.bandwidth by ring,
      Real.exp_add]
  · simp [weights, shiftOffsets, hf]

theorem shiftOffsets_T (t : ℝ) (x : Fin p → ℝ) :
    ((s.shiftOffsets t).weights x).T =
      Real.exp (-t / s.bandwidth) * (s.weights x).T := by
  simp only [FaceWeights.T, shiftOffsets_weight, Finset.mul_sum]

theorem shiftOffsets_F (t : ℝ) (x : Fin p → ℝ) :
    (s.shiftOffsets t).F x =
      1 / (1 + Real.exp (-t / s.bandwidth) * (s.weights x).T) := by
  simp only [F, FaceWeights.F, shiftOffsets_T]

theorem shiftOffsets_randomRectangle (t : ℝ) (e : ℝ × (Face p → ℝ)) :
    (s.shiftOffsets t).randomRectangle e = (s.randomRectangle e).shiftOffsets t := by
  unfold randomRectangle shiftOffsets
  congr 1
  funext f
  ring

theorem shiftOffsets_Inside_iff (t : ℝ) (x : Fin p → ℝ) :
    (s.shiftOffsets t).Inside x ↔ ∀ f ∈ s.faces, s.faceScore f x ≤ t := by
  simp only [Inside, faceScore, shiftOffsets]
  constructor <;> intro h f hf <;> have hh := h f hf <;> linarith

private theorem logistic_finite_difference {T : ℝ} (hT : 0 ≤ T) :
    1 / (1 + T) * (1 - 1 / (1 + T)) ≤
      2 * (1 / (1 + T / 2) - 1 / (1 + 2 * T)) := by
  have h1 : 0 < 1 + T := by positivity
  have h2 : 0 < 1 + T / 2 := by positivity
  have h3 : 0 < 1 + 2 * T := by positivity
  have hl : 1 / (1 + T) * (1 - 1 / (1 + T)) = T / (1 + T) ^ 2 := by
    field_simp [h1.ne']
    left
    ring
  have hr : 2 * (1 / (1 + T / 2) - 1 / (1 + 2 * T)) =
      6 * T / ((2 + T) * (1 + 2 * T)) := by
    field_simp
    ring
  rw [hl, hr, div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos (by positivity) h3)]
  nlinarith [sq_nonneg T, mul_nonneg hT (sq_nonneg T)]

/-- A concrete two-point bound avoids integration in the offset parameter. -/
theorem smallerEnvelope_le_finite_difference (x : Fin p → ℝ) :
    s.F x * (1 - s.F x) ≤
      2 * ((s.shiftOffsets (s.bandwidth * Real.log 2)).F x -
        (s.shiftOffsets (-s.bandwidth * Real.log 2)).F x) := by
  rw [shiftOffsets_F, shiftOffsets_F]
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hbw : s.bandwidth ≠ 0 := ne_of_gt s.bandwidth_pos
  have hp : -(s.bandwidth * Real.log 2) / s.bandwidth = -Real.log 2 := by
    field_simp
    ring
  have hm : -(-s.bandwidth * Real.log 2) / s.bandwidth = Real.log 2 := by
    field_simp
  rw [hp, hm, Real.exp_neg, Real.exp_log hpos, inv_eq_one_div]
  simpa only [F, FaceWeights.F, one_div_mul_eq_div] using
    logistic_finite_difference (s.weights x).T_nonneg

/-- Boundary concentration for actual rectangles implies averaging of the
smaller envelope. The hypothesis is stated as an explicit probability bound;
it is discharged separately for independent sums and for Gaussian bases. -/
theorem integral_smallerEnvelope_le_of_boundary
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] {M : ℝ}
    (hboundary : ∀ r : FaceSmoother p,
      μ.real {x | (∀ f ∈ r.faces, r.faceScore f x ≤ s.bandwidth * Real.log 2) ∧
        ¬(∀ f ∈ r.faces, r.faceScore f x ≤ -(s.bandwidth * Real.log 2))} ≤ M) :
    (∫ x, s.F x * (1 - s.F x) ∂μ) ≤ 2 * M := by
  let a := s.bandwidth * Real.log 2
  have ha : 0 ≤ a := mul_nonneg s.bandwidth_pos.le (Real.log_nonneg (by norm_num))
  have hiF (r : FaceSmoother p) : Integrable r.F μ := by
    apply (integrable_const (1 : ℝ)).mono' r.continuous_F.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall r.norm_F_le_one
  have hiEnv : Integrable (fun x => s.F x * (1 - s.F x)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.mul (continuous_const.sub s.continuous_F)).measurable.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (s.F_pos x).le (by linarith [s.F_le_one x]))]
    nlinarith [s.F_le_one x, sq_nonneg (s.F x)]
  have hiDiff : Integrable
      (fun x => 2 * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x)) μ :=
    (((hiF (s.shiftOffsets a)).sub (hiF (s.shiftOffsets (-a)))).const_mul 2)
  have hpoint := integral_mono_ae hiEnv hiDiff
    (Filter.Eventually.of_forall fun x => by
      simpa only [a, neg_mul] using s.smallerEnvelope_le_finite_difference x)
  have heq : (∫ x, 2 * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x) ∂μ) =
      2 * ∫ e, (μ.real {x | ((s.shiftOffsets a).randomRectangle e).Inside x} -
        μ.real {x | ((s.shiftOffsets (-a)).randomRectangle e).Inside x})
        ∂exponentialRectangleLaw p := by
    rw [integral_const_mul, integral_sub (hiF _) (hiF _),
      integral_F_eq_randomRectangle_average, integral_F_eq_randomRectangle_average,
      integral_sub ((s.shiftOffsets a).integrable_randomRectangle_probability μ)
        ((s.shiftOffsets (-a)).integrable_randomRectangle_probability μ)]
  rw [heq] at hpoint
  have hbound : ∀ e : ℝ × (Face p → ℝ),
      μ.real {x | ((s.shiftOffsets a).randomRectangle e).Inside x} -
        μ.real {x | ((s.shiftOffsets (-a)).randomRectangle e).Inside x} ≤ M := by
    intro e
    simp only [shiftOffsets_randomRectangle]
    have hsub : {x | ((s.randomRectangle e).shiftOffsets (-a)).Inside x} ⊆
        {x | ((s.randomRectangle e).shiftOffsets a).Inside x} := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      rw [shiftOffsets_Inside_iff] at hx ⊢
      intro f hf
      exact (hx f hf).trans (by linarith)
    rw [← measureReal_diff hsub ((s.randomRectangle e).shiftOffsets (-a)).measurableSet_Inside]
    have hset : {x | ((s.randomRectangle e).shiftOffsets a).Inside x} \
        {x | ((s.randomRectangle e).shiftOffsets (-a)).Inside x} =
        {x | (∀ f ∈ (s.randomRectangle e).faces, (s.randomRectangle e).faceScore f x ≤ a) ∧
          ¬(∀ f ∈ (s.randomRectangle e).faces, (s.randomRectangle e).faceScore f x ≤ -a)} := by
      ext x
      simp only [mem_diff, mem_setOf_eq, shiftOffsets_Inside_iff]
    rw [hset]
    exact hboundary (s.randomRectangle e)
  have hh := integral_mono_ae
    (((s.shiftOffsets a).integrable_randomRectangle_probability μ).sub
      ((s.shiftOffsets (-a)).integrable_randomRectangle_probability μ))
    (integrable_const M) (Filter.Eventually.of_forall hbound)
  simp only [Pi.sub_apply, integral_const, measureReal_univ_eq_one, one_smul] at hh
  linarith

end RectangleCLT.FaceSmoother
