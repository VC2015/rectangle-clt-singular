import RectangleCLT.LocalStatement
import RectangleCLT.SubexponentialTail
import RectangleCLT.TruncationMoments

/-!
# Whole-vector truncation on the original probability space

Each observation is transformed by its own measurable vector map, so the
proof preserves independence without requiring identical distributions.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- Truncate one entire observation, using one event for all coordinates. -/
def truncateVector {p : ℕ} (u : ℝ) (x : Vector p) : Vector p :=
  if ‖x‖ ≤ u then x else 0

theorem measurable_truncateVector {p : ℕ} (u : ℝ) :
    Measurable (truncateVector (p := p) u) := by
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    measurable_id measurable_const

theorem norm_truncateVector_le {p : ℕ} {u : ℝ} (hu : 0 ≤ u) (x : Vector p) :
    ‖truncateVector u x‖ ≤ u := by
  by_cases hx : ‖x‖ ≤ u
  · simpa only [truncateVector, if_pos hx] using hx
  · simpa only [truncateVector, if_neg hx, norm_zero] using hu

theorem truncateVector_coordinate_eq_indicator {Ω : Type*} {p : ℕ}
    (Y : Ω → Vector p) (u : ℝ) (j : Fin p) :
    (fun ω => truncateVector u (Y ω) j) =
      {ω | ‖Y ω‖ ≤ u}.indicator (fun ω => Y ω j) := by
  funext ω
  by_cases hω : ‖Y ω‖ ≤ u <;> simp [truncateVector, hω]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual coordinate means removed in the truncation step. -/
def truncationMean {p : ℕ} (μ : Measure Ω) (Y : Ω → Vector p) (u : ℝ) : Vector p :=
  fun j => ∫ ω, truncateVector u (Y ω) j ∂μ

/-- The centered truncated observation, on the original probability space. -/
def centeredTruncateVector {p : ℕ} (μ : Measure Ω) (Y : Ω → Vector p)
    (u : ℝ) (ω : Ω) : Vector p :=
  truncateVector u (Y ω) - truncationMean μ Y u

theorem integrable_truncateVector_coordinate [IsFiniteMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y) {u : ℝ} (hu : 0 ≤ u)
    (j : Fin p) : Integrable (fun ω => truncateVector u (Y ω) j) μ := by
  apply (integrable_const u).mono'
    ((measurable_pi_apply j).comp ((measurable_truncateVector u).comp hY)).aestronglyMeasurable
  exact ae_of_all _ fun ω =>
    (norm_le_pi_norm (truncateVector u (Y ω)) j).trans (norm_truncateVector_le hu _)

theorem norm_truncationMean_le [IsProbabilityMeasure μ]
    {p : ℕ} (Y : Ω → Vector p) {u : ℝ} (hu : 0 ≤ u) :
    ‖truncationMean μ Y u‖ ≤ u := by
  apply (pi_norm_le_iff_of_nonneg hu).mpr
  intro j
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => truncateVector u (Y ω) j)
    (ae_of_all _ fun ω =>
      (norm_le_pi_norm (truncateVector u (Y ω)) j).trans (norm_truncateVector_le hu _))
  simpa only [truncationMean, measureReal_univ_eq_one, mul_one] using h

theorem measurable_centeredTruncateVector {p : ℕ} {Y : Ω → Vector p}
    (hY : Measurable Y) (u : ℝ) : Measurable (centeredTruncateVector μ Y u) :=
  ((measurable_truncateVector u).comp hY).sub measurable_const

theorem centeredTruncateVector_integral_zero [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y) {u : ℝ} (hu : 0 ≤ u)
    (j : Fin p) : (∫ ω, centeredTruncateVector μ Y u ω j ∂μ) = 0 := by
  change (∫ ω, truncateVector u (Y ω) j - truncationMean μ Y u j ∂μ) = 0
  rw [integral_sub (integrable_truncateVector_coordinate hY hu j) (integrable_const _)]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, truncationMean, sub_self]

theorem norm_centeredTruncateVector_le [IsProbabilityMeasure μ]
    {p : ℕ} (Y : Ω → Vector p) {u : ℝ} (hu : 0 ≤ u) (ω : Ω) :
    ‖centeredTruncateVector μ Y u ω‖ ≤ 2 * u := by
  calc
    ‖centeredTruncateVector μ Y u ω‖ ≤
        ‖truncateVector u (Y ω)‖ + ‖truncationMean μ Y u‖ := norm_sub_le _ _
    _ ≤ u + u := add_le_add (norm_truncateVector_le hu _) (norm_truncationMean_le Y hu)
    _ = 2 * u := by ring

/-- Centered truncation preserves the independence of whole observations. -/
theorem independent_centeredTruncateVector
    {p n : ℕ} {Y : Fin n → Ω → Vector p} (hY : iIndepFun Y μ) (u : ℝ) :
    iIndepFun (fun i => centeredTruncateVector μ (Y i) u) μ := by
  exact hY.comp (fun i (x : Vector p) => truncateVector u x - truncationMean μ (Y i) u)
    (fun _ => (measurable_truncateVector u).sub measurable_const)

/-- The truncated observations meet the actual bounded-independent
hypotheses used by the bounded CLT. -/
theorem boundedIndependentHypotheses_centeredTruncateVector [IsProbabilityMeasure μ]
    {p n : ℕ} {Y : Fin n → Ω → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) {u : ℝ} (hu : 0 ≤ u) :
    BoundedIndependentHypotheses μ
      (fun i => centeredTruncateVector μ (Y i) u) (2 * u) := by
  refine ⟨fun i => measurable_centeredTruncateVector (hY i) u,
    independent_centeredTruncateVector hind u,
    fun i j => centeredTruncateVector_integral_zero (hY i) hu j,
    fun i => ae_of_all _ fun ω => norm_centeredTruncateVector_le (Y i) hu ω,
    mul_nonneg (by norm_num) hu⟩

/-- Truncating the entire observation still preserves each marginal
fourth-moment bound, up to the centering factor sixteen. -/
theorem centeredTruncateVector_fourth_integral_le [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y)
    (hY1 : ∀ j, Integrable (fun ω => Y ω j) μ)
    (hY4 : ∀ j, Integrable (fun ω => Y ω j ^ 4) μ) (u : ℝ) (j : Fin p) :
    (∫ ω, centeredTruncateVector μ Y u ω j ^ 4 ∂μ) ≤
      16 * ∫ ω, Y ω j ^ 4 ∂μ := by
  have hA : MeasurableSet {ω | ‖Y ω‖ ≤ u} :=
    measurableSet_le hY.norm measurable_const
  simpa only [centeredTruncateVector, Pi.sub_apply, truncationMean,
    truncateVector_coordinate_eq_indicator] using
      centered_indicator_fourth_integral_le hA (hY1 j) (hY4 j)

end

end RectangleCLT
