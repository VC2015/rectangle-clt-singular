import RectangleCLT.TruncationBasic
import RectangleCLT.SubexponentialStatement

/-!
# Coupling a normalized truncated sum to the original sum

Both vectors live on the original probability space.  The coupling event
is the event that no entire observation was discarded.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The bounded summands used with the fixed proxy after coordinate
normalization of the centered truncated sum. -/
def normalizedCenteredTruncation {p n : ℕ}
    (μ : Measure Ω) (Y : Fin n → Ω → Vector p) (u : ℝ) (d : Vector p) :
    Fin n → Ω → Vector p :=
  fun i ω j => centeredTruncateVector μ (Y i) u ω j / (d j * Real.sqrt (n : ℝ))

/-- On the no-discard event, the original sum equals the centered
truncated sum plus the actual means that were removed. -/
theorem sample_normalized_sum_truncation_identity {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (u : ℝ) (ω : Ω)
    (hgood : ∀ i, ‖Y i ω‖ ≤ u) (j : Fin p) :
    sumVector (sampleNormalizedObservations Y) ω j =
      (∑ i, centeredTruncateVector μ (Y i) u ω j) / Real.sqrt (n : ℝ) +
        (∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ) := by
  simp only [sumVector, sampleNormalizedObservations, Finset.sum_apply,
    centeredTruncateVector, Pi.sub_apply, truncateVector, if_pos (hgood _)]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- A deterministic bound on the centered truncated sum. -/
theorem abs_centered_truncation_sum_le [IsProbabilityMeasure μ]
    {p n : ℕ} (Y : Fin n → Ω → Vector p) {u : ℝ} (hu : 0 ≤ u)
    (ω : Ω) (j : Fin p) :
    |∑ i, centeredTruncateVector μ (Y i) u ω j| ≤ 2 * n * u := by
  calc
    _ ≤ ∑ i, |centeredTruncateVector μ (Y i) u ω j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * u := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (centeredTruncateVector μ (Y i) u ω) j).trans
          (norm_centeredTruncateVector_le (Y i) hu ω)
    _ = 2 * n * u := by simp; ring

/-- The exact deterministic normalization error on the no-discard event.
The mean error and diagonal inverse error are explicit numerical bounds
on the actual truncation quantities. -/
theorem normalized_truncation_coupling_on_good [IsProbabilityMeasure μ]
    {p n : ℕ} (Y : Fin n → Ω → Vector p) {u r e : ℝ} (hu : 0 ≤ u)
    (hn : 0 < n) (hr : 0 ≤ r) (he : 0 ≤ e) (d : Vector p) (hd : ∀ j, 0 < d j)
    (hmean : ∀ j, |(∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ)| ≤ r)
    (hinv : ∀ j, |1 - (d j)⁻¹| ≤ e) (ω : Ω) (hgood : ∀ i, ‖Y i ω‖ ≤ u) :
    ‖sumVector (sampleNormalizedObservations Y) ω -
      sumVector (normalizedCenteredTruncation μ Y u d) ω‖ ≤
        r + e * (2 * n * u / Real.sqrt (n : ℝ)) := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hr
    (mul_nonneg he (div_nonneg (by positivity) hsqrt.le)))).mpr
  intro j
  have hid : (sumVector (sampleNormalizedObservations Y) ω -
      sumVector (normalizedCenteredTruncation μ Y u d) ω) j =
      (∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ) +
        (1 - (d j)⁻¹) *
          ((∑ i, centeredTruncateVector μ (Y i) u ω j) / Real.sqrt (n : ℝ)) := by
    rw [Pi.sub_apply, sample_normalized_sum_truncation_identity Y u ω hgood j]
    simp only [sumVector, normalizedCenteredTruncation, Finset.sum_apply, ← Finset.sum_div]
    field_simp [ne_of_gt (hd j), ne_of_gt hsqrt]
    <;> ring
  rw [Real.norm_eq_abs, hid]
  calc
    _ ≤ |(∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ)| +
        |1 - (d j)⁻¹| *
          |(∑ i, centeredTruncateVector μ (Y i) u ω j) / Real.sqrt (n : ℝ)| := by
      simpa only [abs_mul] using abs_add
        ((∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ))
        ((1 - (d j)⁻¹) *
          ((∑ i, centeredTruncateVector μ (Y i) u ω j) / Real.sqrt (n : ℝ)))
    _ ≤ r + e * (2 * n * u / Real.sqrt (n : ℝ)) := by
      apply add_le_add (hmean j)
      apply mul_le_mul (hinv j) _ (abs_nonneg _) he
      rw [abs_div, abs_of_pos hsqrt]
      exact div_le_div_of_nonneg_right (abs_centered_truncation_sum_le Y hu ω j) hsqrt.le

/-- The coupling can fail only when at least one original observation was
discarded; the sub-exponential finite union bound controls that event. -/
theorem normalized_truncation_coupling_probability [IsProbabilityMeasure μ]
    {p n : ℕ} (Y : Fin n → Ω → Vector p) {u r e K : ℝ} (hu : 0 ≤ u)
    (hn : 0 < n) (hr : 0 ≤ r) (he : 0 ≤ e) (d : Vector p) (hd : ∀ j, 0 < d j)
    (hmean : ∀ j, |(∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ)| ≤ r)
    (hinv : ∀ j, |1 - (d j)⁻¹| ≤ e)
    (htail : ∀ i j, ExponentialMomentBound μ (fun ω => Y i ω j) K) :
    μ.real {ω | r + e * (2 * n * u / Real.sqrt (n : ℝ)) <
      ‖sumVector (sampleNormalizedObservations Y) ω -
        sumVector (normalizedCenteredTruncation μ Y u d) ω‖} ≤
          (2 * n * p : ℝ) * Real.exp (-u / K) := by
  apply (measureReal_mono (μ := μ) (show
      {ω | r + e * (2 * n * u / Real.sqrt (n : ℝ)) <
        ‖sumVector (sampleNormalizedObservations Y) ω -
          sumVector (normalizedCenteredTruncation μ Y u d) ω‖} ⊆
        {ω | ∃ i, u < ‖Y i ω‖} from ?_)).trans
    (observations_norm_subexponential_tail hu htail)
  intro ω hω
  by_contra hnot
  change ¬ ∃ i, u < ‖Y i ω‖ at hnot
  push_neg at hnot
  exact (not_le_of_gt hω)
    (normalized_truncation_coupling_on_good Y hu hn hr he d hd hmean hinv ω hnot)

end

end RectangleCLT
