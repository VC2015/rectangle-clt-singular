import RectangleCLT.SubexponentialStatement
import RectangleCLT.TruncationSampleCovariance
import RectangleCLT.TruncationCovariance
import RectangleCLT.TruncationNormalizedMoments

/-! Actual covariance normalization of the truncated sub-exponential
sample, with the original covariance proxy fixed throughout. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def truncatedSampleCovariance {p n : ℕ} (μ : Measure Ω)
    (Y : Fin n → Ω → Vector p) (u : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  covariance μ (sumVector (sampleNormalizedObservations
    (fun i => centeredTruncateVector μ (Y i) u)))

def truncationStandardDeviations {p n : ℕ} (μ : Measure Ω)
    (Y : Fin n → Ω → Vector p) (u : ℝ) : Vector p :=
  fun j => Real.sqrt (truncatedSampleCovariance μ Y u j j)

/-- Covariance under coordinate division is an actual integral identity. -/
theorem covariance_coordinate_div {p : ℕ} (Y : Ω → Vector p) (d : Vector p) :
    covariance μ (fun ω j => Y ω j / d j) = normalizeCovariance (covariance μ Y) d := by
  ext j k
  simp only [covariance, normalizeCovariance, div_mul_div_comm, integral_div, ← sub_div]

theorem covariance_normalizedCenteredTruncation {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (u : ℝ) (d : Vector p) :
    covariance μ (sumVector (normalizedCenteredTruncation μ Y u d)) =
      normalizeCovariance (truncatedSampleCovariance μ Y u) d := by
  have heq : sumVector (normalizedCenteredTruncation μ Y u d) =
      (fun ω j => sumVector (sampleNormalizedObservations
        (fun i => centeredTruncateVector μ (Y i) u)) ω j / d j) := by
    funext ω j
    simp only [sumVector, Finset.sum_apply, normalizedCenteredTruncation,
      sampleNormalizedObservations]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_div, mul_comm]
  rw [heq, covariance_coordinate_div]
  rfl

namespace SubexponentialHypotheses

variable [IsProbabilityMeasure μ] {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 K : ℝ}

theorem truncated_covariance_entry_error (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q) (j k : Fin p) :
    |covariance μ (sumVector (sampleNormalizedObservations Y)) j k -
      truncatedSampleCovariance μ Y u j k| ≤ 2 * B4 * Real.sqrt q :=
  truncation_sample_covariance_error_le h.measurable h.independent h.centered h.memLp_coordinate
    (fun i j => h.integrable_coordinate_pow i j 4) h.fourth_moment_sum
    (le_trans (by norm_num) h.fourth_scale_ge_one) hq hu
    (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos) hprob j k

/-- Truncation reduces each variance, by at most `2B4 sqrt(q)`. -/
theorem truncated_covariance_diagonal_bounds (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q) (j : Fin p) :
    1 - 2 * B4 * Real.sqrt q ≤ truncatedSampleCovariance μ Y u j j ∧
      truncatedSampleCovariance μ Y u j j ≤ 1 := by
  have herr := h.truncated_covariance_entry_error hq hu hprob j j
  rw [h.unit_diagonal j] at herr
  have hdef := truncation_sample_covariance_deficit h.measurable h.independent h.centered
    h.memLp_coordinate hu (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos) j j
  rw [h.unit_diagonal j] at hdef
  have hnonneg : 0 ≤ (∑ i, ((∫ ω, {x | ‖Y i x‖ ≤ u}ᶜ.indicator
      (fun x => Y i x j * Y i x j) ω ∂μ) +
        truncationMean μ (Y i) u j * truncationMean μ (Y i) u j)) / n := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    apply add_nonneg _ (mul_self_nonneg _)
    apply integral_nonneg
    intro ω
    by_cases hω : ω ∈ {x | ‖Y i x‖ ≤ u}ᶜ <;> simp [hω, mul_self_nonneg]
  change 1 - truncatedSampleCovariance μ Y u j j = _ at hdef
  rw [← hdef] at hnonneg
  constructor
  · linarith [(abs_le.mp herr).1]
  · linarith

theorem truncationStandardDeviations_pos (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1) (j : Fin p) :
    0 < truncationStandardDeviations μ Y u j := by
  apply Real.sqrt_pos.mpr
  linarith [(h.truncated_covariance_diagonal_bounds hq hu hprob j).1]

theorem truncationStandardDeviations_sq (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1) (j : Fin p) :
    truncationStandardDeviations μ Y u j ^ 2 = truncatedSampleCovariance μ Y u j j := by
  apply Real.sq_sqrt
  exact le_of_lt (by linarith [(h.truncated_covariance_diagonal_bounds hq hu hprob j).1])

/-- The concrete centered truncated sample has square-integrable
coordinates, as required by the covariance Cauchy--Schwarz inequality. -/
theorem truncated_sample_memLp (h : SubexponentialHypotheses μ Y B4 K)
    {u : ℝ} (hu : 0 ≤ u) (j : Fin p) :
    MemLp (fun ω => sumVector (sampleNormalizedObservations
      (fun i => centeredTruncateVector μ (Y i) u)) ω j) 2 μ := by
  have hi (i : Fin n) : MemLp
      (fun ω => centeredTruncateVector μ (Y i) u ω j / Real.sqrt (n : ℝ)) 2 μ := by
    have hU : MemLp (fun ω => centeredTruncateVector μ (Y i) u ω j) 2 μ := by
      apply MemLp.of_bound
        (((measurable_pi_apply j).comp
          (measurable_centeredTruncateVector (h.measurable i) u)).aestronglyMeasurable) (2 * u)
      exact ae_of_all _ fun ω =>
        (norm_le_pi_norm (centeredTruncateVector μ (Y i) u ω) j).trans
          (norm_centeredTruncateVector_le (Y i) hu ω)
    simpa only [div_eq_mul_inv, mul_comm] using hU.const_mul ((Real.sqrt (n : ℝ))⁻¹)
  simpa only [sumVector, sampleNormalizedObservations, Finset.sum_apply] using
    memLp_finset_sum' Finset.univ (fun i _ => hi i)

/-- The normalized truncated covariance is compared to the unchanged
proxy, paying only the covariance discrepancy and twice the variance loss. -/
theorem normalized_truncation_fixed_proxy_error (h : SubexponentialHypotheses μ Y B4 K)
    (Q : Matrix (Fin p) (Fin p) ℝ) {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1) :
    proxyCovarianceDiscrepancy
      (covariance μ (sumVector (normalizedCenteredTruncation μ Y u
        (truncationStandardDeviations μ Y u)))) Q ≤
      proxyCovarianceDiscrepancy
        (covariance μ (sumVector (sampleNormalizedObservations Y))) Q +
          4 * B4 * Real.sqrt q := by
  rw [covariance_normalizedCenteredTruncation]
  have hsquare := h.truncationStandardDeviations_sq hq hu hprob hsmall
  have hcauchy : ∀ j k, |truncatedSampleCovariance μ Y u j k| ≤
      truncationStandardDeviations μ Y u j * truncationStandardDeviations μ Y u k := by
    intro j k
    exact covariance_entry_le_standard_deviations (h.truncated_sample_memLp hu) j k
  have h := normalized_covariance_fixed_proxy_discrepancy
    (covariance μ (sumVector (sampleNormalizedObservations Y)))
    (truncatedSampleCovariance μ Y u) Q (truncationStandardDeviations μ Y u)
    (mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) h.fourth_scale_ge_one))
      (Real.sqrt_nonneg _)) hsmall
    (h.truncationStandardDeviations_pos hq hu hprob hsmall)
    (fun j => by rw [hsquare j]; exact (h.truncated_covariance_diagonal_bounds hq hu hprob j).1)
    (fun j => by rw [hsquare j]; exact (h.truncated_covariance_diagonal_bounds hq hu hprob j).2)
    hcauchy (h.truncated_covariance_entry_error hq hu hprob)
  nlinarith only [h]

theorem normalized_truncation_unit_diagonal (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1) :
    ∀ j, covariance μ (sumVector (normalizedCenteredTruncation μ Y u
      (truncationStandardDeviations μ Y u))) j j = 1 := by
  rw [covariance_normalizedCenteredTruncation]
  exact normalizeCovariance_unit_diagonal _ _
    (h.truncationStandardDeviations_pos hq hu hprob hsmall)
    (h.truncationStandardDeviations_sq hq hu hprob hsmall)

theorem normalized_truncation_bounded (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    BoundedIndependentHypotheses μ (normalizedCenteredTruncation μ Y u
      (truncationStandardDeviations μ Y u)) (4 * u / Real.sqrt (n : ℝ)) := by
  have hsmall' : 2 * B4 * Real.sqrt q < 1 := by linarith
  apply boundedIndependentHypotheses_normalizedCenteredTruncation h.measurable h.independent hu
    (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos) _
    (h.truncationStandardDeviations_pos hq hu hprob hsmall')
  intro j
  rw [h.truncationStandardDeviations_sq hq hu hprob hsmall' j]
  linarith [(h.truncated_covariance_diagonal_bounds hq hu hprob j).1]

theorem normalized_truncation_gamma4 (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    gamma4 μ (normalizedCenteredTruncation μ Y u
      (truncationStandardDeviations μ Y u)) ≤ 64 * B4 ^ 2 / n := by
  have hsmall' : 2 * B4 * Real.sqrt q < 1 := by linarith
  apply gamma4_normalizedCenteredTruncation_le h.measurable
    (fun i j => by simpa only [pow_one] using h.integrable_coordinate_pow i j 1)
    (fun i j => h.integrable_coordinate_pow i j 4) h.fourth_moment_sum
    (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos) _
    (h.truncationStandardDeviations_pos hq hu hprob hsmall')
  intro j
  rw [h.truncationStandardDeviations_sq hq hu hprob hsmall' j]
  linarith [(h.truncated_covariance_diagonal_bounds hq hu hprob j).1]

theorem normalized_truncation_gamma3 (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    gamma3 μ (normalizedCenteredTruncation μ Y u
      (truncationStandardDeviations μ Y u)) ≤ 8 * B4 / Real.sqrt (n : ℝ) := by
  have hdata := h.normalized_truncation_bounded hq hu hprob hsmall
  have hsmall' : 2 * B4 * Real.sqrt q < 1 := by linarith
  refine (hdata.gamma3_le_sqrt_gamma4
    (h.normalized_truncation_unit_diagonal hq hu hprob hsmall')).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) h.fourth_scale_ge_one))
      (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (gamma4_nonneg μ _)]
  calc
    _ ≤ 64 * B4 ^ 2 / n := h.normalized_truncation_gamma4 hq hu hprob hsmall
    _ = (8 * B4 / Real.sqrt (n : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hnR.le]
      ring

/-- Coupling the original standardized sample to its actual coordinate
normalized truncation. -/
theorem normalized_truncation_coupling (h : SubexponentialHypotheses μ Y B4 K)
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    μ.real {ω | Real.sqrt (n : ℝ) * Real.sqrt q +
      (4 * B4 * Real.sqrt q) * (2 * n * u / Real.sqrt (n : ℝ)) <
        ‖sumVector (sampleNormalizedObservations Y) ω -
          sumVector (normalizedCenteredTruncation μ Y u
            (truncationStandardDeviations μ Y u)) ω‖} ≤
      (2 * n * p : ℝ) * Real.exp (-u / (2 * K)) := by
  have hB : 0 ≤ B4 := le_trans (by norm_num) h.fourth_scale_ge_one
  have hsmall' : 2 * B4 * Real.sqrt q < 1 := by linarith
  apply normalized_truncation_coupling_probability Y hu
    (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (by positivity) _ (h.truncationStandardDeviations_pos hq hu hprob hsmall')
    (truncationMean_normalized_sum_bound h.measurable
      (fun i j => by simpa only [pow_one] using h.integrable_coordinate_pow i j 1)
      (fun i j => h.integrable_coordinate_pow i j 2) h.centered
      (fun j => (h.second_moment_sum j).le) hq
      (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos) hprob) _ h.exponential_moment
  intro j
  have hsquare := h.truncationStandardDeviations_sq hq hu hprob hsmall' j
  have hd := h.truncationStandardDeviations_pos hq hu hprob hsmall' j
  have hb := h.truncated_covariance_diagonal_bounds hq hu hprob j
  have hi := standard_deviation_inverse_sub_le
    (show 0 ≤ 2 * B4 * Real.sqrt q by positivity) hsmall hd
    (by rw [hsquare]; exact hb.1) (by rw [hsquare]; exact hb.2)
  nlinarith only [hi]

end SubexponentialHypotheses

end

end RectangleCLT
