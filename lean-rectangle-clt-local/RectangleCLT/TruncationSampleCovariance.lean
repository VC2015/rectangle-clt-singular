import RectangleCLT.TruncationCovarianceIdentity
import RectangleCLT.TruncationMean
import RectangleCLT.SubexponentialStatement
import RectangleCLT.IndependentCovariance

/-! Covariance of the actual sample-normalized independent observations,
and the exact covariance deficit after whole-observation truncation. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem covariance_sampleNormalizedObservations
    {p n : ℕ} {Y : Fin n → Ω → Vector p}
    (hind : iIndepFun Y μ) (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    (hLp : ∀ i j, MemLp (fun ω => Y i ω j) 2 μ) (hn : 0 < n)
    (j k : Fin p) :
    covariance μ (sumVector (sampleNormalizedObservations Y)) j k =
      (∑ i, ∫ ω, Y i ω j * Y i ω k ∂μ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hind' : iIndepFun (sampleNormalizedObservations Y) μ := by
    exact hind.comp (fun _ (x : Vector p) => fun j => x j / Real.sqrt (n : ℝ))
      (fun _ => measurable_pi_lambda _ fun j => (measurable_pi_apply j).div_const _)
  have hc : ∀ i j, (∫ ω, sampleNormalizedObservations Y i ω j ∂μ) = 0 := by
    intro i j
    simp only [sampleNormalizedObservations, integral_div, hcenter, zero_div]
  have hlp (i : Fin n) (j : Fin p) :
      MemLp (fun ω => sampleNormalizedObservations Y i ω j) 2 μ := by
    simpa only [sampleNormalizedObservations, div_eq_mul_inv, mul_comm] using
      (hLp i j).const_mul ((Real.sqrt (n : ℝ))⁻¹)
  have hi (i : Fin n) (j : Fin p) :
      Integrable (fun ω => sampleNormalizedObservations Y i ω j) μ :=
    (hlp i j).integrable (by norm_num)
  have hip (i l : Fin n) (j k : Fin p) :
      Integrable (fun ω => sampleNormalizedObservations Y i ω j *
        sampleNormalizedObservations Y l ω k) μ :=
    (hlp i j).integrable_mul (hlp l k)
  rw [covariance_sum_of_centered_cross hi hip hc
    (independent_centered_cross_zero hind' hi hc) j k]
  have heq (i : Fin n) : (∫ ω, sampleNormalizedObservations Y i ω j *
      sampleNormalizedObservations Y i ω k ∂μ) =
        (∫ ω, Y i ω j * Y i ω k ∂μ) / n := by
    simp only [sampleNormalizedObservations, div_mul_div_comm, ← pow_two,
      Real.sq_sqrt hnR.le, integral_div]
  simp_rw [heq]
  rw [Finset.sum_div]

/-- Exact covariance loss for the sample-normalized centered truncation. -/
theorem truncation_sample_covariance_deficit
    {p n : ℕ} {Y : Fin n → Ω → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    (hLp : ∀ i j, MemLp (fun ω => Y i ω j) 2 μ)
    {u : ℝ} (hu : 0 ≤ u) (hn : 0 < n) (j k : Fin p) :
    covariance μ (sumVector (sampleNormalizedObservations Y)) j k -
      covariance μ (sumVector (sampleNormalizedObservations
        (fun i => centeredTruncateVector μ (Y i) u))) j k =
      (∑ i, ((∫ ω, {x | ‖Y i x‖ ≤ u}ᶜ.indicator
        (fun x => Y i x j * Y i x k) ω ∂μ) +
          truncationMean μ (Y i) u j * truncationMean μ (Y i) u k)) / n := by
  have hindU := independent_centeredTruncateVector hind u
  have hcU (i : Fin n) (j : Fin p) :
      (∫ ω, centeredTruncateVector μ (Y i) u ω j ∂μ) = 0 :=
    centeredTruncateVector_integral_zero (hY i) hu j
  have hLpU (i : Fin n) (j : Fin p) :
      MemLp (fun ω => centeredTruncateVector μ (Y i) u ω j) 2 μ := by
    apply MemLp.of_bound
      (((measurable_pi_apply j).comp (measurable_centeredTruncateVector (hY i) u)).aestronglyMeasurable)
      (2 * u)
    exact ae_of_all _ fun ω =>
      (norm_le_pi_norm (centeredTruncateVector μ (Y i) u ω) j).trans
        (norm_centeredTruncateVector_le (Y i) hu ω)
  have heq (i : Fin n) : (∫ ω, Y i ω j * Y i ω k ∂μ) -
      (∫ ω, centeredTruncateVector μ (Y i) u ω j *
        centeredTruncateVector μ (Y i) u ω k ∂μ) =
      (∫ ω, {x | ‖Y i x‖ ≤ u}ᶜ.indicator
        (fun x => Y i x j * Y i x k) ω ∂μ) +
          truncationMean μ (Y i) u j * truncationMean μ (Y i) u k := by
    have hdef := truncation_covariance_deficit (hY i)
      (fun j k => (hLp i j).integrable_mul (hLp i k)) (hcenter i) u j k
    rw [← covariance_centeredTruncateVector (hY i) hu] at hdef
    simpa only [covariance, hcenter, hcU, zero_mul, sub_zero] using hdef
  rw [covariance_sampleNormalizedObservations hind hcenter hLp hn,
    covariance_sampleNormalizedObservations hindU hcU hLpU hn,
    ← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [heq]

/-- Entrywise covariance loss is at most `2 B4 sqrt(q)`.  Only the averaged
fourth-moment condition is used, and the covariance proxy plays no role. -/
theorem truncation_sample_covariance_error_le
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 q u : ℝ}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    (hLp : ∀ i j, MemLp (fun ω => Y i ω j) 2 μ)
    (hY4 : ∀ i j, Integrable (fun ω => Y i ω j ^ 4) μ)
    (hfour : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ n * B4 ^ 2)
    (hB : 0 ≤ B4) (hq : 0 ≤ q) (hu : 0 ≤ u) (hn : 0 < n)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q) (j k : Fin p) :
    |covariance μ (sumVector (sampleNormalizedObservations Y)) j k -
      covariance μ (sumVector (sampleNormalizedObservations
        (fun i => centeredTruncateVector μ (Y i) u))) j k| ≤
      2 * B4 * Real.sqrt q := by
  let A : Fin n → Set Ω := fun i => {ω | ‖Y i ω‖ ≤ u}ᶜ
  let t : Fin n → Fin p → ℝ := fun i j =>
    ∫ ω, (A i).indicator (fun x => Y i x j ^ 2) ω ∂μ
  have hA (i : Fin n) : MeasurableSet (A i) :=
    (measurableSet_le (hY i).norm measurable_const).compl
  have hY1 (i : Fin n) (j : Fin p) : Integrable (fun ω => Y i ω j) μ :=
    (hLp i j).integrable (by norm_num)
  have hY2 (i : Fin n) (j : Fin p) : Integrable (fun ω => Y i ω j ^ 2) μ :=
    (memLp_two_iff_integrable_sq
      (((measurable_pi_apply j).comp (hY i)).aestronglyMeasurable)).mp (hLp i j)
  have htsum (j : Fin p) : (∑ i, t i j) ≤ n * B4 * Real.sqrt q :=
    discarded_second_sum_le hA (fun i => hY2 i j) (fun i => hY4 i j) hB hq (hfour j) hprob
  have hmu (i : Fin n) (j : Fin p) : truncationMean μ (Y i) u j ^ 2 ≤ t i j :=
    truncationMean_sq_le_discarded_second (hY i) (hY1 i) (hY2 i) (hcenter i) u j
  have hpair (i : Fin n) :
      |∫ ω, (A i).indicator (fun x => Y i x j * Y i x k) ω ∂μ| ≤
        (t i j + t i k) / 2 :=
    indicator_pair_integral_abs_le_second_mean (hA i) (hY2 i j) (hY2 i k)
      ((hLp i j).integrable_mul (hLp i k))
  have hmupair (i : Fin n) :
      |truncationMean μ (Y i) u j * truncationMean μ (Y i) u k| ≤
        (t i j + t i k) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|truncationMean μ (Y i) u j| - |truncationMean μ (Y i) u k|),
      sq_abs (truncationMean μ (Y i) u j), sq_abs (truncationMean μ (Y i) u k), hmu i j, hmu i k]
  have hentry (i : Fin n) :
      |(∫ ω, (A i).indicator (fun x => Y i x j * Y i x k) ω ∂μ) +
        truncationMean μ (Y i) u j * truncationMean μ (Y i) u k| ≤ t i j + t i k := by
    exact (abs_add _ _).trans (by linarith [hpair i, hmupair i])
  have hsum : |∑ i, ((∫ ω, (A i).indicator (fun x => Y i x j * Y i x k) ω ∂μ) +
      truncationMean μ (Y i) u j * truncationMean μ (Y i) u k)| ≤
        2 * n * B4 * Real.sqrt q := by
    calc
      _ ≤ ∑ i, |(∫ ω, (A i).indicator (fun x => Y i x j * Y i x k) ω ∂μ) +
          truncationMean μ (Y i) u j * truncationMean μ (Y i) u k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (t i j + t i k) := Finset.sum_le_sum fun i _ => hentry i
      _ = (∑ i, t i j) + ∑ i, t i k := Finset.sum_add_distrib
      _ ≤ 2 * n * B4 * Real.sqrt q := by linarith [htsum j, htsum k]
  rw [truncation_sample_covariance_deficit hY hind hcenter hLp hu hn j k,
    abs_div, abs_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)]
  apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
  simpa only [A] using hsum.trans_eq (by ring)

end

end RectangleCLT
