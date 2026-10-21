import RectangleCLT.TruncationBasic
import RectangleCLT.TruncationTailMoments

/-! The removed means are controlled by the probability of discarding an
observation and the actual summed coordinate second moments. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem truncationMean_eq_neg_discarded
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y)
    (hY1 : ∀ j, Integrable (fun ω => Y ω j) μ)
    (hcenter : ∀ j, (∫ ω, Y ω j ∂μ) = 0) (u : ℝ) (j : Fin p) :
    truncationMean μ Y u j =
      -(∫ ω, {x | ‖Y x‖ ≤ u}ᶜ.indicator (fun x => Y x j) ω ∂μ) := by
  have hA : MeasurableSet {ω | ‖Y ω‖ ≤ u} :=
    measurableSet_le hY.norm measurable_const
  have hs := integral_add_compl hA (hY1 j)
  rw [← integral_indicator hA, ← integral_indicator hA.compl, hcenter j] at hs
  unfold truncationMean
  rw [truncateVector_coordinate_eq_indicator]
  linarith

/-- Centeredness bounds the square of the removed mean by its discarded
second moment. -/
theorem truncationMean_sq_le_discarded_second [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y)
    (hY1 : ∀ j, Integrable (fun ω => Y ω j) μ)
    (hY2 : ∀ j, Integrable (fun ω => Y ω j ^ 2) μ)
    (hcenter : ∀ j, (∫ ω, Y ω j ∂μ) = 0) (u : ℝ) (j : Fin p) :
    truncationMean μ Y u j ^ 2 ≤
      ∫ ω, {x | ‖Y x‖ ≤ u}ᶜ.indicator (fun x => Y x j ^ 2) ω ∂μ := by
  have hA : MeasurableSet {ω | ‖Y ω‖ ≤ u}ᶜ :=
    (measurableSet_le hY.norm measurable_const).compl
  have hc := discarded_mean_sq_le_second_mul_probability hA (hY1 j) (hY2 j)
  have hs : 0 ≤ ∫ ω, {x | ‖Y x‖ ≤ u}ᶜ.indicator (fun x => Y x j ^ 2) ω ∂μ := by
    apply integral_nonneg
    intro ω
    by_cases hω : ω ∈ {x | ‖Y x‖ ≤ u}ᶜ <;> simp [hω, sq_nonneg]
  rw [truncationMean_eq_neg_discarded hY hY1 hcenter u j, neg_sq]
  have hprob1 : μ.real {ω | ‖Y ω‖ ≤ u}ᶜ ≤ 1 := measureReal_le_one
  exact hc.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hprob1 hs)

/-- The coordinate removed-mean error after sample normalization. -/
theorem truncationMean_normalized_sum_bound [IsFiniteMeasure μ]
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {q u : ℝ}
    (hY : ∀ i, Measurable (Y i))
    (hY1 : ∀ i j, Integrable (fun ω => Y i ω j) μ)
    (hY2 : ∀ i j, Integrable (fun ω => Y i ω j ^ 2) μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    (hsecond : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 2 ∂μ) ≤ n)
    (hq : 0 ≤ q) (hn : 0 < n)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q) :
    ∀ j, |(∑ i, truncationMean μ (Y i) u j) / Real.sqrt (n : ℝ)| ≤
      Real.sqrt (n : ℝ) * Real.sqrt q := by
  intro j
  have hA (i : Fin n) : MeasurableSet {ω | ‖Y i ω‖ ≤ u}ᶜ :=
    (measurableSet_le (hY i).norm measurable_const).compl
  have hc := discarded_mean_sum_abs_le hA (fun i => hY1 i j) (fun i => hY2 i j)
    hq (hsecond j) hprob
  have hm (i : Fin n) : truncationMean μ (Y i) u j =
      -(∫ ω, {x | ‖Y i x‖ ≤ u}ᶜ.indicator (fun x => Y i x j) ω ∂μ) :=
    truncationMean_eq_neg_discarded (hY i) (hY1 i) (hcenter i) u j
  have hmean : |∑ i, truncationMean μ (Y i) u j| ≤ n * Real.sqrt q := by
    simpa only [hm, Finset.sum_neg_distrib, abs_neg] using hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  rw [abs_div, abs_of_pos hsqrt]
  calc
    _ ≤ ((n : ℝ) * Real.sqrt q) / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right hmean hsqrt.le
    _ = Real.sqrt (n : ℝ) * Real.sqrt q := by
      apply (div_eq_iff (ne_of_gt hsqrt)).mpr
      calc
        (n : ℝ) * Real.sqrt q = (Real.sqrt (n : ℝ) ^ 2) * Real.sqrt q := by
          rw [Real.sq_sqrt hnR.le]
        _ = _ := by ring

end

end RectangleCLT
