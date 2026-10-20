import RectangleCLT.Statement
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centering and truncation preserve the fourth-moment scale

These are integral estimates for real random variables.  No identical-law
assumption, covariance certificate, or Gaussian approximation is an input.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The elementary fourth-power estimate used when centering. -/
theorem sub_fourth_le_eight (a b : ℝ) :
    (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have htwo : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a + b)]
  have hfour := mul_self_le_mul_self (sq_nonneg (a - b)) htwo
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

/-- Jensen's inequality at the fourth power, with the genuine expectation. -/
theorem fourth_power_integral_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, X ω ∂μ) ^ 4 ≤ ∫ ω, X ω ^ 4 ∂μ := by
  exact (show Even 4 from by decide).convexOn_pow.map_integral_le
    (continuous_id.pow 4).continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hX hX4

/-- Subtracting the mean costs at most a factor sixteen in fourth moments. -/
theorem centered_fourth_integral_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, (X ω - ∫ x, X x ∂μ) ^ 4 ∂μ) ≤
      16 * ∫ ω, X ω ^ 4 ∂μ := by
  let m : ℝ := ∫ ω, X ω ∂μ
  have hdom : Integrable (fun ω => 8 * (X ω ^ 4 + m ^ 4)) μ :=
    (hX4.add (integrable_const _)).const_mul 8
  have hc : Integrable (fun ω => (X ω - m) ^ 4) μ := by
    apply hdom.mono' ((hX.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 4)
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg ((show Even 4 from by decide).pow_nonneg (X ω - m))]
        using sub_fourth_le_eight (X ω) m
  have hbound : (∫ ω, (X ω - m) ^ 4 ∂μ) ≤
      ∫ ω, 8 * (X ω ^ 4 + m ^ 4) ∂μ :=
    integral_mono hc hdom fun ω => sub_fourth_le_eight (X ω) m
  have hm : m ^ 4 ≤ ∫ ω, X ω ^ 4 ∂μ := fourth_power_integral_le hX hX4
  have heq : (∫ ω, 8 * (X ω ^ 4 + m ^ 4) ∂μ) =
      8 * ((∫ ω, X ω ^ 4 ∂μ) + m ^ 4) := by
    rw [integral_const_mul, integral_add hX4 (integrable_const _)]
    simp
  change (∫ ω, (X ω - m) ^ 4 ∂μ) ≤ _
  rw [heq] at hbound
  linarith

/-- Cutting off on an arbitrary measurable event cannot increase a fourth
moment.  This permits one event for all coordinates of an observation. -/
theorem indicator_fourth_integral_le {X : Ω → ℝ} {A : Set Ω}
    (hA : MeasurableSet A) (hX4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, (A.indicator X ω) ^ 4 ∂μ) ≤ ∫ ω, X ω ^ 4 ∂μ := by
  have heq : (fun ω => (A.indicator X ω) ^ 4) =
      A.indicator (fun ω => X ω ^ 4) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [heq]
  apply integral_mono (hX4.indicator hA) hX4
  intro ω
  by_cases hω : ω ∈ A
  · simp [hω]
  · simpa [hω] using (show Even 4 from by decide).pow_nonneg (X ω)

/-- Fourth moments after vector-event truncation and centering. -/
theorem centered_indicator_fourth_integral_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hX : Integrable X μ) (hX4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, (A.indicator X ω - ∫ x, A.indicator X x ∂μ) ^ 4 ∂μ) ≤
      16 * ∫ ω, X ω ^ 4 ∂μ := by
  have heq : (fun ω => (A.indicator X ω) ^ 4) =
      A.indicator (fun ω => X ω ^ 4) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have hi4 : Integrable (fun ω => (A.indicator X ω) ^ 4) μ := by
    rw [heq]
    exact hX4.indicator hA
  exact (centered_fourth_integral_le (hX.indicator hA) hi4).trans
    (mul_le_mul_of_nonneg_left (indicator_fourth_integral_le hA hX4) (by norm_num))

/-- The bound is summed over observations before the maximum over coordinates.
In particular, the fourth-moment scale here is independent of the tail scale. -/
theorem centered_indicator_fourth_sum_le [IsProbabilityMeasure μ]
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {A : Fin n → Set Ω} {B4 : ℝ}
    (hA : ∀ i, MeasurableSet (A i))
    (hY : ∀ i j, Integrable (fun ω => Y i ω j) μ)
    (hY4 : ∀ i j, Integrable (fun ω => Y i ω j ^ 4) μ)
    (hfour : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ n * B4 ^ 2) :
    ∀ j, (∑ i, ∫ ω,
      ((A i).indicator (fun x => Y i x j) ω -
        ∫ x, (A i).indicator (fun x => Y i x j) x ∂μ) ^ 4 ∂μ) ≤
      16 * n * B4 ^ 2 := by
  intro j
  calc
    _ ≤ ∑ i, 16 * ∫ ω, Y i ω j ^ 4 ∂μ :=
      Finset.sum_le_sum fun i _ =>
        centered_indicator_fourth_integral_le (hA i) (hY i j) (hY4 i j)
    _ = 16 * ∑ i, ∫ ω, Y i ω j ^ 4 ∂μ := by rw [Finset.mul_sum]
    _ ≤ 16 * (n * B4 ^ 2) := mul_le_mul_of_nonneg_left (hfour j) (by norm_num)
    _ = 16 * n * B4 ^ 2 := by ring

end

end RectangleCLT
