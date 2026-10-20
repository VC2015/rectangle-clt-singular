import RectangleCLT.GaussianProjectionMaximum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The dyadic shell sum in the signed surface argument is bounded by actual
Gaussian projection moments. This avoids a separate Gaussian tail oracle. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def dyadicRadius (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem sum_dyadicRadius_pow_le {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ n ∈ Finset.range N, dyadicRadius n ^ q ≤ 2 * (2 ^ N : ℝ) ^ q := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have htwo : (2 : ℝ) ≤ 2 ^ q := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq)
    have hN : 0 ≤ (2 ^ N : ℝ) ^ q := by positivity
    have hpow : dyadicRadius N ^ q = (2 ^ N : ℝ) ^ q * 2 ^ q := by
      simp only [dyadicRadius, pow_succ, mul_pow]
    calc
      _ ≤ 2 * (2 ^ N : ℝ) ^ q + dyadicRadius N ^ q := add_le_add_right ih _
      _ ≤ _ := by
        change _ ≤ 2 * dyadicRadius N ^ q
        rw [hpow]
        nlinarith [mul_le_mul_of_nonneg_right htwo hN]

theorem sum_dyadicShell_pow_le {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      if dyadicRadius n ≤ 2 * x then dyadicRadius n ^ q else 0) ≤ 2 * (2 * x) ^ q := by
  induction N with
  | zero => simp; positivity
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : dyadicRadius N ≤ 2 * x
    · have hsum : (∑ n ∈ Finset.range (N + 1),
          if dyadicRadius n ≤ 2 * x then dyadicRadius n ^ q else 0) ≤
          ∑ n ∈ Finset.range (N + 1), dyadicRadius n ^ q := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs
        · exact le_rfl
        · exact pow_nonneg (by unfold dyadicRadius; positivity) q
      rw [Finset.sum_range_succ, if_pos hN] at hsum
      rw [if_pos hN]
      calc
        _ ≤ 2 * (2 ^ (N + 1) : ℝ) ^ q := hsum.trans (sum_dyadicRadius_pow_le hq (N + 1))
        _ ≤ 2 * (2 * x) ^ q := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ (by unfold dyadicRadius; positivity : (0 : ℝ) ≤ dyadicRadius N) hN q
    · simpa only [if_neg hN, add_zero] using ih

/-- Uniform finite-prefix form; it applies to every actual nonnegative
random radius and requires only its genuine q-th moment. -/
theorem sum_dyadic_tail_masses_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → ℝ) (hK : Measurable K)
    (hK0 : ∀ z, 0 ≤ K z) {q : ℕ} (hq : 1 ≤ q)
    (hi : Integrable (fun z => (1 + K z) ^ q) μ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      dyadicRadius n ^ q * μ.real {z | dyadicRadius n / 2 - 1 ≤ K z}) ≤
      2 * 2 ^ q * ∫ z, (1 + K z) ^ q ∂μ := by
  let f : ℕ → Ω → ℝ := fun n z =>
    if dyadicRadius n ≤ 2 * (1 + K z) then dyadicRadius n ^ q else 0
  have hset (n : ℕ) : MeasurableSet {z | dyadicRadius n / 2 - 1 ≤ K z} :=
    measurableSet_le measurable_const hK
  have heq (n : ℕ) :
      f n = {z | dyadicRadius n / 2 - 1 ≤ K z}.indicator (fun _ => dyadicRadius n ^ q) := by
    funext z
    simp only [f, Set.indicator, Set.mem_setOf_eq]
    have hh : dyadicRadius n ≤ 2 * (1 + K z) ↔ dyadicRadius n / 2 - 1 ≤ K z := by
      constructor <;> intro hh <;> linarith
    simp only [hh]
  have hfi (n : ℕ) : Integrable (f n) μ := by
    rw [heq]
    exact (integrable_const _).indicator (hset n)
  have hint (n : ℕ) : ∫ z, f n z ∂μ =
      dyadicRadius n ^ q * μ.real {z | dyadicRadius n / 2 - 1 ≤ K z} := by
    rw [heq, integral_indicator_const _ (hset n)]
    simp only [smul_eq_mul, mul_comm]
  calc
    _ = ∫ z, ∑ n ∈ Finset.range N, f n z ∂μ := by
      rw [integral_finset_sum _ (fun n _ => hfi n)]
      exact Finset.sum_congr rfl (fun n _ => (hint n).symm)
    _ ≤ ∫ z, 2 * (2 * (1 + K z)) ^ q ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun n _ => hfi n))
      · simpa only [mul_pow, mul_assoc] using hi.const_mul (2 * 2 ^ q)
      · intro z
        exact sum_dyadicShell_pow_le hq (by linarith [hK0 z]) N
    _ = _ := by
      simp_rw [mul_pow, ← mul_assoc]
      exact integral_const_mul _ _

/-- The complete countable dyadic shell series, with no tail assumption. -/
theorem tsum_dyadic_tail_masses_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → ℝ) (hK : Measurable K)
    (hK0 : ∀ z, 0 ≤ K z) {q : ℕ} (hq : 1 ≤ q)
    (hi : Integrable (fun z => (1 + K z) ^ q) μ) :
    (∑' n : ℕ, dyadicRadius n ^ q * μ.real {z | dyadicRadius n / 2 - 1 ≤ K z}) ≤
      2 * 2 ^ q * ∫ z, (1 + K z) ^ q ∂μ := by
  exact Real.tsum_le_of_sum_range_le (fun n => by unfold dyadicRadius; positivity)
    (sum_dyadic_tail_masses_le μ K hK hK0 hq hi)

/-- Actual Gaussian finite-family bound for the complete shell series.
The logarithmic family-size condition is explicit and no Gaussian tail or
projection moment estimate is assumed. -/
theorem gaussian_projection_dyadic_tail_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℕ} (A : ι → Fin r → ℝ) (hA : ∀ i, (∑ j, A i j ^ 2) ≤ 1)
    {L C : ℝ} (hL : 1 ≤ L)
    (hcard : 2 * (Fintype.card ι : ℝ) ≤ Real.exp (C * L))
    {q : ℕ} (hq : 1 ≤ q) :
    (∑' n : ℕ, dyadicRadius n ^ q * (standardGaussian r).real
      {z | dyadicRadius n / 2 - 1 ≤ ‖linearProjectionFamily A z‖}) ≤
      (2 * 2 ^ q) * (Real.sqrt L) ^ q * Real.exp (C + (q + 1 : ℝ) ^ 2 / 2) := by
  let K : Vector r → ℝ := fun z => ‖linearProjectionFamily A z‖
  have hK : Measurable K := (measurable_linearProjectionFamily A).norm
  have hK0 : ∀ z, 0 ≤ K z := fun z => norm_nonneg _
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hw := projectionMaximum_weighted_moment_le A hA K hK hK0
    (d := 1) hL hcard (fun z => by simp only [one_mul]; exact le_rfl)
    (M := Real.sqrt L) le_rfl q
  have hpoint (z : Vector r) : (1 + K z) ^ q ≤
      Real.exp (K z / Real.sqrt L) * (1 + K z) ^ q := by
    have he : 1 ≤ Real.exp (K z / Real.sqrt L) :=
      Real.one_le_exp_iff.mpr (div_nonneg (hK0 z) hs.le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he
      (pow_nonneg (by linarith [hK0 z]) q)
  have hi : Integrable (fun z => (1 + K z) ^ q) (standardGaussian r) := by
    apply hw.1.mono' ((measurable_const.add hK).pow_const q).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hK0 z]) q)]
      exact hpoint z
  have hmoment : (∫ z, (1 + K z) ^ q ∂standardGaussian r) ≤
      (Real.sqrt L) ^ q * Real.exp (C + (q + 1 : ℝ) ^ 2 / 2) := by
    exact (integral_mono hi hw.1 hpoint).trans (by simpa only [one_mul] using hw.2)
  calc
    _ ≤ (2 * 2 ^ q) * ∫ z, (1 + K z) ^ q ∂standardGaussian r :=
      tsum_dyadic_tail_masses_le (standardGaussian r) K hK hK0 hq hi
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left hmoment (by positivity)).trans_eq (by ring)

end
end RectangleCLT.Companion.SignedSurface
