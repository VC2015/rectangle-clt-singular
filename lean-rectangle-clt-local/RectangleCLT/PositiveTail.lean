import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! An explicit one-sided moment bound for the concentration argument.
The proof uses a polynomial minorant, so it needs no distributional
approximation or regularity assumption on the random variable. -/

open MeasureTheory

namespace RectangleCLT

private theorem positive_tail_polynomial (y : ℝ) :
    y ^ 2 ≤ 1 / 4 - 32 * y + y ^ 4 / 256 +
      8192 * (if (1 : ℝ) / 256 ≤ y then 1 else 0) := by
  split_ifs with hy
  · by_cases h64 : y ≤ 64
    · have hy0 : 0 ≤ y := by linarith
      have hy2 : y ^ 2 ≤ 4096 := by nlinarith
      nlinarith [sq_nonneg (y ^ 2)]
    · have hsq : 512 ≤ y ^ 2 := by nlinarith
      have hfour : 512 * y ^ 2 ≤ y ^ 4 := by
        nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hsq)]
      nlinarith [sq_nonneg (y - 32)]
  · by_cases hy0 : y ≤ 0
    · by_cases h32 : -32 ≤ y
      · have hm : y * (y + 32) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy0 (by linarith)
        nlinarith [sq_nonneg (y ^ 2)]
      · have hsq : 256 ≤ y ^ 2 := by nlinarith
        have hfour : 256 * y ^ 2 ≤ y ^ 4 := by
          nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hsq)]
        nlinarith
    · have hsmall : y ^ 2 ≤ y / 256 := by
        nlinarith [mul_nonneg (le_of_not_ge hy0) (show 0 ≤ 1 / 256 - y by linarith)]
      nlinarith [sq_nonneg (y ^ 2)]

/-- A centered variance-one variable with fourth moment at most 32 has a
uniform positive right tail. The constants are intentionally conservative. -/
theorem positive_tail_of_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (h1 : Integrable X μ)
    (h2 : Integrable (fun ω => X ω ^ 2) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    (hvariance : (∫ ω, X ω ^ 2 ∂μ) = 1)
    (hfourth : (∫ ω, X ω ^ 4 ∂μ) ≤ 32) :
    (1 : ℝ) / 16384 ≤ μ.real {ω | (1 : ℝ) / 256 ≤ X ω} := by
  classical
  let s : Set Ω := {ω | (1 : ℝ) / 256 ≤ X ω}
  have hs : MeasurableSet s := measurableSet_le measurable_const hm
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have hbound := integral_mono_ae h2
    ((((integrable_const ((1 : ℝ) / 4)).sub (h1.const_mul 32)).add
      (h4.div_const 256)).add (hi.const_mul 8192))
    (Filter.Eventually.of_forall fun ω => by
      simpa only [s, Set.indicator, Set.mem_setOf_eq] using positive_tail_polynomial (X ω))
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  rw [integral_add (f := fun ω => (1 : ℝ) / 4 - 32 * X ω + X ω ^ 4 / 256)
      (((integrable_const ((1 : ℝ) / 4)).sub (h1.const_mul 32)).add
      (h4.div_const 256)) (hi.const_mul 8192),
    integral_add (f := fun ω => (1 : ℝ) / 4 - 32 * X ω)
      ((integrable_const ((1 : ℝ) / 4)).sub (h1.const_mul 32))
      (h4.div_const 256),
    integral_sub (integrable_const ((1 : ℝ) / 4)) (h1.const_mul 32)] at hbound
  simp only [integral_const_mul, integral_div, integral_indicator_const (1 : ℝ) hs,
    hmean, hvariance, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    mul_zero, sub_zero] at hbound
  change (1 : ℝ) / 16384 ≤ μ.real s
  linarith

/-- The same tail bound at the natural standard-deviation scale. -/
theorem positive_tail_of_fourth_moment_scaled
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hm : Measurable X) (h1 : Integrable X μ)
    (h2 : Integrable (fun ω => X ω ^ 2) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    (hvariance : (∫ ω, X ω ^ 2 ∂μ) = σ ^ 2)
    (hfourth : (∫ ω, X ω ^ 4 ∂μ) ≤ 32 * σ ^ 4) :
    (1 : ℝ) / 16384 ≤ μ.real {ω | σ / 256 ≤ X ω} := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hscaled := positive_tail_of_fourth_moment (hm.div_const σ) (h1.div_const σ)
    (by simpa only [div_pow] using h2.div_const (σ ^ 2))
    (by simpa only [div_pow] using h4.div_const (σ ^ 4))
    (by rw [integral_div, hmean, zero_div])
    (by simp only [div_pow, integral_div, hvariance, div_self (pow_ne_zero 2 hσ0)])
    (by
      simp only [div_pow, integral_div]
      exact (div_le_iff₀ (pow_pos hσ 4)).mpr hfourth)
  convert hscaled using 2
  ext ω
  simp only [Set.mem_setOf_eq, le_div_iff₀ hσ]
  ring_nf

end RectangleCLT
