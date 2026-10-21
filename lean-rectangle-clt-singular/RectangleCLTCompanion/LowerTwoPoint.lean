import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The actual skewed two-point distribution used in the lower bounds.
These finite-law identities are supporting lemmas, not the asymptotic
lower-scale or uniform-consistency theorem. -/

open MeasureTheory Set
open scoped ENNReal

namespace RectangleCLT.Companion

noncomputable section

/-- The lower-bound construction puts mass `1/(B²+1)` at `B` and its
remaining mass at `-1/B`. -/
def lowerTwoPointLaw (B : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (B ^ 2 + 1)) • Measure.dirac B +
    ENNReal.ofReal (B ^ 2 / (B ^ 2 + 1)) • Measure.dirac (-B⁻¹)

theorem lowerTwoPointDenominator_pos (B : ℝ) : 0 < B ^ 2 + 1 := by
  nlinarith [sq_nonneg B]

instance lowerTwoPointLaw_isProbability (B : ℝ) :
    IsProbabilityMeasure (lowerTwoPointLaw B) where
  measure_univ := by
    have hden := lowerTwoPointDenominator_pos B
    have hsum : 1 / (B ^ 2 + 1) + B ^ 2 / (B ^ 2 + 1) = 1 := by
      field_simp
      ring
    simp only [lowerTwoPointLaw, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), hsum]
    norm_num

theorem integrable_lowerTwoPointLaw (B : ℝ) (f : ℝ → ℝ) :
    Integrable f (lowerTwoPointLaw B) := by
  exact Integrable.add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)

theorem integral_lowerTwoPointLaw (B : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂lowerTwoPointLaw B) =
      (f B + B ^ 2 * f (-B⁻¹)) / (B ^ 2 + 1) := by
  have hden := lowerTwoPointDenominator_pos B
  rw [lowerTwoPointLaw, integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
    (show 0 ≤ 1 / (B ^ 2 + 1) by positivity), ENNReal.toReal_ofReal
    (show 0 ≤ B ^ 2 / (B ^ 2 + 1) by positivity), smul_eq_mul]
  ring

theorem lowerTwoPointLaw_centered {B : ℝ} (hB : B ≠ 0) :
    (∫ x, x ∂lowerTwoPointLaw B) = 0 := by
  rw [integral_lowerTwoPointLaw]
  field_simp
  <;> ring

theorem lowerTwoPointLaw_second {B : ℝ} (hB : B ≠ 0) :
    (∫ x, x ^ 2 ∂lowerTwoPointLaw B) = 1 := by
  rw [integral_lowerTwoPointLaw]
  field_simp
  <;> ring

theorem lowerTwoPointLaw_third {B : ℝ} (hB : B ≠ 0) :
    (∫ x, x ^ 3 ∂lowerTwoPointLaw B) = B - B⁻¹ := by
  rw [integral_lowerTwoPointLaw]
  field_simp
  <;> ring

theorem lowerTwoPointLaw_fourth {B : ℝ} (hB : B ≠ 0) :
    (∫ x, x ^ 4 ∂lowerTwoPointLaw B) = B ^ 2 - 1 + B⁻¹ ^ 2 := by
  rw [integral_lowerTwoPointLaw]
  field_simp
  <;> ring

theorem lowerTwoPointLaw_envelope {B : ℝ} (hB : 1 ≤ B) :
    ∀ᵐ x ∂lowerTwoPointLaw B, |x| ≤ B := by
  have hBpos : 0 < B := by linarith
  have hi : B⁻¹ ≤ B := (inv_le_one_of_one_le₀ hB).trans hB
  rw [lowerTwoPointLaw, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [ae_eq_dirac (id : ℝ → ℝ)] with x hx
    change x = B at hx
    rw [hx, abs_of_pos hBpos]
  · apply Measure.ae_smul_measure
    filter_upwards [ae_eq_dirac (id : ℝ → ℝ)] with x hx
    change x = -B⁻¹ at hx
    rw [hx, abs_neg, abs_of_pos (inv_pos.mpr hBpos)]
    exact hi

/-- The positive endpoint has positive mass: the envelope is attained. -/
theorem lowerTwoPointLaw_atom {B : ℝ} (hB : 0 < B) :
    (lowerTwoPointLaw B).real {B} = 1 / (B ^ 2 + 1) := by
  have hne : -B⁻¹ ≠ B := by linarith [inv_pos.mpr hB]
  simp [lowerTwoPointLaw, Measure.real, hne, ENNReal.toReal_ofReal,
    (lowerTwoPointDenominator_pos B).le]

theorem lowerTwoPointLaw_attains_envelope {B : ℝ} (hB : 0 < B) :
    0 < (lowerTwoPointLaw B).real {B} := by
  rw [lowerTwoPointLaw_atom hB]
  exact one_div_pos.mpr (lowerTwoPointDenominator_pos B)

/-- For the manuscript's `B ≥ 2`, skewness is uniformly at least `3B/4`. -/
theorem lowerTwoPointLaw_third_ge {B : ℝ} (hB : 2 ≤ B) :
    3 * B / 4 ≤ ∫ x, x ^ 3 ∂lowerTwoPointLaw B := by
  have hBpos : 0 < B := by linarith
  rw [lowerTwoPointLaw_third hBpos.ne']
  have hinv : B⁻¹ ≤ B / 4 := by
    rw [← one_div]
    apply (div_le_iff₀ hBpos).mpr
    nlinarith
  linarith

end

end RectangleCLT.Companion
