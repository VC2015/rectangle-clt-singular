import RectangleCLTCompanion.LowerTwoPoint
import Mathlib.Probability.Moments.Tilted
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual Esscher transforms of the lower-bound two-point law.
The formulas concern the genuine tilted probability measure and its
centered moments; they do not assume a moderate-deviation estimate. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RectangleCLT.Companion

noncomputable section

def lowerTiltNormalizer (B t : ℝ) : ℝ :=
  Real.exp (t * B) + B ^ 2 * Real.exp (t * (-B⁻¹))

theorem lowerTiltNormalizer_pos (B t : ℝ) : 0 < lowerTiltNormalizer B t := by
  unfold lowerTiltNormalizer
  positivity

def lowerTiltProbability (B t : ℝ) : ℝ :=
  Real.exp (t * B) / lowerTiltNormalizer B t

theorem lowerTiltProbability_pos (B t : ℝ) : 0 < lowerTiltProbability B t :=
  div_pos (Real.exp_pos _) (lowerTiltNormalizer_pos B t)

theorem lowerTiltProbability_le_one (B t : ℝ) : lowerTiltProbability B t ≤ 1 := by
  unfold lowerTiltProbability
  apply (div_le_one (lowerTiltNormalizer_pos B t)).mpr
  unfold lowerTiltNormalizer
  linarith [mul_nonneg (sq_nonneg B) (Real.exp_pos (t * (-B⁻¹))).le]

theorem lowerTiltProbability_lt_one {B : ℝ} (hB : B ≠ 0) (t : ℝ) :
    lowerTiltProbability B t < 1 := by
  unfold lowerTiltProbability
  apply (div_lt_one (lowerTiltNormalizer_pos B t)).mpr
  unfold lowerTiltNormalizer
  linarith [mul_pos (sq_pos_of_ne_zero hB) (Real.exp_pos (t * (-B⁻¹)))]

def lowerTwoPointTilt (B t : ℝ) : Measure ℝ :=
  (lowerTwoPointLaw B).tilted (fun x => t * x)

instance lowerTwoPointTilt_isProbability (B t : ℝ) :
    IsProbabilityMeasure (lowerTwoPointTilt B t) :=
  isProbabilityMeasure_tilted (integrable_lowerTwoPointLaw B _)

theorem integrable_lowerTwoPointTilt (B t : ℝ) (f : ℝ → ℝ) :
    Integrable f (lowerTwoPointTilt B t) := by
  exact (integrable_tilted_iff (integrable_lowerTwoPointLaw B _) f).mpr
    (integrable_lowerTwoPointLaw B _)

theorem lowerTwoPointTilt_envelope {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    ∀ᵐ x ∂lowerTwoPointTilt B t, |x| ≤ B :=
  (tilted_absolutelyContinuous (lowerTwoPointLaw B) (fun x => t * x)).ae_le
    (lowerTwoPointLaw_envelope hB)

theorem lowerTwoPointLaw_mgf (B t : ℝ) :
    mgf id (lowerTwoPointLaw B) t = lowerTiltNormalizer B t / (B ^ 2 + 1) := by
  unfold mgf
  rw [integral_lowerTwoPointLaw]
  rfl

theorem integral_lowerTwoPointTilt (B t : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂lowerTwoPointTilt B t) =
      lowerTiltProbability B t * f B +
        (1 - lowerTiltProbability B t) * f (-B⁻¹) := by
  have hd := (lowerTiltNormalizer_pos B t).ne'
  have hb := (lowerTwoPointDenominator_pos B).ne'
  unfold lowerTwoPointTilt
  change (∫ x, f x ∂(lowerTwoPointLaw B).tilted (fun x => t * id x)) = _
  rw [integral_tilted_mul_eq_mgf (X := id)]
  simp only [id_eq, smul_eq_mul]
  rw [integral_lowerTwoPointLaw, lowerTwoPointLaw_mgf]
  unfold lowerTiltProbability lowerTiltNormalizer at *
  field_simp
  <;> ring

def lowerTiltMean (B t : ℝ) : ℝ :=
  lowerTiltProbability B t * B + (1 - lowerTiltProbability B t) * (-B⁻¹)

def lowerTiltVariance (B t : ℝ) : ℝ :=
  (B + B⁻¹) ^ 2 * lowerTiltProbability B t * (1 - lowerTiltProbability B t)

def lowerTiltThird (B t : ℝ) : ℝ :=
  (B + B⁻¹) ^ 3 * lowerTiltProbability B t * (1 - lowerTiltProbability B t) *
    (1 - 2 * lowerTiltProbability B t)

def lowerTiltFourthCumulant (B t : ℝ) : ℝ :=
  (B + B⁻¹) ^ 4 * lowerTiltProbability B t * (1 - lowerTiltProbability B t) *
    (1 - 6 * lowerTiltProbability B t * (1 - lowerTiltProbability B t))

theorem lowerTwoPointTilt_mean (B t : ℝ) :
    (∫ x, x ∂lowerTwoPointTilt B t) = lowerTiltMean B t := by
  rw [integral_lowerTwoPointTilt]
  rfl

theorem lowerTwoPointTilt_centered (B t : ℝ) :
    (∫ x, x - lowerTiltMean B t ∂lowerTwoPointTilt B t) = 0 := by
  rw [integral_lowerTwoPointTilt]
  unfold lowerTiltMean
  ring

theorem lowerTwoPointTilt_variance (B t : ℝ) :
    (∫ x, (x - lowerTiltMean B t) ^ 2 ∂lowerTwoPointTilt B t) =
      lowerTiltVariance B t := by
  rw [integral_lowerTwoPointTilt]
  unfold lowerTiltMean lowerTiltVariance
  ring

theorem lowerTwoPointTilt_third (B t : ℝ) :
    (∫ x, (x - lowerTiltMean B t) ^ 3 ∂lowerTwoPointTilt B t) =
      lowerTiltThird B t := by
  rw [integral_lowerTwoPointTilt]
  unfold lowerTiltMean lowerTiltThird
  ring

theorem lowerTwoPointTilt_fourth_cumulant (B t : ℝ) :
    (∫ x, (x - lowerTiltMean B t) ^ 4 ∂lowerTwoPointTilt B t) -
      3 * lowerTiltVariance B t ^ 2 = lowerTiltFourthCumulant B t := by
  rw [integral_lowerTwoPointTilt]
  unfold lowerTiltMean lowerTiltVariance lowerTiltFourthCumulant
  ring

theorem lowerTiltMean_abs_le {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    |lowerTiltMean B t| ≤ B := by
  have hBpos : 0 < B := by linarith
  have hq0 := (lowerTiltProbability_pos B t).le
  have hq1 := lowerTiltProbability_le_one B t
  have hinv : B⁻¹ ≤ B := (inv_le_one_of_one_le₀ hB).trans hB
  unfold lowerTiltMean
  calc
    _ ≤ |lowerTiltProbability B t * B| +
        |(1 - lowerTiltProbability B t) * (-B⁻¹)| := abs_add _ _
    _ = lowerTiltProbability B t * B + (1 - lowerTiltProbability B t) * B⁻¹ := by
      rw [abs_mul, abs_of_nonneg hq0, abs_of_pos hBpos, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hq1), abs_neg, abs_of_pos (inv_pos.mpr hBpos)]
    _ ≤ lowerTiltProbability B t * B + (1 - lowerTiltProbability B t) * B :=
      add_le_add_left (mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hq1)) _
    _ = B := by ring

theorem lowerTiltVariance_pos {B : ℝ} (hB : 0 < B) (t : ℝ) :
    0 < lowerTiltVariance B t := by
  have hd : 0 < B + B⁻¹ := add_pos hB (inv_pos.mpr hB)
  exact mul_pos (mul_pos (sq_pos_of_pos hd) (lowerTiltProbability_pos B t))
    (sub_pos.mpr (lowerTiltProbability_lt_one hB.ne' t))

theorem hasDerivAt_lowerTiltProbability (B t : ℝ) :
    HasDerivAt (lowerTiltProbability B)
      ((B + B⁻¹) * lowerTiltProbability B t * (1 - lowerTiltProbability B t)) t := by
  have hplus := ((hasDerivAt_id t).mul_const B).exp
  have hminus := ((hasDerivAt_id t).mul_const (-B⁻¹)).exp
  have hden := hplus.add (hminus.const_mul (B ^ 2))
  have hh := hplus.div hden (lowerTiltNormalizer_pos B t).ne'
  convert hh using 1
  unfold lowerTiltProbability lowerTiltNormalizer
  field_simp
  <;> ring

theorem hasDerivAt_lowerTiltMean (B t : ℝ) :
    HasDerivAt (lowerTiltMean B) (lowerTiltVariance B t) t := by
  have hq := hasDerivAt_lowerTiltProbability B t
  have hh := (hq.mul_const B).add ((hasDerivAt_const t (1 : ℝ)).sub hq |>.mul_const (-B⁻¹))
  convert hh using 1
  unfold lowerTiltVariance
  ring

theorem hasDerivAt_lowerTiltVariance (B t : ℝ) :
    HasDerivAt (lowerTiltVariance B) (lowerTiltThird B t) t := by
  have hq := hasDerivAt_lowerTiltProbability B t
  have hh := ((hq.const_mul ((B + B⁻¹) ^ 2)).mul
    ((hasDerivAt_const t (1 : ℝ)).sub hq))
  convert hh using 1
  unfold lowerTiltThird
  ring

theorem hasDerivAt_lowerTiltThird (B t : ℝ) :
    HasDerivAt (lowerTiltThird B) (lowerTiltFourthCumulant B t) t := by
  have hq := hasDerivAt_lowerTiltProbability B t
  have hh := (((hq.const_mul ((B + B⁻¹) ^ 3)).mul
    ((hasDerivAt_const t (1 : ℝ)).sub hq)).mul
    ((hasDerivAt_const t (1 : ℝ)).sub (hq.const_mul 2)))
  convert hh using 1
  unfold lowerTiltFourthCumulant
  ring

end

end RectangleCLT.Companion
