import Kane.Cube
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Coefficients of the Bernoulli interpolation

These are the scalar identities behind equations (17) and (24) of the
rectangle CLT note. They do not assert differentiation of random variables,
translation operators, or Gaussian convolutions.
-/

namespace RectangleCLT

/-- Amplitude of a retained summand on the interpolation path. -/
def thinningScale (t : ℝ) : ℝ := 1 + t

/-- Retention probability, chosen to make the covariance decrease linearly. -/
noncomputable def thinningProbability (t : ℝ) : ℝ := (1 - t) / (1 + t) ^ 2

theorem thinningScale_pos {t : ℝ} (ht : 0 ≤ t) : 0 < thinningScale t := by
  unfold thinningScale
  linarith

theorem thinningScale_le_two {t : ℝ} (ht : t ≤ 1) : thinningScale t ≤ 2 := by
  unfold thinningScale
  linarith

theorem thinningProbability_nonneg {t : ℝ} (ht : t ≤ 1) :
    0 ≤ thinningProbability t := by
  unfold thinningProbability
  exact div_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)

theorem thinningProbability_le_one {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t ≤ 1 := by
  have hp : 0 < (1 + t) ^ 2 := sq_pos_of_pos (by linarith)
  unfold thinningProbability
  apply (div_le_one hp).mpr
  nlinarith [sq_nonneg t]

theorem thinning_covariance {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ^ 2 = 1 - t := by
  have hn : (1 + t) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by linarith))
  unfold thinningProbability thinningScale
  exact div_mul_cancel₀ _ hn

theorem thinning_third_moment {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ^ 3 = 1 - t ^ 2 := by
  have hn : 1 + t ≠ 0 := by linarith
  unfold thinningProbability thinningScale
  field_simp [hn]
  ring

theorem thinning_first_moment_factor_le_one {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ≤ 1 := by
  have hn : 0 < 1 + t := by linarith
  have heq : thinningProbability t * thinningScale t = (1 - t) / (1 + t) := by
    unfold thinningProbability thinningScale
    field_simp [ne_of_gt hn]
    ring
  rw [heq]
  apply (div_le_one hn).mpr
  linarith

theorem thinning_second_moment_factor_le_one {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ^ 2 ≤ 1 := by
  rw [thinning_covariance ht]
  linarith

@[simp] theorem thinningScale_zero : thinningScale 0 = 1 := by
  norm_num [thinningScale]

@[simp] theorem thinningProbability_zero : thinningProbability 0 = 1 := by
  norm_num [thinningProbability]

@[simp] theorem thinningProbability_one : thinningProbability 1 = 0 := by
  norm_num [thinningProbability]

theorem hasDerivAt_thinningScale (t : ℝ) :
    HasDerivAt thinningScale 1 t := by
  simpa [thinningScale] using (hasDerivAt_id t).const_add 1

theorem hasDerivAt_thinningProbability {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt thinningProbability ((t - 3) / (1 + t) ^ 3) t := by
  have hn : 1 + t ≠ 0 := by linarith
  have hd := (HasDerivAt.const_sub 1 (hasDerivAt_id t)).div
    ((hasDerivAt_thinningScale t).pow 2) (pow_ne_zero 2 hn)
  convert hd using 1
  dsimp [thinningScale]
  field_simp [hn]
  ring

/-- The factor producing the covariance cancellation in the operator expansion. -/
theorem hasDerivAt_thinning_covariance_coefficient {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt
      (fun s => (thinningProbability s * thinningScale s ^ 2) / 2) (-1 / 2) t := by
  have hn : 1 + t ≠ 0 := by linarith
  have hd := ((hasDerivAt_thinningProbability ht).mul
    ((hasDerivAt_thinningScale t).pow 2)).div_const 2
  convert hd using 1
  dsimp [thinningProbability, thinningScale]
  field_simp [hn]
  ring

/-- The factor multiplying the aggregate signed third-moment tensor. -/
theorem hasDerivAt_thinning_third_coefficient {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt
      (fun s => (thinningProbability s * thinningScale s ^ 3) / 6) (-t / 3) t := by
  have hn : 1 + t ≠ 0 := by linarith
  have hd := ((hasDerivAt_thinningProbability ht).mul
    ((hasDerivAt_thinningScale t).pow 3)).div_const 6
  convert hd using 1
  dsimp [thinningProbability, thinningScale]
  field_simp [hn]
  ring

theorem abs_thinningProbability_derivative_le_three {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(t - 3) / (1 + t) ^ 3| ≤ 3 := by
  have hp : 0 < (1 + t) ^ 3 := pow_pos (by linarith) _
  rw [abs_div, abs_of_pos hp, abs_of_nonpos (by linarith : t - 3 ≤ 0)]
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)]

end RectangleCLT
