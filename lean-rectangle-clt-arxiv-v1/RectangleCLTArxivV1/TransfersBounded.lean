import RectangleCLTArxivV1.IntrinsicMain
import RectangleCLTCompanion.SubexponentialBounded

/-!
# The width-dependent bounded input after marginal standardization

This module invokes the proved new bounded theorem. Positive lower
marginal variances suffice; no upper variance or rank bound is imposed.
-/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators

/-- Pointwise coordinate scaling transports the actual Gaussian maximum. -/
theorem gaussianMaximumMean_scaledFactor_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (d : Vector p) {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ j, |d j| ≤ M) :
    gaussianMaximumMean (scaledFactor d A) ≤ M * gaussianMaximumMean A := by
  unfold gaussianMaximumMean
  rw [← gaussianLaw_map_diagonalScale,
    integral_map (measurable_diagonalScale d).aemeasurable measurable_norm.aestronglyMeasurable,
    ← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
    ((gaussianLaw_integrable_norm A).const_mul M)
  apply ae_of_all
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg x))).mpr
  intro j
  change ‖d j * x j‖ ≤ M * ‖x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hd j) (norm_le_pi_norm x j) (norm_nonneg _) hM

/-- Standardizing standard deviations bounded below by one half costs at
most a factor two in Gaussian width, exactly as it does in the envelope. -/
theorem gaussianMaximumMean_standardized_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (d : Vector p)
    (hd : ∀ j, (1 / 2 : ℝ) ≤ d j) :
    gaussianMaximumMean (scaledFactor (fun j => (d j)⁻¹) A) ≤
      2 * gaussianMaximumMean A := by
  apply gaussianMaximumMean_scaledFactor_le A _ (by norm_num)
  intro j
  have hj : 0 < d j := lt_of_lt_of_le (by norm_num) (hd j)
  rw [abs_of_pos (inv_pos.mpr hj)]
  apply (inv_le_iff_one_le_mul₀ hj).mpr
  linarith [hd j]

/-- The actual new bounded theorem after marginal standardization, with
its Gaussian width retained. -/
theorem intrinsicEnvelopeCLT_after_standardization
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (d : Vector p) (hd : ∀ j, (1 / 2 : ℝ) ≤ d j)
    (hvar : ∀ j, covariance μ (sumVector ξ) j j = (d j) ^ 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
      min 1 (4 * (δ * gaussianMaximumMean A * dimensionLog p *
        Real.sqrt (D_L (2 * δ) (dimensionLog p)))) := by
  obtain ⟨hs, hu, hf⟩ := bounded_standardization_data h d hd hvar A hA
  have hb := intrinsicEnvelopeCLT μ (standardizedRows ξ d) hs hp hu
    (scaledFactor (fun j => (d j)⁻¹) A) hf
  have hg := gaussianMaximumMean_standardized_le A d hd
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hrate :
      2 * δ * gaussianMaximumMean (scaledFactor (fun j => (d j)⁻¹) A) * dimensionLog p *
        Real.sqrt (D_L (2 * δ) (dimensionLog p)) ≤
      4 * (δ * gaussianMaximumMean A * dimensionLog p *
        Real.sqrt (D_L (2 * δ) (dimensionLog p))) := by
    have hh := mul_le_mul_of_nonneg_right hg
      (mul_nonneg (mul_nonneg (by linarith [h.delta_nonneg] : 0 ≤ 2 * δ) hL)
        (Real.sqrt_nonneg (D_L (2 * δ) (dimensionLog p))))
    nlinarith only [hh]
  apply rectangleDistance_le
  intro R
  apply rectangleError_undo_standardization_le μ (sumVector ξ) d
    (fun j => lt_of_lt_of_le (by norm_num) (hd j)) A _ R
  intro Q
  have he := (rectangleError_le_rectangleDistance μ (sumVector (standardizedRows ξ d))
    (scaledFactor (fun j => (d j)⁻¹) A) Q).trans hb
  rw [sumVector_standardizedRows] at he
  exact he.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate)
    intrinsicUniversalConstant_pos.le)

/-- A positive marginal lower bound is enough for the width-dependent
bounded input used by the conditional truncation route. -/
theorem intrinsicEnvelopeCLT_of_marginal_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hlower : ∀ j, (1 / 4 : ℝ) ≤ covariance μ (sumVector ξ) j j)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ intrinsicUniversalConstant *
      min 1 (4 * (δ * gaussianMaximumMean A * dimensionLog p *
        Real.sqrt (D_L (2 * δ) (dimensionLog p)))) := by
  let d : Vector p := fun j => Real.sqrt (covariance μ (sumVector ξ) j j)
  have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j := by
    have hs := Real.sqrt_le_sqrt (hlower j)
    have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    simpa only [hquarter] using hs
  have hvar (j : Fin p) : covariance μ (sumVector ξ) j j = d j ^ 2 :=
    (Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (hlower j))).symm
  exact intrinsicEnvelopeCLT_after_standardization μ ξ h hp d hd hvar A hA

end RectangleCLTArxivV1
