import RectangleCLTCompanion.TiltContractionMoments
import RectangleCLTCompanion.RestorationCoefficients

/-!
# From Gaussian convolution concavity to actual covariance contraction

This module identifies the quadratic form of the concrete normalized
covariance with the actual directional moments. The final analytic input is
log-concavity of the Gaussian convolution, to be supplied by Prékopa rather
than by an assumed covariance bound.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

variable {r : ℕ}

private theorem quadratic_sub (A B : Matrix (Fin r) (Fin r) ℝ) (u : Vector r) :
    matrixQuadratic (A - B) u = matrixQuadratic A u - matrixQuadratic B u := by
  simp only [matrixQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

private theorem quadratic_smul (a : ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (u : Vector r) :
    matrixQuadratic (a • A) u = a * matrixQuadratic A u := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- The normalized actual covariance has exactly the scalar central-moment
quadratic form used by the cumulant-generating-function derivative. -/
theorem gaussian_weightCovariance_quadratic
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ g, |w g| ≤ 1)
    (hp : weightMass (standardGaussian r) w ≠ 0) (u : Vector r) :
    matrixQuadratic (weightCovariance (standardGaussian r) id w) u =
      (∫ g, w g * (faceDot u g) ^ 2 ∂standardGaussian r) / weightMass (standardGaussian r) w -
        ((∫ g, w g * faceDot u g ∂standardGaussian r) /
          weightMass (standardGaussian r) w) ^ 2 := by
  let M := weightMean (standardGaussian r) id w
  let R : Matrix (Fin r) (Fin r) ℝ := fun j k =>
    ∫ g, w g * (g j * g k) ∂standardGaussian r
  have hrep : weightCovariance (standardGaussian r) id w =
      (weightMass (standardGaussian r) w)⁻¹ • R - rankOne M := by
    ext j k
    simp only [weightCovariance, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, rankOne]
    dsimp only [R, M]
    rw [show (fun g : Vector r => w g * (g j * g k)) =
      (fun g => g j * g k * w g) by funext g; ring]
    simp only [id_eq, div_eq_mul_inv, mul_comm]
  have hraw : matrixQuadratic R u = ∫ g, w g * (faceDot u g) ^ 2 ∂standardGaussian r := by
    change matrixQuadratic (fun j k => ∫ g, (w g • rankOne g) j k ∂standardGaussian r) u = _
    rw [matrixQuadratic_integral (standardGaussian r)
      (fun g => w g • rankOne g)
      (fun j k => by simpa only [Matrix.smul_apply, smul_eq_mul, rankOne, mul_comm]
        using standardGaussian_integrable_weighted_product w hw hb j k)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g => by
      change matrixQuadratic (w g • rankOne g) u = w g * (faceDot u g) ^ 2
      rw [quadratic_smul, matrixQuadratic_rankOne_eq_square])
  have hm := weighted_linear_integral_eq_mean w hw hb hp u
  have hmean : (∫ g, w g * faceDot u g ∂standardGaussian r) /
      weightMass (standardGaussian r) w = faceDot u M := by
    rw [hm]
    exact mul_div_cancel_left₀ _ hp
  rw [hrep, quadratic_sub, quadratic_smul, hraw,
    matrixQuadratic_rankOne_eq_square, hmean]
  ring

theorem weightCovariance_isHermitian (ν : Measure (Vector r)) (w : Vector r → ℝ) :
    (weightCovariance ν id w).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext j k
  simp only [Matrix.transpose_apply, weightCovariance, id_eq]
  congr 1
  · congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g => by ring)
  · ring

/-- The actual Gaussian normalized covariance is bounded above by the
identity once the Gaussian convolution is proved log-concave. Singular
affine factors are allowed because the underlying integration is standard
Gaussian and the selector alone carries the factor. -/
theorem gaussian_weightCovariance_contraction_of_log_convolution_concave
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 < w g) (hw₁ : ∀ g, w g ≤ 1)
    (hc : ConcaveOn ℝ univ
      (fun z : Vector r => Real.log (∫ g, w (g + z) ∂standardGaussian r))) :
    (1 - weightCovariance (standardGaussian r) id w).PosSemidef := by
  refine ⟨Matrix.isHermitian_one.sub (weightCovariance_isHermitian _ w), ?_⟩
  intro u
  have hb (g : Vector r) : |w g| ≤ 1 := by rw [abs_of_pos (hw₀ g)]; exact hw₁ g
  have hp : weightMass (standardGaussian r) w ≠ 0 := by
    have h := gaussian_integral_shift_pos w hw hw₀ hw₁ 0
    simpa only [add_zero, weightMass] using h.ne'
  have hh := gaussianTilt_directional_variance_le_of_log_convolution_concave w hw hw₀ hw₁ hc u
  rw [← gaussian_weightCovariance_quadratic w hw hb hp u] at hh
  have hnorm : matrixQuadratic (1 : Matrix (Fin r) (Fin r) ℝ) u = vectorNormSq u := by
    simp [matrixQuadratic, Matrix.one_apply, vectorNormSq, pow_two]
  have hquad : matrixQuadratic (1 - weightCovariance (standardGaussian r) id w) u =
      vectorNormSq u - matrixQuadratic (weightCovariance (standardGaussian r) id w) u := by
    rw [quadratic_sub, hnorm]
  have hnonneg : 0 ≤ matrixQuadratic
      (1 - weightCovariance (standardGaussian r) id w) u := by rw [hquad]; linarith
  simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hnonneg

end

end RectangleCLT.Companion
