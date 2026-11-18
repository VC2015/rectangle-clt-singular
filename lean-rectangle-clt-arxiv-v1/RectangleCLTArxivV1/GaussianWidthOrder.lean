import RectangleCLTArxivV1.GaussianCalibration

/-!
# Covariance order controls the actual Gaussian maximum

The covariance comparison is reduced to the proved finite Gaussian
Sudakov--Fernique theorem on the original signed-coordinate index. Neither
Gaussian covariance needs to be invertible or have unit diagonal.
-/

namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT
open scoped BigOperators

/-- Quadratic-form order of the actual covariances orders their Gaussian
infinity-norm means, without any spectral lower bound. -/
theorem gaussianMaximumMean_mono {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hquad : ∀ v : Vector p, matrixQuadratic (B * B.transpose) v ≤
      matrixQuadratic (A * A.transpose) v) :
    gaussianMaximumMean B ≤ gaussianMaximumMean A := by
  rw [← gaussianWidth_signedFactorRows B, ← gaussianWidth_signedFactorRows A]
  apply GenericChaining.gaussianWidth_mono_of_increment_le
  intro s t
  rw [signed_factorRows_norm_sq B t s, signed_factorRows_norm_sq A t s]
  exact hquad (signedDirection s - signedDirection t)

/-- Scaling an actual Gaussian factor scales its expected infinity norm by
the absolute scalar, including the zero factor. -/
theorem gaussianMaximumMean_smul {p : ℕ} (c : ℝ) (A : Matrix (Fin p) (Fin p) ℝ) :
    gaussianMaximumMean (c • A) = |c| * gaussianMaximumMean A := by
  unfold gaussianMaximumMean gaussianLaw
  rw [integral_map (measurable_mulVec (c • A)).aemeasurable measurable_norm.aestronglyMeasurable,
    integral_map (measurable_mulVec A).aemeasurable measurable_norm.aestronglyMeasurable]
  simp_rw [Matrix.smul_mulVec_assoc, norm_smul, Real.norm_eq_abs]
  exact integral_const_mul _ _

/-- The covariance of a square-root-scaled factor is the required scalar
multiple of the original covariance. -/
theorem sqrt_smul_factor_gram {p : ℕ} (C : ℝ) (hC : 0 ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (Real.sqrt C • A) * (Real.sqrt C • A).transpose = C • (A * A.transpose) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← pow_two, Real.sq_sqrt hC]

/-- A covariance bounded by `C Σ` has Gaussian width at most `√C g_Σ`.
The factor `C` may vanish and both covariances may be singular. -/
theorem gaussianMaximumMean_le_of_quadratic_le_smul {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ v : Vector p, matrixQuadratic (B * B.transpose) v ≤
      matrixQuadratic (C • (A * A.transpose)) v) :
    gaussianMaximumMean B ≤ Real.sqrt C * gaussianMaximumMean A := by
  have h := gaussianMaximumMean_mono (Real.sqrt C • A) B (by
    intro v
    rw [sqrt_smul_factor_gram C hC A]
    exact hquad v)
  simpa only [gaussianMaximumMean_smul, abs_of_nonneg (Real.sqrt_nonneg C)] using h

theorem matrixQuadratic_smul_real {p : ℕ} (c : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : Vector p) :
    matrixQuadratic (c • A) v = c * matrixQuadratic A v := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A version with the scalar outside the quadratic form. -/
theorem gaussianMaximumMean_le_sqrt_mul {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ v : Vector p, matrixQuadratic (B * B.transpose) v ≤
      C * matrixQuadratic (A * A.transpose) v) :
    gaussianMaximumMean B ≤ Real.sqrt C * gaussianMaximumMean A := by
  apply gaussianMaximumMean_le_of_quadratic_le_smul A B C hC
  intro v
  simpa only [matrixQuadratic_smul_real] using hquad v

end RectangleCLTArxivV1
