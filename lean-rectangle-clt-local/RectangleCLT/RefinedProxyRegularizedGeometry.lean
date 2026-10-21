import RectangleCLT.GaussianComparisonCovariance
import RectangleCLT.GlobalCovariance
import RectangleCLT.RefinedProxyRegularization

/-! The covariance geometry of isotropic regularization. The input covariance
may be singular and need not have a positive pair gap. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

def refinedProxyRegularizedCovariance {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (1 + c)⁻¹ • (S + c • 1)

theorem refinedProxyRegularizedCovariance_apply {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (j k : Fin p) :
    refinedProxyRegularizedCovariance S c j k =
      (1 + c)⁻¹ * (S j k + c * if j = k then 1 else 0) := by
  simp [refinedProxyRegularizedCovariance, Matrix.one_apply]

theorem refinedProxyRegularizedCovariance_quadratic {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (v : Vector p) :
    matrixQuadratic (refinedProxyRegularizedCovariance S c) v =
      (1 + c)⁻¹ * (matrixQuadratic S v + c * vectorNormSq v) := by
  have hsmul (T : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
      matrixQuadratic (t • T) v = t * matrixQuadratic T v := by
    simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hadd (T U : Matrix (Fin p) (Fin p) ℝ) :
      matrixQuadratic (T + U) v = matrixQuadratic T v + matrixQuadratic U v := by
    simp only [matrixQuadratic, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  have hone : matrixQuadratic (1 : Matrix (Fin p) (Fin p) ℝ) v = vectorNormSq v := by
    simp [matrixQuadratic, vectorNormSq, Matrix.one_apply, mul_ite, ite_mul, pow_two]
  rw [refinedProxyRegularizedCovariance, hsmul, hadd, hsmul, hone]

theorem refinedProxyRegularizedCovariance_unitDiagonal {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : ∀ j, S j j = 1)
    {c : ℝ} (hc : 0 ≤ c) :
    ∀ j, refinedProxyRegularizedCovariance S c j j = 1 := by
  intro j
  rw [refinedProxyRegularizedCovariance_apply, hS j, if_pos rfl, mul_one]
  exact inv_mul_cancel₀ (by linarith : (1 : ℝ) + c ≠ 0)

theorem refinedProxyRegularizedCovariance_posSemidef {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (refinedProxyRegularizedCovariance S c).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext j k
    simp only [Matrix.transpose_apply, refinedProxyRegularizedCovariance_apply]
    rw [matrix_symmetric_of_posSemidef hS k j]
    simp only [eq_comm]
  · intro v
    have hq : 0 ≤ matrixQuadratic (refinedProxyRegularizedCovariance S c) v := by
      rw [refinedProxyRegularizedCovariance_quadratic]
      exact mul_nonneg (inv_nonneg.mpr (by linarith))
        (add_nonneg (matrixQuadratic_nonneg_of_posSemidef hS v)
          (mul_nonneg hc (vectorNormSq_nonneg v)))
    simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hq

theorem refinedProxyRegularizedCovariance_fullLower {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) (v : Vector p) :
    (c / (1 + c)) * vectorNormSq v ≤
      matrixQuadratic (refinedProxyRegularizedCovariance S c) v := by
  rw [refinedProxyRegularizedCovariance_quadratic]
  have hq := matrixQuadratic_nonneg_of_posSemidef hS v
  have hi : 0 ≤ (1 + c)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ = (1 + c)⁻¹ * (c * vectorNormSq v) := by ring
    _ ≤ (1 + c)⁻¹ * (matrixQuadratic S v + c * vectorNormSq v) :=
      mul_le_mul_of_nonneg_left (by linarith only [hq]) hi

theorem refinedProxyRegularizedCovariance_fullEigenvalue {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    c / (1 + c) ≤ fullEigenvalue (refinedProxyRegularizedCovariance S c) :=
  le_fullEigenvalue (by omega) (refinedProxyRegularizedCovariance_fullLower hS hc)

theorem refinedProxyRegularizedCovariance_half_le_fullEigenvalue {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    c / 2 ≤ fullEigenvalue (refinedProxyRegularizedCovariance S c) := by
  apply le_trans _ (refinedProxyRegularizedCovariance_fullEigenvalue hp hS hc.le)
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + c)).mpr
  nlinarith only [mul_nonneg hc.le (sub_nonneg.mpr hc1)]

theorem refinedProxyRegularizedCovariance_half_le_pairGap {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    (hdiag : ∀ j, S j j = 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    c / 2 ≤ pairGap (refinedProxyRegularizedCovariance S c) :=
  (refinedProxyRegularizedCovariance_half_le_fullEigenvalue hp hS hc hc1).trans
    (fullEigenvalue_le_pairGap (by omega)
      (refinedProxyRegularizedCovariance_posSemidef hS hc.le)
      (refinedProxyRegularizedCovariance_unitDiagonal hdiag hc.le))

theorem refinedProxyRegularizedCovariance_half_le_fullScale_sq {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    c / 2 ≤ fullCovarianceScale (refinedProxyRegularizedCovariance S c) ^ 2 := by
  rw [fullCovarianceScale_sq (by omega)
    (refinedProxyRegularizedCovariance_posSemidef hS hc.le)]
  exact refinedProxyRegularizedCovariance_half_le_fullEigenvalue hp hS hc hc1

theorem refinedProxyRegularizedCovariance_fullScale_pos {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < fullCovarianceScale (refinedProxyRegularizedCovariance S c) :=
  Real.sqrt_pos.mpr ((half_pos hc).trans_le
    (refinedProxyRegularizedCovariance_half_le_fullEigenvalue hp hS hc hc1))

theorem refinedProxyRegularizedCovariance_half_le_globalDenominator {p : ℕ}
    (hp : 1 ≤ p) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef)
    (hdiag : ∀ j, S j j = 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    c / 2 ≤ fullCovarianceScale (refinedProxyRegularizedCovariance S c) *
      Real.sqrt (pairGap (refinedProxyRegularizedCovariance S c)) :=
  regularized_global_denominator hc (Real.sqrt_nonneg _)
    (refinedProxyRegularizedCovariance_half_le_fullScale_sq hp hS hc hc1)
    (refinedProxyRegularizedCovariance_half_le_pairGap hp hS hdiag hc hc1)

end

end RectangleCLT
