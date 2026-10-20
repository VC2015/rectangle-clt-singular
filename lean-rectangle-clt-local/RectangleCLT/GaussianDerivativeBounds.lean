import RectangleCLT.GaussianDerivativeScaling
import RectangleCLT.GaussianThirdAssembly
import RectangleCLT.Optimization

/-! Concrete variance-time forms of the Gaussian derivative estimates. -/

open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

private theorem sqrt_cube_eq_rpow {v : ℝ} (hv : 0 ≤ v) :
    (Real.sqrt v) ^ 3 = v ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hv (1 / 2 : ℝ) 3]
  norm_num

private theorem third_variance_bound_of_normalized_bound
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {v C cost : ℝ} (hv : 0 < v)
    (hunit : (∑ j, ∑ k, ∑ l,
      |(s.scaleDown (Real.sqrt v) (Real.sqrt_pos.mpr hv)).convolutionThirdDerivative
        (gaussianLaw A) ((Real.sqrt v)⁻¹ • x) j k l|) ≤
      C * (Real.sqrt (dimensionLog p)) ^ 3 / cost) :
    (∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt v • A)) x j k l|) ≤
      C * (dimensionLog p) ^ (3 / 2 : ℝ) / (cost * v ^ (3 / 2 : ℝ)) := by
  rw [s.sum_abs_convolutionThirdDerivative_gaussian_scaleDown (Real.sqrt v)
    (Real.sqrt_pos.mpr hv)]
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hh := div_le_div_of_nonneg_right hunit (pow_nonneg (Real.sqrt_nonneg v) 3)
  rw [sqrt_cube_eq_rpow hv.le, sqrt_cube_eq_rpow hL] at hh
  rw [sqrt_cube_eq_rpow hv.le]
  convert hh using 1
  ring

/-- The actual third Gaussian derivative tensor at variance time `v`.
Only local three-coordinate nondegeneracy is used; the full factor may be singular. -/
theorem sum_abs_convolutionThirdDerivative_gaussian_sqrt_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {a v : ℝ} (hv : 0 < v)
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt v • A)) x j k l|) ≤
      gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap (A * A.transpose) * a * v ^ (3 / 2 : ℝ)) := by
  exact s.third_variance_bound_of_normalized_bound hp A x hv
    ((s.scaleDown (Real.sqrt v) (Real.sqrt_pos.mpr hv)).sum_abs_convolutionThirdDerivative_gaussian_le hp A _ hQ ha hdiag hc hac)

/-- Intrinsic local-covariance specialization, with the exact pair-gap and
three-coordinate parameters of the given covariance matrix. -/
theorem sum_abs_convolutionThirdDerivative_gaussian_sqrt_le_of_localCovariance
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q)
    (hA : A * A.transpose = Q) {v : ℝ} (hv : 0 < v) :
    (∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt v • A)) x j k l|) ≤
      gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap Q * a3 Q * v ^ (3 / 2 : ℝ)) := by
  have hp0 : 0 < p := hp
  have hlocal : LocalCovarianceLower Q 3 (a3 Q) :=
    localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ.posSemidef)
  have ha := a3_pos_of_a4_pos hp0 hQ.posSemidef hQ.a4_pos
  have hc := pairGap_pos_of_a4_pos hp0 hQ.posSemidef hQ.unit_diagonal hQ.a4_pos
  have hac := a3_le_pairGap hp0 hQ.posSemidef hQ.unit_diagonal
  have hh := s.sum_abs_convolutionThirdDerivative_gaussian_sqrt_le hp A x hv
    (by simpa only [hA] using hlocal) ha
    (by simpa only [hA] using hQ.unit_diagonal)
    (by simpa only [hA] using hc) (by simpa only [hA] using hac)
  simpa only [hA] using hh

end

end RectangleCLT.FaceSmoother
