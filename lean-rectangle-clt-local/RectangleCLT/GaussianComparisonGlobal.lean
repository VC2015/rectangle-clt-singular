import RectangleCLT.GaussianComparisonGlobalGeometry
import RectangleCLT.GaussianComparisonGlobalEndpoint
import RectangleCLT.GaussianComparisonGlobalHessian

/-! Full-eigenvalue Gaussian comparison for unit coordinate variances.
The true covariance may be singular. The full lower bound is required only
of the reference covariance; no covariance ordering is assumed. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT

noncomputable section

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem sum_abs_gaussianComparisonSecond_global_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (B * B.transpose) v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∑ j, ∑ k, |s.gaussianComparisonSecond A B t j k|) ≤
      gaussianSecondGlobalConstant * dimensionLog p / Real.sqrt (t * ν) := by
  have hS : (A * A.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hT : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  obtain ⟨C, hC⟩ := gaussianComparison_factor_exists
    (gaussianComparisonCovariance_posSemidef hS hT ht0.le ht1)
  have hdiag : ∀ j, (C * C.transpose) j j = 1 := by
    rw [hC]
    exact gaussianComparisonCovariance_unit_diagonal _ _ hA hB t
  have hlowerC (v : Vector p) : (t * ν) * vectorNormSq v ≤
      matrixQuadratic (C * C.transpose) v := by
    rw [hC]
    exact gaussianComparisonCovariance_full_lower hS hlower ht0.le ht1 v
  simp_rw [s.gaussianComparisonSecond_eq_convolution A B C ht0.le ht1 hC]
  exact s.sum_abs_convolutionSecondDerivative_global_le hp C 0 hdiag
    (mul_pos ht0 hν) hlowerC

theorem abs_gaussianComparisonDerivative_global_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (B * B.transpose) v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |(1 / 2 : ℝ) * ∑ j, ∑ k,
      ((B * B.transpose) j k - (A * A.transpose) j k) *
        s.gaussianComparisonSecond A B t j k| ≤
      (gaussianSecondGlobalConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / (2 * Real.sqrt ν)) * t ^ (-(1 / 2 : ℝ)) := by
  let Δ := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  have hΔ : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (∑ j, ∑ k,
        |((B * B.transpose) j k - (A * A.transpose) j k) *
          s.gaussianComparisonSecond A B t j k|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 / 2 : ℝ) * (Δ * ∑ j, ∑ k, |s.gaussianComparisonSecond A B t j k|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      simpa only [abs_sub_comm] using abs_entry_sub_le_proxyCovarianceDiscrepancy
        (A * A.transpose) (B * B.transpose) j k
    _ ≤ (1 / 2 : ℝ) * (Δ *
        (gaussianSecondGlobalConstant * dimensionLog p / Real.sqrt (t * ν))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (s.sum_abs_gaussianComparisonSecond_global_le hp A B hA hB hν hlower ht0 ht1) hΔ)
        (by norm_num)
    _ = _ := by
      rw [Real.sqrt_mul ht0.le, Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
      dsimp only [Δ]
      ring

theorem gaussianComparison_smoother_gap_global_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (B * B.transpose) v) :
    |(∫ x, s.F x ∂gaussianLaw A) - (∫ y, s.F y ∂gaussianLaw B)| ≤
      gaussianSecondGlobalConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / Real.sqrt ν := by
  let K := gaussianSecondGlobalConstant *
    proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
      dimensionLog p / (2 * Real.sqrt ν)
  have hh := abs_sub_le_integral_of_derivative_bound
    (s.continuous_gaussianComparisonExpectation A B).continuousOn
    (fun t ht => s.hasDerivAt_gaussianComparisonExpectation A B ht.1 ht.2)
    (comparison_integrableOn_inv_sqrt_time.const_mul K)
    (fun t ht => s.abs_gaussianComparisonDerivative_global_le hp A B hA hB hν hlower
      ht.1 ht.2.le)
  rw [s.gaussianComparisonExpectation_zero, s.gaussianComparisonExpectation_one,
    intervalIntegral.integral_const_mul, comparison_integral_inv_sqrt_time] at hh
  calc
    _ ≤ K * 2 := by simpa only [abs_sub_comm] using hh
    _ = _ := by dsimp only [K]; ring

end FaceSmoother

theorem gaussianComparison_closedBox_global_le {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (B * B.transpose) v)
    (lo hi : Vector p) :
    |(gaussianLaw A).real (Rect.closedBox lo hi).carrier -
      (gaussianLaw B).real (Rect.closedBox lo hi).carrier| ≤
      gaussianSecondGlobalConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / Real.sqrt ν := by
  have hL : 0 < Real.sqrt (dimensionLog p) := Real.sqrt_pos.mpr
    (lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp))
  let N : ℝ := (Fintype.card (Face p) : ℝ) + 2
  have hN : 0 < N := by dsimp only [N]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let h := ε / (2 * N * Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p))
  have hh : 0 < h := by dsimp [h]; positivity
  let s := FaceSmoother.closedBox lo hi h hh
  have heA := s.gaussian_integral_endpoint_error_le_gap_free hp A hA
  have heB := s.gaussian_integral_endpoint_error_le_gap_free hp B hB
  have hg := s.gaussianComparison_smoother_gap_global_le hp A B hA hB hν hlower
  have hbox : {x : Vector p | s.Inside x} = (Rect.closedBox lo hi).carrier := by
    ext x
    exact FaceSmoother.closedBox_Inside lo hi h hh x
  rw [hbox] at heA heB
  have hεeq : 2 * (N * Real.exp (3 / 2 : ℝ) * h * Real.sqrt (dimensionLog p)) = ε := by
    dsimp only [h]
    field_simp [hN.ne', (Real.exp_pos (3 / 2 : ℝ)).ne', hL.ne']
    <;> ring
  change |(∫ x, s.F x ∂gaussianLaw A) - (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤
    N * Real.exp (3 / 2 : ℝ) * h * Real.sqrt (dimensionLog p) at heA
  change |(∫ x, s.F x ∂gaussianLaw B) - (gaussianLaw B).real (Rect.closedBox lo hi).carrier| ≤
    N * Real.exp (3 / 2 : ℝ) * h * Real.sqrt (dimensionLog p) at heB
  have ha := abs_le.mp heA
  have hb := abs_le.mp heB
  have hc := abs_le.mp hg
  apply abs_le.mpr
  constructor <;> linarith

/-- The global Gaussian comparison bound requires no nondegeneracy on the
first covariance, and no local covariance parameter beyond the reference
full lower bound. All rectangle endpoint conventions are included. -/
theorem gaussianComparison_rectangle_global_le {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (B * B.transpose) v)
    (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianSecondGlobalConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / Real.sqrt ν :=
  rectangle_abs_probability_le_of_closedBox hp (gaussianLaw A) (gaussianLaw B)
    (gaussianComparison_closedBox_global_le hp A B hA hB hν hlower) R

end

end RectangleCLT
