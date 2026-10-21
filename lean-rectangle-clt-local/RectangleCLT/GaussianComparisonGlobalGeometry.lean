import RectangleCLT.GaussianComparisonCoefficient
import RectangleCLT.GaussianComparisonLocal
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! The genuine comparison path is fully nondegenerate at every positive
time when its reference covariance has a positive full eigenvalue. Endpoint
continuity therefore removes the need to regularize either Gaussian law. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT

theorem gaussianComparisonCovariance_full_lower {p : ℕ}
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) {ν t : ℝ}
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic T v)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : Vector p) :
    (t * ν) * vectorNormSq v ≤
      matrixQuadratic (gaussianComparisonCovariance S T t) v := by
  have heq : matrixQuadratic (gaussianComparisonCovariance S T t) v =
      (1 - t) * matrixQuadratic S v + t * matrixQuadratic T v := by
    simp only [matrixQuadratic, gaussianComparisonCovariance_apply,
      mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> ring
  rw [heq]
  have hp := mul_nonneg (sub_nonneg.mpr ht1) (matrixQuadratic_nonneg_of_posSemidef hS v)
  have hh := mul_le_mul_of_nonneg_left (hlower v) ht0
  nlinarith

theorem comparison_inv_sqrt_time {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    1 / Real.sqrt (t * ν) = (1 / Real.sqrt ν) * t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_mul ht.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  ring

theorem comparison_integrableOn_inv_sqrt_time :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Icc 0 1) volume := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem comparison_integral_inv_sqrt_time :
    (∫ t in (0 : ℝ)..1, t ^ (-(1 / 2 : ℝ))) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num

end RectangleCLT
