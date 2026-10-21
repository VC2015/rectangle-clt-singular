import RectangleCLT.RectangleCoupling
import RectangleCLT.GaussianComparisonLaw

/-! An actual Gaussian marginal bound for the elementary coupling bridge.
This coarse bound deliberately keeps the factor `p`: in the truncation
applications the perturbation tends to zero, or is smaller than a fixed
negative power of `np`. No nondegeneracy beyond unit coordinate variances
is used here. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT

theorem standardRealGaussian_density_le_one (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 := by
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    Real.le_sqrt_of_sq_le (by nlinarith [Real.two_le_pi])
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
    (inv_le_one₀ (zero_lt_one.trans_le hs)).mpr hs
  have he : Real.exp (-x ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
    (by simpa only [mul_one] using hinv)

theorem standardRealGaussian_real_Icc_le (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Icc a b) ≤ b - a := by
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (f := gaussianPDFReal 0 1) (C := 1)
    (s := Icc a b) (isCompact_Icc.measure_lt_top)
    (fun x _ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)] using
        standardRealGaussian_density_le_one x)
  have hi : 0 ≤ ∫ x in Icc a b, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  rw [Real.norm_eq_abs, abs_of_nonneg hi, Real.volume_real_Icc_of_le hab,
    one_mul] at hnorm
  simpa only [Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal hi] using hnorm

theorem gaussianLaw_coordinate_strip_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (j : Fin p) (a b : ℝ) (hab : a ≤ b) :
    (gaussianLaw A).real {x | a ≤ x j ∧ x j ≤ b} ≤ b - a := by
  have hm : ((gaussianLaw A).map (fun x => x j)).real (Icc a b) =
      (gaussianLaw A).real {x | a ≤ x j ∧ x j ≤ b} := by
    simp only [Measure.real, Measure.map_apply (measurable_pi_apply j) measurableSet_Icc]
    rfl
  rw [gaussianLaw_map_eval_eq_standard A j (hdiag j)] at hm
  rw [← hm]
  exact standardRealGaussian_real_Icc_le a b hab

/-- The truncation bridge for every rectangle, with a concrete Gaussian
reference law. Singular full covariance and atoms in `W` are allowed. -/
theorem rectangleError_le_of_gaussian_norm_coupling
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (W V : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {r q E : ℝ} (hr : 0 ≤ r)
    (hbad : μ.real {ω | r < ‖W ω - V ω‖} ≤ q)
    (hbase : ∀ lo hi : Vector p, rectangleError μ V A (Rect.closedBox lo hi) ≤ E)
    (R : Rect p) : rectangleError μ W A R ≤ E + q + 4 * p * r := by
  have hh := rectangleError_le_of_norm_coupling μ hp W V hW A hr hbad hbase
    (K := 1) (fun j a b hab => by
      simpa only [one_mul] using gaussianLaw_coordinate_strip_le A hdiag j a b hab) R
  simpa only [mul_one] using hh

end RectangleCLT
