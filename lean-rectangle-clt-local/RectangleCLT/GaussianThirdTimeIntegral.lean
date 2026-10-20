import RectangleCLT.GaussianDerivativeBounds
import RectangleCLT.DerivativeIntegration

/-! Time integration of the actual Gaussian third-derivative tensor.
Its continuity and integrability are proved from bounded smoother derivatives. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

/-- The concrete Gaussian third derivative is continuous through variance time zero. -/
theorem continuous_convolutionThirdDerivative_gaussian_time
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l : Fin p) :
    Continuous (fun t : ℝ => s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l) := by
  have he (t : ℝ) : s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l =
      ∫ z, s.mixedThirdDerivativeF (x + Real.sqrt t • A.mulVec z) j k l ∂standardGaussian p := by
    rw [s.convolutionThirdDerivative_eq_integral, gaussianLaw]
    have hm : AEStronglyMeasurable
        (fun z : Vector p => s.mixedThirdDerivativeF (x + z) j k l)
        ((standardGaussian p).map (Real.sqrt t • A).mulVec) :=
      ((s.continuous_thirdDerivative j k l).comp
        (show Continuous (fun z : Vector p => x + z) from continuous_const.add continuous_id)).aestronglyMeasurable
    rw [integral_map (measurable_mulVec (Real.sqrt t • A)).aemeasurable hm]
    simp only [Matrix.smul_mulVec_assoc]
  simp_rw [he]
  apply continuous_of_dominated
      (bound := fun _ : Vector p => 13 / s.bandwidth ^ 3)
  · intro t
    exact ((s.continuous_thirdDerivative j k l).comp
      (continuous_const.add (continuous_const.smul
        (continuous_const.matrix_mulVec continuous_id)))).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun z => s.norm_thirdDerivative_le _ j k l)
  · exact integrable_const _
  · exact ae_of_all _ (fun z => (s.continuous_thirdDerivative j k l).comp
      (continuous_const.add (Real.continuous_sqrt.smul continuous_const)))

/-- The total absolute third-derivative mass is a continuous actual function of time. -/
theorem continuous_sum_abs_convolutionThirdDerivative_gaussian_time
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    Continuous (fun t : ℝ => ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l|) := by
  exact continuous_finset_sum _ (fun j _ => continuous_finset_sum _ (fun k _ =>
    continuous_finset_sum _ (fun l _ =>
      (s.continuous_convolutionThirdDerivative_gaussian_time A x j k l).abs)))

/-- Actual third-derivative time integration under local covariance assumptions.
The factor of time cancels the nonintegrable part of the variance singularity. -/
theorem integral_time_mul_sum_abs_convolutionThirdDerivative_gaussian_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∫ t in (0 : ℝ)..1, t * ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l|) ≤
      2 * gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap (A * A.transpose) * a) := by
  have hD := (continuous_id.mul
    (s.continuous_sum_abs_convolutionThirdDerivative_gaussian_time A x)).intervalIntegrable (μ := volume) 0 1
  have hh := integral_time_mul_third_le hD (B :=
      gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap (A * A.transpose) * a)) (fun t ht => by
    have hb := s.sum_abs_convolutionThirdDerivative_gaussian_sqrt_le hp A x ht.1 hQ ha hdiag hc hac
    rw [Real.rpow_neg ht.1.le]
    convert hb using 1
    ring)
  convert hh using 1
  ring

end

end RectangleCLT.FaceSmoother
