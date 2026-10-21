import RectangleCLT.GlobalGaussianHalfConvolution
import RectangleCLT.GaussianFourthSupCounting

/-! Separate coordinate local suprema under independent Gaussian splitting.
The supremum stays inside the tensor sum and is moved only across an
independent expectation by an inequality. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem localConvolutionFourthSup_gaussian_sum_le
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    {r : ℝ} (hr : 0 ≤ r) (x : Vector p) (j k l m : Fin p) :
    s.localConvolutionFourthSup C r x 1 j k l m ≤
      ∫ v, s.localConvolutionFourthSup A r (x + v) 1 j k l m ∂gaussianLaw B := by
  apply s.localConvolutionFourthSup_le_of_uniform C hr x 1 j k l m
  intro u hu
  simp only [Real.sqrt_one, one_smul]
  rw [s.convolutionFourthDerivative_gaussian_sum A B C hcov]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_of_nonneg
    (ae_of_all _ (fun _ => abs_nonneg _))
    (s.integrable_localConvolutionFourthSup_comp A hr 1 (gaussianLaw B)
      (fun v => x + v) (measurable_const.add measurable_id) j k l m)
  exact ae_of_all _ (fun v => by
    have he : x + u + v = (x + v) + u := by abel
    dsimp only
    rw [he]
    simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourthDerivative_le_localSup A (x + v) 1 hu j k l m)

theorem sum_localConvolutionFourthSup_gaussian_sum_le
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    {r : ℝ} (hr : 0 ≤ r) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup C r x 1 j k l m) ≤
      ∫ v, (∑ j, ∑ k, ∑ l, ∑ m,
        s.localConvolutionFourthSup A r (x + v) 1 j k l m) ∂gaussianLaw B := by
  have hi (j k l m : Fin p) :=
    s.integrable_localConvolutionFourthSup_comp A hr 1 (gaussianLaw B)
      (fun v => x + v) (measurable_const.add measurable_id) j k l m
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ => hi j k l m)))),
    integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ => hi _ k l m))),
    integral_finset_sum Finset.univ (fun l _ =>
      integrable_finset_sum Finset.univ (fun m _ => hi _ _ l m)),
    integral_finset_sum Finset.univ (fun m _ => hi _ _ _ m)]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro m _
  exact s.localConvolutionFourthSup_gaussian_sum_le A B C hcov hr x j k l m

theorem sum_abs_convolutionThird_gaussian_sum_le
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw C) x j k l|) ≤
      ∫ v, (∑ j, ∑ k, ∑ l,
        |s.convolutionThirdDerivative (gaussianLaw A) (x + v) j k l|) ∂gaussianLaw B := by
  have hi (j k l : Fin p) : Integrable
      (fun v => |s.convolutionThirdDerivative (gaussianLaw A) (x + v) j k l|)
      (gaussianLaw B) := by
    have hc : Continuous (fun y => s.convolutionThirdDerivative (gaussianLaw A) y j k l) := by
      simpa only [Function.comp_def, Real.sqrt_one, one_smul] using
        (s.continuous_gaussianConvolutionThirdDerivative A j k l).comp
          (show Continuous (fun y : Vector p => (y, (1 : ℝ))) from
            continuous_id.prodMk continuous_const)
    exact (integrable_bounded_test_comp (gaussianLaw B) (fun v => x + v)
      (measurable_const.add measurable_id) _ hc _
      (fun y => s.norm_convolutionThirdDerivative_le (gaussianLaw A) y j k l)).abs
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hi j k l))),
    integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hi _ k l)),
    integral_finset_sum Finset.univ (fun l _ => hi _ _ l)]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  rw [s.convolutionThirdDerivative_gaussian_sum A B C hcov]
  exact abs_integral_le_integral_abs

theorem sum_localConvolutionFourthSup_gaussian_halves_le
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      ∫ v, (∑ j, ∑ k, ∑ l, ∑ m,
        s.localConvolutionFourthSup (gaussianHalfFactor A) r (x + v) 1 j k l m)
        ∂gaussianLaw (gaussianHalfFactor A) := by
  apply s.sum_localConvolutionFourthSup_gaussian_sum_le _ _ _ ?_ hr x
  simp only [gaussianHalfFactor_covariance, ← add_smul]
  norm_num

end

end RectangleCLT.FaceSmoother
