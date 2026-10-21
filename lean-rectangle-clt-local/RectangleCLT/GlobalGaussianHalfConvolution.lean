import RectangleCLT.GaussianComparisonLaw
import RectangleCLT.SmootherConvolution
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent Gaussian splitting for the actual derivative kernels.

The second factor remains independent of the score used in a first-factor
dual tube. Thus boundary concentration may be applied conditionally on the
first factor without separating dependent weights and boundary events.
All identities allow singular factors.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- A square factor for one half of a centered Gaussian covariance. -/
def gaussianHalfFactor {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Real.sqrt (1 / 2 : ℝ) • A

theorem gaussianHalfFactor_covariance {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) :
    gaussianHalfFactor A * (gaussianHalfFactor A).transpose =
      (1 / 2 : ℝ) • (A * A.transpose) := by
  simp only [gaussianHalfFactor, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem gaussianLaw_add_halves {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    ((gaussianLaw (gaussianHalfFactor A)).prod
      (gaussianLaw (gaussianHalfFactor A))).map
      (fun z : Vector p × Vector p => z.1 + z.2) = gaussianLaw A := by
  have hcov : A * A.transpose =
      (1 : ℝ) ^ 2 • (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) +
        (1 : ℝ) ^ 2 • (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) := by
    simp only [one_pow, one_smul, gaussianHalfFactor_covariance, ← add_smul]
    norm_num
  have hmap := gaussianLaw_scaled_sum (gaussianHalfFactor A) (gaussianHalfFactor A) A 1 1 hcov
  change ((gaussianLaw (gaussianHalfFactor A)).prod
    (gaussianLaw (gaussianHalfFactor A))).map
    (fun z : Vector p × Vector p => (1 : ℝ) • z.1 + (1 : ℝ) • z.2) = _ at hmap
  simpa only [one_smul] using hmap

/-- Fubini for a bounded continuous test of the sum of two independent
Gaussians, with the second factor kept outside. -/
theorem integral_gaussianLaw_sum_eq_iterated {p : ℕ}
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (g : Vector p → ℝ) (hg : Continuous g) (K : ℝ)
    (hK : ∀ y, ‖g y‖ ≤ K) (x : Vector p) :
    (∫ z, g (x + z) ∂gaussianLaw C) =
      ∫ v, (∫ z, g ((x + v) + z) ∂gaussianLaw A) ∂gaussianLaw B := by
  have hcov' : C * C.transpose =
      (1 : ℝ) ^ 2 • (A * A.transpose) + (1 : ℝ) ^ 2 • (B * B.transpose) := by
    simpa only [one_pow, one_smul] using hcov
  have hsum : ((gaussianLaw A).prod (gaussianLaw B)).map
      (fun z : Vector p × Vector p => z.1 + z.2) = gaussianLaw C := by
    have hmap := gaussianLaw_scaled_sum A B C 1 1 hcov'
    change ((gaussianLaw A).prod (gaussianLaw B)).map
      (fun z : Vector p × Vector p => (1 : ℝ) • z.1 + (1 : ℝ) • z.2) = _ at hmap
    simpa only [one_smul] using hmap
  have hi : Integrable (fun z : Vector p × Vector p => g (x + (z.1 + z.2)))
      ((gaussianLaw A).prod (gaussianLaw B)) :=
    (integrable_const K).mono'
      ((hg.comp (continuous_const.add (continuous_fst.add continuous_snd))).aestronglyMeasurable)
      (ae_of_all _ (fun z => hK _))
  rw [← hsum, integral_map (f := fun z : Vector p => g (x + z))
    (measurable_fst.add measurable_snd).aemeasurable
    ((hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable),
    integral_prod_symm _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by congr 1; abel))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem convolutionThirdDerivative_gaussian_sum
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw C) x j k l =
      ∫ v, s.convolutionThirdDerivative (gaussianLaw A) (x + v) j k l
        ∂gaussianLaw B := by
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact integral_gaussianLaw_sum_eq_iterated A B C hcov _
    (s.continuous_thirdDerivative j k l) _
    (fun y => s.norm_thirdDerivative_le y j k l) x

theorem convolutionFourthDerivative_gaussian_sum
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw C) x j k l m =
      ∫ v, s.convolutionFourthDerivative (gaussianLaw A) (x + v) j k l m
        ∂gaussianLaw B := by
  simp_rw [s.convolutionFourthDerivative_eq_integral]
  exact integral_gaussianLaw_sum_eq_iterated A B C hcov _
    (s.continuous_fourthDerivative j k l m) _
    (fun y => s.norm_fourthDerivative_le y j k l m) x

theorem convolutionThirdDerivative_gaussian_halves
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw A) x j k l =
      ∫ v, s.convolutionThirdDerivative (gaussianLaw (gaussianHalfFactor A))
        (x + v) j k l ∂gaussianLaw (gaussianHalfFactor A) := by
  apply s.convolutionThirdDerivative_gaussian_sum
  simp only [gaussianHalfFactor_covariance, ← add_smul]
  norm_num

theorem convolutionFourthDerivative_gaussian_halves
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      ∫ v, s.convolutionFourthDerivative (gaussianLaw (gaussianHalfFactor A))
        (x + v) j k l m ∂gaussianLaw (gaussianHalfFactor A) := by
  apply s.convolutionFourthDerivative_gaussian_sum
  simp only [gaussianHalfFactor_covariance, ← add_smul]
  norm_num

end FaceSmoother

end

end RectangleCLT
