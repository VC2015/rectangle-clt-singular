import RectangleCLTArxivV1.SupplementalGRectangularDecomposition
import RectangleCLTCompanion.SubexponentialGaussian

/-! Exact covariance-law transport from the archived square-factor
convolution tensor to a rectangular rank-dimensional Gaussian integral. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_restorationFourthDerivative_last_swap {p : ℕ} (s : FaceSmoother p)
    (x z y w : Vector p) :
    restorationFourthDerivative s x z y w = restorationFourthDerivative s x z w y := by
  simp_rw [restorationFourthDerivative_eq_coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he : (fun l m => s.mixedFourthDerivativeF x k j l m) =
      (fun l m => s.mixedFourthDerivativeF x j k l m) := by
    funext l m
    exact s.mixedFourthDerivativeF_swap_first_two x k j l m
  rw [he]
  ring

theorem cap_convolutionFourthDerivative_rectangular {p r : ℕ} (s : FaceSmoother p)
    (B : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : B*B.transpose = C*C.transpose) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw C) x j k l m =
      ∫ g, s.mixedFourthDerivativeF (B.mulVec g+x) j k l m ∂standardGaussian r := by
  have hlaw := RectangleCLT.Companion.rectangularGaussianLaw_eq_gaussianLaw B C hgram
  rw [s.convolutionFourthDerivative_eq_integral,← hlaw]
  unfold RectangleCLT.Companion.rectangularGaussianLaw
  have hF : Measurable (fun z : Vector p => s.mixedFourthDerivativeF (x+z) j k l m) :=
    ((s.continuous_fourthDerivative j k l m).comp (continuous_const.add continuous_id)).measurable
  have hB : Measurable B.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [integral_map hB.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change s.mixedFourthDerivativeF (x+B.mulVec g) j k l m = s.mixedFourthDerivativeF (B.mulVec g+x) j k l m
    rw [add_comm x])

/-- This is the archived actual convolution tensor, evaluated using any
rectangular factor of its covariance. The Gaussian dimension may be rank. -/
theorem cap_convolutionFourthTensor_rectangular {p r : ℕ} (s : FaceSmoother p)
    (B : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : B*B.transpose = C*C.transpose) (x z y w : Vector p) :
    s.convolutionFourthTensor (gaussianLaw C) x z z y w =
      ∫ g, restorationFourthDerivative s (B.mulVec g+x) z y w ∂standardGaussian r := by
  have hx : Measurable (fun g : Vector r => B.mulVec g+x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable.add_const x
  have he (j k : Fin p) :
      matrixQuadratic (fun l m => s.convolutionFourthDerivative (gaussianLaw C) x j k l m) z =
      ∫ g, matrixQuadratic (fun l m => s.mixedFourthDerivativeF (B.mulVec g+x) j k l m) z
        ∂standardGaussian r := by
    simp_rw [cap_convolutionFourthDerivative_rectangular s B C hgram]
    apply matrixQuadratic_integral
    intro l m
    exact integrable_bounded_test_comp (standardGaussian r) _ hx _
      (s.continuous_fourthDerivative j k l m) _ (fun a => s.norm_fourthDerivative_le a j k l m)
  rw [convolutionFourthTensor_pair_first_eq]
  simp_rw [he]
  have hi (j k : Fin p) := (integrable_paired_fourth_coordinate s B x z j k).const_mul (y j*w k)
  simp_rw [cap_restorationFourthDerivative_last_swap s _ z y w,restorationFourthDerivative_eq_coordinate]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum _ (fun k _ => hi _ k),integral_const_mul]

/-- The actual square-law tensor has the exact intrinsic-dimensional
single H3 / pair H2 decomposition with the manuscript's Gaussian powers. -/
theorem cap_convolutionFourthTensor_intrinsic_single_pair {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : A*A.transpose = C*C.transpose) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x : Vector p) (Z : Vector r) (Y W : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    s.convolutionFourthTensor (gaussianLaw (σ • C)) x (A.mulVec Z) (A.mulVec Z) Y W =
      -(1/(s.bandwidth*σ^3))*(∑ f, (normalDot f Y*normalDot f W)*
        (∫ g, capThirdHermiteScore (capRectangularFactorNormal A f) Z g*
          selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian r)) +
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ g, capRectangularPairCoefficient A f g Y W*
        (∫ z, repeatedDirectionScore z Z*selectorTupleWeight s ![f,g]
          ((σ • A).mulVec z+x) ∂standardGaussian r)) := by
  have hscaled : (σ • A)*(σ • A).transpose = (σ • C)*(σ • C).transpose := by
    simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,hgram]
  rw [cap_convolutionFourthTensor_rectangular s (σ • A) (σ • C) hscaled]
  exact cap_rectangular_fourth_derivative_single_pair s A hdiag x Z Y W hσ

end
end RectangleCLTArxivV1
