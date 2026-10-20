import RectangleCLTCompanion.RestorationPartitions
import RectangleCLTCompanion.FourthIdentityFresh
import RectangleCLT.GaussianFourthAssembly

/-! Exact repeated-first-pair Gaussian IBP for the actual fourth convolution
tensor used by the comparison path.  All finite contractions and Gaussian
moments are genuine integrals. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

theorem mixedFourthDerivativeF_swap_blocks (x : Vector p) (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m = s.mixedFourthDerivativeF x l m j k := by
  rw [s.mixedFourthDerivativeF_swap_middle_two x j k l m,
    s.mixedFourthDerivativeF_swap_first_two x j l k m,
    s.mixedFourthDerivativeF_swap_last_two x l j k m,
    s.mixedFourthDerivativeF_swap_middle_two x l j m k]

theorem convolutionFourthDerivative_swap_blocks
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      s.convolutionFourthDerivative (gaussianLaw A) x l m j k := by
  rw [s.convolutionFourthDerivative_eq_standardGaussian,
    s.convolutionFourthDerivative_eq_standardGaussian]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun g =>
    mixedFourthDerivativeF_swap_blocks s _ j k l m))

private theorem sum_four_rotate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ι → κ → κ → ℝ) :
    (∑ i, ∑ j, ∑ l, ∑ m, f i j l m) = ∑ l, ∑ m, ∑ i, ∑ j, f i j l m := by
  have hs := Finset.sum_comm (s := (Finset.univ : Finset (ι × ι)))
    (t := (Finset.univ : Finset (κ × κ)))
    (f := fun ij lm => f ij.1 ij.2 lm.1 lm.2)
  simpa only [Fintype.sum_prod_type] using hs

theorem convolutionFourthTensor_pair_first_eq
    (A : Matrix (Fin p) (Fin p) ℝ) (x z u v : Vector p) :
    s.convolutionFourthTensor (gaussianLaw A) x z z u v =
      ∑ j, ∑ k, u j * v k *
        matrixQuadratic (fun l m => s.convolutionFourthDerivative (gaussianLaw A) x j k l m) z := by
  unfold FaceSmoother.convolutionFourthTensor
  rw [sum_four_rotate]
  simp only [matrixQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [convolutionFourthDerivative_swap_blocks]
  ring

theorem integrable_score_secondDerivative_gaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (x z : Vector p) (j k : Fin p) :
    Integrable (fun g => repeatedDirectionScore g z *
      s.mixedSecondDerivativeF (A.mulVec g + x) j k) (standardGaussian p) := by
  have hscore : Integrable (fun g => repeatedDirectionScore g z) (standardGaussian p) := by
    simpa only [mul_one] using
      integrable_repeatedDirectionScore_weight (standardGaussian p) id (fun _ => 1)
        (integrable_const 1) (fun l m => by
          simpa only [mul_one] using standardGaussian_integrable_coordinate_product p l m) z
  have hw : Measurable (fun g => s.mixedSecondDerivativeF (A.mulVec g + x) j k) :=
    (s.continuous_secondDerivative j k).measurable.comp
      ((measurable_mulVec A).add measurable_const)
  simpa only [mul_comm] using hscore.bdd_mul hw.aestronglyMeasurable
    ⟨3 / s.bandwidth ^ 2, fun g => s.norm_secondDerivative_le _ j k⟩

theorem matrixQuadratic_convolutionFourth_eq_integral
    (A : Matrix (Fin p) (Fin p) ℝ) (x z : Vector p) (j k : Fin p) :
    matrixQuadratic (fun l m => s.convolutionFourthDerivative (gaussianLaw A) x j k l m) z =
      ∫ g, matrixQuadratic (fun l m => s.mixedFourthDerivativeF (A.mulVec g + x) j k l m) z
        ∂standardGaussian p := by
  simp_rw [s.convolutionFourthDerivative_eq_standardGaussian]
  apply matrixQuadratic_integral
  intro l m
  exact integrable_bounded_test_comp (standardGaussian p) _
    ((measurable_mulVec A).add measurable_const) _
    (s.continuous_fourthDerivative j k l m) _ (fun a => s.norm_fourthDerivative_le a j k l m)

/-- The exact actual convolution tensor appearing in the fresh A/B/C
pairings, with the repeated pair in its first two argument positions. -/
theorem convolutionFourthTensor_repeated_score_scaled
    (A : Matrix (Fin p) (Fin p) ℝ) (x z u v : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    s.convolutionFourthTensor (gaussianLaw (σ • A)) x (A.mulVec z) (A.mulVec z) u v =
      (∫ g, repeatedDirectionScore g z *
        restorationHessian s ((σ • A).mulVec g + x) u v ∂standardGaussian p) / σ ^ 2 := by
  rw [convolutionFourthTensor_pair_first_eq]
  simp_rw [matrixQuadratic_convolutionFourth_eq_integral,
    smoother_fourth_repeated_score_scaled s A x z hσ]
  have hi (j k : Fin p) :=
    ((integrable_score_secondDerivative_gaussian s (σ • A) x z j k).const_mul (u j)).mul_const (v k)
  have heq (g : Vector p) :
      repeatedDirectionScore g z * restorationHessian s ((σ • A).mulVec g + x) u v =
        ∑ j, ∑ k, u j *
          (repeatedDirectionScore g z * s.mixedSecondDerivativeF ((σ • A).mulVec g + x) j k) * v k := by
    simp only [restorationHessian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => hi _ k),
    integral_mul_const, integral_const_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end RectangleCLT.Companion
