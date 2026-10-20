import RectangleCLTCompanion.SharpGaussianRotation

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

theorem splitGaussianFactor_add {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) (z : Vector p × Vector p) :
    (splitGaussianScale t • A).mulVec z.1 + (splitGaussianScale t • A).mulVec z.2 =
      (Real.sqrt t • A).mulVec (gaussianHalfSum z) := by
  have hs : splitGaussianScale t = Real.sqrt t / Real.sqrt 2 := by
    exact Real.sqrt_div' t (by norm_num)
  ext j
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    gaussianHalfSum, hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem integral_splitGaussianFactor {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) (f : Vector p → ℝ) (hf : Measurable f) :
    (∫ z : Vector p × Vector p, f ((splitGaussianScale t • A).mulVec z.1 +
      (splitGaussianScale t • A).mulVec z.2) ∂(standardGaussian p).prod (standardGaussian p)) =
      ∫ g, f ((Real.sqrt t • A).mulVec g) ∂standardGaussian p := by
  simp_rw [splitGaussianFactor_add]
  exact integral_gaussianHalfSum _ (hf.comp (measurable_mulVec _))

/-- Actual probability-shift convolution splits into two independent
Gaussian halves. Joint integrability is discharged by a bounded kernel. -/
theorem shiftIntegral_gaussian_split {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ)
    (hb : ∀ y, ‖G y‖ ≤ C) (x : Vector p) :
    shiftIntegral (gaussianLaw (Real.sqrt t • A)) G x =
      ∫ g, shiftIntegral (gaussianLaw (splitGaussianScale t • A)) G
        (x + (splitGaussianScale t • A).mulVec g) ∂standardGaussian p := by
  have hpull (B : Matrix (Fin p) (Fin p) ℝ) (y : Vector p) :
      shiftIntegral (gaussianLaw B) G y = ∫ g, G (y + B.mulVec g) ∂standardGaussian p := by
    exact integral_map (measurable_mulVec B).aemeasurable
      (hG.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hW : Measurable (fun z : Vector p × Vector p =>
      x + (splitGaussianScale t • A).mulVec z.1 + (splitGaussianScale t • A).mulVec z.2) :=
    (measurable_const.add ((measurable_mulVec _).comp measurable_fst)).add
      ((measurable_mulVec _).comp measurable_snd)
  have hi := integrable_bounded_test_comp ((standardGaussian p).prod (standardGaussian p)) _ hW G hG C hb
  have hadd := integral_splitGaussianFactor A t (fun y => G (x + y))
    (hG.measurable.comp (measurable_const.add measurable_id))
  rw [hpull]
  calc
    _ = ∫ z : Vector p × Vector p,
        G (x + (splitGaussianScale t • A).mulVec z.1 + (splitGaussianScale t • A).mulVec z.2)
          ∂(standardGaussian p).prod (standardGaussian p) := by
      rw [← hadd]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => congrArg G (add_assoc _ _ _).symm)
    _ = ∫ g₀, ∫ g₁, G ((x + (splitGaussianScale t • A).mulVec g₀) +
        (splitGaussianScale t • A).mulVec g₁) ∂standardGaussian p ∂standardGaussian p :=
      integral_prod _ hi
    _ = _ := by simp_rw [hpull]

end
end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem convolutionThirdDerivative_gaussian_split
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l =
      ∫ g, s.convolutionThirdDerivative (gaussianLaw (Companion.splitGaussianScale t • A))
        (x + (Companion.splitGaussianScale t • A).mulVec g) j k l ∂standardGaussian p := by
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact Companion.shiftIntegral_gaussian_split A t (fun y => s.mixedThirdDerivativeF y j k l)
    (s.continuous_thirdDerivative j k l) _ (fun y => s.norm_thirdDerivative_le y j k l) x

theorem convolutionFourthDerivative_gaussian_split
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) x j k l m =
      ∫ g, s.convolutionFourthDerivative (gaussianLaw (Companion.splitGaussianScale t • A))
        (x + (Companion.splitGaussianScale t • A).mulVec g) j k l m ∂standardGaussian p := by
  simp_rw [s.convolutionFourthDerivative_eq_integral]
  exact Companion.shiftIntegral_gaussian_split A t (fun y => s.mixedFourthDerivativeF y j k l m)
    (s.continuous_fourthDerivative j k l m) _ (fun y => s.norm_fourthDerivative_le y j k l m) x

/-- Equal-half splitting for the actual fourth multilinear convolution
contraction. The directions can depend on later independent samples. -/
theorem convolutionFourthTensor_gaussian_split
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (x u v w z : Vector p) :
    s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A)) x u v w z =
      ∫ g, s.convolutionFourthTensor (gaussianLaw (Companion.splitGaussianScale t • A))
        (x + (Companion.splitGaussianScale t • A).mulVec g) u v w z ∂standardGaussian p := by
  let ν := gaussianLaw (Companion.splitGaussianScale t • A)
  let W := fun g => x + (Companion.splitGaussianScale t • A).mulVec g
  have hW : Measurable W := measurable_const.add (measurable_mulVec _)
  have hi (j k l m : Fin p) : Integrable (fun g =>
      s.convolutionFourthDerivative ν (W g) j k l m * u j * v k * w l * z m)
      (standardGaussian p) :=
    ((((integrable_bounded_test_comp _ W hW _
      (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m) _
      (fun y => s.norm_convolutionFourthDerivative_le ν y j k l m)).mul_const (u j)).mul_const
      (v k)).mul_const (w l)).mul_const (z m)
  have hs : (∫ g, ∑ j, ∑ k, ∑ l, ∑ m,
      s.convolutionFourthDerivative ν (W g) j k l m * u j * v k * w l * z m
      ∂standardGaussian p) = ∑ j, ∑ k, ∑ l, ∑ m, ∫ g,
        s.convolutionFourthDerivative ν (W g) j k l m * u j * v k * w l * z m
        ∂standardGaussian p := by
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ =>
      integrable_finset_sum _ (fun l _ => integrable_finset_sum _ (fun m _ => hi j k l m))))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ =>
      integrable_finset_sum _ (fun m _ => hi j k l m)))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finset_sum _ (fun l _ => integrable_finset_sum _ (fun m _ => hi j k l m))]
    apply Finset.sum_congr rfl
    intro l _
    exact integral_finset_sum _ (fun m _ => hi j k l m)
  simp only [integral_mul_const] at hs
  unfold convolutionFourthTensor
  simp_rw [s.convolutionFourthDerivative_gaussian_split]
  exact hs.symm

end
end RectangleCLT.FaceSmoother
