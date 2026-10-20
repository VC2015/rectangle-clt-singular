import RectangleCLTCompanion.RestorationAffineIBP

/-! Two integrations by parts for the actual first and second derivatives of
the rational selector smoother.  Rectangular factors and singular observed
covariances are allowed.  There is no Gaussian integration-by-parts premise. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r : ℕ} (s : FaceSmoother p)

/-- Remove the last repeated pair from an actual third derivative. -/
theorem smoother_third_repeated_score
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r) (j : Fin p) :
    (∫ g, repeatedDirectionScore g z *
      s.coordinateDerivativeF (A.mulVec g + x) j ∂standardGaussian r) =
      ∫ g, matrixQuadratic
        (fun l m => s.mixedThirdDerivativeF (A.mulVec g + x) j l m)
        (A.mulVec z) ∂standardGaussian r := by
  apply restorationAffine_second_stein A x
    (fun a => s.coordinateDerivativeF a j)
    (fun a l => s.mixedSecondDerivativeF a j l)
    (fun a l m => s.mixedThirdDerivativeF a j l m)
  · intro a y
    simpa only [FaceSmoother.line_zero] using
      s.hasDerivAt_firstDerivative_line_sum_translation a y j 0
  · intro a y l
    simpa only [FaceSmoother.line_zero] using
      s.hasDerivAt_secondDerivative_line_sum a y j l 0
  · exact (s.continuous_firstDerivative j).measurable
  · intro l; exact (s.continuous_secondDerivative j l).measurable
  · intro l m; exact (s.continuous_thirdDerivative j l m).measurable
  · exact ⟨1 / s.bandwidth, fun a => s.norm_firstDerivative_le a j⟩
  · intro l; exact ⟨3 / s.bandwidth ^ 2, fun a => s.norm_secondDerivative_le a j l⟩
  · intro l m; exact ⟨13 / s.bandwidth ^ 3, fun a => s.norm_thirdDerivative_le a j l m⟩

/-- Remove the repeated pair from an actual fourth derivative, leaving the
two other directions in the actual Hessian. -/
theorem smoother_fourth_repeated_score
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r) (j k : Fin p) :
    (∫ g, repeatedDirectionScore g z *
      s.mixedSecondDerivativeF (A.mulVec g + x) j k ∂standardGaussian r) =
      ∫ g, matrixQuadratic
        (fun l m => s.mixedFourthDerivativeF (A.mulVec g + x) j k l m)
        (A.mulVec z) ∂standardGaussian r := by
  apply restorationAffine_second_stein A x
    (fun a => s.mixedSecondDerivativeF a j k)
    (fun a l => s.mixedThirdDerivativeF a j k l)
    (fun a l m => s.mixedFourthDerivativeF a j k l m)
  · intro a y
    simpa only [FaceSmoother.line_zero] using
      s.hasDerivAt_secondDerivative_line_sum a y j k 0
  · intro a y l
    simpa only [FaceSmoother.line_zero] using
      s.hasDerivAt_thirdDerivative_line_sum a y j k l 0
  · exact (s.continuous_secondDerivative j k).measurable
  · intro l; exact (s.continuous_thirdDerivative j k l).measurable
  · intro l m; exact (s.continuous_fourthDerivative j k l m).measurable
  · exact ⟨3 / s.bandwidth ^ 2, fun a => s.norm_secondDerivative_le a j k⟩
  · intro l; exact ⟨13 / s.bandwidth ^ 3, fun a => s.norm_thirdDerivative_le a j k l⟩
  · intro l m; exact ⟨75 / s.bandwidth ^ 4, fun a => s.norm_fourthDerivative_le a j k l m⟩

theorem restoration_matrixQuadratic_smul (B : Matrix (Fin p) (Fin p) ℝ)
    (v : Vector p) (σ : ℝ) :
    matrixQuadratic B (σ • v) = σ ^ 2 * matrixQuadratic B v := by
  simp only [matrixQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The paper's explicit inverse-variance factor, for actual third
derivatives and an arbitrary fixed translated base `x`. -/
theorem smoother_third_repeated_score_scaled
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) (j : Fin p) :
    (∫ g, matrixQuadratic
      (fun l m => s.mixedThirdDerivativeF ((σ • A).mulVec g + x) j l m)
      (A.mulVec z) ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z *
        s.coordinateDerivativeF ((σ • A).mulVec g + x) j ∂standardGaussian r) /
          σ ^ 2 := by
  simp_rw [Matrix.smul_mulVec_assoc]
  have hs := smoother_third_repeated_score s (σ • A) x z j
  simp_rw [Matrix.smul_mulVec_assoc, restoration_matrixQuadratic_smul] at hs
  rw [integral_const_mul] at hs
  apply (eq_div_iff (pow_ne_zero 2 hσ)).mpr
  calc
    _ = σ ^ 2 * (∫ g, matrixQuadratic
        (fun l m => s.mixedThirdDerivativeF (σ • A.mulVec g + x) j l m)
        (A.mulVec z) ∂standardGaussian r) := mul_comm _ _
    _ = _ := hs.symm

theorem smoother_fourth_repeated_score_scaled
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) (j k : Fin p) :
    (∫ g, matrixQuadratic
      (fun l m => s.mixedFourthDerivativeF ((σ • A).mulVec g + x) j k l m)
      (A.mulVec z) ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z *
        s.mixedSecondDerivativeF ((σ • A).mulVec g + x) j k ∂standardGaussian r) /
          σ ^ 2 := by
  simp_rw [Matrix.smul_mulVec_assoc]
  have hs := smoother_fourth_repeated_score s (σ • A) x z j k
  simp_rw [Matrix.smul_mulVec_assoc, restoration_matrixQuadratic_smul] at hs
  rw [integral_const_mul] at hs
  apply (eq_div_iff (pow_ne_zero 2 hσ)).mpr
  calc
    _ = σ ^ 2 * (∫ g, matrixQuadratic
        (fun l m => s.mixedFourthDerivativeF (σ • A.mulVec g + x) j k l m)
        (A.mulVec z) ∂standardGaussian r) := mul_comm _ _
    _ = _ := hs.symm

end
end RectangleCLT.Companion
