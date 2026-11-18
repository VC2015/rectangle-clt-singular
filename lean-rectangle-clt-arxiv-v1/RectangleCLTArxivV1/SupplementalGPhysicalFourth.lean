import RectangleCLTArxivV1.SupplementalGRectangularTensor

/-! Bounded continuous physical fourth-directional kernels. These coarse
bounds justify source-law transports and do not enter the final rank rate. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_restorationFourthDerivative_continuous {p : ℕ} (s : FaceSmoother p) (z y w : Vector p) :
    Continuous (fun x => restorationFourthDerivative s x z y w) := by
  simp_rw [restorationFourthDerivative_eq_coordinate,matrixQuadratic]
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  have hc : Continuous (fun x => ∑ l, ∑ m, z l*s.mixedFourthDerivativeF x j k l m*z m) := by
    apply continuous_finset_sum
    intro l _
    apply continuous_finset_sum
    intro m _
    exact (continuous_const.mul (s.continuous_fourthDerivative j k l m)).mul continuous_const
  exact continuous_const.mul hc

theorem cap_restorationFourthDerivative_abs_le {p : ℕ} (s : FaceSmoother p)
    (x z y w : Vector p) {δ : ℝ} (hδ : 0 ≤ δ) (hz : ‖z‖ ≤ δ) (hy : ‖y‖ ≤ δ) (hw : ‖w‖ ≤ δ) :
    |restorationFourthDerivative s x z y w| ≤ (p : ℝ)^4*(75/s.bandwidth^4)*δ^4 := by
  have hD (j k l m : Fin p) : |s.mixedFourthDerivativeF x j k l m| ≤ 75/s.bandwidth^4 := by
    simpa only [Real.norm_eq_abs] using s.norm_fourthDerivative_le x j k l m
  have hzz (j : Fin p) : |z j| ≤ δ := (norm_le_pi_norm z j).trans hz
  have hyy (j : Fin p) : |y j| ≤ δ := (norm_le_pi_norm y j).trans hy
  have hww (j : Fin p) : |w j| ≤ δ := (norm_le_pi_norm w j).trans hw
  simp_rw [restorationFourthDerivative_eq_coordinate,matrixQuadratic,Finset.mul_sum]
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, (75/s.bandwidth^4)*δ^4 := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro m _
      simp only [abs_mul]
      calc
        _ ≤ δ*δ*(δ*(75/s.bandwidth^4)*δ) := by
          gcongr
          · exact hww j
          · exact hyy k
          · exact hzz l
          · exact hD j k l m
          · exact hzz m
        _ = _ := by ring
    _ = _ := by simp; ring

theorem cap_restorationFourthDerivative_bounded {p : ℕ} (s : FaceSmoother p) (z y w : Vector p) :
    ∃ C : ℝ, ∀ x, |restorationFourthDerivative s x z y w| ≤ C := by
  let δ := ‖z‖+‖y‖+‖w‖
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hz : ‖z‖ ≤ δ := by dsimp only [δ]; linarith [norm_nonneg y,norm_nonneg w]
  have hy : ‖y‖ ≤ δ := by dsimp only [δ]; linarith [norm_nonneg z,norm_nonneg w]
  have hw : ‖w‖ ≤ δ := by dsimp only [δ]; linarith [norm_nonneg z,norm_nonneg y]
  exact ⟨_,fun x => cap_restorationFourthDerivative_abs_le s x z y w hδ hz hy hw⟩

end
end RectangleCLTArxivV1
