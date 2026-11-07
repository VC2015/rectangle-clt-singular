import RectangleCLT.BernoulliComparison
import RectangleCLT.ConvolutionEnvelopes
import RectangleCLT.GaussianEnvelope
import RectangleCLT.TranslationTaylor

/-! The common-point fourth-order contraction in Appendix G. The budget is
the maximum of the coordinate sums, with the sum over summands taken first.
The same positive derivative majorant controls every admissible shift. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {p n : ℕ}

/-- Actual maximum of the coordinate fourth-power sums (the Pi sup norm). -/
def coordinateFourthBudget (y : Fin n → Vector p) : ℝ :=
  ‖fun j : Fin p => ∑ i, (y i j) ^ 4‖

theorem coordinateFourthBudget_nonneg (y : Fin n → Vector p) :
    0 ≤ coordinateFourthBudget y := norm_nonneg _

theorem coordinate_fourth_sum_le_budget (y : Fin n → Vector p) (j : Fin p) :
    (∑ i, (y i j) ^ 4) ≤ coordinateFourthBudget y := by
  have h := norm_le_pi_norm (fun j : Fin p => ∑ i, (y i j) ^ 4) j
  exact (le_abs_self _).trans h

theorem sum_four_coordinate_products_le_budget (y : Fin n → Vector p)
    (j k l m : Fin p) :
    (∑ i, |y i j * y i k * y i l * y i m|) ≤ coordinateFourthBudget y := by
  calc
    _ ≤ ∑ i, ((y i j)^4 + (y i k)^4 + (y i l)^4 + (y i m)^4) / 4 :=
      Finset.sum_le_sum fun i _ => abs_four_product_le_fourth_mean _ _ _ _
    _ = ((∑ i, (y i j)^4) + (∑ i, (y i k)^4) +
        (∑ i, (y i l)^4) + (∑ i, (y i m)^4)) / 4 := by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib]
    _ ≤ coordinateFourthBudget y := by
      have hj := coordinate_fourth_sum_le_budget y j
      have hk := coordinate_fourth_sum_le_budget y k
      have hl := coordinate_fourth_sum_le_budget y l
      have hm := coordinate_fourth_sum_le_budget y m
      linarith

/-- Coordinate contraction of the actual fourth mixed derivative tensor. -/
def diagonalFourth (s : FaceSmoother p) (x y : Vector p) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m,
    s.mixedFourthDerivativeF x j k l m * (y j * y k * y l * y m)

theorem abs_diagonalFourth_shift_le (s : FaceSmoother p) (x y z : Vector p)
    (hz : ‖z‖ ≤ s.bandwidth) :
    |diagonalFourth s (x + z) y| ≤
      ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant x j k l m * |y j * y k * y l * y m| := by
  unfold diagonalFourth
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
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (s.abs_mixedFourthDerivativeF_shift_le x hz j k l m)
    (abs_nonneg _)

/-- Simultaneous local shifts retain the coordinate maximum after summing
over observations. No sum of vector fourth norms is substituted. -/
theorem common_point_fourth_contraction_majorant (s : FaceSmoother p) (x : Vector p)
    (y z : Fin n → Vector p) (hz : ∀ i, ‖z i‖ ≤ s.bandwidth) :
    (∑ i, |diagonalFourth s (x + z i) (y i)|) ≤
      coordinateFourthBudget y * (∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant x j k l m) := by
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant x j k l m * |y i j * y i k * y i l * y i m| :=
      Finset.sum_le_sum fun i _ => abs_diagonalFourth_shift_le s x (y i) (z i) (hz i)
    _ = ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m *
        (∑ i, |y i j * y i k * y i l * y i m|) := by
      simp only [Finset.mul_sum]
      exact (Finset.sum_comm.trans (congrArg _ (funext fun _ =>
        Finset.sum_comm.trans (congrArg _ (funext fun _ =>
          Finset.sum_comm.trans (congrArg _ (funext fun _ => Finset.sum_comm)))))))
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        s.fourthLocalMajorant x j k l m * coordinateFourthBudget y := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      apply Finset.sum_le_sum; intro m _
      exact mul_le_mul_of_nonneg_left (sum_four_coordinate_products_le_budget y j k l m)
        (s.fourthLocalMajorant_nonneg x j k l m)
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum, mul_comm]

theorem common_point_fourth_contraction (s : FaceSmoother p) (x : Vector p)
    (y z : Fin n → Vector p) (hz : ∀ i, ‖z i‖ ≤ s.bandwidth) :
    (∑ i, |diagonalFourth s (x + z i) (y i)|) ≤
      coordinateFourthBudget y *
        ((75 * (Real.exp 2)^5) * s.F x * (1 - s.F x) / s.bandwidth^4) :=
  (common_point_fourth_contraction_majorant s x y z hz).trans
    (mul_le_mul_of_nonneg_left (s.sum_fourthLocalMajorant_le_variance x)
      (coordinateFourthBudget_nonneg y))

theorem diagonalFourth_eq_translationD4 (s : FaceSmoother p) (x y : Vector p) :
    diagonalFourth s x y = s.translationD4 x y := by
  simp only [diagonalFourth, FaceSmoother.translationD4, mul_assoc]

theorem continuous_diagonalFourth (s : FaceSmoother p) (y : Vector p) :
    Continuous (fun x => diagonalFourth s x y) := by
  simpa only [diagonalFourth_eq_translationD4] using s.continuous_translationD4 y

/-- Gaussian averaging follows the deterministic common-point contraction.
Every summand retains its own shift; the covariance factor may be singular. -/
theorem gaussian_common_point_fourth_contraction {p n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p)
    (y z : Fin n → Vector p) (hz : ∀ i, ‖z i‖ ≤ s.bandwidth) :
    (∫ g : Vector p, ∑ i, |diagonalFourth s ((g + r) + z i) (y i)| ∂gaussianLaw A) ≤
      coordinateFourthBudget y *
        ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
          Real.sqrt (dimensionLog p / v) / s.bandwidth^3) := by
  let M : Vector p → ℝ := fun g => ∑ j, ∑ k, ∑ l, ∑ m,
    s.fourthLocalMajorant (g + r) j k l m
  have hM : Integrable M (gaussianLaw A) := by
    apply integrable_finset_sum; intro j _
    apply integrable_finset_sum; intro k _
    apply integrable_finset_sum; intro l _
    apply integrable_finset_sum; intro m _
    exact s.integrable_fourthLocalMajorant_comp (gaussianLaw A) (fun g => g + r)
      (measurable_id.add measurable_const) j k l m
  have hupper := hM.const_mul (coordinateFourthBudget y)
  have hcont : Continuous (fun g : Vector p =>
      ∑ i, |diagonalFourth s ((g + r) + z i) (y i)|) := by
    apply continuous_finset_sum; intro i _
    exact ((continuous_diagonalFourth s (y i)).comp
      ((continuous_id.add continuous_const).add continuous_const)).abs
  have hbound (g : Vector p) := common_point_fourth_contraction_majorant s (g + r) y z hz
  have hlo : Integrable (fun g : Vector p =>
      ∑ i, |diagonalFourth s ((g + r) + z i) (y i)|) (gaussianLaw A) :=
    hupper.mono' hcont.aestronglyMeasurable (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      exact hbound g)
  calc
    _ ≤ ∫ g, coordinateFourthBudget y * M g ∂gaussianLaw A :=
      integral_mono hlo hupper (fun g => hbound g)
    _ = coordinateFourthBudget y * ∫ g, M g ∂gaussianLaw A := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (s.gaussian_integral_sum_fourthLocalMajorant_le hp A hv hdiag r)
      (coordinateFourthBudget_nonneg y)

end
end RectangleCLT.Companion.SplitV4
