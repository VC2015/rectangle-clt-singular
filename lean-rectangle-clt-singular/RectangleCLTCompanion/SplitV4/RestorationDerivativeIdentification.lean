import RectangleCLTCompanion.SplitV4.SmootherC4
import RectangleCLTCompanion.RestorationSmootherIBP

/-! Canonical mixed Fréchet contractions for the actual face smoother.
The coordinate tensor order is the order established by `SmootherC4`;
no derivative bound or integration-by-parts estimate is assumed. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem multilinear_eq_sum_coordinate_directions {p k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vector p) ℝ)
    (v : Fin k → Vector p) :
    M v = ∑ α : Fin k → Fin p,
      (∏ i, v i (α i)) * M (fun i => FaceSmoother.coordinateDirection (α i)) := by
  calc
    _ = M (fun i => ∑ j, v i j • FaceSmoother.coordinateDirection j) := by
      congr 1
      funext i
      exact vector_eq_sum_coordinate_directions (v i)
    _ = _ := by
      rw [M.map_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [M.map_smul_univ]
      rfl

private theorem sum_fin_succ_functions {α : Type*} [Fintype α] {k : ℕ}
    (f : (Fin (k + 1) → α) → ℝ) :
    (∑ v : Fin (k + 1) → α, f v) = ∑ a, ∑ v : Fin k → α, f (Fin.cons a v) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv] using
    ((Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp f).symm

private theorem sum_three_reverse {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

private theorem sum_four_reverse {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ c, ∑ b, f a b c d :=
      Finset.sum_congr rfl (fun a _ => sum_three_reverse (f a))
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        _ = ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- Genuine rank-three derivative, with its repeated pair first. -/
def restorationThirdDerivative {p : ℕ} (s : FaceSmoother p)
    (x z y : Vector p) : ℝ := iteratedFDeriv ℝ 3 s.F x ![z, z, y]

/-- Genuine rank-four derivative, with its repeated pair first. -/
def restorationFourthDerivative {p : ℕ} (s : FaceSmoother p)
    (x z y w : Vector p) : ℝ := iteratedFDeriv ℝ 4 s.F x ![z, z, y, w]

theorem restorationThirdDerivative_eq_coordinate {p : ℕ} (s : FaceSmoother p)
    (x z y : Vector p) :
    restorationThirdDerivative s x z y = ∑ j, y j *
      matrixQuadratic (fun l m => s.mixedThirdDerivativeF x j l m) z := by
  rw [restorationThirdDerivative, multilinear_eq_sum_coordinate_directions]
  simp_rw [smoother_iteratedFDeriv_three_coordinate]
  rw [sum_fin_succ_functions]
  simp_rw [sum_fin_succ_functions]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Finset.univ_unique, Finset.sum_singleton, mul_one]
  rw [sum_three_reverse]
  simp only [matrixQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  simp [Fin.prod_univ_succ]
  change (z m * (z l * y j)) * s.mixedThirdDerivativeF x j l m = _
  ring

theorem restorationFourthDerivative_eq_coordinate {p : ℕ} (s : FaceSmoother p)
    (x z y w : Vector p) :
    restorationFourthDerivative s x z y w = ∑ j, ∑ k, w j * y k *
      matrixQuadratic (fun l m => s.mixedFourthDerivativeF x j k l m) z := by
  rw [restorationFourthDerivative, multilinear_eq_sum_coordinate_directions]
  simp_rw [smoother_iteratedFDeriv_four_coordinate]
  rw [sum_fin_succ_functions]
  simp_rw [sum_fin_succ_functions]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Finset.univ_unique, Finset.sum_singleton, mul_one]
  rw [sum_four_reverse]
  simp only [matrixQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  simp [Fin.prod_univ_succ]
  change (z m * (z l * (y k * w j))) * s.mixedFourthDerivativeF x j k l m = _
  ring

theorem smootherC4Test_third_eq_restorationThirdDerivative {p : ℕ}
    (s : FaceSmoother p) (x z y : Vector p) :
    (smootherC4Test s).third x ![z, z, y] = restorationThirdDerivative s x z y := rfl

theorem smootherC4Test_fourth_eq_restorationFourthDerivative {p : ℕ}
    (s : FaceSmoother p) (x z y w : Vector p) :
    (smootherC4Test s).fourth x ![z, z, y, w] = restorationFourthDerivative s x z y w := rfl

end
end RectangleCLT.Companion.SplitV4
