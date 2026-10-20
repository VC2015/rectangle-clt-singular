import RectangleCLTCompanion.RestorationBound
import RectangleCLTCompanion.RestorationSmootherIBP

/-! The first two actual derivative partitions of the rational selector.
These are finite algebraic identities, with repeated faces included. -/

open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

theorem restoration_sum_pi_fin_one {α : Type*} [Fintype α]
    (g : (Fin 1 → α) → ℝ) : (∑ f, g f) = ∑ a, g ![a] := by
  have he := (Fin.consEquiv (fun _ : Fin 1 => α)).sum_comp g
  rw [Fintype.sum_prod_type] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fintype.sum_unique]
  rfl

theorem restoration_sum_pi_fin_two {α : Type*} [Fintype α]
    (g : (Fin 2 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, g ![a, b] := by
  have he := (Fin.consEquiv (fun _ : Fin 2 => α)).sum_comp g
  rw [Fintype.sum_prod_type] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  rw [restoration_sum_pi_fin_one]
  rfl

theorem sum_pi_normalDot_eq (x y : Vector p) :
    (∑ f, s.pi x f * FaceSmoother.normalDot f y) =
      (s.weights x).directionalMean y := rfl

theorem sum_pi_normalDot_mul_eq (x y z : Vector p) :
    (∑ f, s.pi x f * FaceSmoother.normalDot f y * FaceSmoother.normalDot f z) =
      ∑ j, (s.weights x).coordinateMass j * y j * z j := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro j _
  simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte,
    FaceWeights.coordinateMass, FaceSmoother.pi]
  ring

theorem sum_selectorTupleWeight_one_normalDot_eq (x y : Vector p) :
    (∑ α : Fin 1 → Face p, selectorTupleWeight s α x *
      FaceSmoother.normalDot (α 0) y) = s.F x * (s.weights x).directionalMean y := by
  rw [restoration_sum_pi_fin_one]
  simp only [selectorTupleWeight, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, mul_one]
  rw [← sum_pi_normalDot_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem sum_selectorTupleWeight_one_normalDot_mul_eq (x y z : Vector p) :
    (∑ α : Fin 1 → Face p, selectorTupleWeight s α x *
      FaceSmoother.normalDot (α 0) y * FaceSmoother.normalDot (α 0) z) =
        s.F x * ∑ j, (s.weights x).coordinateMass j * y j * z j := by
  rw [restoration_sum_pi_fin_one]
  simp only [selectorTupleWeight, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, mul_one]
  rw [← sum_pi_normalDot_mul_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem sum_selectorTupleWeight_two_normalDot_eq (x y z : Vector p) :
    (∑ α : Fin 2 → Face p, selectorTupleWeight s α x *
      FaceSmoother.normalDot (α 0) y * FaceSmoother.normalDot (α 1) z) =
        s.F x * (s.weights x).directionalMean y * (s.weights x).directionalMean z := by
  rw [restoration_sum_pi_fin_two]
  simp only [selectorTupleWeight, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, mul_one]
  rw [← sum_pi_normalDot_eq, ← sum_pi_normalDot_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  ring

def restorationHessian (x y z : Vector p) : ℝ :=
  ∑ j, ∑ l, s.mixedSecondDerivativeF x j l * y j * z l

theorem restorationHessian_eq_moments (x y z : Vector p) :
    restorationHessian s x y z = (s.F x / s.bandwidth ^ 2) *
      (2 * (s.weights x).directionalMean y * (s.weights x).directionalMean z -
        ∑ j, (s.weights x).coordinateMass j * y j * z j) := by
  have hdiag : (∑ j, ∑ l, (s.weights x).diagonalMass j l * y j * z l) =
      ∑ j, (s.weights x).coordinateMass j * y j * z j := by
    classical
    apply Finset.sum_congr rfl
    intro j _
    simp [FaceWeights.diagonalMass]
  rw [← hdiag]
  simp only [restorationHessian, s.mixedSecondDerivativeF_eq,
    FaceWeights.directionalMean_eq, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  · conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

/-- The two partitions of two derivative directions, with the exact
coefficients `2` and `−1` from Appendix B. -/
theorem restorationHessian_eq_selector_partitions (x y z : Vector p) :
    restorationHessian s x y z =
      (2 * (∑ α : Fin 2 → Face p, selectorTupleWeight s α x *
        FaceSmoother.normalDot (α 0) y * FaceSmoother.normalDot (α 1) z) -
      (∑ α : Fin 1 → Face p, selectorTupleWeight s α x *
        FaceSmoother.normalDot (α 0) y * FaceSmoother.normalDot (α 0) z)) /
          s.bandwidth ^ 2 := by
  rw [restorationHessian_eq_moments, sum_selectorTupleWeight_two_normalDot_eq,
    sum_selectorTupleWeight_one_normalDot_mul_eq]
  ring

end
end RectangleCLT.Companion
