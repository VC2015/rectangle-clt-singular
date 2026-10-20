import RectangleCLT.GaussianFaceIndexSums

/-! Fourth-order coordinate/sign indexing, without dimension factors. -/

open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

private theorem sum_pi_fin_succ_four {α : Type*} [Fintype α] {q : ℕ}
    (g : (Fin (q + 1) → α) → ℝ) :
    (∑ f, g f) = ∑ a, ∑ f : Fin q → α, g (Fin.cons a f) := by
  have he := (Fin.consEquiv (fun _ : Fin (q + 1) => α)).sum_comp g
  rw [Fintype.sum_prod_type] at he
  exact he.symm

private theorem sum_pi_fin_one_four {α : Type*} [Fintype α]
    (g : (Fin 1 → α) → ℝ) : (∑ f, g f) = ∑ a, g ![a] := by
  rw [sum_pi_fin_succ_four]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fintype.sum_unique]
  congr 1

private theorem sum_pi_fin_two_four {α : Type*} [Fintype α]
    (g : (Fin 2 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, g ![a, b] := by
  rw [sum_pi_fin_succ_four]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_one_four]
  rfl

private theorem sum_pi_fin_three_four {α : Type*} [Fintype α]
    (g : (Fin 3 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, ∑ c, g ![a, b, c] := by
  rw [sum_pi_fin_succ_four]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_two_four]
  rfl

private theorem sum_pi_fin_four {α : Type*} [Fintype α]
    (g : (Fin 4 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, ∑ c, ∑ d, g ![a, b, c, d] := by
  rw [sum_pi_fin_succ_four]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_three_four]
  rfl

private theorem injective_quadruple_coordinates {p : ℕ}
    (j k l m : Fin p) (b c d e : Bool) :
    Function.Injective (fun i : Fin 4 =>
      ((![((j, b) : Face p), (k, c), (l, d), (m, e)]) i).1) ↔
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m := by
  simp [Function.Injective, Fin.forall_fin_succ]
  tauto

/-- Four distinct ordered coordinates with signs enumerate compatible ordered
quadruples exactly once. The weight may depend on their full ordering. -/
theorem sum_quadruple_coordinate_signs {p : ℕ} (g : (Fin 4 → Face p) → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, ∑ m : Fin p,
      if j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m then
        ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
          g ![(j, b), (k, c), (l, d), (m, e)] else 0) =
      ∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4, g S.val.face := by
  classical
  rw [sum_orderedFaceTuples_eq_sum_face_functions, sum_pi_fin_four]
  simp_rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => arg 2; intro b; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  conv_rhs => arg 2; intro b; arg 2; intro c; rw [Finset.sum_comm]
  conv_rhs => arg 2; intro b; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hdistinct : j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m <;>
    simp [injective_quadruple_coordinates, hdistinct]

end

end RectangleCLT.GaussianTube
