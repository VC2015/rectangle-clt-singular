import RectangleCLT.GaussianFourthDetAssembly
import RectangleCLT.GaussianFaceIndexFour

/-! Zero extensions of explicit compatible-face caps and their dimension-free
coordinate/sign enumeration. -/

open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

/-- Extend a cap on compatible tuples by zero to all ordered face vectors. -/
def compatibleTupleCap {p q : ℕ} (g : CompatibleFaceTuple p q → ℝ)
    (f : Fin q → Face p) : ℝ := by
  classical
  exact if hf : Function.Injective (fun i => (f i).1) then g ⟨f, hf⟩ else 0

theorem compatibleTupleCap_of_injective {p q : ℕ} (g : CompatibleFaceTuple p q → ℝ)
    (f : Fin q → Face p) (hf : Function.Injective (fun i => (f i).1)) :
    compatibleTupleCap g f = g ⟨f, hf⟩ := by
  classical
  simp only [compatibleTupleCap, dif_pos hf]

@[simp] theorem compatibleTupleCap_face {p q : ℕ} (g : CompatibleFaceTuple p q → ℝ)
    (T : CompatibleFaceTuple p q) : compatibleTupleCap g T.face = g T := by
  rw [compatibleTupleCap_of_injective g T.face T.coordinate_injective]

@[simp] theorem compatibleTupleCap_of_not_injective {p q : ℕ} (g : CompatibleFaceTuple p q → ℝ)
    (f : Fin q → Face p) (hf : ¬ Function.Injective (fun i => (f i).1)) :
    compatibleTupleCap g f = 0 := by
  classical
  simp only [compatibleTupleCap, dif_neg hf]

theorem compatibleTupleCap_nonneg {p q : ℕ} (g : CompatibleFaceTuple p q → ℝ)
    (hg : ∀ T, 0 ≤ g T) (f : Fin q → Face p) : 0 ≤ compatibleTupleCap g f := by
  classical
  unfold compatibleTupleCap
  split_ifs with hf
  · exact hg _
  · exact le_rfl

theorem injective_singleton_coordinates {p : ℕ} (j : Fin p) (b : Bool) :
    Function.Injective (fun i : Fin 1 => ((![((j, b) : Face p)]) i).1) ↔ True := by
  simp [Function.Injective, Fin.forall_fin_succ]

theorem injective_pair_coordinates {p : ℕ} (j k : Fin p) (b c : Bool) :
    Function.Injective (fun i : Fin 2 => ((![((j, b) : Face p), (k, c)]) i).1) ↔ j ≠ k := by
  simp [Function.Injective, Fin.forall_fin_succ]
  exact fun h => Ne.symm h

theorem injective_triple_coordinates {p : ℕ} (j k l : Fin p) (b c d : Bool) :
    Function.Injective (fun i : Fin 3 => ((![((j, b) : Face p), (k, c), (l, d)]) i).1) ↔
      j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  simp [Function.Injective, Fin.forall_fin_succ]
  tauto

theorem injective_quadruple_face_coordinates {p : ℕ}
    (j k l m : Fin p) (b c d e : Bool) :
    Function.Injective (fun i : Fin 4 =>
      ((![((j, b) : Face p), (k, c), (l, d), (m, e)]) i).1) ↔
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m := by
  simp [Function.Injective, Fin.forall_fin_succ]
  tauto

theorem injective_quadruple_coordinates {p : ℕ}
    (j k l m : Fin p) (b c d e : Bool) :
    Function.Injective (fun i : Fin 4 =>
      ((![((j, b) : Face p), (k, c), (l, d), (m, e)]) i).1) ↔
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m :=
  injective_quadruple_face_coordinates j k l m b c d e

theorem sum_singleton_compatibleTupleCap {p : ℕ} (g : CompatibleFaceTuple p 1 → ℝ) :
    (∑ j : Fin p, ∑ b : Bool, compatibleTupleCap g ![(j, b)]) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1, g T.val := by
  simpa only [compatibleTupleCap_face] using sum_singleton_coordinate_signs (compatibleTupleCap g)

theorem sum_pair_compatibleTupleCap {p : ℕ} (g : CompatibleFaceTuple p 2 → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, if j ≠ k then
      ∑ b : Bool, ∑ c : Bool, compatibleTupleCap g ![(j, b), (k, c)] else 0) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2, g T.val := by
  classical
  simpa only [compatibleTupleCap_face] using sum_pair_coordinate_signs (compatibleTupleCap g)

theorem sum_triple_compatibleTupleCap {p : ℕ} (g : CompatibleFaceTuple p 3 → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, if j ≠ k ∧ j ≠ l ∧ k ≠ l then
      ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, compatibleTupleCap g ![(j, b), (k, c), (l, d)] else 0) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3, g T.val := by
  classical
  simpa only [compatibleTupleCap_face] using sum_triple_coordinate_signs (compatibleTupleCap g)

theorem sum_quadruple_compatibleTupleCap {p : ℕ} (g : CompatibleFaceTuple p 4 → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, ∑ m : Fin p,
      if j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m then
        ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
          compatibleTupleCap g ![(j, b), (k, c), (l, d), (m, e)] else 0) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4, g T.val := by
  classical
  simpa only [compatibleTupleCap_face] using sum_quadruple_coordinate_signs (compatibleTupleCap g)

end
end RectangleCLT.GaussianTube
