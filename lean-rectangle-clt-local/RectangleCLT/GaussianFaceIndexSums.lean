import RectangleCLT.GaussianFaceEnumeration
import RectangleCLT.GaussianSoftRecursion

/-! Exact finite reindexing of coordinate/sign sums by compatible ordered faces.
No dimension-dependent multiplicity is introduced. -/

open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

private theorem indexTuple_ext {p q : ℕ} {S T : CompatibleFaceTuple p q}
    (h : S.face = T.face) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Ordered tuples over all faces are the injective-coordinate face functions. -/
def orderedFaceFunctionEquiv {p q : ℕ} :
    OrderedFaceTuples (Finset.univ : Finset (Face p)) q ≃
      {f : Fin q → Face p // Function.Injective (fun i => (f i).1)} where
  toFun S := ⟨S.val.face, S.val.coordinate_injective⟩
  invFun f := ⟨⟨f.val, f.property⟩, fun _ => Finset.mem_univ _⟩
  left_inv S := by apply Subtype.ext; apply indexTuple_ext; rfl
  right_inv f := by rfl

/-- Restriction to compatible coordinates is exactly the zero extension on
all face functions; the weight may depend on their order. -/
theorem sum_orderedFaceTuples_eq_sum_face_functions {p q : ℕ}
    (g : (Fin q → Face p) → ℝ) :
    (∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) q, g S.val.face) =
      ∑ f : Fin q → Face p, if Function.Injective (fun i => (f i).1) then g f else 0 := by
  classical
  calc
    _ = ∑ f : {f : Fin q → Face p // Function.Injective (fun i => (f i).1)}, g f.val :=
      (orderedFaceFunctionEquiv (p := p) (q := q)).sum_comp (fun f => g f.val)
    _ = _ := by
      rw [← Finset.sum_subtype (Finset.univ.filter
        (fun f : Fin q → Face p => Function.Injective (fun i => (f i).1))) (by simp) g]
      simp only [Finset.sum_filter]

private theorem sum_pi_fin_succ {α : Type*} [Fintype α] {q : ℕ}
    (g : (Fin (q + 1) → α) → ℝ) :
    (∑ f, g f) = ∑ a, ∑ f : Fin q → α, g (Fin.cons a f) := by
  have he := (Fin.consEquiv (fun _ : Fin (q + 1) => α)).sum_comp g
  rw [Fintype.sum_prod_type] at he
  exact he.symm

private theorem sum_pi_fin_one {α : Type*} [Fintype α]
    (g : (Fin 1 → α) → ℝ) : (∑ f, g f) = ∑ a, g ![a] := by
  rw [sum_pi_fin_succ]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fintype.sum_unique]
  congr 1

private theorem sum_pi_fin_two {α : Type*} [Fintype α]
    (g : (Fin 2 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, g ![a, b] := by
  rw [sum_pi_fin_succ]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_one]
  rfl

private theorem sum_pi_fin_three {α : Type*} [Fintype α]
    (g : (Fin 3 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, ∑ c, g ![a, b, c] := by
  rw [sum_pi_fin_succ]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_two]
  rfl

private theorem sum_pi_fin_four {α : Type*} [Fintype α]
    (g : (Fin 4 → α) → ℝ) : (∑ f, g f) = ∑ a, ∑ b, ∑ c, ∑ d, g ![a, b, c, d] := by
  rw [sum_pi_fin_succ]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_pi_fin_three]
  rfl

private theorem injective_pair_coordinates {p : ℕ} (j k : Fin p) (b c : Bool) :
    Function.Injective (fun i : Fin 2 => ((![((j, b) : Face p), (k, c)]) i).1) ↔ j ≠ k := by
  simp [Function.Injective, Fin.forall_fin_succ]
  exact fun h => Ne.symm h

private theorem injective_triple_coordinates {p : ℕ} (j k l : Fin p) (b c d : Bool) :
    Function.Injective (fun i : Fin 3 => ((![((j, b) : Face p), (k, c), (l, d)]) i).1) ↔
      j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  simp [Function.Injective, Fin.forall_fin_succ]
  tauto

/-- One coordinate and its two signs enumerate all ordered singleton faces. -/
theorem sum_singleton_coordinate_signs {p : ℕ} (g : (Fin 1 → Face p) → ℝ) :
    (∑ j : Fin p, ∑ b : Bool, g ![(j, b)]) =
      ∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1, g S.val.face := by
  classical
  rw [sum_orderedFaceTuples_eq_sum_face_functions, sum_pi_fin_one]
  simp only [Function.Injective, Fin.forall_fin_one, forall_const, implies_true, ite_true]
  exact (Fintype.sum_prod_type (fun f : Face p => g ![f])).symm

/-- Distinct ordered coordinates and independent signs enumerate ordered pairs. -/
theorem sum_pair_coordinate_signs {p : ℕ} (g : (Fin 2 → Face p) → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, if j ≠ k then
      ∑ b : Bool, ∑ c : Bool, g ![(j, b), (k, c)] else 0) =
      ∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2, g S.val.face := by
  classical
  rw [sum_orderedFaceTuples_eq_sum_face_functions, sum_pi_fin_two]
  simp_rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j ≠ k <;> simp [injective_pair_coordinates, hjk]

/-- Three pairwise distinct ordered coordinates with signs enumerate triples. -/
theorem sum_triple_coordinate_signs {p : ℕ} (g : (Fin 3 → Face p) → ℝ) :
    (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, if j ≠ k ∧ j ≠ l ∧ k ≠ l then
      ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, g ![(j, b), (k, c), (l, d)] else 0) =
      ∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3, g S.val.face := by
  classical
  rw [sum_orderedFaceTuples_eq_sum_face_functions, sum_pi_fin_three]
  simp_rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => arg 2; intro b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hjkl : j ≠ k ∧ j ≠ l ∧ k ≠ l <;> simp [injective_triple_coordinates, hjkl]

private theorem injective_snoc_coordinates_iff {p q : ℕ}
    (f : Fin q → Face p) (a : Face p) :
    Function.Injective (fun i : Fin (q + 1) =>
      (Fin.snoc (α := fun _ : Fin (q + 1) => Face p) f a i).1) ↔
      Function.Injective (fun i => (f i).1) ∧ ∀ i, (f i).1 ≠ a.1 := by
  constructor
  · intro h
    constructor
    · intro i j hij
      apply Fin.castSucc_injective q
      apply h
      simpa using hij
    · intro i hi
      exact Fin.castSucc_ne_last i (h (by simpa using hi))
  · rintro ⟨hf, ha⟩ i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · exact congrArg Fin.castSucc (hf (by simpa using hij))
      · exact (ha i (by simpa using hij)).elim
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · exact (ha j (by simpa using hij.symm)).elim
      · rfl

private theorem mem_inactive_raw_faces_iff {p q : ℕ}
    (f : Fin q → Face p) (a : Face p) :
    a ∈ inactiveCoordinateFaces (Finset.univ.image f) ↔ ∀ i, (f i).1 ≠ a.1 := by
  classical
  constructor
  · intro ha i hi
    apply (Finset.mem_filter.mp ha).2
    exact Finset.mem_image.mpr ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  · intro ha
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact ha i hba

/-- Appending one previously inactive coordinate counts each longer ordered
tuple once, by its unique prefix and last face. The weight can depend on the
full ordering. -/
theorem sum_orderedFaceTuples_extend {p q : ℕ}
    (g : (Fin (q + 1) → Face p) → ℝ) :
    (∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
      ∑ a ∈ inactiveCoordinateFaces (activeFaces S.val), g (Fin.snoc S.val.face a)) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) (q + 1), g T.val.face := by
  classical
  simp only [activeFaces]
  rw [sum_orderedFaceTuples_eq_sum_face_functions
    (fun f => ∑ a ∈ inactiveCoordinateFaces (Finset.univ.image f), g (Fin.snoc f a))]
  rw [sum_orderedFaceTuples_eq_sum_face_functions]
  have he := (Fin.snocEquiv (fun _ : Fin (q + 1) => Face p)).sum_comp
    (fun f => if Function.Injective (fun i => (f i).1) then g f else 0)
  rw [Fintype.sum_prod_type] at he
  simp only [Fin.snocEquiv_apply] at he
  rw [← he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : Function.Injective (fun i => (f i).1)
  · simp only [hf, ite_true]
    rw [← Finset.sum_filter]
    have hs : inactiveCoordinateFaces (Finset.univ.image f) =
        Finset.univ.filter (fun a : Face p =>
          Function.Injective (fun i : Fin (q + 1) =>
            (Fin.snoc (α := fun _ : Fin (q + 1) => Face p) f a i).1)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        injective_snoc_coordinates_iff, hf, true_and, mem_inactive_raw_faces_iff]
    rw [hs]
    apply Finset.sum_congr rfl
    intro a _
    rfl
  · simp only [hf, ite_false]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro a _
    simp only [Fin.snocEquiv_apply, injective_snoc_coordinates_iff, hf, false_and, ite_false]

/-- Zero weights on tuples containing a missing face allow restriction from
all coordinate/sign indices to the rectangle's actual face family. -/
theorem sum_orderedFaceTuples_univ_eq_restrict {p q : ℕ}
    (faces : Finset (Face p)) (w : CompatibleFaceTuple p q → ℝ)
    (hw : ∀ S, (∃ i, S.face i ∉ faces) → w S = 0) :
    (∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) q, w S.val) =
      ∑ S : OrderedFaceTuples faces q, w S.val := by
  classical
  let e : OrderedFaceTuples (Finset.univ : Finset (Face p)) q ≃ CompatibleFaceTuple p q :=
    { toFun := Subtype.val
      invFun := fun S => ⟨S, fun _ => Finset.mem_univ _⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ S : CompatibleFaceTuple p q, w S := e.sum_comp w
    _ = ∑ S : CompatibleFaceTuple p q, if ∀ i, S.face i ∈ faces then w S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : ∀ i, S.face i ∈ faces
      · simp only [if_pos hS]
      · have hmissing : ∃ i, S.face i ∉ faces := not_forall.mp hS
        simp only [hS, ite_false, hw S hmissing]
    _ = _ := by
      have hs := Finset.sum_subtype (F := (inferInstance : Fintype (OrderedFaceTuples faces q)))
        (Finset.univ.filter (fun S : CompatibleFaceTuple p q => ∀ i, S.face i ∈ faces))
        (by simp) w
      rw [Finset.sum_filter] at hs
      exact hs

end

end RectangleCLT.GaussianTube
