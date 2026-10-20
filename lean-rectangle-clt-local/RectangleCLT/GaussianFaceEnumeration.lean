import RectangleCLT.GaussianTubeUnion
import Mathlib.Data.Fintype.Perm

/-! Order-invariant active Gram determinants and exact factorial multiplicity
of ordered compatible tuples. This converts ordered derivative sums into
sums over the actual face sets without an ambient dimension factor. -/

open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

private theorem tuple_ext {p q : ℕ} {S T : CompatibleFaceTuple p q}
    (h : ∀ i, S.face i = T.face i) : S = T := by
  cases S with
  | mk fs hs => cases T with
    | mk ft ht =>
      have hh : fs = ft := funext h
      cases hh
      rfl

private theorem tuple_face_injective {p q : ℕ} (S : CompatibleFaceTuple p q) :
    Function.Injective S.face := by
  intro i j hij
  exact S.coordinate_injective (congrArg Prod.fst hij)

/-- A compatible tuple enumerates its active face set bijectively. -/
def tupleFaceEquiv {p q : ℕ} (S : CompatibleFaceTuple p q) : Fin q ≃ activeFaces S :=
  Equiv.ofBijective (fun i => ⟨S.face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => tuple_face_injective S (congrArg Subtype.val h), by
      intro f
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp f.property
      exact ⟨i, Subtype.ext hi⟩⟩

private theorem finset_cast_val {α : Type*} {U V : Finset α} (h : U = V) (x : U) :
    ((Equiv.cast (congrArg (fun T : Finset α => ↥T) h)) x).val = x.val := by
  subst V
  rfl

/-- The unique permutation matching two orderings of the same active face set. -/
def tupleIndexEquiv {p q : ℕ} (S T : CompatibleFaceTuple p q)
    (hset : activeFaces S = activeFaces T) : Equiv.Perm (Fin q) :=
  (tupleFaceEquiv S).trans
    ((Equiv.cast (congrArg (fun U : Finset (Face p) => ↥U) hset)).trans (tupleFaceEquiv T).symm)

theorem tupleIndexEquiv_face {p q : ℕ} (S T : CompatibleFaceTuple p q)
    (hset : activeFaces S = activeFaces T) (i : Fin q) :
    T.face (tupleIndexEquiv S T hset i) = S.face i := by
  have hh := congrArg Subtype.val ((tupleFaceEquiv T).apply_symm_apply
    ((Equiv.cast (congrArg (fun U : Finset (Face p) => ↥U) hset)) (tupleFaceEquiv S i)))
  exact hh.trans (finset_cast_val hset (tupleFaceEquiv S i))

/-- Gram determinants depend only on the active face set, including signs,
and are independent of its chosen enumeration. -/
theorem gram_det_eq_of_activeFaces_eq {p q : ℕ}
    (S T : CompatibleFaceTuple p q) (Q : Matrix (Fin p) (Fin p) ℝ)
    (hset : activeFaces S = activeFaces T) : (S.gram Q).det = (T.gram Q).det := by
  let e := tupleIndexEquiv S T hset
  have hmatrix : S.gram Q = (T.gram Q).submatrix e e := by
    ext i j
    simp only [CompatibleFaceTuple.gram, Matrix.submatrix_apply,
      tupleIndexEquiv_face, e]
  rw [hmatrix, Matrix.det_submatrix_equiv_self]

/-- Permute a compatible tuple without changing its complete face set. -/
def reorderTuple {p q : ℕ} (S : CompatibleFaceTuple p q) (σ : Equiv.Perm (Fin q)) :
    CompatibleFaceTuple p q where
  face i := S.face (σ i)
  coordinate_injective := fun _ _ h => σ.injective (S.coordinate_injective h)

@[simp] theorem activeFaces_reorderTuple {p q : ℕ} (S : CompatibleFaceTuple p q)
    (σ : Equiv.Perm (Fin q)) : activeFaces (reorderTuple S σ) = activeFaces S := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
    exact Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, hi⟩
  · intro hf
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
    exact Finset.mem_image.mpr ⟨σ.symm i, Finset.mem_univ _, by simpa [reorderTuple] using hi⟩

noncomputable instance {p q : ℕ} : Fintype (CompatibleFaceTuple p q) := by
  classical
  exact Fintype.ofInjective (fun S : CompatibleFaceTuple p q => S.face)
    (fun _ _ h => tuple_ext (congrFun h))

/-- All ordered compatible tuples using faces from the specified rectangle. -/
def OrderedFaceTuples {p : ℕ} (faces : Finset (Face p)) (q : ℕ) :=
  {S : CompatibleFaceTuple p q // ∀ i, S.face i ∈ faces}

noncomputable instance {p q : ℕ} {faces : Finset (Face p)} :
    Fintype (OrderedFaceTuples faces q) := by
  classical
  unfold OrderedFaceTuples
  exact Fintype.ofFinite _

/-- Discard the ordering of an actual compatible tuple. -/
def tupleActiveSet {p q : ℕ} {faces : Finset (Face p)}
    (S : OrderedFaceTuples faces q) : CompatibleFaceSets faces q := by
  classical
  refine ⟨activeFaces S.val, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact S.property i
  · simp only [activeFaces, Finset.card_image_of_injective _ (tuple_face_injective S.val),
      Finset.card_univ, Fintype.card_fin]
  · intro f hf g hg hcoord
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
    exact congrArg S.val.face (S.val.coordinate_injective hcoord)

private theorem compatibleSetTuple_mem {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) (i : Fin q) : (compatibleSetTuple T).face i ∈ faces := by
  apply T.property.1
  rw [← activeFaces_compatibleSetTuple T]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The fibre of the map forgetting tuple order. -/
def OrderingFiber {p q : ℕ} {faces : Finset (Face p)} (T : CompatibleFaceSets faces q) :=
  {S : OrderedFaceTuples faces q // tupleActiveSet S = T}

noncomputable instance {p q : ℕ} {faces : Finset (Face p)}
    {T : CompatibleFaceSets faces q} : Fintype (OrderingFiber T) := by
  classical
  unfold OrderingFiber
  infer_instance

private def orderingMap {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) (σ : Equiv.Perm (Fin q)) : OrderingFiber T := by
  refine ⟨⟨reorderTuple (compatibleSetTuple T) σ, fun i => compatibleSetTuple_mem T (σ i)⟩, ?_⟩
  apply Subtype.ext
  change activeFaces (reorderTuple (compatibleSetTuple T) σ) = T.val
  rw [activeFaces_reorderTuple, activeFaces_compatibleSetTuple]

private theorem orderingMap_bijective {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) : Function.Bijective (orderingMap T) := by
  constructor
  · intro σ τ hστ
    apply Equiv.ext
    intro i
    apply tuple_face_injective (compatibleSetTuple T)
    exact congrArg (fun U : OrderingFiber T => U.val.val.face i) hστ
  · intro U
    have hset : activeFaces U.val.val = activeFaces (compatibleSetTuple T) := by
      have hh := congrArg Subtype.val U.property
      change activeFaces U.val.val = T.val at hh
      simpa only [activeFaces_compatibleSetTuple] using hh
    let σ := tupleIndexEquiv U.val.val (compatibleSetTuple T) hset
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply tuple_ext
    intro i
    exact tupleIndexEquiv_face U.val.val (compatibleSetTuple T) hset i

/-- There are exactly `q!` orderings of every compatible active set. -/
def orderingEquivPerm {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) : Equiv.Perm (Fin q) ≃ OrderingFiber T :=
  Equiv.ofBijective (orderingMap T) (orderingMap_bijective T)

theorem card_orderingFiber {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) : Fintype.card (OrderingFiber T) = q.factorial := by
  rw [← Fintype.card_congr (orderingEquivPerm T), Fintype.card_perm, Fintype.card_fin]

/-- Exact conversion of an order-invariant sum over all ordered tuples into
one sum over compatible face sets, with the fixed factorial multiplicity. -/
theorem sum_orderedFaceTuples_eq_factorial {p q : ℕ} (faces : Finset (Face p))
    (g : CompatibleFaceSets faces q → ℝ) :
    (∑ S : OrderedFaceTuples faces q, g (tupleActiveSet S)) =
      (q.factorial : ℝ) * ∑ T : CompatibleFaceSets faces q, g T := by
  classical
  have he := (Equiv.sigmaFiberEquiv (tupleActiveSet (faces := faces) (q := q))).sum_comp
    (fun S : OrderedFaceTuples faces q => g (tupleActiveSet S))
  rw [Fintype.sum_sigma] at he
  have hf (T : CompatibleFaceSets faces q) :
      (∑ S : OrderingFiber T, g (tupleActiveSet S.val)) = (q.factorial : ℝ) * g T := by
    simp_rw [fun S : OrderingFiber T => S.property]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_orderingFiber]
  change (∑ T : CompatibleFaceSets faces q, ∑ S : OrderingFiber T, g (tupleActiveSet S.val)) =
    (∑ S : OrderedFaceTuples faces q, g (tupleActiveSet S)) at he
  simp_rw [hf] at he
  rw [← Finset.mul_sum] at he
  exact he.symm

/-- Pointwise domination by a face-set weight loses only the universal
factorial, independent of the dimension and number of rectangle faces. -/
theorem sum_orderedFaceTuples_le_factorial {p q : ℕ} (faces : Finset (Face p))
    (w : OrderedFaceTuples faces q → ℝ) (g : CompatibleFaceSets faces q → ℝ)
    (hw : ∀ S, w S ≤ g (tupleActiveSet S)) :
    (∑ S, w S) ≤ (q.factorial : ℝ) * ∑ T, g T := by
  exact (Finset.sum_le_sum (fun S _ => hw S)).trans_eq (sum_orderedFaceTuples_eq_factorial faces g)

@[simp] theorem tupleActiveSet_val {p q : ℕ} {faces : Finset (Face p)}
    (S : OrderedFaceTuples faces q) : (tupleActiveSet S).val = activeFaces S.val := rfl

/-- Replace an ordered tuple's determinant by the determinant of the
canonical representative of its actual face set. -/
theorem gram_det_eq_canonical {p q : ℕ} {faces : Finset (Face p)}
    (S : OrderedFaceTuples faces q) (Q : Matrix (Fin p) (Fin p) ℝ) :
    (S.val.gram Q).det = ((compatibleSetTuple (tupleActiveSet S)).gram Q).det := by
  apply gram_det_eq_of_activeFaces_eq
  simp only [activeFaces_compatibleSetTuple, tupleActiveSet_val]

end

end RectangleCLT.GaussianTube
