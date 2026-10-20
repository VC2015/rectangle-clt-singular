import RectangleCLTCompanion.SignedSurfaceKernel
import RectangleCLT.GaussianFaceIndexSums
import RectangleCLT.GaussianTubeFaceBounds
import RectangleCLTCompanion.SignedSurfacePairTube

/-! Exact finite reindexing of signed paired ridge kernels. Same-coordinate
zeros and symmetry are used before any estimate, so the canonical pair sum
has exactly the factor `2!`. -/

open RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {p : ℕ}

/-- Deleting the identically zero same-coordinate terms produces exactly
the ordered compatible-pair index, with no numerical loss. -/
theorem sum_face_pairs_eq_ordered (w : Face p → Face p → ℝ)
    (hz : ∀ f k, f.1 = k.1 → w f k = 0) :
    (∑ f : Face p, ∑ k : Face p, w f k) =
      ∑ S : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        w (S.val.face 0) (S.val.face 1) := by
  classical
  have hi := sum_pair_coordinate_signs (fun f : Fin 2 → Face p => w (f 0) (f 1))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hi
  calc
    _ = ∑ j : Fin p, ∑ b : Bool, ∑ k : Fin p, ∑ c : Bool, w (j, b) (k, c) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ j : Fin p, ∑ k : Fin p, ∑ b : Bool, ∑ c : Bool, w (j, b) (k, c) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin p, ∑ k : Fin p, if j ≠ k then
        ∑ b : Bool, ∑ c : Bool, w (j, b) (k, c) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hjk : j = k
      · subst k
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro b _
        apply Finset.sum_eq_zero
        intro c _
        exact hz (j, b) (j, c) rfl
      · simp only [hjk, ne_eq, not_false_eq_true, ↓reduceIte]
    _ = _ := hi

private theorem pair_faces_ne (S : CompatibleFaceTuple p 2) : S.face 0 ≠ S.face 1 := by
  intro h
  have hh := S.coordinate_injective (congrArg Prod.fst h)
  exact (by decide : (0 : Fin 2) ≠ 1) hh

/-- A symmetric pair weight depends only on the actual two-face set. -/
theorem symmetric_pair_weight_eq_of_activeFaces_eq
    (w : Face p → Face p → ℝ) (hs : ∀ f k, w f k = w k f)
    (S T : CompatibleFaceTuple p 2) (hset : activeFaces S = activeFaces T) :
    w (S.face 0) (S.face 1) = w (T.face 0) (T.face 1) := by
  classical
  have hm0 : S.face 0 ∈ activeFaces T := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hm1 : S.face 1 ∈ activeFaces T := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm0
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm1
  fin_cases i <;> fin_cases j
  · exact (pair_faces_ne S (hi.symm.trans hj)).elim
  · rw [← hi, ← hj]
    rfl
  · rw [← hi, ← hj, hs]
    rfl
  · exact (pair_faces_ne S (hi.symm.trans hj)).elim

/-- Exact `2!` multiplicity of the two possible orders of an actual
compatible two-face set. -/
theorem sum_symmetric_ordered_pairs_eq_two_canonical (faces : Finset (Face p))
    (w : Face p → Face p → ℝ) (hs : ∀ f k, w f k = w k f) :
    (∑ S : OrderedFaceTuples faces 2, w (S.val.face 0) (S.val.face 1)) =
      2 * ∑ T : CompatibleFaceSets faces 2,
        w ((compatibleSetTuple T).face 0) ((compatibleSetTuple T).face 1) := by
  classical
  let g := fun T : CompatibleFaceSets faces 2 =>
    w ((compatibleSetTuple T).face 0) ((compatibleSetTuple T).face 1)
  calc
    _ = ∑ S : OrderedFaceTuples faces 2, g (tupleActiveSet S) := by
      apply Finset.sum_congr rfl
      intro S _
      apply symmetric_pair_weight_eq_of_activeFaces_eq w hs S.val
        (compatibleSetTuple (tupleActiveSet S))
      simp only [activeFaces_compatibleSetTuple, tupleActiveSet_val]
    _ = _ := by
      have hh := sum_orderedFaceTuples_eq_factorial faces g
      norm_num at hh
      exact hh

/-- Zero weights on missing faces restrict the compatible pair sum to the
actual rectangle before it is converted to canonical face sets. -/
theorem sum_face_pairs_eq_ordered_restrict (faces : Finset (Face p))
    (w : Face p → Face p → ℝ)
    (hz : ∀ f k, f.1 = k.1 → w f k = 0)
    (hm : ∀ f k, f ∉ faces ∨ k ∉ faces → w f k = 0) :
    (∑ f : Face p, ∑ k : Face p, w f k) =
      ∑ S : OrderedFaceTuples faces 2, w (S.val.face 0) (S.val.face 1) := by
  rw [sum_face_pairs_eq_ordered w hz]
  apply sum_orderedFaceTuples_univ_eq_restrict faces
    (fun S : CompatibleFaceTuple p 2 => w (S.face 0) (S.face 1))
  intro S hmissing
  obtain ⟨i, hi⟩ := hmissing
  fin_cases i
  · exact hm _ _ (Or.inl hi)
  · exact hm _ _ (Or.inr hi)

theorem sum_face_pairs_eq_two_canonical (faces : Finset (Face p))
    (w : Face p → Face p → ℝ)
    (hz : ∀ f k, f.1 = k.1 → w f k = 0)
    (hm : ∀ f k, f ∉ faces ∨ k ∉ faces → w f k = 0)
    (hs : ∀ f k, w f k = w k f) :
    (∑ f : Face p, ∑ k : Face p, w f k) =
      2 * ∑ T : CompatibleFaceSets faces 2,
        w ((compatibleSetTuple T).face 0) ((compatibleSetTuple T).face 1) := by
  rw [sum_face_pairs_eq_ordered_restrict faces w hz hm,
    sum_symmetric_ordered_pairs_eq_two_canonical faces w hs]

/-- A nonnegative finite determinant index may be restricted to its strictly
positive part when the weight vanishes at determinant zero. -/
theorem sum_eq_sum_positive_subtype {ι : Type*} [Fintype ι]
    (d w : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (hz : ∀ i, d i = 0 → w i = 0) :
    (∑ i, w i) = ∑ i : {i : ι // 0 < d i}, w i.val := by
  classical
  calc
    _ = ∑ i, if 0 < d i then w i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 < d i
      · rw [if_pos hi]
      · have hdi : d i = 0 := le_antisymm (le_of_not_gt hi) (hd i)
        rw [if_neg hi, hz i hdi]
    _ = _ := by
      have hh := Finset.sum_subtype
        (F := (inferInstance : Fintype {i : ι // 0 < d i}))
        (Finset.univ.filter (fun i : ι => 0 < d i)) (by simp) w
      rw [Finset.sum_filter] at hh
      exact hh

/-- Canonical actual two-face sets whose Gaussian normals span a plane.
Singular covariance matrices are allowed; zero-determinant pairs are omitted. -/
def NondegenerateFacePairs (faces : Finset (Face p))
    (A : Matrix (Fin p) (Fin p) ℝ) :=
  {T : CompatibleFaceSets faces 2 // 0 < ((compatibleSetTuple T).gram (A * A.transpose)).det}

instance (faces : Finset (Face p)) (A : Matrix (Fin p) (Fin p) ℝ) :
    Fintype (NondegenerateFacePairs faces A) := by
  unfold NondegenerateFacePairs
  infer_instance

namespace NondegenerateFacePairs

def tuple {faces : Finset (Face p)} {A : Matrix (Fin p) (Fin p) ℝ}
    (T : NondegenerateFacePairs faces A) : CompatibleFaceTuple p 2 := compatibleSetTuple T.val

theorem tuple_det_pos {faces : Finset (Face p)} {A : Matrix (Fin p) (Fin p) ℝ}
    (T : NondegenerateFacePairs faces A) : 0 < (T.tuple.gram (A * A.transpose)).det := T.property

end NondegenerateFacePairs

theorem canonicalPair_gram_det_nonneg {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces 2) (A : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ((compatibleSetTuple T).gram (A * A.transpose)).det := by
  simpa only [normalMatrix_gram] using normalMatrix_gram_det_nonneg (compatibleSetTuple T) A

/-- Exact removal of degenerate canonical pairs for any weight whose
actual numerator vanishes at determinant zero. -/
theorem sum_canonical_pairs_eq_nondegenerate (faces : Finset (Face p))
    (A : Matrix (Fin p) (Fin p) ℝ) (w : CompatibleFaceSets faces 2 → ℝ)
    (hz : ∀ T, ((compatibleSetTuple T).gram (A * A.transpose)).det = 0 → w T = 0) :
    (∑ T : CompatibleFaceSets faces 2, w T) =
      ∑ T : NondegenerateFacePairs faces A, w T.val := by
  exact sum_eq_sum_positive_subtype
    (fun T : CompatibleFaceSets faces 2 => ((compatibleSetTuple T).gram (A * A.transpose)).det)
    w (fun T => canonicalPair_gram_det_nonneg T A) hz

/-- Exact canonical restriction for a symmetric paired weight, with the
strictly positive determinant carried by the actual index subtype. -/
theorem sum_face_pairs_eq_two_nondegenerate (faces : Finset (Face p))
    (A : Matrix (Fin p) (Fin p) ℝ) (w : Face p → Face p → ℝ)
    (hz : ∀ f k, f.1 = k.1 → w f k = 0)
    (hm : ∀ f k, f ∉ faces ∨ k ∉ faces → w f k = 0)
    (hs : ∀ f k, w f k = w k f)
    (hd : ∀ T : CompatibleFaceSets faces 2,
      ((compatibleSetTuple T).gram (A * A.transpose)).det = 0 →
        w ((compatibleSetTuple T).face 0) ((compatibleSetTuple T).face 1) = 0) :
    (∑ f : Face p, ∑ k : Face p, w f k) =
      2 * ∑ T : NondegenerateFacePairs faces A, w (T.tuple.face 0) (T.tuple.face 1) := by
  rw [sum_face_pairs_eq_two_canonical faces w hz hm hs,
    sum_canonical_pairs_eq_nondegenerate faces A
      (fun T => w ((compatibleSetTuple T).face 0) ((compatibleSetTuple T).face 1)) hd]
  rfl

/-- The actual signed paired ridge kernel, retaining the sum of the two
normal coordinates inside one coefficient. -/
def pairedRidgeKernel (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (y z : Vector p) (f k : Face p) : ℝ :=
  softFacePower s a f y * (s.weights y).pi k *
    ((1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
      (faceDot (signedRowNormal A f) z + faceDot (signedRowNormal A k) z))

theorem pairedRidgeKernel_symm (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (y z : Vector p) (f k : Face p) :
    pairedRidgeKernel s a A y z f k = pairedRidgeKernel s a A y z k f := by
  unfold pairedRidgeKernel
  rw [softFacePower_pair_kernel_symm s a f k y,
    faceDot_comm (signedRowNormal A f) (signedRowNormal A k)]
  ring

theorem softFacePower_eq_zero_of_missing (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (y : Vector p) (hf : f ∉ s.faces) : softFacePower s a f y = 0 := by
  simp only [softFacePower, FaceSmoother.softFaceWeight, Finset.prod_singleton,
    FaceWeights.pi, FaceSmoother.weights, hf, ↓reduceIte, zero_div, mul_zero]

theorem pairedRidgeKernel_eq_zero_of_missing (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (y z : Vector p) (f k : Face p)
    (hm : f ∉ s.faces ∨ k ∉ s.faces) : pairedRidgeKernel s a A y z f k = 0 := by
  rcases hm with hf | hk
  · rw [pairedRidgeKernel, softFacePower_eq_zero_of_missing s a f y hf, zero_mul, zero_mul]
  · have hpi : (s.weights y).pi k = 0 := by
      simp only [FaceWeights.pi, FaceSmoother.weights, hk, ↓reduceIte, zero_div]
    rw [pairedRidgeKernel, hpi, mul_zero, zero_mul]

/-- Both signs of the same coordinate contribute zero to the actual paired
numerator, including the diagonal term. -/
theorem pairedRidgeKernel_eq_zero_same_coordinate (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (y z : Vector p) (f k : Face p) (hc : f.1 = k.1) :
    pairedRidgeKernel s a A y z f k = 0 := by
  rcases f with ⟨j, b⟩
  rcases k with ⟨l, c⟩
  dsimp only at hc
  subst l
  unfold pairedRidgeKernel
  rw [signedRowNormal_gram, hdiag]
  cases b <;> cases c <;>
    simp [faceSign, signedRowNormal, faceDot, Finset.sum_neg_distrib]

theorem pairedRidgeKernel_eq_pairRidgeNumerator (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (y z : Vector p) (S : CompatibleFaceTuple p 2) :
    pairedRidgeKernel s a A y z (S.face 0) (S.face 1) =
      softFacePower s a (S.face 0) y * (s.weights y).pi (S.face 1) * pairRidgeNumerator S A z := rfl

/-- Exact actual signed sum over nondegenerate canonical pairs. The factor
`2` is solely the two possible orders of one pair. -/
theorem sum_pairedRidgeKernel_eq_two_nondegenerate (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (y z : Vector p) :
    (∑ f : Face p, ∑ k : Face p, pairedRidgeKernel s a A y z f k) =
      2 * ∑ T : NondegenerateFacePairs s.faces A,
        softFacePower s a (T.tuple.face 0) y * (s.weights y).pi (T.tuple.face 1) *
          pairRidgeNumerator T.tuple A z := by
  have hd (T : CompatibleFaceSets s.faces 2)
      (hdet : ((compatibleSetTuple T).gram (A * A.transpose)).det = 0) :
      pairedRidgeKernel s a A y z ((compatibleSetTuple T).face 0)
        ((compatibleSetTuple T).face 1) = 0 := by
    rw [pairedRidgeKernel_eq_pairRidgeNumerator,
      pairRidgeNumerator_zero_of_det_zero (compatibleSetTuple T) A hdiag hdet z, mul_zero]
  rw [sum_face_pairs_eq_two_nondegenerate s.faces A (pairedRidgeKernel s a A y z)
    (pairedRidgeKernel_eq_zero_same_coordinate s a A hdiag y z)
    (pairedRidgeKernel_eq_zero_of_missing s a A y z)
    (pairedRidgeKernel_symm s a A y z) hd]
  rfl

/-- The corresponding positive sum, with cancellation already incorporated
in `pairRidgeNumerator`, for the Gaussian tube estimate. -/
theorem sum_abs_pairedRidgeKernel_eq_two_nondegenerate (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (y z : Vector p) :
    (∑ f : Face p, ∑ k : Face p, |pairedRidgeKernel s a A y z f k|) =
      2 * ∑ T : NondegenerateFacePairs s.faces A,
        softFacePower s a (T.tuple.face 0) y * (s.weights y).pi (T.tuple.face 1) *
          |pairRidgeNumerator T.tuple A z| := by
  have hz (f k : Face p) (hc : f.1 = k.1) : |pairedRidgeKernel s a A y z f k| = 0 := by
    rw [pairedRidgeKernel_eq_zero_same_coordinate s a A hdiag y z f k hc, abs_zero]
  have hm (f k : Face p) (hmissing : f ∉ s.faces ∨ k ∉ s.faces) :
      |pairedRidgeKernel s a A y z f k| = 0 := by
    rw [pairedRidgeKernel_eq_zero_of_missing s a A y z f k hmissing, abs_zero]
  have hs (f k : Face p) : |pairedRidgeKernel s a A y z f k| =
      |pairedRidgeKernel s a A y z k f| := congrArg abs (pairedRidgeKernel_symm s a A y z f k)
  have hd (T : CompatibleFaceSets s.faces 2)
      (hdet : ((compatibleSetTuple T).gram (A * A.transpose)).det = 0) :
      |pairedRidgeKernel s a A y z ((compatibleSetTuple T).face 0)
        ((compatibleSetTuple T).face 1)| = 0 := by
    rw [pairedRidgeKernel_eq_pairRidgeNumerator,
      pairRidgeNumerator_zero_of_det_zero (compatibleSetTuple T) A hdiag hdet z, mul_zero, abs_zero]
  rw [sum_face_pairs_eq_two_nondegenerate s.faces A
    (fun f k => |pairedRidgeKernel s a A y z f k|) hz hm hs hd]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [pairedRidgeKernel_eq_pairRidgeNumerator, abs_mul,
    abs_of_nonneg (mul_nonneg (softFacePower_nonneg _ _ _ _) ((s.weights _).pi_nonneg _))]

end
end RectangleCLT.Companion.SignedSurface
