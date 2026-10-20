import RectangleCLT.GaussianThirdMajorant
import RectangleCLT.GaussianFaceIndexSums
import RectangleCLT.GaussianTubeFaceBounds

/-! Assembly of the actual third Gaussian derivatives by ordered active faces.
The finite indexing is exact; in particular, the number of coordinates never
appears as a multiplicative loss. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

open GaussianTube

variable {p : ℕ} (s : FaceSmoother p)

def faceFamilySet {q : ℕ} (f : Fin q → Face p) : Finset (Face p) :=
  Finset.univ.image f

@[simp] theorem faceFamilySet_singleton (f : Face p) : faceFamilySet ![f] = {f} := by
  classical
  ext g
  simp [faceFamilySet, Fin.exists_fin_succ, eq_comm]

@[simp] theorem faceFamilySet_pair (f g : Face p) : faceFamilySet ![f, g] = {f, g} := by
  classical
  ext a
  simp [faceFamilySet, Fin.exists_fin_succ, eq_comm]

@[simp] theorem faceFamilySet_triple (f g h : Face p) : faceFamilySet ![f, g, h] = {f, g, h} := by
  classical
  ext a
  simp [faceFamilySet, Fin.exists_fin_succ, eq_comm]

@[simp] theorem faceFamilySet_snoc {q : ℕ} (f : Fin q → Face p) (a : Face p) :
    faceFamilySet (Fin.snoc f a) = insert a (faceFamilySet f) := by
  classical
  ext b
  simp only [faceFamilySet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · exact Or.inr ⟨i, by simp⟩
    · exact Or.inl (by simp)
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last q, by simp⟩
    · exact ⟨i.castSucc, by simp⟩

def faceFamilyGram {q : ℕ} (f : Fin q → Face p) (Q : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i j => faceSign (f i) * faceSign (f j) * Q (f i).1 (f j).1

def gaussianFaceMomentSumAll (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) : ℝ :=
  ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
    (T.val.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.val.activeFaceSet k

theorem gaussianFaceMomentSumAll_extend (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (q k : ℕ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
      ∑ f ∈ inactiveCoordinateFaces T.val.activeFaceSet,
        (T.val.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.val.activeFaceSet) k) =
      s.gaussianFaceMomentSumAll A x (q + 1) k := by
  let g : (Fin (q + 1) → Face p) → ℝ := fun f =>
    (faceFamilyGram f (A * A.transpose)).det * s.gaussianSoftFaceMoment A x (faceFamilySet f) k
  have hi := sum_orderedFaceTuples_extend g
  dsimp only [g] at hi
  simp only [faceFamilySet_snoc] at hi
  exact hi

theorem gaussianFaceMomentSumAll_extend_twice (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (q k : ℕ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
      ∑ f ∈ inactiveCoordinateFaces T.val.activeFaceSet,
        ∑ g ∈ inactiveCoordinateFaces (insert f T.val.activeFaceSet),
          (T.val.appendTwoGram f g (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert g (insert f T.val.activeFaceSet)) k) =
      s.gaussianFaceMomentSumAll A x (q + 2) k := by
  let g : (Fin (q + 1) → Face p) → ℝ := fun f =>
    ∑ a ∈ inactiveCoordinateFaces (faceFamilySet f),
      (faceFamilyGram (Fin.snoc f a) (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x (insert a (faceFamilySet f)) k
  have hi := sum_orderedFaceTuples_extend g
  dsimp only [g] at hi
  simp only [faceFamilySet_snoc] at hi
  have hleft :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
        ∑ f ∈ inactiveCoordinateFaces T.val.activeFaceSet,
          ∑ a ∈ inactiveCoordinateFaces (insert f T.val.activeFaceSet),
            (T.val.appendTwoGram f a (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert a (insert f T.val.activeFaceSet)) k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) (q + 1), g T.val.face := by
    exact hi
  rw [hleft]
  exact s.gaussianFaceMomentSumAll_extend A x (q + 1) k

/-- Ordered determinant-weighted soft-face moments. For `q` active faces this
is exactly `q!` times the canonical compatible-face-set sum. The factorial
cancels the same one in the actual exponential tube integral. -/
def gaussianFaceMomentSum (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) : ℝ :=
  ∑ T : OrderedFaceTuples s.faces q,
    (T.val.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.val.activeFaceSet k

theorem gaussianFaceMomentSumAll_eq (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (q k : ℕ) :
    s.gaussianFaceMomentSumAll A x q k = s.gaussianFaceMomentSum A x q k := by
  unfold gaussianFaceMomentSumAll gaussianFaceMomentSum
  apply sum_orderedFaceTuples_univ_eq_restrict s.faces
    (fun T : CompatibleFaceTuple p q => (T.gram (A * A.transpose)).det *
      s.gaussianSoftFaceMoment A x T.activeFaceSet k)
  rintro T ⟨i, hi⟩
  have hmem : T.face i ∈ T.activeFaceSet :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [s.gaussianSoftFaceMoment_eq_zero_of_missing A x k hmem hi, mul_zero]

theorem sum_ordered_pair_derivatives_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
      (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
        (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) ≤
      (2 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 1 +
      (12 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 0 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceDirectional_pair_le_det_moments hp A T.val hQ ha hdiag hc hac 0 x)
        (show (0 : ℝ) ≤ 2 / s.bandwidth ^ 2 from
          div_nonneg (by norm_num) (sq_nonneg _)))
  apply hh.trans_eq
  rw [← s.gaussianFaceMomentSumAll_extend A x 2 0]
  change _ = (2 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 2) *
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (T.val.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.val.activeFaceSet 1) + _
  simp only [mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

private theorem singleton_gram_det (T : CompatibleFaceTuple p 1)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, Q j j = 1) :
    (T.gram Q).det = 1 := by
  rw [Matrix.det_fin_one, T.gram_diagonal hdiag 0]

theorem sum_ordered_singleton_second_derivatives_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
      (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
        (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) ≤
      (2 / (pairGap (A * A.transpose) * a) / s.bandwidth) *
        s.gaussianFaceMomentSumAll A x 1 2 +
      (4 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 1 +
      (12 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 0 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceCoordinateSecond_singleton_le_det_moments hp A T.val hQ ha hdiag hc hac 0 x)
        (div_nonneg zero_le_one s.bandwidth_pos.le))
  apply hh.trans_eq
  have hsingle : s.gaussianFaceMomentSumAll A x 1 2 =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        s.gaussianSoftFaceMoment A x T.val.activeFaceSet 2 := by
    unfold gaussianFaceMomentSumAll
    simp only [singleton_gram_det _ _ hdiag, one_mul]
  rw [hsingle, ← s.gaussianFaceMomentSumAll_extend A x 1 1,
    ← s.gaussianFaceMomentSumAll_extend_twice A x 1 0]
  simp only [mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

private theorem triple_gram_det_lower (T : CompatibleFaceTuple p 3)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    pairGap (A * A.transpose) * a ≤ (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hpair := T.initial.gram_two_det_ge_pairGap hsym hdiag hc.le
  have hpd : 0 < ((T.gram (A * A.transpose)).submatrix Fin.castSucc Fin.castSucc).det := by
    simpa only [← T.initial_gram (A * A.transpose)] using hc.trans_le hpair
  have hstep := det_succ_ge_mul_leading_det (T.gram (A * A.transpose)) ha.le
    (T.gram_symmetric hsym) hpd (T.gram_lower hQ)
  have hh := (mul_le_mul_of_nonneg_left hpair ha.le).trans hstep
  simpa only [mul_comm, CompatibleFaceTuple.initial_gram] using hh

theorem sum_ordered_triple_weights_le_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
      (6 / s.bandwidth ^ 3) *
        (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p)) ≤
      (6 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 0 := by
  classical
  have hpos : 0 < pairGap (A * A.transpose) * a := mul_pos hc ha
  unfold gaussianFaceMomentSumAll
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  have hdet := triple_gram_det_lower T.val A hQ ha hdiag hc
  have hcoef : 6 / s.bandwidth ^ 3 ≤
      (6 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 3) *
        (T.val.gram (A * A.transpose)).det := by
    have hh : 1 ≤ (T.val.gram (A * A.transpose)).det /
        (pairGap (A * A.transpose) * a) := (le_div_iff₀ hpos).mpr (by simpa using hdet)
    have hm := mul_le_mul_of_nonneg_left hh
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 6) (pow_nonneg s.bandwidth_pos.le 3))
    convert hm using 1 <;> ring
  simpa only [gaussianSoftFaceMoment_zero, mul_assoc] using
    mul_le_mul_of_nonneg_right hcoef
      (integral_nonneg (fun z => s.softFaceWeight_nonneg T.val.activeFaceSet (A.mulVec z + x)))

theorem sum_thirdSingleContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, s.thirdSingleContribution A x j) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 1 → Face p) → ℝ := fun f => (1 / s.bandwidth) *
    |∫ z, s.softFaceCoordinateSecond (faceFamilySet f) (f 0).1 (A.mulVec z + x)
      ∂standardGaussian p|
  have hi := sum_singleton_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [g, faceFamilySet_singleton, Matrix.cons_val_zero,
    thirdSingleContribution, ← Finset.mul_sum]

theorem sum_thirdPairContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, s.thirdPairContribution A x j k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 2 → Face p) → ℝ := fun f => (2 / s.bandwidth ^ 2) *
    |∫ z, s.softFaceDirectional (faceFamilySet f) (coordinateDirection (f 0).1)
      (A.mulVec z + x) ∂standardGaussian p|
  have hi := sum_pair_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j = k
  · simp only [thirdPairContribution, if_pos hjk, if_neg (not_not_intro hjk)]
  · simp only [thirdPairContribution, if_neg hjk, if_pos hjk,
      g, faceFamilySet_pair, Matrix.cons_val_zero, ← Finset.mul_sum]

theorem sum_thirdDistinctContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.thirdDistinctContribution A x j k l) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
  classical
  let g : (Fin 3 → Face p) → ℝ := fun f => (6 / s.bandwidth ^ 3) *
    (∫ z, s.softFaceWeight (faceFamilySet f) (A.mulVec z + x) ∂standardGaussian p)
  have hi := sum_triple_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hd : j ≠ k ∧ j ≠ l ∧ k ≠ l
  · simp only [thirdDistinctContribution, if_pos hd, g, faceFamilySet_triple,
      ← Finset.mul_sum]
  · simp only [thirdDistinctContribution, if_neg hd]

theorem sum_abs_convolutionThirdDerivative_le_ordered_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) +
      3 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) +
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
  simpa only [s.sum_thirdSingleContribution_eq_ordered,
    s.sum_thirdPairContribution_eq_ordered, s.sum_thirdDistinctContribution_eq_ordered]
      using s.sum_abs_convolutionThirdDerivative_le_soft_faces A x

/-- The full actual third-derivative tensor is bounded by three positive
determinant-weighted face moment sums. All local covariance losses have
already been paid, and no dimension-dependent factor is present. -/
theorem sum_abs_convolutionThirdDerivative_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      (2 / (pairGap (A * A.transpose) * a) / s.bandwidth) *
        s.gaussianFaceMomentSum A x 1 2 +
      (10 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSum A x 2 1 +
      (54 / (pairGap (A * A.transpose) * a) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSum A x 3 0 := by
  have h₁ := s.sum_ordered_singleton_second_derivatives_le_moments hp A x hQ ha hdiag hc hac
  have h₂ := s.sum_ordered_pair_derivatives_le_moments hp A x hQ ha hdiag hc hac
  have h₃ := s.sum_ordered_triple_weights_le_moments A x hQ ha hdiag hc
  have hh := add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 3))) h₃
  apply (s.sum_abs_convolutionThirdDerivative_le_ordered_soft_faces A x).trans
  apply hh.trans_eq
  simp only [s.gaussianFaceMomentSumAll_eq]
  ring

theorem faceMoment_eq_gaussianSoftFaceMoment {q : ℕ}
    (T : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (k : ℕ) :
    faceMoment T s A x k = (T.gram (A * A.transpose)).det / s.bandwidth ^ q *
      s.gaussianSoftFaceMoment A x T.activeFaceSet k := by
  unfold faceMoment gaussianSoftFaceMoment
  rw [normalMatrix_gram]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => mul_comm _ _)

theorem gaussianFaceMomentSum_div_eq_factorial (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (q k : ℕ) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q =
      (q.factorial : ℝ) * ∑ T : CompatibleFaceSets s.faces q,
        faceMoment (compatibleSetTuple T) s A x k := by
  classical
  rw [← sum_ordered_faceMoment_eq_factorial]
  unfold gaussianFaceMomentSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  rw [s.faceMoment_eq_gaussianSoftFaceMoment]
  ring

theorem gaussianFaceMomentSum_div_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {q k : ℕ}
    (hq0 : 0 < q) (hq : q ≤ 3) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q ≤
      (2 : ℝ) ^ k * (q : ℝ) ^ q * (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  rw [s.gaussianFaceMomentSum_div_eq_factorial]
  have hd (T : CompatibleFaceSets s.faces q) :
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det :=
    normalMatrix_gram_det_isUnit (compatibleSetTuple T) A (hQ.mono hq) ha
  have hh := sum_faceMoment_le s A x hp hq0 (hq.trans (by omega))
    (by norm_num : (0 : ℝ) < 1) hdiag hd k
  simpa only [Real.sqrt_one, one_pow, mul_one] using hh

/-- One explicit universal constant for the third Gaussian derivative
estimate. Its numerical value is immaterial; its finiteness and positivity
follow directly from the displayed exponential expression. -/
def gaussianThirdConstant : ℝ := 8 * Real.exp 80 + 80 * Real.exp 40 + 1458 * Real.exp 16

theorem gaussianThirdConstant_pos : 0 < gaussianThirdConstant := by
  unfold gaussianThirdConstant
  positivity

/-- Genuine Gaussian third-derivative estimate. It follows from the actual
Gaussian tube change of variables and local active Gram bounds; the full
Gaussian covariance may be singular. -/
theorem sum_abs_convolutionThirdDerivative_gaussian_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose)) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      gaussianThirdConstant * (Real.sqrt (dimensionLog p)) ^ 3 /
        (pairGap (A * A.transpose) * a) := by
  have h₁ := s.gaussianFaceMomentSum_div_le hp A x (q := 1) (k := 2)
    (by omega) (by omega) hQ ha hdiag
  have h₂ := s.gaussianFaceMomentSum_div_le hp A x (q := 2) (k := 1)
    (by omega) (by omega) hQ ha hdiag
  have h₃ := s.gaussianFaceMomentSum_div_le hp A x (q := 3) (k := 0)
    (by omega) (by omega) hQ ha hdiag
  norm_num only [Nat.cast_ofNat, pow_one, pow_zero, one_mul, mul_one, Nat.reduceAdd,
    Nat.cast_add, Nat.cast_one] at h₁ h₂ h₃
  have hc₁ : 0 ≤ 2 / (pairGap (A * A.transpose) * a) := by positivity
  have hc₂ : 0 ≤ 10 / (pairGap (A * A.transpose) * a) := by positivity
  have hc₃ : 0 ≤ 54 / (pairGap (A * A.transpose) * a) := by positivity
  have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ hc₁)
    (mul_le_mul_of_nonneg_left h₂ hc₂)) (mul_le_mul_of_nonneg_left h₃ hc₃)
  calc
    _ ≤ (2 / (pairGap (A * A.transpose) * a)) *
        (s.gaussianFaceMomentSum A x 1 2 / s.bandwidth ^ 1) +
      (10 / (pairGap (A * A.transpose) * a)) *
        (s.gaussianFaceMomentSum A x 2 1 / s.bandwidth ^ 2) +
      (54 / (pairGap (A * A.transpose) * a)) *
        (s.gaussianFaceMomentSum A x 3 0 / s.bandwidth ^ 3) := by
      convert s.sum_abs_convolutionThirdDerivative_le_det_moments hp A x hQ ha hdiag hc hac
        using 1
      ring
    _ ≤ 2 / (pairGap (A * A.transpose) * a) *
        (4 * (Real.sqrt (dimensionLog p)) ^ 3 * Real.exp 80) +
      10 / (pairGap (A * A.transpose) * a) *
        (8 * (Real.sqrt (dimensionLog p)) ^ 3 * Real.exp 40) +
      54 / (pairGap (A * A.transpose) * a) *
        (27 * (Real.sqrt (dimensionLog p)) ^ 3 * Real.exp 16) := by
      simpa only [pow_one] using hh
    _ = _ := by unfold gaussianThirdConstant; ring

end
end RectangleCLT.FaceSmoother
