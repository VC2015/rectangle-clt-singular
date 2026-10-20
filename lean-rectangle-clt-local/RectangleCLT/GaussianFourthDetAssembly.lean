import RectangleCLT.GaussianFourthAssembly
import RectangleCLT.GaussianFourthMajorant
import RectangleCLT.GaussianFourthTriple
import RectangleCLT.GaussianFourthHermite

/-! Determinant-weighted assembly of the five actual fourth derivative
patterns. All sums are over compatible ordered faces. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

/-- Positive singleton-face right-hand side, retained entrywise for shifts. -/
def fourthSingletonMomentCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (T : CompatibleFaceTuple p 1) : ℝ :=
  (4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
    s.gaussianSoftFaceMoment A x T.activeFaceSet 3 +
  (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
    ((6 / (pairGap (A * A.transpose) * a₃ * a₄)) *
      (T.appendGram f (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2 +
    (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
      ((6 / (pairGap (A * A.transpose) * a₃ * a₄)) *
        (T.appendTwoGram f g (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 1 +
      (4 / s.bandwidth) * ∑ h ∈ inactiveCoordinateFaces (insert g (insert f T.activeFaceSet)),
        (4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
          (T.appendThreeGram f g h (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert h (insert g (insert f T.activeFaceSet))) 0))

/-- Positive two-face right-hand side for both `3+1` and `2+2` patterns. -/
def fourthPairMomentCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (T : CompatibleFaceTuple p 2) : ℝ :=
  (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
    s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
  (3 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
    ((4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
      (T.appendGram f (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
    (4 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
      (4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
        (T.appendTwoGram f g (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0)

/-- Positive three-face right-hand side for the `2+1+1` pattern. -/
def fourthTripleMomentCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (T : CompatibleFaceTuple p 3) : ℝ :=
  (1 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
    s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
  (4 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
    (2 / (pairGap (A * A.transpose) * a₃ * a₄)) *
      (T.appendGram f (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0

/-- Positive four-face right-hand side for distinct coordinates. -/
def fourthQuadrupleMomentCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (T : CompatibleFaceTuple p 4) : ℝ :=
  (1 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
    s.gaussianSoftFaceMoment A x T.activeFaceSet 0

theorem sum_ordered_pair_second_derivatives_le_fourth_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i j : Fin 2) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
      (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceMixedSecond T.val.activeFaceSet
        (T.val.face i).1 (T.val.face j).1 (A.mulVec z + x) ∂standardGaussian p|) ≤
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 2 +
      (24 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (96 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceMixedSecond_pair_le_det_moments hp A T.val
          hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc i j x)
        (show (0 : ℝ) ≤ 2 / s.bandwidth ^ 2 from by positivity))
  apply hh.trans_eq
  rw [← s.gaussianFaceMomentSumAll_extend A x 2 1,
    ← s.gaussianFaceMomentSumAll_extend_twice A x 2 0]
  simp only [gaussianFaceMomentSumAll, mul_add, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem gaussianFaceMomentSumAll_extend_thrice
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
      ∑ f ∈ inactiveCoordinateFaces T.val.activeFaceSet,
        ∑ g ∈ inactiveCoordinateFaces (insert f T.val.activeFaceSet),
          ∑ h ∈ inactiveCoordinateFaces (insert g (insert f T.val.activeFaceSet)),
            (T.val.appendThreeGram f g h (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert h (insert g (insert f T.val.activeFaceSet))) k) =
      s.gaussianFaceMomentSumAll A x (q + 3) k := by
  let g : (Fin (q + 1) → Face p) → ℝ := fun f =>
    ∑ a ∈ inactiveCoordinateFaces (faceFamilySet f),
      ∑ b ∈ inactiveCoordinateFaces (insert a (faceFamilySet f)),
        (faceFamilyGram (Fin.snoc (Fin.snoc f a) b) (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert b (insert a (faceFamilySet f))) k
  have hi := sum_orderedFaceTuples_extend g
  dsimp only [g] at hi
  simp only [faceFamilySet_snoc] at hi
  have hleft :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
        ∑ f ∈ inactiveCoordinateFaces T.val.activeFaceSet,
          ∑ a ∈ inactiveCoordinateFaces (insert f T.val.activeFaceSet),
            ∑ b ∈ inactiveCoordinateFaces (insert a (insert f T.val.activeFaceSet)),
              (T.val.appendThreeGram f a b (A * A.transpose)).det *
                s.gaussianSoftFaceMoment A x (insert b (insert a (insert f T.val.activeFaceSet))) k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) (q + 1), g T.val.face := by
    exact hi
  rw [hleft]
  exact s.gaussianFaceMomentSumAll_extend_twice A x (q + 1) k

theorem gaussianFaceMomentSumAll_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) :
    0 ≤ s.gaussianFaceMomentSumAll A x q k := by
  unfold gaussianFaceMomentSumAll
  apply Finset.sum_nonneg
  intro T _
  apply mul_nonneg _ (s.gaussianSoftFaceMoment_nonneg A x _ k)
  simpa only [normalMatrix_gram] using normalMatrix_gram_det_nonneg T.val A

/-- The checked tube integral controls all local fourth-order face sizes;
only active principal Grams need be nondegenerate. -/
theorem gaussianFaceMomentSum_div_le_fourth (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {q k : ℕ}
    (hq0 : 0 < q) (hq : q ≤ 4) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q ≤
      (2 : ℝ) ^ k * (q : ℝ) ^ q * (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  rw [s.gaussianFaceMomentSum_div_eq_factorial]
  have hd (T : CompatibleFaceSets s.faces q) :
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det :=
    normalMatrix_gram_det_isUnit (compatibleSetTuple T) A (hQ.mono hq) ha
  have hh := sum_faceMoment_le s A x hp hq0 hq
    (by norm_num : (0 : ℝ) < 1) hdiag hd k
  simpa only [Real.sqrt_one, one_pow, mul_one] using hh

theorem sum_ordered_triple_first_derivatives_le_fourth_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
      (6 / s.bandwidth ^ 3) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
        (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) ≤
      (6 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (48 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceDirectional_triple_le_det_moments hp A T.val
          hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc 0 x)
        (show (0 : ℝ) ≤ 6 / s.bandwidth ^ 3 from
          div_nonneg (by norm_num) (pow_nonneg s.bandwidth_pos.le _)))
  apply hh.trans_eq
  rw [← s.gaussianFaceMomentSumAll_extend A x 3 0]
  simp only [gaussianFaceMomentSumAll, mul_add, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem sum_ordered_quadruple_weights_le_fourth_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
      (24 / s.bandwidth ^ 4) *
        (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p)) ≤
      (24 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  classical
  unfold gaussianFaceMomentSumAll
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  have hd := T.val.one_le_localFourthCost_mul_quadruple_det A hQ3 ha3 hQ4 ha4 hdiag hc
  have hh := mul_le_mul_of_nonneg_left hd
    (show (0 : ℝ) ≤ 24 / s.bandwidth ^ 4 from
      div_nonneg (by norm_num) (pow_nonneg s.bandwidth_pos.le _))
  have hc₁ : 24 / s.bandwidth ^ 4 ≤
      (24 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        (T.val.gram (A * A.transpose)).det := by
    convert hh using 1 <;> ring
  simpa only [gaussianSoftFaceMoment_zero, mul_assoc] using
    mul_le_mul_of_nonneg_right hc₁
      (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))

theorem sum_ordered_pairMomentCap_eq_fourth_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a₃ a₄ : ℝ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
      (2 / s.bandwidth ^ 2) * s.fourthPairMomentCap A a₃ a₄ x T.val) =
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 2 +
      (24 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (96 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  rw [← s.gaussianFaceMomentSumAll_extend A x 2 1,
    ← s.gaussianFaceMomentSumAll_extend_twice A x 2 0]
  simp only [fourthPairMomentCap, gaussianFaceMomentSumAll, mul_add,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

private theorem fourth_singleton_gram_det (T : CompatibleFaceTuple p 1)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, Q j j = 1) :
    (T.gram Q).det = 1 := by
  rw [Matrix.det_fin_one, T.gram_diagonal hdiag 0]

theorem sum_ordered_singletonMomentCap_eq_fourth_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a₃ a₄ : ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
      (1 / s.bandwidth) * s.fourthSingletonMomentCap A a₃ a₄ x T.val) =
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth) *
        s.gaussianFaceMomentSumAll A x 1 3 +
      (12 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 2 +
      (36 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (96 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  have hsingle : s.gaussianFaceMomentSumAll A x 1 3 =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        s.gaussianSoftFaceMoment A x T.val.activeFaceSet 3 := by
    unfold gaussianFaceMomentSumAll
    simp only [fourth_singleton_gram_det _ _ hdiag, one_mul]
  rw [hsingle, ← s.gaussianFaceMomentSumAll_extend A x 1 2,
    ← s.gaussianFaceMomentSumAll_extend_twice A x 1 1,
    ← s.gaussianFaceMomentSumAll_extend_thrice A x 1 0]
  simp only [fourthSingletonMomentCap, mul_add, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem sum_ordered_tripleMomentCap_eq_fourth_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a₃ a₄ : ℝ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
      (6 / s.bandwidth ^ 3) * s.fourthTripleMomentCap A a₃ a₄ x T.val) =
      (6 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (48 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  rw [← s.gaussianFaceMomentSumAll_extend A x 3 0]
  simp only [fourthTripleMomentCap, gaussianFaceMomentSumAll, mul_add,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem sum_ordered_quadrupleMomentCap_eq_fourth_moments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a₃ a₄ : ℝ) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
      (24 / s.bandwidth ^ 4) * s.fourthQuadrupleMomentCap A a₃ a₄ x T.val) =
      (24 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  simp only [fourthQuadrupleMomentCap, gaussianFaceMomentSumAll,
    mul_assoc, ← Finset.mul_sum]
  ring

/-- Summing the retained positive caps keeps the same fourth-order local
covariance cost, with explicit dimension-free pattern coefficients. -/
theorem sum_ordered_fourthMomentCaps_eq
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a₃ a₄ : ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
      (1 / s.bandwidth) * s.fourthSingletonMomentCap A a₃ a₄ x T.val) +
    4 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
      (2 / s.bandwidth ^ 2) * s.fourthPairMomentCap A a₃ a₄ x T.val) +
    3 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
      (2 / s.bandwidth ^ 2) * s.fourthPairMomentCap A a₃ a₄ x T.val) +
    6 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
      (6 / s.bandwidth ^ 3) * s.fourthTripleMomentCap A a₃ a₄ x T.val) +
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
      (24 / s.bandwidth ^ 4) * s.fourthQuadrupleMomentCap A a₃ a₄ x T.val) =
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth) *
        s.gaussianFaceMomentSumAll A x 1 3 +
      (40 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 2 +
      (240 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (1080 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  rw [s.sum_ordered_singletonMomentCap_eq_fourth_moments A x a₃ a₄ hdiag,
    s.sum_ordered_pairMomentCap_eq_fourth_moments,
    s.sum_ordered_tripleMomentCap_eq_fourth_moments,
    s.sum_ordered_quadrupleMomentCap_eq_fourth_moments]
  ring

theorem abs_softFaceCoordinateThird_le_fourthSingletonMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (T : CompatibleFaceTuple p 1) (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceCoordinateThird T.activeFaceSet (T.face i).1
      (A.mulVec z + x) ∂standardGaussian p| ≤ s.fourthSingletonMomentCap A a₃ a₄ x T :=
  s.abs_softFaceCoordinateThird_singleton_le_det_moments hp A T
    hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc i x

theorem abs_softFaceMixedSecond_le_fourthPairMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (T : CompatibleFaceTuple p 2) (i j : Fin 2) (x : Vector p) :
    |∫ z, s.softFaceMixedSecond T.activeFaceSet (T.face i).1 (T.face j).1
      (A.mulVec z + x) ∂standardGaussian p| ≤ s.fourthPairMomentCap A a₃ a₄ x T :=
  s.abs_softFaceMixedSecond_pair_le_det_moments hp A T
    hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc i j x

theorem abs_softFaceCoordinateSecond_le_fourthPairMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (T : CompatibleFaceTuple p 2) (i : Fin 2) (x : Vector p) :
    |∫ z, s.softFaceCoordinateSecond T.activeFaceSet (T.face i).1
      (A.mulVec z + x) ∂standardGaussian p| ≤ s.fourthPairMomentCap A a₃ a₄ x T := by
  simpa only [softFaceMixedSecond_diagonal] using
    s.abs_softFaceMixedSecond_le_fourthPairMomentCap hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T i i x

theorem abs_softFaceDirectional_le_fourthTripleMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (T : CompatibleFaceTuple p 3) (i : Fin 3) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face i).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤ s.fourthTripleMomentCap A a₃ a₄ x T :=
  s.abs_softFaceDirectional_triple_le_det_moments hp A T
    hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc i x

theorem integral_softFaceWeight_le_fourthQuadrupleMomentCap
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceTuple p 4) (x : Vector p) :
    (∫ z, s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      s.fourthQuadrupleMomentCap A a₃ a₄ x T := by
  have hd := T.one_le_localFourthCost_mul_quadruple_det A hQ3 ha3 hQ4 ha4 hdiag hc
  simpa only [fourthQuadrupleMomentCap, gaussianSoftFaceMoment_zero, one_mul] using
    mul_le_mul_of_nonneg_right hd
      (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))

theorem sum_ordered_singleton_third_derivatives_le_fourth_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (x : Vector p) :
    (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
      (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateThird T.val.activeFaceSet
        (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) ≤
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth) *
        s.gaussianFaceMomentSumAll A x 1 3 +
      (12 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSumAll A x 2 2 +
      (36 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSumAll A x 3 1 +
      (96 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSumAll A x 4 0 := by
  rw [← s.sum_ordered_singletonMomentCap_eq_fourth_moments A x a₃ a₄ hdiag]
  apply Finset.sum_le_sum
  intro T _
  exact mul_le_mul_of_nonneg_left
    (s.abs_softFaceCoordinateThird_le_fourthSingletonMomentCap hp A
      hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T.val 0 x)
    (div_nonneg zero_le_one s.bandwidth_pos.le)

/-- The full actual fourth Gaussian derivative tensor has a positive
four-face moment majorant with the exact local cost `c*a3*a4`. -/
theorem sum_abs_convolutionFourthDerivative_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, |s.convolutionFourthDerivative (gaussianLaw A) x j k l m|) ≤
      (4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth) *
        s.gaussianFaceMomentSum A x 1 3 +
      (40 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
        s.gaussianFaceMomentSum A x 2 2 +
      (240 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
        s.gaussianFaceMomentSum A x 3 1 +
      (1080 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
        s.gaussianFaceMomentSum A x 4 0 := by
  have h₁ := s.sum_ordered_singleton_third_derivatives_le_fourth_moments
    hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc x
  have h₂ := s.sum_ordered_pair_second_derivatives_le_fourth_moments
    hp A x hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc 0 0
  simp only [softFaceMixedSecond_diagonal] at h₂
  have h₃ := s.sum_ordered_pair_second_derivatives_le_fourth_moments
    hp A x hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc 0 1
  have h₄ := s.sum_ordered_triple_first_derivatives_le_fourth_moments
    hp A x hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc
  have h₅ := s.sum_ordered_quadruple_weights_le_fourth_moments A x hQ3 ha3 hQ4 ha4 hdiag hc
  have hh := add_le_add (add_le_add (add_le_add
    (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 4)))
    (mul_le_mul_of_nonneg_left h₃ (by norm_num : (0 : ℝ) ≤ 3)))
    (mul_le_mul_of_nonneg_left h₄ (by norm_num : (0 : ℝ) ≤ 6))) h₅
  apply (s.sum_abs_convolutionFourthDerivative_le_ordered_soft_faces A x).trans
  apply hh.trans_eq
  simp only [s.gaussianFaceMomentSumAll_eq]
  ring

end
end RectangleCLT.FaceSmoother
