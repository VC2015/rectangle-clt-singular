import RectangleCLT.GaussianFourthShiftedCaps
import RectangleCLT.GaussianFourthSupCounting
import RectangleCLT.GaussianFourthCapEnumeration
import RectangleCLT.GaussianFourthMomentIntegral

/-! Positive entrywise bounds for the separate local suprema of actual fourth
Gaussian derivatives. The order of supremum, finite sums, and expectation is
preserved; shifts are controlled on each positive active-face moment. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

def fourthSingletonCoordinateCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (j : Fin p) : ℝ :=
  (1 / s.bandwidth) * ∑ b : Bool,
    compatibleTupleCap (s.fourthSingletonMomentCap A a₃ a₄ x) ![(j, b)]

def fourthPairCoordinateCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (j k : Fin p) : ℝ :=
  if j ≠ k then (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
    compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) ![(j, b), (k, c)]
  else 0

def fourthTripleCoordinateCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (j k l : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ k ≠ l then (6 / s.bandwidth ^ 3) *
    ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      compatibleTupleCap (s.fourthTripleMomentCap A a₃ a₄ x) ![(j, b), (k, c), (l, d)]
  else 0

def fourthQuadrupleCoordinateCap (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ)
    (x : Vector p) (j k l m : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m then
    (24 / s.bandwidth ^ 4) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
      compatibleTupleCap (s.fourthQuadrupleMomentCap A a₃ a₄ x)
        ![(j, b), (k, c), (l, d), (m, e)]
  else 0

theorem sum_fourthSingletonCoordinateCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ) (x : Vector p) :
    (∑ j, s.fourthSingletonCoordinateCap A a₃ a₄ x j) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * s.fourthSingletonMomentCap A a₃ a₄ x T.val := by
  classical
  let g : (Fin 1 → Face p) → ℝ := fun f => (1 / s.bandwidth) *
    compatibleTupleCap (s.fourthSingletonMomentCap A a₃ a₄ x) f
  have hi := sum_singleton_coordinate_signs g
  have hright :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1, g T.val.face) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * s.fourthSingletonMomentCap A a₃ a₄ x T.val := by
    apply Finset.sum_congr rfl
    intro T _
    simp only [g, compatibleTupleCap_face]
  rw [hright] at hi
  apply Eq.trans _ hi
  apply Finset.sum_congr rfl
  intro j _
  simp only [fourthSingletonCoordinateCap, g, ← Finset.mul_sum]

theorem sum_fourthPairCoordinateCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ) (x : Vector p) :
    (∑ j, ∑ k, s.fourthPairCoordinateCap A a₃ a₄ x j k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * s.fourthPairMomentCap A a₃ a₄ x T.val := by
  classical
  let g : (Fin 2 → Face p) → ℝ := fun f => (2 / s.bandwidth ^ 2) *
    compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) f
  have hi := sum_pair_coordinate_signs g
  have hright :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2, g T.val.face) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * s.fourthPairMomentCap A a₃ a₄ x T.val := by
    apply Finset.sum_congr rfl
    intro T _
    simp only [g, compatibleTupleCap_face]
  rw [hright] at hi
  apply Eq.trans _ hi
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hd : j ≠ k
  · simp only [fourthPairCoordinateCap, if_pos hd, g, ← Finset.mul_sum]
  · simp only [fourthPairCoordinateCap, if_neg hd]

theorem sum_fourthTripleCoordinateCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.fourthTripleCoordinateCap A a₃ a₄ x j k l) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) * s.fourthTripleMomentCap A a₃ a₄ x T.val := by
  classical
  let g : (Fin 3 → Face p) → ℝ := fun f => (6 / s.bandwidth ^ 3) *
    compatibleTupleCap (s.fourthTripleMomentCap A a₃ a₄ x) f
  have hi := sum_triple_coordinate_signs g
  have hright :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3, g T.val.face) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) * s.fourthTripleMomentCap A a₃ a₄ x T.val := by
    apply Finset.sum_congr rfl
    intro T _
    simp only [g, compatibleTupleCap_face]
  rw [hright] at hi
  apply Eq.trans _ hi
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hd : j ≠ k ∧ j ≠ l ∧ k ≠ l
  · simp only [fourthTripleCoordinateCap, if_pos hd, g, ← Finset.mul_sum]
  · simp only [fourthTripleCoordinateCap, if_neg hd]

theorem sum_fourthQuadrupleCoordinateCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (a₃ a₄ : ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fourthQuadrupleCoordinateCap A a₃ a₄ x j k l m) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
        (24 / s.bandwidth ^ 4) * s.fourthQuadrupleMomentCap A a₃ a₄ x T.val := by
  classical
  let g : (Fin 4 → Face p) → ℝ := fun f => (24 / s.bandwidth ^ 4) *
    compatibleTupleCap (s.fourthQuadrupleMomentCap A a₃ a₄ x) f
  have hi := sum_quadruple_coordinate_signs g
  have hright :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4, g T.val.face) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
        (24 / s.bandwidth ^ 4) * s.fourthQuadrupleMomentCap A a₃ a₄ x T.val := by
    apply Finset.sum_congr rfl
    intro T _
    simp only [g, compatibleTupleCap_face]
  rw [hright] at hi
  apply Eq.trans _ hi
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hd : j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m
  · simp only [fourthQuadrupleCoordinateCap, if_pos hd, g, ← Finset.mul_sum]
  · simp only [fourthQuadrupleCoordinateCap, if_neg hd]

theorem fourthSingletonCoordinateCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (j : Fin p) :
    0 ≤ s.fourthSingletonCoordinateCap A a₃ a₄ x j := by
  have hb := s.bandwidth_pos
  unfold fourthSingletonCoordinateCap
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro _ _
  exact compatibleTupleCap_nonneg _
    (fun T => s.fourthSingletonMomentCap_nonneg A ha3 ha4 hc x T) _

theorem fourthPairCoordinateCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (j k : Fin p) :
    0 ≤ s.fourthPairCoordinateCap A a₃ a₄ x j k := by
  have hb := s.bandwidth_pos
  unfold fourthPairCoordinateCap
  split_ifs
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    exact compatibleTupleCap_nonneg _
      (fun T => s.fourthPairMomentCap_nonneg A ha3 ha4 hc x T) _
  · exact le_rfl

theorem fourthTripleCoordinateCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (j k l : Fin p) :
    0 ≤ s.fourthTripleCoordinateCap A a₃ a₄ x j k l := by
  have hb := s.bandwidth_pos
  unfold fourthTripleCoordinateCap
  split_ifs
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    exact compatibleTupleCap_nonneg _
      (fun T => s.fourthTripleMomentCap_nonneg A ha3 ha4 hc x T) _
  · exact le_rfl

theorem fourthQuadrupleCoordinateCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (j k l m : Fin p) :
    0 ≤ s.fourthQuadrupleCoordinateCap A a₃ a₄ x j k l m := by
  have hb := s.bandwidth_pos
  unfold fourthQuadrupleCoordinateCap
  split_ifs
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    exact compatibleTupleCap_nonneg _
      (fun T => s.fourthQuadrupleMomentCap_nonneg A ha3 ha4 hc x T) _
  · exact le_rfl

theorem abs_convolutionFourthDerivative_diagonal_le_shiftedMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr : r ≤ s.bandwidth) (x u : Vector p) (hu : ‖u‖ ≤ r)
    (j : Fin p)  :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j j j| ≤
      Real.exp 9 * s.fourthSingletonCoordinateCap A a₃ a₄ x j := by
  have hb := s.bandwidth_pos
  have hentry (b : Bool) :
      |∫ z, s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + (x + u)) ∂standardGaussian p| ≤ Real.exp 9 *
        compatibleTupleCap (s.fourthSingletonMomentCap A a₃ a₄ x) ![(j, b)] := by
    have hf : Function.Injective (fun i : Fin 1 => (![(j, b)] i : Face p).1) :=
      (injective_singleton_coordinates j b).mpr trivial
    let T : CompatibleFaceTuple p 1 := ⟨![(j, b)], hf⟩
    have hset : T.activeFaceSet = {(j, b)} := by
      change faceFamilySet ![(j, b)] = _
      exact faceFamilySet_singleton _
    have ha := s.abs_softFaceCoordinateThird_le_fourthSingletonMomentCap hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T 0 (x + u)
    have hs := s.fourthSingletonMomentCap_shift_le_exp_nine hp A ha3 ha4 hc x T hu hr
    rw [compatibleTupleCap_of_injective _ _ hf]
    simpa only [hset, T, Matrix.cons_val_zero, Matrix.cons_val_one] using ha.trans hs
  have hbase := s.abs_convolutionFourthDerivative_diagonal_soft_faces A (x + u) j
  simp only [Fintype.sum_prod_type] at hbase
  apply hbase.trans
  calc
    _ ≤ (1 / s.bandwidth) * ∑ b : Bool, Real.exp 9 *
        compatibleTupleCap (s.fourthSingletonMomentCap A a₃ a₄ x) ![(j, b)] := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b _
      exact hentry b
    _ = _ := by
      simp only [fourthSingletonCoordinateCap, ← Finset.mul_sum]
      ring

theorem abs_convolutionFourthDerivative_triple_le_shiftedMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr : r ≤ s.bandwidth) (x u : Vector p) (hu : ‖u‖ ≤ r)
    {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j j k| ≤
      Real.exp 9 * s.fourthPairCoordinateCap A a₃ a₄ x j k := by
  have hb := s.bandwidth_pos
  have hentry (b c : Bool) :
      |∫ z, s.softFaceCoordinateSecond {(j, b), (k, c)} j (A.mulVec z + (x + u)) ∂standardGaussian p| ≤ Real.exp 9 *
        compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) ![(j, b), (k, c)] := by
    have hf : Function.Injective (fun i : Fin 2 => (![(j, b), (k, c)] i : Face p).1) :=
      (injective_pair_coordinates j k b c).mpr hjk
    let T : CompatibleFaceTuple p 2 := ⟨![(j, b), (k, c)], hf⟩
    have hset : T.activeFaceSet = {(j, b), (k, c)} := by
      change faceFamilySet ![(j, b), (k, c)] = _
      exact faceFamilySet_pair _ _
    have ha := s.abs_softFaceCoordinateSecond_le_fourthPairMomentCap hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T 0 (x + u)
    have hs := s.fourthPairMomentCap_shift_le_exp_nine hp A ha3 ha4 hc x T hu hr
    rw [compatibleTupleCap_of_injective _ _ hf]
    simpa only [hset, T, Matrix.cons_val_zero, Matrix.cons_val_one] using ha.trans hs
  have hbase := s.abs_convolutionFourthDerivative_triple_soft_faces A (x + u) hjk
  simp only [Fintype.sum_prod_type] at hbase
  apply hbase.trans
  calc
    _ ≤ (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool, Real.exp 9 *
        compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) ![(j, b), (k, c)] := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      exact hentry b c
    _ = _ := by
      simp only [fourthPairCoordinateCap, if_pos hjk, ← Finset.mul_sum]
      ring

theorem abs_convolutionFourthDerivative_two_pairs_le_shiftedMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr : r ≤ s.bandwidth) (x u : Vector p) (hu : ‖u‖ ≤ r)
    {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j k k| ≤
      Real.exp 9 * s.fourthPairCoordinateCap A a₃ a₄ x j k := by
  have hb := s.bandwidth_pos
  have hentry (b c : Bool) :
      |∫ z, s.softFaceMixedSecond {(j, b), (k, c)} j k (A.mulVec z + (x + u)) ∂standardGaussian p| ≤ Real.exp 9 *
        compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) ![(j, b), (k, c)] := by
    have hf : Function.Injective (fun i : Fin 2 => (![(j, b), (k, c)] i : Face p).1) :=
      (injective_pair_coordinates j k b c).mpr hjk
    let T : CompatibleFaceTuple p 2 := ⟨![(j, b), (k, c)], hf⟩
    have hset : T.activeFaceSet = {(j, b), (k, c)} := by
      change faceFamilySet ![(j, b), (k, c)] = _
      exact faceFamilySet_pair _ _
    have ha := s.abs_softFaceMixedSecond_le_fourthPairMomentCap hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T 0 1 (x + u)
    have hs := s.fourthPairMomentCap_shift_le_exp_nine hp A ha3 ha4 hc x T hu hr
    rw [compatibleTupleCap_of_injective _ _ hf]
    simpa only [hset, T, Matrix.cons_val_zero, Matrix.cons_val_one] using ha.trans hs
  have hbase := s.abs_convolutionFourthDerivative_two_pairs_soft_faces A (x + u) hjk
  simp only [Fintype.sum_prod_type] at hbase
  apply hbase.trans
  calc
    _ ≤ (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool, Real.exp 9 *
        compatibleTupleCap (s.fourthPairMomentCap A a₃ a₄ x) ![(j, b), (k, c)] := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      exact hentry b c
    _ = _ := by
      simp only [fourthPairCoordinateCap, if_pos hjk, ← Finset.mul_sum]
      ring

theorem abs_convolutionFourthDerivative_one_pair_le_shiftedMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr : r ≤ s.bandwidth) (x u : Vector p) (hu : ‖u‖ ≤ r)
    {j k l : Fin p} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j k l| ≤
      Real.exp 9 * s.fourthTripleCoordinateCap A a₃ a₄ x j k l := by
  have hb := s.bandwidth_pos
  have hentry (b c d : Bool) :
      |∫ z, s.softFaceDirectional {(j, b), (k, c), (l, d)} (coordinateDirection j) (A.mulVec z + (x + u)) ∂standardGaussian p| ≤ Real.exp 9 *
        compatibleTupleCap (s.fourthTripleMomentCap A a₃ a₄ x) ![(j, b), (k, c), (l, d)] := by
    have hf : Function.Injective (fun i : Fin 3 => (![(j, b), (k, c), (l, d)] i : Face p).1) :=
      (injective_triple_coordinates j k l b c d).mpr (show j ≠ k ∧ j ≠ l ∧ k ≠ l from ⟨hjk, hjl, hkl⟩)
    let T : CompatibleFaceTuple p 3 := ⟨![(j, b), (k, c), (l, d)], hf⟩
    have hset : T.activeFaceSet = {(j, b), (k, c), (l, d)} := by
      change faceFamilySet ![(j, b), (k, c), (l, d)] = _
      exact faceFamilySet_triple _ _ _
    have ha := s.abs_softFaceDirectional_le_fourthTripleMomentCap hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc T 0 (x + u)
    have hs := s.fourthTripleMomentCap_shift_le_exp_nine hp A ha3 ha4 hc x T hu hr
    rw [compatibleTupleCap_of_injective _ _ hf]
    simpa only [hset, T, Matrix.cons_val_zero, Matrix.cons_val_one] using ha.trans hs
  have hbase := s.abs_convolutionFourthDerivative_one_pair_soft_faces A (x + u) hjk hjl hkl
  simp only [Fintype.sum_prod_type] at hbase
  apply hbase.trans
  calc
    _ ≤ (6 / s.bandwidth ^ 3) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, Real.exp 9 *
        compatibleTupleCap (s.fourthTripleMomentCap A a₃ a₄ x) ![(j, b), (k, c), (l, d)] := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d _
      exact hentry b c d
    _ = _ := by
      simp only [fourthTripleCoordinateCap, if_pos (show j ≠ k ∧ j ≠ l ∧ k ≠ l from ⟨hjk, hjl, hkl⟩), ← Finset.mul_sum]
      ring

theorem abs_convolutionFourthDerivative_distinct_le_shiftedMomentCap
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (_h43 : a₄ ≤ a₃) (_h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr : r ≤ s.bandwidth) (x u : Vector p) (hu : ‖u‖ ≤ r)
    {j k l m : Fin p} (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j k l m| ≤
      Real.exp 9 * s.fourthQuadrupleCoordinateCap A a₃ a₄ x j k l m := by
  have hb := s.bandwidth_pos
  have hentry (b c d e : Bool) :
      (∫ z, s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)} (A.mulVec z + (x + u)) ∂standardGaussian p) ≤ Real.exp 9 *
        compatibleTupleCap (s.fourthQuadrupleMomentCap A a₃ a₄ x) ![(j, b), (k, c), (l, d), (m, e)] := by
    have hf : Function.Injective (fun i : Fin 4 => (![(j, b), (k, c), (l, d), (m, e)] i : Face p).1) :=
      (injective_quadruple_coordinates j k l m b c d e).mpr (show j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m from ⟨hjk, hjl, hjm, hkl, hkm, hlm⟩)
    let T : CompatibleFaceTuple p 4 := ⟨![(j, b), (k, c), (l, d), (m, e)], hf⟩
    have hset : T.activeFaceSet = {(j, b), (k, c), (l, d), (m, e)} := by
      change faceFamilySet ![(j, b), (k, c), (l, d), (m, e)] = _
      exact faceFamilySet_quadruple _ _ _ _
    have ha := s.integral_softFaceWeight_le_fourthQuadrupleMomentCap A hQ3 ha3 hQ4 ha4 hdiag hc T (x + u)
    have hs := s.fourthQuadrupleMomentCap_shift_le_exp_nine hp A ha3 ha4 hc x T hu hr
    rw [compatibleTupleCap_of_injective _ _ hf]
    simpa only [hset, T, Matrix.cons_val_zero, Matrix.cons_val_one] using ha.trans hs
  have hbase := s.abs_convolutionFourthDerivative_distinct_soft_faces A (x + u) hjk hjl hjm hkl hkm hlm
  have hmass (S : Finset (Face p)) :
      0 ≤ ∫ z, s.softFaceWeight S (A.mulVec z + (x + u)) ∂standardGaussian p :=
    integral_nonneg (fun z => s.softFaceWeight_nonneg _ _)
  simp only [Fintype.sum_prod_type, abs_of_nonneg (hmass _)] at hbase
  apply hbase.trans
  calc
    _ ≤ (24 / s.bandwidth ^ 4) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool, Real.exp 9 *
        compatibleTupleCap (s.fourthQuadrupleMomentCap A a₃ a₄ x) ![(j, b), (k, c), (l, d), (m, e)] := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro e _
      exact hentry b c d e
    _ = _ := by
      simp only [fourthQuadrupleCoordinateCap, if_pos (show j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m from ⟨hjk, hjl, hjm, hkl, hkm, hlm⟩), ← Finset.mul_sum]
      ring

/-- The sum of the separate local fourth-derivative suprema is bounded by
positive face moments at the single common base point. Each supremum has
been bounded before the finite tensor is summed. -/
theorem sum_localConvolutionFourthSup_unit_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      Real.exp 9 *
        ((4 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth) *
          s.gaussianFaceMomentSum A x 1 3 +
        (40 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 2) *
          s.gaussianFaceMomentSum A x 2 2 +
        (240 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 3) *
          s.gaussianFaceMomentSum A x 3 1 +
        (1080 / (pairGap (A * A.transpose) * a₃ * a₄) / s.bandwidth ^ 4) *
          s.gaussianFaceMomentSum A x 4 0) := by
  have hh : (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      (∑ j, Real.exp 9 * s.fourthSingletonCoordinateCap A a₃ a₄ x j) +
      4 * (∑ j, ∑ k, Real.exp 9 * s.fourthPairCoordinateCap A a₃ a₄ x j k) +
      3 * (∑ j, ∑ k, Real.exp 9 * s.fourthPairCoordinateCap A a₃ a₄ x j k) +
      6 * (∑ j, ∑ k, ∑ l, Real.exp 9 * s.fourthTripleCoordinateCap A a₃ a₄ x j k l) +
      ∑ j, ∑ k, ∑ l, ∑ m, Real.exp 9 * s.fourthQuadrupleCoordinateCap A a₃ a₄ x j k l m := by
    apply s.sum_localConvolutionFourthSup_le_of_uniform_canonical_bounds A hr0 x 1
    · intro j
      exact mul_nonneg (Real.exp_nonneg _) (s.fourthSingletonCoordinateCap_nonneg A ha3 ha4 hc x j)
    · intro j k
      exact mul_nonneg (Real.exp_nonneg _) (s.fourthPairCoordinateCap_nonneg A ha3 ha4 hc x j k)
    · intro j k
      exact mul_nonneg (Real.exp_nonneg _) (s.fourthPairCoordinateCap_nonneg A ha3 ha4 hc x j k)
    · intro j k l
      exact mul_nonneg (Real.exp_nonneg _) (s.fourthTripleCoordinateCap_nonneg A ha3 ha4 hc x j k l)
    · intro j k l m
      exact mul_nonneg (Real.exp_nonneg _) (s.fourthQuadrupleCoordinateCap_nonneg A ha3 ha4 hc x j k l m)
    · intro j u hu
      simpa only [Real.sqrt_one, one_smul] using
        s.abs_convolutionFourthDerivative_diagonal_le_shiftedMomentCap
          hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr x u hu j
    · intro j k hjk u hu
      simpa only [Real.sqrt_one, one_smul] using
        s.abs_convolutionFourthDerivative_triple_le_shiftedMomentCap
          hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr x u hu hjk
    · intro j k hjk u hu
      simpa only [Real.sqrt_one, one_smul] using
        s.abs_convolutionFourthDerivative_two_pairs_le_shiftedMomentCap
          hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr x u hu hjk
    · intro j k l hjk hjl hkl u hu
      simpa only [Real.sqrt_one, one_smul] using
        s.abs_convolutionFourthDerivative_one_pair_le_shiftedMomentCap
          hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr x u hu hjk hjl hkl
    · intro j k l m hjk hjl hjm hkl hkm hlm u hu
      simpa only [Real.sqrt_one, one_smul] using
        s.abs_convolutionFourthDerivative_distinct_le_shiftedMomentCap
          hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr x u hu hjk hjl hjm hkl hkm hlm
  apply hh.trans_eq
  simp only [← Finset.mul_sum,
    s.sum_fourthSingletonCoordinateCap_eq_ordered,
    s.sum_fourthPairCoordinateCap_eq_ordered,
    s.sum_fourthTripleCoordinateCap_eq_ordered,
    s.sum_fourthQuadrupleCoordinateCap_eq_ordered]
  have he := congrArg (fun y : ℝ => Real.exp 9 * y)
    (s.sum_ordered_fourthMomentCaps_eq A x a₃ a₄ hdiag)
  simp only [← Finset.mul_sum, s.gaussianFaceMomentSumAll_eq] at he
  linear_combination he

/-- Entrywise local suprema in the actual ordered tube-moment form. -/
theorem sum_localConvolutionFourthSup_unit_le_faceMoments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      (Real.exp 9 / (pairGap (A * A.transpose) * a₃ * a₄)) *
        (4 * (∑ T : OrderedFaceTuples s.faces 1, faceMoment T.val s A x 3) +
        40 * (∑ T : OrderedFaceTuples s.faces 2, faceMoment T.val s A x 2) +
        240 * (∑ T : OrderedFaceTuples s.faces 3, faceMoment T.val s A x 1) +
        1080 * (∑ T : OrderedFaceTuples s.faces 4, faceMoment T.val s A x 0)) := by
  apply (s.sum_localConvolutionFourthSup_unit_le_det_moments hp A
    hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr0 hr x).trans_eq
  rw [← s.gaussianFaceMomentSum_div_eq_ordered_faceMoments A x 1 3,
    ← s.gaussianFaceMomentSum_div_eq_ordered_faceMoments A x 2 2,
    ← s.gaussianFaceMomentSum_div_eq_ordered_faceMoments A x 3 1,
    ← s.gaussianFaceMomentSum_div_eq_ordered_faceMoments A x 4 0]
  ring

end
end RectangleCLT.FaceSmoother
