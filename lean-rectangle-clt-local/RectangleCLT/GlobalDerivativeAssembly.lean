import RectangleCLT.GlobalDerivativeBounds

/-! Assembly of the genuine full-dual fourth derivative bounds.
Each separate local supremum is controlled before tensor summation.
The face moments below are concrete integrals, not assumed Gaussian caps. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

private theorem full_family_card_le {q : ℕ} (f : Fin q → Face p) :
    (faceFamilySet f).card ≤ q := by
  exact (Finset.card_image_le).trans_eq (by simp)

theorem abs_softFaceDirectional_fullDual_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (hS : S.card ≤ 4) (j : Fin p)
    {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r) :
    |∫ z, s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + (x + u))
      ∂standardGaussian p| ≤ Real.exp 9 * ((Real.sqrt ν)⁻¹ *
        s.fullDualGaussianSoftFaceMoment A ν x S 1) := by
  exact (s.abs_softFaceDirectional_fullDual_le_moment hp A hν hlower (x + u) S j).trans
    ((mul_le_mul_of_nonneg_left
      (s.fullDualGaussianSoftFaceMoment_shift_le_exp_nine hp A hν hlower x S hS 1 hu hr)
      (by positivity)).trans_eq (by ring))

theorem abs_softFaceCoordinateSecond_fullDual_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (hS : S.card ≤ 4) (j : Fin p)
    (hj : j ∈ S.image Prod.fst)
    {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r) :
    |∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + (x + u))
      ∂standardGaussian p| ≤ Real.exp 9 * (2 * (Real.sqrt ν)⁻¹ ^ 2 *
        s.fullDualGaussianSoftFaceMoment A ν x S 2) := by
  exact (s.abs_softFaceCoordinateSecond_fullDual_le_moment hp A hν hlower (x + u) S j hj).trans
    ((mul_le_mul_of_nonneg_left
      (s.fullDualGaussianSoftFaceMoment_shift_le_exp_nine hp A hν hlower x S hS 2 hu hr)
      (by positivity)).trans_eq (by ring))

theorem abs_softFaceMixedSecond_fullDual_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (hS : S.card ≤ 4) (j k : Fin p)
    (hj : j ∈ S.image Prod.fst) (hk : k ∈ S.image Prod.fst)
    {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r) :
    |∫ z, s.softFaceMixedSecond S j k (A.mulVec z + (x + u))
      ∂standardGaussian p| ≤ Real.exp 9 * (2 * (Real.sqrt ν)⁻¹ ^ 2 *
        s.fullDualGaussianSoftFaceMoment A ν x S 2) := by
  exact (s.abs_softFaceMixedSecond_fullDual_le_moment hp A hν hlower (x + u) S j k hj hk).trans
    ((mul_le_mul_of_nonneg_left
      (s.fullDualGaussianSoftFaceMoment_shift_le_exp_nine hp A hν hlower x S hS 2 hu hr)
      (by positivity)).trans_eq (by ring))

theorem abs_softFaceCoordinateThird_fullDual_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (hS : S.card ≤ 4) (j : Fin p)
    (hj : j ∈ S.image Prod.fst)
    {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r) :
    |∫ z, s.softFaceCoordinateThird S j (A.mulVec z + (x + u))
      ∂standardGaussian p| ≤ Real.exp 9 * (4 * (Real.sqrt ν)⁻¹ ^ 3 *
        s.fullDualGaussianSoftFaceMoment A ν x S 3) := by
  exact (s.abs_softFaceCoordinateThird_fullDual_le_moment hp A hν hlower (x + u) S j hj).trans
    ((mul_le_mul_of_nonneg_left
      (s.fullDualGaussianSoftFaceMoment_shift_le_exp_nine hp A hν hlower x S hS 3 hu hr)
      (by positivity)).trans_eq (by ring))

def fullFourthSingletonCap (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (j : Fin p) : ℝ :=
  (4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) * ∑ b : Bool,
    s.fullDualGaussianSoftFaceMoment A ν x {(j, b)} 3

def fullFourthPairCap (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (j k : Fin p) : ℝ :=
  if j ≠ k then (4 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) *
    ∑ b : Bool, ∑ c : Bool, s.fullDualGaussianSoftFaceMoment A ν x {(j, b), (k, c)} 2
  else 0

def fullFourthTripleCap (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (j k l : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ k ≠ l then (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) *
    ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      s.fullDualGaussianSoftFaceMoment A ν x {(j, b), (k, c), (l, d)} 1
  else 0

def fullFourthQuadrupleCap (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (j k l m : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m then
    (24 / s.bandwidth ^ 4) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
      s.fullDualGaussianSoftFaceMoment A ν x {(j, b), (k, c), (l, d), (m, e)} 0
  else 0

theorem fullFourthSingletonCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) (j : Fin p) :
    0 ≤ s.fullFourthSingletonCap A ν x j := by
  have hband := s.bandwidth_pos
  unfold fullFourthSingletonCap
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    s.fullDualGaussianSoftFaceMoment_nonneg A ν x _ _)

theorem fullFourthPairCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) (j k : Fin p) :
    0 ≤ s.fullFourthPairCap A ν x j k := by
  unfold fullFourthPairCap
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => s.fullDualGaussianSoftFaceMoment_nonneg A ν x _ _)
  · exact le_rfl

theorem fullFourthTripleCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) (j k l : Fin p) :
    0 ≤ s.fullFourthTripleCap A ν x j k l := by
  have hband := s.bandwidth_pos
  unfold fullFourthTripleCap
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        s.fullDualGaussianSoftFaceMoment_nonneg A ν x _ _)
  · exact le_rfl

theorem fullFourthQuadrupleCap_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) (j k l m : Fin p) :
    0 ≤ s.fullFourthQuadrupleCap A ν x j k l m := by
  unfold fullFourthQuadrupleCap
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        s.fullDualGaussianSoftFaceMoment_nonneg A ν x _ _)
  · exact le_rfl

theorem abs_convolutionFourth_fullDual_singleton_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r)
    (j : Fin p) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j j j| ≤
      Real.exp 9 * s.fullFourthSingletonCap A ν x j := by
  have hband := s.bandwidth_pos
  have hentry (b : Bool) := s.abs_softFaceCoordinateThird_fullDual_shifted_le
    hp A hν hlower x {(j, b)} (by simp) j (by simp) hr u hu
  apply (s.abs_convolutionFourthDerivative_diagonal_soft_faces A (x + u) j).trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun b _ => hentry b)
    (by positivity : 0 ≤ 1 / s.bandwidth)
  exact hh.trans_eq (by simp only [fullFourthSingletonCap, ← Finset.mul_sum]; ring)

theorem abs_convolutionFourth_fullDual_triple_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r)
    {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j j k| ≤
      Real.exp 9 * s.fullFourthPairCap A ν x j k := by
  have hentry (b c : Bool) := s.abs_softFaceCoordinateSecond_fullDual_shifted_le
    hp A hν hlower x {(j, b), (k, c)}
    (by simpa only [faceFamilySet_pair] using
      (full_family_card_le ![(j, b), (k, c)]).trans (by decide : 2 ≤ 4)) j (by simp) hr u hu
  have hb := s.abs_convolutionFourthDerivative_triple_soft_faces A (x + u) hjk
  simp only [Fintype.sum_prod_type] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ => hentry b c)
    (by positivity : 0 ≤ 2 / s.bandwidth ^ 2)
  exact hh.trans_eq (by simp only [fullFourthPairCap, if_pos hjk, ← Finset.mul_sum]; ring)

theorem abs_convolutionFourth_fullDual_two_pairs_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r)
    {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j k k| ≤
      Real.exp 9 * s.fullFourthPairCap A ν x j k := by
  have hentry (b c : Bool) := s.abs_softFaceMixedSecond_fullDual_shifted_le
    hp A hν hlower x {(j, b), (k, c)}
    (by simpa only [faceFamilySet_pair] using
      (full_family_card_le ![(j, b), (k, c)]).trans (by decide : 2 ≤ 4)) j k (by simp) (by simp) hr u hu
  have hb := s.abs_convolutionFourthDerivative_two_pairs_soft_faces A (x + u) hjk
  simp only [Fintype.sum_prod_type] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ => hentry b c)
    (by positivity : 0 ≤ 2 / s.bandwidth ^ 2)
  exact hh.trans_eq (by simp only [fullFourthPairCap, if_pos hjk, ← Finset.mul_sum]; ring)

theorem abs_convolutionFourth_fullDual_one_pair_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r)
    {j k l : Fin p} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j j k l| ≤
      Real.exp 9 * s.fullFourthTripleCap A ν x j k l := by
  have hband := s.bandwidth_pos
  have hentry (b c d : Bool) := s.abs_softFaceDirectional_fullDual_shifted_le
    hp A hν hlower x {(j, b), (k, c), (l, d)}
    (by simpa only [faceFamilySet_triple] using
      (full_family_card_le ![(j, b), (k, c), (l, d)]).trans (by decide : 3 ≤ 4)) j hr u hu
  have hb := s.abs_convolutionFourthDerivative_one_pair_soft_faces A (x + u) hjk hjl hkl
  simp only [Fintype.sum_prod_type] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ =>
      Finset.sum_le_sum (s := Finset.univ) fun d _ => hentry b c d)
    (by positivity : 0 ≤ 6 / s.bandwidth ^ 3)
  exact hh.trans_eq (by simp only [fullFourthTripleCap,
    if_pos (show j ≠ k ∧ j ≠ l ∧ k ≠ l from ⟨hjk, hjl, hkl⟩), ← Finset.mul_sum]; ring)

theorem abs_convolutionFourth_fullDual_distinct_shifted_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr : r ≤ s.bandwidth) (u : Vector p) (hu : ‖u‖ ≤ r)
    {j k l m : Fin p} (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    |s.convolutionFourthDerivative (gaussianLaw A) (x + u) j k l m| ≤
      Real.exp 9 * s.fullFourthQuadrupleCap A ν x j k l m := by
  have hentry (b c d e : Bool) :
      |∫ z, s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)}
        (A.mulVec z + (x + u)) ∂standardGaussian p| ≤ Real.exp 9 *
          s.fullDualGaussianSoftFaceMoment A ν x {(j, b), (k, c), (l, d), (m, e)} 0 := by
    have hh := s.fullDualGaussianSoftFaceMoment_shift_le_exp_nine hp A hν hlower x
      {(j, b), (k, c), (l, d), (m, e)}
      (by simpa only [faceFamilySet_quadruple] using
        full_family_card_le ![(j, b), (k, c), (l, d), (m, e)]) 0 hu hr
    have hn : 0 ≤ ∫ z, s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)}
        (A.mulVec z + (x + u)) ∂standardGaussian p :=
      integral_nonneg fun z => s.softFaceWeight_nonneg _ _
    rw [abs_of_nonneg hn]
    simpa only [fullDualGaussianSoftFaceMoment_zero] using hh
  have hb := s.abs_convolutionFourthDerivative_distinct_soft_faces A (x + u) hjk hjl hjm hkl hkm hlm
  simp only [Fintype.sum_prod_type] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ =>
      Finset.sum_le_sum (s := Finset.univ) fun d _ =>
      Finset.sum_le_sum (s := Finset.univ) fun e _ => hentry b c d e)
    (by positivity : 0 ≤ 24 / s.bandwidth ^ 4)
  exact hh.trans_eq (by simp only [fullFourthQuadrupleCap,
    if_pos (show j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m from
      ⟨hjk, hjl, hjm, hkl, hkm, hlm⟩), ← Finset.mul_sum]; ring)

/-- The genuine sum of separate fourth local suprema has a positive
full-score moment majorant at a single common center. -/
theorem sum_localConvolutionFourthSup_fullDual_le_coordinate_caps (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      Real.exp 9 * ((∑ j, s.fullFourthSingletonCap A ν x j) +
        7 * (∑ j, ∑ k, s.fullFourthPairCap A ν x j k) +
        6 * (∑ j, ∑ k, ∑ l, s.fullFourthTripleCap A ν x j k l) +
        ∑ j, ∑ k, ∑ l, ∑ m, s.fullFourthQuadrupleCap A ν x j k l m) := by
  have hh := s.sum_localConvolutionFourthSup_le_of_uniform_canonical_bounds A hr0 x 1
    (fun j => Real.exp 9 * s.fullFourthSingletonCap A ν x j)
    (fun j k => Real.exp 9 * s.fullFourthPairCap A ν x j k)
    (fun j k => Real.exp 9 * s.fullFourthPairCap A ν x j k)
    (fun j k l => Real.exp 9 * s.fullFourthTripleCap A ν x j k l)
    (fun j k l m => Real.exp 9 * s.fullFourthQuadrupleCap A ν x j k l m)
    (fun j => mul_nonneg (Real.exp_nonneg _) (s.fullFourthSingletonCap_nonneg A ν x j))
    (fun j k => mul_nonneg (Real.exp_nonneg _) (s.fullFourthPairCap_nonneg A ν x j k))
    (fun j k => mul_nonneg (Real.exp_nonneg _) (s.fullFourthPairCap_nonneg A ν x j k))
    (fun j k l => mul_nonneg (Real.exp_nonneg _) (s.fullFourthTripleCap_nonneg A ν x j k l))
    (fun j k l m => mul_nonneg (Real.exp_nonneg _) (s.fullFourthQuadrupleCap_nonneg A ν x j k l m))
    (fun j u hu => by simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourth_fullDual_singleton_shifted_le hp A hν hlower x hr u hu j)
    (fun j k hjk u hu => by simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourth_fullDual_triple_shifted_le hp A hν hlower x hr u hu hjk)
    (fun j k hjk u hu => by simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourth_fullDual_two_pairs_shifted_le hp A hν hlower x hr u hu hjk)
    (fun j k l hjk hjl hkl u hu => by simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourth_fullDual_one_pair_shifted_le hp A hν hlower x hr u hu hjk hjl hkl)
    (fun j k l m hjk hjl hjm hkl hkm hlm u hu => by simpa only [Real.sqrt_one, one_smul] using
      s.abs_convolutionFourth_fullDual_distinct_shifted_le hp A hν hlower x hr u hu hjk hjl hjm hkl hkm hlm)
  exact hh.trans_eq (by simp only [← Finset.mul_sum]; ring)

def fullDualFaceMomentSumAll (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (q k : ℕ) : ℝ :=
  ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) q,
    s.fullDualGaussianSoftFaceMoment A ν x T.val.activeFaceSet k

def fullDualFaceMomentSum (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (q k : ℕ) : ℝ :=
  ∑ T : OrderedFaceTuples s.faces q,
    s.fullDualGaussianSoftFaceMoment A ν x T.val.activeFaceSet k

theorem fullDualFaceMomentSumAll_eq (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (q k : ℕ) :
    s.fullDualFaceMomentSumAll A ν x q k = s.fullDualFaceMomentSum A ν x q k := by
  unfold fullDualFaceMomentSumAll fullDualFaceMomentSum
  apply sum_orderedFaceTuples_univ_eq_restrict s.faces
    (fun T => s.fullDualGaussianSoftFaceMoment A ν x T.activeFaceSet k)
  rintro T ⟨i, hi⟩
  have hm : T.face i ∈ T.activeFaceSet :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp only [fullDualGaussianSoftFaceMoment,
    s.softFaceWeight_eq_zero_of_missing hm hi, mul_zero, integral_zero]

theorem sum_fullFourthSingletonCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) :
    (∑ j, s.fullFourthSingletonCap A ν x j) =
      (4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) * s.fullDualFaceMomentSumAll A ν x 1 3 := by
  have hh := sum_singleton_coordinate_signs (fun f : Fin 1 → Face p =>
    (4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) *
      s.fullDualGaussianSoftFaceMoment A ν x (faceFamilySet f) 3)
  simpa only [fullFourthSingletonCap, faceFamilySet_singleton,
    fullDualFaceMomentSumAll, ← Finset.mul_sum] using hh

theorem sum_fullFourthPairCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) :
    (∑ j, ∑ k, s.fullFourthPairCap A ν x j k) =
      (4 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) * s.fullDualFaceMomentSumAll A ν x 2 2 := by
  have hh := sum_pair_coordinate_signs (fun f : Fin 2 → Face p =>
    (4 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) *
      s.fullDualGaussianSoftFaceMoment A ν x (faceFamilySet f) 2)
  simpa only [fullFourthPairCap, faceFamilySet_pair,
    fullDualFaceMomentSumAll, ← Finset.mul_sum] using hh

theorem sum_fullFourthTripleCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.fullFourthTripleCap A ν x j k l) =
      (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) * s.fullDualFaceMomentSumAll A ν x 3 1 := by
  have hh := sum_triple_coordinate_signs (fun f : Fin 3 → Face p =>
    (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) *
      s.fullDualGaussianSoftFaceMoment A ν x (faceFamilySet f) 1)
  simpa only [fullFourthTripleCap, faceFamilySet_triple,
    fullDualFaceMomentSumAll, ← Finset.mul_sum] using hh

theorem sum_fullFourthQuadrupleCap_eq_ordered
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fullFourthQuadrupleCap A ν x j k l m) =
      (24 / s.bandwidth ^ 4) * s.fullDualFaceMomentSumAll A ν x 4 0 := by
  have hh := sum_quadruple_coordinate_signs (fun f : Fin 4 → Face p =>
    (24 / s.bandwidth ^ 4) *
      s.fullDualGaussianSoftFaceMoment A ν x (faceFamilySet f) 0)
  simpa only [fullFourthQuadrupleCap, faceFamilySet_quadruple,
    fullDualFaceMomentSumAll, ← Finset.mul_sum] using hh

/-- Ordered full-score moments control the sum of the separate local
suprema, with no active determinant or local-eigenvalue coefficient. -/
theorem sum_localConvolutionFourthSup_fullDual_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      Real.exp 9 *
        ((4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) * s.fullDualFaceMomentSum A ν x 1 3 +
        (28 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) * s.fullDualFaceMomentSum A ν x 2 2 +
        (36 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) * s.fullDualFaceMomentSum A ν x 3 1 +
        (24 / s.bandwidth ^ 4) * s.fullDualFaceMomentSum A ν x 4 0) := by
  apply (s.sum_localConvolutionFourthSup_fullDual_le_coordinate_caps hp A hν hlower x hr0 hr).trans_eq
  rw [s.sum_fullFourthSingletonCap_eq_ordered, s.sum_fullFourthPairCap_eq_ordered,
    s.sum_fullFourthTripleCap_eq_ordered, s.sum_fullFourthQuadrupleCap_eq_ordered]
  simp only [s.fullDualFaceMomentSumAll_eq]
  ring

/-- The third tensor has the corresponding full-score majorant. Averaging
these concrete moments is a separate tube/concentration step. -/
theorem sum_abs_convolutionThird_fullDual_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      (2 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth) * s.fullDualFaceMomentSum A ν x 1 2 +
        (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 2) * s.fullDualFaceMomentSum A ν x 2 1 +
        (6 / s.bandwidth ^ 3) * s.fullDualFaceMomentSum A ν x 3 0 := by
  have hband := s.bandwidth_pos
  have hsingle :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) ≤
        (2 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth) * s.fullDualFaceMomentSumAll A ν x 1 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceCoordinateSecond_fullDual_le_moment hp A hν hlower x
          T.val.activeFaceSet (T.val.face 0).1 (T.val.coordinate_mem_activeFaceSet 0))
        (by positivity : 0 ≤ 1 / s.bandwidth))
    exact hh.trans_eq (by simp only [fullDualFaceMomentSumAll, ← Finset.mul_sum]; ring)
  have hpair :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) ≤
        (2 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 2) * s.fullDualFaceMomentSumAll A ν x 2 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceDirectional_fullDual_le_moment hp A hν hlower x
          T.val.activeFaceSet (T.val.face 0).1)
        (by positivity : 0 ≤ 2 / s.bandwidth ^ 2))
    exact hh.trans_eq (by simp only [fullDualFaceMomentSumAll, ← Finset.mul_sum]; ring)
  have htriple :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) * (∫ z, s.softFaceWeight T.val.activeFaceSet
          (A.mulVec z + x) ∂standardGaussian p)) =
        (6 / s.bandwidth ^ 3) * s.fullDualFaceMomentSumAll A ν x 3 0 := by
    simp only [fullDualFaceMomentSumAll, fullDualGaussianSoftFaceMoment_zero,
      Finset.mul_sum]
  apply (s.sum_abs_convolutionThirdDerivative_le_ordered_soft_faces A x).trans
  have hh := add_le_add (add_le_add hsingle
    (mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 3))) (le_of_eq htriple)
  exact hh.trans_eq (by simp only [s.fullDualFaceMomentSumAll_eq]; ring)

end

end RectangleCLT.FaceSmoother
