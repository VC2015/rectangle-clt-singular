import RectangleCLT.GaussianThirdAssembly

/-! Second Gaussian derivatives using only pairwise nondegeneracy.
The estimates are uniform in the smoother bandwidth and in translations;
the full Gaussian factor is allowed to be singular. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section
open GaussianTube

variable {p : ℕ} (s : FaceSmoother p)

theorem mixedSecondDerivativeF_distinct_soft_faces (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.mixedSecondDerivativeF x j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) * s.softFaceWeight {(j, b), (k, c)} x := by
  classical
  simp only [s.mixedSecondDerivativeF_eq, FaceWeights.diagonalMass, if_neg hjk, sub_zero]
  simp_rw [s.softFaceWeight_pair x hjk]
  simp only [Fintype.sum_bool, faceSign, Bool.false_eq_true, ↓reduceIte, FaceWeights.v]
  ring

theorem mixedSecondDerivativeF_diagonal_soft_faces (x : Vector p) (j : Fin p) :
    s.mixedSecondDerivativeF x j j =
      -(1 / s.bandwidth) * ∑ b : Bool,
        faceSign (j, b) * s.softFaceDirectional {(j, b)} (coordinateDirection j) x := by
  classical
  simp only [s.mixedSecondDerivativeF_eq, FaceWeights.diagonalMass, ↓reduceIte]
  simp only [softFaceDirectional, Finset.sum_singleton, Finset.card_singleton,
    normalDot_coordinate_eq, ↓reduceIte, softFaceWeight, Finset.prod_singleton,
    directionalMean_coordinate]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem convolutionSecondDerivative_eq_standardGaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw A) x j k =
      ∫ z, s.mixedSecondDerivativeF (A.mulVec z + x) j k ∂standardGaussian p := by
  have hm : AEStronglyMeasurable (fun y : Vector p => s.mixedSecondDerivativeF (x + y) j k)
      ((standardGaussian p).map A.mulVec) :=
    (((s.continuous_secondDerivative j k).comp
      (continuous_const.add continuous_id)).measurable.aestronglyMeasurable)
  rw [s.convolutionSecondDerivative_eq_integral]
  change (∫ y, s.mixedSecondDerivativeF (x + y) j k ∂(standardGaussian p).map A.mulVec) = _
  rw [integral_map (measurable_mulVec A).aemeasurable hm]
  exact integral_congr_ae (ae_of_all _ (fun z =>
    congrArg (fun y : Vector p => s.mixedSecondDerivativeF y j k) (add_comm x (A.mulVec z))))

theorem convolutionSecondDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p} (hjk : j ≠ k) :
    s.convolutionSecondDerivative (gaussianLaw A) x j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) *
          (∫ z, s.softFaceWeight {(j, b), (k, c)} (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2)) *
      s.softFaceWeight {(j, b.1), (k, b.2)} (A.mulVec z + x)
  have hF (b : Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceWeight_gaussian A _ x).const_mul _
  have hpoint (z : Vector p) : s.mixedSecondDerivativeF (A.mulVec z + x) j k =
      (2 / s.bandwidth ^ 2) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedSecondDerivativeF_distinct_soft_faces (A.mulVec z + x) hjk
  rw [s.convolutionSecondDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul, Fintype.sum_prod_type]

theorem convolutionSecondDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw A) x j j =
      -(1 / s.bandwidth) * ∑ b : Bool, faceSign (j, b) *
        (∫ z, s.softFaceDirectional {(j, b)} (coordinateDirection j)
          (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.convolutionSecondDerivative_eq_standardGaussian]
  simp_rw [s.mixedSecondDerivativeF_diagonal_soft_faces]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ =>
    (s.integrable_softFaceDirectional_gaussian A _ x _).const_mul (faceSign (j, b)))]
  simp only [integral_const_mul]

private theorem comparison_abs_signed_sum_le {ι : Type*} [Fintype ι] (c t : ι → ℝ)
    (hc : ∀ i, |c i| = 1) : |∑ i, c i * t i| ≤ ∑ i, |t i| := by
  calc
    _ ≤ ∑ i, |c i * t i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => by rw [abs_mul, hc, one_mul])

theorem abs_convolutionSecondDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionSecondDerivative (gaussianLaw A) x j k| ≤
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        (∫ z, s.softFaceWeight {(j, b), (k, c)} (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.convolutionSecondDerivative_distinct_soft_faces A x hjk, abs_mul,
    abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (sq_nonneg _))
  have hh := comparison_abs_signed_sum_le
    (fun b : Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2))
    (fun b : Bool × Bool => ∫ z, s.softFaceWeight {(j, b.1), (k, b.2)}
      (A.mulVec z + x) ∂standardGaussian p)
    (fun _ => by simp only [abs_mul, abs_faceSign, one_mul])
  have ht (b : Bool × Bool) : 0 ≤ ∫ z, s.softFaceWeight {(j, b.1), (k, b.2)}
      (A.mulVec z + x) ∂standardGaussian p :=
    integral_nonneg (fun z => s.softFaceWeight_nonneg _ _)
  simpa only [Fintype.sum_prod_type, abs_of_nonneg (ht _)] using hh

theorem abs_convolutionSecondDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p) :
    |s.convolutionSecondDerivative (gaussianLaw A) x j j| ≤
      (1 / s.bandwidth) * ∑ b : Bool,
        |∫ z, s.softFaceDirectional {(j, b)} (coordinateDirection j)
          (A.mulVec z + x) ∂standardGaussian p| := by
  rw [s.convolutionSecondDerivative_diagonal_soft_faces A x j, abs_mul, abs_neg,
    abs_of_pos (div_pos zero_lt_one s.bandwidth_pos)]
  exact mul_le_mul_of_nonneg_left
    (comparison_abs_signed_sum_le (fun b : Bool => faceSign (j, b))
      (fun b : Bool => ∫ z, s.softFaceDirectional {(j, b)} (coordinateDirection j)
        (A.mulVec z + x) ∂standardGaussian p) (fun _ => abs_faceSign _))
    (div_nonneg zero_le_one s.bandwidth_pos.le)

/-- The second-order positive face majorant, before any covariance estimate.
It is useful under additional averages over independent shifts as well. -/
theorem sum_abs_convolutionSecondDerivative_le_ordered_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) +
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
  classical
  let d : Fin p → ℝ := fun j => (1 / s.bandwidth) * ∑ b : Bool,
    |∫ z, s.softFaceDirectional {(j, b)} (coordinateDirection j)
      (A.mulVec z + x) ∂standardGaussian p|
  let o : Fin p → Fin p → ℝ := fun j k => if j ≠ k then
    (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
      (∫ z, s.softFaceWeight {(j, b), (k, c)} (A.mulVec z + x) ∂standardGaussian p) else 0
  have hpoint (j k : Fin p) : |s.convolutionSecondDerivative (gaussianLaw A) x j k| ≤
      (if j = k then d j else 0) + o j k := by
    by_cases hjk : j = k
    · subst k
      simpa [d, o] using s.abs_convolutionSecondDerivative_diagonal_soft_faces A x j
    · simpa [o, hjk] using s.abs_convolutionSecondDerivative_distinct_soft_faces A x hjk
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpoint j k))
  have hd : (∑ j, d j) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p| := by
    have hh := sum_singleton_coordinate_signs (p := p)
      (fun f => (1 / s.bandwidth) * |∫ z, s.softFaceDirectional (faceFamilySet f)
        (coordinateDirection (f 0).1) (A.mulVec z + x) ∂standardGaussian p|)
    simpa only [d, faceFamilySet_singleton, Matrix.cons_val_zero, ← Finset.mul_sum] using hh
  have ho : (∑ j, ∑ k, o j k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
    have hh := sum_pair_coordinate_signs (p := p)
      (fun f => (2 / s.bandwidth ^ 2) *
        (∫ z, s.softFaceWeight (faceFamilySet f) (A.mulVec z + x) ∂standardGaussian p))
    simpa only [o, faceFamilySet_pair, Matrix.cons_val_zero, ← Finset.mul_sum] using hh
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, hd, ho] using hs

theorem abs_softFaceDirectional_singleton_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face i).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤
      s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  have hd : IsUnit (T.gram (A * A.transpose)).det := by
    rw [Matrix.det_fin_one, T.gram_diagonal hdiag 0]
    exact isUnit_one
  have hb := s.abs_softFaceDirectional_gaussian_active_coordinate_le A
    T.activeFaceSet (T.face i).1 (T.coordinate_mem_activeFaceSet i) x
    (T.coordinateDual A (T.face i).1)
    (T.coordinateDual_agrees_on_activeFaceSet A hd (T.face i).1)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_one,
    show (1 : ℝ) + 1 = 2 by norm_num] at hb
  apply hb.trans
  apply add_le_add
  · simpa only [one_mul] using s.integral_abs_linear_softFaceWeight_le_moment hp A
      T.activeFaceSet x _ zero_le_one (fun z => by
        simpa only [one_mul] using T.singleton_abs_faceDot_coordinateDual_le A hdiag i z)
  · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
    apply Finset.sum_le_sum
    intro f _
    simpa only [gaussianSoftFaceMoment_zero, one_mul] using
      mul_le_mul_of_nonneg_right (T.singleton_abs_newFace_coefficient_le_one A hdiag i f)
        (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))

private theorem comparison_covariance_symmetric (A : Matrix (Fin p) (Fin p) ℝ) :
    ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
  intro j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem abs_softFaceDirectional_singleton_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face i).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤
      (1 / pairGap (A * A.transpose)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        (1 / pairGap (A * A.transpose)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  have hcoef : 1 ≤ 1 / pairGap (A * A.transpose) :=
    (le_div_iff₀ hc).mpr (by simpa using pairGap_le_one (A * A.transpose))
  apply (s.abs_softFaceDirectional_singleton_le_moments hp A T hdiag i x).trans
  apply add_le_add
  · rw [Matrix.det_fin_one, T.gram_diagonal hdiag 0, mul_one]
    exact le_mul_of_one_le_left (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 1) hcoef
  · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
    apply Finset.sum_le_sum
    intro f hf
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hdet : pairGap (A * A.transpose) ≤ (T.appendGram f (A * A.transpose)).det := by
      change pairGap (A * A.transpose) ≤ (U.gram (A * A.transpose)).det
      exact U.gram_two_det_ge_pairGap (comparison_covariance_symmetric A) hdiag hc.le
    have hfactor : 1 ≤ (1 / pairGap (A * A.transpose)) *
        (T.appendGram f (A * A.transpose)).det := by
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hc).mpr (by simpa using hdet)
    exact le_mul_of_one_le_left
      (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 0) hfactor

/-- Determinant-weighted positive majorant at second order, retaining the
two face orders separately for subsequent averaging arguments. -/
theorem sum_abs_convolutionSecondDerivative_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      (1 / pairGap (A * A.transpose) / s.bandwidth) * s.gaussianFaceMomentSum A x 1 1 +
      (4 / pairGap (A * A.transpose) / s.bandwidth ^ 2) * s.gaussianFaceMomentSum A x 2 0 := by
  have hsingle := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceDirectional_singleton_le_det_moments hp A T.val hdiag hc 0 x)
        (div_nonneg zero_le_one s.bandwidth_pos.le))
  have hsingle' :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) ≤
      (1 / pairGap (A * A.transpose) / s.bandwidth) * s.gaussianFaceMomentSumAll A x 1 1 +
      (2 / pairGap (A * A.transpose) / s.bandwidth ^ 2) * s.gaussianFaceMomentSumAll A x 2 0 := by
    apply hsingle.trans_eq
    rw [← s.gaussianFaceMomentSumAll_extend A x 1 0]
    change _ = (1 / pairGap (A * A.transpose) / s.bandwidth) *
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (T.val.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.val.activeFaceSet 1) + _
    simp only [mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hpair :
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p)) ≤
      (2 / pairGap (A * A.transpose) / s.bandwidth ^ 2) * s.gaussianFaceMomentSumAll A x 2 0 := by
    unfold gaussianFaceMomentSumAll
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T _
    have hdet := T.val.gram_two_det_ge_pairGap (comparison_covariance_symmetric A) hdiag hc.le
    have hfactor : 1 ≤ (T.val.gram (A * A.transpose)).det / pairGap (A * A.transpose) :=
      (le_div_iff₀ hc).mpr (by simpa using hdet)
    have hcoef := mul_le_mul_of_nonneg_left hfactor
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s.bandwidth))
    have hh := mul_le_mul_of_nonneg_right hcoef
      (s.gaussianSoftFaceMoment_nonneg A x T.val.activeFaceSet 0)
    simpa only [gaussianSoftFaceMoment_zero, mul_one, one_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hh
  apply (s.sum_abs_convolutionSecondDerivative_le_ordered_soft_faces A x).trans
  apply (add_le_add hsingle' hpair).trans_eq
  simp only [s.gaussianFaceMomentSumAll_eq]
  ring

theorem gaussianFaceMomentSum_div_le_pairGap (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {q k : ℕ}
    (hq0 : 0 < q) (hq : q ≤ 2)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q ≤
      (2 : ℝ) ^ k * (q : ℝ) ^ q * (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  rw [s.gaussianFaceMomentSum_div_eq_factorial]
  have hd (T : CompatibleFaceSets s.faces q) :
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det := by
    rw [normalMatrix_gram]
    have hqcases : q = 1 ∨ q = 2 := by omega
    rcases hqcases with rfl | rfl
    · rw [Matrix.det_fin_one, (compatibleSetTuple T).gram_diagonal hdiag 0]
      exact isUnit_one
    · exact isUnit_iff_ne_zero.mpr (ne_of_gt (hc.trans_le
        ((compatibleSetTuple T).gram_two_det_ge_pairGap
          (comparison_covariance_symmetric A) hdiag hc.le)))
  have hh := sum_faceMoment_le s A x hp hq0 (hq.trans (by omega))
    (by norm_num : (0 : ℝ) < 1) hdiag hd k
  simpa only [Real.sqrt_one, one_pow, mul_one] using hh

/-- One explicit positive universal constant for the local Gaussian
comparison Hessian. -/
def gaussianSecondConstant : ℝ := 2 * Real.exp 40 + 16 * Real.exp 16

theorem gaussianSecondConstant_pos : 0 < gaussianSecondConstant := by
  unfold gaussianSecondConstant
  positivity

/-- Uniform second Gaussian derivative bound requiring only a positive
pairwise gap. No positive lower bound for triples, quadruples or the full
covariance is assumed. -/
theorem sum_abs_convolutionSecondDerivative_gaussian_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose) := by
  have h₁ := s.gaussianFaceMomentSum_div_le_pairGap hp A x (q := 1) (k := 1)
    (by omega) (by omega) hdiag hc
  have h₂ := s.gaussianFaceMomentSum_div_le_pairGap hp A x (q := 2) (k := 0)
    (by omega) (by omega) hdiag hc
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, pow_zero, pow_one, one_mul, mul_one,
    Nat.reduceAdd, Nat.cast_add, Real.sq_sqrt hL] at h₁ h₂
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left h₁ (div_nonneg zero_le_one hc.le))
    (mul_le_mul_of_nonneg_left h₂ (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc.le))
  calc
    _ ≤ (1 / pairGap (A * A.transpose)) *
        (s.gaussianFaceMomentSum A x 1 1 / s.bandwidth ^ 1) +
      (4 / pairGap (A * A.transpose)) *
        (s.gaussianFaceMomentSum A x 2 0 / s.bandwidth ^ 2) := by
      convert s.sum_abs_convolutionSecondDerivative_le_det_moments hp A x hdiag hc using 1
      ring
    _ ≤ (1 / pairGap (A * A.transpose)) * (2 * dimensionLog p * Real.exp 40) +
      (4 / pairGap (A * A.transpose)) * (4 * dimensionLog p * Real.exp 16) := by
      simpa only [pow_one] using hh
    _ = _ := by unfold gaussianSecondConstant; ring

end
end RectangleCLT.FaceSmoother
