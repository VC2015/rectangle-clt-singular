import RectangleCLT.GaussianFourthRecursion
import RectangleCLT.GaussianThirdMajorant
import RectangleCLT.FourthCoefficientScales

/-! Positive, projection-weighted majorants for the repeated fourth Gaussian
derivatives. Every derivative below is an actual differentiated Gaussian
integral; the nonnegative face moments retain the active coordinate set. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT

noncomputable section

set_option maxRecDepth 2048

theorem abs_faceDot_le_euclidean_norm (u v : Vector p) :
    |faceDot u v| ≤ ‖projectionEuclideanVector u‖ * ‖projectionEuclideanVector v‖ := by
  have heq : faceDot u v =
      ⟪projectionEuclideanVector u, projectionEuclideanVector v⟫_ℝ := by
    simp [faceDot, projectionEuclideanVector, PiLp.inner_apply, mul_comm]
  rw [heq]
  exact abs_real_inner_le_norm _ _

namespace CompatibleFaceTuple

open FaceSmoother

def appendThreeGram {p q : ℕ} (T : CompatibleFaceTuple p q) (f g h : Face p)
    (Q : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin (q + 3)) (Fin (q + 3)) ℝ :=
  let faces : Fin (q + 3) → Face p := Fin.snoc (Fin.snoc (Fin.snoc T.face f) g) h
  fun i j => faceSign (faces i) * faceSign (faces j) * Q (faces i).1 (faces j).1

theorem triple_initial_dualCoefficient_mul_inverse_sqrt_le_det {p : ℕ}
    (T : CompatibleFaceTuple p 3) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (ha4 : 0 < a₄) (h43 : a₄ ≤ a₃)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (i : Fin 2) :
    |normalDot (T.face 2) (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))| *
      (1 / Real.sqrt a₃) ≤
      (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ3 ha3 hsym
  have hb := (div_le_iff₀ hdet).mp
    (T.triple_initial_dualCoefficient_weight_div_det_le A hQ3 ha3 hdiag hc i)
  have hcoef : |normalDot (T.face 2)
      (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))| ≤
      (2 / (a₃ * pairGap (A * A.transpose))) * (T.gram (A * A.transpose)).det := by
    linarith
  have ha31 : a₃ ≤ 1 := h3c.trans (pairGap_le_one _)
  have hroot : a₄ ≤ Real.sqrt a₃ := by
    have hsq := Real.sq_sqrt ha3.le
    have hnon := Real.sqrt_nonneg a₃
    have hh : a₃ ≤ Real.sqrt a₃ := by
      nlinarith [mul_nonneg ha3.le (sub_nonneg.mpr ha31)]
    exact h43.trans hh
  calc
    _ ≤ ((2 / (a₃ * pairGap (A * A.transpose))) * (T.gram (A * A.transpose)).det) *
        (1 / a₄) := mul_le_mul hcoef (one_div_le_one_div_of_le ha4 hroot)
          (div_nonneg zero_le_one (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

theorem triple_initial_dualCoefficient_mul_pair_inverse_sqrt_le_det {p : ℕ}
    (T : CompatibleFaceTuple p 3) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (ha4 : 0 < a₄) (h43 : a₄ ≤ a₃)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (i : Fin 2) :
    |normalDot (T.face 2) (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))| *
      (1 / Real.sqrt (pairGap (A * A.transpose))) ≤
      (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ3 ha3 hsym
  have hb := (div_le_iff₀ hdet).mp
    (T.triple_initial_dualCoefficient_weight_div_det_le A hQ3 ha3 hdiag hc i)
  have hcoef : |normalDot (T.face 2)
      (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))| ≤
      (2 / (a₃ * pairGap (A * A.transpose))) * (T.gram (A * A.transpose)).det := by linarith
  calc
    _ ≤ ((2 / (a₃ * pairGap (A * A.transpose))) * (T.gram (A * A.transpose)).det) *
        (1 / Real.sqrt (pairGap (A * A.transpose))) :=
      mul_le_mul_of_nonneg_right hcoef (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    _ = (2 * (1 / (pairGap (A * A.transpose) * a₃ * Real.sqrt (pairGap (A * A.transpose))))) *
        (T.gram (A * A.transpose)).det := by ring
    _ ≤ (2 * (1 / (pairGap (A * A.transpose) * a₃ * a₄))) *
        (T.gram (A * A.transpose)).det := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (one_div_sqrt_pairGap_cost_le_localFourthCost ha4 h43 h3c (pairGap_le_one _))
        (by norm_num)) hdet.le
    _ = _ := by ring

theorem quadruple_nested_dualCoefficients_le_det {p : ℕ}
    (T : CompatibleFaceTuple p 4) (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) (j : Fin 3) :
    |normalDot (T.initial.face 2)
      (A.mulVec (T.initial.initial.coordinateDual A (T.initial.initial.face i).1))| *
      |normalDot (T.face 3) (A.mulVec (T.initial.coordinateDual A (T.initial.face j).1))| ≤
      (4 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ4 ha4 hsym
  have hbase := (div_le_iff₀ hdet).mp
    (T.quadruple_nested_regression_weight_div_det_le A hQ3 ha3 hQ4 ha4 hdiag hc)
  apply le_trans _ hbase
  apply mul_le_mul
  · exact (T.initial.initial.abs_coordinateDual_newFace_coefficient_le A i
      (T.initial.face 2)).trans (le_add_of_nonneg_left zero_le_one)
  · exact (T.initial.abs_coordinateDual_newFace_coefficient_le A j (T.face 3)).trans
      (le_add_of_nonneg_left zero_le_one)
  · exact abs_nonneg _
  · positivity

end CompatibleFaceTuple

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem gaussianSoftFaceMoment_mono (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (S : Finset (Face p))
    {k l : ℕ} (hkl : k ≤ l) :
    s.gaussianSoftFaceMoment A x S k ≤ s.gaussianSoftFaceMoment A x S l := by
  apply integral_mono (s.integrable_gaussianSoftFaceMoment hp A x S k)
    (s.integrable_gaussianSoftFaceMoment hp A x S l)
  intro z
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [fourFaceProjectionRadius_nonneg A z]) hkl)
    (s.softFaceWeight_nonneg S _)

theorem integral_abs_bilinear_softFaceWeight_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x u v : Vector p)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ z, |faceDot u z| ≤ C * fourFaceProjectionRadius A z)
    (hv : ∀ z, |faceDot v z| ≤ D * fourFaceProjectionRadius A z) :
    (∫ z, |faceDot u z| * |faceDot v z| * s.softFaceWeight S (A.mulVec z + x)
      ∂standardGaussian p) ≤ (C * D) * s.gaussianSoftFaceMoment A x S 2 := by
  rw [gaussianSoftFaceMoment, ← integral_const_mul]
  apply integral_mono
  · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
      (s.integrable_bilinear_softFaceWeight_gaussian A S x u v).abs
  · exact (s.integrable_gaussianSoftFaceMoment hp A x S 2).const_mul _
  · intro z
    dsimp only
    have hR := fourFaceProjectionRadius_nonneg A z
    have hh := mul_le_mul (hu z) (hv z) (abs_nonneg _) (mul_nonneg hC hR)
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (s.softFaceWeight_nonneg S _)
    calc
      _ ≤ (C * fourFaceProjectionRadius A z) * (D * fourFaceProjectionRadius A z) := hh
      _ = (C * D) * (fourFaceProjectionRadius A z) ^ 2 := by ring
      _ ≤ (C * D) * (1 + fourFaceProjectionRadius A z) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        nlinarith
      _ = _ := by ring

theorem abs_softFaceMixedSecond_gaussian_active_coordinate_le
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j k : Fin p)
    (hj : j ∈ S.image Prod.fst) (hk : k ∈ S.image Prod.fst) (x u v : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1)
    (hv : ∀ f ∈ S, A.mulVec v f.1 = coordinateDirection k f.1) :
    |∫ z, s.softFaceMixedSecond S j k (A.mulVec z + x) ∂standardGaussian p| ≤
      (∫ z, |faceDot v z| * |faceDot u z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      |faceDot v u| * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec v)| *
          (∫ z, |faceDot u z| * s.softFaceWeight (insert f S) (A.mulVec z + x)
            ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          |∫ z, s.softFaceDirectional (insert f S) (coordinateDirection k)
            (A.mulVec z + x) ∂standardGaussian p| := by
  rw [s.softFaceMixedSecond_gaussian_active_coordinate A S j k hj x u hu]
  have hC : 0 ≤ ((S.card : ℝ) + 1) / s.bandwidth :=
    div_nonneg (by positivity) s.bandwidth_pos.le
  refine (abs_add _ _).trans (add_le_add
    (s.abs_softFaceDirectional_gaussian_weighted_active_coordinate_le A S k hk x v u hv) ?_)
  rw [abs_mul, abs_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left _ hC
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro f _
    exact abs_mul _ _)

@[simp] theorem softFaceMixedSecond_diagonal (S : Finset (Face p)) (j : Fin p)
    (x : Vector p) : s.softFaceMixedSecond S j j x = s.softFaceCoordinateSecond S j x := by
  simp only [softFaceMixedSecond, softFaceCoordinateSecond, FaceWeights.diagonalMass,
    ite_true, pow_two]

theorem abs_softFaceDirectional_triple_mul_initialCoefficient_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 3)
    {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) (j : Fin 3) (x : Vector p) :
    |normalDot (T.face 2) (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))| *
      |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face j).1)
        (A.mulVec z + x) ∂standardGaussian p| ≤
      (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (4 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        (4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
          (T.appendGram f (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  classical
  let b := |normalDot (T.face 2)
    (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))|
  let u := T.coordinateDual A (T.face j).1
  have hb : 0 ≤ b := abs_nonneg _
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ3 ha3 hsym
  have hd := isUnit_iff_ne_zero.mpr hdet.ne'
  have hbase := s.abs_softFaceDirectional_gaussian_active_coordinate_le A T.activeFaceSet
    (T.face j).1 (T.coordinate_mem_activeFaceSet j) x u
    (T.coordinateDual_agrees_on_activeFaceSet A hd _)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_ofNat,
    show (3 : ℝ) + 1 = 4 by norm_num] at hbase
  have hlin := s.integral_abs_linear_softFaceWeight_le_moment hp A T.activeFaceSet x u
    (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (T.abs_faceDot_coordinateDual_le_inv_sqrt A hd ha3 (T.gram_lower hQ3)
      (by decide) (by decide) j)
  have hmain : b * (∫ z, |faceDot u z| * s.softFaceWeight T.activeFaceSet
      (A.mulVec z + x) ∂standardGaussian p) ≤
      (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 := by
    calc
      _ ≤ b * ((1 / Real.sqrt a₃) * s.gaussianSoftFaceMoment A x T.activeFaceSet 1) :=
        mul_le_mul_of_nonneg_left hlin hb
      _ = (b * (1 / Real.sqrt a₃)) * s.gaussianSoftFaceMoment A x T.activeFaceSet 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (T.triple_initial_dualCoefficient_mul_inverse_sqrt_le_det A hQ3 ha3 ha4 h43
          hdiag hc h3c i) (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 1)
  have hsum :
      (∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        b * |normalDot f (A.mulVec u)| * s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0) ≤
      ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        (4 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
    apply Finset.sum_le_sum
    intro f hf
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hcoef := U.quadruple_nested_dualCoefficients_le_det A hQ3 ha3 hQ4 ha4 hdiag hc i j
    have hi : U.initial = T := T.appendFace_initial f _
    have hf' : U.face 3 = f := T.appendFace_last f _
    rw [hi, hf'] at hcoef
    exact mul_le_mul_of_nonneg_right hcoef
      (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 0)
  calc
    _ ≤ b * ((∫ z, |faceDot u z| * s.softFaceWeight T.activeFaceSet (A.mulVec z + x)
        ∂standardGaussian p) + (4 / s.bandwidth) *
        ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet, |normalDot f (A.mulVec u)| *
          (∫ z, s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x)
            ∂standardGaussian p)) := mul_le_mul_of_nonneg_left hbase hb
    _ = b * (∫ z, |faceDot u z| * s.softFaceWeight T.activeFaceSet (A.mulVec z + x)
        ∂standardGaussian p) + (4 / s.bandwidth) *
        ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          b * |normalDot f (A.mulVec u)| * s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
      simp only [gaussianSoftFaceMoment_zero, mul_add]
      congr 1
      calc
        _ = (4 / s.bandwidth) * (b * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          |normalDot f (A.mulVec u)| * (∫ z, s.softFaceWeight (insert f T.activeFaceSet)
            (A.mulVec z + x) ∂standardGaussian p)) := by ring
        _ = _ := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f _
          ring
    _ ≤ _ := add_le_add hmain (mul_le_mul_of_nonneg_left hsum
      (div_nonneg (by norm_num) s.bandwidth_pos.le))

theorem abs_softFaceMixedSecond_pair_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 2)
    {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i j : Fin 2) (x : Vector p) :
    |∫ z, s.softFaceMixedSecond T.activeFaceSet (T.face i).1 (T.face j).1
      (A.mulVec z + x) ∂standardGaussian p| ≤
      (2 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
      (3 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        ((4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
          (T.appendGram f (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
        (4 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
          (4 / (pairGap (A * A.transpose) * a₃ * a₄)) *
            (T.appendTwoGram f g (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0) := by
  classical
  let c := pairGap (A * A.transpose)
  let D := 1 / (c * a₃ * a₄)
  let u := T.coordinateDual A (T.face i).1
  let v := T.coordinateDual A (T.face j).1
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdetlow := T.gram_two_det_ge_pairGap hsym hdiag hc.le
  have hdet := hc.trans_le hdetlow
  have hd := isUnit_iff_ne_zero.mpr hdet.ne'
  have hcoef : 1 / c ≤ D * (T.gram (A * A.transpose)).det :=
    one_div_pairGap_le_localFourthCost_mul_det ha4 h43 h3c (pairGap_le_one _) hdetlow
  have huR (z : Vector p) : |faceDot u z| ≤ (1 / Real.sqrt c) * fourFaceProjectionRadius A z :=
    T.pair_abs_faceDot_coordinateDual_le A hdiag hc i z
  have hvR (z : Vector p) : |faceDot v z| ≤ (1 / Real.sqrt c) * fourFaceProjectionRadius A z :=
    T.pair_abs_faceDot_coordinateDual_le A hdiag hc j z
  have hnormu : ‖projectionEuclideanVector u‖ ≤ 1 / Real.sqrt c :=
    T.pair_coordinateDual_norm_le A hdiag hc i
  have hnormv : ‖projectionEuclideanVector v‖ ≤ 1 / Real.sqrt c :=
    T.pair_coordinateDual_norm_le A hdiag hc j
  have hroots : (1 / Real.sqrt c) * (1 / Real.sqrt c) = 1 / c := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hc.le]
  have hbil : (∫ z, |faceDot v z| * |faceDot u z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      D * (T.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    have hh := s.integral_abs_bilinear_softFaceWeight_le_moment hp A T.activeFaceSet x v u
      (div_nonneg zero_le_one (Real.sqrt_nonneg _))
      (div_nonneg zero_le_one (Real.sqrt_nonneg _)) hvR huR
    rw [hroots] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcoef
      (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 2))
  have hinner : |faceDot v u| ≤ 1 / c := by
    calc
      _ ≤ ‖projectionEuclideanVector v‖ * ‖projectionEuclideanVector u‖ :=
        abs_faceDot_le_euclidean_norm _ _
      _ ≤ (1 / Real.sqrt c) * (1 / Real.sqrt c) :=
        mul_le_mul hnormv hnormu (norm_nonneg _) (by positivity)
      _ = _ := hroots
  have hconst : |faceDot v u| * (∫ z, s.softFaceWeight T.activeFaceSet
      (A.mulVec z + x) ∂standardGaussian p) ≤
      D * (T.gram (A * A.transpose)).det * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    calc
      _ ≤ (1 / c) * s.gaussianSoftFaceMoment A x T.activeFaceSet 0 := by
        simpa only [gaussianSoftFaceMoment_zero] using
          mul_le_mul_of_nonneg_right hinner (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 0)
      _ ≤ (1 / c) * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 :=
        mul_le_mul_of_nonneg_left (s.gaussianSoftFaceMoment_mono hp A x _ (by decide)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef
        (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 2)
  have htail (f : Face p) (hf : f ∈ inactiveCoordinateFaces T.activeFaceSet) :
      |normalDot f (A.mulVec v)| * (∫ z, |faceDot u z| *
        s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x) ∂standardGaussian p) +
      |normalDot f (A.mulVec u)| * |∫ z, s.softFaceDirectional (insert f T.activeFaceSet)
        (coordinateDirection (T.face j).1) (A.mulVec z + x) ∂standardGaussian p| ≤
      (4 / (c * a₃ * a₄)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
        (4 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
          (4 / (c * a₃ * a₄)) * (T.appendTwoGram f g (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0 := by
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hUinitial : U.initial = T := T.appendFace_initial f _
    have hUlast : U.face 2 = f := T.appendFace_last f _
    have hUset : U.activeFaceSet = insert f T.activeFaceSet := T.activeFaceSet_appendFace f _
    have hUj : (U.face j.castSucc).1 = (T.face j).1 := by simp [U]
    have hlin := s.integral_abs_linear_softFaceWeight_le_moment hp A (insert f T.activeFaceSet)
      x u (div_nonneg zero_le_one (Real.sqrt_nonneg _)) huR
    have hcoeflin := U.triple_initial_dualCoefficient_mul_pair_inverse_sqrt_le_det A
      hQ3 ha3 ha4 h43 hdiag hc h3c j
    rw [hUinitial, hUlast] at hcoeflin
    have hfirst : |normalDot f (A.mulVec v)| * (∫ z, |faceDot u z| *
        s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x) ∂standardGaussian p) ≤
        (2 / (c * a₃ * a₄)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 := by
      calc
        _ ≤ |normalDot f (A.mulVec v)| * ((1 / Real.sqrt c) *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1) :=
          mul_le_mul_of_nonneg_left hlin (abs_nonneg _)
        _ = (|normalDot f (A.mulVec v)| * (1 / Real.sqrt c)) *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeflin
          (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 1)
    have hsecond := s.abs_softFaceDirectional_triple_mul_initialCoefficient_le_det_moments
      hp A U hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc i j.castSucc x
    rw [hUinitial, hUlast, hUset, hUj] at hsecond
    have hUg : U.gram (A * A.transpose) = T.appendGram f (A * A.transpose) := rfl
    have hUapp (g : Face p) : U.appendGram g (A * A.transpose) =
        T.appendTwoGram f g (A * A.transpose) := rfl
    rw [hUg] at hsecond
    simp_rw [hUapp] at hsecond
    have hh := add_le_add hfirst hsecond
    apply hh.trans_eq
    change (2 / (c * a₃ * a₄)) * _ * _ + ((2 / (c * a₃ * a₄)) * _ * _ + _) = _
    ring
  have hbase := s.abs_softFaceMixedSecond_gaussian_active_coordinate_le A T.activeFaceSet
    (T.face i).1 (T.face j).1 (T.coordinate_mem_activeFaceSet i) (T.coordinate_mem_activeFaceSet j)
    x u v (T.coordinateDual_agrees_on_activeFaceSet A hd _) (T.coordinateDual_agrees_on_activeFaceSet A hd _)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_ofNat,
    show (2 : ℝ) + 1 = 3 by norm_num] at hbase
  have hsum := Finset.sum_le_sum (fun f hf => htail f hf)
  have hh := add_le_add (add_le_add hbil hconst)
    (mul_le_mul_of_nonneg_left hsum
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) s.bandwidth_pos.le))
  apply hbase.trans
  convert hh using 1
  · rw [Finset.sum_add_distrib]
    ring
  · dsimp only [D, c]
    ring

end FaceSmoother
end
end RectangleCLT
