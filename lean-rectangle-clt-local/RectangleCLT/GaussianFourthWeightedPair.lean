import RectangleCLT.GaussianThirdMajorant

/-! A linearly weighted actual pair-face derivative bound. The coefficient
is absorbed using the final three-face Gram determinant, before summation. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem abs_weighted_softFaceDirectional_pair_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 2)
    {a : ℝ} (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose))
    (i : Fin 2) (x v : Vector p)
    (hv : ∀ z, |faceDot v z| ≤ fourFaceProjectionRadius A z)
    (hvnorm : ‖projectionEuclideanVector v‖ ≤ 1) :
    |∫ z, faceDot v z * s.softFaceDirectional T.activeFaceSet
      (coordinateDirection (T.face i).1) (A.mulVec z + x) ∂standardGaussian p| ≤
      (2 / (pairGap (A * A.transpose) * a)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
      (3 / s.bandwidth) *
        ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          (2 / (a * pairGap (A * A.transpose))) *
            (T.appendGram f (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 := by
  classical
  let c := pairGap (A * A.transpose)
  let u := T.coordinateDual A (T.face i).1
  let C := 1 / Real.sqrt c
  have hC : 0 ≤ C := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hu (z : Vector p) : |faceDot u z| ≤ C * fourFaceProjectionRadius A z :=
    T.pair_abs_faceDot_coordinateDual_le A hdiag hc i z
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet : 0 < (T.gram (A * A.transpose)).det :=
    hc.trans_le (T.gram_two_det_ge_pairGap hsym hdiag hc.le)
  have hd : IsUnit (T.gram (A * A.transpose)).det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hinner : |faceDot u v| ≤ C := by
    have heq : faceDot u v =
        ⟪projectionEuclideanVector u, projectionEuclideanVector v⟫_ℝ := by
      simp [faceDot, projectionEuclideanVector, PiLp.inner_apply, mul_comm]
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul
      (T.pair_coordinateDual_norm_le A hdiag hc i) hvnorm
      (norm_nonneg _) hC).trans_eq (mul_one _))
  have hbil : (∫ z, |faceDot u z| * |faceDot v z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      C * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    rw [gaussianSoftFaceMoment, ← integral_const_mul]
    apply integral_mono
    · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg T.activeFaceSet _)] using
        (s.integrable_bilinear_softFaceWeight_gaussian A T.activeFaceSet x u v).abs
    · exact (s.integrable_gaussianSoftFaceMoment hp A x T.activeFaceSet 2).const_mul C
    · intro z
      dsimp only
      have hR := fourFaceProjectionRadius_nonneg A z
      calc
        _ ≤ (C * fourFaceProjectionRadius A z) * fourFaceProjectionRadius A z *
            s.softFaceWeight T.activeFaceSet (A.mulVec z + x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hu z) (hv z) (abs_nonneg _)
            (mul_nonneg hC hR)) (s.softFaceWeight_nonneg _ _)
        _ ≤ C * ((1 + fourFaceProjectionRadius A z) ^ 2 *
            s.softFaceWeight T.activeFaceSet (A.mulVec z + x)) := by
          have hh : (fourFaceProjectionRadius A z) ^ 2 ≤
              (1 + fourFaceProjectionRadius A z) ^ 2 := by nlinarith
          have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC)
            (s.softFaceWeight_nonneg T.activeFaceSet (A.mulVec z + x))
          convert hm using 1 <;> ring
  have hconst : |faceDot u v| *
      (∫ z, s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      C * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    apply (mul_le_mul_of_nonneg_right hinner
      (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply integral_mono (s.integrable_softFaceWeight_gaussian A T.activeFaceSet x)
      (s.integrable_gaussianSoftFaceMoment hp A x T.activeFaceSet 2)
    intro z
    dsimp only
    apply le_mul_of_one_le_left (s.softFaceWeight_nonneg T.activeFaceSet _)
    nlinarith [fourFaceProjectionRadius_nonneg A z,
      sq_nonneg (fourFaceProjectionRadius A z)]
  have hbase := s.abs_softFaceDirectional_gaussian_weighted_active_coordinate_le A
    T.activeFaceSet (T.face i).1 (T.coordinate_mem_activeFaceSet i) x u v
    (T.coordinateDual_agrees_on_activeFaceSet A hd (T.face i).1)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_ofNat,
    show (2 : ℝ) + 1 = 3 by norm_num] at hbase
  apply hbase.trans
  apply add_le_add
  · have hcoef := (div_le_iff₀ hdet).mp
      (T.pair_inverse_sqrt_weight_div_det_le A hdiag hc ha hac)
    calc
      _ ≤ 2 * C * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by linarith
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef
          (by norm_num : (0 : ℝ) ≤ 2)) (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 2)
        convert hm using 1
        ring
  · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
    apply Finset.sum_le_sum
    intro f hf
    have hlin := s.integral_abs_linear_softFaceWeight_le_moment hp A
      (insert f T.activeFaceSet) x v zero_le_one (fun z => by simpa using hv z)
    simp only [one_mul] at hlin
    apply (mul_le_mul_of_nonneg_left hlin (abs_nonneg _)).trans
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hUdet : 0 < (U.gram (A * A.transpose)).det := U.gram_det_pos hQ ha hsym
    have hcoef := U.triple_initial_dualCoefficient_weight_div_det_le A hQ ha hdiag hc i
    have hsame : U.initial = T := T.appendFace_initial f _
    have hlast : U.face 2 = f := T.appendFace_last f _
    rw [hsame, hlast] at hcoef
    have habs := (div_le_iff₀ hUdet).mp hcoef
    apply mul_le_mul_of_nonneg_right _
      (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 1)
    change |normalDot f (A.mulVec u)| ≤
      (2 / (a * c)) * (U.gram (A * A.transpose)).det
    exact (le_add_of_nonneg_left zero_le_one).trans habs

end
end RectangleCLT.FaceSmoother
