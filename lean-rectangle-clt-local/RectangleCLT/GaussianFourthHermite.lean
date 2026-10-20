import RectangleCLT.GaussianFourthMajorant
import RectangleCLT.GaussianFourthWeightedPair

/-! The third Gaussian Hermite step for a singleton active face, including
all pair, triple and quadruple correction kernels. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.FaceSmoother

noncomputable section

set_option maxRecDepth 2048

variable {p : ℕ} (s : FaceSmoother p)

private theorem hermite_algebra {ι : Type*} (S : Finset ι) (C V J₁ J₃ : ℝ)
    (b Q M W D : ι → ℝ) :
    (((J₃ - V * J₁ - V * J₁ + C * ∑ f ∈ S, b f * Q f) -
      V * (J₁ + C * ∑ f ∈ S, b f * M f)) + C * ∑ f ∈ S, b f * W f) +
      C * ∑ f ∈ S, b f * D f =
      J₃ - 3 * V * J₁ + C * ∑ f ∈ S, b f * (Q f - V * M f + W f + D f) := by
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  ring

private theorem pair_tail_algebra {ι : Type*} (S : Finset ι) (C K M : ℝ)
    (G H : ι → ℝ) :
    (2 / K) * M + ((2 / K) * M + C * ∑ f ∈ S, (2 / K) * G f) +
      ((2 / K) * M + C * ∑ f ∈ S, ((4 / K) * G f + H f)) =
      (6 / K) * M + C * ∑ f ∈ S, ((6 / K) * G f + H f) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem softFaceCoordinateThird_gaussian_hermite_recursion
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * (faceDot u z * (faceDot u z *
        s.softFaceWeight S (A.mulVec z + x))) ∂standardGaussian p) -
      3 * faceDot u u * (∫ z, faceDot u z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          ((∫ z, faceDot u z * (faceDot u z *
              s.softFaceWeight (insert f S) (A.mulVec z + x)) ∂standardGaussian p) -
            faceDot u u * (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x)
              ∂standardGaussian p) +
            (∫ z, faceDot u z * s.softFaceDirectional (insert f S) (coordinateDirection j)
              (A.mulVec z + x) ∂standardGaussian p) +
            (∫ z, s.softFaceCoordinateSecond (insert f S) j (A.mulVec z + x)
              ∂standardGaussian p)) := by
  rw [s.softFaceCoordinateThird_gaussian_active_coordinate A S j hj x u hu,
    s.softFaceCoordinateSecond_gaussian_linear_weighted_recursion A S j hj x u u hu,
    s.softFaceDirectional_gaussian_quadratic_active_coordinate A S j hj x u u u hu,
    s.softFaceDirectional_gaussian_active_coordinate A S j hj x u hu]
  exact hermite_algebra _ _ _ _ _ _ _ _ _ _

theorem abs_softFaceCoordinateThird_gaussian_hermite_recursion_le
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    |∫ z, s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p| ≤
      (∫ z, |faceDot u z| * (|faceDot u z| * (|faceDot u z| *
        s.softFaceWeight S (A.mulVec z + x))) ∂standardGaussian p) +
      3 * |faceDot u u| * (∫ z, |faceDot u z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          ((∫ z, |faceDot u z| * |faceDot u z| *
              s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p) +
            |faceDot u u| * (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x)
              ∂standardGaussian p) +
            |∫ z, faceDot u z * s.softFaceDirectional (insert f S) (coordinateDirection j)
              (A.mulVec z + x) ∂standardGaussian p| +
            |∫ z, s.softFaceCoordinateSecond (insert f S) j (A.mulVec z + x)
              ∂standardGaussian p|) := by
  have hC : 0 ≤ ((S.card : ℝ) + 1) / s.bandwidth :=
    div_nonneg (by positivity) s.bandwidth_pos.le
  rw [s.softFaceCoordinateThird_gaussian_hermite_recursion A S j hj x u hu]
  refine (abs_add _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
        abs_integral_le_integral_abs (f := fun z => faceDot u z * (faceDot u z *
          (faceDot u z * s.softFaceWeight S (A.mulVec z + x))))
    · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left (s.abs_integral_linear_softFaceWeight_le A S x u)
        (mul_nonneg (by norm_num) (abs_nonneg _))
  · rw [abs_mul, abs_of_nonneg hC]
    apply mul_le_mul_of_nonneg_left _ hC
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro f _
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (abs_add _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact s.abs_integral_bilinear_softFaceWeight_le A (insert f S) x u u
    · rw [abs_mul, abs_of_nonneg (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))]

theorem abs_softFaceCoordinateThird_singleton_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 1)
    {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceCoordinateThird T.activeFaceSet (T.face i).1 (A.mulVec z + x)
      ∂standardGaussian p| ≤
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
                s.gaussianSoftFaceMoment A x (insert h (insert g (insert f T.activeFaceSet))) 0)) := by
  classical
  let c := pairGap (A * A.transpose)
  let D := 1 / (c * a₃ * a₄)
  let u := T.coordinateDual A (T.face i).1
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hG : T.gram (A * A.transpose) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext j k
    have hjk : j = k := Subsingleton.elim _ _
    subst k
    simpa using T.gram_diagonal hdiag j
  have hd : IsUnit (T.gram (A * A.transpose)).det := by
    rw [hG, Matrix.det_one]
    exact isUnit_one
  have huR (z : Vector p) : |faceDot u z| ≤ fourFaceProjectionRadius A z :=
    T.singleton_abs_faceDot_coordinateDual_le A hdiag i z
  have hnormu : ‖projectionEuclideanVector u‖ ≤ 1 :=
    T.singleton_coordinateDual_norm_le_one A hdiag i
  have huu : |faceDot u u| ≤ 1 := (abs_faceDot_le_euclidean_norm u u).trans
    ((mul_le_mul hnormu hnormu (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hD1 : 1 ≤ D := one_le_localFourthCost ha4 h43 h3c (pairGap_le_one _)
  have ha41 : a₄ ≤ 1 := h43.trans (h3c.trans (pairGap_le_one _))
  have hcost : 2 / (c * a₃) ≤ 2 / (c * a₃ * a₄) := by
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (mul_pos hc ha3) ha4)
    exact (mul_le_mul_of_nonneg_left ha41 (mul_nonneg hc.le ha3.le)).trans_eq (mul_one _)
  have hquad (S : Finset (Face p)) :
      (∫ z, |faceDot u z| * |faceDot u z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) ≤ s.gaussianSoftFaceMoment A x S 2 := by
    simpa only [one_mul, mul_one] using
      s.integral_abs_bilinear_softFaceWeight_le_moment hp A S x u u zero_le_one zero_le_one
        (fun z => by simpa using huR z) (fun z => by simpa using huR z)
  have hconst (S : Finset (Face p)) :
      |faceDot u u| * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) ≤
        s.gaussianSoftFaceMoment A x S 2 := by
    calc
      _ ≤ 1 * s.gaussianSoftFaceMoment A x S 0 := by
        simpa only [gaussianSoftFaceMoment_zero] using
          mul_le_mul_of_nonneg_right huu (s.gaussianSoftFaceMoment_nonneg A x S 0)
      _ ≤ _ := by
        rw [one_mul]
        exact s.gaussianSoftFaceMoment_mono hp A x S (by decide)
  have hcube : (∫ z, |faceDot u z| * (|faceDot u z| * (|faceDot u z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x))) ∂standardGaussian p) ≤
      s.gaussianSoftFaceMoment A x T.activeFaceSet 3 := by
    apply integral_mono
    · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg T.activeFaceSet _), mul_assoc] using
        (s.integrable_trilinear_softFaceWeight_gaussian A T.activeFaceSet x u u u).abs
    · exact s.integrable_gaussianSoftFaceMoment hp A x T.activeFaceSet 3
    · intro z
      dsimp only
      calc
        _ = |faceDot u z| ^ 3 * s.softFaceWeight T.activeFaceSet (A.mulVec z + x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (by linarith [huR z]) 3) (s.softFaceWeight_nonneg _ _)
  have hlinear : 3 * |faceDot u u| * (∫ z, |faceDot u z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      3 * s.gaussianSoftFaceMoment A x T.activeFaceSet 3 := by
    have hl := s.integral_abs_linear_softFaceWeight_le_moment hp A T.activeFaceSet x u
      zero_le_one (fun z => by simpa using huR z)
    simp only [one_mul] at hl
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left huu (by norm_num : (0 : ℝ) ≤ 3))
      hl (integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (s.softFaceWeight_nonneg _ _)))
      (by norm_num : (0 : ℝ) ≤ 3 * 1)
    exact hh.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
      (s.gaussianSoftFaceMoment_mono hp A x T.activeFaceSet (by decide : 1 ≤ 3))
        (by norm_num : (0 : ℝ) ≤ 3)))
  have hmain : (∫ z, |faceDot u z| * (|faceDot u z| * (|faceDot u z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x))) ∂standardGaussian p) +
      3 * |faceDot u u| * (∫ z, |faceDot u z| * s.softFaceWeight T.activeFaceSet (A.mulVec z + x)
        ∂standardGaussian p) ≤ (4 / (c * a₃ * a₄)) * s.gaussianSoftFaceMoment A x T.activeFaceSet 3 := by
    have hh := add_le_add hcube hlinear
    have hm := mul_le_mul_of_nonneg_right hD1 (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 3)
    calc
      _ ≤ _ := hh
      _ = 4 * s.gaussianSoftFaceMoment A x T.activeFaceSet 3 := by ring
      _ ≤ 4 * (D * s.gaussianSoftFaceMoment A x T.activeFaceSet 3) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
      _ = _ := by dsimp only [D]; ring
  have htail (f : Face p) (hf : f ∈ inactiveCoordinateFaces T.activeFaceSet) :
      (∫ z, |faceDot u z| * |faceDot u z| * s.softFaceWeight (insert f T.activeFaceSet)
        (A.mulVec z + x) ∂standardGaussian p) +
        |faceDot u u| * (∫ z, s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x)
          ∂standardGaussian p) +
        |∫ z, faceDot u z * s.softFaceDirectional (insert f T.activeFaceSet)
          (coordinateDirection (T.face i).1) (A.mulVec z + x) ∂standardGaussian p| +
        |∫ z, s.softFaceCoordinateSecond (insert f T.activeFaceSet) (T.face i).1
          (A.mulVec z + x) ∂standardGaussian p| ≤
      (6 / (c * a₃ * a₄)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2 +
        (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
          ((6 / (c * a₃ * a₄)) * (T.appendTwoGram f g (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 1 +
            (4 / s.bandwidth) * ∑ h ∈ inactiveCoordinateFaces (insert g (insert f T.activeFaceSet)),
              (4 / (c * a₃ * a₄)) * (T.appendThreeGram f g h (A * A.transpose)).det *
                s.gaussianSoftFaceMoment A x (insert h (insert g (insert f T.activeFaceSet))) 0) := by
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hUset : U.activeFaceSet = insert f T.activeFaceSet := T.activeFaceSet_appendFace f _
    have hUi : (U.face i.castSucc).1 = (T.face i).1 := by simp [U]
    have hUgram : U.gram (A * A.transpose) = T.appendGram f (A * A.transpose) := rfl
    have hUapp (g : Face p) : U.appendGram g (A * A.transpose) = T.appendTwoGram f g (A * A.transpose) := rfl
    have hUapp2 (g h : Face p) : U.appendTwoGram g h (A * A.transpose) = T.appendThreeGram f g h (A * A.transpose) := rfl
    have hUdetlo := U.gram_two_det_ge_pairGap hsym hdiag hc.le
    have hUdet := hc.trans_le hUdetlo
    have hcoe := one_le_localFourthCost_mul_det ha4 h43 h3c (pairGap_le_one _) hUdetlo
    have hpairmain : (∫ z, |faceDot u z| * |faceDot u z| * s.softFaceWeight (insert f T.activeFaceSet)
        (A.mulVec z + x) ∂standardGaussian p) + |faceDot u u| *
        (∫ z, s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x) ∂standardGaussian p) ≤
        (2 / (c * a₃ * a₄)) * (U.gram (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2 := by
      have hh := add_le_add (hquad (insert f T.activeFaceSet)) (hconst (insert f T.activeFaceSet))
      have hm := mul_le_mul_of_nonneg_right hcoe
        (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 2)
      simp only [one_mul] at hm
      calc
        _ ≤ _ := hh
        _ = 2 * s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2 := by ring
        _ ≤ 2 * ((1 / (c * a₃ * a₄)) * (U.gram (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
        _ = _ := by ring
    have hw := s.abs_weighted_softFaceDirectional_pair_le_det_moments hp A U hQ3 ha3
      hdiag hc h3c i.castSucc x u huR hnormu
    have hweighted : |∫ z, faceDot u z * s.softFaceDirectional U.activeFaceSet
        (coordinateDirection (U.face i.castSucc).1) (A.mulVec z + x) ∂standardGaussian p| ≤
        (2 / (c * a₃ * a₄)) * (U.gram (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x U.activeFaceSet 2 +
        (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces U.activeFaceSet,
          (2 / (c * a₃ * a₄)) * (U.appendGram g (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert g U.activeFaceSet) 1 := by
      apply hw.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost hUdet.le)
          (s.gaussianSoftFaceMoment_nonneg A x U.activeFaceSet 2)
      · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
        apply Finset.sum_le_sum
        intro g hg
        let V := U.appendFace g (U.distinct_coordinate_of_inactive hg)
        have hVdet := V.gram_det_pos hQ3 ha3 hsym
        have hcost' : 2 / (a₃ * c) ≤ 2 / (c * a₃ * a₄) := by simpa only [mul_comm a₃ c] using hcost
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost' hVdet.le)
          (s.gaussianSoftFaceMoment_nonneg A x (insert g U.activeFaceSet) 1)
    have hs := s.abs_softFaceMixedSecond_pair_le_det_moments hp A U hQ3 ha3 hQ4 ha4
      h43 h3c hdiag hc i.castSucc i.castSucc x
    simp only [softFaceMixedSecond_diagonal] at hs
    rw [hUset, hUi] at hweighted hs
    rw [hUgram] at hpairmain hweighted hs
    simp_rw [hUapp] at hweighted hs
    simp_rw [hUapp2] at hs
    have hh := add_le_add (add_le_add hpairmain hweighted) hs
    apply hh.trans_eq
    simpa only [mul_assoc] using
      (pair_tail_algebra (inactiveCoordinateFaces (insert f T.activeFaceSet))
        (3 / s.bandwidth) (c * a₃ * a₄)
        ((T.appendGram f (A * A.transpose)).det * s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 2)
        (fun g => (T.appendTwoGram f g (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 1)
        (fun g => (4 / s.bandwidth) * ∑ h ∈ inactiveCoordinateFaces (insert g (insert f T.activeFaceSet)),
          (4 / (c * a₃ * a₄)) * (T.appendThreeGram f g h (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert h (insert g (insert f T.activeFaceSet))) 0))
  have hbase := s.abs_softFaceCoordinateThird_gaussian_hermite_recursion_le A T.activeFaceSet
    (T.face i).1 (T.coordinate_mem_activeFaceSet i) x u
    (T.coordinateDual_agrees_on_activeFaceSet A hd _)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_one,
    show (1 : ℝ) + 1 = 2 by norm_num] at hbase
  apply hbase.trans
  apply add_le_add hmain
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
  apply Finset.sum_le_sum
  intro f hf
  have hquadnon : 0 ≤ ∫ z, |faceDot u z| * |faceDot u z| *
      s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x) ∂standardGaussian p :=
    integral_nonneg (fun z => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (s.softFaceWeight_nonneg _ _))
  have hmassnon : 0 ≤ ∫ z, s.softFaceWeight (insert f T.activeFaceSet)
      (A.mulVec z + x) ∂standardGaussian p := integral_nonneg (fun z => s.softFaceWeight_nonneg _ _)
  exact (mul_le_mul_of_nonneg_right
    (T.singleton_abs_newFace_coefficient_le_one A hdiag i f)
      (by positivity)).trans (by simpa only [one_mul] using htail f hf)

end
end RectangleCLT.FaceSmoother
