import RectangleCLT.GaussianThirdMajorant
import RectangleCLT.FourthCoefficientScales

/-! Triple directional and distinct quadruple terms for the actual fourth
Gaussian derivative. Sparse Schur factors retain the cost `c * a3 * a4`. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

set_option autoImplicit false

namespace CompatibleFaceTuple

variable {p : ℕ}

/-- A local three-coordinate Rayleigh bound preserves the separate pair gap. -/
theorem triple_det_lower_of_local (T : CompatibleFaceTuple p 3)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    pairGap (A * A.transpose) * a₃ ≤ (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hpair := T.initial.gram_two_det_ge_pairGap hsym hdiag hc.le
  have hpd : 0 < ((T.gram (A * A.transpose)).submatrix Fin.castSucc Fin.castSucc).det := by
    simpa only [← T.initial_gram (A * A.transpose)] using hc.trans_le hpair
  have hstep := det_succ_ge_mul_leading_det (T.gram (A * A.transpose)) ha3.le
    (T.gram_symmetric hsym) hpd (T.gram_lower hQ3)
  have hh := (mul_le_mul_of_nonneg_left hpair ha3.le).trans hstep
  simpa only [mul_comm, initial_gram] using hh

/-- A further sparse Schur step gives the exact four-coordinate product. -/
theorem quadruple_det_lower_of_local (T : CompatibleFaceTuple p 4)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    pairGap (A * A.transpose) * a₃ * a₄ ≤ (T.gram (A * A.transpose)).det := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have htriple := T.initial.triple_det_lower_of_local A hQ3 ha3 hdiag hc
  have htd : 0 < ((T.gram (A * A.transpose)).submatrix Fin.castSucc Fin.castSucc).det := by
    simpa only [← T.initial_gram (A * A.transpose)] using (mul_pos hc ha3).trans_le htriple
  have hstep := det_succ_ge_mul_leading_det (T.gram (A * A.transpose)) ha4.le
    (T.gram_symmetric hsym) htd (T.gram_lower hQ4)
  have hh := (mul_le_mul_of_nonneg_left htriple ha4.le).trans hstep
  simpa only [initial_gram, mul_comm, mul_left_comm, mul_assoc] using hh

/-- The distinct-four-face term is absorbed with no additional spectral loss. -/
theorem one_le_localFourthCost_mul_quadruple_det (T : CompatibleFaceTuple p 4)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    1 ≤ (1 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det := by
  have hd := T.quadruple_det_lower_of_local A hQ3 ha3 hQ4 ha4 hdiag hc
  have hh : (1 : ℝ) ≤ (T.gram (A * A.transpose)).det /
      (pairGap (A * A.transpose) * a₃ * a₄) :=
    (le_div_iff₀ (mul_pos (mul_pos hc ha3) ha4)).mpr (by simpa only [one_mul] using hd)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh

end CompatibleFaceTuple

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- Actual triple directional derivative bound, without a preceding
regression coefficient. New-face factors are absorbed by the refined Schur step. -/
theorem abs_softFaceDirectional_triple_le_det_moments
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 3)
    {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (j : Fin 3) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face j).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤
      (1 / (pairGap (A * A.transpose) * a₃ * a₄)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (4 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        (2 / (pairGap (A * A.transpose) * a₃ * a₄)) *
          (T.appendGram f (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  classical
  let c := pairGap (A * A.transpose)
  let D := 1 / (c * a₃ * a₄)
  let u := T.coordinateDual A (T.face j).1
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ3 ha3 hsym
  have hd := isUnit_iff_ne_zero.mpr hdet.ne'
  have hdetlow := T.triple_det_lower_of_local A hQ3 ha3 hdiag hc
  have hcost : 0 < c * a₃ * a₄ := mul_pos (mul_pos hc ha3) ha4
  have hD : 0 ≤ D := (one_div_pos.mpr hcost).le
  have hmaincoef : 1 / Real.sqrt a₃ ≤ D * (T.gram (A * A.transpose)).det := by
    calc
      _ = (1 / (c * a₃ * Real.sqrt a₃)) * (c * a₃) := by
        field_simp [ne_of_gt hc, ne_of_gt ha3]
      _ ≤ D * (c * a₃) := mul_le_mul_of_nonneg_right
        (one_div_sqrt_localThird_cost_le_localFourthCost ha4 h43 h3c (pairGap_le_one _))
        (mul_nonneg hc.le ha3.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hdetlow hD
  have hbase := s.abs_softFaceDirectional_gaussian_active_coordinate_le A T.activeFaceSet
    (T.face j).1 (T.coordinate_mem_activeFaceSet j) x u
    (T.coordinateDual_agrees_on_activeFaceSet A hd _)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_ofNat,
    show (3 : ℝ) + 1 = 4 by norm_num] at hbase
  simp only [← gaussianSoftFaceMoment_zero] at hbase
  have hlin := s.integral_abs_linear_softFaceWeight_le_moment hp A T.activeFaceSet x u
    (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (T.abs_faceDot_coordinateDual_le_inv_sqrt A hd ha3 (T.gram_lower hQ3)
      (by decide) (by decide) j)
  have hmain := hlin.trans (mul_le_mul_of_nonneg_right hmaincoef
    (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 1))
  have hsum :
      (∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        |normalDot f (A.mulVec u)| * s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0) ≤
      ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        (2 / (c * a₃ * a₄)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
    apply Finset.sum_le_sum
    intro f hf
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hquad := U.gram_det_pos hQ4 ha4 hsym
    have hreg := U.initial_regression_weight_div_det_le A hQ4 ha4
    have hi : U.initial = T := T.appendFace_initial f _
    have hf' : U.face (Fin.last 3) = f := T.appendFace_last f _
    rw [hi, hf'] at hreg
    have hreg' := (div_le_iff₀ hquad).mp hreg
    have hden : c * a₃ * a₄ ≤ a₄ * (T.gram (A * A.transpose)).det := by
      have hh := mul_le_mul_of_nonneg_left hdetlow ha4.le
      dsimp only [c]
      nlinarith
    have hratio : 2 / (a₄ * (T.gram (A * A.transpose)).det) ≤ 2 / (c * a₃ * a₄) :=
      div_le_div_of_nonneg_left (by norm_num) hcost hden
    have hcoef : |normalDot f (A.mulVec u)| ≤
        (2 / (c * a₃ * a₄)) * (U.gram (A * A.transpose)).det := by
      calc
        _ ≤ Real.sqrt (vectorNormSq (T.regressionCoefficients A f)) :=
          T.abs_coordinateDual_newFace_coefficient_le A j f
        _ ≤ 1 + Real.sqrt (vectorNormSq (T.regressionCoefficients A f)) := by linarith
        _ ≤ _ := hreg'
        _ ≤ _ := mul_le_mul_of_nonneg_right hratio hquad.le
    have hUg : U.gram (A * A.transpose) = T.appendGram f (A * A.transpose) := rfl
    rw [hUg] at hcoef
    exact mul_le_mul_of_nonneg_right hcoef
      (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 0)
  simpa only [D, c] using
    hbase.trans (add_le_add hmain (mul_le_mul_of_nonneg_left hsum
      (div_nonneg (by norm_num) s.bandwidth_pos.le)))

end FaceSmoother

end

end RectangleCLT
