import RectangleCLT.GlobalDerivativeStein
import RectangleCLT.GaussianFourthHermite
import RectangleCLT.GaussianTubeEvents

/-!
# Actual higher soft-face derivatives in full Gaussian dual directions

Full coordinate duals agree with the coordinate direction on every face,
so all inactive-face corrections in the local Gaussian recursions vanish.
The resulting Hermite identities below concern genuine integrated first,
second, mixed second, and third soft-face derivatives. They are analytic
identities, not assumed derivative caps.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem normalDot_inactive_coordinateDirection_eq_zero
    (S : Finset (Face p)) (j : Fin p) (hj : j ∈ S.image Prod.fst)
    (f : Face p) (hf : f ∈ inactiveCoordinateFaces S) :
    normalDot f (coordinateDirection j) = 0 := by
  have hnot : f.1 ∉ S.image Prod.fst := (Finset.mem_filter.mp hf).2
  have hne : f.1 ≠ j := fun h => hnot (h.symm ▸ hj)
  simp [GaussianTube.normalDot_eq_faceSign_mul, coordinateDirection, hne]

theorem sum_inactive_fullGaussianDual_eq_zero
    (S : Finset (Face p)) (j : Fin p) (hj : j ∈ S.image Prod.fst)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (F : Face p → ℝ) :
    (∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec (fullGaussianDual A j)) * F f) =
      0 := by
  apply Finset.sum_eq_zero
  intro f hf
  rw [fullGaussianDual_right_inverse A hd,
    normalDot_inactive_coordinateDirection_eq_zero S j hj f hf, zero_mul]

/-- Full Gaussian integration by parts has no inactive-face correction. -/
theorem softFaceDirectional_gaussian_fullDual
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (S : Finset (Face p)) (j : Fin p) (x : Vector p) :
    (∫ z, s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p) =
      ∫ z, faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p := by
  simpa only [fullGaussianDual_right_inverse A hd] using
    (s.softFaceWeight_gaussian_directional_stein A S x (fullGaussianDual A j)).symm

theorem softFaceDirectional_gaussian_weighted_fullDual
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (S : Finset (Face p)) (j : Fin p) (x v : Vector p) :
    (∫ z, faceDot v z * s.softFaceDirectional S (coordinateDirection j)
      (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot (fullGaussianDual A j) z * (faceDot v z *
        s.softFaceWeight S (A.mulVec z + x)) ∂standardGaussian p) -
      faceDot (fullGaussianDual A j) v *
        (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) := by
  have hh := s.softFaceWeight_gaussian_weighted_stein A S x (fullGaussianDual A j) v
  rw [fullGaussianDual_right_inverse A hd] at hh
  linarith

/-- Actual repeated second derivatives become the second Gaussian Hermite
polynomial in the full dual score. -/
theorem softFaceCoordinateSecond_gaussian_fullDual
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (S : Finset (Face p)) (j : Fin p) (hj : j ∈ S.image Prod.fst) (x : Vector p) :
    (∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot (fullGaussianDual A j) z * (faceDot (fullGaussianDual A j) z *
        s.softFaceWeight S (A.mulVec z + x)) ∂standardGaussian p) -
      faceDot (fullGaussianDual A j) (fullGaussianDual A j) *
        (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.softFaceCoordinateSecond_gaussian_active_coordinate A S j hj x
    (fullGaussianDual A j) (fun f _ => congrFun (fullGaussianDual_right_inverse A hd j) f.1)]
  rw [sum_inactive_fullGaussianDual_eq_zero S j hj A hd, mul_zero, add_zero]
  exact s.softFaceDirectional_gaussian_weighted_fullDual A hd S j x (fullGaussianDual A j)

/-- Actual mixed second derivatives retain the exact dual-score covariance
correction, without any appended-face remainder. -/
theorem softFaceMixedSecond_gaussian_fullDual
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (S : Finset (Face p)) (j k : Fin p)
    (hj : j ∈ S.image Prod.fst) (hk : k ∈ S.image Prod.fst) (x : Vector p) :
    (∫ z, s.softFaceMixedSecond S j k (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot (fullGaussianDual A k) z * (faceDot (fullGaussianDual A j) z *
        s.softFaceWeight S (A.mulVec z + x)) ∂standardGaussian p) -
      faceDot (fullGaussianDual A k) (fullGaussianDual A j) *
        (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.softFaceMixedSecond_gaussian_active_coordinate A S j k hj x
    (fullGaussianDual A j) (fun f _ => congrFun (fullGaussianDual_right_inverse A hd j) f.1)]
  rw [sum_inactive_fullGaussianDual_eq_zero S j hj A hd, mul_zero, add_zero]
  exact s.softFaceDirectional_gaussian_weighted_fullDual A hd S k x (fullGaussianDual A j)

/-- The genuine repeated third derivative has the pure third Hermite score
representation. This is the global replacement for the local recursion's
pair, triple, and quadruple appended-face corrections. -/
theorem softFaceCoordinateThird_gaussian_fullDual
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (S : Finset (Face p)) (j : Fin p) (hj : j ∈ S.image Prod.fst) (x : Vector p) :
    (∫ z, s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot (fullGaussianDual A j) z * (faceDot (fullGaussianDual A j) z *
        (faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x)))
        ∂standardGaussian p) -
      3 * faceDot (fullGaussianDual A j) (fullGaussianDual A j) *
        (∫ z, faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x)
          ∂standardGaussian p) := by
  rw [s.softFaceCoordinateThird_gaussian_hermite_recursion A S j hj x
    (fullGaussianDual A j) (fun f _ => congrFun (fullGaussianDual_right_inverse A hd j) f.1)]
  rw [sum_inactive_fullGaussianDual_eq_zero S j hj A hd, mul_zero, add_zero]

end

end RectangleCLT.FaceSmoother
