import RectangleCLTArxivV1.SupplementalGSmallAngle
import RectangleCLTArxivV1.SupplementalGRectangularStein
import RectangleCLT.GaussianFourthBound
import RectangleCLTCompanion.RestorationAffineIBP

/-! Exact rectangular second-Hermite transfer to the actual second
directional derivative used by the small-angle branch. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_softFaceDirectional_coordinate_sum {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (y x : Vector p) :
    s.softFaceDirectional S y x = ∑ j, s.softFaceDirectional S (coordinateDirection j) x*y j := by
  have ht := cap_softFaceDirectional_mulVec s (1 : Matrix (Fin p) (Fin p) ℝ) S y x
  simpa only [Matrix.one_mulVec,Matrix.one_apply,coordinateDirection,mul_comm] using ht

theorem cap_softFaceMixedSecond_jet {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (j k : Fin p) (x : Vector p) :
    s.softFaceMixedSecond S j k x =
      (s.softFaceDirectional S (coordinateDirection k) x/s.bandwidth)*
        ((∑ f ∈ S, normalDot f (coordinateDirection j))-((S.card:ℝ)+1)*(s.weights x).v j)-
      (s.softFaceWeight S x/s.bandwidth)*((S.card:ℝ)+1)*s.potentialCoordinateHessian x j k := by
  rw [s.potentialCoordinateHessian_eq]
  unfold FaceWeights.covarianceEntry
  unfold softFaceMixedSecond softFaceDirectional
  rw [directionalMean_coordinate]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem cap_softFaceMixedSecond_row {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (j : Fin p) (y x : Vector p) :
    (∑ k, s.softFaceMixedSecond S j k x*y k) =
      (s.softFaceDirectional S y x/s.bandwidth)*
        ((∑ f ∈ S, normalDot f (coordinateDirection j))-((S.card:ℝ)+1)*(s.weights x).v j)-
      (s.softFaceWeight S x/s.bandwidth)*((S.card:ℝ)+1)*
        (∑ k, y k*s.potentialCoordinateHessian x j k) := by
  simp_rw [cap_softFaceMixedSecond_jet,sub_mul]
  rw [Finset.sum_sub_distrib,cap_softFaceDirectional_coordinate_sum]
  congr 1
  · rw [Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Ordinary directional derivatives of the coordinate gradient of the
positive soft-face weight. These are the actual jets used by Gaussian Stein. -/
theorem cap_hasDerivAt_softFaceDirectional_coordinate_line {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (x y : Vector p) (j : Fin p) :
    HasDerivAt (fun t => s.softFaceDirectional S (coordinateDirection j) (line x y t))
      (∑ k, s.softFaceMixedSecond S j k x*y k) 0 := by
  have hW := (s.hasDerivAt_softFaceWeight_line S x y 0).div_const s.bandwidth
  have hV := (s.hasDerivAt_v_line_hessian x y j).const_mul ((S.card:ℝ)+1)
  have hd := hW.mul ((hasDerivAt_const 0 (∑ f ∈ S, normalDot f (coordinateDirection j))).sub hV)
  convert hd using 1
  · funext t
    simp only [softFaceDirectional,directionalMean_coordinate,v]
    rfl
  · simp only [line_zero,zero_smul,add_zero,v]
    rw [cap_softFaceMixedSecond_row]
    unfold softFaceDirectional
    ring

/-- The archived coordinate Hessian is the exact actual second directional
derivative, including mixed-coordinate terms. -/
theorem cap_softFaceMixedSecond_quadratic {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (x y : Vector p) :
    matrixQuadratic (fun j k => s.softFaceMixedSecond S j k x) y = capSoftFaceSecond s S y x := by
  have hd := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
    (cap_hasDerivAt_softFaceDirectional_coordinate_line s S x y j).mul_const (y j))
  have hefun : (fun t => ∑ j, s.softFaceDirectional S (coordinateDirection j) (line x y t)*y j) =
      (fun t => s.softFaceDirectional S y (line x y t)) := by
    funext t
    exact (cap_softFaceDirectional_coordinate_sum s S y _).symm
  rw [hefun] at hd
  have hsecond := capSoftFaceSecond_is_derivative s S x y 0
  simp only [line_zero] at hsecond
  have he := hd.unique hsecond
  calc
    _ = ∑ j, (∑ k, s.softFaceMixedSecond S j k x*y k)*y j := by
      simp only [matrixQuadratic,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := he

/-- The actual second Gaussian integration by parts for a rectangular
factor and arbitrary positive soft-face kernel. -/
theorem cap_secondHermite_softFace_transfer {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (S : Finset (Face p)) (x : Vector p) (Z : Vector r) :
    (∫ g, repeatedDirectionScore g Z*s.softFaceWeight S (A.mulVec g+x) ∂standardGaussian r) =
      ∫ g, capSoftFaceSecond s S (A.mulVec Z) (A.mulVec g+x) ∂standardGaussian r := by
  have ht := restorationAffine_second_stein A x (s.softFaceWeight S)
    (fun a j => s.softFaceDirectional S (coordinateDirection j) a)
    (fun a j k => s.softFaceMixedSecond S j k a)
    (fun a y => by
      rw [← cap_softFaceDirectional_coordinate_sum]
      simpa only [line_zero] using s.hasDerivAt_softFaceWeight_line S a y 0)
    (fun a y j => cap_hasDerivAt_softFaceDirectional_coordinate_line s S a y j)
    (s.continuous_softFaceWeight S).measurable
    (fun j => (s.continuous_softFaceDirectional S _).measurable)
    (fun j k => (s.continuous_softFaceMixedSecond S j k).measurable)
    ⟨1,fun a => by rw [abs_of_nonneg (s.softFaceWeight_nonneg S a)]; exact s.softFaceWeight_le_one S a⟩
    (fun j => ⟨_,fun a => s.abs_softFaceDirectional_le S (coordinateDirection j) a⟩)
    (fun j k => by
      obtain ⟨C,hC⟩ := s.softFaceMixedSecond_bounded S j k
      exact ⟨C,fun a => by simpa only [Real.norm_eq_abs] using hC a⟩) Z
  simpa only [cap_softFaceMixedSecond_quadratic] using ht

theorem capSoftFaceSecond_smul {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (c : ℝ) (y x : Vector p) :
    capSoftFaceSecond s S (c • y) x = c^2*capSoftFaceSecond s S y x := by
  rw [← cap_softFaceMixedSecond_quadratic,restoration_matrixQuadratic_smul,
    cap_softFaceMixedSecond_quadratic]

/-- The exact σ² factor cancels the inverse Gaussian variance in the
fourth-tensor pair term. No inverse or full-rank assumption is needed. -/
theorem cap_secondHermite_pair_transfer_scaled {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (Z : Vector r)
    (f g : Face p) (hfg : f ≠ g) (σ : ℝ) :
    (∫ z, repeatedDirectionScore z Z*selectorTupleWeight s ![f,g] ((σ • A).mulVec z+x)
      ∂standardGaussian r) = σ^2*(∫ z,
        capSoftFaceSecond s {f,g} (A.mulVec Z) ((σ • A).mulVec z+x) ∂standardGaussian r) := by
  have ht := cap_secondHermite_softFace_transfer s (σ • A) {f,g} x Z
  simp_rw [cap_softFaceWeight_pair_eq s f g hfg,Matrix.smul_mulVec_assoc,
    capSoftFaceSecond_smul,integral_const_mul] at ht
  simpa only [Matrix.smul_mulVec_assoc] using ht

end
end RectangleCLTArxivV1
