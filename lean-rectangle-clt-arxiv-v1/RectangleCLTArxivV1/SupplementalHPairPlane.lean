import RectangleCLTArxivV1.SupplementalHLineReference
import RectangleCLTArxivV1.SupplementalHPairProjectionLaw

/-! The actual rank-two projection for the two original unit normals.
No covariance inverse or ambient rank condition is used. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHPairPlane {r : ℕ} (u v : Vector r) : Matrix (Fin r) (Fin r) ℝ :=
  rankOne u+rankOne (hReferencePairComplement u v)

theorem supplementalH_pair_rankOne_cross_zero {r : ℕ} (u e : Vector r) (he : faceDot u e=0) :
    rankOne u*rankOne e=0 := by
  ext j k
  change (∑ l, (u j*u l)*(e l*e k))=0
  calc
    _ = (u j*e k)*faceDot u e := by
      unfold faceDot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [he,mul_zero]

theorem supplementalHPairPlane_transpose {r : ℕ} (u v : Vector r) :
    (supplementalHPairPlane u v).transpose=supplementalHPairPlane u v := by
  rw [supplementalHPairPlane,Matrix.transpose_add,
    supplementalH_rankOne_transpose,supplementalH_rankOne_transpose]

theorem supplementalHPairPlane_idempotent {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    supplementalHPairPlane u v*supplementalHPairPlane u v=supplementalHPairPlane u v := by
  have he := hReferencePairComplement_unit u v hu hv hρ
  have ho := hReferencePairComplement_orthogonal u v hu
  have hor : faceDot (hReferencePairComplement u v) u=0 := by rw [faceDot_comm]; exact ho
  unfold supplementalHPairPlane
  rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
    supplementalH_rankOne_idempotent u hu,supplementalH_rankOne_idempotent _ he,
    supplementalH_pair_rankOne_cross_zero _ _ ho,supplementalH_pair_rankOne_cross_zero _ _ hor]
  simp

private theorem pairPlane_faceDot_add_right {r : ℕ} (u x y : Vector r) :
    faceDot u (x+y)=faceDot u x+faceDot u y := by
  unfold faceDot
  simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem supplementalHPairPlane_first_coordinate {r : ℕ} (u v g : Vector r)
    (hu : vectorNormSq u=1) : faceDot u ((supplementalHPairPlane u v).mulVec g)=faceDot u g := by
  rw [supplementalHPairPlane,Matrix.add_mulVec,pairPlane_faceDot_add_right,
    supplementalH_rankOne_coordinate u g hu,supplementalH_rankOne_mulVec,
    threshold_faceDot_smul_right,hReferencePairComplement_orthogonal u v hu,mul_zero,add_zero]

theorem supplementalHPairPlane_complement_coordinate {r : ℕ} (u v g : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    faceDot (hReferencePairComplement u v) ((supplementalHPairPlane u v).mulVec g)=
      faceDot (hReferencePairComplement u v) g := by
  have ho : faceDot (hReferencePairComplement u v) u=0 := by
    rw [faceDot_comm]
    exact hReferencePairComplement_orthogonal u v hu
  rw [supplementalHPairPlane,Matrix.add_mulVec,pairPlane_faceDot_add_right,
    supplementalH_rankOne_coordinate _ g (hReferencePairComplement_unit u v hu hv hρ),
    supplementalH_rankOne_mulVec,threshold_faceDot_smul_right,ho,mul_zero,zero_add]

theorem supplementalHPairPlane_second_coordinate {r : ℕ} (u v g : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    faceDot v ((supplementalHPairPlane u v).mulVec g)=faceDot v g := by
  have he (z : Vector r) : faceDot v z=faceDot u v*faceDot u z+
      Real.sqrt (1-(faceDot u v)^2)*faceDot (hReferencePairComplement u v) z := by
    have h := congrArg (fun w => faceDot w z) (hReferencePairComplement_reconstruct u v hρ)
    simpa only [gaussianPair_faceDot_add_left,threshold_faceDot_smul_left] using h
  rw [he,he g,supplementalHPairPlane_first_coordinate u v g hu,
    supplementalHPairPlane_complement_coordinate u v g hu hv hρ]

theorem supplementalHPairPlane_normSq {r : ℕ} (u v g : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    vectorNormSq ((supplementalHPairPlane u v).mulVec g)=
      (faceDot u g)^2+(faceDot (hReferencePairComplement u v) g)^2 := by
  let e := hReferencePairComplement u v
  have he := hReferencePairComplement_unit u v hu hv hρ
  have ho := hReferencePairComplement_orthogonal u v hu
  rw [supplementalHPairPlane,Matrix.add_mulVec,supplementalH_rankOne_mulVec,
    supplementalH_rankOne_mulVec]
  have hform (a b : ℝ) : vectorNormSq (a • u+b • e)=
      a^2*vectorNormSq u+b^2*vectorNormSq e+2*a*b*faceDot u e := by
      unfold vectorNormSq faceDot
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hform,hu,he,ho]
  ring

end
end RectangleCLTArxivV1
