import RectangleCLTArxivV1.SupplementalHFrameSections
import RectangleCLTArxivV1.SupplementalHNormalChartIsometry
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Data.Fin.Tuple.Basic

/-! Canonical finite-normal affine charts. A given orthonormal normal
frame is extended with all of its rays in the last coordinates.
Every section and norm identity is geometric, without a Gaussian-law,
surface-mass or Fubini supplier. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {n q : ℕ}

theorem nonsimpleFiniteFrameChartBasis_exists
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) :
    ∃ b : OrthonormalBasis (Fin (n+q)) ℝ (EuclideanSpace ℝ (Fin (n+q))),
      ∀ j,b (Fin.natAdd n j)=v j := by
  classical
  let w : Fin (n+q) → EuclideanSpace ℝ (Fin (n+q)) := Fin.append (fun _ : Fin n => 0) v
  let s : Set (Fin (n+q)) := Set.range (Fin.natAdd n : Fin q → Fin (n+q))
  have hinj : Function.Injective (Fin.natAdd n : Fin q → Fin (n+q)) := (Fin.natAddEmb n).injective
  have hs : Orthonormal ℝ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_,⟨i,rfl⟩⟩ ⟨_,⟨j,rfl⟩⟩
    simpa only [Set.restrict_apply,w,Fin.append_right,Subtype.mk.injEq,hinj.eq_iff] using
      (orthonormal_iff_ite.mp hv i j)
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n+q))) (ι := Fin (n+q))
    (v := w) (s := s) (by simp) hs
  refine ⟨b,?_⟩
  intro j
  simpa only [w,Fin.append_right] using hb (Fin.natAdd n j) ⟨j,rfl⟩

def nonsimpleFiniteFrameChartBasis
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) :
    OrthonormalBasis (Fin (n+q)) ℝ (EuclideanSpace ℝ (Fin (n+q))) :=
  (nonsimpleFiniteFrameChartBasis_exists v hv).choose

theorem nonsimpleFiniteFrameChartBasis_normal
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (j : Fin q) :
    nonsimpleFiniteFrameChartBasis v hv (Fin.natAdd n j)=v j :=
  (nonsimpleFiniteFrameChartBasis_exists v hv).choose_spec j

theorem nonsimpleFiniteFrameChartBasis_normal_coordinate
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (x : EuclideanSpace ℝ (Fin (n+q))) (j : Fin q) :
    (nonsimpleFiniteFrameChartBasis v hv).repr x (Fin.natAdd n j)=⟪v j,x⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply,nonsimpleFiniteFrameChartBasis_normal]

def nonsimpleFiniteFrameChart
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : Vector n) : Vector (n+q) :=
  gaussianRotation (nonsimpleFiniteFrameChartBasis v hv).repr.symm (Fin.append y a)

def nonsimpleFiniteFrameEuclideanChart
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+q)) :=
  (WithLp.equiv 2 (Vector (n+q))).symm
    (nonsimpleFiniteFrameChart v hv a (WithLp.equiv 2 (Vector n) y))

theorem nonsimpleFiniteFrameChart_normal_equations
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : Vector n) (j : Fin q) :
    ⟪v j,(WithLp.equiv 2 (Vector (n+q))).symm (nonsimpleFiniteFrameChart v hv a y)⟫_ℝ=a j := by
  rw [←nonsimpleFiniteFrameChartBasis_normal_coordinate v hv]
  change (nonsimpleFiniteFrameChartBasis v hv).repr
    ((nonsimpleFiniteFrameChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+q))).symm (Fin.append y a))) (Fin.natAdd n j)=a j
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact Fin.append_right y a j

theorem nonsimpleFiniteFrameChart_range
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    Set.range (nonsimpleFiniteFrameChart v hv a)=
      {x : Vector (n+q) | ∀ j,⟪v j,(WithLp.equiv 2 (Vector (n+q))).symm x⟫_ℝ=a j} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact nonsimpleFiniteFrameChart_normal_equations v hv a y
  · intro hx
    let g : Vector (n+q) := WithLp.equiv 2 (Vector (n+q))
      ((nonsimpleFiniteFrameChartBasis v hv).repr ((WithLp.equiv 2 (Vector (n+q))).symm x))
    let y : Vector n := fun i => g (Fin.castAdd q i)
    have he : Fin.append y a=g := by
      ext i
      induction i using Fin.addCases with
      | left i => exact Fin.append_left y a i
      | right j =>
        rw [Fin.append_right]
        exact (hx j).symm.trans (nonsimpleFiniteFrameChartBasis_normal_coordinate v hv _ j).symm
    refine ⟨y,?_⟩
    rw [nonsimpleFiniteFrameChart,he]
    change WithLp.equiv 2 (Vector (n+q))
      ((nonsimpleFiniteFrameChartBasis v hv).repr.symm
        ((nonsimpleFiniteFrameChartBasis v hv).repr ((WithLp.equiv 2 (Vector (n+q))).symm x)))=x
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact Equiv.apply_symm_apply _ _

theorem nonsimpleFiniteFrame_vectorNormSq_append (y : Vector n) (a : Vector q) :
    vectorNormSq (Fin.append y a)=vectorNormSq y+vectorNormSq a := by
  unfold vectorNormSq
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]

theorem nonsimpleFiniteFrameChart_normSq
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : Vector n) :
    vectorNormSq (nonsimpleFiniteFrameChart v hv a y)=vectorNormSq y+∑ j,(a j)^2 := by
  rw [nonsimpleFiniteFrameChart,vectorNormSq_gaussianRotation,nonsimpleFiniteFrame_vectorNormSq_append]
  rfl

theorem nonsimpleFiniteFrameChart_normalSum_eq_rotation
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    (∑ j,a j • v j)=(nonsimpleFiniteFrameChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+q))).symm (Fin.append (0 : Vector n) a)) := by
  have h := (nonsimpleFiniteFrameChartBasis v hv).sum_repr
    ((nonsimpleFiniteFrameChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+q))).symm (Fin.append (0 : Vector n) a)))
  rw [LinearIsometryEquiv.apply_symm_apply,Fin.sum_univ_add] at h
  simpa only [WithLp.equiv_symm_pi_apply,Fin.append_left,Fin.append_right,Pi.zero_apply,zero_smul,
    Finset.sum_const_zero,zero_add,nonsimpleFiniteFrameChartBasis_normal] using h

theorem nonsimpleFiniteFrameChart_rotated_inner
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (g : Vector (n+q)) (j : Fin q) :
    ⟪v j,(nonsimpleFiniteFrameChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+q))).symm g)⟫_ℝ=g (Fin.natAdd n j) := by
  rw [←nonsimpleFiniteFrameChartBasis_normal_coordinate v hv,LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Actual physical affine section after the full orthogonal rotation.
Only the first n rotated coordinates remain random. -/
theorem nonsimpleFiniteFrameChart_rotated_section
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (g : Vector (n+q)) :
    WithLp.equiv 2 (Vector (n+q))
      (gaussianFrameSectionPoint v a ((nonsimpleFiniteFrameChartBasis v hv).repr.symm
        ((WithLp.equiv 2 (Vector (n+q))).symm g)))=
      nonsimpleFiniteFrameChart v hv a (fun i => g (Fin.castAdd q i)) := by
  let L := (nonsimpleFiniteFrameChartBasis v hv).repr.symm
  have hproj : gaussianFrameProjection v (L ((WithLp.equiv 2 (Vector (n+q))).symm g))=
      L ((WithLp.equiv 2 (Vector (n+q))).symm
        (Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)))) := by
    dsimp only [L]
    unfold gaussianFrameProjection
    simp_rw [nonsimpleFiniteFrameChart_rotated_inner]
    exact nonsimpleFiniteFrameChart_normalSum_eq_rotation v hv _
  unfold gaussianFrameSectionPoint
  rw [nonsimpleFiniteFrameChart_normalSum_eq_rotation v hv a,hproj]
  change WithLp.equiv 2 (Vector (n+q))
    (L ((WithLp.equiv 2 (Vector (n+q))).symm (Fin.append (0 : Vector n) a))+
      L ((WithLp.equiv 2 (Vector (n+q))).symm g)-
      L ((WithLp.equiv 2 (Vector (n+q))).symm
        (Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)))))=
    WithLp.equiv 2 (Vector (n+q))
      (L ((WithLp.equiv 2 (Vector (n+q))).symm
        (Fin.append (fun i => g (Fin.castAdd q i)) a)))
  rw [←map_add,←map_sub]
  apply congrArg (WithLp.equiv 2 (Vector (n+q)))
  apply congrArg L
  apply PiLp.ext
  intro i
  change Fin.append (0 : Vector n) a i+g i-
      Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)) i=
    Fin.append (fun j => g (Fin.castAdd q j)) a i
  induction i using Fin.addCases <;> simp

theorem nonsimpleFiniteFrameChart_measurable
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    Measurable (nonsimpleFiniteFrameChart v hv a) := by
  exact (gaussianRotation (nonsimpleFiniteFrameChartBasis v hv).repr.symm).measurable.comp
    (((Fin.continuous_append n q).comp (continuous_id.prodMk continuous_const)).measurable)

def nonsimpleFiniteFrameEuclideanAppend (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n+q)) :=
  (WithLp.equiv 2 (Vector (n+q))).symm
    (Fin.append (WithLp.equiv 2 (Vector n) y) a)

theorem nonsimpleFiniteFrameEuclideanAppend_normSq (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) :
    ‖nonsimpleFiniteFrameEuclideanAppend a y‖^2=‖y‖^2+∑ j,(a j)^2 := by
  calc
    _=vectorNormSq (Fin.append (WithLp.equiv 2 (Vector n) y) a) :=
      (vectorNormSq_eq_euclidean_norm_sq _).symm
    _=vectorNormSq (WithLp.equiv 2 (Vector n) y)+vectorNormSq a :=
      nonsimpleFiniteFrame_vectorNormSq_append _ _
    _=‖y‖^2+∑ j,(a j)^2 := by
      rw [supplementalH_vectorNormSq_equiv]
      rfl

/-- The genuine Euclidean isometry that inserts q zero normal coordinates. -/
def nonsimpleFiniteFrameTangentAppend :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+q)) where
  toFun y := nonsimpleFiniteFrameEuclideanAppend 0 y
  map_add' y z := by
    apply PiLp.ext
    intro i
    change Fin.append (WithLp.equiv 2 (Vector n) (y+z)) (0 : Vector q) i=
      Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector q) i+
        Fin.append (WithLp.equiv 2 (Vector n) z) (0 : Vector q) i
    induction i using Fin.addCases <;> simp
  map_smul' c y := by
    apply PiLp.ext
    intro i
    change Fin.append (WithLp.equiv 2 (Vector n) (c • y)) (0 : Vector q) i=
      c*Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector q) i
    induction i using Fin.addCases <;> simp
  norm_map' y := by
    have h := nonsimpleFiniteFrameEuclideanAppend_normSq (0 : Vector q) y
    simp only [Pi.zero_apply,zero_pow (by decide : (2 : ℕ)≠0),
      Finset.sum_const_zero,add_zero] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def nonsimpleFiniteFrameChartTangentIsometry
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+q)) :=
  (nonsimpleFiniteFrameChartBasis v hv).repr.symm.toLinearIsometry.comp nonsimpleFiniteFrameTangentAppend

/-- Actual Euclidean affine isometry onto the fixed finite-normal section. -/
def nonsimpleFiniteFrameChartAffineIsometry
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    EuclideanSpace ℝ (Fin n) →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (n+q)) :=
  (AffineIsometryEquiv.vaddConst ℝ (∑ j,a j • v j)).toAffineIsometry.comp
    (nonsimpleFiniteFrameChartTangentIsometry v hv).toAffineIsometry

theorem nonsimpleFiniteFrameChartAffineIsometry_apply
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) :
    nonsimpleFiniteFrameChartAffineIsometry v hv a y=nonsimpleFiniteFrameEuclideanChart v hv a y := by
  let L := (nonsimpleFiniteFrameChartBasis v hv).repr.symm
  change L (nonsimpleFiniteFrameEuclideanAppend (0 : Vector q) y)+(∑ j,a j • v j)=
    L (nonsimpleFiniteFrameEuclideanAppend a y)
  rw [nonsimpleFiniteFrameChart_normalSum_eq_rotation v hv a,←map_add]
  apply congrArg L
  apply PiLp.ext
  intro i
  change Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector q) i+
      Fin.append (0 : Vector n) a i=Fin.append (WithLp.equiv 2 (Vector n) y) a i
  induction i using Fin.addCases <;> simp

theorem nonsimpleFiniteFrameEuclideanChart_isometry
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    Isometry (nonsimpleFiniteFrameEuclideanChart v hv a) := by
  have hfun : (nonsimpleFiniteFrameChartAffineIsometry v hv a :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+q)))=
      nonsimpleFiniteFrameEuclideanChart v hv a :=
    funext (nonsimpleFiniteFrameChartAffineIsometry_apply v hv a)
  rw [←hfun]
  exact (nonsimpleFiniteFrameChartAffineIsometry v hv a).isometry

theorem nonsimpleFiniteFrameEuclideanChart_normal_equations
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) (j : Fin q) :
    ⟪v j,nonsimpleFiniteFrameEuclideanChart v hv a y⟫_ℝ=a j :=
  nonsimpleFiniteFrameChart_normal_equations v hv a (WithLp.equiv 2 (Vector n) y) j

theorem nonsimpleFiniteFrameEuclideanChart_range
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v) (a : Vector q) :
    Set.range (nonsimpleFiniteFrameEuclideanChart v hv a)=
      {x : EuclideanSpace ℝ (Fin (n+q)) | ∀ j,⟪v j,x⟫_ℝ=a j} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact nonsimpleFiniteFrameEuclideanChart_normal_equations v hv a y
  · intro hx
    have hraw : WithLp.equiv 2 (Vector (n+q)) x∈Set.range (nonsimpleFiniteFrameChart v hv a) := by
      rw [nonsimpleFiniteFrameChart_range]
      simpa only [Set.mem_setOf_eq,Equiv.symm_apply_apply] using hx
    obtain ⟨y,hy⟩ := hraw
    refine ⟨(WithLp.equiv 2 (Vector n)).symm y,?_⟩
    change (WithLp.equiv 2 (Vector (n+q))).symm
      (nonsimpleFiniteFrameChart v hv a (WithLp.equiv 2 (Vector n) ((WithLp.equiv 2 (Vector n)).symm y)))=x
    rw [Equiv.apply_symm_apply,hy,Equiv.symm_apply_apply]

theorem nonsimpleFiniteFrameEuclideanChart_normSq
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : EuclideanSpace ℝ (Fin n)) :
    ‖nonsimpleFiniteFrameEuclideanChart v hv a y‖^2=‖y‖^2+∑ j,(a j)^2 := by
  change ‖(nonsimpleFiniteFrameChartBasis v hv).repr.symm (nonsimpleFiniteFrameEuclideanAppend a y)‖^2=_
  rw [LinearIsometryEquiv.norm_map,nonsimpleFiniteFrameEuclideanAppend_normSq]

theorem nonsimpleFiniteFrameChart_gaussianKernel
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : Vector n) :
    RectangleCLT.gaussianKernel (nonsimpleFiniteFrameChart v hv a y)=
      RectangleCLT.gaussianKernel y*RectangleCLT.gaussianKernel a := by
  simp only [RectangleCLT.gaussianKernel]
  rw [nonsimpleFiniteFrameChart_normSq]
  change Real.exp (-(vectorNormSq y+vectorNormSq a)/2)=
    Real.exp (-vectorNormSq y/2)*Real.exp (-vectorNormSq a/2)
  rw [show -(vectorNormSq y+vectorNormSq a)/2= -vectorNormSq y/2+-vectorNormSq a/2 by ring,
    Real.exp_add]

end
end RectangleCLTArxivV1
