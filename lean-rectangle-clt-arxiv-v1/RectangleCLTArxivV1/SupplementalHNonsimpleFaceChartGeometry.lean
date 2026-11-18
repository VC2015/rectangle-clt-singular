import RectangleCLTArxivV1.SupplementalHFrameSections
import RectangleCLTArxivV1.SupplementalHNormalChartIsometry
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Data.Fin.Tuple.Basic

/-! Canonical three-normal affine charts. A given orthonormal normal
frame is extended with its three rays in the last three coordinates.
Every section and norm identity is geometric, without a Gaussian-law,
surface-mass or Fubini supplier. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem nonsimpleFaceChartBasis_exists
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) :
    ∃ b : OrthonormalBasis (Fin (n+3)) ℝ (EuclideanSpace ℝ (Fin (n+3))),
      ∀ j,b (Fin.natAdd n j)=v j := by
  classical
  let w : Fin (n+3) → EuclideanSpace ℝ (Fin (n+3)) := Fin.append (fun _ : Fin n => 0) v
  let s : Set (Fin (n+3)) := Set.range (Fin.natAdd n : Fin 3 → Fin (n+3))
  have hinj : Function.Injective (Fin.natAdd n : Fin 3 → Fin (n+3)) := (Fin.natAddEmb n).injective
  have hs : Orthonormal ℝ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_,⟨i,rfl⟩⟩ ⟨_,⟨j,rfl⟩⟩
    simpa only [Set.restrict_apply,w,Fin.append_right,Subtype.mk.injEq,hinj.eq_iff] using
      (orthonormal_iff_ite.mp hv i j)
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n+3))) (ι := Fin (n+3))
    (v := w) (s := s) (by simp) hs
  refine ⟨b,?_⟩
  intro j
  simpa only [w,Fin.append_right] using hb (Fin.natAdd n j) ⟨j,rfl⟩

def nonsimpleFaceChartBasis
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) :
    OrthonormalBasis (Fin (n+3)) ℝ (EuclideanSpace ℝ (Fin (n+3))) :=
  (nonsimpleFaceChartBasis_exists v hv).choose

theorem nonsimpleFaceChartBasis_normal
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (j : Fin 3) :
    nonsimpleFaceChartBasis v hv (Fin.natAdd n j)=v j :=
  (nonsimpleFaceChartBasis_exists v hv).choose_spec j

theorem nonsimpleFaceChartBasis_normal_coordinate
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (x : EuclideanSpace ℝ (Fin (n+3))) (j : Fin 3) :
    (nonsimpleFaceChartBasis v hv).repr x (Fin.natAdd n j)=⟪v j,x⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply,nonsimpleFaceChartBasis_normal]

def nonsimpleFaceChart
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : Vector n) : Vector (n+3) :=
  gaussianRotation (nonsimpleFaceChartBasis v hv).repr.symm (Fin.append y a)

def nonsimpleFaceEuclideanChart
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+3)) :=
  (WithLp.equiv 2 (Vector (n+3))).symm
    (nonsimpleFaceChart v hv a (WithLp.equiv 2 (Vector n) y))

theorem nonsimpleFaceChart_normal_equations
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : Vector n) (j : Fin 3) :
    ⟪v j,(WithLp.equiv 2 (Vector (n+3))).symm (nonsimpleFaceChart v hv a y)⟫_ℝ=a j := by
  rw [←nonsimpleFaceChartBasis_normal_coordinate v hv]
  change (nonsimpleFaceChartBasis v hv).repr
    ((nonsimpleFaceChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+3))).symm (Fin.append y a))) (Fin.natAdd n j)=a j
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact Fin.append_right y a j

theorem nonsimpleFaceChart_range
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    Set.range (nonsimpleFaceChart v hv a)=
      {x : Vector (n+3) | ∀ j,⟪v j,(WithLp.equiv 2 (Vector (n+3))).symm x⟫_ℝ=a j} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact nonsimpleFaceChart_normal_equations v hv a y
  · intro hx
    let g : Vector (n+3) := WithLp.equiv 2 (Vector (n+3))
      ((nonsimpleFaceChartBasis v hv).repr ((WithLp.equiv 2 (Vector (n+3))).symm x))
    let y : Vector n := fun i => g (Fin.castAdd 3 i)
    have he : Fin.append y a=g := by
      ext i
      induction i using Fin.addCases with
      | left i => exact Fin.append_left y a i
      | right j =>
        rw [Fin.append_right]
        exact (hx j).symm.trans (nonsimpleFaceChartBasis_normal_coordinate v hv _ j).symm
    refine ⟨y,?_⟩
    rw [nonsimpleFaceChart,he]
    change WithLp.equiv 2 (Vector (n+3))
      ((nonsimpleFaceChartBasis v hv).repr.symm
        ((nonsimpleFaceChartBasis v hv).repr ((WithLp.equiv 2 (Vector (n+3))).symm x)))=x
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact Equiv.apply_symm_apply _ _

theorem nonsimple_vectorNormSq_append (y : Vector n) (a : Vector 3) :
    vectorNormSq (Fin.append y a)=vectorNormSq y+vectorNormSq a := by
  unfold vectorNormSq
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]

theorem nonsimpleFaceChart_normSq
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : Vector n) :
    vectorNormSq (nonsimpleFaceChart v hv a y)=vectorNormSq y+∑ j,(a j)^2 := by
  rw [nonsimpleFaceChart,vectorNormSq_gaussianRotation,nonsimple_vectorNormSq_append]
  rfl

theorem nonsimpleFaceChart_normalSum_eq_rotation
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    (∑ j,a j • v j)=(nonsimpleFaceChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+3))).symm (Fin.append (0 : Vector n) a)) := by
  have h := (nonsimpleFaceChartBasis v hv).sum_repr
    ((nonsimpleFaceChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+3))).symm (Fin.append (0 : Vector n) a)))
  rw [LinearIsometryEquiv.apply_symm_apply,Fin.sum_univ_add] at h
  simpa only [WithLp.equiv_symm_pi_apply,Fin.append_left,Fin.append_right,Pi.zero_apply,zero_smul,
    Finset.sum_const_zero,zero_add,nonsimpleFaceChartBasis_normal] using h

theorem nonsimpleFaceChart_rotated_inner
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (g : Vector (n+3)) (j : Fin 3) :
    ⟪v j,(nonsimpleFaceChartBasis v hv).repr.symm
      ((WithLp.equiv 2 (Vector (n+3))).symm g)⟫_ℝ=g (Fin.natAdd n j) := by
  rw [←nonsimpleFaceChartBasis_normal_coordinate v hv,LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Actual physical affine section after the full orthogonal rotation.
Only the first n rotated coordinates remain random. -/
theorem nonsimpleFaceChart_rotated_section
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (g : Vector (n+3)) :
    WithLp.equiv 2 (Vector (n+3))
      (gaussianFrameSectionPoint v a ((nonsimpleFaceChartBasis v hv).repr.symm
        ((WithLp.equiv 2 (Vector (n+3))).symm g)))=
      nonsimpleFaceChart v hv a (fun i => g (Fin.castAdd 3 i)) := by
  let L := (nonsimpleFaceChartBasis v hv).repr.symm
  have hproj : gaussianFrameProjection v (L ((WithLp.equiv 2 (Vector (n+3))).symm g))=
      L ((WithLp.equiv 2 (Vector (n+3))).symm
        (Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)))) := by
    dsimp only [L]
    unfold gaussianFrameProjection
    simp_rw [nonsimpleFaceChart_rotated_inner]
    exact nonsimpleFaceChart_normalSum_eq_rotation v hv _
  unfold gaussianFrameSectionPoint
  rw [nonsimpleFaceChart_normalSum_eq_rotation v hv a,hproj]
  change WithLp.equiv 2 (Vector (n+3))
    (L ((WithLp.equiv 2 (Vector (n+3))).symm (Fin.append (0 : Vector n) a))+
      L ((WithLp.equiv 2 (Vector (n+3))).symm g)-
      L ((WithLp.equiv 2 (Vector (n+3))).symm
        (Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)))))=
    WithLp.equiv 2 (Vector (n+3))
      (L ((WithLp.equiv 2 (Vector (n+3))).symm
        (Fin.append (fun i => g (Fin.castAdd 3 i)) a)))
  rw [←map_add,←map_sub]
  apply congrArg (WithLp.equiv 2 (Vector (n+3)))
  apply congrArg L
  apply PiLp.ext
  intro i
  change Fin.append (0 : Vector n) a i+g i-
      Fin.append (0 : Vector n) (fun j => g (Fin.natAdd n j)) i=
    Fin.append (fun j => g (Fin.castAdd 3 j)) a i
  induction i using Fin.addCases <;> simp

theorem nonsimpleFaceChart_measurable
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    Measurable (nonsimpleFaceChart v hv a) := by
  exact (gaussianRotation (nonsimpleFaceChartBasis v hv).repr.symm).measurable.comp
    (((Fin.continuous_append n 3).comp (continuous_id.prodMk continuous_const)).measurable)

def nonsimpleFaceEuclideanAppend (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n+3)) :=
  (WithLp.equiv 2 (Vector (n+3))).symm
    (Fin.append (WithLp.equiv 2 (Vector n) y) a)

theorem nonsimpleFaceEuclideanAppend_normSq (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) :
    ‖nonsimpleFaceEuclideanAppend a y‖^2=‖y‖^2+∑ j,(a j)^2 := by
  calc
    _=vectorNormSq (Fin.append (WithLp.equiv 2 (Vector n) y) a) :=
      (vectorNormSq_eq_euclidean_norm_sq _).symm
    _=vectorNormSq (WithLp.equiv 2 (Vector n) y)+vectorNormSq a :=
      nonsimple_vectorNormSq_append _ _
    _=‖y‖^2+∑ j,(a j)^2 := by
      rw [supplementalH_vectorNormSq_equiv]
      rfl

/-- The genuine Euclidean isometry that inserts three zero normal coordinates. -/
def nonsimpleFaceTangentAppend :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+3)) where
  toFun y := nonsimpleFaceEuclideanAppend 0 y
  map_add' y z := by
    apply PiLp.ext
    intro i
    change Fin.append (WithLp.equiv 2 (Vector n) (y+z)) (0 : Vector 3) i=
      Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector 3) i+
        Fin.append (WithLp.equiv 2 (Vector n) z) (0 : Vector 3) i
    induction i using Fin.addCases <;> simp
  map_smul' c y := by
    apply PiLp.ext
    intro i
    change Fin.append (WithLp.equiv 2 (Vector n) (c • y)) (0 : Vector 3) i=
      c*Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector 3) i
    induction i using Fin.addCases <;> simp
  norm_map' y := by
    have h := nonsimpleFaceEuclideanAppend_normSq (0 : Vector 3) y
    simp only [Pi.zero_apply,zero_pow (by decide : (2 : ℕ)≠0),
      Finset.sum_const_zero,add_zero] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def nonsimpleFaceChartTangentIsometry
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+3)) :=
  (nonsimpleFaceChartBasis v hv).repr.symm.toLinearIsometry.comp nonsimpleFaceTangentAppend

/-- Actual Euclidean affine isometry onto the fixed three-normal section. -/
def nonsimpleFaceChartAffineIsometry
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    EuclideanSpace ℝ (Fin n) →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (n+3)) :=
  (AffineIsometryEquiv.vaddConst ℝ (∑ j,a j • v j)).toAffineIsometry.comp
    (nonsimpleFaceChartTangentIsometry v hv).toAffineIsometry

theorem nonsimpleFaceChartAffineIsometry_apply
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) :
    nonsimpleFaceChartAffineIsometry v hv a y=nonsimpleFaceEuclideanChart v hv a y := by
  let L := (nonsimpleFaceChartBasis v hv).repr.symm
  change L (nonsimpleFaceEuclideanAppend (0 : Vector 3) y)+(∑ j,a j • v j)=
    L (nonsimpleFaceEuclideanAppend a y)
  rw [nonsimpleFaceChart_normalSum_eq_rotation v hv a,←map_add]
  apply congrArg L
  apply PiLp.ext
  intro i
  change Fin.append (WithLp.equiv 2 (Vector n) y) (0 : Vector 3) i+
      Fin.append (0 : Vector n) a i=Fin.append (WithLp.equiv 2 (Vector n) y) a i
  induction i using Fin.addCases <;> simp

theorem nonsimpleFaceEuclideanChart_isometry
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    Isometry (nonsimpleFaceEuclideanChart v hv a) := by
  have hfun : (nonsimpleFaceChartAffineIsometry v hv a :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+3)))=
      nonsimpleFaceEuclideanChart v hv a :=
    funext (nonsimpleFaceChartAffineIsometry_apply v hv a)
  rw [←hfun]
  exact (nonsimpleFaceChartAffineIsometry v hv a).isometry

theorem nonsimpleFaceEuclideanChart_normal_equations
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) (j : Fin 3) :
    ⟪v j,nonsimpleFaceEuclideanChart v hv a y⟫_ℝ=a j :=
  nonsimpleFaceChart_normal_equations v hv a (WithLp.equiv 2 (Vector n) y) j

theorem nonsimpleFaceEuclideanChart_range
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v) (a : Vector 3) :
    Set.range (nonsimpleFaceEuclideanChart v hv a)=
      {x : EuclideanSpace ℝ (Fin (n+3)) | ∀ j,⟪v j,x⟫_ℝ=a j} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact nonsimpleFaceEuclideanChart_normal_equations v hv a y
  · intro hx
    have hraw : WithLp.equiv 2 (Vector (n+3)) x∈Set.range (nonsimpleFaceChart v hv a) := by
      rw [nonsimpleFaceChart_range]
      simpa only [Set.mem_setOf_eq,Equiv.symm_apply_apply] using hx
    obtain ⟨y,hy⟩ := hraw
    refine ⟨(WithLp.equiv 2 (Vector n)).symm y,?_⟩
    change (WithLp.equiv 2 (Vector (n+3))).symm
      (nonsimpleFaceChart v hv a (WithLp.equiv 2 (Vector n) ((WithLp.equiv 2 (Vector n)).symm y)))=x
    rw [Equiv.apply_symm_apply,hy,Equiv.symm_apply_apply]

theorem nonsimpleFaceEuclideanChart_normSq
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : EuclideanSpace ℝ (Fin n)) :
    ‖nonsimpleFaceEuclideanChart v hv a y‖^2=‖y‖^2+∑ j,(a j)^2 := by
  change ‖(nonsimpleFaceChartBasis v hv).repr.symm (nonsimpleFaceEuclideanAppend a y)‖^2=_
  rw [LinearIsometryEquiv.norm_map,nonsimpleFaceEuclideanAppend_normSq]

theorem nonsimpleFaceChart_gaussianKernel
    (v : Fin 3 → EuclideanSpace ℝ (Fin (n+3))) (hv : Orthonormal ℝ v)
    (a : Vector 3) (y : Vector n) :
    RectangleCLT.gaussianKernel (nonsimpleFaceChart v hv a y)=
      RectangleCLT.gaussianKernel y*RectangleCLT.gaussianKernel a := by
  simp only [RectangleCLT.gaussianKernel]
  rw [nonsimpleFaceChart_normSq]
  change Real.exp (-(vectorNormSq y+vectorNormSq a)/2)=
    Real.exp (-vectorNormSq y/2)*Real.exp (-vectorNormSq a/2)
  rw [show -(vectorNormSq y+vectorNormSq a)/2= -vectorNormSq y/2+-vectorNormSq a/2 by ring,
    Real.exp_add]

end
end RectangleCLTArxivV1
