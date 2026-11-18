import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Basic

/-! Actual trihedral normal-cone halfspaces and their oriented dual
normals. These are geometric constructions, not supplied conormals. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The Riesz vector of the actual basis coordinate functional. -/
def trihedralCoordinateNormal (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  (InnerProductSpace.toDual ℝ E).symm (e.coord i).toContinuousLinearMap

theorem inner_trihedralCoordinateNormal (e : Basis (Fin 3) ℝ E) (i : Fin 3) (x : E) :
    ⟪trihedralCoordinateNormal e i,x⟫_ℝ=e.repr x i := by
  exact InnerProductSpace.toDual_symm_apply

theorem trihedralCoordinateNormal_ne_zero (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    trihedralCoordinateNormal e i≠0 := by
  intro hz
  have h := inner_trihedralCoordinateNormal e i (e i)
  rw [hz,inner_zero_left] at h
  simp at h

/-- The actual inward unit conormal to the cone facet omitting e_i. -/
def trihedralInwardNormal (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  ‖trihedralCoordinateNormal e i‖⁻¹ • trihedralCoordinateNormal e i

theorem trihedralInwardNormal_norm (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    ‖trihedralInwardNormal e i‖=1 := by
  have hp := norm_pos_iff.mpr (trihedralCoordinateNormal_ne_zero e i)
  simp only [trihedralInwardNormal,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
  exact inv_mul_cancel₀ hp.ne'

theorem inner_trihedralInwardNormal (e : Basis (Fin 3) ℝ E) (i : Fin 3) (x : E) :
    ⟪trihedralInwardNormal e i,x⟫_ℝ=‖trihedralCoordinateNormal e i‖⁻¹*e.repr x i := by
  rw [trihedralInwardNormal,inner_smul_left,conj_trivial,inner_trihedralCoordinateNormal]

theorem trihedralInwardNormal_orthogonal_other (e : Basis (Fin 3) ℝ E)
    (i j : Fin 3) (hji : j≠i) : ⟪trihedralInwardNormal e i,e j⟫_ℝ=0 := by
  rw [inner_trihedralInwardNormal]
  simp [hji,Ne.symm hji]

theorem trihedralInwardNormal_positive_own (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    0<⟪trihedralInwardNormal e i,e i⟫_ℝ := by
  rw [inner_trihedralInwardNormal]
  simp only [Basis.repr_self,Finsupp.single_eq_same,mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr (trihedralCoordinateNormal_ne_zero e i))

/-- The three constructed inward normals are themselves independent. -/
theorem trihedralInwardNormal_linearIndependent (e : Basis (Fin 3) ℝ E) :
    LinearIndependent ℝ (trihedralInwardNormal e) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (fun z : E => ⟪z,e i⟫_ℝ) ha
  simp only [sum_inner,inner_smul_left,conj_trivial,inner_zero_left] at h
  have he (j : Fin 3) : ⟪trihedralInwardNormal e j,e i⟫_ℝ=
      if j=i then ‖trihedralCoordinateNormal e i‖⁻¹ else 0 := by
    rw [inner_trihedralInwardNormal]
    by_cases hji : j=i
    · subst j
      simp
    · simp [hji,Ne.symm hji]
  simp_rw [he] at h
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_pos] at h
  exact (mul_eq_zero.mp h).resolve_right
    (inv_ne_zero (norm_ne_zero_iff.mpr (trihedralCoordinateNormal_ne_zero e i)))

/-- The orientation and tangent orthogonality characterize the actual
unit conormal uniquely. -/
theorem trihedralInwardNormal_unique (e : Basis (Fin 3) ℝ E) (i : Fin 3)
    (w : E) (hw : ‖w‖=1) (hortho : ∀ j, j≠i → ⟪w,e j⟫_ℝ=0)
    (hpositive : 0<⟪w,e i⟫_ℝ) : w=trihedralInwardNormal e i := by
  classical
  have hlin (x : E) : ⟪w,x⟫_ℝ=e.repr x i*⟪w,e i⟫_ℝ := by
    calc
      _ = ⟪w,∑ j, e.repr x j • e j⟫_ℝ := by rw [e.sum_repr]
      _ = _ := by
        rw [inner_sum]
        simp only [inner_smul_right]
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hortho j hji,mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ i))
  have he : w=⟪w,e i⟫_ℝ • trihedralCoordinateNormal e i := by
    apply ext_inner_right ℝ
    intro x
    rw [inner_smul_left,conj_trivial,inner_trihedralCoordinateNormal,hlin]
    ring
  have hn := congrArg norm he
  rw [hw,norm_smul,Real.norm_eq_abs,abs_of_pos hpositive] at hn
  have hN : ‖trihedralCoordinateNormal e i‖≠0 :=
    norm_ne_zero_iff.mpr (trihedralCoordinateNormal_ne_zero e i)
  have hcoef : ⟪w,e i⟫_ℝ=‖trihedralCoordinateNormal e i‖⁻¹ := by
    rw [←one_div]
    exact (eq_div_iff hN).mpr hn.symm
  rw [he,hcoef]
  rfl

/-- The actual finitely generated trihedral cone. -/
def trihedralGeneratedCone (e : Basis (Fin 3) ℝ E) : Set E :=
  {x | ∃ a : Fin 3 → ℝ, (∀ i, 0≤a i) ∧ x=∑ i, a i • e i}

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mem_trihedralGeneratedCone_iff (e : Basis (Fin 3) ℝ E) (x : E) :
    x∈trihedralGeneratedCone e ↔ ∀ i, 0≤e.repr x i := by
  constructor
  · rintro ⟨a,ha,rfl⟩ i
    simpa [Finset.sum_apply,Finsupp.single_apply] using ha i
  · intro hx
    refine ⟨fun i => e.repr x i,hx,?_⟩
    exact (e.sum_repr x).symm

/-- The halfspace cone is proved equal to the actual positive generated
cone, with outward normals minus the constructed inward conormals. -/
theorem trihedralGeneratedCone_eq_halfspaces (e : Basis (Fin 3) ℝ E) :
    trihedralGeneratedCone e={x | ∀ i, ⟪-trihedralInwardNormal e i,x⟫_ℝ≤0} := by
  ext x
  rw [mem_trihedralGeneratedCone_iff]
  simp only [Set.mem_setOf_eq,inner_neg_left,neg_nonpos]
  apply forall_congr'
  intro i
  rw [inner_trihedralInwardNormal]
  exact (mul_nonneg_iff_of_pos_left
    (inv_pos.mpr (norm_pos_iff.mpr (trihedralCoordinateNormal_ne_zero e i)))).symm

/-- The facet is exactly the actual positive span of the remaining two
rays. Its plane and orientation are determined by the basis coordinates. -/
theorem trihedral_facet_eq_generated_other (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    {x | x∈trihedralGeneratedCone e ∧ ⟪trihedralInwardNormal e i,x⟫_ℝ=0}=
      {x | ∃ a : Fin 3 → ℝ, (∀ j, 0≤a j) ∧ a i=0 ∧
        x=∑ j∈Finset.univ.erase i, a j • e j} := by
  classical
  ext x
  constructor
  · rintro ⟨hx,hi⟩
    have hcoord : e.repr x i=0 := by
      rw [inner_trihedralInwardNormal] at hi
      exact (mul_eq_zero.mp hi).resolve_left
        (inv_ne_zero (norm_ne_zero_iff.mpr (trihedralCoordinateNormal_ne_zero e i)))
    refine ⟨fun j => e.repr x j,(mem_trihedralGeneratedCone_iff e x).mp hx,hcoord,?_⟩
    have h := e.sum_repr x
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),hcoord,zero_smul,add_zero] at h
    exact h.symm
  · rintro ⟨a,ha,hai,hx⟩
    have hxall : x=∑ j, a j • e j := by
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),hai,zero_smul,add_zero]
      exact hx
    refine ⟨⟨a,ha,hxall⟩,?_⟩
    rw [inner_trihedralInwardNormal,hxall]
    simp [hai,Finset.sum_apply,Finsupp.single_apply]

end
end RectangleCLTArxivV1
