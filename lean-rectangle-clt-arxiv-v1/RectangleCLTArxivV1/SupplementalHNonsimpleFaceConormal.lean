import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry

/-! Canonical conormals of actual ridge/codimension-three incidences.
Their orientation is determined by actual relative-interior witnesses,
not a supplied sign condition. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {m : ℕ}

abbrev NonsimpleRidgeAt (u : Fin m → E) (b : Fin m → ℝ) (H : NonsimpleFaceIndex u b 3) :=
  {R : NonsimpleFaceIndex u b 2 // R.1⊆H.1}

noncomputable instance nonsimpleRidgeAtFintype (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) : Fintype (NonsimpleRidgeAt u b H) := Fintype.ofFinite _

def nonsimpleIncidentDirection (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) : E :=
  nonsimpleFaceRepresentative u b I.1-nonsimpleFaceRepresentative u b H

def nonsimpleIncidentProjection (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) : E :=
  (nonsimpleFaceNormalSpace u H.1).orthogonalProjection (nonsimpleIncidentDirection u b H I)

def nonsimpleIncidentConormal (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) : E :=
  -‖nonsimpleIncidentProjection u b H I‖⁻¹ • nonsimpleIncidentProjection u b H I

theorem nonsimpleIncidentProjection_mem (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) :
    nonsimpleIncidentProjection u b H I∈nonsimpleFaceNormalSpace u H.1 :=
  ((nonsimpleFaceNormalSpace u H.1).orthogonalProjection (nonsimpleIncidentDirection u b H I)).property

theorem nonsimpleIncidentProjection_inner (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) (j : Fin m) (hj : j∈H.1) :
    ⟪u j,nonsimpleIncidentProjection u b H I⟫_ℝ=
      ⟪u j,nonsimpleFaceRepresentative u b I.1⟫_ℝ-b j := by
  have hp : ⟪u j,nonsimpleIncidentProjection u b H I⟫_ℝ=
      ⟪u j,nonsimpleIncidentDirection u b H I⟫_ℝ :=
    (nonsimpleFaceNormalSpace u H.1).inner_orthogonalProjection_eq_of_mem_left
      ⟨u j,nonsimple_normal_mem u H.1 j hj⟩ _
  rw [hp,nonsimpleIncidentDirection,inner_sub_right,nonsimpleFaceRepresentative_levels u b H j hj]

theorem nonsimpleIncidentProjection_zero_on_ridge (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) (j : Fin m) (hj : j∈I.1.1) :
    ⟪u j,nonsimpleIncidentProjection u b H I⟫_ℝ=0 := by
  rw [nonsimpleIncidentProjection_inner u b H I j (I.2 hj),
    nonsimpleFaceRepresentative_levels u b I.1 j hj,sub_self]

theorem nonsimpleIncidentProjection_strict_on_other (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H)
    (j : Fin m) (hj : j∈H.1) (hjr : j∉I.1.1) :
    ⟪u j,nonsimpleIncidentProjection u b H I⟫_ℝ<0 := by
  rw [nonsimpleIncidentProjection_inner u b H I j hj]
  exact sub_neg.mpr (nonsimpleFaceRepresentative_strict u b I.1 j hjr)

theorem nonsimpleRidgeAt_exists_other_active (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) :
    ∃ j,j∈H.1 ∧ j∉I.1.1 := by
  classical
  by_contra hn
  have hsub : H.1⊆I.1.1 := by
    intro j hj
    by_contra hnr
    exact hn ⟨j,hj,hnr⟩
  have heq : I.1.1=H.1 := Finset.Subset.antisymm I.2 hsub
  have hr := I.1.2.2
  rw [heq,H.2.2] at hr
  norm_num at hr

theorem nonsimpleIncidentProjection_ne_zero (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) :
    nonsimpleIncidentProjection u b H I≠0 := by
  obtain ⟨j,hj,hjr⟩ := nonsimpleRidgeAt_exists_other_active u b H I
  intro he
  have hs := nonsimpleIncidentProjection_strict_on_other u b H I j hj hjr
  exact (lt_irrefl (0 : ℝ)) (by simpa only [he,inner_zero_right] using hs)

theorem nonsimpleIncidentConormal_unit (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) :
    ‖nonsimpleIncidentConormal u b H I‖=1 := by
  have hp := norm_pos_iff.mpr (nonsimpleIncidentProjection_ne_zero u b H I)
  simp only [nonsimpleIncidentConormal,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hp]
  exact inv_mul_cancel₀ hp.ne'

theorem nonsimpleIncidentConormal_mem (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) :
    nonsimpleIncidentConormal u b H I∈nonsimpleFaceNormalSpace u H.1 :=
  Submodule.smul_mem _ _ (nonsimpleIncidentProjection_mem u b H I)

theorem nonsimpleIncidentConormal_zero_on_ridge (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) (j : Fin m) (hj : j∈I.1.1) :
    ⟪nonsimpleIncidentConormal u b H I,u j⟫_ℝ=0 := by
  rw [nonsimpleIncidentConormal,inner_smul_left,conj_trivial,real_inner_comm,
    nonsimpleIncidentProjection_zero_on_ridge u b H I j hj,mul_zero]

theorem nonsimpleIncidentConormal_strict_on_other (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H)
    (j : Fin m) (hj : j∈H.1) (hjr : j∉I.1.1) :
    0<⟪nonsimpleIncidentConormal u b H I,u j⟫_ℝ := by
  rw [nonsimpleIncidentConormal,inner_smul_left,conj_trivial,real_inner_comm]
  exact mul_pos_of_neg_of_neg
    (neg_neg_of_pos (inv_pos.mpr (norm_pos_iff.mpr (nonsimpleIncidentProjection_ne_zero u b H I))))
    (nonsimpleIncidentProjection_strict_on_other u b H I j hj hjr)

theorem nonsimpleIncidentConormal_nonneg (u : Fin m → E) (b : Fin m → ℝ)
    (H : NonsimpleFaceIndex u b 3) (I : NonsimpleRidgeAt u b H) (j : Fin m) (hj : j∈H.1) :
    0≤⟪nonsimpleIncidentConormal u b H I,u j⟫_ℝ := by
  classical
  by_cases hr : j∈I.1.1
  · exact (nonsimpleIncidentConormal_zero_on_ridge u b H I j hr).ge
  · exact (nonsimpleIncidentConormal_strict_on_other u b H I j hj hr).le

end
end RectangleCLTArxivV1
