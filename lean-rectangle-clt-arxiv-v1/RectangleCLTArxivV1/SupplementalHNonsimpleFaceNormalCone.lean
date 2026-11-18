import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCone

/-! The positive hull of all active original normals is the genuine
outward normal cone of the actual polyhedron.  Local feasible rays are
constructed from the strict inactive inequalities; no generic threshold
or pre-assumed normal-cone equality is used. -/
namespace RectangleCLTArxivV1
open Set Filter RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem nonsimple_exactStratum_local_feasible_ray (u : Fin m → E) (b : Fin m → ℝ)
    (S : Finset (Fin m)) {x : E} (hx : x∈exactStratum u b S)
    (y : E) (hy : ∀ j∈S,⟪u j,y⟫_ℝ≤0) :
    ∃ t : ℝ,0<t ∧ x+t • y∈polyhedron u b := by
  classical
  have hevent : ∀ᶠ t : ℝ in 𝓝 0,∀ j,j∉S → ⟪u j,x+t • y⟫_ℝ<b j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j∈S
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hj))
    · have hgap : ⟪u j,x⟫_ℝ<b j :=
        lt_of_le_of_ne (hx.1 j) (fun he => hj ((hx.2 j).mp he))
      have hc : ContinuousAt (fun t : ℝ => ⟪u j,x+t • y⟫_ℝ) 0 := by fun_prop
      have hh : (fun t : ℝ => ⟪u j,x+t • y⟫_ℝ) 0<(fun _ : ℝ => b j) 0 := by
        simpa using hgap
      exact (hc.eventually_lt continuousAt_const hh).mono (fun _ ht _ => ht)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have ht : 0<ε/2 := half_pos hε
  have hdist : dist (ε/2) (0 : ℝ)<ε := by
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith
  refine ⟨ε/2,ht,?_⟩
  intro j
  by_cases hj : j∈S
  · rw [inner_add_right,inner_smul_right,(hx.2 j).mpr hj]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht.le (hy j hj))
  · exact (hball hdist j hj).le

theorem nonsimple_isOutwardNormal_iff_activeGeneratedCone [CompleteSpace E]
    (u : Fin m → E) (b : Fin m → ℝ) (S : Finset (Fin m))
    (hi : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) {x : E} (hx : x∈exactStratum u b S) (v : E) :
    IsOutwardNormal (polyhedron u b) x v ↔ v∈nonsimpleActiveGeneratedCone u S := by
  obtain ⟨z,hz⟩ := hi
  have hd : ∀ j∈S,⟪u j,z-x⟫_ℝ<0 := by
    intro j hj
    rw [inner_sub_right,(hx.2 j).mpr hj]
    exact sub_neg.mpr (hz j)
  constructor
  · intro hv
    apply (nonsimpleActiveGeneratedCone_mem_iff_polar u S (z-x) hd v).mpr
    intro y hy
    obtain ⟨t,ht,hfeas⟩ := nonsimple_exactStratum_local_feasible_ray u b S hx y hy
    have h := hv (x+t • y) hfeas
    have hh : t*⟪v,y⟫_ℝ≤0 := by simpa only [add_sub_cancel_left,inner_smul_right] using h
    exact (mul_le_mul_left ht).mp (by simpa using hh)
  · intro hv
    obtain ⟨c,hc,he⟩ := (nonsimpleActiveGeneratedCone_mem_iff u S v).mp hv
    rw [he]
    exact coneDisplacement_isOutward u b S hx c hc

theorem nonsimpleFace_genuine_normalCone [CompleteSpace E]
    (u : Fin m → E) (b : Fin m → ℝ)
    (hi : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) {q : ℕ} (F : NonsimpleFaceIndex u b q) :
    {v | IsOutwardNormal (polyhedron u b) (nonsimpleFaceRepresentative u b F) v}=
      (nonsimpleActiveGeneratedCone u F.1 : Set E) := by
  ext v
  exact nonsimple_isOutwardNormal_iff_activeGeneratedCone u b F.1 hi
    (nonsimpleFaceRepresentative_mem u b F) v

theorem nonsimple_generator_mem_activeCone (u : Fin m → E) (S : Finset (Fin m))
    (j : Fin m) (hj : j∈S) : u j∈nonsimpleActiveGeneratedCone u S := by
  classical
  apply (nonsimpleActiveGeneratedCone_mem_iff u S (u j)).mpr
  refine ⟨Pi.single j 1,?_,?_⟩
  · intro k _
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply,ite_smul,hj]

theorem nonsimple_generated_mem_normalSpace (u : Fin m → E) (S : Finset (Fin m))
    {v : E} (hv : v∈nonsimpleActiveGeneratedCone u S) : v∈nonsimpleFaceNormalSpace u S := by
  obtain ⟨a,ha,he⟩ := (nonsimpleActiveGeneratedCone_mem_iff u S v).mp hv
  rw [he]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (nonsimple_normal_mem u S j hj)

theorem nonsimple_activeCone_eq_of_presentation [CompleteSpace E] {k : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (v : Fin k → E) (c : Fin k → ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin k)) (x : E)
    (hiu : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) (hiv : ∃ z : E,∀ j,⟪v j,z⟫_ℝ<c j)
    (hxu : x∈exactStratum u b S) (hxv : x∈exactStratum v c T)
    (hP : polyhedron u b=polyhedron v c) :
    (nonsimpleActiveGeneratedCone u S : Set E)=(nonsimpleActiveGeneratedCone v T : Set E) := by
  ext w
  change w∈nonsimpleActiveGeneratedCone u S ↔ w∈nonsimpleActiveGeneratedCone v T
  rw [←nonsimple_isOutwardNormal_iff_activeGeneratedCone u b S hiu hxu w,
    ←nonsimple_isOutwardNormal_iff_activeGeneratedCone v c T hiv hxv w,hP]

theorem nonsimple_activeNormalSpace_eq_of_presentation [CompleteSpace E] {k : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (v : Fin k → E) (c : Fin k → ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin k)) (x : E)
    (hiu : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) (hiv : ∃ z : E,∀ j,⟪v j,z⟫_ℝ<c j)
    (hxu : x∈exactStratum u b S) (hxv : x∈exactStratum v c T)
    (hP : polyhedron u b=polyhedron v c) :
    nonsimpleFaceNormalSpace u S=nonsimpleFaceNormalSpace v T := by
  have hC := nonsimple_activeCone_eq_of_presentation u b v c S T x hiu hiv hxu hxv hP
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    apply nonsimple_generated_mem_normalSpace v T
    change u j∈(nonsimpleActiveGeneratedCone v T : Set E)
    rw [←hC]
    exact nonsimple_generator_mem_activeCone u S j hj
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    apply nonsimple_generated_mem_normalSpace u S
    change v j∈(nonsimpleActiveGeneratedCone u S : Set E)
    rw [hC]
    exact nonsimple_generator_mem_activeCone v T j hj

theorem nonsimple_active_normal_ne_zero (u : Fin m → E) (b : Fin m → ℝ)
    (hi : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) (S : Finset (Fin m)) {x : E}
    (hx : x∈exactStratum u b S) (j : Fin m) (hj : j∈S) : u j≠0 := by
  intro he
  obtain ⟨z,hz⟩ := hi
  have hlevel := (hx.2 j).mpr hj
  have hstrict := hz j
  simp only [he,inner_zero_left] at hlevel hstrict
  linarith

/-- Deleting duplicate residual facets changes neither the actual
supporting hyperplane nor its outward orientation.  Every original
active residual normal is a strictly positive multiple of the selected
actual facet normal, including at a nonsimple original vertex. -/
theorem nonsimple_singleton_presentation_active_multiple [CompleteSpace E] {k : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (v : Fin k → E) (c : Fin k → ℝ)
    (S : Finset (Fin m)) (l : Fin k) (x : E)
    (hiu : ∃ z : E,∀ j,⟪u j,z⟫_ℝ<b j) (hiv : ∃ z : E,∀ j,⟪v j,z⟫_ℝ<c j)
    (hxu : x∈exactStratum u b S) (hxv : x∈exactStratum v c {l})
    (hP : polyhedron u b=polyhedron v c) (j : Fin m) (hj : j∈S) :
    ∃ a : ℝ,0<a ∧ u j=a • v l ∧ b j=a*c l := by
  classical
  have hC := nonsimple_activeCone_eq_of_presentation u b v c S {l} x hiu hiv hxu hxv hP
  have hmem := nonsimple_generator_mem_activeCone u S j hj
  change u j∈(nonsimpleActiveGeneratedCone u S : Set E) at hmem
  rw [hC] at hmem
  obtain ⟨a,ha,he⟩ := (nonsimpleActiveGeneratedCone_mem_iff v {l} (u j)).mp hmem
  have heq : u j=a l • v l := by simpa only [Finset.sum_singleton] using he
  have hap : 0<a l := lt_of_le_of_ne (ha l (Finset.mem_singleton_self _)) (by
    intro hz
    apply nonsimple_active_normal_ne_zero u b hiu S hxu j hj
    rw [heq,←hz,zero_smul])
  refine ⟨a l,hap,heq,?_⟩
  rw [←(hxu.2 j).mpr hj,heq,inner_smul_left,conj_trivial,
    (hxv.2 l).mpr (Finset.mem_singleton_self _)]

end
end RectangleCLTArxivV1
