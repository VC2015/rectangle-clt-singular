import RectangleCLTArxivV1.SupplementalHNonsimpleFaceNormalCone

/-! Retained original inequalities have the same oriented supporting
normal as a singleton active facet in any exact selected presentation.
Unused original inequalities are replaced by the strict tautology 0 < 1,
so the genuine full-family normal-cone theorem applies without a new
proportionality or normal-cone premise. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {m q : ℕ}

theorem nonsimple_retained_presentation_active_multiple_of_exactStratum
    (u : Fin m → E) (b : Fin m → ℝ) (s : Finset (Fin m))
    (v : Fin q → E) (c : Fin q → ℝ)
    (hpoly : ∀ y : E, (∀ j, ⟪v j,y⟫_ℝ ≤ c j) ↔
      ∀ k ∈ s, ⟪u k,y⟫_ℝ ≤ b k)
    (horigstrict : ∃ z : E, ∀ k ∈ s, ⟪u k,z⟫_ℝ < b k)
    (hselstrict : ∃ z : E, ∀ j, ⟪v j,z⟫_ℝ < c j)
    (x : E) (i : Fin q) (hx : x ∈ exactStratum v c {i})
    (k : Fin m) (hks : k ∈ s) (hkactive : ⟪u k,x⟫_ℝ = b k) :
    ∃ a : ℝ, 0 < a ∧ u k = a • v i ∧ b k = a * c i := by
  classical
  let U : Fin m → E := fun j => if j ∈ s then u j else 0
  let B : Fin m → ℝ := fun j => if j ∈ s then b j else 1
  have hUstrict : ∃ z : E, ∀ j, ⟪U j,z⟫_ℝ < B j := by
    obtain ⟨z,hz⟩ := horigstrict
    refine ⟨z,fun j => ?_⟩
    by_cases hj : j ∈ s
    · simpa only [U,B,if_pos hj] using hz j hj
    · simp only [U,B,if_neg hj,inner_zero_left]
      norm_num
  have hP : polyhedron U B = polyhedron v c := by
    ext y
    change (∀ j, ⟪U j,y⟫_ℝ ≤ B j) ↔ ∀ j, ⟪v j,y⟫_ℝ ≤ c j
    constructor
    · intro hy
      apply (hpoly y).mpr
      intro j hj
      simpa only [U,B,if_pos hj] using hy j
    · intro hy j
      by_cases hj : j ∈ s
      · simpa only [U,B,if_pos hj] using (hpoly y).mp hy j hj
      · simp only [U,B,if_neg hj,inner_zero_left]
        norm_num
  have hxU : x ∈ polyhedron U B := by
    rw [hP]
    exact hx.1
  have hxS : x ∈ exactStratum U B (nonsimpleActiveSet U B x) :=
    nonsimpleActiveSet_exactStratum U B hxU
  have hkS : k ∈ nonsimpleActiveSet U B x := by
    apply (mem_nonsimpleActiveSet U B x k).mpr
    simpa only [U,B,if_pos hks] using hkactive
  obtain ⟨a,ha,hu,hb⟩ := nonsimple_singleton_presentation_active_multiple
    U B v c (nonsimpleActiveSet U B x) i x hUstrict hselstrict hxS hx hP k hkS
  exact ⟨a,ha,by simpa only [U,if_pos hks] using hu,
    by simpa only [B,if_pos hks] using hb⟩

theorem nonsimple_retained_presentation_active_multiple
    (u : Fin m → E) (b : Fin m → ℝ) (s : Finset (Fin m))
    (v : Fin q → E) (c : Fin q → ℝ)
    (hpoly : ∀ y : E, (∀ j, ⟪v j,y⟫_ℝ ≤ c j) ↔
      ∀ k ∈ s, ⟪u k,y⟫_ℝ ≤ b k)
    (horigstrict : ∃ z : E, ∀ k ∈ s, ⟪u k,z⟫_ℝ < b k)
    (hselstrict : ∃ z : E, ∀ j, ⟪v j,z⟫_ℝ < c j)
    (x : E) (i : Fin q)
    (hx : ⟪v i,x⟫_ℝ = c i ∧ ∀ j, j ≠ i → ⟪v j,x⟫_ℝ < c j)
    (k : Fin m) (hks : k ∈ s) (hkactive : ⟪u k,x⟫_ℝ = b k) :
    ∃ a : ℝ, 0 < a ∧ u k = a • v i ∧ b k = a * c i := by
  have hxS : x ∈ exactStratum v c {i} := by
    constructor
    · intro j
      by_cases hji : j = i
      · simpa only [hji] using hx.1.le
      · exact (hx.2 j hji).le
    · intro j
      simp only [Finset.mem_singleton]
      constructor
      · intro he
        by_contra hji
        exact (ne_of_lt (hx.2 j hji)) he
      · rintro rfl
        exact hx.1
  exact nonsimple_retained_presentation_active_multiple_of_exactStratum
    u b s v c hpoly horigstrict hselstrict x i hxS k hks hkactive

end
end RectangleCLTArxivV1
