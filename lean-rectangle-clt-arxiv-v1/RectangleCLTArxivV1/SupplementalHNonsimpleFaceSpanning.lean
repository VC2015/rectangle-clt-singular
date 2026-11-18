import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry

/-! A complete actual face can be recovered from any active spanning
family, without discarding the other original constraints. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem nonsimpleClosedFace_eq_spanning_levels {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m q : ℕ}
    (u : Fin m → E) (b : Fin m → ℝ) (H : NonsimpleFaceIndex u b q)
    (f : ι → Fin m) (hf : ∀ i,f i∈H.1)
    (hspan : Submodule.span ℝ (range (fun i => u (f i)))=nonsimpleFaceNormalSpace u H.1) :
    nonsimpleClosedFace u b H.1={x | x∈polyhedron u b ∧ ∀ i,⟪u (f i),x⟫_ℝ=b (f i)} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1,fun i => hx.2 (f i) (hf i)⟩
  · rintro ⟨hx,hflev⟩
    refine ⟨hx,?_⟩
    have heq : ∀ v∈Submodule.span ℝ (range (fun i => u (f i))),
        ⟪v,x⟫_ℝ=⟪v,nonsimpleFaceRepresentative u b H⟫_ℝ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i,rfl⟩ := hv
        rw [hflev i,nonsimpleFaceRepresentative_levels u b H (f i) (hf i)]
      | zero => simp
      | add v w hv hw ihv ihw => simp [inner_add_left,ihv,ihw]
      | smul c v hv ih => simp [inner_smul_left,ih]
    intro j hj
    rw [heq (u j) (hspan.symm ▸ nonsimple_normal_mem u H.1 j hj),
      nonsimpleFaceRepresentative_levels u b H j hj]

end
end RectangleCLTArxivV1
