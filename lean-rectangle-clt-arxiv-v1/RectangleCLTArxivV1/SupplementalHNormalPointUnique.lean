import RectangleCLTArxivV1.SupplementalHFrameSections

/-! The actual constant normal-space point is uniquely determined by its
supporting levels, independently of the selected conditioning frame. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalPoint_eq_of_spanning_levels {q : ℕ} (u : Fin q → E) (x y : E)
    (hx : x∈Submodule.span ℝ (Set.range u)) (hy : y∈Submodule.span ℝ (Set.range u))
    (hlevels : ∀ i, ⟪u i,x⟫_ℝ=⟪u i,y⟫_ℝ) : x=y := by
  let S := Submodule.span ℝ (Set.range u)
  let ℓ : E →ₗ[ℝ] ℝ := (innerSL ℝ (x-y)).toLinearMap
  have hker : S≤LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change ⟪x-y,u i⟫_ℝ=0
    rw [inner_sub_left]
    calc
      _ = ⟪u i,x⟫_ℝ-⟪u i,y⟫_ℝ := by
        congr 1 <;> exact real_inner_comm _ _
      _ = 0 := by rw [hlevels i,sub_self]
  have h := hker (S.sub_mem hx hy)
  change ⟪x-y,x-y⟫_ℝ=0 at h
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

end
end RectangleCLTArxivV1
