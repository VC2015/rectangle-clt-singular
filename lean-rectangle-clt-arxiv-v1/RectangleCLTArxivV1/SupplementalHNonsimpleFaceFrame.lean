import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry
import RectangleCLTArxivV1.SupplementalHFrameSections

/-! Canonical orthonormal coordinates for the complete normal space of an
actual face.  The rank, not the number of active facets, determines the
coordinate dimension. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m q : ℕ}

def nonsimpleFaceBasis (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) :
    OrthonormalBasis (Fin q) ℝ (nonsimpleFaceNormalSpace u F.1) :=
  (stdOrthonormalBasis ℝ (nonsimpleFaceNormalSpace u F.1)).reindex (finCongr F.2.2)

def nonsimpleFaceFrame (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) : Fin q → E :=
  fun i => (nonsimpleFaceBasis u b F i : E)

theorem nonsimpleFaceFrame_orthonormal (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) : Orthonormal ℝ (nonsimpleFaceFrame u b F) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact (orthonormal_iff_ite.mp (nonsimpleFaceBasis u b F).orthonormal) i j

theorem nonsimpleFaceFrame_span (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) :
    Submodule.span ℝ (Set.range (nonsimpleFaceFrame u b F)) = nonsimpleFaceNormalSpace u F.1 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (nonsimpleFaceBasis u b F i).2
  · intro x hx
    let y : nonsimpleFaceNormalSpace u F.1 := ⟨x,hx⟩
    have he : (∑ i, ((nonsimpleFaceBasis u b F).repr y i) • nonsimpleFaceFrame u b F i) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, nonsimpleFaceFrame, y] using
        congrArg (fun z : nonsimpleFaceNormalSpace u F.1 => (z : E))
          ((nonsimpleFaceBasis u b F).sum_repr y)
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

def nonsimpleFaceNormalPoint (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) : E :=
  (nonsimpleFaceNormalSpace u F.1).orthogonalProjection (nonsimpleFaceRepresentative u b F)

theorem nonsimpleFaceNormalPoint_mem (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) :
    nonsimpleFaceNormalPoint u b F ∈ nonsimpleFaceNormalSpace u F.1 :=
  Submodule.coe_mem _

theorem nonsimpleFaceNormalPoint_levels (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) (j : Fin m) (hj : j ∈ F.1) :
    ⟪u j,nonsimpleFaceNormalPoint u b F⟫_ℝ = b j := by
  have hproj := Submodule.inner_orthogonalProjection_eq_of_mem_left
    (K := nonsimpleFaceNormalSpace u F.1)
    (⟨u j,nonsimple_normal_mem u F.1 j hj⟩ : nonsimpleFaceNormalSpace u F.1)
    (nonsimpleFaceRepresentative u b F)
  exact hproj.trans (nonsimpleFaceRepresentative_levels u b F j hj)

theorem nonsimpleFaceNormalPoint_eq_frameProjection (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) :
    nonsimpleFaceNormalPoint u b F =
      ∑ i, ⟪nonsimpleFaceFrame u b F i,nonsimpleFaceRepresentative u b F⟫_ℝ •
        nonsimpleFaceFrame u b F i := by
  change _ = gaussianFrameProjection (nonsimpleFaceFrame u b F) _
  rw [gaussianFrameProjection_eq_orthogonalProjection _ (nonsimpleFaceFrame_orthonormal u b F),
    nonsimpleFaceFrame_span]
  rfl

theorem nonsimpleFaceNormalPoint_unique (u : Fin m → E) (b : Fin m → ℝ)
    (S : Finset (Fin m)) (x y : E)
    (hx : x ∈ nonsimpleFaceNormalSpace u S) (hy : y ∈ nonsimpleFaceNormalSpace u S)
    (hlevels : ∀ j ∈ S, ⟪u j,x⟫_ℝ = ⟪u j,y⟫_ℝ) : x = y := by
  let T := nonsimpleFaceNormalSpace u S
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ (x-y)).toLinearMap
  have hk : T ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change ⟪x-y,u j⟫_ℝ = 0
    rw [inner_sub_left]
    calc
      _ = ⟪u j,x⟫_ℝ - ⟪u j,y⟫_ℝ := by
        congr 1 <;> exact real_inner_comm _ _
      _ = 0 := by rw [hlevels j hj, sub_self]
  have hh := hk (T.sub_mem hx hy)
  change ⟪x-y,x-y⟫_ℝ = 0 at hh
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)

theorem nonsimpleFaceNormalPoint_eq_of_closedFace (u : Fin m → E) (b : Fin m → ℝ)
    (F : NonsimpleFaceIndex u b q) (x : E) (hx : x ∈ nonsimpleClosedFace u b F.1) :
    ((nonsimpleFaceNormalSpace u F.1).orthogonalProjection x : E) =
      nonsimpleFaceNormalPoint u b F := by
  apply nonsimpleFaceNormalPoint_unique u b F.1 _ _ (Submodule.coe_mem _)
    (nonsimpleFaceNormalPoint_mem u b F)
  intro j hj
  rw [nonsimpleFaceNormalPoint_levels u b F j hj]
  exact (Submodule.inner_orthogonalProjection_eq_of_mem_left
    (K := nonsimpleFaceNormalSpace u F.1)
    (⟨u j,nonsimple_normal_mem u F.1 j hj⟩ : nonsimpleFaceNormalSpace u F.1) x).trans (hx.2 j hj)

end
end RectangleCLTArxivV1
