import RectangleCLTArxivV1.SupplementalHSphericalPolygonConormal
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The rank-one residual space of a supporting pair inside an actual
three-dimensional normal space. No simplicity or pairwise proportionality
premise is supplied. -/
namespace RectangleCLTArxivV1
open Set Submodule
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem sphericalPolygon_orthogonal_range_span_le {ι : Type*}
    (e : Basis (Fin 3) ℝ E) (i : Fin 3) (v : ι → E)
    (horth : ∀ a j,j≠i → ⟪v a,e j⟫_ℝ=0) :
    Submodule.span ℝ (Set.range v)≤ℝ ∙ trihedralCoordinateNormal e i := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,rfl⟩
  rw [sphericalPolygon_vector_eq_coordinate_normal e i (v a) (horth a)]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem sphericalPolygon_orthogonal_range_finrank_le_one {ι : Type*}
    (e : Basis (Fin 3) ℝ E) (i : Fin 3) (v : ι → E)
    (horth : ∀ a j,j≠i → ⟪v a,e j⟫_ℝ=0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range v))≤1 := by
  calc
    _≤Module.finrank ℝ (ℝ ∙ trihedralCoordinateNormal e i) :=
      Submodule.finrank_mono (sphericalPolygon_orthogonal_range_span_le e i v horth)
    _=1 := finrank_span_singleton (trihedralCoordinateNormal_ne_zero e i)

theorem sphericalPolygon_orthogonal_pair_not_linearIndependent
    (e : Basis (Fin 3) ℝ E) (i : Fin 3) (u v : E)
    (hu : ∀ j,j≠i → ⟪u,e j⟫_ℝ=0)
    (hv : ∀ j,j≠i → ⟪v,e j⟫_ℝ=0) :
    ¬LinearIndependent ℝ ![u,v] := by
  intro hlin
  have horth : ∀ (a : Fin 2) j,j≠i → ⟪(![u,v] : Fin 2 → E) a,e j⟫_ℝ=0 := by
    intro a j hj
    fin_cases a
    · exact hu j hj
    · exact hv j hj
  have hb := sphericalPolygon_orthogonal_range_finrank_le_one e i (![u,v] : Fin 2 → E) horth
  have heq : Module.finrank ℝ (Submodule.span ℝ (Set.range (![u,v] : Fin 2 → E)))=2 := by
    simpa using finrank_span_eq_card hlin
  omega

theorem sphericalPolygon_orthogonal_range_finrank_le_one_of_three {ι : Type*}
    (rays : Fin 3 → E) (hlin : LinearIndependent ℝ rays)
    (hdim : Module.finrank ℝ E=3) (v : ι → E)
    (hzero : ∀ a,⟪v a,rays 0⟫_ℝ=0) (hone : ∀ a,⟪v a,rays 1⟫_ℝ=0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range v))≤1 := by
  let e := basisOfLinearIndependentOfCardEqFinrank hlin (by simpa using hdim.symm)
  have he (j : Fin 3) : e j=rays j := by simp [e]
  apply sphericalPolygon_orthogonal_range_finrank_le_one e 2 v
  intro a j hj
  fin_cases j
  · simpa only [he] using hzero a
  · simpa only [he] using hone a
  · exact False.elim (hj rfl)

end
end RectangleCLTArxivV1
