import RectangleCLTArxivV1.SupplementalHTrihedralNormals
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual uniqueness of a supporting pair conormal. A basis is only a
coordinate frame for the three-dimensional normal space; the conormal
itself may belong to a polygon with any number of generating rays. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Every vector orthogonal to the other two basis rays lies in the
actual one-dimensional conormal space, with its exact signed coefficient. -/
theorem sphericalPolygon_vector_eq_coordinate_normal (e : Basis (Fin 3) ℝ E)
    (i : Fin 3) (u : E) (horth : ∀ j,j≠i → ⟪u,e j⟫_ℝ=0) :
    u=⟪u,e i⟫_ℝ • trihedralCoordinateNormal e i := by
  have hlin (x : E) : ⟪u,x⟫_ℝ=e.repr x i*⟪u,e i⟫_ℝ := by
    calc
      _=⟪u,∑ j,e.repr x j • e j⟫_ℝ := by rw [e.sum_repr]
      _=_ := by
        rw [inner_sum]
        simp only [inner_smul_right]
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [horth j hji,mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ i))
  apply ext_inner_right ℝ
  intro x
  rw [inner_smul_left,conj_trivial,inner_trihedralCoordinateNormal,hlin]
  ring

theorem sphericalPolygon_unit_conormal_positive (e : Basis (Fin 3) ℝ E)
    (i : Fin 3) (u : E) (hu : ‖u‖=1)
    (horth : ∀ j,j≠i → ⟪u,e j⟫_ℝ=0) (hpos : 0≤⟪u,e i⟫_ℝ) :
    0<⟪u,e i⟫_ℝ := by
  have hne : ⟪u,e i⟫_ℝ≠0 := by
    intro hz
    have h := sphericalPolygon_vector_eq_coordinate_normal e i u horth
    rw [hz,zero_smul] at h
    have hn := congrArg norm h
    rw [hu,norm_zero] at hn
    exact one_ne_zero hn
  exact lt_of_le_of_ne hpos hne.symm

/-- A feasible supporting-pair direction is a nonnegative multiple of
the actual feasible unit conormal. Orthogonality and signs are the only
geometric inputs; no proportionality or balance identity is supplied. -/
theorem sphericalPolygon_conormal_nonneg_smul (e : Basis (Fin 3) ℝ E)
    (i : Fin 3) (u n : E) (hn : ‖n‖=1)
    (huorth : ∀ j,j≠i → ⟪u,e j⟫_ℝ=0)
    (hnorth : ∀ j,j≠i → ⟪n,e j⟫_ℝ=0)
    (hupos : 0≤⟪u,e i⟫_ℝ) (hnpos : 0≤⟪n,e i⟫_ℝ) :
    ∃ t : ℝ,0≤t ∧ u=t • n := by
  have hnid := trihedralInwardNormal_unique e i n hn hnorth
    (sphericalPolygon_unit_conormal_positive e i n hn hnorth hnpos)
  refine ⟨⟪u,e i⟫_ℝ*‖trihedralCoordinateNormal e i‖,
    mul_nonneg hupos (norm_nonneg _),?_⟩
  rw [hnid,trihedralInwardNormal,smul_smul,mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (trihedralCoordinateNormal_ne_zero e i)),mul_one]
  exact sphericalPolygon_vector_eq_coordinate_normal e i u huorth

theorem sphericalPolygon_unit_conormal_unique (e : Basis (Fin 3) ℝ E)
    (i : Fin 3) (u n : E) (hu : ‖u‖=1) (hn : ‖n‖=1)
    (huorth : ∀ j,j≠i → ⟪u,e j⟫_ℝ=0)
    (hnorth : ∀ j,j≠i → ⟪n,e j⟫_ℝ=0)
    (hupos : 0≤⟪u,e i⟫_ℝ) (hnpos : 0≤⟪n,e i⟫_ℝ) : u=n := by
  exact (trihedralInwardNormal_unique e i u hu huorth
    (sphericalPolygon_unit_conormal_positive e i u hu huorth hupos)).trans
    (trihedralInwardNormal_unique e i n hn hnorth
      (sphericalPolygon_unit_conormal_positive e i n hn hnorth hnpos)).symm

/-- Three independent actual generator rays supply the coordinate basis
internally. This is convenient when a genuine face incidence provides two
zero endpoint rays and any third active generator. -/
theorem sphericalPolygon_conormal_nonneg_smul_of_three
    (v : Fin 3 → E) (hlin : LinearIndependent ℝ v) (hdim : Module.finrank ℝ E=3)
    (u n : E) (hn : ‖n‖=1)
    (hu0 : ⟪u,v 0⟫_ℝ=0) (hu1 : ⟪u,v 1⟫_ℝ=0)
    (hn0 : ⟪n,v 0⟫_ℝ=0) (hn1 : ⟪n,v 1⟫_ℝ=0)
    (hupos : 0≤⟪u,v 2⟫_ℝ) (hnpos : 0≤⟪n,v 2⟫_ℝ) :
    ∃ t : ℝ,0≤t ∧ u=t • n := by
  let e := basisOfLinearIndependentOfCardEqFinrank hlin (by simpa using hdim.symm)
  have he (j : Fin 3) : e j=v j := by simp [e]
  apply sphericalPolygon_conormal_nonneg_smul e 2 u n hn
  · intro j hj
    fin_cases j
    · simpa only [he] using hu0
    · simpa only [he] using hu1
    · exact False.elim (hj rfl)
  · intro j hj
    fin_cases j
    · simpa only [he] using hn0
    · simpa only [he] using hn1
    · exact False.elim (hj rfl)
  · simpa only [he] using hupos
  · simpa only [he] using hnpos

end
end RectangleCLTArxivV1
