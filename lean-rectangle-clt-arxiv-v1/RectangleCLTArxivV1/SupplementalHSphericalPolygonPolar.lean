import RectangleCLTArxivV1.SupplementalHNonsimpleFacePolarLine
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite polar testing in three dimensions. A polar direction with at
most one active generator can be split into two feasible directions, each
with an additional zero. Thus supporting pair planes suffice. -/
namespace RectangleCLTArxivV1
open Set Submodule
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Two prescribed vectors in three dimensions have a genuine nonzero
common orthogonal direction, including dependent and zero constraints. -/
theorem sphericalPolygon_exists_orthogonal_pair (z a : E3) :
    ∃ d : E3,d≠0 ∧ ⟪z,d⟫_ℝ=0 ∧ ⟪a,d⟫_ℝ=0 := by
  classical
  let s : Finset E3 := {z,a}
  let K : Submodule ℝ E3 := Submodule.span ℝ (s : Set E3)
  have hcard : s.card≤2 := by
    exact (Finset.card_insert_le z {a}).trans (by simp)
  have hdim : Module.finrank ℝ K<Module.finrank ℝ E3 := by
    have hle : Module.finrank ℝ K≤s.card := finrank_span_finset_le_card s
    have hE : Module.finrank ℝ E3=3 := by simp
    rw [hE]
    omega
  have hK : K≠⊤ := (Submodule.lt_top_of_finrank_lt_finrank hdim).ne
  have horth : Kᗮ≠⊥ := by
    intro h
    exact hK (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨d,hd,hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  refine ⟨d,hd0,?_,?_⟩
  · exact (K.mem_orthogonal d).mp hd z (Submodule.subset_span (by simp [s]))
  · exact (K.mem_orthogonal d).mp hd a (Submodule.subset_span (by simp [s]))

/-- On a three-dimensional polar cone, a direction already on one
supporting plane is a positive combination of directions on two planes.
It is enough to test any linear functional on those latter directions. -/
theorem sphericalPolygon_polar_linear_nonneg_of_one_zero {m : ℕ}
    (v : Fin m → E3) (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (L : E3 →ₗ[ℝ] ℝ)
    (htwo : ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ a b : Fin m,a≠b ∧ ⟪v a,w⟫_ℝ=0 ∧ ⟪v b,w⟫_ℝ=0) → 0≤L w)
    (w : E3) (hw : ∀ i,0≤⟪v i,w⟫_ℝ)
    (j : Fin m) (hj : ⟪v j,w⟫_ℝ=0) : 0≤L w := by
  classical
  by_cases hother : ∃ k : Fin m,k≠j ∧ ⟪v k,w⟫_ℝ=0
  · obtain ⟨k,hkj,hk⟩ := hother
    exact htwo w hw ⟨j,k,hkj.symm,hj,hk⟩
  · obtain ⟨d,hd0,hdz,hdj⟩ := sphericalPolygon_exists_orthogonal_pair (∑ i,v i) (v j)
    have hzero : ∀ i,⟪v i,w⟫_ℝ=0 → ⟪v i,d⟫_ℝ=0 := by
      intro i hi
      have hij : i=j := by
        by_contra hn
        exact hother ⟨i,hn,hi⟩
      simpa only [hij] using hdj
    obtain ⟨hpos,hneg⟩ := nonsimple_polar_inner_slopes_both_signs v d hspan hd0 hdz
    obtain ⟨tm,tp,α,β,jm,jp,htm,htp,hα,hβ,hsum,htime,hnewm,hnewp,
      hzm,hzp,hwm,hwp,hold,hall,hdecomp⟩ :=
      nonsimple_polar_inner_line_split v w d hw hzero hpos hneg
    have hjm : jm≠j := by
      intro h
      rw [h,hdj] at hnewm
      exact (lt_irrefl (0 : ℝ)) hnewm
    have hjp : jp≠j := by
      intro h
      rw [h,hdj] at hnewp
      exact (lt_irrefl (0 : ℝ)) hnewp
    have hLm : 0≤L (w+tm • d) :=
      htwo _ hwm ⟨j,jm,hjm.symm,(hold j hj).1,hzm⟩
    have hLp : 0≤L (w+tp • d) :=
      htwo _ hwp ⟨j,jp,hjp.symm,(hold j hj).2,hzp⟩
    rw [hdecomp,map_add,map_smul,map_smul]
    exact add_nonneg (mul_nonneg hα.le hLm) (mul_nonneg hβ.le hLp)

/-- Every polar direction is controlled by supporting pair planes. The
proof uses exactly two finite line splittings, with all original
inequalities retained and no extremal-ray or conic-decomposition premise. -/
theorem sphericalPolygon_polar_linear_nonneg_of_two_zero {m : ℕ}
    (v : Fin m → E3) (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (L : E3 →ₗ[ℝ] ℝ)
    (htwo : ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ a b : Fin m,a≠b ∧ ⟪v a,w⟫_ℝ=0 ∧ ⟪v b,w⟫_ℝ=0) → 0≤L w)
    (w : E3) (hw : ∀ i,0≤⟪v i,w⟫_ℝ) : 0≤L w := by
  classical
  by_cases hzero : ∃ j : Fin m,⟪v j,w⟫_ℝ=0
  · obtain ⟨j,hj⟩ := hzero
    exact sphericalPolygon_polar_linear_nonneg_of_one_zero v hspan L htwo w hw j hj
  · obtain ⟨d,hd0,hdz,hdzero⟩ := sphericalPolygon_exists_orthogonal_pair (∑ i,v i) 0
    obtain ⟨hpos,hneg⟩ := nonsimple_polar_inner_slopes_both_signs v d hspan hd0 hdz
    have hkeep : ∀ i,⟪v i,w⟫_ℝ=0 → ⟪v i,d⟫_ℝ=0 := by
      intro i hi
      exact False.elim (hzero ⟨i,hi⟩)
    obtain ⟨tm,tp,α,β,jm,jp,htm,htp,hα,hβ,hsum,htime,hnewm,hnewp,
      hzm,hzp,hwm,hwp,hold,hall,hdecomp⟩ :=
      nonsimple_polar_inner_line_split v w d hw hkeep hpos hneg
    have hLm := sphericalPolygon_polar_linear_nonneg_of_one_zero v hspan L htwo
      (w+tm • d) hwm jm hzm
    have hLp := sphericalPolygon_polar_linear_nonneg_of_one_zero v hspan L htwo
      (w+tp • d) hwp jp hzp
    rw [hdecomp,map_add,map_smul,map_smul]
    exact add_nonneg (mul_nonneg hα.le hLm) (mul_nonneg hβ.le hLp)

end
end RectangleCLTArxivV1
