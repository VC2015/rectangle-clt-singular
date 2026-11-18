import RectangleCLTArxivV1.SupplementalHSphericalPolygonSupport
import RectangleCLTArxivV1.SupplementalHSphericalPolygonPolar

/-! Actual finite supporting-pair halfspace completeness. Bipolarity and
the proved two-level polar split reduce all polar tests to directions
annihilating two distinct generators. Actual incident-ridge coverage then
identifies a finite halfspace presentation, with no angular/area premise. -/
namespace RectangleCLTArxivV1
open Set
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sphericalPolygonGeneratedCone_eq_nonsimple {m : ℕ} (v : Fin m → E3) :
    sphericalPolygonGeneratedCone v=(nonsimpleGeneratedCone v : Set E3) := rfl

theorem sphericalPolygonGeneratedCone_mem_iff_nonneg_polar {m : ℕ}
    (v : Fin m → E3) (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0) (x : E3) :
    x∈sphericalPolygonGeneratedCone v ↔
      ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) → 0≤⟪x,w⟫_ℝ := by
  rw [sphericalPolygonGeneratedCone_eq_nonsimple]
  change (x∈nonsimpleGeneratedCone v) ↔ _
  rw [nonsimpleGeneratedCone_mem_iff_polar v d hd]
  constructor
  · intro hx w hw
    have h := hx (-w) (fun i => by simpa only [inner_neg_right,neg_nonpos] using hw i)
    simpa only [inner_neg_right,neg_nonpos] using h
  · intro hx y hy
    have h := hx (-y) (fun i => by simpa only [inner_neg_right,neg_nonneg] using hy i)
    simpa only [inner_neg_right,neg_nonneg] using h

/-- The actual finitely generated cone is determined by its supporting
pair-plane directions. No finite-halfspace or extremal-ray assertion is
assumed here: all remaining polar directions are split explicitly. -/
theorem sphericalPolygonGeneratedCone_mem_iff_supporting_pairs {m : ℕ}
    (v : Fin m → E3) (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0) (x : E3) :
    x∈sphericalPolygonGeneratedCone v ↔
      ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
        (∃ a b : Fin m,a≠b ∧ ⟪v a,w⟫_ℝ=0 ∧ ⟪v b,w⟫_ℝ=0) → 0≤⟪x,w⟫_ℝ := by
  rw [sphericalPolygonGeneratedCone_mem_iff_nonneg_polar v d hd]
  constructor
  · intro hx w hw _
    exact hx w hw
  · intro hx w hw
    exact sphericalPolygon_polar_linear_nonneg_of_two_zero v hspan
      (innerSL ℝ x).toLinearMap hx w hw

/-- A finite family of genuine incident-ridge rays gives all halfspaces
of the actual generated normal cone. The ray-coverage premise is geometric;
it is independent of balance, area, Gaussian mass or a Green formula. -/
theorem sphericalPolygonGeneratedCone_mem_iff_incident_halfspaces {m q : ℕ}
    (v : Fin m → E3) (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0) (n : Fin q → E3)
    (hn : ∀ e i,0≤⟪v i,n e⟫_ℝ)
    (hcover : ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ a b : Fin m,a≠b ∧ ⟪v a,w⟫_ℝ=0 ∧ ⟪v b,w⟫_ℝ=0) →
      ∃ e : Fin q,∃ t : ℝ,0≤t ∧ w=t • n e)
    (x : E3) :
    x∈sphericalPolygonGeneratedCone v ↔ ∀ e,0≤⟪n e,x⟫_ℝ := by
  constructor
  · intro hx e
    have h := (sphericalPolygonGeneratedCone_mem_iff_nonneg_polar v d hd x).mp hx (n e) (hn e)
    simpa only [real_inner_comm] using h
  · intro hx
    apply (sphericalPolygonGeneratedCone_mem_iff_supporting_pairs v hspan d hd x).mpr
    intro w hw hpair
    obtain ⟨e,t,ht,rfl⟩ := hcover w hw hpair
    rw [inner_smul_right]
    exact mul_nonneg ht (by simpa only [real_inner_comm] using hx e)

end
end RectangleCLTArxivV1
