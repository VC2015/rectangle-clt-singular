import RectangleCLTArxivV1.SupplementalHSphericalPolygonBalance
import RectangleCLTArxivV1.SupplementalHSphericalPolygonDual

/-! Spherical balance from actual incident-ridge ray coverage. The complete
halfspace description is proved internally from finite polar splitting and
bipolarity; neither a halfspace identity nor an angular/area formula is a
supplier. Original-polyhedron incidence supplies the remaining ray coverage. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sphericalPolygon_incident_ridge_balance {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hcover : ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ i j : Fin m,i≠j ∧ ⟪v i,w⟫_ℝ=0 ∧ ⟪v j,w⟫_ℝ=0) →
      ∃ e : Fin q,∃ t : ℝ,0≤t ∧ w=t • n e) :
    (∑ e,Real.arccos ⟪v (a e),v (b e)⟫_ℝ • n e)=
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection (sphericalPolygonGeneratedCone v),
        ω.1 ∂(volume : Measure E3).toSphere := by
  have hnpolar (e : Fin q) (i : Fin m) : 0≤⟪v i,n e⟫_ℝ := by
    rw [real_inner_comm]
    by_cases ha : i=a e
    · simp [ha,(hzero e).1]
    by_cases hb : i=b e
    · simp [hb,(hzero e).2]
    exact (hstrict e i ha hb).le
  have hhalf := sphericalPolygonGeneratedCone_mem_iff_incident_halfspaces
    v hspan d hd n hnpolar hcover
  exact sphericalPolygon_generated_balance v a b n hv hn hab hinj hzero hstrict hp hm hhalf

theorem sphericalPolygon_incident_ridge_balance_norm_le {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hcover : ∀ w : E3,(∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ i j : Fin m,i≠j ∧ ⟪v i,w⟫_ℝ=0 ∧ ⟪v j,w⟫_ℝ=0) →
      ∃ e : Fin q,∃ t : ℝ,0≤t ∧ w=t • n e) :
    ‖∑ e,Real.arccos ⟪v (a e),v (b e)⟫_ℝ • n e‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (sphericalPolygonGeneratedCone v)) := by
  rw [sphericalPolygon_incident_ridge_balance v a b n hspan d hd hv hn hab hinj
    hzero hstrict hp hm hcover,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1
