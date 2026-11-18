import RectangleCLTArxivV1.SupplementalHSphericalPolygonBalance
import RectangleCLTArxivV1.SupplementalHSphericalPolygonDual

/-! Native supporting-pair coverage only needs nonzero directions. The
zero direction is handled internally and does not require an arbitrary
incident ridge or a positivity assertion for a zero normal. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sphericalPolygonGeneratedCone_mem_iff_nonzero_incident_halfspaces {m q : ℕ}
    (v : Fin m → E3) (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0) (n : Fin q → E3)
    (hn : ∀ e i,0≤⟪v i,n e⟫_ℝ)
    (hcover : ∀ w : E3,w≠0 → (∀ i,0≤⟪v i,w⟫_ℝ) →
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
    by_cases hw0 : w=0
    · simp [hw0]
    · obtain ⟨e,t,ht,rfl⟩ := hcover w hw0 hw hpair
      rw [inner_smul_right]
      exact mul_nonneg ht (by simpa only [real_inner_comm] using hx e)

theorem sphericalPolygon_nonzero_incident_balance {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hcover : ∀ w : E3,w≠0 → (∀ i,0≤⟪v i,w⟫_ℝ) →
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
  have hhalf := sphericalPolygonGeneratedCone_mem_iff_nonzero_incident_halfspaces
    v hspan d hd n hnpolar hcover
  exact sphericalPolygon_generated_balance v a b n hv hn hab hinj hzero hstrict hp hm hhalf

theorem sphericalPolygon_nonzero_incident_balance_norm_le {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hspan : Submodule.span ℝ (Set.range v)=⊤)
    (d : E3) (hd : ∀ i,⟪v i,d⟫_ℝ<0)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hcover : ∀ w : E3,w≠0 → (∀ i,0≤⟪v i,w⟫_ℝ) →
      (∃ i j : Fin m,i≠j ∧ ⟪v i,w⟫_ℝ=0 ∧ ⟪v j,w⟫_ℝ=0) →
      ∃ e : Fin q,∃ t : ℝ,0≤t ∧ w=t • n e) :
    ‖∑ e,Real.arccos ⟪v (a e),v (b e)⟫_ℝ • n e‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (sphericalPolygonGeneratedCone v)) := by
  rw [sphericalPolygon_nonzero_incident_balance v a b n hspan d hd hv hn hab hinj
    hzero hstrict hp hm hcover,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1
