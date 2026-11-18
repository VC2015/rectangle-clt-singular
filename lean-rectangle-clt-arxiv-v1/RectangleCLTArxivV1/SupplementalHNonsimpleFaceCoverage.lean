import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCofaces
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceConormal
import RectangleCLTArxivV1.SupplementalHSphericalPolygonConormal

/-! Every nonzero pair-supported polar direction is covered by a
genuine actual ridge incidence.  The finite family and its conormals are
constructed from original faces, including nonsimple codimension3. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem nonsimple_nonzero_polar_covered_by_actual_incidence {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
    (w : EuclideanSpace ℝ (Fin r)) (hw0 : w≠0)
    (hwS : w∈nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1)
    (hwp : ∀ j∈H.1,0≤⟪w,projectionEuclideanVector (u j)⟫_ℝ)
    (a d : Fin m) (ha : a∈H.1) (hd : d∈H.1) (had : a≠d)
    (hwa : ⟪w,projectionEuclideanVector (u a)⟫_ℝ=0)
    (hwd : ⟪w,projectionEuclideanVector (u d)⟫_ℝ=0) :
    ∃ I : NonsimpleRidgeAt (fun j => projectionEuclideanVector (u j)) b H,
      ∃ t : ℝ,0≤t ∧ w=t • nonsimpleIncidentConormal _ b H I := by
  classical
  obtain ⟨R,hR,hRH⟩ := nonsimple_supporting_pair_has_actual_ridge u b hi hw hu H w hw0 hwS
    hwp a d ha hd had hwa hwd
  let I : NonsimpleRidgeAt (fun j => projectionEuclideanVector (u j)) b H := ⟨R,hRH⟩
  obtain ⟨k,hk,hkr⟩ := nonsimpleRidgeAt_exists_other_active _ b H I
  have hka : k≠a := by intro he; subst k; simp [I,hR] at hkr
  have hkd : k≠d := by intro he; subst k; simp [I,hR] at hkr
  let F : Fin 3 → Fin m := ![a,d,k]
  have hF : Function.Injective F := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [F]
  have hFS (i : Fin 3) : F i∈H.1 := by fin_cases i <;> simp [F,ha,hd,hk]
  let S := nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1
  let v : Fin 3 → S := fun i => ⟨projectionEuclideanVector (u (F i)),nonsimple_normal_mem _ H.1 _ (hFS i)⟩
  let z := nonsimpleFaceRepresentative (fun j => projectionEuclideanVector (u j)) b H
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have hlev (i : Fin 3) : faceDot (u (F i)) x=b (F i) := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceRepresentative_levels _ b H _ (hFS i)
  have hlin0 := nonsimple_active_triple_euclidean_linearIndependent u b hi hw hu F hF x hlev
  have hlin : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp S.subtype
    exact hlin0
  let W : S := ⟨w,hwS⟩
  let N : S := ⟨nonsimpleIncidentConormal _ b H I,nonsimpleIncidentConormal_mem _ b H I⟩
  have hN : ‖N‖=1 := nonsimpleIncidentConormal_unit _ b H I
  have hWa : ⟪W,v 0⟫_ℝ=0 := hwa
  have hWd : ⟪W,v 1⟫_ℝ=0 := hwd
  have hNa : ⟪N,v 0⟫_ℝ=0 :=
    nonsimpleIncidentConormal_zero_on_ridge _ b H I a (by simp [I,hR])
  have hNd : ⟪N,v 1⟫_ℝ=0 :=
    nonsimpleIncidentConormal_zero_on_ridge _ b H I d (by simp [I,hR])
  have hWk : 0≤⟪W,v 2⟫_ℝ := hwp k hk
  have hNk : 0≤⟪N,v 2⟫_ℝ := nonsimpleIncidentConormal_nonneg _ b H I k hk
  obtain ⟨t,ht,he⟩ := sphericalPolygon_conormal_nonneg_smul_of_three v hlin H.2.2 W N hN
    hWa hWd hNa hNd hWk hNk
  refine ⟨I,t,ht,?_⟩
  exact congrArg (fun y : S => (y : EuclideanSpace ℝ (Fin r))) he

end
end RectangleCLTArxivV1
