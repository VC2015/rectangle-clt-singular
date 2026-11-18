import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinateIncidence

/-! Original irredundant faces discharge every geometric input of the
arbitrary-edge spherical balance. No coverage, cone or conormal supplier
is assumed in the resulting original-face theorems. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
local notation "uE" => (fun j => projectionEuclideanVector (u j))
local notation "V" => nonsimpleFaceCoordinateNormals uE b H
local notation "N" => nonsimpleRidgeCoordinateConormal uE b H
local notation "A" => nonsimpleRidgeCoordinateLeft u b hi hw hu H
local notation "B" => nonsimpleRidgeCoordinateRight u b hi hw hu H
local notation "Ridges" => NonsimpleRidgeAt uE b H

include hi in
theorem nonsimpleOriginal_strictInterior_euclidean :
    ∃ x : EuclideanSpace ℝ (Fin r),∀ j,⟪projectionEuclideanVector (u j),x⟫_ℝ<b j := by
  obtain ⟨x,hx⟩ := hi
  refine ⟨projectionEuclideanVector x,?_⟩
  intro j
  change ⟪(WithLp.equiv 2 (Vector r)).symm (u j),(WithLp.equiv 2 (Vector r)).symm x⟫_ℝ<b j
  rw [←faceDot_eq_euclidean_inner]
  exact hx j

include hu in
theorem nonsimpleOriginal_coordinateNormals_unit : ∀ i,‖V i‖=1 :=
  nonsimpleFaceCoordinateNormals_unit uE b H (fun j => thresholdEuclideanNormal_unit _ (hu j))

include hi hw hu in
theorem nonsimpleOriginal_coordinateNormals_injective : Function.Injective V := by
  intro i j he
  by_contra hij
  have hiS := nonsimple_normal_mem uE H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i)
  have hjS := nonsimple_normal_mem uE H.1 _ (nonsimpleFaceActiveIndex_mem H.1 j)
  have hrepr : (nonsimpleFaceBasis uE b H).repr ⟨uE (nonsimpleFaceActiveIndex H.1 i),hiS⟩=
      (nonsimpleFaceBasis uE b H).repr ⟨uE (nonsimpleFaceActiveIndex H.1 j),hjS⟩ := by
    simpa only [nonsimpleFaceCoordinateNormals,nonsimpleFaceCoordinateMap_of_mem uE b H _ hiS,
      nonsimpleFaceCoordinateMap_of_mem uE b H _ hjS] using he
  have hE := congrArg (fun x : nonsimpleFaceNormalSpace uE H.1 => (x : EuclideanSpace ℝ (Fin r)))
    ((nonsimpleFaceBasis uE b H).repr.injective hrepr)
  have hU : u (nonsimpleFaceActiveIndex H.1 i)=u (nonsimpleFaceActiveIndex H.1 j) :=
    (WithLp.equiv 2 (Vector r)).symm.injective hE
  let z := nonsimpleFaceRepresentative uE b H
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have hlev (k : Fin (Fintype.card H.1)) : faceDot (u (nonsimpleFaceActiveIndex H.1 k)) x=
      b (nonsimpleFaceActiveIndex H.1 k) := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceRepresentative_levels uE b H _ (nonsimpleFaceActiveIndex_mem H.1 k)
  have hli := nonsimple_active_pair_linearIndependent u b hi hw hu _ _
    ((nonsimpleFaceActiveIndex_injective H.1).ne hij) x (hlev i) (hlev j)
  have hne : u (nonsimpleFaceActiveIndex H.1 i)≠u (nonsimpleFaceActiveIndex H.1 j) :=
    hli.injective.ne (by decide : (0 : Fin 2)≠1)
  exact hne hU

theorem nonsimpleOriginal_coordinateConormal_zero (e : Fin (Fintype.card Ridges)) :
    ⟪N e,V (A e)⟫_ℝ=0 ∧ ⟪N e,V (B e)⟫_ℝ=0 := by
  have hz (j : Fin m) (hj : j∈(nonsimpleFaceRidgeIndex uE b H e).1.1) :
      ⟪nonsimpleIncidentConormal uE b H (nonsimpleFaceRidgeIndex uE b H e),uE j⟫_ℝ=0 :=
    nonsimpleIncidentConormal_zero_on_ridge uE b H _ j hj
  constructor
  · rw [nonsimpleRidgeCoordinateConormal_inner,nonsimpleRidgeCoordinateLeft_original]
    apply hz
    exact (Finset.ext_iff.mp (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2 _).mpr (by simp)
  · rw [nonsimpleRidgeCoordinateConormal_inner,nonsimpleRidgeCoordinateRight_original]
    apply hz
    exact (Finset.ext_iff.mp (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2 _).mpr (by simp)

theorem nonsimpleOriginal_coordinateConormal_strict (e : Fin (Fintype.card Ridges))
    (i : Fin (Fintype.card H.1)) (hia : i≠A e) (hib : i≠B e) :
    0<⟪N e,V i⟫_ℝ := by
  rw [nonsimpleRidgeCoordinateConormal_inner]
  apply nonsimpleIncidentConormal_strict_on_other uE b H _ _ (nonsimpleFaceActiveIndex_mem H.1 i)
  intro hmem
  have hp := (Finset.ext_iff.mp
    (nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)).2.2 _).mp hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with hp|hp
  · apply hia
    apply nonsimpleFaceActiveIndex_injective H.1
    rw [nonsimpleRidgeCoordinateLeft_original]
    exact hp
  · apply hib
    apply nonsimpleFaceActiveIndex_injective H.1
    rw [nonsimpleRidgeCoordinateRight_original]
    exact hp

theorem nonsimpleOriginal_coordinateNormals_pair_plus_ne (e : Fin (Fintype.card Ridges)) :
    V (A e)+V (B e)≠0 := by
  obtain ⟨d,hd⟩ := nonsimpleFaceCoordinateNormals_exists_strictPolar uE b H
    (nonsimpleOriginal_strictInterior_euclidean u b hi)
  intro hz
  have h := congrArg (fun x : E3 => ⟪x,d⟫_ℝ) hz
  dsimp only at h
  rw [inner_add_left,inner_zero_left] at h
  linarith [hd (A e),hd (B e)]

theorem nonsimpleOriginal_coordinateNormals_pair_minus_ne (e : Fin (Fintype.card Ridges)) :
    V (A e)-V (B e)≠0 :=
  sub_ne_zero.mpr ((nonsimpleOriginal_coordinateNormals_injective u b hi hw hu H).ne
    (nonsimpleRidgeCoordinate_pair_distinct u b hi hw hu H e))

include hi hw hu in
theorem nonsimpleOriginal_coordinate_nonzero_coverage
    (w : E3) (hw0 : w≠0) (hwp : ∀ i,0≤⟪V i,w⟫_ℝ)
    (hpair : ∃ a d : Fin (Fintype.card H.1),a≠d ∧ ⟪V a,w⟫_ℝ=0 ∧ ⟪V d,w⟫_ℝ=0) :
    ∃ e : Fin (Fintype.card Ridges),∃ t : ℝ,0≤t ∧ w=t • N e := by
  let W := (nonsimpleFaceBasis uE b H).repr.symm w
  have hW : nonsimpleFaceCoordinateMap uE b H W.val=w := by
    rw [nonsimpleFaceCoordinateMap_of_mem uE b H W.val W.property]
    change (nonsimpleFaceBasis uE b H).repr W=w
    exact (nonsimpleFaceBasis uE b H).repr.apply_symm_apply w
  have hW0 : W.val≠0 := by
    intro hz
    apply hw0
    rw [←hW,hz,map_zero]
  have hinner (i : Fin (Fintype.card H.1)) :
      ⟪V i,w⟫_ℝ=⟪W.val,uE (nonsimpleFaceActiveIndex H.1 i)⟫_ℝ := by
    rw [←hW,nonsimpleFaceCoordinateNormals,nonsimpleFaceCoordinateMap_inner_left uE b H _ _
      (nonsimple_normal_mem uE H.1 _ (nonsimpleFaceActiveIndex_mem H.1 i))]
    exact real_inner_comm _ _
  have hpolar (j : Fin m) (hj : j∈H.1) : 0≤⟪W.val,uE j⟫_ℝ := by
    have h := hwp (nonsimpleFaceLocalIndex H.1 j hj)
    rw [hinner,nonsimpleFaceActiveIndex_localIndex] at h
    exact h
  obtain ⟨a,d,had,hwa,hwd⟩ := hpair
  rw [hinner] at hwa hwd
  obtain ⟨I,t,ht,he⟩ := nonsimple_nonzero_polar_covered_by_actual_incidence u b hi hw hu H W.val hW0 W.property
    hpolar (nonsimpleFaceActiveIndex H.1 a) (nonsimpleFaceActiveIndex H.1 d)
    (nonsimpleFaceActiveIndex_mem H.1 a) (nonsimpleFaceActiveIndex_mem H.1 d)
    ((nonsimpleFaceActiveIndex_injective H.1).ne had) hwa hwd
  let e := (nonsimpleFaceRidgeIndex uE b H).symm I
  refine ⟨e,t,ht,?_⟩
  calc
    w=nonsimpleFaceCoordinateMap uE b H W.val := hW.symm
    _=nonsimpleFaceCoordinateMap uE b H (t • nonsimpleIncidentConormal uE b H I) := by rw [he]
    _=t • N e := by
      rw [map_smul]
      congr 1
      unfold nonsimpleRidgeCoordinateConormal
      rw [show nonsimpleFaceRidgeIndex uE b H e=I from (nonsimpleFaceRidgeIndex uE b H).apply_symm_apply I]

end
end RectangleCLTArxivV1
