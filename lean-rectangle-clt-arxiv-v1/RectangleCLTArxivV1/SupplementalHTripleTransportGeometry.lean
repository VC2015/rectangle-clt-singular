import RectangleCLTArxivV1.SupplementalHTripleTransportCone
import RectangleCLTArxivV1.SupplementalHFourthTransportGeometry

/-! Actual conical normal fibers lie in the genuine nearest-base outward
tube of their complete active set. No incidence bound is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tripleOutwardNormalCone {m r : ℕ} (u : Fin m → Vector r) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ∃ c : Fin m → ℝ,(∀ k∈active,0≤c k) ∧
    L y=coneDisplacement (fun k => projectionEuclideanVector (u k)) active c}


theorem tripleOutwardNormalCone_smul_iff {m r : ℕ} (u : Fin m → Vector r) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (t : ℝ) (ht : 0<t) (y : EuclideanSpace ℝ (Fin 3)) :
    t • y∈tripleOutwardNormalCone u active L ↔ y∈tripleOutwardNormalCone u active L := by
  have hsmul (c : Fin m → ℝ) (a : ℝ) :
      coneDisplacement (fun k => projectionEuclideanVector (u k)) active (fun k => a*c k)=
        a • coneDisplacement (fun k => projectionEuclideanVector (u k)) active c := by
    simp only [coneDisplacement,Finset.smul_sum,smul_smul]
  constructor
  · rintro ⟨c,hc,he⟩
    refine ⟨fun k => t⁻¹*c k,fun k hk => mul_nonneg (inv_nonneg.mpr ht.le) (hc k hk),?_⟩
    calc
      L y=t⁻¹ • L (t • y) := by rw [map_smul,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
      _=t⁻¹ • coneDisplacement (fun k => projectionEuclideanVector (u k)) active c := by rw [he]
      _=_ := (hsmul c t⁻¹).symm
  · rintro ⟨c,hc,he⟩
    refine ⟨fun k => t*c k,fun k hk => mul_nonneg ht.le (hc k hk),?_⟩
    rw [map_smul,he,hsmul]

theorem tripleTransportSection_reconstruct {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    projectionEuclideanVector g=projectionEuclideanVector (tripleTransportSection L Z g)+
      L (tripleTransportCoordinate L g-Z) := by
  have hp : gaussianFrameProjection (tripleTransportFrame L) (projectionEuclideanVector g)=
      L (tripleTransportCoordinate L g) := by
    rw [tripleTransportFrame_sum]
    unfold gaussianFrameProjection
    apply Finset.sum_congr rfl
    intro i _
    have he : tripleTransportCoordinate L g i=⟪tripleTransportFrame L i,projectionEuclideanVector g⟫_ℝ :=
      faceDot_eq_euclidean_inner _ _
    rw [he]
  rw [tripleTransportSection_eq_frame,gaussianFrameSectionPoint,← tripleTransportFrame_sum,hp,map_sub]
  module

theorem tripleTransportSection_active_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (Z : EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ k∈active,projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame L)))
    (hlevel : ∀ k∈active,⟪projectionEuclideanVector (u k),L Z⟫_ℝ=b k)
    (g : Vector r) (k : Fin m) (hk : k∈active) :
    faceDot (u k) (tripleTransportSection L Z g)=b k := by
  let S := Submodule.span ℝ (range (tripleTransportFrame L))
  have hi : ⟪projectionEuclideanVector (u k),(S.orthogonalProjection (projectionEuclideanVector g) : EuclideanSpace ℝ (Fin r))⟫_ℝ=
      ⟪projectionEuclideanVector (u k),projectionEuclideanVector g⟫_ℝ :=
    S.inner_orthogonalProjection_eq_of_mem_left ⟨_,hspan k hk⟩ _
  have he : faceDot (u k) (tripleTransportSection L Z g)=
      ⟪projectionEuclideanVector (u k),projectionEuclideanVector (tripleTransportSection L Z g)⟫_ℝ :=
    faceDot_eq_euclidean_inner _ _
  rw [he,tripleTransportSection_eq_affine_projection,inner_sub_right,inner_add_right,hi,hlevel k hk]
  ring

/-- The inactive inequalities are strict and every active equality is
proved from the actual normal-space point and its span. -/
theorem tripleConeEvent_exactStratum {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (Z : EuclideanSpace ℝ (Fin 3))
    (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (hspan : ∀ k∈active,projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame L)))
    (hlevel : ∀ k∈active,⟪projectionEuclideanVector (u k),L Z⟫_ℝ=b k)
    {g : Vector r} (hg : g∈tripleConeEvent L Z R u b (Finset.univ\active) (tripleOutwardNormalCone u active L)) :
    projectionEuclideanVector (tripleTransportSection L Z g)∈exactStratum
      (fun k => projectionEuclideanVector (u k)) b active := by
  have hactive := tripleTransportSection_active_levels u b active L Z hspan hlevel g
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k),projectionEuclideanVector (tripleTransportSection L Z g)⟫_ℝ=
      faceDot (u k) (tripleTransportSection L Z g) := (faceDot_eq_euclidean_inner _ _).symm
  change (∀ k,⟪_,_⟫_ℝ≤b k) ∧ ∀ k,⟪_,_⟫_ℝ=b k ↔ k∈active
  simp only [hd]
  constructor
  · intro k
    by_cases hk : k∈active
    · exact (hactive k hk).le
    · exact (hg.1 k (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hk⟩)).le
  · intro k
    constructor
    · intro he
      by_contra hk
      have hl := hg.1 k (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hk⟩)
      linarith
    · exact hactive k

/-- This is the actual nonnegative normal cone, so the complete fiber is
an outward tube based at the unique nearest point in its exact stratum. -/
theorem tripleConeEvent_mem_adaptiveOutwardTube {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (Z : EuclideanSpace ℝ (Fin 3))
    (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (hspan : ∀ k∈active,projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame L)))
    (hlevel : ∀ k∈active,⟪projectionEuclideanVector (u k),L Z⟫_ℝ=b k)
    {g : Vector r} (hg : g∈tripleConeEvent L Z R u b (Finset.univ\active) (tripleOutwardNormalCone u active L)) :
    projectionEuclideanVector g∈adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b R active := by
  obtain ⟨c,hc,he⟩ := hg.2.1
  have hx := tripleConeEvent_exactStratum u b active L Z R hspan hlevel hg
  refine ⟨projectionEuclideanVector (tripleTransportSection L Z g),hx,c,hc,?_,?_,?_⟩
  · rw [← he]
    intro hzero
    apply hg.2.2.2
    apply L.injective
    simpa only [map_zero] using hzero
  · rw [← he,L.norm_map]
    exact hg.2.2.1.le
  · rw [← he]
    exact tripleTransportSection_reconstruct L Z g

theorem tripleConeEvent_mem_outerLayer {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (active : Finset (Fin m))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (Z : EuclideanSpace ℝ (Fin 3))
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (hspan : ∀ k∈active,projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame L)))
    (hlevel : ∀ k∈active,⟪projectionEuclideanVector (u k),L Z⟫_ℝ=b k)
    {g : Vector r} (hg : g∈tripleConeEvent L Z R u b (Finset.univ\active) (tripleOutwardNormalCone u active L)) :
    g∈fourthOuterLayer u b R := by
  have ht := adaptiveOutwardTube_subset_outerLayer (fun k => projectionEuclideanVector (u k)) b
    (fun k => thresholdEuclideanNormal_unit _ (hu k)) R hR hRadd active
    (tripleConeEvent_mem_adaptiveOutwardTube u b active L Z R hspan hlevel hg)
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k),projectionEuclideanVector g⟫_ℝ=faceDot (u k) g :=
    (faceDot_eq_euclidean_inner _ _).symm
  change (∀ k,⟪_,_⟫_ℝ≤b k+_) ∧ ¬(∀ k,⟪_,_⟫_ℝ≤b k) at ht
  simpa only [hd] using ht

end
end RectangleCLTArxivV1
