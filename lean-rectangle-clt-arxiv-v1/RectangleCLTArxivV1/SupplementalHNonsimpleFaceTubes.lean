import RectangleCLTArxivV1.SupplementalHNonsimpleFaceNormalCone
import RectangleCLTArxivV1.SupplementalHTripleTransportGeometry

/-! Actual codimension-three normal events are indexed once by their
complete active face. Their nearest-base tubes are disjoint, even when
more than three original facets meet. No ordered-triple multiplicity is
introduced. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev NonsimpleCodimThreeFace {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) :=
  NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3

def nonsimpleFaceNormalEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (L : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3))
    (H : NonsimpleCodimThreeFace u b) : Set (Vector r) :=
  tripleConeEvent (L H) (Z H) R u b (Finset.univ\H.1)
    (tripleOutwardNormalCone u H.1 (L H))

theorem nonsimpleFaceNormalEvent_disjoint {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (L : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ H k,k∈H.1 → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L H))))
    (hlevel : ∀ H k,k∈H.1 → ⟪projectionEuclideanVector (u k),L H (Z H)⟫_ℝ=b k)
    (H G : NonsimpleCodimThreeFace u b) (hHG : H≠G) :
    Disjoint (nonsimpleFaceNormalEvent u b R L Z H) (nonsimpleFaceNormalEvent u b R L Z G) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := tripleConeEvent_mem_adaptiveOutwardTube u b H.1 (L H) (Z H) R (hspan H) (hlevel H) hx
  have hg := tripleConeEvent_mem_adaptiveOutwardTube u b G.1 (L G) (Z G) R (hspan G) (hlevel G) hy
  have hne : H.1≠G.1 := fun h => hHG (Subtype.ext h)
  exact Set.disjoint_left.mp
    (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b R hne) hh hg

theorem nonsimpleFaceNormalEvent_indicator_sum_le {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (L : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ H k,k∈H.1 → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L H))))
    (hlevel : ∀ H k,k∈H.1 → ⟪projectionEuclideanVector (u k),L H (Z H)⟫_ℝ=b k)
    (P : Vector r → ℝ) (hP : ∀ x,0≤P x) (x : Vector r) :
    (∑ H : NonsimpleCodimThreeFace u b,(nonsimpleFaceNormalEvent u b R L Z H).indicator P x)≤
      (fourthOuterLayer u b R).indicator P x := by
  classical
  by_cases hex : ∃ H,x∈nonsimpleFaceNormalEvent u b R L Z H
  · obtain ⟨H,hx⟩ := hex
    have hout := tripleConeEvent_mem_outerLayer u b H.1 (L H) (Z H) R hR hRadd hu (hspan H) (hlevel H) hx
    have hzero (G : NonsimpleCodimThreeFace u b) (hGH : G≠H) :
        (nonsimpleFaceNormalEvent u b R L Z G).indicator P x=0 := by
      apply indicator_of_not_mem
      intro hg
      exact Set.disjoint_left.mp (nonsimpleFaceNormalEvent_disjoint u b R L Z hspan hlevel G H hGH) hg hx
    rw [Finset.sum_eq_single H (fun G _ hGH => hzero G hGH) (by simp),indicator_of_mem hx,indicator_of_mem hout]
  · have hn H : x∉nonsimpleFaceNormalEvent u b R L Z H := fun h => hex ⟨H,h⟩
    simp only [indicator_of_not_mem (hn _),Finset.sum_const_zero]
    exact indicator_nonneg (fun y _ => hP y) x

theorem nonsimpleFaceNormalEvent_integral_sum_le {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (L : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : NonsimpleCodimThreeFace u b → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ H k,k∈H.1 → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L H))))
    (hlevel : ∀ H k,k∈H.1 → ⟪projectionEuclideanVector (u k),L H (Z H)⟫_ℝ=b k)
    (hC : ∀ H,MeasurableSet (tripleOutwardNormalCone u H.1 (L H)))
    (hR4 : Integrable (fun g => R (projectionEuclideanVector g)^4) (standardGaussian r)) :
    (∑ H : NonsimpleCodimThreeFace u b,∫ g,(nonsimpleFaceNormalEvent u b R L Z H).indicator
      (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r)≤
      ∫ g,(fourthOuterLayer u b R).indicator (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r := by
  classical
  have hi H : Integrable ((nonsimpleFaceNormalEvent u b R L Z H).indicator
      (fun g => R (projectionEuclideanVector g)^4)) (standardGaussian r) :=
    hR4.indicator (measurableSet_tripleConeEvent (L H) (Z H) R hRm u b _ _ (hC H))
  rw [←integral_finset_sum Finset.univ (fun H _ => hi H)]
  exact integral_mono (integrable_finset_sum _ (fun H _ => hi H))
    (hR4.indicator (measurableSet_fourthOuterLayer u b R hRm))
    (fun x => nonsimpleFaceNormalEvent_indicator_sum_le u b R hR hRadd hu L Z hspan hlevel _
      (fun x => pow_nonneg (zero_le_one.trans (hR _)) 4) x)

end
end RectangleCLTArxivV1
