import RectangleCLTArxivV1.SupplementalHTripleTransportModelEvent

/-! Genuine factor-six transport over the actual independent triples.
No frames or levels are requested for dependent triples, so the result
also covers an empty family when the ambient normal rank is below three. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def independentNormalTripleTransportTuple {m r : ℕ} (u : Fin m → Vector r)
    (F : IndependentNormalTriple u) : TripleFaceTuple m :=
  tripleIncidenceTransportTuple u F.val F.property

theorem independentNormalTripleTransportTuple_injective {m r : ℕ} (u : Fin m → Vector r) :
    Function.Injective (independentNormalTripleTransportTuple u) := by
  intro F G he
  apply Subtype.ext
  exact congrArg (fun t : TripleFaceTuple m => t.val) he

theorem tripleIncidenceTransportEvent_integral_sum_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (hR4 : Integrable (fun g => R (projectionEuclideanVector g)^4) (standardGaussian r)) :
    (∑ F : IndependentNormalTriple u,∫ g,
      (tripleIncidenceTransportEvent u b F.val F.property (fun i => hu (F.val i)) R).indicator
        (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r)≤
      6*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r) := by
  classical
  have h := tripleOrderedEvent_integral_sum_le u b R hRm hR hRadd hu
    (independentNormalTripleTransportTuple u) (independentNormalTripleTransportTuple_injective u)
    (fun F => tripleIncidenceTransportIsometry u F.val F.property (fun i => hu (F.val i)))
    (fun F => tripleIncidenceTransportPoint u b F.val)
    (fun F => tripleIncidenceTransport_active_span u F.val F.property _)
    (fun F => tripleIncidenceTransport_active_levels u b F.val F.property _)
    (fun F => by
      dsimp only [independentNormalTripleTransportTuple]
      rw [← tripleIncidenceTransport_cone_eq]
      exact tripleIncidenceTransport_cone_measurableSet u F.val F.property _)
    hR4
  simpa only [tripleOrderedEvent,independentNormalTripleTransportTuple,
    ← tripleIncidenceTransportEvent_eq_outward] using h

/-- Actual three-face radius and moment discharge for the whole genuine
LI3 family.  All frames, supporting levels and cones are constructed. -/
theorem tripleIncidenceTransportEvent_threeFace_integral_sum_le {p m r : ℕ} (hp : 1≤p)
    (U : Face p → Vector r) (a : Fin m → Face p) (b : Vector m)
    (hu : ∀ k,vectorNormSq (U (a k))=1) :
    (∑ F : IndependentNormalTriple (fun k => U (a k)),∫ g,
      (tripleIncidenceTransportEvent (fun k => U (a k)) b F.val F.property
        (fun i => hu (F.val i)) (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian r)≤
      6*(∫ g,(fourthOuterLayer (fun k => U (a k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian r) :=
  tripleIncidenceTransportEvent_integral_sum_le (fun k => U (a k)) b (fourthThreeFaceRadius U)
    (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
    (fourthThreeFaceRadius_add_le U) hu (fourthThreeFaceRadius_fourth_integrable hp U)

end
end RectangleCLTArxivV1
