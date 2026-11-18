import RectangleCLTArxivV1.SupplementalHTripleTransportModelCone

/-! Actual conical events and their three-face-radius transport, with all
frame, level, cone, and normal-point inputs discharged from the selected
independent original normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tripleIncidenceTransportEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (R : EuclideanSpace ℝ (Fin r) → ℝ) : Set (Vector r) :=
  tripleConeEvent (tripleIncidenceTransportIsometry u F hi hu) (tripleIncidenceTransportPoint u b F)
    R u b (Finset.univ\tripleFaceActive (tripleIncidenceTransportTuple u F hi))
    (trihedralGeneratedCone (tripleIncidenceTransportBasis u F hi hu))

theorem tripleIncidenceTransportEvent_eq_outward {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (R : EuclideanSpace ℝ (Fin r) → ℝ) :
    tripleIncidenceTransportEvent u b F hi hu R=
      tripleConeEvent (tripleIncidenceTransportIsometry u F hi hu) (tripleIncidenceTransportPoint u b F)
        R u b (Finset.univ\tripleFaceActive (tripleIncidenceTransportTuple u F hi))
        (tripleOutwardNormalCone u (tripleFaceActive (tripleIncidenceTransportTuple u F hi))
          (tripleIncidenceTransportIsometry u F hi hu)) := by
  unfold tripleIncidenceTransportEvent
  rw [tripleIncidenceTransport_cone_eq]

theorem tripleIncidenceTransportEvent_measurableSet {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R) :
    MeasurableSet (tripleIncidenceTransportEvent u b F hi hu R) :=
  measurableSet_tripleConeEvent _ _ _ hR _ _ _ _ (tripleIncidenceTransport_cone_measurableSet u F hi hu)

theorem tripleIncidenceTransportEvent_exactStratum {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (R : EuclideanSpace ℝ (Fin r) → ℝ)
    {g : Vector r} (hg : g∈tripleIncidenceTransportEvent u b F hi hu R) :
    projectionEuclideanVector (tripleTransportSection (tripleIncidenceTransportIsometry u F hi hu)
      (tripleIncidenceTransportPoint u b F) g)∈exactStratum
        (fun k => projectionEuclideanVector (u k)) b
        (tripleFaceActive (tripleIncidenceTransportTuple u F hi)) := by
  rw [tripleIncidenceTransportEvent_eq_outward] at hg
  exact tripleConeEvent_exactStratum u b _ _ _ R
    (tripleIncidenceTransport_active_span u F hi hu)
    (tripleIncidenceTransport_active_levels u b F hi hu) hg

theorem tripleIncidenceTransportEvent_mem_adaptiveOutwardTube {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (R : EuclideanSpace ℝ (Fin r) → ℝ)
    {g : Vector r} (hg : g∈tripleIncidenceTransportEvent u b F hi hu R) :
    projectionEuclideanVector g∈adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b R
      (tripleFaceActive (tripleIncidenceTransportTuple u F hi)) := by
  rw [tripleIncidenceTransportEvent_eq_outward] at hg
  exact tripleConeEvent_mem_adaptiveOutwardTube u b _ _ _ R
    (tripleIncidenceTransport_active_span u F hi hu)
    (tripleIncidenceTransport_active_levels u b F hi hu) hg

theorem tripleIncidenceTransportEvent_mem_outerLayer {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ k, vectorNormSq (u k)=1) (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (hR : ∀ x,1≤R x) (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    {g : Vector r} (hg : g∈tripleIncidenceTransportEvent u b F hi (fun i => hu (F i)) R) :
    g∈fourthOuterLayer u b R := by
  rw [tripleIncidenceTransportEvent_eq_outward] at hg
  exact tripleConeEvent_mem_outerLayer u b _ _ _ R hR hRadd hu
    (tripleIncidenceTransport_active_span u F hi _)
    (tripleIncidenceTransport_active_levels u b F hi _) hg

/-- This specialization constructs the conditioning frame and cone from
the actual selected signed normals, and discharges the actual radius and
Gaussian moment inputs.  No geometric identification is assumed. -/
theorem tripleIncidence_spherical_coefficient_le_threeFace_event {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (a : Fin m → Face p) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => U (a (F i))))
    (hu : ∀ i, vectorNormSq (U (a (F i)))=1) :
    (|⟪tripleIncidenceTransportPoint (fun k => U (a k)) b F,
        (2:ℝ) • ∫ ω in supplementalHSphericalSection
          (trihedralGeneratedCone (tripleIncidenceTransportBasis (fun k => U (a k)) F hi hu)),
            ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ| *
      tripleEuclideanDensity (tripleIncidenceTransportPoint (fun k => U (a k)) b F))*
      (standardGaussian (n+1)).real {g | ∀ k∈Finset.univ\tripleFaceActive
        (tripleIncidenceTransportTuple (fun k => U (a k)) F hi),
        faceDot (U (a k)) (tripleTransportSection (tripleIncidenceTransportIsometry (fun k => U (a k)) F hi hu)
          (tripleIncidenceTransportPoint (fun k => U (a k)) b F) g)<b k}≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,
        (tripleIncidenceTransportEvent (fun k => U (a k)) b F hi hu (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  apply tripleCone_spherical_coefficient_le_threeFace_event hp U (fun i => a (F i))
    (tripleIncidenceTransportIsometry (fun k => U (a k)) F hi hu)
  · exact tripleIncidenceTransportFrame_span _ F hi hu
  · exact tripleIncidenceTransport_cone_measurableSet _ F hi hu
  · exact tripleIncidenceTransport_cone_smul_iff _ F hi hu

end
end RectangleCLTArxivV1
