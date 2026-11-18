import RectangleCLTArxivV1.SupplementalHTripleTransportIncidence
import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace

/-! The actual three-face radius discharges the normal-point and Gaussian
moment inputs of the rank-three conical transport. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem tripleTransport_normalPoint_norm_le_threeFaceRadius {p r : ℕ} (hp : 1≤p)
    (U : Face p → Vector r) (f : Fin 3 → Face p)
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (hspan : Submodule.span ℝ (range (tripleTransportFrame L))=
      Submodule.span ℝ (range (fun i => projectionEuclideanVector (U (f i)))))
    (Z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    ‖Z‖≤supplementalHRadius U (tripleTransportSection L Z g) := by
  let S := Submodule.span ℝ (range (tripleTransportFrame L))
  have hzmem : L Z∈S := by
    rw [tripleTransportFrame_sum]
    exact S.sum_mem (fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩))
  have hzmem' : L Z∈Submodule.span ℝ (range (fun i => projectionEuclideanVector (U (f i)))) := by
    change L Z∈Submodule.span ℝ (range (tripleTransportFrame L)) at hzmem
    rwa [hspan] at hzmem
  have hi : ⟪L Z,(S.orthogonalProjection (projectionEuclideanVector g) : EuclideanSpace ℝ (Fin r))⟫_ℝ=
      ⟪L Z,projectionEuclideanVector g⟫_ℝ := S.inner_orthogonalProjection_eq_of_mem_left ⟨_,hzmem⟩ _
  have hnormal : ⟪L Z,projectionEuclideanVector (tripleTransportSection L Z g)⟫_ℝ=‖Z‖^2 := by
    rw [tripleTransportSection_eq_affine_projection,inner_sub_right,inner_add_right,hi,
      real_inner_self_eq_norm_sq,L.norm_map]
    ring
  have hb := supplementalHRadius_abs_inner_small_span_le hp U f (by norm_num) (L Z) hzmem'
    (tripleTransportSection L Z g)
  rw [hnormal,abs_of_nonneg (sq_nonneg _),L.norm_map] at hb
  by_cases hz : ‖Z‖=0
  · rw [hz]
    exact (supplementalHRadius_pos U _).le
  · have hzpos : 0<‖Z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact le_of_mul_le_mul_left (by simpa only [pow_two] using hb) hzpos

/-- True rank-three conical coefficient transport with actual R3 radius:
no normal-point bound or integrability supplier is assumed. -/
theorem tripleCone_spherical_coefficient_le_threeFace_event {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin 3 → Face p)
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hspan : Submodule.span ℝ (range (tripleTransportFrame L))=
      Submodule.span ℝ (range (fun i => projectionEuclideanVector (U (f i)))))
    (Z : EuclideanSpace ℝ (Fin 3)) (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ,0<t → ∀ y : EuclideanSpace ℝ (Fin 3),t • y∈C ↔ y∈C)
    (u : Fin m → Vector (n+1)) (b : Vector m) (s : Finset (Fin m)) :
    (|⟪Z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C,ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ| *
      tripleEuclideanDensity Z)*(standardGaussian (n+1)).real
        {g | ∀ k∈s,faceDot (u k) (tripleTransportSection L Z g)<b k}≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,(tripleConeEvent L Z (fourthThreeFaceRadius U) u b s C).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) :=
  tripleCone_spherical_coefficient_le_fourth_event L Z C hC hcone (fourthThreeFaceRadius U)
    (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U) (fourthThreeFaceRadius_add_le U)
    u b s (fun g => tripleTransport_normalPoint_norm_le_threeFaceRadius hp U f L hspan Z g)
    (fourthThreeFaceRadius_fourth_integrable hp U)

end
end RectangleCLTArxivV1
