import RectangleCLTCompanion.SplitV4.Printed.EndpointMixture
import RectangleCLTCompanion.SplitV4.Concentration
import RectangleCLTCompanion.SplitV4.SignedCoordinateMoments

/-! Instantiation of the actual Lemma 1 at the random-threshold endpoint.
No endpoint smoothing conclusion is used as an input. -/
open MeasureTheory ProbabilityTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem signed_coordinate_layer_eq {p : ℕ} (s : FaceSmoother p)
    (hs : s.faces = Finset.univ) (r : ℝ) :
    gaussianPolyhedronLayer (signedCoordinateRows p) (signedCoordinateThresholds s) r =
      s.boundaryLayer r := by
  have he (t : ℝ) : facePolyhedron (signedCoordinateRows p)
      (fun α => signedCoordinateThresholds s α+t) = s.outerSet t := by
    ext x
    simp only [facePolyhedron, FaceSmoother.outerSet, hs, Finset.mem_univ, forall_true_left]
    constructor
    · intro hx f
      have h := hx ((signedCoordinateFaceEquiv p).symm f)
      change faceDot (signedCoordinateRows p ((signedCoordinateFaceEquiv p).symm f)) x ≤ _ at h
      simpa only [signedCoordinateThresholds, signedCoordinateRows_projection,
        Equiv.apply_symm_apply] using h
    · intro hx α
      change faceDot (signedCoordinateRows p α) x ≤ _
      simpa only [signedCoordinateThresholds, signedCoordinateRows_projection] using
        hx (signedCoordinateFaceEquiv p α)
  unfold gaussianPolyhedronLayer
  rw [he r]
  have hn : (fun α => signedCoordinateThresholds s α-r) =
      (fun α => signedCoordinateThresholds s α+(-r)) := by funext α; ring
  rw [hn,he (-r)]
  rfl

theorem bounded_boundary_layer_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hb : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hs : s.faces = Finset.univ) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | sumVector ξ ω ∈ s.boundaryLayer r} ≤
      512*(r+δ)*Real.sqrt (dimensionLog p) := by
  letI : NeZero p := ⟨by omega⟩
  have hξi (i : Fin n) : Integrable (ξ i) μ :=
    (integrable_const δ).mono' (hb.measurable i).aestronglyMeasurable (hb.bounded i)
  have hcenter (i : Fin n) : (∫ ω, ξ i ω ∂μ) = 0 := by
    ext j
    have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm (hξi i)
    simpa only [ContinuousLinearMap.proj_apply, hb.centered i j, Pi.zero_apply] using he.symm
  have hbound (i : Fin n) : ∀ᵐ ω ∂μ,
      faceProjectionNorm (signedCoordinateRows p) (ξ i ω) ≤ δ := by
    simpa only [signedCoordinateRows_faceProjectionNorm] using hb.bounded i
  have hv (α : Fin (2*p)) : variance
      (fun ω => dotProduct (signedCoordinateRows p α) (sumVector ξ ω)) μ = 1 :=
    (signedCoordinateRows_variance_sum μ ξ hb α).trans (hunit _)
  have hc := bounded_face_intrinsic_concentration_signed_faces μ (signedCoordinateRows p)
    ξ hb.measurable hb.independent hξi hcenter hb.delta_nonneg (by norm_num : (0:ℝ)<1)
    hbound hv (fun _ => 0) measurable_const (indepFun_constant_right μ (sumVector ξ) 0)
    (signedCoordinateThresholds s) hr
  rw [signed_coordinate_layer_eq s hs] at hc
  simp only [add_zero, div_one] at hc
  apply hc.trans
  have hm : min 1 (min (((r+δ)*∫ ω, faceProjectionNorm (signedCoordinateRows p) (sumVector ξ ω) ∂μ))
      ((r+δ)*Real.sqrt (dimensionLog p))) ≤ (r+δ)*Real.sqrt (dimensionLog p) :=
    (min_le_right _ _).trans (min_le_right _ _)
  nlinarith

theorem gaussian_boundary_layer_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (s : FaceSmoother p) (hs : s.faces = Finset.univ) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianLaw A).real (s.boundaryLayer r) ≤ 512*r*Real.sqrt (dimensionLog p) := by
  letI : NeZero p := ⟨by omega⟩
  have hv (α : Fin (2*p)) : dotProduct (signedCoordinateRows p α)
      ((A*A.transpose).mulVec (signedCoordinateRows p α)) = 1 :=
    (signedCoordinateRows_quadratic _ α).trans (hdiag _)
  have hc := (gaussian_intrinsic_concentration_signed_faces (gaussianLaw A)
    id (fun _ => 0) measurable_id measurable_const
    (indepFun_constant_right (gaussianLaw A) id 0)
    (signedCoordinateRows p) A (by simp) (signedCoordinateThresholds s)
    (by norm_num : (0:ℝ)<1) hr hv).2
  rw [signed_coordinate_layer_eq s hs] at hc
  simp only [id_eq, add_zero, div_one] at hc
  exact hc.trans (by nlinarith [min_le_right (1:ℝ) (r*Real.sqrt (dimensionLog p))])

end
end RectangleCLT.Companion.SplitV4.Printed
