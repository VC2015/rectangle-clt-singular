import RectangleCLTArxivV1.SupplementalHTripleIncidenceTransport
import RectangleCLTArxivV1.SupplementalHTripleTransportModelEvent
import RectangleCLTArxivV1.SupplementalHRidgeIndependentGrouping
import RectangleCLTArxivV1.SupplementalHTripleTransportModelFamily
import RectangleCLTArxivV1.SupplementalHRidgeRegularity

/-! The actual signed ridge incidence coefficient, including every hard
inactive inequality, transported to its actual conical Gaussian event. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

theorem tripleIncidenceTransportSection_eq_native {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (g : Vector r) :
    tripleTransportSection (tripleIncidenceTransportIsometry u F hi hu)
      (tripleIncidenceTransportPoint u b F) g=
      gaussianPairSectionPoint (tripleIncidenceFirst u F 0) (tripleIncidenceSecond u F 0)
        (tripleIncidenceAlpha u b F 0) (tripleIncidenceBeta u b F 0)
        (gaussianSectionPoint (tripleIncidenceThird u F 0)
          (tripleIncidenceShift u b F 0/tripleIncidenceScale u F 0) g) := by
  obtain ⟨he,hf,hef⟩ := tripleIncidence_pair_geometry u F hi hu 0
  have hh := hardPairThirdDirection_geometry u _ _ he hf hef (F 0)
    (tripleIncidence_third_residual_ne_zero u F hi hu 0)
  apply (WithLp.equiv 2 (Vector r)).symm.injective
  change projectionEuclideanVector _=_
  rw [tripleTransportSection_eq_frame,tripleIncidenceTransportFrame_eq]
  simpa only [Equiv.symm_apply_apply] using congrArg (WithLp.equiv 2 (Vector r)).symm
    (gaussianFrameSectionPoint_native_triple _ _ _ hef hh.2.1 hh.2.2 _ _ _ g)

theorem tripleIncidenceTransportSection_ae_no_boundary {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (hreg : TripleIncidenceRegularity u b F) :
    ∀ᵐ g ∂standardGaussian r, ∀ k∈tripleIncidenceRemaining F,
      faceDot (u k) (tripleTransportSection (tripleIncidenceTransportIsometry u F hi hu)
        (tripleIncidenceTransportPoint u b F) g)≠b k := by
  let e := tripleIncidenceFirst u F 0
  let f := tripleIncidenceSecond u F 0
  let h := tripleIncidenceThird u F 0
  let a := tripleIncidenceAlpha u b F 0
  let c := tripleIncidenceBeta u b F 0
  let v := hardPairResidualNormals u e f
  let d := hardPairResidualLevels u b e f a c
  let t := tripleIncidenceShift u b F 0/tripleIncidenceScale u F 0
  have hlocal : ∀ k∈tripleIncidenceRemaining F,
      gaussianNormalProjection h (v k)≠0 ∨ d k-t*faceDot (v k) h≠0 := by
    rw [← tripleIncidence_remaining_eq F 0]
    exact (hreg 0 (F 0) (tripleIncidence_third_mem_pairFaces u F hi 0)).2
  have hn := gaussianFiniteThreshold_ae_no_boundary_of_slack (tripleIncidenceRemaining F)
    (fun k => gaussianNormalProjection h (v k)) (fun k => d k-t*faceDot (v k) h) hlocal
  filter_upwards [hn] with g hg
  intro k hk heq
  apply hg k hk
  rw [tripleIncidenceTransportSection_eq_native u b F hi hu] at heq
  change faceDot (u k) (gaussianPairSectionPoint e f a c (gaussianSectionPoint h t g))=b k at heq
  rw [gaussianPairSectionPoint_faceDot_residual e f (u k) a c _
    (tripleIncidence_pair_geometry u F hi hu 0).2.2,gaussianSectionPoint_faceDot] at heq
  change faceDot (gaussianNormalProjection h (v k)) g=d k-t*faceDot (v k) h
  dsimp only [d,hardPairResidualLevels,v,hardPairResidualNormals] at *
  linarith

theorem tripleIncidenceCommonMass_eq_strict_transport {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (hreg : TripleIncidenceRegularity u b F) :
    tripleIncidenceCommonMass u b F=
      tripleEuclideanDensity (tripleIncidenceTransportPoint u b F)*
      (standardGaussian r).real {g | ∀ k∈Finset.univ\tripleFaceActive
        (tripleIncidenceTransportTuple u F hi),
        faceDot (u k) (tripleTransportSection (tripleIncidenceTransportIsometry u F hi hu)
          (tripleIncidenceTransportPoint u b F) g)<b k} := by
  have hremaining : tripleIncidenceRemaining F=Finset.univ\tripleFaceActive
      (tripleIncidenceTransportTuple u F hi) := by
    classical
    ext k
    simp [tripleIncidenceRemaining,tripleFaceActive,tripleIncidenceTransportTuple,
      Finset.mem_image,not_exists,eq_comm]
  unfold tripleIncidenceCommonMass gaussianFrameHardMass
  have hd : (∏ i,gaussianPDFReal 0 1 (tripleIncidenceLevels u b F 0 i))=
      tripleEuclideanDensity (tripleIncidenceTransportPoint u b F) :=
    by simpa only [Fin.prod_univ_three] using
      (tripleEuclideanDensity_eq_scalarProduct (tripleIncidenceTransportPoint u b F)).symm
  rw [hd]
  congr 1
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [tripleIncidenceTransportSection_ae_no_boundary u b F hi hu hreg] with g hg
  have hp : WithLp.equiv 2 (Vector r) (gaussianFrameSectionPoint (tripleIncidenceFrame u F 0)
      (tripleIncidenceLevels u b F 0) ((WithLp.equiv 2 (Vector r)).symm g))=
      tripleTransportSection (tripleIncidenceTransportIsometry u F hi hu)
        (tripleIncidenceTransportPoint u b F) g := by
    have hh := tripleTransportSection_eq_frame (tripleIncidenceTransportIsometry u F hi hu)
      (tripleIncidenceTransportPoint u b F) g
    rw [tripleIncidenceTransportFrame_eq] at hh
    simpa [projectionEuclideanVector,tripleIncidenceTransportPoint] using
      (congrArg (WithLp.equiv 2 (Vector r)) hh).symm
  apply propext
  change (_∈gaussianFiniteThresholdEvent _ _ _)↔_
  rw [hp]
  change (∀ k∈tripleIncidenceRemaining F,_≤_)↔_
  rw [← hremaining]
  exact ⟨fun h k hk => lt_of_le_of_ne (h k hk) (hg k hk),fun h k hk => (h k hk).le⟩

/-- Each actual signed native incidence group is paid by its genuine
conical Gaussian event, after closed hard constraints are made strict
using the already present local threshold slack. -/
theorem hardGaussianRidgeThirdIncidenceGroup_threeFace_bound {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (a : Fin m → Face p) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => U (a (F i))))
    (hu : ∀ i, vectorNormSq (U (a (F i)))=1)
    (hreg : TripleIncidenceRegularity (fun k => U (a k)) b F) :
    |hardGaussianRidgeThirdIncidenceGroup (fun k => U (a k)) b (F 0) (F 1) (F 2)|≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,
        (tripleIncidenceTransportEvent (fun k => U (a k)) b F hi hu (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  rw [hardGaussianRidgeThirdIncidenceGroup_eq_spherical_vector _ b F hi hu hreg,
    abs_mul,abs_of_nonneg (tripleIncidenceCommonMass_nonneg _ b F),
    tripleIncidenceCommonMass_eq_strict_transport _ b F hi hu hreg]
  convert tripleIncidence_spherical_coefficient_le_threeFace_event hp U a b F hi hu using 1 <;> ring

/-- The true one-sixth signed incidence grouping cancels the proved
six-order geometric multiplicity. No matrix/surface estimate enters as
an assumption, and no frame is chosen for dependent triples. -/
theorem abs_hardGaussianRidgeThirdBoundaryIntegral_threeFace_tube_bound {p m n : ℕ}
    (hp : 1≤p) (U : Face p → Vector (n+1)) (a : Fin m → Face p) (b : Vector m)
    (hu : ∀ k,vectorNormSq (U (a k))=1)
    (hreg : AllPairResidualThresholdRegularity (fun k => U (a k)) b) :
    |hardGaussianRidgeThirdBoundaryIntegral (fun k => U (a k)) b|≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (a k)) b (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  classical
  let u := fun k => U (a k)
  have hz (F : Fin 3 → Fin m) (hdep : ¬LinearIndependent ℝ (fun i => u (F i))) :
      |hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)|=0 := by
    rw [hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent u b F hdep (fun i => hu (F i))
      (hreg.triple F),abs_zero]
  have hs := sum_cube_eq_independent_triples u
    (fun j l k => |hardGaussianRidgeThirdIncidenceGroup u b j l k|) hz
  have hb := abs_hardGaussianRidgeThirdBoundaryIntegral_le_groups u b
  rw [hs] at hb
  have hi := tripleIncidenceTransportEvent_threeFace_integral_sum_le hp U a b hu
  have hc : ∑ F : IndependentNormalTriple u,
      |hardGaussianRidgeThirdIncidenceGroup u b (F.val 0) (F.val 1) (F.val 2)|≤
      (6144*Real.exp ((3:ℝ)/2))*(∑ F : IndependentNormalTriple u,∫ g,
        (tripleIncidenceTransportEvent u b F.val F.property (fun i => hu (F.val i))
          (fourthThreeFaceRadius U)).indicator (fun g => supplementalHRadius U g^4) g
            ∂standardGaussian (n+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro F _
    exact hardGaussianRidgeThirdIncidenceGroup_threeFace_bound hp U a b F.val F.property
      (fun i => hu (F.val i)) (hreg.triple F.val)
  have h := hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/6))
  have hi' := mul_le_mul_of_nonneg_left hi
    (by positivity : 0≤(1/6:ℝ)*(6144*Real.exp ((3:ℝ)/2)))
  exact h.trans (by convert hi' using 1 <;> ring)

/-- The actual signed third boundary after affine standardization is
bounded by the physical base/Gaussian outward event with the same radius. -/
theorem abs_hardGaussianRidgeThirdBoundaryIntegral_affine_tube_bound {p m n : ℕ}
    (hp : 1≤p) (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    (x : Vector (n+1)) {σ : ℝ} (hσ : 0<σ) (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hreg : AllPairResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)) :
    |hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)|≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,
        (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
          (fun z => supplementalHRadius U z.2^4) (x,g) ∂standardGaussian (n+1)) := by
  have hh := abs_hardGaussianRidgeThirdBoundaryIntegral_threeFace_tube_bound hp U f
    (fun k => (a k-faceDot (U (f k)) x)/σ) hu hreg
  apply hh.trans_eq
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have he := fourthOuterLayer_shift_threshold (fun k => U (f k)) a x hσ (fourthThreeFaceRadius U) g
    change g∈fourthOuterLayer (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U) ↔
      (x,g)∈gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U) at he
    by_cases hg : g∈fourthOuterLayer (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U)
    · rw [indicator_of_mem hg,indicator_of_mem (he.mp hg)]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (he.mpr h))])

end
end RectangleCLTArxivV1
