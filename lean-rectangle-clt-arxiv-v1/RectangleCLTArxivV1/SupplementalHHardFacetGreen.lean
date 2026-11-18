import RectangleCLTArxivV1.SupplementalHSurfaceMeasure
import RectangleCLTCompanion.SplitV4.GaussianThresholdIdentity
import RectangleCLTCompanion.SplitV4.Printed.GammaDifferentiation

/-! The hard-facet signed Gaussian Green identity. The surface measure is
constructed from an orthogonal Euclidean chart; the proof reuses the
archive's genuine threshold derivatives and radial scaling, rather than
assuming a polyhedral surface functional identity. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SignedSurface
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- The actual Gaussian signed score integrated over the hard facet on
`u_j⋅x=b_j`. The ambient polyhedron supplies every remaining inequality. -/
def hardGaussianFacetIntegral {m n : ℕ} (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) : ℝ :=
  ∫ x in gaussianFiniteThresholdEvent Finset.univ u b,
    (vectorNormSq x-((n+1:ℕ):ℝ))*standardGaussianDensity (n+1) x
    ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j)

/-- Exact identification of the genuine hard-facet surface integral with
the existing concrete signed Gaussian section. -/
theorem hardGaussianFacetIntegral_eq_signedSection {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    hardGaussianFacetIntegral u b j=
      gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u b j (b j) := by
  let P := gaussianFiniteThresholdEvent Finset.univ u b
  let Q := gaussianFiniteThresholdEvent (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j))
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have he (g : Vector (n+1)) : gaussianSectionPoint (u j) (b j) g ∈ P ↔ g ∈ Q := by
    constructor
    · intro h l hl
      have hh := h l (Finset.mem_univ _)
      rw [gaussianSectionPoint_faceDot] at hh
      change faceDot (gaussianNormalProjection (u j) (u l)) g≤b l-b j*faceDot (u l) (u j)
      linarith
    · intro h l _
      by_cases hlj : l=j
      · subst l
        rw [gaussianSectionPoint_on_hyperplane (u j) (b j) hu]
      · have hh := h l (Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩)
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
  unfold hardGaussianFacetIntegral
  rw [hardFacet_signed_surface_eq_section _ _ hu _ _ hP]
  congr 1
  rw [←integral_indicator hP]
  unfold gaussianSectionLaw
  have hscore : Measurable (P.indicator (fun x : Vector (n+1) => vectorNormSq x-((n+1:ℕ):ℝ))) := by
    apply Measurable.indicator _ hP
    unfold vectorNormSq
    fun_prop
  rw [integral_map (measurable_gaussianSectionPoint (u j) (b j)).aemeasurable hscore.aestronglyMeasurable]
  unfold Printed.thresholdSignedSection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change P.indicator (fun x => vectorNormSq x-((n+1:ℕ):ℝ)) (gaussianSectionPoint (u j) (b j) g)=
      Q.indicator (fun x => vectorNormSq (gaussianSectionPoint (u j) (b j) x)-((n+1:ℕ):ℝ)) g
    by_cases hg : g ∈ Q
    · rw [Set.indicator_of_mem ((he g).mpr hg),Set.indicator_of_mem hg]
    · rw [Set.indicator_of_not_mem (fun hp => hg ((he g).mp hp)),Set.indicator_of_not_mem hg])

/-- The genuine hard-facet Gauss–Green formula, initially for a linearly
independent normal family so every threshold derivative is continuous.
The residual coefficient is the actual tangential ridge distance times
the Gaussian mixed-threshold density. -/
theorem hardGaussianFacet_Green_independent {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : ∀ k, vectorNormSq (u k)=1) (hi : LinearIndependent ℝ u) :
    hardGaussianFacetIntegral u b j=
      (b j^2-1)*gaussianThresholdFirst u b j-
      ∑ l ∈ Finset.univ.erase j,
        (b l-faceDot (u j) (u l)*b j)*gaussianThresholdMixed u b j l := by
  classical
  rw [hardGaussianFacetIntegral_eq_signedSection u b j (hu j)]
  have he := (Printed.hasDerivAt_gaussianThresholdTrace_update_printed u b j (hu j) hi (b j)).unique
    (hasDerivAt_gaussianThresholdTrace_update u b j hu hi)
  rw [he]
  simp_rw [gaussianThresholdMixed_symm u b hu hi]
  have hsplit : (∑ l, b l*gaussianThresholdMixed u b j l)=
      b j*gaussianThresholdMixed u b j j+
      ∑ l ∈ Finset.univ.erase j, b l*gaussianThresholdMixed u b j l := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm.trans (add_comm _ _)
  rw [hsplit,gaussianThreshold_diagonal_identity u b j (hu j) hi]
  have hs : (∑ l ∈ Finset.univ.erase j,
      (b l-faceDot (u j) (u l)*b j)*gaussianThresholdMixed u b j l)=
      (∑ l ∈ Finset.univ.erase j, b l*gaussianThresholdMixed u b j l)-
      b j*(∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l)*gaussianThresholdMixed u b j l) := by
    simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hs]
  ring

end
end RectangleCLTArxivV1
