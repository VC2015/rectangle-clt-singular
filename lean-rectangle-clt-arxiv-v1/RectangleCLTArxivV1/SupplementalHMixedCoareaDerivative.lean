import RectangleCLTArxivV1.SupplementalHMixedCoareaRegularity
import RectangleCLTArxivV1.SupplementalHMixedCoareaCoordinates
import RectangleCLTArxivV1.SupplementalHResidualGreen

/-! The actual local signed mixed Gaussian coarea derivative. Only the
selected pair's local double-residual slack is required. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- Ordinary boundary nullity in the actual double residual section,
without differentiability or full-family independence assumptions. -/
def MixedGaussianSectionSlack {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : Prop :=
  ∀ k∈(Finset.univ.erase j).erase l,
    gaussianNormalProjection (gaussianPairConditionalDirection u j l)
      (gaussianNormalProjection (u j) (u k))≠0 ∨
    (b k-b j*faceDot (u k) (u j))-
      gaussianPairConditionalLevel u b j l*
        faceDot (gaussianNormalProjection (u j) (u k)) (gaussianPairConditionalDirection u j l)≠0

theorem hasDerivAt_thresholdSignedSection_update_conditional_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => Printed.thresholdSignedSection u (Function.update b l z) j (b j))
      ((gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/gaussianThresholdResidualScale u j l)*
        hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b (u j)
          (gaussianPairConditionalDirection u j l) (b j) (gaussianPairConditionalLevel u b j l)) (b l) := by
  classical
  let s := Finset.univ.erase j
  let v := fun k => gaussianNormalProjection (u j) (u k)
  let d := fun k => b k-b j*faceDot (u k) (u j)
  let q := gaussianPairConditionalDirection u j l
  let ν := gaussianThresholdResidualScale u j l
  let F := gaussianFacetScore (u j) (b j)
  obtain ⟨hq,heq,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hl : l∈s := Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩
  have hul : v l=ν • q := by
    change v l=ν • (ν⁻¹ • v l)
    rw [smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  have hcont := continuousAt_gaussianFiniteWeightedSection_score_of_slack (s.erase l) v d
    (u j) q hu hq heq (b j) (d l/ν) hreg
  have hd := hasDerivAt_gaussianFiniteWeightedThreshold_update s v d l hl q hq hν hul F
    (measurable_gaussianFacetScore _ _) (integrable_gaussianFacetScore _ hu _) (d l) hcont
  have hd' := hd.comp (b l) ((hasDerivAt_id (b l)).sub_const (b j*faceDot (u l) (u j)))
  have hefun (z : ℝ) : Printed.thresholdSignedSection u (Function.update b l z) j (b j)=
      gaussianFiniteWeightedThreshold s v (Function.update d l (z-b j*faceDot (u l) (u j))) F := by
    have hethreshold : (fun k => Function.update b l z k-b j*faceDot (u k) (u j))=
        Function.update d l (z-b j*faceDot (u l) (u j)) := by
      funext k
      by_cases hkl : k=l
      · subst k
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hkl]
        rfl
    unfold Printed.thresholdSignedSection
    change gaussianFiniteWeightedThreshold s v (fun k => Function.update b l z k-b j*faceDot (u k) (u j)) F=_
    rw [hethreshold]
  have hsect : gaussianFiniteWeightedSection (s.erase l) v d q F (d l/ν)=
      hardGaussianPairSignedSection (s.erase l) u b (u j) q (b j) (d l/ν) := by
    unfold gaussianFiniteWeightedSection hardGaussianPairSignedSection
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      have hiff : gaussianPairSectionPoint (u j) q (b j) (d l/ν) g∈gaussianFiniteThresholdEvent (s.erase l) u b ↔
          gaussianSectionPoint q (d l/ν) g∈gaussianFiniteThresholdEvent (s.erase l) v d := by
        constructor <;> intro h k hk
        · have hh := h k hk
          change faceDot (u k) (gaussianSectionPoint (u j) (b j) (gaussianSectionPoint q (d l/ν) g))≤b k at hh
          rw [gaussianSectionPoint_faceDot] at hh
          change faceDot (v k) (gaussianSectionPoint q (d l/ν) g)≤d k
          dsimp only [d]
          linarith
        · have hh := h k hk
          change faceDot (u k) (gaussianSectionPoint (u j) (b j) (gaussianSectionPoint q (d l/ν) g))≤b k
          rw [gaussianSectionPoint_faceDot]
          change faceDot (v k) (gaussianSectionPoint q (d l/ν) g)≤d k at hh
          dsimp only [d] at hh
          linarith
      dsimp only
      by_cases hg : gaussianSectionPoint q (d l/ν) g∈gaussianFiniteThresholdEvent (s.erase l) v d
      · rw [indicator_of_mem hg,indicator_of_mem (hiff.mpr hg)]
        rfl
      · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (hiff.mp h))])
  have hh := hd'.congr_of_eventuallyEq (Eventually.of_forall hefun)
  rw [hsect] at hh
  simpa only [mul_one] using hh

/-- The derivative of the actual signed first-facet Gaussian density in
an independent second threshold is the actual signed two-normal hard
section divided by its exact Gram determinant square root. -/
theorem hasDerivAt_gaussianSignedFacetDensity_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : MixedGaussianSectionSlack u b j l) :
    HasDerivAt (fun z => gaussianPDFReal 0 1 (b j)*
      Printed.thresholdSignedSection u (Function.update b l z) j (b j))
      ((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
        hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b
          (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) (b l) := by
  have hd := (hasDerivAt_thresholdSignedSection_update_conditional_of_slack u b j l hjl hu hv hp hm hreg).const_mul
    (gaussianPDFReal 0 1 (b j))
  rwa [hardGaussianConditionalMixedSignedSection_nested_eq_pairSection u b j l hu hv hp hm] at hd

/-- Ordinary first-facet residual regularity supplies precisely the
selected pair's local double-residual boundary slack. -/
theorem ResidualThresholdRegularity.mixedGaussianSectionSlack {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (h : ResidualThresholdRegularity u b j) (hlj : l≠j) : MixedGaussianSectionSlack u b j l :=
  (h l (Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩)).2

/-- All actual signed mixed facet derivatives hold simultaneously
outside an ordinary threshold-volume null set for arbitrary dependent
unit normal families. Only the selected pair is nonparallel. -/
theorem ae_hasDerivAt_gaussianSignedFacetDensity_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume,∀ j l, j≠l →
      projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 →
      HasDerivAt (fun z => gaussianPDFReal 0 1 (b j)*
        Printed.thresholdSignedSection u (Function.update b l z) j (b j))
        ((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
          gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
          hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b
            (thresholdPairBisector u j l) (thresholdPairDifference u j l)
            (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) (b l) := by
  filter_upwards [ae_residualThresholdRegularity u] with b hb
  intro j l hjl hp hm
  exact hasDerivAt_gaussianSignedFacetDensity_update_of_slack u b j l hjl (hu j) (hu l) hp hm
    ((hb j).mixedGaussianSectionSlack hjl.symm)

end
end RectangleCLTArxivV1
