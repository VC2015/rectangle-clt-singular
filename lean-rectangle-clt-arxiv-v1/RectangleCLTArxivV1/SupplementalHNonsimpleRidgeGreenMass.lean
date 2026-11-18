import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNative
import RectangleCLTArxivV1.SupplementalHTripleMass

/-! The genuine selected tangent-facet Gaussian mass is the full original
codimension-three affine section mass. Deleted inequalities are restored
by exact event equivalence, not generic threshold derivatives. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem ActualRidgeFacetPresentation.outwardConormal_orthogonal {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    faceDot (thresholdPairBisector u j l) (P.outwardConormal i) = 0 ∧
      faceDot (thresholdPairDifference u j l) (P.outwardConormal i) = 0 := by
  have h := hardPairResidualNormal_orthogonal (thresholdPairBisector u j l)
    (thresholdPairDifference u j l) (u (P.index i))
    (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
    (thresholdPair_frame_orthogonal u j l hu hv)
  have h' : faceDot (P.normals i) (thresholdPairBisector u j l) = 0 ∧
      faceDot (P.normals i) (thresholdPairDifference u j l) = 0 := h
  constructor
  · rw [faceDot_comm]
    change faceDot ((localFiniteThresholdScale P.normals i)⁻¹ • P.normals i)
      (thresholdPairBisector u j l) = 0
    rw [threshold_faceDot_smul_left, h'.1, mul_zero]
  · rw [faceDot_comm]
    change faceDot ((localFiniteThresholdScale P.normals i)⁻¹ • P.normals i)
      (thresholdPairDifference u j l) = 0
    rw [threshold_faceDot_smul_left, h'.2, mul_zero]

theorem ActualRidgeFacetPresentation.normal_eq_scale_conormal {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    P.normals i = localFiniteThresholdScale P.normals i • P.outwardConormal i := by
  have hpos := actualFacet_scale_pos P.normals P.levels P.strict P.irredundant i
  change P.normals i = localFiniteThresholdScale P.normals i •
    ((localFiniteThresholdScale P.normals i)⁻¹ • P.normals i)
  rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem ActualRidgeFacetPresentation.selected_support_on_section {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) (g : Vector r) :
    faceDot (P.normals i)
      (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g) = P.levels i := by
  have hpos := actualFacet_scale_pos P.normals P.levels P.strict P.irredundant i
  rw [P.normal_eq_scale_conormal i, threshold_faceDot_smul_left,
    gaussianSectionPoint_on_hyperplane _ _ (P.outwardConormal_unit i)]
  change localFiniteThresholdScale P.normals i *
    (P.levels i / localFiniteThresholdScale P.normals i) = P.levels i
  field_simp

theorem ActualRidgeFacetPresentation.section_event_iff_retained {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) (g : Vector r) :
    gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g ∈
        gaussianFiniteThresholdEvent (Finset.univ.erase i) P.normals P.levels ↔
      gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g ∈
        gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l)
          (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
          (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
            (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) := by
  classical
  let x := gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g
  change (∀ k ∈ Finset.univ.erase i, faceDot (P.normals k) x ≤ P.levels k) ↔ _
  constructor
  · intro hx
    apply (P.event_iff x).mp
    intro k
    by_cases hki : k = i
    · subst k
      exact (P.selected_support_on_section i g).le
    · exact hx k (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩)
  · intro hx k _
    exact (P.event_iff x).mpr hx k

theorem gaussianPairBase_mem_full_event_iff_residual {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (g : Vector r) :
    gaussianPairBase u b j l g ∈ gaussianFiniteThresholdEvent Finset.univ u b ↔
      g ∈ gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l)
        (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
        (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) := by
  have heq := gaussianPairSectionPoint_mem_event_iff ((Finset.univ.erase j).erase l) u b
    (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g
    (thresholdPair_frame_orthogonal u j l hu hv)
  change _ ↔ _ at heq
  rw [← heq]
  constructor
  · intro hx k hk
    exact hx k (Finset.mem_univ _)
  · intro hx k _
    by_cases hkj : k = j
    · subst k
      exact (gaussianPairBase_left_level u b j l hu hv hp.1 hp.2 g).le
    by_cases hkl : k = l
    · subst k
      exact (gaussianPairBase_right_level u b j l hu hv hp.1 hp.2 g).le
    exact hx k (Finset.mem_erase.mpr ⟨hkl, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩⟩)

theorem ActualRidgeFacetPresentation.section_event_iff_original {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) (g : Vector r) :
    gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g ∈
        gaussianFiniteThresholdEvent (Finset.univ.erase i) P.normals P.levels ↔
      gaussianPairBase u b j l (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g) ∈
        gaussianFiniteThresholdEvent Finset.univ u b :=
  (P.section_event_iff_retained i g).trans
    (gaussianPairBase_mem_full_event_iff_residual u b j l hu hv hp _).symm

theorem ActualRidgeFacetPresentation.normalDensity_mul_boundaryMass_eq_frameMass {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)) * P.boundaryMass i =
      gaussianFrameHardMass Finset.univ u b
        (nativeTripleFrame (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (P.outwardConormal i))
        (nativeTripleLevels (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
          (P.signedDistance i)) := by
  have horth := P.outwardConormal_orthogonal hu hv hp i
  have hprob : gaussianThresholdSectionProbability (Finset.univ.erase i) P.normals P.levels
      (P.outwardConormal i) (P.signedDistance i) =
      (standardGaussian r).real {g | gaussianPairBase u b j l
        (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) g) ∈
          gaussianFiniteThresholdEvent Finset.univ u b} := by
    rw [gaussianThresholdSectionProbability_eq_section]
    congr 1
    ext g
    exact P.section_event_iff_original hu hv hp i g
  change (_ * _) * (gaussianPDFReal 0 1 (P.signedDistance i) *
    gaussianThresholdSectionProbability (Finset.univ.erase i) P.normals P.levels
      (P.outwardConormal i) (P.signedDistance i)) = _
  rw [hprob]
  unfold gaussianFrameHardMass
  simp_rw [gaussianFrameSectionPoint_native_triple _ _ _
    (thresholdPair_frame_orthogonal u j l hu hv) horth.1 horth.2]
  simp only [nativeTripleLevels, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [gaussianPairBase, mul_assoc]

end
end RectangleCLTArxivV1
