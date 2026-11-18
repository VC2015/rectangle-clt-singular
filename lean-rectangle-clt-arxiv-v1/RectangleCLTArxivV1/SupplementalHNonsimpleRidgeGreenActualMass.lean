import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenFrame
import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass

/-! A selected ridge boundary has the canonical mass and normal-space
point of the complete actual codimension-three face, even when more than
three original facets are active there. Three active normals determine
the rank-three normal space; no cardinality-three hypothesis is imposed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem ActualRidgeFacetPresentation.nativeBoundaryFrame_span_actualFace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (hj : j ∈ H.1) (hl : l ∈ H.1) (hk : P.index i ∈ H.1) :
    Submodule.span ℝ (Set.range (P.nativeBoundaryFrame i)) =
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1 := by
  have hle : Submodule.span ℝ (Set.range (P.nativeBoundaryFrame i)) ≤
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1 := by
    rw [P.nativeBoundaryFrame_span hu hv hp i]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · exact nonsimple_normal_mem (nonsimpleNativeNormals u) H.1 j hj
    · exact nonsimple_normal_mem (nonsimpleNativeNormals u) H.1 l hl
    · exact nonsimple_normal_mem (nonsimpleNativeNormals u) H.1 (P.index i) hk
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card (P.nativeBoundaryFrame_orthonormal hu hv hp i).linearIndependent, H.2.2]
  simp only [Fintype.card_fin]

theorem ActualRidgeFacetPresentation.nativeBoundaryPoint_eq_actualFaceNormalPoint {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (hj : j ∈ H.1) (hl : l ∈ H.1) (hk : P.index i ∈ H.1) :
    P.nativeBoundaryPoint i = nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H := by
  have hspan := (P.nativeBoundaryFrame_span hu hv hp i).symm.trans
    (P.nativeBoundaryFrame_span_actualFace hu hv hp i H hj hl hk)
  have hz : nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H ∈
      Submodule.span ℝ (Set.range (nativeTripleFrame (u j) (u l) (u (P.index i)))) := by
    rw [hspan]
    exact nonsimpleFaceNormalPoint_mem _ _ H
  apply normalPoint_eq_of_spanning_levels (nativeTripleFrame (u j) (u l) (u (P.index i)))
    _ _ (P.nativeBoundaryPoint_mem_span hu hv hp i) hz
  have hlevels := P.nativeBoundaryPoint_supporting_levels hu hv hp i
  intro a
  fin_cases a
  · exact hlevels.1.trans (nonsimpleFaceNormalPoint_levels _ _ H j hj).symm
  · exact hlevels.2.1.trans (nonsimpleFaceNormalPoint_levels _ _ H l hl).symm
  · exact hlevels.2.2.trans (nonsimpleFaceNormalPoint_levels _ _ H (P.index i) hk).symm

/-- The local selected-facet mass is the one canonical Gaussian mass of
the complete original codimension-three face. All original inequalities
are retained in both descriptions. -/
theorem ActualRidgeFacetPresentation.normalDensity_mul_boundaryMass_eq_actualFaceMass {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (hj : j ∈ H.1) (hl : l ∈ H.1) (hk : P.index i ∈ H.1) :
    (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)) * P.boundaryMass i =
      nonsimpleActualGaussianMass u b H := by
  rw [P.normalDensity_mul_boundaryMass_eq_frameMass hu hv hp i]
  apply gaussianFrameHardMass_eq_actualFaceMass u b H
    (P.nativeBoundaryFrame i) (P.nativeBoundaryFrame_orthonormal hu hv hp i)
    (P.nativeBoundaryLevels i) (P.nativeBoundaryFrame_span_actualFace hu hv hp i H hj hl hk)
  intro k hkm
  change ⟪nonsimpleNativeNormals u k, P.nativeBoundaryPoint i⟫_ℝ = b k
  rw [P.nativeBoundaryPoint_eq_actualFaceNormalPoint hu hv hp i H hj hl hk]
  exact nonsimpleFaceNormalPoint_levels _ _ H k hkm

end
end RectangleCLTArxivV1
