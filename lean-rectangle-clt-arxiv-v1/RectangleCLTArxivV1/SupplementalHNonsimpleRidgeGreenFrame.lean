import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenMass

/-! The actual selected ridge-boundary frame and its supporting point.
Only the selected residual facet is required to be nonzero; no linear
independence hypothesis on the entire original family is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ActualRidgeFacetPresentation.nativeBoundaryFrame {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    Fin 3 → EuclideanSpace ℝ (Fin r) :=
  nativeTripleFrame (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (P.outwardConormal i)

def ActualRidgeFacetPresentation.nativeBoundaryLevels {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) : Fin 3 → ℝ :=
  nativeTripleLevels (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
    (P.signedDistance i)

def ActualRidgeFacetPresentation.nativeBoundaryPoint {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    EuclideanSpace ℝ (Fin r) :=
  ∑ a, P.nativeBoundaryLevels i a • P.nativeBoundaryFrame i a

theorem ActualRidgeFacetPresentation.nativeBoundaryFrame_orthonormal {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    Orthonormal ℝ (P.nativeBoundaryFrame i) := by
  have horth := P.outwardConormal_orthogonal hu hv hp i
  exact nativeTripleFrame_orthonormal _ _ _
    (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
    (P.outwardConormal_unit i) (thresholdPair_frame_orthogonal u j l hu hv)
    horth.1 horth.2

private theorem native_pair_frame_span {m r : ℕ}
    (u : Fin m → Vector r) (j l k : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    Submodule.span ℝ (Set.range
      (nativeTripleFrame (thresholdPairBisector u j l) (thresholdPairDifference u j l) (u k))) =
      Submodule.span ℝ (Set.range (nativeTripleFrame (u j) (u l) (u k))) := by
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let S := Submodule.span ℝ (Set.range (nativeTripleFrame (u j) (u l) (u k)))
  let T := Submodule.span ℝ (Set.range (nativeTripleFrame e f (u k)))
  have hjS : (WithLp.equiv 2 (Vector r)).symm (u j) ∈ S :=
    Submodule.subset_span ⟨0, by simp [nativeTripleFrame]⟩
  have hlS : (WithLp.equiv 2 (Vector r)).symm (u l) ∈ S :=
    Submodule.subset_span ⟨1, by simp [nativeTripleFrame]⟩
  have hkS : (WithLp.equiv 2 (Vector r)).symm (u k) ∈ S :=
    Submodule.subset_span ⟨2, by simp [nativeTripleFrame]⟩
  have heS : (WithLp.equiv 2 (Vector r)).symm e ∈ S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ • (u j + u l)) ∈ S
    rw [WithLp.equiv_symm_smul, WithLp.equiv_symm_add]
    exact S.smul_mem _ (S.add_mem hjS hlS)
  have hfS : (WithLp.equiv 2 (Vector r)).symm f ∈ S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ • (u j - u l)) ∈ S
    rw [WithLp.equiv_symm_smul, WithLp.equiv_symm_sub]
    exact S.smul_mem _ (S.sub_mem hjS hlS)
  have heT : (WithLp.equiv 2 (Vector r)).symm e ∈ T :=
    Submodule.subset_span ⟨0, by simp [nativeTripleFrame]⟩
  have hfT : (WithLp.equiv 2 (Vector r)).symm f ∈ T :=
    Submodule.subset_span ⟨1, by simp [nativeTripleFrame]⟩
  have hkT : (WithLp.equiv 2 (Vector r)).symm (u k) ∈ T :=
    Submodule.subset_span ⟨2, by simp [nativeTripleFrame]⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · exact heS
    · exact hfS
    · exact hkS
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · change (WithLp.equiv 2 (Vector r)).symm (u j) ∈ T
      rw [thresholdPair_left_expansion u j l hp hm, WithLp.equiv_symm_add,
        WithLp.equiv_symm_smul, WithLp.equiv_symm_smul]
      exact T.add_mem (T.smul_mem _ heT) (T.smul_mem _ hfT)
    · change (WithLp.equiv 2 (Vector r)).symm (u l) ∈ T
      rw [thresholdPair_right_expansion u j l hp hm, WithLp.equiv_symm_sub,
        WithLp.equiv_symm_smul, WithLp.equiv_symm_smul]
      exact T.sub_mem (T.smul_mem _ heT) (T.smul_mem _ hfT)
    · exact hkT

/-- The actual boundary frame spans exactly the selected three original
normals. The nonzero third residual is derived from the selected facet. -/
theorem ActualRidgeFacetPresentation.nativeBoundaryFrame_span {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    Submodule.span ℝ (Set.range (P.nativeBoundaryFrame i)) =
      Submodule.span ℝ (Set.range (nativeTripleFrame (u j) (u l) (u (P.index i)))) := by
  have hk : hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u (P.index i)) ≠ 0 :=
    actualFacet_normal_ne_zero P.normals P.levels P.strict P.irredundant i
  change Submodule.span ℝ (Set.range (nativeTripleFrame
    (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (hardPairThirdDirection u (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (P.index i)))) = _
  rw [hardPairThirdFrame_span u _ _ (thresholdPair_frame_orthogonal u j l hu hv) _ hk]
  exact native_pair_frame_span u j l (P.index i) hp.1 hp.2

private theorem native_frame_point_zero {r q : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (a : Fin q → ℝ) :
    gaussianFrameSectionPoint v a 0 = ∑ i, a i • v i := by
  simp [gaussianFrameSectionPoint, gaussianFrameProjection]

/-- The affine normal point is the actual pair section followed by the
selected outward-conormal section, evaluated at zero ambient residual. -/
theorem ActualRidgeFacetPresentation.nativeBoundaryPoint_native {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    WithLp.equiv 2 (Vector r) (P.nativeBoundaryPoint i) =
      gaussianPairBase u b j l
        (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) 0) := by
  have horth := P.outwardConormal_orthogonal hu hv hp i
  have hpoint := gaussianFrameSectionPoint_native_triple
    (thresholdPairBisector u j l) (thresholdPairDifference u j l) (P.outwardConormal i)
    (thresholdPair_frame_orthogonal u j l hu hv) horth.1 horth.2
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
    (P.signedDistance i) (0 : Vector r)
  rw [WithLp.equiv_symm_zero, native_frame_point_zero] at hpoint
  exact hpoint

private theorem native_boundary_inner {r : ℕ} (v : Vector r)
    (x : EuclideanSpace ℝ (Fin r)) :
    ⟪(WithLp.equiv 2 (Vector r)).symm v, x⟫_ℝ =
      faceDot v (WithLp.equiv 2 (Vector r) x) := by
  rw [faceDot_eq_euclidean_inner]
  rfl

/-- The synthesized normal point has all three original supporting
levels, not only the orthonormal coordinate levels. -/
theorem ActualRidgeFacetPresentation.nativeBoundaryPoint_supporting_levels {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    ⟪(WithLp.equiv 2 (Vector r)).symm (u j), P.nativeBoundaryPoint i⟫_ℝ = b j ∧
      ⟪(WithLp.equiv 2 (Vector r)).symm (u l), P.nativeBoundaryPoint i⟫_ℝ = b l ∧
      ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)), P.nativeBoundaryPoint i⟫_ℝ =
        b (P.index i) := by
  have hpoint := P.nativeBoundaryPoint_native hu hv hp i
  have hleft := gaussianPairBase_left_level u b j l hu hv hp.1 hp.2
    (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) 0)
  have hright := gaussianPairBase_right_level u b j l hu hv hp.1 hp.2
    (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) 0)
  rw [← hpoint] at hleft hright
  have hthird : faceDot (u (P.index i)) (WithLp.equiv 2 (Vector r) (P.nativeBoundaryPoint i)) =
      b (P.index i) := by
    rw [hpoint]
    unfold gaussianPairBase
    rw [gaussianPairSectionPoint_faceDot_residual _ _ _ _ _ _
      (thresholdPair_frame_orthogonal u j l hu hv)]
    have h := P.selected_support_on_section i 0
    change faceDot (hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u (P.index i)))
        (gaussianSectionPoint (P.outwardConormal i) (P.signedDistance i) 0) =
      b (P.index i) - thresholdPairFirstLevel u b j l * faceDot (u (P.index i)) (thresholdPairBisector u j l) -
        thresholdPairSecondLevel u b j l * faceDot (u (P.index i)) (thresholdPairDifference u j l) at h
    linarith
  simpa only [native_boundary_inner] using And.intro hleft (And.intro hright hthird)

theorem ActualRidgeFacetPresentation.nativeBoundaryPoint_mem_span {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    P.nativeBoundaryPoint i ∈
      Submodule.span ℝ (Set.range (nativeTripleFrame (u j) (u l) (u (P.index i)))) := by
  rw [← P.nativeBoundaryFrame_span hu hv hp i]
  apply Submodule.sum_mem
  intro a _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end
end RectangleCLTArxivV1
