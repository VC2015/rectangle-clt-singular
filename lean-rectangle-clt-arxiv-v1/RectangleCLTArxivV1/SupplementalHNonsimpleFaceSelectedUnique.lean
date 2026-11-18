import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenActualMass

/-! Actual selected residuals at a complete codimension-three face lie
in a single conormal line. These are geometric span statements with no
mass, Green, pairwise proportionality or boundary-identity supplier. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ActualRidgeFacetPresentation.residual_mem_actual_normalSpace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (hj : j∈H.1) (hl : l∈H.1) (k : Fin P.count) (hk : P.index k∈H.1) :
    projectionEuclideanVector (P.normals k)∈
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1 := by
  let S := nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  have hmj : projectionEuclideanVector (u j)∈S := nonsimple_normal_mem _ _ j hj
  have hml : projectionEuclideanVector (u l)∈S := nonsimple_normal_mem _ _ l hl
  have hmk : projectionEuclideanVector (u (P.index k))∈S := nonsimple_normal_mem _ _ _ hk
  have he : projectionEuclideanVector e∈S := by
    have heq : projectionEuclideanVector e=
        ‖projectionEuclideanVector (u j)+projectionEuclideanVector (u l)‖⁻¹ •
          (projectionEuclideanVector (u j)+projectionEuclideanVector (u l)) := by
      apply PiLp.ext
      intro a
      rfl
    rw [heq]
    exact S.smul_mem _ (S.add_mem hmj hml)
  have hf : projectionEuclideanVector f∈S := by
    have heq : projectionEuclideanVector f=
        ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖⁻¹ •
          (projectionEuclideanVector (u j)-projectionEuclideanVector (u l)) := by
      apply PiLp.ext
      intro a
      rfl
    rw [heq]
    exact S.smul_mem _ (S.sub_mem hmj hml)
  have hres : projectionEuclideanVector (P.normals k)=
      projectionEuclideanVector (u (P.index k))-
        faceDot (u (P.index k)) e • projectionEuclideanVector e-
        faceDot (u (P.index k)) f • projectionEuclideanVector f := by
    apply (WithLp.equiv 2 (Vector r)).injective
    exact hardPairResidualNormal_eq_sub e f (u (P.index k))
      (thresholdPair_frame_orthogonal u j l hu hv)
  rw [hres]
  exact S.sub_mem (S.sub_mem hmk (S.smul_mem _ he)) (S.smul_mem _ hf)

/-- Any other selected residual whose original facet is active at H
lies in the actual chosen conormal line, with no proportionality premise. -/
theorem ActualRidgeFacetPresentation.residual_mem_selected_conormal_span {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : hardGaussianRidgeNonparallel u j l) (i k : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (hj : j∈H.1) (hl : l∈H.1)
    (hi : P.index i∈H.1) (hk : P.index k∈H.1) :
    projectionEuclideanVector (P.normals k)∈
      ℝ ∙ projectionEuclideanVector (P.outwardConormal i) := by
  let N := projectionEuclideanVector (P.normals k)
  have hmem : N∈Submodule.span ℝ (Set.range (P.nativeBoundaryFrame i)) := by
    rw [P.nativeBoundaryFrame_span_actualFace hu hv hp i H hj hl hi]
    exact P.residual_mem_actual_normalSpace hu hv H hj hl k hk
  have hon := P.nativeBoundaryFrame_orthonormal hu hv hp i
  have hexp : (∑ a,⟪P.nativeBoundaryFrame i a,N⟫_ℝ • P.nativeBoundaryFrame i a)=N := by
    change gaussianFrameProjection (P.nativeBoundaryFrame i) N=N
    rw [gaussianFrameProjection_eq_orthogonalProjection _ hon]
    exact Submodule.orthogonalProjection_eq_self_iff.mpr hmem
  have horth : faceDot (P.normals k) (thresholdPairBisector u j l)=0 ∧
      faceDot (P.normals k) (thresholdPairDifference u j l)=0 :=
    hardPairResidualNormal_orthogonal _ _ (u (P.index k))
      (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
      (thresholdPair_frame_orthogonal u j l hu hv)
  have he : ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairBisector u j l),N⟫_ℝ=0 := by
    change ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairBisector u j l),
      (WithLp.equiv 2 (Vector r)).symm (P.normals k)⟫_ℝ=0
    rw [←faceDot_eq_euclidean_inner,faceDot_comm]
    exact horth.1
  have hf : ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairDifference u j l),N⟫_ℝ=0 := by
    change ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairDifference u j l),
      (WithLp.equiv 2 (Vector r)).symm (P.normals k)⟫_ℝ=0
    rw [←faceDot_eq_euclidean_inner,faceDot_comm]
    exact horth.2
  simp only [ActualRidgeFacetPresentation.nativeBoundaryFrame,nativeTripleFrame,
    Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,he,hf,zero_smul,zero_add] at hexp
  exact Submodule.mem_span_singleton.mpr ⟨_,hexp⟩

end
end RectangleCLTArxivV1
