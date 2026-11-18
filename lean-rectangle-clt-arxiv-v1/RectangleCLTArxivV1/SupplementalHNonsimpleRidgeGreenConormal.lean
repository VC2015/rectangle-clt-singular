import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenFrame

/-! Actual outward-conormal orientation and uniqueness inside the selected
three-dimensional normal space. The orientation comes from the original
selected normal and its strictly positive residual length. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The selected original normal has positive pairing with the actual
outward conormal; the pairing is its exact residual normal length. -/
theorem ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_eq_scale {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)),
      (WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i)⟫_ℝ =
        localFiniteThresholdScale P.normals i := by
  have horth := P.outwardConormal_orthogonal hu hv hp i
  have hres : faceDot (P.normals i) (P.outwardConormal i) =
      faceDot (u (P.index i)) (P.outwardConormal i) := by
    change faceDot (hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u (P.index i))) (P.outwardConormal i) = _
    rw [hardPairResidualNormal_eq_sub _ _ _ (thresholdPair_frame_orthogonal u j l hu hv),
      threshold_faceDot_sub_left, threshold_faceDot_sub_left,
      threshold_faceDot_smul_left, threshold_faceDot_smul_left,
      horth.1, horth.2, mul_zero, mul_zero, sub_zero, sub_zero]
  have hself : faceDot (P.outwardConormal i) (P.outwardConormal i) = 1 := by
    simpa only [faceDot, vectorNormSq, pow_two] using P.outwardConormal_unit i
  have hscale : faceDot (P.normals i) (P.outwardConormal i) =
      localFiniteThresholdScale P.normals i := by
    rw [P.normal_eq_scale_conormal i, threshold_faceDot_smul_left, hself, mul_one]
  rw [← faceDot_eq_euclidean_inner]
  exact hres.symm.trans hscale

theorem ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_pos {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    0 < ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)),
      (WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i)⟫_ℝ := by
  rw [P.originalNormal_inner_outwardConormal_eq_scale hu hv hp i]
  exact actualFacet_scale_pos P.normals P.levels P.strict P.irredundant i

/-- In the actual selected normal space, the unit direction orthogonal
to the ridge pair and positive on the selected third original normal is
uniquely the outward conormal of that residual facet. -/
theorem ActualRidgeFacetPresentation.outwardConormal_unique {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (v : EuclideanSpace ℝ (Fin r)) (hvnorm : ‖v‖ = 1)
    (hspan : v ∈ Submodule.span ℝ (Set.range (P.nativeBoundaryFrame i)))
    (he : ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairBisector u j l), v⟫_ℝ = 0)
    (hf : ⟪(WithLp.equiv 2 (Vector r)).symm (thresholdPairDifference u j l), v⟫_ℝ = 0)
    (hpositive : 0 < ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)), v⟫_ℝ) :
    v = (WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i) := by
  let D := (WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i)
  let c := ⟪D, v⟫_ℝ
  have hon := P.nativeBoundaryFrame_orthonormal hu hv hp i
  have hexp : (∑ a, ⟪P.nativeBoundaryFrame i a, v⟫_ℝ • P.nativeBoundaryFrame i a) = v := by
    change gaussianFrameProjection (P.nativeBoundaryFrame i) v = v
    rw [gaussianFrameProjection_eq_orthogonalProjection _ hon]
    exact Submodule.orthogonalProjection_eq_self_iff.mpr hspan
  have hv_eq : v = c • D := by
    simpa only [ActualRidgeFacetPresentation.nativeBoundaryFrame, nativeTripleFrame,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, he, hf, zero_smul, zero_add] using hexp.symm
  have hDnorm : ‖D‖ = 1 := thresholdEuclideanNormal_unit _ (P.outwardConormal_unit i)
  have hpair : 0 < ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)), D⟫_ℝ :=
    P.originalNormal_inner_outwardConormal_pos hu hv hp i
  have hproduct : 0 < c * ⟪(WithLp.equiv 2 (Vector r)).symm (u (P.index i)), D⟫_ℝ := by
    simpa only [hv_eq, real_inner_smul_right] using hpositive
  have hc : 0 < c := by
    rcases mul_pos_iff.mp hproduct with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge hpair.le) h.2)
  have habs : |c| = 1 := by
    calc
      |c| = ‖c • D‖ := by rw [norm_smul, Real.norm_eq_abs, hDnorm, mul_one]
      _ = ‖v‖ := by rw [← hv_eq]
      _ = 1 := hvnorm
  have hc1 : c = 1 := by simpa only [abs_of_pos hc] using habs
  simpa only [hc1, one_smul] using hv_eq

end
end RectangleCLTArxivV1
