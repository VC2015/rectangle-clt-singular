import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNative

/-! Actual selected facets have genuine relative-interior points.
The witness is constructed by interpolating a strict interior point with
a deleted-inequality witness; no incidence or active-set assertion is
assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem actualFacet_exists_strict_support_point {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hint : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (j : Fin m) :
    ∃ x : Vector r, faceDot (u j) x = b j ∧
      ∀ k, k ≠ j → faceDot (u k) x < b k := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨y, hy, hyj⟩ := hw j
  let t := (b j - faceDot (u j) x) / (faceDot (u j) y - faceDot (u j) x)
  have hden : 0 < faceDot (u j) y - faceDot (u j) x := by linarith [hx j]
  have ht : 0 < t := div_pos (sub_pos.mpr (hx j)) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hmul : t * (faceDot (u j) y - faceDot (u j) x) = b j - faceDot (u j) x :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨(1-t) • x + t • y, ?_, ?_⟩
  · rw [threshold_faceDot_add_right, threshold_faceDot_smul_right, threshold_faceDot_smul_right]
    nlinarith only [hmul]
  · intro k hkj
    rw [threshold_faceDot_add_right, threshold_faceDot_smul_right, threshold_faceDot_smul_right]
    calc
      (1-t) * faceDot (u k) x + t * faceDot (u k) y <
          (1-t) * b k + t * b k :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx k) (by linarith))
          (mul_le_mul_of_nonneg_left (hy k hkj) ht.le)
      _ = b k := by ring

theorem ActualRidgeFacetPresentation.exists_strict_support_point {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    ∃ x : Vector r, faceDot (P.normals i) x = P.levels i ∧
      ∀ k, k ≠ i → faceDot (P.normals k) x < P.levels k :=
  actualFacet_exists_strict_support_point P.normals P.levels P.strict P.irredundant i

/-- Pull the constructed residual-facet point back to the actual original
polyhedron. The selected third facet is active, and every other selected
tangent facet is strict. Deleted original inequalities remain present. -/
theorem ActualRidgeFacetPresentation.exists_original_boundary_point {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count) :
    ∃ x : Vector r, (∀ k, faceDot (u k) x ≤ b k) ∧
      faceDot (u j) x = b j ∧ faceDot (u l) x = b l ∧
      faceDot (u (P.index i)) x = b (P.index i) ∧
      ∀ k : Fin P.count, k ≠ i → faceDot (u (P.index k)) x < b (P.index k) := by
  obtain ⟨g, hgi, hstrict⟩ := P.exists_strict_support_point i
  have hs : ∀ k, faceDot (P.normals k) g ≤ P.levels k := by
    intro k
    by_cases hki : k = i
    · subst k
      exact hgi.le
    · exact (hstrict k hki).le
  have hres := (P.event_iff g).mp hs
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  let x := gaussianPairBase u b j l g
  have hxj : faceDot (u j) x = b j := gaussianPairBase_left_level u b j l hu hv hp.1 hp.2 g
  have hxl : faceDot (u l) x = b l := gaussianPairBase_right_level u b j l hu hv hp.1 hp.2 g
  have hdot (k : Fin m) : faceDot (u k) x =
      thresholdPairFirstLevel u b j l * faceDot (u k) (thresholdPairBisector u j l) +
      thresholdPairSecondLevel u b j l * faceDot (u k) (thresholdPairDifference u j l) +
      faceDot (hardPairResidualNormal (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) (u k)) g :=
    gaussianPairSectionPoint_faceDot_residual _ _ _ _ _ g hef
  refine ⟨x, ?_, hxj, hxl, ?_, ?_⟩
  · intro k
    by_cases hkj : k = j
    · subst k
      exact hxj.le
    by_cases hkl : k = l
    · subst k
      exact hxl.le
    have h := hres k (Finset.mem_erase.mpr ⟨hkl, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩⟩)
    rw [hdot]
    dsimp only [hardPairResidualNormals, hardPairResidualLevels] at h
    linarith
  · rw [hdot]
    change faceDot (hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u (P.index i))) g =
      b (P.index i) - thresholdPairFirstLevel u b j l * faceDot (u (P.index i)) (thresholdPairBisector u j l) -
      thresholdPairSecondLevel u b j l * faceDot (u (P.index i)) (thresholdPairDifference u j l) at hgi
    linarith
  · intro k hki
    have h := hstrict k hki
    rw [hdot]
    change faceDot (hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u (P.index k))) g <
      b (P.index k) - thresholdPairFirstLevel u b j l * faceDot (u (P.index k)) (thresholdPairBisector u j l) -
      thresholdPairSecondLevel u b j l * faceDot (u (P.index k)) (thresholdPairDifference u j l) at h
    linarith

end
end RectangleCLTArxivV1
