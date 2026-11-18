import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNormalized
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNativeGeometry
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNull
import RectangleCLTArxivV1.SupplementalHRidgeGreen

/-! Native actual-ridge interfaces. An ordinary point with exactly two
active original facets supplies the tangent presentation. Non-ridge pairs
have genuine zero Gaussian sections, rather than a formal derivative at a
nonsmooth duplicated threshold. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def HasStrictRidgeInterior {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l : Fin m) : Prop :=
  ∃ x : Vector r, faceDot (u j) x = b j ∧ faceDot (u l) x = b l ∧
    ∀ k, k ≠ j → k ≠ l → faceDot (u k) x < b k

theorem hasStrictRidgeInterior_iff_residual {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) :
    HasStrictRidgeInterior u b j l ↔
      HasStrictRetainedInterior ((Finset.univ.erase j).erase l)
        (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
        (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) := by
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  constructor
  · rintro ⟨x, hx, hy, hstrict⟩
    obtain ⟨he, hf⟩ := thresholdPair_frame_levels_of_support u b j l x hp.1 hp.2 hx hy
    apply hardPairResidual_strictInterior_of_affine_witness _ u b _ _ _ _ hef
    refine ⟨x, he, hf, ?_⟩
    intro k hk
    exact hstrict k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp hk).1
  · rintro ⟨g, hg⟩
    refine ⟨gaussianPairBase u b j l g,
      gaussianPairBase_left_level u b j l hu hv hp.1 hp.2 g,
      gaussianPairBase_right_level u b j l hu hv hp.1 hp.2 g, ?_⟩
    intro k hkj hkl
    have h := hg k (Finset.mem_erase.mpr ⟨hkl, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩⟩)
    have heq := gaussianPairSectionPoint_faceDot_residual
      (thresholdPairBisector u j l) (thresholdPairDifference u j l) (u k)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g hef
    unfold gaussianPairBase
    rw [heq]
    dsimp only [hardPairResidualNormals, hardPairResidualLevels] at h
    linarith

/-- Pure geometric data of the actual tangent facets of one native ridge.
No Green or surface-functional identity is a field or input. -/
structure ActualRidgeFacetPresentation {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) where
  count : ℕ
  index : Fin count → Fin m
  count_le : count ≤ m
  injective : Function.Injective index
  retained : ∀ i, index i ∈ (Finset.univ.erase j).erase l
  event_iff : ∀ x : Vector r,
    (∀ i, faceDot (hardPairResidualNormals u (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) (index i)) x ≤
      hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) (index i)) ↔
    ∀ k ∈ (Finset.univ.erase j).erase l,
      faceDot (hardPairResidualNormals u (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) k) x ≤
      hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k
  strict : HasStrictFacetInterior
    (fun i => hardPairResidualNormals u (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (index i))
    (fun i => hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) (index i))
  irredundant : HasIrredundantFacetWitnesses
    (fun i => hardPairResidualNormals u (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (index i))
    (fun i => hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) (index i))

def ActualRidgeFacetPresentation.normals {m r : ℕ} {u : Fin m → Vector r}
    {b : Vector m} {j l : Fin m} (P : ActualRidgeFacetPresentation u b j l) :
    Fin P.count → Vector r :=
  fun i => hardPairResidualNormals u (thresholdPairBisector u j l)
    (thresholdPairDifference u j l) (P.index i)

def ActualRidgeFacetPresentation.levels {m r : ℕ} {u : Fin m → Vector r}
    {b : Vector m} {j l : Fin m} (P : ActualRidgeFacetPresentation u b j l) :
    Vector P.count :=
  fun i => hardPairResidualLevels u b (thresholdPairBisector u j l)
    (thresholdPairDifference u j l) (thresholdPairFirstLevel u b j l)
    (thresholdPairSecondLevel u b j l) (P.index i)

def ActualRidgeFacetPresentation.outwardConormal {m r : ℕ} {u : Fin m → Vector r}
    {b : Vector m} {j l : Fin m} (P : ActualRidgeFacetPresentation u b j l)
    (i : Fin P.count) : Vector r := actualFacetOutwardConormal P.normals i

def ActualRidgeFacetPresentation.signedDistance {m r : ℕ} {u : Fin m → Vector r}
    {b : Vector m} {j l : Fin m} (P : ActualRidgeFacetPresentation u b j l)
    (i : Fin P.count) : ℝ := actualFacetSignedSupportDistance P.normals P.levels i

def ActualRidgeFacetPresentation.boundaryMass {m r : ℕ} {u : Fin m → Vector r}
    {b : Vector m} {j l : Fin m} (P : ActualRidgeFacetPresentation u b j l)
    (i : Fin P.count) : ℝ := actualFacetGaussianBoundaryMass P.normals P.levels i

theorem ActualRidgeFacetPresentation.outwardConormal_unit {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    vectorNormSq (P.outwardConormal i) = 1 :=
  actualFacetOutwardConormal_unit P.normals P.levels P.strict P.irredundant i

theorem ActualRidgeFacetPresentation.boundaryMass_nonneg {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l) (i : Fin P.count) :
    0 ≤ P.boundaryMass i := actualFacetGaussianBoundaryMass_nonneg P.normals P.levels i

theorem ActualRidgeFacetPresentation.signedDistance_eq_support {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (i : Fin P.count) (x : Vector r)
    (hx : faceDot (thresholdPairBisector u j l) x = thresholdPairFirstLevel u b j l)
    (hy : faceDot (thresholdPairDifference u j l) x = thresholdPairSecondLevel u b j l)
    (hk : faceDot (u (P.index i)) x = b (P.index i)) :
    P.signedDistance i = faceDot (P.outwardConormal i) x := by
  exact (hardPairResidual_unitConormal_support_level u b _ _ x _ _
    (thresholdPair_frame_orthogonal u j l hu hv) (P.index i) hx hy hk).symm

/-- The native signed ridge term has its actual pointwise Green formula
over any exact actual tangent-facet presentation. -/
theorem ActualRidgeFacetPresentation.native_Green {m n : ℕ}
    {u : Fin m → Vector (n+1)} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) :
    hardGaussianSignedRidgeTerm u b j l = hardGaussianRidgeLeadingTerm u b j l -
      ∑ i, P.signedDistance i * (hardGaussianRidgeNormalWeight u b j l * P.boundaryMass i) := by
  have h := hardGaussianPairSection_Green_of_actual_presentation
    ((Finset.univ.erase j).erase l) u b _ _
    (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
    (thresholdPair_frame_orthogonal u j l hu hv) _ _
    (hardGaussianRidgeNormalWeight u b j l) P.index P.event_iff P.strict P.irredundant
  simpa only [hardGaussianSignedRidgeTerm, hardGaussianRidgeLeadingTerm, if_pos hp,
    ActualRidgeFacetPresentation.signedDistance, ActualRidgeFacetPresentation.boundaryMass,
    ActualRidgeFacetPresentation.normals, ActualRidgeFacetPresentation.levels] using h

theorem actualFacet_exists_ridgeFacetPresentation {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hint : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (j l : Fin m) (hjl : j ≠ l)
    (hridge : HasStrictRidgeInterior u b j l) :
    Nonempty (ActualRidgeFacetPresentation u b j l) := by
  have hridge_copy := hridge
  obtain ⟨x, hx, hy, _⟩ := hridge_copy
  have hp := actualFacet_pair_support_nonparallel u b hint hw j l hjl x hx hy
  have hs := (hasStrictRidgeInterior_iff_residual u b j l (hu j) (hu l) hp).mp hridge
  obtain ⟨q, ι, hq, hi, hmem, hpoly, hstrict, hirr⟩ :=
    exists_actual_retained_facet_presentation _ _ _ hs
  exact ⟨⟨q, ι, hq, hi, hmem, hpoly, hstrict, hirr⟩⟩

/-- Nonactual pairs contribute zero to both the signed and leading native
ridge sums, proved from actual spatial Gaussian nullity. -/
theorem actualFacet_nativeRidgeTerms_zero_of_no_strictInterior {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hint : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (j l : Fin m)
    (hnot : ¬HasStrictRidgeInterior u b j l) :
    hardGaussianSignedRidgeTerm u b j l = 0 ∧ hardGaussianRidgeLeadingTerm u b j l = 0 := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j ≠ l := by
      intro heq
      subst l
      exact hp.2 (sub_self _)
    have hno := hnot ∘ (hasStrictRidgeInterior_iff_residual u b j l (hu j) (hu l) hp).mpr
    have hreg := actualFacet_pairResidual_nonzero_or_level u b hint hw hu j l hjl
    have hef := thresholdPair_frame_orthogonal u j l (hu j) (hu l)
    have hprob := hardGaussianPairSectionProbability_zero_of_no_strictResidualInterior
      ((Finset.univ.erase j).erase l) u b _ _ _ _ hef hreg hno
    have hsigned := hardGaussianPairSignedSection_zero_of_no_strictResidualInterior
      ((Finset.univ.erase j).erase l) u b _ _ _ _ hef hreg hno
    simp only [hardGaussianSignedRidgeTerm, hardGaussianRidgeLeadingTerm, if_pos hp,
      hsigned, hprob, mul_zero, and_self]
  · simp only [hardGaussianSignedRidgeTerm, hardGaussianRidgeLeadingTerm, if_neg hp, and_self]

end
end RectangleCLTArxivV1
