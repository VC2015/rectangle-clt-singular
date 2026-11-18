import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenSelection
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenRadial

/-! Pointwise Gaussian Green on a genuine ridge. Its tangent polyhedron
is represented by an exact irredundant selection of the retained residual
inequalities. Tied copies of a tangent facet are therefore counted once.
The premise is an ordinary strict relative-interior witness, not generic
threshold regularity or an assumed Green formula. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem gaussianPairSectionPoint_eq_self_of_levels {r : ℕ}
    (e f x : Vector r) (a c : ℝ)
    (he : faceDot e x = a) (hf : faceDot f x = c) :
    gaussianPairSectionPoint e f a c x = x := by
  have hfe : gaussianSectionPoint e a x = x := by
    rw [gaussianSectionPoint_eq, he, sub_self, zero_smul, add_zero]
  have hff : gaussianSectionPoint f c x = x := by
    rw [gaussianSectionPoint_eq, hf, sub_self, zero_smul, add_zero]
  simpa only [gaussianPairSectionPoint, hff] using hfe

theorem hardPairResidual_strictInterior_of_affine_witness {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (hef : faceDot e f = 0)
    (hw : ∃ x : Vector r, faceDot e x = a ∧ faceDot f x = c ∧
      ∀ k ∈ s, faceDot (u k) x < b k) :
    HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) := by
  obtain ⟨x, hx, hy, hstrict⟩ := hw
  apply hardPairResidual_strictInterior_of_section_witness s u b e f a c hef
  refine ⟨x, ?_⟩
  simpa only [gaussianPairSectionPoint_eq_self_of_levels e f x a c hx hy] using hstrict

/-- A true supporting point has exactly the residual supporting level.
Consequently normalizing the residual normal produces the genuine signed
tangential support distance, without a genericity assumption. -/
theorem hardPairResidual_support_level {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e f x : Vector r)
    (a c : ℝ) (hef : faceDot e f = 0) (k : Fin m)
    (hx : faceDot e x = a) (hy : faceDot f x = c)
    (hk : faceDot (u k) x = b k) :
    faceDot (hardPairResidualNormals u e f k) x =
      hardPairResidualLevels u b e f a c k := by
  have h := gaussianPairSectionPoint_faceDot_residual e f (u k) a c x hef
  rw [gaussianPairSectionPoint_eq_self_of_levels e f x a c hx hy, hk] at h
  change faceDot (hardPairResidualNormal e f (u k)) x =
    b k - a * faceDot (u k) e - c * faceDot (u k) f
  linarith

theorem hardPairResidual_unitConormal_support_level {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e f x : Vector r)
    (a c : ℝ) (hef : faceDot e f = 0) (k : Fin m)
    (hx : faceDot e x = a) (hy : faceDot f x = c)
    (hk : faceDot (u k) x = b k) :
    faceDot (localFiniteThresholdDirection (hardPairResidualNormals u e f) k) x =
      hardPairResidualLevels u b e f a c k /
        localFiniteThresholdScale (hardPairResidualNormals u e f) k := by
  rw [localFiniteThresholdDirection, threshold_faceDot_smul_left,
    hardPairResidual_support_level u b e f x a c hef k hx hy hk]
  simp only [div_eq_mul_inv, mul_comm]

/-- The actual signed pair section has a pointwise Green decomposition
over its selected actual tangent facets. No derivative of the unmerged
original threshold list occurs on the right-hand side. -/
theorem exists_hardGaussianPairSection_Green_actualFacets {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (hef : faceDot e f = 0) (a c : ℝ)
    (hint : HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    ∃ (q : ℕ) (ι : Fin q → Fin m), q ≤ m ∧ Function.Injective ι ∧
      (∀ i, ι i ∈ s) ∧
      (∀ x : Vector (n+1),
        (∀ i, faceDot (hardPairResidualNormals u e f (ι i)) x ≤
          hardPairResidualLevels u b e f a c (ι i)) ↔
        ∀ k ∈ s, faceDot (hardPairResidualNormals u e f k) x ≤
          hardPairResidualLevels u b e f a c k) ∧
      HasStrictFacetInterior (fun i => hardPairResidualNormals u e f (ι i))
        (fun i => hardPairResidualLevels u b e f a c (ι i)) ∧
      HasIrredundantFacetWitnesses (fun i => hardPairResidualNormals u e f (ι i))
        (fun i => hardPairResidualLevels u b e f a c (ι i)) ∧
      hardGaussianPairSignedSection s u b e f a c =
        (a^2+c^2-2)*hardGaussianPairSectionProbability s u b e f a c -
        ∑ i, hardPairResidualLevels u b e f a c (ι i) *
          gaussianFiniteThresholdFirst Finset.univ
            (fun k => hardPairResidualNormals u e f (ι k))
            (fun k => hardPairResidualLevels u b e f a c (ι k)) i := by
  obtain ⟨q, ι, hq, hi, hmem, hpoly, hstrict, hw⟩ :=
    exists_actual_retained_facet_presentation s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) hint
  refine ⟨q, ι, hq, hi, hmem, hpoly, hstrict, hw, ?_⟩
  have hevent := selected_retained_threshold_event_eq s (hardPairResidualNormals u e f)
    (hardPairResidualLevels u b e f a c) ι hpoly
  have htrace : gaussianFiniteThresholdRadialTrace s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) =
      -(∑ i, hardPairResidualLevels u b e f a c (ι i) *
        gaussianFiniteThresholdFirst Finset.univ
          (fun k => hardPairResidualNormals u e f (ι k))
          (fun k => hardPairResidualLevels u b e f a c (ι k)) i) := by
    unfold gaussianFiniteThresholdRadialTrace
    rw [← hevent]
    exact gaussianFiniteThreshold_radialTrace_of_actualFacets _ _ hstrict hw
  rw [hardGaussianPairSignedSection_eq_residual_trace s u b e f he hf hef a c, htrace]
  ring

end
end RectangleCLTArxivV1
