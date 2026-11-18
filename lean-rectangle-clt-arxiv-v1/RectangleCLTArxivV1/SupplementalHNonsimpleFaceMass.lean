import RectangleCLTArxivV1.SupplementalHTripleMass

/-! Gaussian mass of an actual affine face with all original inequalities
retained.  These lemmas allow different independent triples at a nonsimple
face to use one mass.  They do not assume a boundary or Green identity. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

theorem gaussianFrameSectionPoint_inner_of_mem_span {r q : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v)
    (a : Fin q → ℝ) (g N : EuclideanSpace ℝ (Fin r))
    (hN : N ∈ Submodule.span ℝ (Set.range v)) :
    ⟪N, gaussianFrameSectionPoint v a g⟫_ℝ = ⟪N, ∑ i, a i • v i⟫_ℝ := by
  let S := Submodule.span ℝ (Set.range v)
  have hp : ⟪N, (S.orthogonalProjection g : EuclideanSpace ℝ (Fin r))⟫_ℝ =
      ⟪N, g⟫_ℝ := by
    exact Submodule.inner_orthogonalProjection_eq_of_mem_left (K := S) (⟨N, hN⟩ : S) g
  rw [gaussianFrameSectionPoint_eq_affine_projection v hv, inner_sub_right,
    inner_add_right, hp]
  ring

theorem gaussianFrameSectionPoint_supporting_level {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v)
    (a : Fin q → ℝ) (j : Fin m)
    (hj : (WithLp.equiv 2 (Vector r)).symm (u j) ∈ Submodule.span ℝ (Set.range v))
    (hlevel : ⟪(WithLp.equiv 2 (Vector r)).symm (u j), ∑ i, a i • v i⟫_ℝ = b j)
    (g : EuclideanSpace ℝ (Fin r)) :
    faceDot (u j) (WithLp.equiv 2 (Vector r) (gaussianFrameSectionPoint v a g)) = b j := by
  rw [faceDot_eq_euclidean_inner]
  exact (gaussianFrameSectionPoint_inner_of_mem_span v hv a g _ hj).trans hlevel

/-- Supporting equations may be retained among the hard inequalities on
their affine section. This includes every extra active facet at a
nonsimple face, rather than just one chosen independent triple. -/
theorem gaussianFrameHardMass_union_supporting {m r q : ℕ}
    (s t : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (a : Fin q → ℝ)
    (hspan : ∀ j ∈ t, (WithLp.equiv 2 (Vector r)).symm (u j) ∈
      Submodule.span ℝ (Set.range v))
    (hlevel : ∀ j ∈ t, ⟪(WithLp.equiv 2 (Vector r)).symm (u j),
      ∑ i, a i • v i⟫_ℝ = b j) :
    gaussianFrameHardMass (s ∪ t) u b v a = gaussianFrameHardMass s u b v a := by
  classical
  unfold gaussianFrameHardMass
  congr 1
  apply congrArg (fun P : Set (Vector r) => (standardGaussian r).real P)
  ext g
  change (∀ j ∈ s ∪ t, faceDot (u j) (WithLp.equiv 2 (Vector r)
    (gaussianFrameSectionPoint v a ((WithLp.equiv 2 (Vector r)).symm g))) ≤ b j) ↔
    ∀ j ∈ s, faceDot (u j) (WithLp.equiv 2 (Vector r)
    (gaussianFrameSectionPoint v a ((WithLp.equiv 2 (Vector r)).symm g))) ≤ b j
  constructor
  · intro h j hj
    exact h j (Finset.mem_union_left _ hj)
  · intro h j hj
    rcases Finset.mem_union.mp hj with hs | ht
    · exact h j hs
    · exact (gaussianFrameSectionPoint_supporting_level u b v hv a j
        (hspan j ht) (hlevel j ht) _).le

theorem gaussianFrameHardMass_univ_eq_sdiff_supporting {m r q : ℕ}
    (t : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (a : Fin q → ℝ)
    (hspan : ∀ j ∈ t, (WithLp.equiv 2 (Vector r)).symm (u j) ∈
      Submodule.span ℝ (Set.range v))
    (hlevel : ∀ j ∈ t, ⟪(WithLp.equiv 2 (Vector r)).symm (u j),
      ∑ i, a i • v i⟫_ℝ = b j) :
    gaussianFrameHardMass Finset.univ u b v a =
      gaussianFrameHardMass (Finset.univ \ t) u b v a := by
  classical
  have he : (Finset.univ \ t) ∪ t = Finset.univ := by ext j; simp
  calc
    _ = gaussianFrameHardMass ((Finset.univ \ t) ∪ t) u b v a := by rw [he]
    _ = _ := gaussianFrameHardMass_union_supporting _ t u b v hv a hspan hlevel

/-- The actual full-event Gaussian mass of an affine face through `x`. -/
def nonsimpleFaceGaussianMass {m r q : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (x : EuclideanSpace ℝ (Fin r)) : ℝ :=
  gaussianFrameHardMass Finset.univ u b v (fun i => ⟪v i, x⟫_ℝ)

theorem nonsimpleFaceGaussianMass_nonneg {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (x : EuclideanSpace ℝ (Fin r)) :
    0 ≤ nonsimpleFaceGaussianMass u b v x := gaussianFrameHardMass_nonneg _ _ _ _ _

/-- Different independent triples spanning one face normal space give
the same actual mass, without any generic-threshold hypothesis. -/
theorem nonsimpleFaceGaussianMass_frame_independent {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (v w : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (hspan : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (Set.range w))
    (x : EuclideanSpace ℝ (Fin r)) :
    nonsimpleFaceGaussianMass u b v x = nonsimpleFaceGaussianMass u b w x := by
  apply gaussianFrameHardMass_frame_independent _ u b v w hv hw _ _ hspan
  change gaussianFrameProjection v x = gaussianFrameProjection w x
  rw [gaussianFrameProjection_eq_orthogonalProjection v hv,
    gaussianFrameProjection_eq_orthogonalProjection w hw, hspan]

/-- The chosen point on the affine face has no effect: its supporting
levels determine the unique normal projection. -/
theorem nonsimpleFaceGaussianMass_point_independent {m r q p : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v)
    (N : Fin p → EuclideanSpace ℝ (Fin r))
    (hspan : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (Set.range N))
    (x y : EuclideanSpace ℝ (Fin r)) (hlevels : ∀ j, ⟪N j, x⟫_ℝ = ⟪N j, y⟫_ℝ) :
    nonsimpleFaceGaussianMass u b v x = nonsimpleFaceGaussianMass u b v y := by
  apply gaussianFrameHardMass_eq_of_spanning_levels _ u b v v hv hv _ _ N hspan hspan
  intro j
  have hj : N j ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hx := gaussianFrameSectionPoint_inner_of_mem_span v hv (fun i => ⟪v i, x⟫_ℝ) x (N j) hj
  have hy := gaussianFrameSectionPoint_inner_of_mem_span v hv (fun i => ⟪v i, y⟫_ℝ) y (N j) hj
  have ex : gaussianFrameSectionPoint v (fun i => ⟪v i, x⟫_ℝ) x = x := by
    simp only [gaussianFrameSectionPoint, gaussianFrameProjection]
    abel
  have ey : gaussianFrameSectionPoint v (fun i => ⟪v i, y⟫_ℝ) y = y := by
    simp only [gaussianFrameSectionPoint, gaussianFrameProjection]
    abel
  rw [ex] at hx
  rw [ey] at hy
  exact hx.symm.trans ((hlevels j).trans hy)

end
end RectangleCLTArxivV1
