import RectangleCLTArxivV1.SupplementalHNonsimpleFaceMass
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceFrame

/-! One canonical Gaussian mass for every actual face, indexed by its
complete active set. All original inequalities are retained. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section

def nonsimpleNativeNormals {m r : ℕ} (u : Fin m → Vector r) :
    Fin m → EuclideanSpace ℝ (Fin r) := fun j => (WithLp.equiv 2 (Vector r)).symm (u j)

def nonsimpleActualGaussianMass {m r q : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) : ℝ :=
  nonsimpleFaceGaussianMass u b
    (nonsimpleFaceFrame (nonsimpleNativeNormals u) b F)
    (nonsimpleFaceRepresentative (nonsimpleNativeNormals u) b F)

theorem nonsimpleActualGaussianMass_nonneg {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (F : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    0 ≤ nonsimpleActualGaussianMass u b F := nonsimpleFaceGaussianMass_nonneg _ _ _ _

/-- An arbitrary orthonormal description with the actual face normal
space and supporting levels has the canonical face mass. The number of
active original inequalities is unrestricted. -/
theorem gaussianFrameHardMass_eq_actualFaceMass {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (F : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (a : Fin q → ℝ)
    (hspan : Submodule.span ℝ (Set.range v) =
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) F.1)
    (hlevels : ∀ j ∈ F.1, ⟪nonsimpleNativeNormals u j, ∑ i,a i • v i⟫_ℝ = b j) :
    gaussianFrameHardMass Finset.univ u b v a = nonsimpleActualGaussianMass u b F := by
  have hzmem : (∑ i,a i • v i) ∈ nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) F.1 := by
    rw [← hspan]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have hz : (∑ i,a i • v i) = nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b F := by
    apply nonsimpleFaceNormalPoint_unique (nonsimpleNativeNormals u) b F.1 _ _ hzmem
      (nonsimpleFaceNormalPoint_mem _ _ F)
    intro j hj
    rw [hlevels j hj, nonsimpleFaceNormalPoint_levels _ _ F j hj]
  unfold nonsimpleActualGaussianMass nonsimpleFaceGaussianMass
  exact gaussianFrameHardMass_frame_independent _ u b v _ hv
    (nonsimpleFaceFrame_orthonormal _ _ F) a _
    (hspan.trans (nonsimpleFaceFrame_span _ _ F).symm)
    (hz.trans (nonsimpleFaceNormalPoint_eq_frameProjection _ _ F))

/-- The same canonical mass is obtained when the constraints used as
supporting equations have been omitted from the section event. -/
theorem gaussianFrameHardMass_sdiff_eq_actualFaceMass {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (F : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (a : Fin q → ℝ)
    (hspan : Submodule.span ℝ (Set.range v) =
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) F.1)
    (hlevels : ∀ j ∈ F.1, ⟪nonsimpleNativeNormals u j, ∑ i,a i • v i⟫_ℝ = b j)
    (t : Finset (Fin m)) (ht : t ⊆ F.1) :
    gaussianFrameHardMass (Finset.univ \ t) u b v a = nonsimpleActualGaussianMass u b F := by
  have hm := gaussianFrameHardMass_univ_eq_sdiff_supporting t u b v hv a
    (fun j hj => by
      change nonsimpleNativeNormals u j ∈ _
      rw [hspan]
      exact nonsimple_normal_mem _ _ _ (ht hj))
    (fun j hj => hlevels j (ht hj))
  rw [← hm]
  exact gaussianFrameHardMass_eq_actualFaceMass u b F v hv a hspan hlevels

/-- Full original sections are independent of which actual point of
the face is used to locate its affine normal space. -/
theorem nonsimpleActualGaussianMass_eq_at_closedFacePoint {m r q : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (F : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (x : EuclideanSpace ℝ (Fin r))
    (hx : x ∈ nonsimpleClosedFace (nonsimpleNativeNormals u) b F.1) :
    nonsimpleActualGaussianMass u b F =
      nonsimpleFaceGaussianMass u b (nonsimpleFaceFrame (nonsimpleNativeNormals u) b F) x := by
  unfold nonsimpleActualGaussianMass
  apply nonsimpleFaceGaussianMass_point_independent u b _
    (nonsimpleFaceFrame_orthonormal _ _ F)
    (fun j : Fin m => if j ∈ F.1 then nonsimpleNativeNormals u j else 0)
  · rw [nonsimpleFaceFrame_span]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      apply Submodule.subset_span
      refine ⟨j,?_⟩
      change (if j ∈ F.1 then nonsimpleNativeNormals u j else 0) = nonsimpleNativeNormals u j
      exact if_pos hj
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      by_cases hj : j ∈ F.1
      · simp only [hj,if_true]
        exact nonsimple_normal_mem _ _ j hj
      · simp only [hj,if_false]
        exact Submodule.zero_mem _
  · intro j
    by_cases hj : j ∈ F.1
    · simp only [hj,if_true]
      rw [nonsimpleFaceRepresentative_levels _ _ F j hj, hx.2 j hj]
    · simp [hj]

end
end RectangleCLTArxivV1
