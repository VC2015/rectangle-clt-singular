import RectangleCLTCompanion.SignedSurfaceTubeDomains
import RectangleCLT.GaussianTubeDomination

/-! Boundary localization uses the physical Euclidean displacement, rather
than the potentially large individual coefficients near opposite normals. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

theorem sourceDomainOf_base_exactActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) (e : ℝ × (Face p → ℝ))
    (h0 : 0 < e.1) (he : ∀ f, 0 < e.2 f)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hD : ∀ c ∈ D, ∀ i, 0 < c i) (w : Coordinates p q)
    (hw : w ∈ sourceDomainOf S s A r e.1 e.2 B D)
    (heq : ∀ i, tube (GaussianTube.map (normalMatrix S A) s.bandwidth e.1
      (activeOffsets S s r) w) i = e.2 (S.face i)) :
    base w ∈ exactActiveFace s.faces (activeFaces S) (signedRowNormal A) (commonOffsets s r e) := by
  apply source_base_exactActiveFace S s A r hactive e h0 he (1 + ‖tube w‖) w _ heq
  refine ⟨?_, hw.2.2⟩
  intro i
  refine ⟨hD _ hw.2.1 i, ?_⟩
  have hh := (le_abs_self (tube w i)).trans
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (tube w) i)
  linarith

theorem normal_add_shift_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (z r : Vector p) :
    FaceSmoother.normalDot f (A.mulVec z + r) =
      faceDot (signedRowNormal A f) z + FaceSmoother.normalDot f r := by
  simp only [normalDot_eq_faceSign_mul, Matrix.mulVec, dotProduct, Pi.add_apply,
    faceDot, signedRowNormal, mul_add, Finset.mul_sum, mul_assoc]

/-- Actual common-space localization with a covariance-free physical
length bound. The Gaussian factor may be singular. -/
theorem imageEventOf_mem_boundaryLayer {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces)
    {σ ε : ℝ} (hσ : 0 ≤ σ) (hε : 0 ≤ ε)
    (hrow : ∀ f, ‖projectionEuclideanVector (signedRowNormal A f)‖ ≤ σ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq : 0 < q) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hD : ∀ c ∈ D, ∀ i, 0 < c i)
    (hphysical : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S A).mulVec c)‖ ≤ ε)
    {ze : Vector p × (ℝ × (Face p → ℝ))}
    (hz : ze ∈ imageEventOf S s A r B D) :
    A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).boundaryLayer (σ * ε) := by
  obtain ⟨h0, he, w, hw, hm⟩ := hz
  have het (i : Fin q) := congrArg (fun v : Coordinates p q => tube v i) hm
  have hb := sourceDomainOf_base_exactActive S s A r hactive ze.2 h0 he B D hD w hw het
  have hface (i : Fin q) :
      faceDot (signedRowNormal A (S.face i)) (base w) = commonOffsets s r ze.2 (S.face i) :=
    (hb.2 (S.face i) (hactive i)).mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hout := outward_not_mem_polyhedron s.faces (signedRowNormal A) (commonOffsets s r ze.2)
    S.face (normalMatrix S A) (fun _ _ => rfl) hactive hd hq (base w) (tube w) hface
    (hD _ hw.2.1)
  have hy := congrArg (base : Coordinates p q → Vector p) hm
  rw [base_map] at hy
  change base w + (normalMatrix S A).mulVec (tube w) = ze.1 at hy
  have hcorr (f : Face p) :
      faceDot (signedRowNormal A f) ((normalMatrix S A).mulVec (tube w)) ≤ σ * ε := by
    have hCS := abs_real_inner_le_norm
      (projectionEuclideanVector (signedRowNormal A f))
      (projectionEuclideanVector ((normalMatrix S A).mulVec (tube w)))
    have heq : ⟪projectionEuclideanVector (signedRowNormal A f),
        projectionEuclideanVector ((normalMatrix S A).mulVec (tube w))⟫_ℝ =
        faceDot (signedRowNormal A f) ((normalMatrix S A).mulVec (tube w)) := by
      simp [projectionEuclideanVector, PiLp.inner_apply, faceDot, mul_comm]
    rw [heq] at hCS
    exact (le_abs_self _).trans (hCS.trans (mul_le_mul (hrow f) (hphysical _ hw.2.1)
      (norm_nonneg _) hσ))
  have hpoly (d : ℝ) :
      ze.1 ∈ facePolyhedron s.faces (signedRowNormal A)
        (fun f => commonOffsets s r ze.2 f + d) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet d := by
    simp only [facePolyhedron, Set.mem_setOf_eq, FaceSmoother.outerSet,
      FaceSmoother.randomRectangle, commonOffsets]
    constructor <;> intro h f hf <;> have hh := h f hf <;>
      rw [normal_add_shift_eq] at * <;> linarith
  have hpoly0 : ze.1 ∈ facePolyhedron s.faces (signedRowNormal A) (commonOffsets s r ze.2) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet 0 := by
    simpa only [add_zero] using hpoly 0
  refine ⟨(hpoly _).mp ?_, ?_⟩
  · rw [← hy]
    intro f hf
    have hh := hb.1 f hf
    have hc := hcorr f
    simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    linarith
  · intro hinner
    apply hout
    rw [hy]
    apply hpoly0.mpr
    intro f hf
    have hh := hinner f hf
    have hwidth : 0 ≤ σ * ε := mul_nonneg hσ hε
    linarith

end
end RectangleCLT.Companion.SignedSurface
