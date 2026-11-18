import RectangleCLTArxivV1.FaceCoordinates
import RectangleCLTCompanion.SplitV4.LogisticActiveFaces
import RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration

/-! Exact transport between the archived rectangle smoother and its list
of active signed-coordinate faces. Empty lists are retained explicitly. -/

namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable def activeCoordinateNormals {p : ℕ} (s : FaceSmoother p) :
    Fin s.faces.card → Vector p := fun j =>
  signedDirection (some ((activeFaceEquiv s j).1.2, (activeFaceEquiv s j).1.1))

theorem activeCoordinateProjection_eq {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    faceProjection (activeCoordinateNormals s) x = activeFaceProjection s x := by
  ext j
  rw [faceProjection, activeCoordinateNormals, ← signedCoordinate_eq_dotProduct]
  cases he : (activeFaceEquiv s j).1.2 <;>
    simp [activeFaceProjection, signedCoordinate, signedVectors, FaceSmoother.normalDot, he]

theorem activeFaceProjection_norm_le {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    ‖activeFaceProjection s x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  have hc := norm_le_pi_norm x (activeFaceEquiv s j).1.1
  dsimp [activeFaceProjection, FaceSmoother.normalDot]
  split_ifs <;> simpa using hc

theorem activeFaceProjection_sum {p n : ℕ} (s : FaceSmoother p)
    (ξ : Fin n → Vector p) :
    activeFaceProjection s (∑ i, ξ i) = ∑ i, activeFaceProjection s (ξ i) := by
  ext j
  simp only [activeFaceProjection, FaceSmoother.normalDot, Finset.sum_apply]
  split_ifs <;> simp

theorem activeFaceProjection_add {p : ℕ} (s : FaceSmoother p) (x y : Vector p) :
    activeFaceProjection s (x+y) = activeFaceProjection s x + activeFaceProjection s y := by
  rw [← activeCoordinateProjection_eq, ← activeCoordinateProjection_eq,
    ← activeCoordinateProjection_eq, faceProjection_add]

theorem boundaryLayer_eq_activeFaceLayer {p : ℕ} (s : FaceSmoother p) (d : ℝ) (x : Vector p) :
    x ∈ s.boundaryLayer d ↔
      x ∈ faceLayer (activeCoordinateNormals s) (activeFaceOffsets s) d := by
  rw [s.mem_boundaryLayer_iff_score]
  change _ ↔ (∀ j, dotProduct (activeCoordinateNormals s j) x ≤ activeFaceOffsets s j+d) ∧
    ¬(∀ j, dotProduct (activeCoordinateNormals s j) x ≤ activeFaceOffsets s j + -d)
  have hh (q : ℝ) : (∀ f ∈ s.faces, s.faceScore f x ≤ q) ↔
      ∀ j, dotProduct (activeCoordinateNormals s j) x ≤ activeFaceOffsets s j+q := by
    constructor
    · intro h j
      have he := h (activeFaceEquiv s j).1 (activeFaceEquiv s j).2
      change faceProjection (activeCoordinateNormals s) x j ≤ activeFaceOffsets s j + q
      rw [activeCoordinateProjection_eq]
      change FaceSmoother.normalDot _ x ≤ s.offsets _ + q
      dsimp [FaceSmoother.faceScore] at he
      linarith
    · intro h f hf
      let j := (activeFaceEquiv s).symm ⟨f,hf⟩
      have he := h j
      change faceProjection (activeCoordinateNormals s) x j ≤ activeFaceOffsets s j+q at he
      rw [activeCoordinateProjection_eq] at he
      have hj : activeFaceEquiv s j = ⟨f,hf⟩ := (activeFaceEquiv s).apply_symm_apply ⟨f,hf⟩
      simp only [activeFaceProjection, activeFaceOffsets, hj] at he
      dsimp [FaceSmoother.faceScore]
      linarith
  exact (hh d).and (not_congr (hh (-d)))

theorem boundaryLayer_empty_of_faces_empty {p : ℕ} (s : FaceSmoother p) (hs : s.faces = ∅)
    (d : ℝ) : s.boundaryLayer d = ∅ := by
  ext x
  simp [s.mem_boundaryLayer_iff_score, hs]

theorem mem_boundaryLayer_iff_activeProjected {p : ℕ} (s : FaceSmoother p)
    (d : ℝ) (x : Vector p) :
    x ∈ s.boundaryLayer d ↔ activeFaceProjection s x ∈
      RectangleCLT.Companion.SplitV4.projectedFaceLayer (activeFaceOffsets s) d := by
  rw [boundaryLayer_eq_activeFaceLayer]
  change (faceProjection (activeCoordinateNormals s) x ∈
    RectangleCLT.Companion.SplitV4.projectedFaceLayer (activeFaceOffsets s) d) ↔ _
  rw [activeCoordinateProjection_eq]

end RectangleCLTArxivV1
