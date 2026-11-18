import RectangleCLTArxivV1.ActiveFaceCoordinates

namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion.SplitV4

theorem activeFaceProjection_norm_eq_of_full {p : ℕ}
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (x : Vector p) :
    ‖activeFaceProjection s x‖ = ‖x‖ := by
  apply le_antisymm (activeFaceProjection_norm_le s x)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  let f : s.faces := ⟨(i,true), by simp [hfaces]⟩
  let j := (activeFaceEquiv s).symm f
  have he : activeFaceEquiv s j = f := (activeFaceEquiv s).apply_symm_apply f
  have hh := norm_le_pi_norm (activeFaceProjection s x) j
  simpa only [activeFaceProjection, he, f, FaceSmoother.normalDot, if_true] using hh

theorem faceNorm_activeCoordinateNormals_eq_of_full {p : ℕ}
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (x : Vector p) :
    faceNorm (activeCoordinateNormals s) x = ‖x‖ := by
  rw [faceNorm, activeCoordinateProjection_eq]
  exact activeFaceProjection_norm_eq_of_full s hfaces x

end RectangleCLTArxivV1
