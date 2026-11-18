import RectangleCLTArxivV1.SupplementalHCubicMatrix

/-! A deterministic face-coordinate shift is absorbed into the actual
original rectangle offsets, with every selector factor retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def supplementalHInputShift {p : ℕ} (s : FaceSmoother p) (z : Vector p) : FaceSmoother p where
  faces := s.faces
  offsets := fun f => s.offsets f-FaceSmoother.normalDot f z
  bandwidth := s.bandwidth
  bandwidth_pos := s.bandwidth_pos

theorem supplementalHInputShift_faceScore {p : ℕ} (s : FaceSmoother p) (z x : Vector p) (f : Face p) :
    (supplementalHInputShift s z).faceScore f x=s.faceScore f (x+z) := by
  simp only [FaceSmoother.faceScore,supplementalHInputShift,FaceSmoother.normalDot_add]
  ring

theorem supplementalHInputShift_weights {p : ℕ} (s : FaceSmoother p) (z x : Vector p) :
    (supplementalHInputShift s z).weights x=s.weights (x+z) := by
  unfold FaceSmoother.weights
  congr 1
  funext f
  change (if f∈s.faces then Real.exp ((supplementalHInputShift s z).faceScore f x/s.bandwidth) else 0)=_
  rw [supplementalHInputShift_faceScore]

theorem supplementalHInputShift_selectorWeight {p K : ℕ}
    (s : FaceSmoother p) (z x : Vector p) (α : Fin K → Face p) :
    selectorWeight (supplementalHInputShift s z) α x=selectorWeight s α (x+z) := by
  unfold selectorWeight FaceSmoother.F FaceSmoother.pi
  rw [supplementalHInputShift_weights]

theorem supplementalHInputShift_cubicScore {p r K : ℕ}
    (s : FaceSmoother p) (z v : Vector p) (M : Matrix (Fin p) (Fin r) ℝ)
    (α : Fin K → Face p) (u : Vector r) :
    supplementalHCubicSelectorScore (supplementalHInputShift s z) M v α u=
      supplementalHCubicSelectorScore s M (z+v) α u := by
  ext j k
  unfold supplementalHCubicSelectorScore
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    rw [supplementalHInputShift_selectorWeight]
    have he : (M.mulVec g+v)+z=M.mulVec g+(z+v) := by abel
    rw [he])

end
end RectangleCLTArxivV1
