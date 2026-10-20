import RectangleCLT.BoundedCurvature
import RectangleCLT.BoundedEnvelopeShift

/-! Leave-one-out points are inside the already averaged full-sum cube.
Thus no common-variance assumption is needed for a leave-one-out sum. -/

open MeasureTheory

namespace RectangleCLT.FaceSmoother

variable {p n : ℕ} (s : FaceSmoother p)

theorem leaveOneOut_shift_eq {Ω : Type*} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (ω : Ω) (u r : Vector p) :
    leaveOneOut ξ i ω + u + r = (sumVector ξ ω + r) + (u - ξ i ω) := by
  rw [sumVector_eq_leaveOneOut_add ξ i ω]
  abel

theorem abs_third_leaveOneOut_le {Ω : Type*} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (ω : Ω) (u r : Vector p) {η : ℝ}
    (hξ : ‖ξ i ω‖ ≤ η) (hu : ‖u‖ ≤ η) (hband : 2 * η ≤ s.bandwidth)
    (j k l : Fin p) :
    |s.mixedThirdDerivativeF (leaveOneOut ξ i ω + u + r) j k l| ≤
      s.thirdLocalMajorant (sumVector ξ ω + r) j k l := by
  rw [leaveOneOut_shift_eq ξ i ω u r]
  apply s.abs_mixedThirdDerivativeF_shift_le
  exact (norm_sub_le u (ξ i ω)).trans ((add_le_add hu hξ).trans (by linarith))

theorem abs_fourth_leaveOneOut_le {Ω : Type*} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (ω : Ω) (u r : Vector p) {η : ℝ}
    (hξ : ‖ξ i ω‖ ≤ η) (hu : ‖u‖ ≤ η) (hband : 2 * η ≤ s.bandwidth)
    (j k l m : Fin p) :
    |s.mixedFourthDerivativeF (leaveOneOut ξ i ω + u + r) j k l m| ≤
      s.fourthLocalMajorant (sumVector ξ ω + r) j k l m := by
  rw [leaveOneOut_shift_eq ξ i ω u r]
  apply s.abs_mixedFourthDerivativeF_shift_le
  exact (norm_sub_le u (ξ i ω)).trans ((add_le_add hu hξ).trans (by linarith))

/-- The same full-sum majorant controls every bounded random leave-one-out
translation simultaneously. The translation may depend on the observations. -/
theorem ae_abs_fourth_leaveOneOut_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {η : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (i : Fin n)
    (U : Ω → Vector p) (hU : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ η)
    (r : Vector p) (hband : 2 * η ≤ s.bandwidth) :
    ∀ᵐ ω ∂μ, ∀ j k l m,
      |s.mixedFourthDerivativeF (leaveOneOut ξ i ω + U ω + r) j k l m| ≤
        s.fourthLocalMajorant (sumVector ξ ω + r) j k l m := by
  filter_upwards [h.bounded i, hU] with ω hω hu
  exact s.abs_fourth_leaveOneOut_le ξ i ω (U ω) r hω hu hband

end RectangleCLT.FaceSmoother
