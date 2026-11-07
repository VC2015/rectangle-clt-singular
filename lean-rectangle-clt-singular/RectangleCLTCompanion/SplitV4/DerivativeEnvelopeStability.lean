import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeLocal34

/-! Actual smaller-envelope stability under arbitrary translations measured
only in the face seminorm. The null and face masses are compared separately. -/

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem smoother_smallerEnvelope_shift_le {m : ℕ} (s : FaceSmoother m)
    (x : Vector m) {v : Vector m} (hv : ‖v‖ ≤ s.bandwidth) :
    s.F (x+v)*(1-s.F (x+v)) ≤ Real.exp 3*(s.F x*(1-s.F x)) := by
  have hF := s.F_shift_le x hv
  rw [div_self s.bandwidth_pos.ne'] at hF
  have hθ := s.theta_shift_le x hv
  change 1-s.F (x+v) ≤ Real.exp (2*s.bandwidth/s.bandwidth)*(1-s.F x) at hθ
  rw [mul_div_cancel_right₀ _ s.bandwidth_pos.ne'] at hθ
  have hm := mul_le_mul hF hθ (sub_nonneg.mpr (s.F_le_one (x+v)))
    (mul_nonneg (Real.exp_nonneg _) (s.F_pos x).le)
  exact hm.trans_eq (by
    calc
      _ = (Real.exp 1*Real.exp 2)*(s.F x*(1-s.F x)) := by ring
      _ = _ := by rw [← Real.exp_add]; norm_num)

theorem logistic_smallerEnvelope_shift_le {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) {v : Vector r} (hv : faceProjectionNorm U v ≤ h) :
    logisticNullWeight U a h (x+v)*(1-logisticNullWeight U a h (x+v)) ≤
      Real.exp 3*(logisticNullWeight U a h x*(1-logisticNullWeight U a h x)) := by
  have hs := smoother_smallerEnvelope_shift_le (upperFaceSmoother a h hh) (U.mulVec x) hv
  rw [← Matrix.mulVec_add, upperFaceSmoother_F, upperFaceSmoother_F] at hs
  exact hs

end
end RectangleCLT.Companion.SplitV4
