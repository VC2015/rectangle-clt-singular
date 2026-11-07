import RectangleCLTCompanion.SplitV4.LogisticGammaTrace

/-! The literal common-threshold theta-power derivative in printed B.4. -/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The actual power of the complementary logistic weight has exactly
the derivative used in equation `F theta k trick`. -/
theorem hasDerivAt_shiftOffsets_theta_pow {m : ℕ}
    (s : FaceSmoother m) (x : Vector m) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun z => (s.shiftOffsets z).theta x ^ (k + 1))
      (-((k : ℝ) + 1) / s.bandwidth *
        ((s.shiftOffsets t).F x * (s.shiftOffsets t).theta x ^ (k + 1))) t := by
  have hh := ((hasDerivAt_const t (1 : ℝ)).sub (s.hasDerivAt_shiftOffsets_F x t)).pow (k + 1)
  convert hh using 1
  dsimp only [FaceSmoother.theta, FaceWeights.theta, FaceSmoother.F]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, zero_sub, pow_succ]
  ring

/-- The printed differential representation of the actual selector sum. -/
theorem transition_weight_eq_theta_power_derivative {m : ℕ}
    (s : FaceSmoother m) (x : Vector m) (k : ℕ) :
    s.F x * s.theta x ^ (k + 1) =
      -(s.bandwidth / ((k : ℝ) + 1)) *
        deriv (fun z => (s.shiftOffsets z).theta x ^ (k + 1)) 0 := by
  rw [(hasDerivAt_shiftOffsets_theta_pow s x k 0).deriv]
  have hs0 : s.shiftOffsets 0 = s := by cases s; simp [FaceSmoother.shiftOffsets]
  rw [hs0]
  field_simp [s.bandwidth_pos.ne']
  <;> ring

end
end RectangleCLT.Companion.SplitV4.Printed
