import RectangleCLTCompanion.LowerSkewTail
import RectangleCLTCompanion.LowerSkewExponential
import RectangleCLTCompanion.LowerMaxCDFActual

/-! The sharp lower scale on the genuine independent-coordinate
two-point construction. All scalar-tail approximations are discharged
by the preceding actual change-of-measure and cumulant proofs. -/

open Filter

namespace RectangleCLT.Companion

noncomputable section

theorem lowerSkewTail_sharp_facts {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (nhds 0)) :
    Tendsto (fun n => lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
        standardNormalUpperTail (normalMaxThreshold (p n)) - 1) atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 < lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
        standardNormalUpperTail (normalMaxThreshold (p n)) - 1) ∧
      atTop.IsBoundedUnder (·≤·) (fun n =>
        (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
          standardNormalUpperTail (normalMaxThreshold (p n)) - 1) /
            lowerSkewRate (B n) (p n) n) ∧
      Real.sqrt 2 / 4 ≤ liminf (fun n =>
        (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
          standardNormalUpperTail (normalMaxThreshold (p n)) - 1) /
            lowerSkewRate (B n) (p n) n) atTop := by
  have hR : ∀ᶠ n in atTop, 0 < lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
      standardNormalUpperTail (normalMaxThreshold (p n)) := by
    filter_upwards [lowerSkew_cramer_eventually hB hp hr] with n hn
    exact div_pos hn.1 (standardNormalUpperTail_pos _)
  have hh := lower_log_relative_tail_to_relative_tail
    (by positivity : 0 < Real.sqrt 2 / 4)
    (Filter.Eventually.of_forall (fun n => lowerSkewCoefficient_bounds (hB n)))
    hr (lowerSkewRate_eventually_pos hB hp) hR (lowerSkew_log_tail_normalized hB hp hr)
  exact hh.2

/-- The lower constant in companion Theorem 4 is attained already on
one explicit maximum rectangle, without a limit assumption on B. -/
theorem lowerScaleRectangle_liminf {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (nhds 0)) :
    Real.sqrt 2 / (4 * Real.exp 1) ≤ liminf (fun n =>
      rectangleError (lowerArrayLaw (B n) n (p n))
        (sumVector (lowerNormalizedRows (n := n) (p := p n))) 1
        (partialMaximumRectangle (p n) (p n) (normalMaxThreshold (p n))) /
          lowerSkewRate (B n) (p n) n) atTop := by
  have hs := lowerSkewTail_sharp_facts hB hp hr
  have hh := lowerMaximum_rectangleError_liminf hp
    (Filter.Eventually.of_forall (fun n => (le_rfl : p n ≤ p n)))
    hs.1 hs.2.1 (lowerSkewRate_eventually_pos hB hp) hs.2.2.1 hs.2.2.2
  apply le_trans _ hh
  rw [Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv]
  ring_nf
  exact le_rfl

end

end RectangleCLT.Companion
