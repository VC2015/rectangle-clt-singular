import RectangleCLTArxivV1.GapComparison
import RectangleCLTArxivV1.SupplementalIIntegration

/-! Literal cutoff crossing-time integration with the independent
exceptional cost added outside the minimum. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set
open scoped Interval
noncomputable section
set_option autoImplicit false

theorem exceptional_early_late_additive_bound {R A B E C : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hearly : |R|≤C*A) (hlate : |R|≤C*B+C*E) :
    |R|≤C*min A B+C*E := by
  rw [mul_min_of_nonneg _ _ hC,←min_add_add_right]
  exact le_min (hearly.trans (le_add_of_nonneg_right (mul_nonneg hC hE))) hlate

/-- This is the actual finite crossing integral from Appendix I. The
exceptional contribution is constant in time, so it has no logarithm. -/
theorem exceptional_integral_majorant_bound {ε A C c E : ℝ}
    (hε : 0<ε) (hA : 0<A) (hC : 0≤C) (hc : 0<c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1, positiveGapMajorant A ε C c (t+ε)+C*E)≤
      2*C*A*exceptionalCutoffLog c+C*E := by
  have he (t : ℝ) : positiveGapMajorant A ε C c (t+ε)+C*E=
      C*(min (A/(t+ε)) ((A*Real.sqrt ε/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε)))+E) := by
    unfold positiveGapMajorant
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hi := exceptional_integral_minimum_add_constant (E := E) hε
    (by linarith : ε≤1+ε) hA hc hc1
  have hshift : (∫ t in (0:ℝ)..1,
      min (A/(t+ε)) ((A*Real.sqrt ε/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε)))+E)=
      ∫ v in ε..1+ε, min (A/v) ((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v))+E := by
    simpa only [zero_add] using intervalIntegral.integral_comp_add_right
      (a := 0) (b := 1)
      (fun v : ℝ => min (A/v) ((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v))+E) ε
  rw [hshift]
  exact (mul_le_mul_of_nonneg_left hi hC).trans_eq (by ring)

end
end RectangleCLTArxivV1
