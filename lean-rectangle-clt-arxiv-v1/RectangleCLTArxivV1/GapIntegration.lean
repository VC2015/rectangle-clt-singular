import RectangleCLTArxivV1.SupplementalIRestriction
import RectangleCLTArxivV1.SupplementalGCapIntegration

/-! Literal scalar integration in Appendix H. The late derivative estimate
has an inverse determinant gap, while its time integral costs only the
logarithm of the correlation gap. Analytic remainder bounds are explicit
inputs of the scalar reduction below. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set
open scoped Interval
noncomputable section
set_option autoImplicit false

def positiveGapGain (c : ℝ) : ℝ := 1+Real.log (1/c)

theorem one_le_positiveGapGain {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    1 ≤ positiveGapGain c := by
  have hlog : 0 ≤ Real.log (1/c) := Real.log_nonneg ((le_div_iff₀ hc).2 (by simpa))
  unfold positiveGapGain
  linarith

theorem positiveGapGain_det_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    positiveGapGain (exceptionalCutoffDet c) ≤ positiveGapGain c := by
  have hd := exceptionalCutoffDet_bounds hc hc1
  have hr : 1/exceptionalCutoffDet c ≤ 1/c :=
    one_div_le_one_div_of_le hc hd.2.1
  exact add_le_add_left (Real.log_le_log (one_div_pos.mpr hd.1) hr) 1

/-- The exact initial-scale ratio in the early/late crossing calculation. -/
theorem positiveGap_seed_ratio {δ κ L h d : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hL : 0 < L) (hh : 0 < h) (hd : 0 < d) :
    (δ^2*κ*L*Real.sqrt L/d)/
      ((δ^2*κ*L/h)*Real.sqrt (L*h^2)) = 1/d := by
  rw [Real.sqrt_mul hL.le, Real.sqrt_sq hh.le]
  field_simp
  <;> ring

/-- This retains every crossing position in the actual finite interval;
`cap_integral_single_minimum` supplies those three cases. -/
theorem positiveGap_integral_minimum {ε b A d : ℝ}
    (hε : 0 < ε) (hb : ε ≤ b) (hA : 0 < A) (hd : 0 < d) (hd1 : d ≤ 1) :
    (∫ v in ε..b, min (A/v) ((A*Real.sqrt ε/d)/(v*Real.sqrt v))) ≤
      2*A*positiveGapGain d := by
  have hS : 0 < A*Real.sqrt ε/d := by positivity
  have h := cap_integral_single_minimum hε hb hA hS
  have heq : (A*Real.sqrt ε/d)/(A*Real.sqrt ε) = 1/d := by field_simp <;> ring
  have hlog : 0 ≤ Real.log (1/d) :=
    Real.log_nonneg ((le_div_iff₀ hd).2 (by simpa))
  rw [heq,max_eq_left hlog] at h
  exact h

/-- An explicit intermediate: a genuinely interval-integrable remainder
with both early and late bounds has only logarithmic gap cost. -/
theorem positiveGap_integrated_remainder_bound {ε A C c : ℝ} {R : ℝ → ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : IntervalIntegrable R volume ε (1+ε))
    (hearly : ∀ v ∈ Ioo ε (1+ε), |R v| ≤ C*(A/v))
    (hlate : ∀ v ∈ Ioo ε (1+ε), |R v| ≤
      C*((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v))) :
    (∫ v in ε..1+ε, |R v|) ≤ 2*C*A*positiveGapGain c := by
  have hd := exceptionalCutoffDet_bounds hc hc1
  have hab : ε ≤ 1+ε := by linarith
  have hcont := (cap_const_inv_continuousOn (b := 1+ε) hε A).inf
    (cap_const_inv_mul_sqrt_continuousOn hε (A*Real.sqrt ε/exceptionalCutoffDet c))
  have hi := (hcont.intervalIntegrable_of_Icc (μ := volume) hab).const_mul C
  have hpoint (v : ℝ) (hv : v ∈ Ioo ε (1+ε)) : |R v| ≤
      C*min (A/v) ((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v)) := by
    rw [mul_min_of_nonneg _ _ hC]
    exact le_min (hearly v hv) (hlate v hv)
  have hi' := intervalIntegral.integral_mono_on_of_le_Ioo hab hR.abs hi hpoint
  rw [intervalIntegral.integral_const_mul] at hi'
  have hmin := positiveGap_integral_minimum hε hab hA hd.1 hd.2.2
  have hgain := positiveGapGain_det_le hc hc1
  calc
    _ ≤ C*(∫ v in ε..1+ε,
        min (A/v) ((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v))) := hi'
    _ ≤ C*(2*A*positiveGapGain (exceptionalCutoffDet c)) :=
      mul_le_mul_of_nonneg_left hmin hC
    _ ≤ C*(2*A*positiveGapGain c) := by gcongr
    _ = _ := by ring

end
end RectangleCLTArxivV1
