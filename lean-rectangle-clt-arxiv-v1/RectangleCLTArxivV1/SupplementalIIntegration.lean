import RectangleCLTArxivV1.SupplementalIRestriction
import RectangleCLTArxivV1.SupplementalGCapIntegration

/-! The cutoff logarithm is paid by time integration, before the bandwidth
is chosen. The exceptional term is additive. -/
namespace RectangleCLTArxivV1
open MeasureTheory
noncomputable section
set_option autoImplicit false

def exceptionalCutoffLog (c : ℝ) : ℝ := 1+Real.log (1/c)

theorem one_le_exceptionalCutoffLog {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    1 ≤ exceptionalCutoffLog c := by
  unfold exceptionalCutoffLog
  have hi : 1 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  linarith [Real.log_nonneg hi]

theorem exceptionalCutoff_crossing_log_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    1+max (Real.log (1/exceptionalCutoffDet c)) 0 ≤ exceptionalCutoffLog c := by
  have hd := exceptionalCutoffDet_bounds hc hc1
  have hi : 1 ≤ 1/exceptionalCutoffDet c := (le_div_iff₀ hd.1).mpr (by simpa using hd.2.2)
  rw [max_eq_left (Real.log_nonneg hi)]
  unfold exceptionalCutoffLog
  have hr : 1/exceptionalCutoffDet c ≤ 1/c :=
    one_div_le_one_div_of_le hc hd.2.1
  exact add_le_add_left (Real.log_le_log (by positivity) hr) 1

/-- The crossing of v⁻¹ and v⁻³ᐟ² occurs at a/d_c². This bound includes
crossings outside the finite integration interval. -/
theorem exceptional_integral_separated_minimum {a b A c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : 0 < A) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ v in a..b, min (A/v)
      ((A*Real.sqrt a/exceptionalCutoffDet c)/(v*Real.sqrt v))) ≤
      2*A*exceptionalCutoffLog c := by
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  have hs : 0 < A*Real.sqrt a/exceptionalCutoffDet c := by positivity
  have he : (A*Real.sqrt a/exceptionalCutoffDet c)/(A*Real.sqrt a)=
      1/exceptionalCutoffDet c := by field_simp; ring
  have ht := cap_integral_single_minimum ha hab hA hs
  rw [he] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (exceptionalCutoff_crossing_log_le hc hc1) (by positivity))

/-- Adding a v-independent exceptional cost does not change the separated
crossing calculation. The interval length remains explicit. -/
theorem exceptional_integral_minimum_add_constant {a b A c E : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : 0 < A) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ v in a..b, min (A/v)
      ((A*Real.sqrt a/exceptionalCutoffDet c)/(v*Real.sqrt v))+E) ≤
      2*A*exceptionalCutoffLog c+(b-a)*E := by
  have hi : IntervalIntegrable (fun v : ℝ => min (A/v)
      ((A*Real.sqrt a/exceptionalCutoffDet c)/(v*Real.sqrt v))) volume a b :=
    ((cap_const_inv_continuousOn ha A).inf
    (cap_const_inv_mul_sqrt_continuousOn ha (A*Real.sqrt a/exceptionalCutoffDet c))).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const]
  simpa only [smul_eq_mul] using add_le_add_right (exceptional_integral_separated_minimum ha hab hA hc hc1) ((b-a)*E)

end
end RectangleCLTArxivV1
