import RectangleCLTArxivV1.LowerLemmaF1

/-! Literal normal weighted-tail derivative estimates used in the proof of F.1. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem lemma_F_1_weighted_normal_log_derivative {s : ℝ} (hs : 0 ≤ s) :
    |deriv (fun u => Real.log (normalWeightedTail u)) s| ≤ 8/(1+s) := by
  rw [(hasDerivAt_log_normalWeightedTail s).deriv]
  exact Printed.abs_log_normalWeightedTail_deriv_printed hs

theorem lemma_F_1_weighted_normal_derivative {s : ℝ} (hs : 0 ≤ s) :
    |deriv normalWeightedTail s| ≤ 16*(standardNormalPDF 0+1)/(1+s)^2 := by
  have hJ := normalWeightedTail_pos s
  have hlog := Printed.abs_log_normalWeightedTail_deriv_printed hs
  rw [abs_div,abs_of_pos hJ] at hlog
  have hnum := (div_le_iff₀ hJ).mp hlog
  rw [(hasDerivAt_normalWeightedTail s).deriv]
  calc
    _ ≤ 8/(1+s)*normalWeightedTail s := hnum
    _ ≤ 8/(1+s)*(2*(standardNormalPDF 0+1)/(1+s)) :=
      mul_le_mul_of_nonneg_left (Printed.normalWeightedTail_printed_upper hs) (by positivity)
    _ = _ := by
      have hd : 1+s ≠ 0 := ne_of_gt (by positivity)
      field_simp
      <;> ring

end
end RectangleCLTArxivV1
