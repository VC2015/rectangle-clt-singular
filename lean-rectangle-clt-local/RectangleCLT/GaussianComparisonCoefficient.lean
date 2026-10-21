import RectangleCLT.GlobalCovariance
import RectangleCLT.ProxyCovariance

/-! The exact Gaussian comparison coefficient, with the full-eigenvalue
alternative omitted when its denominator vanishes. -/

namespace RectangleCLT

noncomputable section

def gaussianComparisonCoefficient (b c : ℝ) : ℝ :=
  if 0 < b then min (1 / b) (1 / c) else 1 / c

theorem gaussianComparisonCoefficient_nonneg {b c : ℝ} (hc : 0 < c) :
    0 ≤ gaussianComparisonCoefficient b c := by
  unfold gaussianComparisonCoefficient
  split_ifs with hb
  · exact le_min (one_div_nonneg.mpr hb.le) (one_div_nonneg.mpr hc.le)
  · exact one_div_nonneg.mpr hc.le

theorem gaussianComparisonCoefficient_le_pair {b c : ℝ} :
    gaussianComparisonCoefficient b c ≤ 1 / c := by
  unfold gaussianComparisonCoefficient
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem gaussianComparisonCoefficient_le_global {b c : ℝ} (hb : 0 < b) :
    gaussianComparisonCoefficient b c ≤ 1 / b := by
  simp only [gaussianComparisonCoefficient, if_pos hb]
  exact min_le_left _ _

theorem gaussianComparisonCoefficient_of_nonpositive {b c : ℝ} (hb : b ≤ 0) :
    gaussianComparisonCoefficient b c = 1 / c := by
  simp only [gaussianComparisonCoefficient, if_neg (not_lt.mpr hb)]

theorem gaussianComparisonCoefficient_eq_inv_max {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) :
    gaussianComparisonCoefficient b c = 1 / max b c := by
  by_cases hb0 : 0 < b
  · rw [gaussianComparisonCoefficient, if_pos hb0]
    by_cases hbc : b ≤ c
    · rw [max_eq_right hbc, min_eq_right ((one_div_le_one_div hc hb0).mpr hbc)]
    · have hcb : c ≤ b := le_of_not_ge hbc
      rw [max_eq_left hcb, min_eq_left ((one_div_le_one_div hb0 hc).mpr hcb)]
  · have hbzero : b = 0 := le_antisymm (le_of_not_gt hb0) hb
    subst b
    simp only [gaussianComparisonCoefficient, lt_self_iff_false, if_false,
      max_eq_right hc.le]

end

end RectangleCLT
