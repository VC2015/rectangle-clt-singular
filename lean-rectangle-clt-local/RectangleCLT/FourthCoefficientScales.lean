import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Absorbing the Gaussian fourth-derivative coefficient costs into the
intrinsic sparse covariance denominator. -/

namespace RectangleCLT

private theorem self_le_sqrt_on_unit_interval {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ Real.sqrt x := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

theorem one_le_localFourthCost {c a3 a4 : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) :
    1 ≤ 1 / (c * a3 * a4) := by
  have ha3 := lt_of_lt_of_le ha4 ha43
  have hc := lt_of_lt_of_le ha3 ha3c
  have ha31 := ha3c.trans hc1
  have ha41 := ha43.trans ha31
  have hc3 : c * a3 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hc1 ha3.le).trans (by simpa using ha31)
  have hcost : c * a3 * a4 ≤ 1 :=
    (mul_le_mul_of_nonneg_left ha41 (mul_nonneg hc.le ha3.le)).trans (by simpa using hc3)
  exact (le_div_iff₀ (mul_pos (mul_pos hc ha3) ha4)).mpr (by simpa using hcost)

theorem one_div_pairGap_sq_le_localFourthCost {c a3 a4 : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) :
    1 / c ^ 2 ≤ 1 / (c * a3 * a4) := by
  have ha3 := lt_of_lt_of_le ha4 ha43
  have hc := lt_of_lt_of_le ha3 ha3c
  apply one_div_le_one_div_of_le (mul_pos (mul_pos hc ha3) ha4)
  have ha41 := ha43.trans (ha3c.trans hc1)
  have hprod : a3 * a4 ≤ c :=
    (mul_le_mul_of_nonneg_left ha41 ha3.le).trans (by simpa using ha3c)
  calc
    _ = c * (a3 * a4) := mul_assoc _ _ _
    _ ≤ c * c := mul_le_mul_of_nonneg_left hprod hc.le
    _ = _ := (pow_two _).symm

theorem one_div_sqrt_pairGap_cost_le_localFourthCost {c a3 a4 : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) :
    1 / (c * a3 * Real.sqrt c) ≤ 1 / (c * a3 * a4) := by
  have ha3 := lt_of_lt_of_le ha4 ha43
  have hc := lt_of_lt_of_le ha3 ha3c
  apply one_div_le_one_div_of_le (mul_pos (mul_pos hc ha3) ha4)
  exact mul_le_mul_of_nonneg_left
    ((ha43.trans ha3c).trans (self_le_sqrt_on_unit_interval hc.le hc1))
    (mul_nonneg hc.le ha3.le)

theorem one_div_sqrt_localThird_cost_le_localFourthCost {c a3 a4 : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) :
    1 / (c * a3 * Real.sqrt a3) ≤ 1 / (c * a3 * a4) := by
  have ha3 := lt_of_lt_of_le ha4 ha43
  have hc := lt_of_lt_of_le ha3 ha3c
  apply one_div_le_one_div_of_le (mul_pos (mul_pos hc ha3) ha4)
  exact mul_le_mul_of_nonneg_left
    (ha43.trans (self_le_sqrt_on_unit_interval ha3.le (ha3c.trans hc1)))
    (mul_nonneg hc.le ha3.le)

theorem one_div_pairGap_le_localFourthCost_mul_det {c a3 a4 d : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) (hd : c ≤ d) :
    1 / c ≤ (1 / (c * a3 * a4)) * d := by
  have ha3 := lt_of_lt_of_le ha4 ha43
  have hc := lt_of_lt_of_le ha3 ha3c
  calc
    _ = (1 / c ^ 2) * c := by field_simp; ring
    _ ≤ (1 / (c * a3 * a4)) * c :=
      mul_le_mul_of_nonneg_right
        (one_div_pairGap_sq_le_localFourthCost ha4 ha43 ha3c hc1) hc.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

theorem one_div_sqrt_pairGap_le_localFourthCost_mul_det {c a3 a4 d : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) (hd : c ≤ d) :
    1 / Real.sqrt c ≤ (1 / (c * a3 * a4)) * d := by
  have hc := lt_of_lt_of_le (lt_of_lt_of_le ha4 ha43) ha3c
  exact (one_div_le_one_div_of_le hc
    (self_le_sqrt_on_unit_interval hc.le hc1)).trans
      (one_div_pairGap_le_localFourthCost_mul_det ha4 ha43 ha3c hc1 hd)

theorem one_le_localFourthCost_mul_det {c a3 a4 d : ℝ}
    (ha4 : 0 < a4) (ha43 : a4 ≤ a3) (ha3c : a3 ≤ c) (hc1 : c ≤ 1) (hd : c ≤ d) :
    1 ≤ (1 / (c * a3 * a4)) * d := by
  have hc := lt_of_lt_of_le (lt_of_lt_of_le ha4 ha43) ha3c
  exact ((le_div_iff₀ hc).mpr (by simpa using hc1)).trans
    (one_div_pairGap_le_localFourthCost_mul_det ha4 ha43 ha3c hc1 hd)

end RectangleCLT
