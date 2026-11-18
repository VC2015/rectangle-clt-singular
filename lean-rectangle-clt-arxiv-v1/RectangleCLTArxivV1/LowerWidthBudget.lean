import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar error budgets for the lower construction with two independent
counts. The coordinate count controls the remainder, while the rare-shift
count occurs in the leading width-sensitive scale. -/

namespace RectangleCLTArxivV1

noncomputable section
set_option autoImplicit false

def lowerWidthScale (a ell g n : ℝ) : ℝ := a * ell * g / Real.sqrt n

/-- The linear comparison error loses one rare-shift logarithm against
the actual width-sensitive leading scale. -/
theorem lowerWidthBudget_linear {a ell g n R c : ℝ}
    (ha : 1 ≤ a) (hell : 1 ≤ ell) (_hn : 0 < n) (_hR : 0 ≤ R)
    (hc : 0 < c) (hg : c * Real.sqrt R ≤ g) :
    Real.sqrt R / Real.sqrt n ≤ lowerWidthScale a ell g n / (c * ell) := by
  have hg0 : 0 ≤ g := (mul_nonneg hc.le (Real.sqrt_nonneg R)).trans hg
  have hell0 : 0 < ell := zero_lt_one.trans_le hell
  have hag : c * Real.sqrt R ≤ a * g := hg.trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hg0])
  have hh := mul_le_mul_of_nonneg_left hag
    (div_nonneg hell0.le (Real.sqrt_nonneg n))
  apply (le_div_iff₀ (mul_pos hc hell0)).mpr
  unfold lowerWidthScale
  convert hh using 1 <;> ring

/-- The quadratic shift cost is directly controlled by the squared
width-sensitive scale. -/
theorem lowerWidthBudget_shift_square {a ell g n R c : ℝ}
    (hn : 0 < n) (hR : 0 ≤ R) (hc : 0 < c)
    (hg : c * Real.sqrt R ≤ g) :
    R * a ^ 2 * ell ^ 2 / n ≤ lowerWidthScale a ell g n ^ 2 / c ^ 2 := by
  have hh := pow_le_pow_left₀ (mul_nonneg hc.le (Real.sqrt_nonneg R)) hg 2
  rw [mul_pow, Real.sq_sqrt hR] at hh
  have hscaled := mul_le_mul_of_nonneg_left hh
    (div_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg ell)) hn.le)
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    (R * a ^ 2 * ell ^ 2 / n) * c ^ 2 = (a ^ 2 * ell ^ 2 / n) * (c ^ 2 * R) := by ring
    _ ≤ (a ^ 2 * ell ^ 2 / n) * g ^ 2 := hscaled
    _ = lowerWidthScale a ell g n ^ 2 := by
      unfold lowerWidthScale
      rw [div_pow, Real.sq_sqrt hn.le]
      ring

/-- The coordinate count may be smaller than the shift count. Its
quadratic comparison remainder still has the squared leading budget. -/
theorem lowerWidthBudget_coordinate_square {a ell g n R c : ℝ}
    (ha : 1 ≤ a) (hell : 1 ≤ ell) (hn : 0 < n) (hR : 0 ≤ R)
    (hRell : R ≤ 2 * ell) (hc : 0 < c) (hg : c * Real.sqrt R ≤ g) :
    R ^ 2 / n ≤ 2 * lowerWidthScale a ell g n ^ 2 / c ^ 2 := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hell2 : ell ≤ ell ^ 2 := by nlinarith
  have he : ell ≤ a ^ 2 * ell ^ 2 := hell2.trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg ell)])
  have hRf : R ≤ 2 * (a ^ 2 * ell ^ 2) := hRell.trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hRf (div_nonneg hR hn.le)
  calc
    R ^ 2 / n ≤ 2 * (R * a ^ 2 * ell ^ 2 / n) := by
      convert hh using 1 <;> ring
    _ ≤ 2 * (lowerWidthScale a ell g n ^ 2 / c ^ 2) :=
      mul_le_mul_of_nonneg_left (lowerWidthBudget_shift_square hn hR hc hg) (by norm_num)
    _ = _ := by ring

/-- The leading shift remains in the global Gaussian detection range
under the same width-sensitive smallness condition. -/
theorem lowerWidthBudget_range {a ell g n R c : ℝ}
    (ha : 1 ≤ a) (hell : 1 ≤ ell) (_hn : 0 < n) (hR : 1 ≤ R)
    (hRell : R ≤ 2 * ell) (hc : 0 < c) (hg : c * Real.sqrt R ≤ g) :
    R / Real.sqrt n ≤ (2 / c) * lowerWidthScale a ell g n := by
  have hsqrt : 1 ≤ Real.sqrt R := by
    nlinarith [Real.sq_sqrt (zero_le_one.trans hR), Real.sqrt_nonneg R]
  have hcg : c ≤ g := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hsqrt)]
  have hRl : R ≤ 2 * a * ell := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (zero_le_one.trans hell)]
  have hprod : c * R ≤ 2 * a * ell * g := by
    calc
      c * R ≤ c * (2 * a * ell) := mul_le_mul_of_nonneg_left hRl hc.le
      _ = (2 * a * ell) * c := by ring
      _ ≤ (2 * a * ell) * g := mul_le_mul_of_nonneg_left hcg (by positivity)
  have hh := div_le_div_of_nonneg_right hprod (Real.sqrt_nonneg n)
  calc
    R / Real.sqrt n ≤ (2 * lowerWidthScale a ell g n) / c := by
      apply (le_div_iff₀ hc).mpr
      unfold lowerWidthScale
      convert hh using 1 <;> ring
    _ = _ := by ring

/-- All scalar terms of the comparison remainder are bounded by a
linear scale divided by `ell` and a squared leading scale. -/
theorem lowerWidthBudget_combined {a ell g n R c K H M : ℝ}
    (ha : 1 ≤ a) (hell : 1 ≤ ell) (hn : 0 < n) (hR : 0 ≤ R)
    (hRell : R ≤ 2 * ell) (hc : 0 < c) (hg : c * Real.sqrt R ≤ g)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hM : 0 ≤ M) :
    K * (Real.sqrt R / Real.sqrt n + R ^ 2 / n) +
      (H * R / 2) * M * a ^ 2 * ell ^ 2 / n ≤
      (K / c) * (lowerWidthScale a ell g n / ell) +
        (2 * K + H * M / 2) * (lowerWidthScale a ell g n ^ 2 / c ^ 2) := by
  have h₁ := mul_le_mul_of_nonneg_left (lowerWidthBudget_linear ha hell hn hR hc hg) hK
  have h₂ := mul_le_mul_of_nonneg_left
    (lowerWidthBudget_coordinate_square ha hell hn hR hRell hc hg) hK
  have h₃ := mul_le_mul_of_nonneg_left (lowerWidthBudget_shift_square (a := a) (ell := ell) hn hR hc hg)
    (div_nonneg (mul_nonneg hH hM) (by norm_num : (0 : ℝ) ≤ 2))
  have hsum := add_le_add (add_le_add h₁ h₂) h₃
  convert hsum using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end
end RectangleCLTArxivV1
