import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A finite Taylor estimate with an explicit chain of actual derivatives.
The harmless remainder constant is one; the cubic coefficient is exact. -/

open Set

namespace RectangleCLT.Companion

theorem lower_meanvalue_bound {f f' : ℝ → ℝ} {T M : ℝ} (hT : 0 ≤ T)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc 0 T, |f' x| ≤ M) :
    |f T - f 0| ≤ M * T := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Icc 0 T) => (hf x).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
    (convex_Icc (0 : ℝ) T) (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT)
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hT] using hh

theorem lower_taylor_chain_cubic {f f₁ f₂ f₃ f₄ : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (h₀ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (h₃ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hbound : ∀ x ∈ Icc 0 T, |f₄ x| ≤ M) :
    |f T - f 0 - f₁ 0 * T - f₂ 0 * T ^ 2 / 2 - f₃ 0 * T ^ 3 / 6| ≤ M * T ^ 4 := by
  have h3 (x : ℝ) (hx : x ∈ Icc 0 T) : |f₃ x - f₃ 0| ≤ M * x :=
    lower_meanvalue_bound hx.1 h₃ (fun u hu => hbound u ⟨hu.1, hu.2.trans hx.2⟩)
  have h2 (x : ℝ) (hx : x ∈ Icc 0 T) :
      |f₂ x - f₂ 0 - f₃ 0 * x| ≤ M * x ^ 2 := by
    have hd (u : ℝ) : HasDerivAt (fun u => f₂ u - f₂ 0 - f₃ 0 * u)
        (f₃ u - f₃ 0) u := by
      simpa only [sub_zero, mul_one] using
        ((h₂ u).sub_const (f₂ 0)).sub ((hasDerivAt_id u).const_mul (f₃ 0))
    have hh := lower_meanvalue_bound hx.1 hd (fun u hu =>
      (h3 u ⟨hu.1, hu.2.trans hx.2⟩).trans (mul_le_mul_of_nonneg_left hu.2 hM))
    simp only [mul_zero, sub_self, sub_zero] at hh
    convert hh using 1 <;> ring
  have h1 (x : ℝ) (hx : x ∈ Icc 0 T) :
      |f₁ x - f₁ 0 - f₂ 0 * x - f₃ 0 * x ^ 2 / 2| ≤ M * x ^ 3 := by
    have hd (u : ℝ) : HasDerivAt
        (fun u => f₁ u - f₁ 0 - f₂ 0 * u - f₃ 0 * u ^ 2 / 2)
        (f₂ u - f₂ 0 - f₃ 0 * u) u := by
      have hh := (((h₁ u).sub_const (f₁ 0)).sub
        ((hasDerivAt_id u).const_mul (f₂ 0))).sub
        (((hasDerivAt_id u).pow 2).const_mul (f₃ 0) |>.div_const 2)
      simp only [id_eq] at hh
      convert hh using 1 <;> ring
    have hh := lower_meanvalue_bound hx.1 hd (fun u hu =>
      (h2 u ⟨hu.1, hu.2.trans hx.2⟩).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1 hu.2 2) hM))
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div,
      sub_self, sub_zero] at hh
    convert hh using 1 <;> ring
  have hd (u : ℝ) : HasDerivAt
      (fun u => f u - f 0 - f₁ 0 * u - f₂ 0 * u ^ 2 / 2 - f₃ 0 * u ^ 3 / 6)
      (f₁ u - f₁ 0 - f₂ 0 * u - f₃ 0 * u ^ 2 / 2) u := by
    have hh := ((((h₀ u).sub_const (f 0)).sub
      ((hasDerivAt_id u).const_mul (f₁ 0))).sub
      (((hasDerivAt_id u).pow 2).const_mul (f₂ 0) |>.div_const 2)).sub
      (((hasDerivAt_id u).pow 3).const_mul (f₃ 0) |>.div_const 6)
    simp only [id_eq] at hh
    convert hh using 1 <;> ring
  have hh := lower_meanvalue_bound hT hd (fun u hu =>
    (h1 u hu).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1 hu.2 3) hM))
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0),
    zero_div, sub_self, sub_zero] at hh
  convert hh using 1 <;> ring

end RectangleCLT.Companion
