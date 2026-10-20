import RectangleCLT.BernoulliComparisonFinal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact integral Taylor identities used by the fourth-order Bernoulli
comparison. The integral kernels are obtained by differentiating finite
weighted telescopes, rather than assuming a Taylor remainder formula. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion

noncomputable section

theorem integral_taylor_one (f₀ f₁ : ℝ → ℝ)
    (h₀ : ∀ t, HasDerivAt f₀ (f₁ t) t) (hc : Continuous f₁) (a : ℝ) :
    f₀ a - f₀ 0 = ∫ r in (0 : ℝ)..1, a * f₁ (a * r) := by
  have hd (t : ℝ) : HasDerivAt (fun r => f₀ (a * r)) (a * f₁ (a * t)) t := by
    convert (h₀ (a * t)).comp t ((hasDerivAt_id t).const_mul a) using 1
    ring
  have hc' : Continuous (fun r => a * f₁ (a * r)) :=
    continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc'.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero] using hi.symm

theorem integral_taylor_two (f₀ f₁ f₂ : ℝ → ℝ)
    (h₀ : ∀ t, HasDerivAt f₀ (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t) (hc : Continuous f₂) (a : ℝ) :
    f₀ a - (f₀ 0 + a * f₁ 0) =
      ∫ r in (0 : ℝ)..1, a ^ 2 * (1 - r) * f₂ (a * r) := by
  let H : ℝ → ℝ := fun r => f₀ (a * r) + a * (1 - r) * f₁ (a * r)
  have hd (t : ℝ) : HasDerivAt H (a ^ 2 * (1 - t) * f₂ (a * t)) t := by
    have ha := (hasDerivAt_id t).const_mul a
    have hl := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hh := ((h₀ (a * t)).comp t ha).add
      ((hl.const_mul a).mul ((h₁ (a * t)).comp t ha))
    convert hh using 1
    simp only [H, Function.comp_apply, id_eq]
    ring
  have hc' : Continuous (fun r => a ^ 2 * (1 - r) * f₂ (a * r)) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).mul
      (hc.comp (continuous_const.mul continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc'.intervalIntegrable 0 1)
  norm_num only [H, mul_one, mul_zero, sub_self, zero_mul, sub_zero, add_zero] at hi
  exact hi.symm

theorem integral_taylor_three (f₀ f₁ f₂ f₃ : ℝ → ℝ)
    (h₀ : ∀ t, HasDerivAt f₀ (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t, HasDerivAt f₂ (f₃ t) t) (hc : Continuous f₃) (a : ℝ) :
    f₀ a - (f₀ 0 + a * f₁ 0 + a ^ 2 / 2 * f₂ 0) =
      ∫ r in (0 : ℝ)..1, (a ^ 3 / 2) * (1 - r) ^ 2 * f₃ (a * r) := by
  let H : ℝ → ℝ := fun r => f₀ (a * r) + a * (1 - r) * f₁ (a * r) +
    (a ^ 2 / 2) * (1 - r) ^ 2 * f₂ (a * r)
  have hd (t : ℝ) : HasDerivAt H ((a ^ 3 / 2) * (1 - t) ^ 2 * f₃ (a * t)) t := by
    have ha := (hasDerivAt_id t).const_mul a
    have hl := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hh := (((h₀ (a * t)).comp t ha).add
      ((hl.const_mul a).mul ((h₁ (a * t)).comp t ha))).add
        (((hl.pow 2).const_mul (a ^ 2 / 2)).mul ((h₂ (a * t)).comp t ha))
    convert hh using 1
    simp only [H, Function.comp_apply, id_eq]
    ring
  have hc' : Continuous (fun r => (a ^ 3 / 2) * (1 - r) ^ 2 * f₃ (a * r)) :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).mul
      (hc.comp (continuous_const.mul continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc'.intervalIntegrable 0 1)
  norm_num only [H, mul_one, mul_zero, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_mul, sub_zero, one_pow, add_zero] at hi
  exact hi.symm

theorem integral_taylor_four (f₀ f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ t, HasDerivAt f₀ (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t, HasDerivAt f₂ (f₃ t) t)
    (h₃ : ∀ t, HasDerivAt f₃ (f₄ t) t) (hc : Continuous f₄) (a : ℝ) :
    f₀ a - (f₀ 0 + a * f₁ 0 + a ^ 2 / 2 * f₂ 0 + a ^ 3 / 6 * f₃ 0) =
      ∫ r in (0 : ℝ)..1, (a ^ 4 / 6) * (1 - r) ^ 3 * f₄ (a * r) := by
  let H : ℝ → ℝ := fun r => f₀ (a * r) + a * (1 - r) * f₁ (a * r) +
    (a ^ 2 / 2) * (1 - r) ^ 2 * f₂ (a * r) +
    (a ^ 3 / 6) * (1 - r) ^ 3 * f₃ (a * r)
  have hd (t : ℝ) : HasDerivAt H ((a ^ 4 / 6) * (1 - t) ^ 3 * f₄ (a * t)) t := by
    have ha := (hasDerivAt_id t).const_mul a
    have hl := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hh := ((((h₀ (a * t)).comp t ha).add
      ((hl.const_mul a).mul ((h₁ (a * t)).comp t ha))).add
        (((hl.pow 2).const_mul (a ^ 2 / 2)).mul ((h₂ (a * t)).comp t ha))).add
          (((hl.pow 3).const_mul (a ^ 3 / 6)).mul ((h₃ (a * t)).comp t ha))
    convert hh using 1
    simp only [H, Function.comp_apply, id_eq]
    ring
  have hc' : Continuous (fun r => (a ^ 4 / 6) * (1 - r) ^ 3 * f₄ (a * r)) :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).mul
      (hc.comp (continuous_const.mul continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc'.intervalIntegrable 0 1)
  norm_num only [H, mul_one, mul_zero, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_mul, sub_zero, one_pow, add_zero] at hi
  exact hi.symm

end
end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

open Companion

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

theorem continuous_convolutionFourthDerivative_commonPoint (j k l m : Fin p) :
    Continuous (fun x => s.convolutionFourthDerivative ν x j k l m) := by
  simp_rw [s.convolutionFourthDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν
    (fun x => s.mixedFourthDerivativeF x j k l m)
    (s.continuous_fourthDerivative j k l m) _
    (fun x => s.norm_fourthDerivative_le x j k l m)

theorem continuous_convolutionTranslationD4 (y : Vector p) :
    Continuous (fun x => s.convolutionTranslationD4 ν x y) := by
  unfold convolutionTranslationD4
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro l _
  apply continuous_finset_sum
  intro m _
  exact ((((s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).mul
    continuous_const).mul continuous_const).mul continuous_const).mul continuous_const

theorem convolutionTaylor3_integral_remainder (x y : Vector p) (a : ℝ) :
    s.convolution ν (x + a • y) - s.convolutionTaylor3 ν x (a • y) =
      ∫ r in (0 : ℝ)..1, (a ^ 4 / 6) * (1 - r) ^ 3 *
        s.convolutionTranslationD4 ν (line x y (a * r)) y := by
  have hc : Continuous (fun r => s.convolutionTranslationD4 ν (line x y r) y) :=
    (s.continuous_convolutionTranslationD4 ν y).comp (by
      change Continuous (fun r : ℝ => x + r • y)
      exact continuous_const.add (continuous_id.smul continuous_const))
  have hh := integral_taylor_four
    (fun r => s.convolution ν (line x y r))
    (fun r => s.convolutionTranslationD1 ν (line x y r) y)
    (fun r => s.convolutionTranslationD2 ν (line x y r) y)
    (fun r => s.convolutionTranslationD3 ν (line x y r) y)
    (fun r => s.convolutionTranslationD4 ν (line x y r) y)
    (s.hasDerivAt_convolutionTranslationD0_line ν x y)
    (s.hasDerivAt_convolutionTranslationD1_line ν x y)
    (s.hasDerivAt_convolutionTranslationD2_line ν x y)
    (s.hasDerivAt_convolutionTranslationD3_line ν x y) hc a
  simp only [line_zero] at hh
  convert hh using 1
  unfold convolutionTaylor3
  rw [s.convolutionTranslationD1_smul, s.convolutionTranslationD2_smul,
    s.convolutionTranslationD3_smul]
  change s.convolution ν (line x y a) - _ = _
  ring

theorem convolutionGradientTaylor2_integral_remainder (x y : Vector p) (a : ℝ) :
    s.convolutionTranslationD1 ν (x + a • y) y - s.convolutionGradientTaylor2 ν x y a =
      ∫ r in (0 : ℝ)..1, (a ^ 3 / 2) * (1 - r) ^ 2 *
        s.convolutionTranslationD4 ν (line x y (a * r)) y := by
  have hc : Continuous (fun r => s.convolutionTranslationD4 ν (line x y r) y) :=
    (s.continuous_convolutionTranslationD4 ν y).comp (by
      change Continuous (fun r : ℝ => x + r • y)
      exact continuous_const.add (continuous_id.smul continuous_const))
  have hh := integral_taylor_three
    (fun r => s.convolutionTranslationD1 ν (line x y r) y)
    (fun r => s.convolutionTranslationD2 ν (line x y r) y)
    (fun r => s.convolutionTranslationD3 ν (line x y r) y)
    (fun r => s.convolutionTranslationD4 ν (line x y r) y)
    (s.hasDerivAt_convolutionTranslationD1_line ν x y)
    (s.hasDerivAt_convolutionTranslationD2_line ν x y)
    (s.hasDerivAt_convolutionTranslationD3_line ν x y) hc a
  simp only [line_zero] at hh
  convert hh using 1
  unfold convolutionGradientTaylor2
  change s.convolutionTranslationD1 ν (line x y a) y - _ = _
  ring

theorem convolutionSecondDerivative_integral_remainder
    (x y : Vector p) (j k : Fin p) (a : ℝ) :
    s.convolutionSecondDerivative ν (x + a • y) j k -
      (s.convolutionSecondDerivative ν x j k +
        a * ∑ l, s.convolutionThirdDerivative ν x j k l * y l) =
      ∫ r in (0 : ℝ)..1, a ^ 2 * (1 - r) *
        (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y (a * r)) j k l m * y l * y m) := by
  have hline : Continuous (line x y) := by
    change Continuous (fun r : ℝ => x + r • y)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hd₁ (t : ℝ) : HasDerivAt
      (fun r => ∑ l, s.convolutionThirdDerivative ν (line x y r) j k l * y l)
      (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y l * y m) t := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
      (s.hasDerivAt_convolutionThirdDerivative_line_sum_translation ν x y j k l t).mul_const (y l))
    convert hh using 1
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hc : Continuous (fun r => ∑ l, ∑ m,
      s.convolutionFourthDerivative ν (line x y r) j k l m * y l * y m) :=
    continuous_finset_sum _ (fun l _ => continuous_finset_sum _ (fun m _ =>
      (((s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp hline).mul
        continuous_const).mul continuous_const))
  have hh := integral_taylor_two
    (fun r => s.convolutionSecondDerivative ν (line x y r) j k)
    (fun r => ∑ l, s.convolutionThirdDerivative ν (line x y r) j k l * y l)
    (fun r => ∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y r) j k l m * y l * y m)
    (s.hasDerivAt_convolutionSecondDerivative_line_sum_translation ν x y j k) hd₁ hc a
  simpa only [line_zero] using hh

theorem convolutionThirdDerivative_integral_increment
    (x y : Vector p) (j k l : Fin p) (a : ℝ) :
    s.convolutionThirdDerivative ν (x + a • y) j k l - s.convolutionThirdDerivative ν x j k l =
      ∫ r in (0 : ℝ)..1, a *
        (∑ m, s.convolutionFourthDerivative ν (line x y (a * r)) j k l m * y m) := by
  have hline : Continuous (line x y) := by
    change Continuous (fun r : ℝ => x + r • y)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hc : Continuous (fun r => ∑ m,
      s.convolutionFourthDerivative ν (line x y r) j k l m * y m) :=
    continuous_finset_sum _ (fun m _ =>
      ((s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp hline).mul continuous_const)
  have hh := integral_taylor_one
    (fun r => s.convolutionThirdDerivative ν (line x y r) j k l)
    (fun r => ∑ m, s.convolutionFourthDerivative ν (line x y r) j k l m * y m)
    (s.hasDerivAt_convolutionThirdDerivative_line_sum_translation ν x y j k l) hc a
  simpa only [line_zero] using hh

end
end RectangleCLT.FaceSmoother
