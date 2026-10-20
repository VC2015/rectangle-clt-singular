import RectangleCLT.Normalization
import Mathlib.MeasureTheory.Integral.Prod

/-! Fourth-moment bounds for products of expectations. Independent copies
are used only as an actual product integration space; no independence of the
coordinate functions on the original probability space is assumed. -/

open MeasureTheory

universe u

namespace RectangleCLT

private theorem abs_four_product_le_fourth_mean_core (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h₁ : 2 * (a * b) ^ 2 ≤ a ^ 4 + b ^ 4 := by
    nlinarith only [sq_nonneg (a ^ 2 - b ^ 2)]
  have h₂ : 2 * (c * d) ^ 2 ≤ c ^ 4 + d ^ 4 := by
    nlinarith only [sq_nonneg (c ^ 2 - d ^ 2)]
  have h₃ : 2 * |a * b * c * d| ≤ (a * b) ^ 2 + (c * d) ^ 2 := by
    calc
      _ = 2 * |a * b| * |c * d| := by simp only [abs_mul]; ring
      _ ≤ |a * b| ^ 2 + |c * d| ^ 2 := by
        nlinarith only [sq_nonneg (|a * b| - |c * d|)]
      _ = _ := by rw [sq_abs, sq_abs]
  nlinarith only [h₁, h₂, h₃]

private theorem integral_abs_four_product_le_fourth_mean_core
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (a b c d : Ω → ℝ)
    (hprod : Integrable (fun ω => a ω * b ω * c ω * d ω) μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    (∫ ω, |a ω * b ω * c ω * d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
  have h := integral_mono_ae hprod.abs ((((ha.add hb).add hc).add hd).div_const 4)
    (ae_of_all μ (fun ω => abs_four_product_le_fourth_mean_core (a ω) (b ω) (c ω) (d ω)))
  change (∫ ω, |a ω * b ω * c ω * d ω| ∂μ) ≤
    (∫ ω, (a ω ^ 4 + b ω ^ 4 + c ω ^ 4 + d ω ^ 4) / 4 ∂μ) at h
  rw [integral_div,
    integral_add (f := fun ω => a ω ^ 4 + b ω ^ 4 + c ω ^ 4) (g := fun ω => d ω ^ 4)
      ((ha.add hb).add hc) hd,
    integral_add (f := fun ω => a ω ^ 4 + b ω ^ 4) (g := fun ω => c ω ^ 4)
      (ha.add hb) hc, integral_add ha hb] at h
  exact h

private theorem integrable_fourth_fst {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ℝ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) :
    Integrable (fun z : Ω × Ω => a z.1 ^ 4) (μ.prod μ) := by
  simpa only [mul_one] using ha.mul_prod (integrable_const (1 : ℝ))

private theorem integrable_fourth_snd {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ℝ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) :
    Integrable (fun z : Ω × Ω => a z.2 ^ 4) (μ.prod μ) := by
  simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod ha

private theorem integral_fourth_fst {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ℝ) :
    (∫ z : Ω × Ω, a z.1 ^ 4 ∂μ.prod μ) = ∫ ω, a ω ^ 4 ∂μ := by
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := μ) (ν := μ) (fun ω => a ω ^ 4))

private theorem integral_fourth_snd {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ℝ) :
    (∫ z : Ω × Ω, a z.2 ^ 4 ∂μ.prod μ) = ∫ ω, a ω ^ 4 ∂μ := by
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_snd (μ := μ) (ν := μ) (fun ω => a ω ^ 4))

/-- Pair products in two independent copies are bounded by the mean of
their four marginal fourth moments. The four coordinates in one copy may
have arbitrary dependence. -/
theorem integral_abs_pair_mul_integral_abs_pair_le_fourth_mean
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b c d : Ω → ℝ)
    (hab : Integrable (fun ω => a ω * b ω) μ)
    (hcd : Integrable (fun ω => c ω * d ω) μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    (∫ ω, |a ω * b ω| ∂μ) * (∫ ω, |c ω * d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
  have hprod : Integrable (fun z : Ω × Ω => a z.1 * b z.1 * c z.2 * d z.2) (μ.prod μ) := by
    simpa only [mul_assoc] using hab.mul_prod hcd
  have h := integral_abs_four_product_le_fourth_mean_core (μ.prod μ)
    (fun z => a z.1) (fun z => b z.1) (fun z => c z.2) (fun z => d z.2) hprod
    (integrable_fourth_fst μ a ha) (integrable_fourth_fst μ b hb)
    (integrable_fourth_snd μ c hc) (integrable_fourth_snd μ d hd)
  have heq : (∫ z : Ω × Ω, |a z.1 * b z.1 * c z.2 * d z.2| ∂μ.prod μ) =
      (∫ ω, |a ω * b ω| ∂μ) * (∫ ω, |c ω * d ω| ∂μ) := by
    calc
      _ = ∫ z : Ω × Ω, |a z.1 * b z.1| * |c z.2 * d z.2| ∂μ.prod μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by simp only [abs_mul]; ring)
      _ = _ := integral_prod_mul (μ := μ) (ν := μ) (fun ω => |a ω * b ω|) (fun ω => |c ω * d ω|)
  simpa only [heq, integral_fourth_fst, integral_fourth_snd] using h

/-- The common-point quadratic correction is bounded using fourth moments
of individual coordinates, with no moment of their maximum norm. -/
theorem abs_integral_pair_mul_integral_abs_pair_le_fourth_mean
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b c d : Ω → ℝ)
    (hab : Integrable (fun ω => a ω * b ω) μ)
    (hcd : Integrable (fun ω => c ω * d ω) μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    |∫ ω, a ω * b ω ∂μ| * (∫ ω, |c ω * d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
  exact (mul_le_mul_of_nonneg_right abs_integral_le_integral_abs
    (integral_nonneg (fun ω => abs_nonneg (c ω * d ω)))).trans
    (integral_abs_pair_mul_integral_abs_pair_le_fourth_mean μ a b c d hab hcd ha hb hc hd)

/-- The common-point cubic correction admits the same fourth-moment bound,
again without coordinate independence or a maximum-norm moment. -/
theorem abs_integral_triple_mul_integral_abs_le_fourth_mean
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b c d : Ω → ℝ)
    (habc : Integrable (fun ω => a ω * b ω * c ω) μ) (hd₁ : Integrable d μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    |∫ ω, a ω * b ω * c ω ∂μ| * (∫ ω, |d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
  have hprod : Integrable (fun z : Ω × Ω => a z.1 * b z.1 * c z.1 * d z.2) (μ.prod μ) :=
    habc.mul_prod hd₁
  have h := integral_abs_four_product_le_fourth_mean_core (μ.prod μ)
    (fun z => a z.1) (fun z => b z.1) (fun z => c z.1) (fun z => d z.2) hprod
    (integrable_fourth_fst μ a ha) (integrable_fourth_fst μ b hb)
    (integrable_fourth_fst μ c hc) (integrable_fourth_snd μ d hd)
  have heq : (∫ z : Ω × Ω, |a z.1 * b z.1 * c z.1 * d z.2| ∂μ.prod μ) =
      (∫ ω, |a ω * b ω * c ω| ∂μ) * (∫ ω, |d ω| ∂μ) := by
    rw [show (fun z : Ω × Ω => |a z.1 * b z.1 * c z.1 * d z.2|) =
      (fun z => |a z.1 * b z.1 * c z.1| * |d z.2|) by
        funext z; exact abs_mul _ _]
    exact integral_prod_mul (μ := μ) (ν := μ) (fun ω => |a ω * b ω * c ω|) (fun ω => |d ω|)
  have hbound : (∫ ω, |a ω * b ω * c ω| ∂μ) * (∫ ω, |d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
    simpa only [heq, integral_fourth_fst, integral_fourth_snd] using h
  exact (mul_le_mul_of_nonneg_right abs_integral_le_integral_abs
    (integral_nonneg (fun ω => abs_nonneg (d ω)))).trans hbound

end RectangleCLT
