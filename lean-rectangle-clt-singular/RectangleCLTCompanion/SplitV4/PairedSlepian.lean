import RectangleCLTCompanion.SplitV4.PairedExchange
import RectangleCLTCompanion.FourthIdentityTaylor
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

/-!
The vector trapezoidal step in the paired Slepian argument of Lemma G.3.
Derivative tensors have genuine Frechet derivative witnesses of their
contractions. The full time derivative and conditional-coefficient assembly
are separate obligations.
-/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4

noncomputable section

abbrev DerivativeOne (p : ℕ) := Vector p →L[ℝ] ℝ
abbrev DerivativeTwo (p : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Vector p) ℝ
abbrev DerivativeThree (p : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Vector p) ℝ
abbrev DerivativeFour (p : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Vector p) ℝ

/-- A C4 test with actual derivative witnesses and globally bounded
first through fourth derivatives. Multilinearity is explicit in each tensor.
No probability or comparison estimate is part of this regularity contract. -/
structure C4Test (p : ℕ) where
  value : Vector p → ℝ
  gradient : Vector p → DerivativeOne p
  hessian : Vector p → DerivativeTwo p
  third : Vector p → DerivativeThree p
  fourth : Vector p → DerivativeFour p
  has_gradient : ∀ x, HasFDerivAt value (gradient x) x
  has_hessian : ∀ x v, HasFDerivAt (fun z => gradient z v)
    ((hessian x).toContinuousLinearMap (fun _ => v) 0) x
  has_third : ∀ x v, HasFDerivAt (fun z => hessian z (fun _ => v))
    ((third x).toContinuousLinearMap (fun _ => v) 0) x
  has_fourth : ∀ x v, HasFDerivAt (fun z => third z (fun _ => v))
    ((fourth x).toContinuousLinearMap (fun _ => v) 0) x
  continuous_gradient : Continuous gradient
  continuous_hessian : Continuous hessian
  continuous_third : Continuous third
  continuous_fourth : Continuous fourth
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_gradient_le : ∀ x, ‖gradient x‖ ≤ bound
  norm_hessian_le : ∀ x, ‖hessian x‖ ≤ bound
  norm_third_le : ∀ x, ‖third x‖ ≤ bound
  norm_fourth_le : ∀ x, ‖fourth x‖ ≤ bound

namespace C4Test

variable {p : ℕ} (f : C4Test p)

def secondDiagonal (x y : Vector p) : ℝ := f.hessian x (fun _ => y)
def thirdDiagonal (x y : Vector p) : ℝ := f.third x (fun _ => y)
def fourthDiagonal (x y : Vector p) : ℝ := f.fourth x (fun _ => y)

private theorem hasDerivAt_segment (x y : Vector p) (a r : ℝ) :
    HasDerivAt (fun t : ℝ => x + (a * t) • y) (a • y) r := by
  simpa only [mul_one] using
    (((hasDerivAt_id r).const_mul a).smul_const y).const_add x

private theorem diagonal_update {k : ℕ} [NeZero k] (v : Vector p) :
    Function.update (fun _ : Fin k => v) 0 v = (fun _ => v) := by simp

theorem hasDerivAt_gradient_segment (x y : Vector p) (a r : ℝ) :
    HasDerivAt (fun t => f.gradient (x + (a * t) • y) y)
      (a * f.secondDiagonal (x + (a * r) • y) y) r := by
  have hd := (f.has_hessian (x + (a * r) • y) y).comp_hasDerivAt r
    (hasDerivAt_segment x y a r)
  simpa only [map_smul, smul_eq_mul,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, diagonal_update,
    secondDiagonal] using hd

theorem hasDerivAt_hessian_segment (x y : Vector p) (a r : ℝ) :
    HasDerivAt (fun t => f.secondDiagonal (x + (a * t) • y) y)
      (a * f.thirdDiagonal (x + (a * r) • y) y) r := by
  have hd := (f.has_third (x + (a * r) • y) y).comp_hasDerivAt r
    (hasDerivAt_segment x y a r)
  simpa only [map_smul, smul_eq_mul,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, diagonal_update,
    secondDiagonal, thirdDiagonal] using hd

theorem hasDerivAt_third_segment (x y : Vector p) (a r : ℝ) :
    HasDerivAt (fun t => f.thirdDiagonal (x + (a * t) • y) y)
      (a * f.fourthDiagonal (x + (a * r) • y) y) r := by
  have hd := (f.has_fourth (x + (a * r) • y) y).comp_hasDerivAt r
    (hasDerivAt_segment x y a r)
  simpa only [map_smul, smul_eq_mul,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, diagonal_update,
    thirdDiagonal, fourthDiagonal] using hd

theorem continuous_secondDiagonal :
    Continuous (fun z : Vector p × Vector p => f.secondDiagonal z.1 z.2) := by
  unfold secondDiagonal
  exact (f.continuous_hessian.comp continuous_fst).eval
    (continuous_pi fun _ => continuous_snd)

theorem continuous_fourthDiagonal :
    Continuous (fun z : Vector p × Vector p => f.fourthDiagonal z.1 z.2) := by
  unfold fourthDiagonal
  exact (f.continuous_fourth.comp continuous_fst).eval
    (continuous_pi fun _ => continuous_snd)

theorem continuous_hessian_segment (x y : Vector p) (a : ℝ) :
    Continuous (fun r : ℝ => f.secondDiagonal (x + (a * r) • y) y) :=
  f.continuous_secondDiagonal.comp
    (show Continuous (fun r : ℝ => (x + (a * r) • y, y)) by fun_prop)

theorem continuous_fourth_segment (x y : Vector p) (a : ℝ) :
    Continuous (fun r : ℝ => f.fourthDiagonal (x + (a * r) • y) y) :=
  f.continuous_fourthDiagonal.comp
    (show Continuous (fun r : ℝ => (x + (a * r) • y, y)) by fun_prop)

/-- Exact vector gradient increment, with the Hessian at both actual segment
endpoints and the signed fourth derivative trapezoidal remainder. -/
theorem gradient_segment_trapezoidal (x y : Vector p) (a : ℝ) :
    f.gradient (x + a • y) y - f.gradient x y =
      a / 2 * (f.secondDiagonal x y + f.secondDiagonal (x + a • y) y) -
        a ^ 3 / 2 * ∫ r in (0 : ℝ)..1,
          r * (1 - r) * f.fourthDiagonal (x + (a * r) • y) y := by
  let g : ℝ → ℝ := fun r => f.secondDiagonal (x + (a * r) • y) y
  let g' : ℝ → ℝ := fun r => a * f.thirdDiagonal (x + (a * r) • y) y
  let g'' : ℝ → ℝ := fun r => a ^ 2 * f.fourthDiagonal (x + (a * r) • y) y
  have hg (r : ℝ) : HasDerivAt g (g' r) r := f.hasDerivAt_hessian_segment x y a r
  have hg' (r : ℝ) : HasDerivAt g' (g'' r) r := by
    convert (f.hasDerivAt_third_segment x y a r).const_mul a using 1
    dsimp only [g', g'']
    ring
  have hc : Continuous g'' := continuous_const.mul (f.continuous_fourth_segment x y a)
  have htrap := integral_trapezoidal g g' g'' hg hg' hc
  have hinc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => f.hasDerivAt_gradient_segment x y a r)
    ((continuous_const.mul (f.continuous_hessian_segment x y a)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hinc
  have heq : (∫ r in (0 : ℝ)..1, r * (1 - r) * g'' r) =
      a ^ 2 * ∫ r in (0 : ℝ)..1,
        r * (1 - r) * f.fourthDiagonal (x + (a * r) • y) y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [g'']
    ring
  rw [heq] at htrap
  norm_num only [g, mul_zero, mul_one, zero_smul, add_zero] at htrap hinc
  rw [htrap] at hinc
  linarith

theorem norm_gradient_eval_le (x y : Vector p) :
    ‖f.gradient x y‖ ≤ f.bound * ‖y‖ :=
  ((f.gradient x).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (f.norm_gradient_le x) (norm_nonneg y))

theorem norm_secondDiagonal_le (x y : Vector p) :
    ‖f.secondDiagonal x y‖ ≤ f.bound * ‖y‖ ^ 2 := by
  have hn := (f.hessian x).le_opNorm (fun _ => y)
  have hh : ‖f.secondDiagonal x y‖ ≤ ‖f.hessian x‖ * ‖y‖ ^ 2 := by
    simpa only [secondDiagonal, Finset.prod_const, Fintype.card_fin] using hn
  exact hh.trans (mul_le_mul_of_nonneg_right (f.norm_hessian_le x) (sq_nonneg _))

theorem norm_fourthDiagonal_le (x y : Vector p) :
    ‖f.fourthDiagonal x y‖ ≤ f.bound * ‖y‖ ^ 4 := by
  have hn := (f.fourth x).le_opNorm (fun _ => y)
  have hh : ‖f.fourthDiagonal x y‖ ≤ ‖f.fourth x‖ * ‖y‖ ^ 4 := by
    simpa only [fourthDiagonal, Finset.prod_const, Fintype.card_fin] using hn
  exact hh.trans (mul_le_mul_of_nonneg_right (f.norm_fourth_le x) (by positivity))

theorem secondDiagonal_neg (x y : Vector p) :
    f.secondDiagonal x (-y) = f.secondDiagonal x y := by
  have hh := (f.hessian x).map_smul_univ (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => y)
  simpa [secondDiagonal] using hh

theorem secondDiagonal_zero (x : Vector p) : f.secondDiagonal x 0 = 0 := by
  exact (f.hessian x).map_coord_zero (0 : Fin 2) rfl

/-- The actual fourth derivative segment remainder from the trapezoidal
identity, including the integrable kernel on the unit interval. -/
def trapezoidalRemainder (x y : Vector p) (a : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, r * (1 - r) * f.fourthDiagonal (x + (a * r) • y) y

theorem measurable_trapezoidalRemainder (a : ℝ) :
    Measurable (fun z : Vector p × Vector p => f.trapezoidalRemainder z.1 z.2 a) := by
  have hh : Continuous (fun z : (Vector p × Vector p) × ℝ =>
      z.2 * (1 - z.2) * f.fourthDiagonal (z.1.1 + (a * z.2) • z.1.2) z.1.2) := by
    apply Continuous.mul
    · fun_prop
    · exact f.continuous_fourthDiagonal.comp
        (show Continuous (fun z : (Vector p × Vector p) × ℝ =>
          (z.1.1 + (a * z.2) • z.1.2, z.1.2)) by fun_prop)
  have hm := hh.measurable.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  simpa only [trapezoidalRemainder, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    using hm.measurable

theorem norm_trapezoidalRemainder_le (x y : Vector p) (a : ℝ) :
    ‖f.trapezoidalRemainder x y a‖ ≤ f.bound * ‖y‖ ^ 4 := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := f.bound * ‖y‖ ^ 4)
    (f := fun r => r * (1 - r) * f.fourthDiagonal (x + (a * r) • y) y) ?_
  · simpa only [trapezoidalRemainder, sub_zero, abs_one, mul_one] using hi
  · intro r hr
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    have hk : ‖r * (1 - r)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.1.le (sub_nonneg.mpr hr.2))]
      nlinarith [sq_nonneg r, hr.2]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hk (norm_nonneg _)).trans
      (by simpa only [one_mul] using f.norm_fourthDiagonal_le (x + (a * r) • y) y)

theorem integrable_gradient_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V Y : Ω → Vector p)
    (hV : Measurable V) (hY : Measurable Y) (h : ℝ)
    (hbound : ∀ ω, ‖Y ω‖ ≤ h) :
    Integrable (fun ω => f.gradient (V ω) (Y ω)) μ := by
  have hc : Continuous (fun z : Vector p × Vector p => f.gradient z.1 z.2) :=
    (f.continuous_gradient.comp continuous_fst).clm_apply continuous_snd
  apply (integrable_const (f.bound * h)).mono'
    ((hc.measurable.comp (hV.prodMk hY)).aestronglyMeasurable)
  exact ae_of_all _ (fun ω => (f.norm_gradient_eval_le _ _).trans
    (mul_le_mul_of_nonneg_left (hbound ω) f.bound_nonneg))

theorem integrable_secondDiagonal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V Y : Ω → Vector p)
    (hV : Measurable V) (hY : Measurable Y) (h : ℝ)
    (hbound : ∀ ω, ‖Y ω‖ ≤ h) :
    Integrable (fun ω => f.secondDiagonal (V ω) (Y ω)) μ := by
  apply (integrable_const (f.bound * h ^ 2)).mono'
    ((f.continuous_secondDiagonal.measurable.comp (hV.prodMk hY)).aestronglyMeasurable)
  exact ae_of_all _ (fun ω => (f.norm_secondDiagonal_le _ _).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2)
      f.bound_nonneg))

theorem integrable_trapezoidalRemainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V Y : Ω → Vector p)
    (hV : Measurable V) (hY : Measurable Y) (h : ℝ)
    (hbound : ∀ ω, ‖Y ω‖ ≤ h) (a : ℝ) :
    Integrable (fun ω => f.trapezoidalRemainder (V ω) (Y ω) a) μ := by
  apply (integrable_const (f.bound * h ^ 4)).mono'
    (((f.measurable_trapezoidalRemainder a).comp (hV.prodMk hY)).aestronglyMeasurable)
  exact ae_of_all _ (fun ω => (f.norm_trapezoidalRemainder_le _ _ a).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 4)
      f.bound_nonneg))

/-- Integrating the genuine vector Taylor identity under an arbitrary law
with bounded increments. The base may depend on those increments. -/
theorem integral_gradient_segment_trapezoidal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V Y : Ω → Vector p) (hV : Measurable V) (hY : Measurable Y)
    (h : ℝ) (hbound : ∀ ω, ‖Y ω‖ ≤ h) (a : ℝ) :
    (∫ ω, f.gradient (V ω + a • Y ω) (Y ω) - f.gradient (V ω) (Y ω) ∂μ) =
      a / 2 * ((∫ ω, f.secondDiagonal (V ω) (Y ω) ∂μ) +
        ∫ ω, f.secondDiagonal (V ω + a • Y ω) (Y ω) ∂μ) -
      a ^ 3 / 2 * ∫ ω, f.trapezoidalRemainder (V ω) (Y ω) a ∂μ := by
  have hi₀ := f.integrable_secondDiagonal μ V Y hV hY h hbound
  have hi₁ := f.integrable_secondDiagonal μ (fun ω => V ω + a • Y ω) Y
    (hV.add (measurable_const.smul hY)) hY h hbound
  have hiR := f.integrable_trapezoidalRemainder μ V Y hV hY h hbound a
  have hiA : Integrable (fun ω => a / 2 * (f.secondDiagonal (V ω) (Y ω) +
      f.secondDiagonal (V ω + a • Y ω) (Y ω))) μ := (hi₀.add hi₁).const_mul _
  calc
    _ = ∫ ω, a / 2 * (f.secondDiagonal (V ω) (Y ω) +
        f.secondDiagonal (V ω + a • Y ω) (Y ω)) -
        a ^ 3 / 2 * f.trapezoidalRemainder (V ω) (Y ω) a ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => f.gradient_segment_trapezoidal (V ω) (Y ω) a)
    _ = _ := by
      rw [integral_sub hiA (hiR.const_mul _),
        integral_const_mul, integral_add hi₀ hi₁, integral_const_mul]

theorem measurable_pairedTruncatedIncrement {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Vector p) (hX : Measurable X) (h : ℝ) :
    Measurable (fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h) := by
  have hd := (hX.comp measurable_snd).sub (hX.comp measurable_fst)
  exact Measurable.ite (measurableSet_le hd.norm measurable_const) hd measurable_const

theorem norm_pairedTruncatedIncrement_le (x y : Vector p) {h : ℝ} (hh : 0 ≤ h) :
    ‖pairedTruncatedIncrement x y h‖ ≤ h := by
  unfold pairedTruncatedIncrement
  split_ifs with he
  · exact he
  · simpa only [norm_zero] using hh

/-- The vector trapezoidal expectation identity at an actual paired-copy
point. No symmetry or identical-law assumption between different summands
is used: this theorem pairs one observation with a copy of its own law.
The truncation makes every displayed expectation genuinely integrable. -/
theorem integral_paired_gradient_increment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (base : Vector p) (a h : ℝ) (hh : 0 ≤ h) :
    let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
    let U := fun z : Ω × Ω => base + a • X z.1
    (∫ z, f.gradient (U z + a • Y z) (Y z) - f.gradient (U z) (Y z) ∂μ.prod μ) =
      a * (∫ z, f.secondDiagonal (U z) (Y z) ∂μ.prod μ) -
        a ^ 3 / 2 * ∫ z, f.trapezoidalRemainder (U z) (Y z) a ∂μ.prod μ := by
  let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
  let U := fun z : Ω × Ω => base + a • X z.1
  have hY : Measurable Y := measurable_pairedTruncatedIncrement X hX h
  have hU : Measurable U := measurable_const.add
    (measurable_const.smul (hX.comp measurable_fst))
  have hbound : ∀ z, ‖Y z‖ ≤ h := fun z =>
    norm_pairedTruncatedIncrement_le (X z.1) (X z.2) hh
  have hi := f.integrable_secondDiagonal (μ.prod μ) U Y hU hY h hbound
  have hcopy := (pairedTruncatedIncrement_integral_even_exchange μ X base a h
    (fun v z => f.secondDiagonal z v) (fun v z => f.secondDiagonal_neg z v)
    f.secondDiagonal_zero hi).2
  have ht := f.integral_gradient_segment_trapezoidal (μ.prod μ) U Y hU hY h hbound a
  change (∫ z, f.secondDiagonal (U z) (Y z) ∂μ.prod μ) =
    (∫ z, f.secondDiagonal (U z + a • Y z) (Y z) ∂μ.prod μ) at hcopy
  rw [← hcopy] at ht
  change (∫ z, f.gradient (U z + a • Y z) (Y z) -
      f.gradient (U z) (Y z) ∂μ.prod μ) = _
  rw [ht]
  ring

/-- The resulting paired-copy Stein balance for the truncated increment.
This is the exact gradient/Hessian/fourth-derivative part of G.3 before
the large-increment mean, Gaussian integration by parts, and time derivative
are assembled. -/
theorem integral_paired_truncated_gradient
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (base : Vector p) (a h : ℝ) (hh : 0 ≤ h) :
    let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
    let U := fun z : Ω × Ω => base + a • X z.1
    (∫ z, f.gradient (U z) (Y z) ∂μ.prod μ) =
      -(a / 2) * (∫ z, f.secondDiagonal (U z) (Y z) ∂μ.prod μ) +
        a ^ 3 / 4 * ∫ z, f.trapezoidalRemainder (U z) (Y z) a ∂μ.prod μ := by
  let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
  let U := fun z : Ω × Ω => base + a • X z.1
  have hY : Measurable Y := measurable_pairedTruncatedIncrement X hX h
  have hU : Measurable U := measurable_const.add
    (measurable_const.smul (hX.comp measurable_fst))
  have hbound : ∀ z, ‖Y z‖ ≤ h := fun z =>
    norm_pairedTruncatedIncrement_le (X z.1) (X z.2) hh
  have hi₀ := f.integrable_gradient_eval (μ.prod μ) U Y hU hY h hbound
  have hi₁ := f.integrable_gradient_eval (μ.prod μ) (fun z => U z + a • Y z) Y
    (hU.add (measurable_const.smul hY)) hY h hbound
  have hcopy := (pairedTruncatedIncrement_integral_exchange μ X base a h
    (fun v z => f.gradient z v) (fun v z => (f.gradient z).map_neg v) hi₀).2
  have ht := f.integral_paired_gradient_increment μ X hX base a h hh
  change (∫ z, f.gradient (U z) (Y z) ∂μ.prod μ) =
    -(∫ z, f.gradient (U z + a • Y z) (Y z) ∂μ.prod μ) at hcopy
  change (∫ z, f.gradient (U z + a • Y z) (Y z) -
      f.gradient (U z) (Y z) ∂μ.prod μ) = _ at ht
  rw [integral_sub hi₁ hi₀] at ht
  change (∫ z, f.gradient (U z) (Y z) ∂μ.prod μ) = _
  linarith

theorem integrable_gradient_eval_of_integrable_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V Y : Ω → Vector p) (hV : Measurable V) (hY : Measurable Y)
    (hYint : Integrable (fun ω => ‖Y ω‖) μ) :
    Integrable (fun ω => f.gradient (V ω) (Y ω)) μ := by
  have hc : Continuous (fun z : Vector p × Vector p => f.gradient z.1 z.2) :=
    (f.continuous_gradient.comp continuous_fst).clm_apply continuous_snd
  exact (hYint.const_mul f.bound).mono'
    ((hc.measurable.comp (hV.prodMk hY)).aestronglyMeasurable)
    (ae_of_all _ (fun ω => f.norm_gradient_eval_le (V ω) (Y ω)))

/-- Centering of the actual independent copy supplies the original-observation
gradient term. This uses genuine first-moment integrability, with no
symmetry assumption and no independence between the increment and the base. -/
theorem integral_centered_copy_gradient
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (hXint : Integrable X μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (base : Vector p) (a : ℝ) :
    (∫ z : Ω × Ω, f.gradient (base + a • X z.1) (X z.2 - X z.1) ∂μ.prod μ) =
      -(∫ z : Ω × Ω, f.gradient (base + a • X z.1) (X z.1) ∂μ.prod μ) := by
  have hV : Measurable (fun z : Ω × Ω => base + a • X z.1) :=
    measurable_const.add (measurable_const.smul (hX.comp measurable_fst))
  have hN₀ : Integrable (fun z : Ω × Ω => ‖X z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using hXint.norm.mul_prod (integrable_const (1 : ℝ))
  have hN₁ : Integrable (fun z : Ω × Ω => ‖X z.2‖) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hXint.norm
  have hi₀ : Integrable (fun z : Ω × Ω => f.gradient (base + a • X z.1) (X z.1))
      (μ.prod μ) := f.integrable_gradient_eval_of_integrable_norm (μ.prod μ)
        _ _ hV (hX.comp measurable_fst) hN₀
  have hi₁ : Integrable (fun z : Ω × Ω => f.gradient (base + a • X z.1) (X z.2))
      (μ.prod μ) := f.integrable_gradient_eval_of_integrable_norm (μ.prod μ)
        _ _ hV (hX.comp measurable_snd) hN₁
  have hz : (∫ z : Ω × Ω, f.gradient (base + a • X z.1) (X z.2) ∂μ.prod μ) = 0 := by
    rw [integral_prod _ hi₁]
    apply integral_eq_zero_of_ae
    exact ae_of_all _ (fun ω => by
      change (∫ y, f.gradient (base + a • X ω) (X y) ∂μ) = 0
      rw [(f.gradient (base + a • X ω)).integral_comp_comm hXint, hmean, map_zero])
  simp_rw [map_sub]
  rw [integral_sub hi₁ hi₀, hz, zero_sub]

/-- One summand's paired Stein identity with its large increment retained.
The tail term is an actual expectation and is not discarded by centering.
After multiplying by the Slepian factor and summing, this gives the signed
fourth-derivative coefficient and the large-increment mean term of G.3. -/
theorem integral_paired_stein_with_large_increment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (hXint : Integrable X μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (base : Vector p) (a h : ℝ) (hh : 0 ≤ h) :
    let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
    let U := fun z : Ω × Ω => base + a • X z.1
    (∫ z, f.gradient (U z) (X z.1) ∂μ.prod μ) =
      a / 2 * (∫ z, f.secondDiagonal (U z) (Y z) ∂μ.prod μ) -
        a ^ 3 / 4 * (∫ z, f.trapezoidalRemainder (U z) (Y z) a ∂μ.prod μ) -
        ∫ z, f.gradient (U z) (X z.2 - X z.1 - Y z) ∂μ.prod μ := by
  let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
  let U := fun z : Ω × Ω => base + a • X z.1
  have hY : Measurable Y := measurable_pairedTruncatedIncrement X hX h
  have hU : Measurable U := measurable_const.add
    (measurable_const.smul (hX.comp measurable_fst))
  have hbound : ∀ z, ‖Y z‖ ≤ h := fun z =>
    norm_pairedTruncatedIncrement_le (X z.1) (X z.2) hh
  have hiY := f.integrable_gradient_eval (μ.prod μ) U Y hU hY h hbound
  have hN₀ : Integrable (fun z : Ω × Ω => ‖X z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using hXint.norm.mul_prod (integrable_const (1 : ℝ))
  have hN₁ : Integrable (fun z : Ω × Ω => ‖X z.2‖) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hXint.norm
  have hi₀ : Integrable (fun z : Ω × Ω => f.gradient (U z) (X z.1)) (μ.prod μ) :=
    f.integrable_gradient_eval_of_integrable_norm (μ.prod μ)
      U _ hU (hX.comp measurable_fst) hN₀
  have hi₁ : Integrable (fun z : Ω × Ω => f.gradient (U z) (X z.2)) (μ.prod μ) :=
    f.integrable_gradient_eval_of_integrable_norm (μ.prod μ)
      U _ hU (hX.comp measurable_snd) hN₁
  have hiDiff : Integrable (fun z => f.gradient (U z) (X z.2 - X z.1)) (μ.prod μ) := by
    simpa only [map_sub] using hi₁.sub hi₀
  have htail : (∫ z, f.gradient (U z) (X z.2 - X z.1 - Y z) ∂μ.prod μ) =
      (∫ z, f.gradient (U z) (X z.2 - X z.1) ∂μ.prod μ) -
        ∫ z, f.gradient (U z) (Y z) ∂μ.prod μ := by
    calc
      _ = ∫ z, f.gradient (U z) (X z.2 - X z.1) - f.gradient (U z) (Y z) ∂μ.prod μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => (f.gradient (U z)).map_sub _ _)
      _ = _ := integral_sub hiDiff hiY
  have hcenter := f.integral_centered_copy_gradient μ X hX hXint hmean base a
  have htrunc := f.integral_paired_truncated_gradient μ X hX base a h hh
  change (∫ z, f.gradient (U z) (X z.1) ∂μ.prod μ) = _
  change (∫ z, f.gradient (U z) (X z.2 - X z.1) ∂μ.prod μ) =
    -(∫ z, f.gradient (U z) (X z.1) ∂μ.prod μ) at hcenter
  rw [htail, hcenter]
  rw [htrunc]
  ring

/-- The one-summand identity remains exact after averaging an arbitrary
independent random base. In particular the base may contain all other
summands and an independent, possibly singular, Gaussian contribution. -/
theorem integral_paired_stein_with_independent_base
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (X : Ω → Vector p) (hX : Measurable X) (hXint : Integrable X μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (V : Γ → Vector p) (hV : Measurable V)
    (a h : ℝ) (hh : 0 ≤ h) :
    let Y := fun z : Γ × (Ω × Ω) =>
      pairedTruncatedIncrement (X z.2.1) (X z.2.2) h
    let U := fun z : Γ × (Ω × Ω) => V z.1 + a • X z.2.1
    (∫ z, f.gradient (U z) (X z.2.1) ∂ν.prod (μ.prod μ)) =
      a / 2 * (∫ z, f.secondDiagonal (U z) (Y z) ∂ν.prod (μ.prod μ)) -
        a ^ 3 / 4 * (∫ z, f.trapezoidalRemainder (U z) (Y z) a ∂ν.prod (μ.prod μ)) -
        ∫ z, f.gradient (U z) (X z.2.2 - X z.2.1 - Y z) ∂ν.prod (μ.prod μ) := by
  let Y := fun z : Γ × (Ω × Ω) =>
    pairedTruncatedIncrement (X z.2.1) (X z.2.2) h
  let U := fun z : Γ × (Ω × Ω) => V z.1 + a • X z.2.1
  have hY : Measurable Y :=
    (measurable_pairedTruncatedIncrement X hX h).comp measurable_snd
  have hU : Measurable U := (hV.comp measurable_fst).add
    (measurable_const.smul (hX.comp (measurable_fst.comp measurable_snd)))
  have hbound : ∀ z, ‖Y z‖ ≤ h := fun z =>
    norm_pairedTruncatedIncrement_le (X z.2.1) (X z.2.2) hh
  have hN₀ : Integrable (fun z : Ω × Ω => ‖X z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using hXint.norm.mul_prod (integrable_const (1 : ℝ))
  have hN₁ : Integrable (fun z : Ω × Ω => ‖X z.2‖) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hXint.norm
  have hM₀ : Integrable (fun z : Γ × (Ω × Ω) => ‖X z.2.1‖) (ν.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hN₀
  have hM₁ : Integrable (fun z : Γ × (Ω × Ω) => ‖X z.2.2‖) (ν.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hN₁
  let G := fun z : Γ × (Ω × Ω) => f.gradient (U z) (X z.2.1)
  let H := fun z : Γ × (Ω × Ω) => f.secondDiagonal (U z) (Y z)
  let R := fun z : Γ × (Ω × Ω) => f.trapezoidalRemainder (U z) (Y z) a
  let T := fun z : Γ × (Ω × Ω) => f.gradient (U z) (X z.2.2 - X z.2.1 - Y z)
  have hG : Integrable G (ν.prod (μ.prod μ)) :=
    f.integrable_gradient_eval_of_integrable_norm _ U _ hU
      (hX.comp (measurable_fst.comp measurable_snd)) hM₀
  have hG' : Integrable (fun z : Γ × (Ω × Ω) => f.gradient (U z) (X z.2.2))
      (ν.prod (μ.prod μ)) :=
    f.integrable_gradient_eval_of_integrable_norm _ U _ hU
      (hX.comp (measurable_snd.comp measurable_snd)) hM₁
  have hGY := f.integrable_gradient_eval (ν.prod (μ.prod μ)) U Y hU hY h hbound
  have hH : Integrable H (ν.prod (μ.prod μ)) :=
    f.integrable_secondDiagonal _ U Y hU hY h hbound
  have hR : Integrable R (ν.prod (μ.prod μ)) :=
    f.integrable_trapezoidalRemainder _ U Y hU hY h hbound a
  have hT : Integrable T (ν.prod (μ.prod μ)) := by
    simpa only [T, G, map_sub] using (hG'.sub hG).sub hGY
  have hpoint (γ : Γ) :
      (∫ z, G (γ, z) ∂μ.prod μ) =
        a / 2 * (∫ z, H (γ, z) ∂μ.prod μ) -
          a ^ 3 / 4 * (∫ z, R (γ, z) ∂μ.prod μ) -
          ∫ z, T (γ, z) ∂μ.prod μ :=
    f.integral_paired_stein_with_large_increment μ X hX hXint hmean (V γ) a h hh
  have hiA : Integrable (fun γ => a / 2 * (∫ z, H (γ, z) ∂μ.prod μ) -
      a ^ 3 / 4 * (∫ z, R (γ, z) ∂μ.prod μ)) ν :=
    (hH.integral_prod_left.const_mul _).sub (hR.integral_prod_left.const_mul _)
  change (∫ z, G z ∂ν.prod (μ.prod μ)) = _
  calc
    _ = ∫ γ, ∫ z, G (γ, z) ∂μ.prod μ ∂ν := integral_prod _ hG
    _ = ∫ γ, a / 2 * (∫ z, H (γ, z) ∂μ.prod μ) -
        a ^ 3 / 4 * (∫ z, R (γ, z) ∂μ.prod μ) -
        (∫ z, T (γ, z) ∂μ.prod μ) ∂ν := integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_sub hiA hT.integral_prod_left,
        integral_sub (hH.integral_prod_left.const_mul _) (hR.integral_prod_left.const_mul _),
        integral_const_mul, integral_const_mul,
        ← integral_prod _ hH, ← integral_prod _ hR, ← integral_prod _ hT]

/-- Canonical iterated Frechet derivatives supply the actual derivative of
each diagonal contraction. This connects the explicit derivative-witness
API to an ordinary `ContDiff` function. -/
theorem hasFDerivAt_iterated_diagonal {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {k : ℕ} (hk : k < 4) (x v : Vector p) :
    HasFDerivAt (fun z => iteratedFDeriv ℝ k F z (fun _ => v))
      ((iteratedFDeriv ℝ (k + 1) F x).toContinuousLinearMap (fun _ => v) 0) x := by
  have hd := ((hF.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast hk)) x).hasFDerivAt
  have hh := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vector p) ℝ
    (fun _ => v)).hasFDerivAt.comp x hd
  convert hh using 1

/-- Every ordinary C4 function whose first four actual iterated derivatives
are bounded yields the test contract used by the Slepian identities. The
constructor introduces no interpolation or comparison premise. -/
def ofContDiff (F : Vector p → ℝ) (hF : ContDiff ℝ 4 F) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C) :
    C4Test p where
  value := F
  gradient := fderiv ℝ F
  hessian := iteratedFDeriv ℝ 2 F
  third := iteratedFDeriv ℝ 3 F
  fourth := iteratedFDeriv ℝ 4 F
  has_gradient := fun x => (hF.differentiable (by norm_num) x).hasFDerivAt
  has_hessian := fun x v => by
    simpa only [iteratedFDeriv_one_apply] using
      hasFDerivAt_iterated_diagonal hF (k := 1) (by norm_num) x v
  has_third := fun x v => hasFDerivAt_iterated_diagonal hF (k := 2) (by norm_num) x v
  has_fourth := fun x v => hasFDerivAt_iterated_diagonal hF (k := 3) (by norm_num) x v
  continuous_gradient := hF.continuous_fderiv (by norm_num)
  continuous_hessian := hF.continuous_iteratedFDeriv
    (by exact_mod_cast (show (2 : ℕ) ≤ 4 by decide))
  continuous_third := hF.continuous_iteratedFDeriv
    (by exact_mod_cast (show (3 : ℕ) ≤ 4 by decide))
  continuous_fourth := hF.continuous_iteratedFDeriv
    (by exact_mod_cast (show (4 : ℕ) ≤ 4 by decide))
  bound := C
  bound_nonneg := hC
  norm_gradient_le := fun x => by
    have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := F) (x := x)
    simp only [norm_iteratedFDeriv_zero, zero_add] at hn
    rw [hn]
    exact hbound 1 (by norm_num) (by norm_num) x
  norm_hessian_le := hbound 2 (by norm_num) (by norm_num)
  norm_third_le := hbound 3 (by norm_num) (by norm_num)
  norm_fourth_le := hbound 4 (by norm_num) (by norm_num)

end C4Test

end

end RectangleCLT.Companion.SplitV4
