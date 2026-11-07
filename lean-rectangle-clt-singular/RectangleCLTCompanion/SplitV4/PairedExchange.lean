import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Proof ingredients for the paired exchange in split-V4 Lemma G.3.

The trapezoidal identity below is proved by the fundamental theorem of
calculus. The finite-dimensional exchange identities explicitly retain the
truncation event. These ingredients do not assert the full Slepian identity:
its differentiation, Gaussian integration by parts, conditional expectations,
and fourth-derivative integral exchanges are separate proof obligations.
-/

open MeasureTheory
open scoped Interval

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- The exact trapezoidal identity used in Lemma G.3, with its signed
second-derivative remainder. All derivative and integrability hypotheses are
actual regularity conditions, rather than an assumed Taylor estimate. -/
theorem integral_trapezoidal (g g' g'' : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (hc : Continuous g'') :
    (∫ r in (0 : ℝ)..1, g r) =
      (g 0 + g 1) / 2 -
        (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1, r * (1 - r) * g'' r := by
  let H : ℝ → ℝ := fun r =>
    (r - 1 / 2) * g r + (r * (1 - r) / 2) * g' r
  have hd (t : ℝ) : HasDerivAt H
      (g t + (1 / 2 : ℝ) * (t * (1 - t) * g'' t)) t := by
    have hi := hasDerivAt_id t
    have hleft := hi.sub_const (1 / 2 : ℝ)
    have hone := (hasDerivAt_const t (1 : ℝ)).sub hi
    have hright := (hi.mul hone).div_const 2
    convert (hleft.mul (hg t)).add (hright.mul (hg' t)) using 1 <;>
      dsimp only [H] <;> ring
  have hcg : Continuous g := continuous_iff_continuousAt.mpr
    (fun t => (hg t).continuousAt)
  have hcr : Continuous (fun r : ℝ => r * (1 - r) * g'' r) :=
    (continuous_id.mul (continuous_const.sub continuous_id)).mul hc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((hcg.add (continuous_const.mul hcr)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hcg.intervalIntegrable 0 1)
    ((continuous_const.mul hcr).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at hi
  norm_num [H] at hi
  linarith

/-- The norm cutoff is invariant under swapping an observation and its copy.
No symmetry hypothesis on the observation law is involved. -/
theorem truncation_event_swap {p : ℕ} (x y : Fin p → ℝ) (h : ℝ) :
    (‖y - x‖ ≤ h) ↔ (‖x - y‖ ≤ h) := by
  rw [norm_sub_rev]

/-- The bounded paired increment used in Appendix G. -/
def pairedTruncatedIncrement {p : ℕ} (x y : Fin p → ℝ) (h : ℝ) : Fin p → ℝ :=
  if ‖y - x‖ ≤ h then y - x else 0

/-- Swapping the two actual observations reverses the truncated increment.
This is true on the truncation event and on its complement. -/
theorem pairedTruncatedIncrement_swap {p : ℕ} (x y : Fin p → ℝ) (h : ℝ) :
    pairedTruncatedIncrement y x h = -pairedTruncatedIncrement x y h := by
  classical
  unfold pairedTruncatedIncrement
  rw [norm_sub_rev y x]
  split_ifs <;> ext j <;> simp <;> ring

/-- On the cutoff event, swapping the original observation replaces the
path point by the endpoint of the short truncated segment. Off that event
the increment vanishes, so the pairing still holds with its zero multiplier. -/
theorem pairedTruncatedIncrement_mul_exchange
    {p : ℕ} (x y base : Fin p → ℝ) (a h : ℝ)
    (F : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (hodd : ∀ v z, F (-v) z = -F v z) :
    F (pairedTruncatedIncrement y x h) (base + a • y) =
      -F (pairedTruncatedIncrement x y h)
        (base + a • x + a • pairedTruncatedIncrement x y h) := by
  classical
  have hzero (z : Fin p → ℝ) : F 0 z = 0 := by
    have hz := hodd 0 z
    simp only [neg_zero] at hz
    linarith
  rw [pairedTruncatedIncrement_swap, hodd]
  by_cases he : ‖y - x‖ ≤ h
  · have hv : pairedTruncatedIncrement x y h = y - x := if_pos he
    rw [hv]
    congr 2
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have hv : pairedTruncatedIncrement x y h = 0 := if_neg he
    rw [hv, hzero, hzero]

/-- Actual independent-copy exchange under the product law. The observation
law is arbitrary: in particular it need not be symmetric. The conclusion
includes genuine integrability of the paired endpoint term. -/
theorem pairedTruncatedIncrement_integral_exchange
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {p : ℕ} (X : Ω → Fin p → ℝ) (base : Fin p → ℝ) (a h : ℝ)
    (F : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (hodd : ∀ v z, F (-v) z = -F v z)
    (hI : Integrable (fun z : Ω × Ω =>
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1)) (μ.prod μ)) :
    Integrable (fun z : Ω × Ω =>
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1 +
          a • pairedTruncatedIncrement (X z.1) (X z.2) h)) (μ.prod μ) ∧
    (∫ z : Ω × Ω,
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1) ∂μ.prod μ) =
      -(∫ z : Ω × Ω,
        F (pairedTruncatedIncrement (X z.1) (X z.2) h)
          (base + a • X z.1 +
            a • pairedTruncatedIncrement (X z.1) (X z.2) h) ∂μ.prod μ) := by
  let f : Ω × Ω → ℝ := fun z =>
    F (pairedTruncatedIncrement (X z.1) (X z.2) h) (base + a • X z.1)
  let g : Ω × Ω → ℝ := fun z =>
    F (pairedTruncatedIncrement (X z.1) (X z.2) h)
      (base + a • X z.1 + a • pairedTruncatedIncrement (X z.1) (X z.2) h)
  have he (z : Ω × Ω) : f z.swap = -g z :=
    pairedTruncatedIncrement_mul_exchange (X z.1) (X z.2) base a h F hodd
  have hJ : Integrable g (μ.prod μ) := by
    apply hI.swap.neg.congr
    exact ae_of_all _ (fun z => by change -f z.swap = g z; rw [he, neg_neg])
  refine ⟨hJ, ?_⟩
  change (∫ z, f z ∂μ.prod μ) = -(∫ z, g z ∂μ.prod μ)
  calc
    _ = ∫ z, f z.swap ∂μ.prod μ := (integral_prod_swap f).symm
    _ = ∫ z, -g z ∂μ.prod μ := integral_congr_ae (ae_of_all _ he)
    _ = _ := integral_neg g

/-- The even contraction counterpart of the gradient pairing. For Hessian
contractions, evenness and vanishing at the zero increment are automatic.
It is the deterministic reason the two endpoint Hessians have the same
expectation in Lemma G.3. -/
theorem pairedTruncatedIncrement_even_exchange
    {p : ℕ} (x y base : Fin p → ℝ) (a h : ℝ)
    (F : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (heven : ∀ v z, F (-v) z = F v z) (hzero : ∀ z, F 0 z = 0) :
    F (pairedTruncatedIncrement y x h) (base + a • y) =
      F (pairedTruncatedIncrement x y h)
        (base + a • x + a • pairedTruncatedIncrement x y h) := by
  classical
  rw [pairedTruncatedIncrement_swap, heven]
  by_cases he : ‖y - x‖ ≤ h
  · have hv : pairedTruncatedIncrement x y h = y - x := if_pos he
    rw [hv]
    congr 1
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have hv : pairedTruncatedIncrement x y h = 0 := if_neg he
    rw [hv, hzero, hzero]

/-- Under the actual product law, the even contraction has equal
expectations at the two paired endpoints; genuine integrability transfers
from the first endpoint to the second. -/
theorem pairedTruncatedIncrement_integral_even_exchange
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {p : ℕ} (X : Ω → Fin p → ℝ) (base : Fin p → ℝ) (a h : ℝ)
    (F : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (heven : ∀ v z, F (-v) z = F v z) (hzero : ∀ z, F 0 z = 0)
    (hI : Integrable (fun z : Ω × Ω =>
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1)) (μ.prod μ)) :
    Integrable (fun z : Ω × Ω =>
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1 +
          a • pairedTruncatedIncrement (X z.1) (X z.2) h)) (μ.prod μ) ∧
    (∫ z : Ω × Ω,
      F (pairedTruncatedIncrement (X z.1) (X z.2) h)
        (base + a • X z.1) ∂μ.prod μ) =
      (∫ z : Ω × Ω,
        F (pairedTruncatedIncrement (X z.1) (X z.2) h)
          (base + a • X z.1 +
            a • pairedTruncatedIncrement (X z.1) (X z.2) h) ∂μ.prod μ) := by
  let f : Ω × Ω → ℝ := fun z =>
    F (pairedTruncatedIncrement (X z.1) (X z.2) h) (base + a • X z.1)
  let g : Ω × Ω → ℝ := fun z =>
    F (pairedTruncatedIncrement (X z.1) (X z.2) h)
      (base + a • X z.1 + a • pairedTruncatedIncrement (X z.1) (X z.2) h)
  have he (z : Ω × Ω) : f z.swap = g z :=
    pairedTruncatedIncrement_even_exchange (X z.1) (X z.2) base a h F heven hzero
  have hJ : Integrable g (μ.prod μ) := hI.swap.congr (ae_of_all _ he)
  refine ⟨hJ, ?_⟩
  change (∫ z, f z ∂μ.prod μ) = (∫ z, g z ∂μ.prod μ)
  calc
    _ = ∫ z, f z.swap ∂μ.prod μ := (integral_prod_swap f).symm
    _ = _ := integral_congr_ae (ae_of_all _ he)

/-- The numeric coefficient of the fourth-order remainder after inserting
the trapezoidal identity into the Slepian derivative. This algebraic fact
is separate from the analytic Slepian formula. -/
theorem paired_fourth_remainder_coefficient (s : ℝ) (hs : 0 < s) :
    (1 / (2 * Real.sqrt s)) * (1 / 2 : ℝ) *
      (-(s * Real.sqrt s) / 2) = -s / 8 := by
  have hn : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  field_simp [hn]
  <;> ring

end

end RectangleCLT.Companion.SplitV4
