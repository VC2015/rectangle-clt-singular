import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAllOrders
import RectangleCLTArxivV1.EnvelopeThresholdIntegration

/-!
# Intrinsic averaging of the actual logistic derivatives

Frozen main source: A.1, lines 3158–3178 and proof 3180–3239. Unlike the
archived logarithmic specialization, the boundary coefficient here is an
arbitrary `κ`. The input is exactly the layer-probability hypothesis of A.1;
no expectation or derivative envelope estimate is assumed. Derivative order
is explicitly positive, as in the published statement and the archive's
qualification. All suprema below are genuine measurable translated suprema.
-/

namespace RectangleCLTArxivV1

set_option autoImplicit false

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The explicit boundary-layer premise of A.1. -/
def IntrinsicBoundaryBound {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ}
    (μ : Measure Ω) (X : Ω → Vector r) (U : Matrix (Fin m) (Fin r) ℝ)
    (δ κ C₀ : ℝ) : Prop :=
  ∀ (a : Vector m) (s : ℝ), 0 < s →
    μ.real {ω | X ω ∈ gaussianPolyhedronLayer U a s} ≤ C₀ * κ * (s + δ)

/-- First assertion of A.1 with the intrinsic boundary coefficient retained. -/
theorem integral_logisticEnvelope_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {δ κ C₀ h : ℝ}
    (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hh : 0 < h) (hδh : 4 * δ ≤ h)
    (hboundary : IntrinsicBoundaryBound μ X U δ κ C₀) :
    Integrable (fun ω => logisticNullWeight U a h (X ω) *
      (1 - logisticNullWeight U a h (X ω))) μ ∧
    (∫ ω, logisticNullWeight U a h (X ω) * (1 - logisticNullWeight U a h (X ω)) ∂μ) ≤
      4 * C₀ * h * κ := by
  refine ⟨integrable_logisticEnvelope μ X hX U a hh, ?_⟩
  have hp := integral_logisticEnvelope_le_of_layer_bound_printed μ X hX U a hh
    (fun b => hboundary b h hh)
  have hw : h + δ ≤ 2*h := by linarith only [hδh,hh]
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hC₀ hκ)
  have hm' := mul_le_mul_of_nonneg_left hm
    (div_nonneg (Real.exp_nonneg 1) (by norm_num : (0:ℝ)≤2))
  have he := mul_le_mul_of_nonneg_right exp_one_le_four
    (mul_nonneg (mul_nonneg hC₀ hh.le) hκ)
  exact hp.trans (hm'.trans (by nlinarith only [he]))

/-- A constant depending only on the boundary constant and the positive derivative order. -/
noncomputable def intrinsicDerivativeConstant (C₀ : ℝ) (q : ℕ) : ℝ :=
  4 * C₀ * (allOrderLogisticEnvelopeConstant q + 1)

/-- Averaging the proved local logistic derivative bound yields A.1 at every
positive order, with `κ` and the genuine translated supremum preserved. -/
theorem averaged_translated_derivative_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {m r q : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {δ κ C₀ h ρ : ℝ}
    (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hh : 0 < h) (hδh : 4 * δ ≤ h)
    (hρ : 0 ≤ ρ) (hρh : ρ ≤ h) (hq : 1 ≤ q)
    (hboundary : IntrinsicBoundaryBound μ X U δ κ C₀) (z : Fin q → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum
      (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      intrinsicDerivativeConstant C₀ q / h ^ (q - 1) * κ *
        (∏ i, faceProjectionNorm U (z i)) := by
  let K := allOrderLogisticEnvelopeConstant q + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [allOrderLogisticEnvelopeConstant_nonneg q]
  have hr := integrable_integral_translated_logistic_derivativeSup_of_local_bound
    μ X hX U a hh hρ z K
    (fun x v hv => logistic_allOrder_local_envelope U a hh hρh hq x v hv z)
  refine ⟨hr.1, hr.2.trans ?_⟩
  have hn : 0 ≤ K / h ^ q * (∏ i, faceProjectionNorm U (z i)) := by
    exact mul_nonneg (div_nonneg hK (pow_nonneg hh.le q))
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_left
    (integral_logisticEnvelope_intrinsic μ X hX U a hC₀ hκ hh hδh hboundary).2 hn
  apply hm.trans_eq
  have heq : h ^ q = h ^ (q - 1) * h := by rw [← pow_succ, Nat.sub_add_cancel hq]
  change (K / h ^ q * (∏ i, faceProjectionNorm U (z i))) * (4 * C₀ * h * κ) = _
  rw [heq]
  unfold intrinsicDerivativeConstant
  dsimp only [K]
  field_simp [hh.ne']
  ring

/-- The natural-power denominator in the checked derivative estimate is the
paper's `h^(1-q)` for exactly the asserted positive integer orders. -/
theorem intrinsicDerivative_inverse_power_eq_rpow {h : ℝ} (hh : 0 < h)
    {q : ℕ} (hq : 1 ≤ q) : 1 / h ^ (q - 1) = h ^ (1 - (q : ℝ)) :=
  derivative_envelope_inverse_power_eq_rpow hh hq

end RectangleCLTArxivV1
