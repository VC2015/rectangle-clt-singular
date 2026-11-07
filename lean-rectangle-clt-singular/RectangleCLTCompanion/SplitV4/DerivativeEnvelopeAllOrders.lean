import RectangleCLTCompanion.SplitV4.LogisticDerivativeFaceEnvelope
import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage34

/-! Whole Lemma A.1. Its constants are chosen before dimensions, laws,
face normals, thresholds, directions and translations. Every positive
canonical derivative order is included, and the true translated supremum
has a proved genuine Bochner integral. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def averagedDerivativeEnvelopeConstant (q : ℕ) : ℝ :=
  derivativeEnvelopeAverageConstant*(allOrderLogisticEnvelopeConstant q+1)

def averagedSignedDerivativeEnvelopeConstant (q : ℕ) : ℝ :=
  derivativeEnvelopeSignedAverageConstant*(allOrderLogisticEnvelopeConstant q+1)

theorem averagedDerivativeEnvelopeConstant_pos (q : ℕ) : 0 < averagedDerivativeEnvelopeConstant q := by
  unfold averagedDerivativeEnvelopeConstant
  exact mul_pos derivativeEnvelopeAverageConstant_pos (by have := allOrderLogisticEnvelopeConstant_nonneg q; linarith)

theorem averagedSignedDerivativeEnvelopeConstant_pos (q : ℕ) : 0 < averagedSignedDerivativeEnvelopeConstant q := by
  unfold averagedSignedDerivativeEnvelopeConstant derivativeEnvelopeSignedAverageConstant
  exact mul_pos (mul_pos (by norm_num) derivativeEnvelopeAverageConstant_pos)
    (by have := allOrderLogisticEnvelopeConstant_nonneg q; linarith)

theorem logistic_allOrder_local_envelope {m r q : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h ρ : ℝ} (hh : 0 < h)
    (hρh : ρ ≤ h) (hq : 1 ≤ q) (x v : Vector r) (hv : faceProjectionNorm U v ≤ ρ)
    (z : Fin q → Vector r) :
    ‖iteratedFDeriv ℝ q (logisticNullWeight U a h) (x+v) z‖ ≤
      ((allOrderLogisticEnvelopeConstant q+1)*logisticNullWeight U a h x*
        (1-logisticNullWeight U a h x)/h^q)*(∏ i, faceProjectionNorm U (z i)) := by
  have hb := abs_iteratedFDeriv_logisticNullWeight_shift_le U a hh hq x z (hv.trans hρh)
  have hF : 0 ≤ logisticNullWeight U a h x := by
    rw [← upperFaceSmoother_F U a h hh]
    exact ((upperFaceSmoother a h hh).F_pos _).le
  have hθ : 0 ≤ 1-logisticNullWeight U a h x := by
    rw [← upperFaceSmoother_F U a h hh]
    exact sub_nonneg.mpr ((upperFaceSmoother a h hh).F_le_one _)
  have hc : allOrderLogisticEnvelopeConstant q/h^q ≤ (allOrderLogisticEnvelopeConstant q+1)/h^q :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (pow_nonneg hh.le q)
  have hP : 0 ≤ ∏ i : Fin q, faceProjectionNorm U (z i) :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc hF) hθ) hP
  rw [Real.norm_eq_abs]
  exact hb.trans (hm.trans_eq (by ring))

theorem averaged_translated_derivative_component
    {Ω : Type*} [MeasurableSpace Ω] {m r q : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector m) (hq : 1 ≤ q) (z : Fin q → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      averagedDerivativeEnvelopeConstant q/h^(q-1)*Real.sqrt (dimensionLog m)*
        (∏ i, faceProjectionNorm U (z i)) := by
  let K := allOrderLogisticEnvelopeConstant q+1
  have hK : 0 ≤ K := by dsimp [K]; have := allOrderLogisticEnvelopeConstant_nonneg q; linarith
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z K (fun x v hv => logistic_allOrder_local_envelope U a hh hρh hq x v hv z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ K/h^q*(∏ i, faceProjectionNorm U (z i)) :=
    mul_nonneg (div_nonneg hK (pow_nonneg hh.le q)) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  have hp : h^q = h^(q-1)*h := by rw [← pow_succ, Nat.sub_add_cancel hq]
  unfold averagedDerivativeEnvelopeConstant
  change (K/h^q*(∏ i, faceProjectionNorm U (z i)))*
    (derivativeEnvelopeAverageConstant*h*Real.sqrt (dimensionLog m)) = _
  rw [hp]
  field_simp [hh.ne']
  ring

theorem averaged_translated_derivative_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r q : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin (2*p)) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector (2*p)) (hq : 1 ≤ q) (z : Fin q → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      averagedSignedDerivativeEnvelopeConstant q/h^(q-1)*Real.sqrt (dimensionLog p)*
        (∏ i, faceProjectionNorm U (z i)) := by
  let K := allOrderLogisticEnvelopeConstant q+1
  have hK : 0 ≤ K := by dsimp [K]; have := allOrderLogisticEnvelopeConstant_nonneg q; linarith
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z K (fun x v hv => logistic_allOrder_local_envelope U a hh hρh hq x v hv z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ K/h^q*(∏ i, faceProjectionNorm U (z i)) :=
    mul_nonneg (div_nonneg hK (pow_nonneg hh.le q)) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component_signed_faces μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  have hp : h^q = h^(q-1)*h := by rw [← pow_succ, Nat.sub_add_cancel hq]
  unfold averagedSignedDerivativeEnvelopeConstant
  change (K/h^q*(∏ i, faceProjectionNorm U (z i)))*
    (derivativeEnvelopeSignedAverageConstant*h*Real.sqrt (dimensionLog p)) = _
  rw [hp]
  field_simp [hh.ne']
  ring

/-- Positive-order reciprocal-power notation is exactly the paper's `h^(1-q)`. -/
theorem derivative_envelope_inverse_power_eq_rpow {h : ℝ} (hh : 0 < h) {q : ℕ} (hq : 1 ≤ q) :
    1/h^(q-1) = h^(1-(q : ℝ)) := by
  have he : (1-(q : ℝ)) = -((q-1 : ℕ) : ℝ) := by rw [Nat.cast_sub hq]; norm_num
  rw [he, Real.rpow_neg hh.le, Real.rpow_natCast]
  simp only [one_div]

def DerivativeEnvelopeAverageContract (C : ℝ) (Cq : ℕ → ℝ) : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p r : ℕ) [NeZero p] (U : Matrix (Fin (2*p)) (Fin r) ℝ) (X : Ω → Vector r)
    (δ v h ρ : ℝ), DerivativeEnvelopeComponent μ U X δ v → 0 ≤ δ → 1/2 ≤ v →
    0 < h → 4*δ ≤ h → 0 ≤ ρ → ρ ≤ h → ∀ a : Vector (2*p),
    Integrable (fun ω => logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω))) μ ∧
    (∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ) ≤
      C*h*Real.sqrt (dimensionLog p) ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ z : Fin q → Vector r,
      Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
      (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
        Cq q/h^(q-1)*Real.sqrt (dimensionLog p)*(∏ i, faceProjectionNorm U (z i))

/-- **Whole Lemma A.1 (`appx-lem:envelope`).** Both actual component
models and every positive derivative order share constants fixed first. -/
theorem lemma_derivative_envelope :
    ∃ C : ℝ, 0 < C ∧ ∃ Cq : ℕ → ℝ, (∀ q, 0 < Cq q) ∧ DerivativeEnvelopeAverageContract C Cq := by
  refine ⟨derivativeEnvelopeSignedAverageConstant, ?_, averagedSignedDerivativeEnvelopeConstant,
    averagedSignedDerivativeEnvelopeConstant_pos, ?_⟩
  · unfold derivativeEnvelopeSignedAverageConstant derivativeEnvelopeAverageConstant
    norm_num
  · intro Ω _ μ _ p r _ U X δ v h ρ hmodel hδ hv hh hδh hρ hρh a
    refine ⟨integrable_logisticEnvelope μ X hmodel.measurable U a hh,
      integral_logisticEnvelope_component_signed_faces μ U X hmodel hδ hv hh hδh a, ?_⟩
    intro q hq z
    exact averaged_translated_derivative_signed_faces μ U X hmodel hδ hv hh hδh hρ hρh a hq z

end
end RectangleCLT.Companion.SplitV4
