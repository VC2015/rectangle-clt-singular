import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeModels
import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeLocal34

/-! Genuine expected translated suprema for the actual canonical third
and fourth derivatives. These are complete specializations of A.1; the
all-positive-order assertion is recorded separately. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem integrable_integral_translated_logistic_derivativeSup_of_local_bound
    {Ω : Type*} [MeasurableSpace Ω] {m r q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h ρ : ℝ} (hh : 0 < h) (hρ : 0 ≤ ρ)
    (z : Fin q → Vector r) (K : ℝ)
    (hlocal : ∀ x v, faceProjectionNorm U v ≤ ρ →
      ‖iteratedFDeriv ℝ q (logisticNullWeight U a h) (x+v) z‖ ≤
        (K*logisticNullWeight U a h x*(1-logisticNullWeight U a h x)/h^q)*
          (∏ i, faceProjectionNorm U (z i))) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      (K/h^q*(∏ i, faceProjectionNorm U (z i)))*
        ∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ := by
  let B : Vector r → ℝ := fun x => (K/h^q*(∏ i, faceProjectionNorm U (z i)))*
    (logisticNullWeight U a h x*(1-logisticNullWeight U a h x))
  have hbound (x v : Vector r) (hv : faceProjectionNorm U v ≤ ρ) :
      ‖iteratedFDeriv ℝ q (logisticNullWeight U a h) (x+v) z‖ ≤ B x := by
    exact (hlocal x v hv).trans_eq (by dsimp only [B]; ring)
  have hiB : Integrable (fun ω => B (X ω)) μ := (integrable_logisticEnvelope μ X hX U a hh).const_mul _
  have hc : Continuous (iteratedFDeriv ℝ q (logisticNullWeight U a h)) :=
    (contDiff_logisticNullWeight U a hh).continuous_iteratedFDeriv (by simp)
  have hi := integrable_translatedFaceDerivativeSupremum μ X hX _ U hρ z hc B hiB hbound
  refine ⟨hi, ?_⟩
  have hm := integral_mono_ae hi hiB (ae_of_all _ (fun ω =>
    translatedFaceDerivativeSupremum_le _ U hρ z B hbound (X ω)))
  exact hm.trans_eq (integral_const_mul _ _)

theorem averaged_translated_third_derivative_component
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector m) (z : Fin 3 → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      (derivativeEnvelopeAverageConstant*thirdDerivativeEnvelopeConstant)*Real.sqrt (dimensionLog m)/h^2*
        (∏ i, faceProjectionNorm U (z i)) := by
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z thirdDerivativeEnvelopeConstant
    (fun x v hv => logistic_iteratedFDeriv_three_shift_envelope U a hh x (hv.trans hρh) z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ thirdDerivativeEnvelopeConstant/h^3*(∏ i, faceProjectionNorm U (z i)) := by
    unfold thirdDerivativeEnvelopeConstant faceProjectionNorm
    positivity
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  field_simp [hh.ne']
  ring

theorem averaged_translated_fourth_derivative_component
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector m) (z : Fin 4 → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      (derivativeEnvelopeAverageConstant*fourthDerivativeEnvelopeConstant)*Real.sqrt (dimensionLog m)/h^3*
        (∏ i, faceProjectionNorm U (z i)) := by
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z fourthDerivativeEnvelopeConstant
    (fun x v hv => logistic_iteratedFDeriv_four_shift_envelope U a hh x (hv.trans hρh) z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ fourthDerivativeEnvelopeConstant/h^4*(∏ i, faceProjectionNorm U (z i)) := by
    unfold fourthDerivativeEnvelopeConstant faceProjectionNorm
    positivity
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  field_simp [hh.ne']
  ring

theorem averaged_translated_third_derivative_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin (2*p)) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector (2*p)) (z : Fin 3 → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      (derivativeEnvelopeSignedAverageConstant*thirdDerivativeEnvelopeConstant)*Real.sqrt (dimensionLog p)/h^2*
        (∏ i, faceProjectionNorm U (z i)) := by
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z thirdDerivativeEnvelopeConstant
    (fun x v hv => logistic_iteratedFDeriv_three_shift_envelope U a hh x (hv.trans hρh) z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ thirdDerivativeEnvelopeConstant/h^3*(∏ i, faceProjectionNorm U (z i)) := by
    unfold thirdDerivativeEnvelopeConstant faceProjectionNorm
    positivity
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component_signed_faces μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  field_simp [hh.ne']
  ring

theorem averaged_translated_fourth_derivative_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin (2*p)) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h ρ : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (hρ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (a : Vector (2*p)) (z : Fin 4 → Vector r) :
    Integrable (fun ω => translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω)) μ ∧
    (∫ ω, translatedFaceDerivativeSupremum (logisticNullWeight U a h) U ρ z (X ω) ∂μ) ≤
      (derivativeEnvelopeSignedAverageConstant*fourthDerivativeEnvelopeConstant)*Real.sqrt (dimensionLog p)/h^3*
        (∏ i, faceProjectionNorm U (z i)) := by
  have hres := integrable_integral_translated_logistic_derivativeSup_of_local_bound μ X hmodel.measurable
    U a hh hρ z fourthDerivativeEnvelopeConstant
    (fun x v hv => logistic_iteratedFDeriv_four_shift_envelope U a hh x (hv.trans hρh) z)
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hn : 0 ≤ fourthDerivativeEnvelopeConstant/h^4*(∏ i, faceProjectionNorm U (z i)) := by
    unfold fourthDerivativeEnvelopeConstant faceProjectionNorm
    positivity
  have hm := mul_le_mul_of_nonneg_left (integral_logisticEnvelope_component_signed_faces μ U X hmodel hδ hv hh hδh a) hn
  apply hm.trans_eq
  field_simp [hh.ne']
  ring

end
end RectangleCLT.Companion.SplitV4
