import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage

/-! The two concrete independent-component models of Lemma A.1. These
constructors contain actual laws, independence and genuine moments; they
do not contain a boundary or derivative estimate as an assumption. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

inductive DerivativeEnvelopeComponent
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ}
    (μ : Measure Ω) (U : Matrix (Fin m) (Fin r) ℝ) (X : Ω → Vector r) (δ v : ℝ) : Prop
  | bounded {n : ℕ} (ξ : Fin n → Ω → Vector r)
      (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
      (hξi : ∀ i, Integrable (ξ i) μ) (hcenter : ∀ i, (∫ ω, ξ i ω ∂μ) = 0)
      (hbound : ∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ 2*δ)
      (hvariance : ∀ α, variance (fun ω => dotProduct (U α) (sumVector ξ ω)) μ = v)
      (R : Ω → Vector r) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
      (hX : X = fun ω => sumVector ξ ω+R ω) : DerivativeEnvelopeComponent μ U X δ v
  | gaussian (V R : Ω → Vector r) (hV : Measurable V) (hR : Measurable R)
      (hind : IndepFun V R μ) (A : Matrix (Fin r) (Fin r) ℝ)
      (hLaw : μ.map V = gaussianLaw A)
      (hvariance : ∀ α, dotProduct (U α) ((A*A.transpose).mulVec (U α)) = v)
      (hX : X = fun ω => V ω+R ω) : DerivativeEnvelopeComponent μ U X δ v

theorem DerivativeEnvelopeComponent.measurable
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ}
    {μ : Measure Ω} {U : Matrix (Fin m) (Fin r) ℝ} {X : Ω → Vector r} {δ v : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) : Measurable X := by
  cases hmodel with
  | bounded ξ hξ _ _ _ _ _ R hR _ hX =>
    rw [hX]
    exact (Finset.measurable_sum _ (fun i _ => hξ i)).add hR
  | gaussian V R hV hR _ _ _ _ hX =>
    rw [hX]
    exact hV.add hR

theorem integral_logisticEnvelope_component
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (a : Vector m) :
    (∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ) ≤
      derivativeEnvelopeAverageConstant*h*Real.sqrt (dimensionLog m) := by
  cases hmodel with
  | bounded ξ hξ hind hξi hcenter hbound hvariance R hR hRind hX =>
    rw [hX]
    exact integral_logisticEnvelope_bounded_component μ U ξ hξ hind hξi hcenter hδ hv hh hδh
      hbound hvariance R hR hRind a
  | gaussian V R hV hR hind A hLaw hvariance hX =>
    rw [hX]
    exact integral_logisticEnvelope_gaussian_component μ V R hV hR hind U A hLaw hv hh hvariance a

def derivativeEnvelopeSignedAverageConstant : ℝ := 2*derivativeEnvelopeAverageConstant

/-- The manuscript uses `L=log(e p)` for `2p` signed faces. -/
theorem integral_logisticEnvelope_component_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin (2*p)) (Fin r) ℝ)
    (X : Ω → Vector r) {δ v h : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ U X δ v) (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) (a : Vector (2*p)) :
    (∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ) ≤
      derivativeEnvelopeSignedAverageConstant*h*Real.sqrt (dimensionLog p) := by
  have hb := integral_logisticEnvelope_component μ U X hmodel hδ hv hh hδh a
  have hs := sqrt_dimensionLog_double_div_le (p := p) (v := 1) zero_lt_one
  simp only [div_one] at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ derivativeEnvelopeAverageConstant*h by unfold derivativeEnvelopeAverageConstant; positivity)
  unfold derivativeEnvelopeSignedAverageConstant
  exact hb.trans (by nlinarith)

end
end RectangleCLT.Companion.SplitV4
