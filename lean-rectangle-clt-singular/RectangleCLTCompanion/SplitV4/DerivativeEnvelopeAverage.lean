import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverageBase

/-! Actual smaller-envelope expectations for the two independent-component
models in Lemma A.1. The Gaussian factor may be singular, the summands may
be nonidentically distributed, and the independent shift needs no moments. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def derivativeEnvelopeAverageConstant : ℝ := 2048

theorem derivativeEnvelopeAverageConstant_pos : 0 < derivativeEnvelopeAverageConstant := by
  norm_num [derivativeEnvelopeAverageConstant]

theorem derivative_envelope_layer_scale {L v h δ : ℝ}
    (hL : 0 ≤ L) (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h) :
    (h*Real.log 2+2*δ)*Real.sqrt (L/v) ≤ 4*h*Real.sqrt L := by
  have hv0 : 0 < v := by linarith
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hwidth : h*Real.log 2+2*δ ≤ 2*h := by
    have hhlog := mul_le_mul_of_nonneg_left hlog hh.le
    nlinarith
  have hratio : L/v ≤ 2*L := by
    apply (div_le_iff₀ hv0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hv hL]
  have hsqrt : Real.sqrt (L/v) ≤ 2*Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hL]
      nlinarith
  have hm := mul_le_mul hwidth hsqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2*h)
  nlinarith

/-- First assertion of A.1 for an actual independent bounded-sum component.
The bound is on face projections, rather than the full ambient norm. -/
theorem integral_logisticEnvelope_bounded_component
    {Ω : Type*} [MeasurableSpace Ω] {m r n : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin r) ℝ)
    (ξ : Fin n → Ω → Vector r) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hcenter : ∀ i, (∫ ω, ξ i ω ∂μ) = 0) {δ v h : ℝ} (hδ : 0 ≤ δ)
    (hv : 1/2 ≤ v) (hh : 0 < h) (hδh : 4*δ ≤ h)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ 2*δ)
    (hvariance : ∀ α, variance (fun ω => dotProduct (U α) (sumVector ξ ω)) μ = v)
    (R : Ω → Vector r) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector m) :
    (∫ ω, logisticNullWeight U a h (sumVector ξ ω+R ω)*
      (1-logisticNullWeight U a h (sumVector ξ ω+R ω)) ∂μ) ≤
        derivativeEnvelopeAverageConstant*h*Real.sqrt (dimensionLog m) := by
  have hsum : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hm : Measurable (fun ω => sumVector ξ ω+R ω) := hsum.add hR
  have hL : 0 ≤ dimensionLog m := zero_le_one.trans
    (log_exp_mul_nat_ge_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)))
  have hscale := derivative_envelope_layer_scale hL hv hh hδh
  have hb := integral_logisticEnvelope_le_of_layer_bound μ _ hm U a hh (M := 1024*h*Real.sqrt (dimensionLog m))
    (fun b => by
      have hp := bounded_face_intrinsic_concentration μ U ξ hξ hind hξi hcenter
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ) (by linarith : 0 < v)
        hbound hvariance R hR hRind b
        (mul_nonneg hh.le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
      have hcut : min 1 (min
          (((h*Real.log 2+2*δ)/v)*∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ)
          ((h*Real.log 2+2*δ)*Real.sqrt (dimensionLog m/v))) ≤
          (h*Real.log 2+2*δ)*Real.sqrt (dimensionLog m/v) :=
        (min_le_right _ _).trans (min_le_right _ _)
      exact hp.trans ((mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 256)).trans (by nlinarith)))
  unfold derivativeEnvelopeAverageConstant
  nlinarith

/-- First assertion of A.1 for an actual independent Gaussian component.
No lower eigenvalue or positive pair-gap hypothesis occurs. -/
theorem integral_logisticEnvelope_gaussian_component
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V R : Ω → Vector r)
    (hV : Measurable V) (hR : Measurable R) (hind : IndepFun V R μ)
    (U : Matrix (Fin m) (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (hLaw : μ.map V = gaussianLaw A) {v h : ℝ} (hv : 1/2 ≤ v) (hh : 0 < h)
    (hvariance : ∀ α, dotProduct (U α) ((A*A.transpose).mulVec (U α)) = v)
    (a : Vector m) :
    (∫ ω, logisticNullWeight U a h (V ω+R ω)*(1-logisticNullWeight U a h (V ω+R ω)) ∂μ) ≤
        derivativeEnvelopeAverageConstant*h*Real.sqrt (dimensionLog m) := by
  have hL : 0 ≤ dimensionLog m := zero_le_one.trans
    (log_exp_mul_nat_ge_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)))
  have hscale := derivative_envelope_layer_scale (δ := 0) hL hv hh (by simpa using hh.le)
  simp only [mul_zero, add_zero] at hscale
  have hb := integral_logisticEnvelope_le_of_layer_bound μ _ (hV.add hR) U a hh (M := 1024*h*Real.sqrt (dimensionLog m))
    (fun b => by
      have hp := gaussianIntrinsicConcentration_independent_shift_logarithmic μ V R hV hR hind U A hLaw b
        (by linarith : 0 < v) (mul_nonneg hh.le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) hvariance
      have hcut := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ)
        ((h*Real.log 2)*Real.sqrt (dimensionLog m/v))) (by norm_num : (0 : ℝ) ≤ 4)
      have hn : 0 ≤ h*Real.sqrt (dimensionLog m) := by positivity
      exact hp.trans (hcut.trans (by nlinarith)))
  unfold derivativeEnvelopeAverageConstant
  nlinarith

end
end RectangleCLT.Companion.SplitV4
