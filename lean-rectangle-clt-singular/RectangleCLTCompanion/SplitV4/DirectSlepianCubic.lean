import RectangleCLTCompanion.SplitV4.SlepianEnvelope
import RectangleCLTCompanion.SplitV4.DirectCubicMoments
import RectangleCLTCompanion.SplitV4.GenericC4CubicTensor

/-! The direct cubic estimate in Proposition 1, at the actual Slepian
law and with the complete signed aggregate third tensor. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem genericCubicContraction_smoother_eq_relative
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (s : FaceSmoother p) (h : RelativeMomentBounds μ ξ s₃ s₄) (x : Vector p) :
    genericCubicContraction μ s.F ξ x = relativeCubicContraction s μ ξ x :=
  (relativeCubicContraction_eq_sum_integral_canonical_third s h x).symm

theorem canonicalSignedCubicContraction_smoother_eq_relative
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ s₃ s₄ : ℝ}
    (s : FaceSmoother p) (h : BoundedIndependentHypotheses μ ξ δ)
    (hmom : RelativeMomentBounds μ ξ s₃ s₄) (x : Vector p) :
    canonicalSignedCubicContraction μ s.F ξ x = relativeCubicContraction s μ ξ x := by
  rw [← genericCubicContraction_eq_signedTensor μ ξ h s.F]
  exact genericCubicContraction_smoother_eq_relative s hmom x

def directSlepianCubicTerm
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, canonicalSignedCubicContraction μ s.F ξ (directSlepianPoint ξ v z)
    ∂μ.prod (gaussianLaw A)

def directInitializationCubicConstant : ℝ := 13*derivativeEnvelopeSignedAverageConstant

theorem integrable_directSlepianCubicTerm
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (A : Matrix (Fin p) (Fin p) ℝ)
    (s : FaceSmoother p) (v : ℝ) :
    Integrable (fun z : Ω × Vector p => canonicalSignedCubicContraction μ s.F ξ
      (directSlepianPoint ξ v z)) (μ.prod (gaussianLaw A)) := by
  simpa only [canonicalSignedCubicContraction_smoother_eq_relative s h hmom] using
    (integrable_relativeCubicContraction_and_integral_bound μ (μ.prod (gaussianLaw A)) ξ s hmom hunit
      (directSlepianPoint ξ v) (measurable_directSlepianPoint ξ h.measurable v)).1

/-- The complete signed direct cubic assertion of Proposition 1. -/
theorem abs_directSlepianCubicTerm_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |directSlepianCubicTerm s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2 := by
  have hc := (integrable_relativeCubicContraction_and_integral_bound μ (μ.prod (gaussianLaw A)) ξ s hmom hunit
    (directSlepianPoint ξ v) (measurable_directSlepianPoint ξ h.measurable v)).2
  have hcoef : 0 ≤ 13*s₃/s.bandwidth^3 :=
    div_nonneg (mul_nonneg (by norm_num) hmom.s₃_nonneg) (pow_nonneg s.bandwidth_pos.le _)
  have he := mul_le_mul_of_nonneg_left
    (integral_smallerEnvelope_directSlepian μ ξ h hunit A hA s hfaces hband hv0 hv1) hcoef
  unfold directSlepianCubicTerm
  simp_rw [canonicalSignedCubicContraction_smoother_eq_relative s h hmom]
  apply hc.trans (he.trans_eq ?_)
  unfold directInitializationCubicConstant
  field_simp [s.bandwidth_pos.ne']
  ring

end
end RectangleCLT.Companion.SplitV4
