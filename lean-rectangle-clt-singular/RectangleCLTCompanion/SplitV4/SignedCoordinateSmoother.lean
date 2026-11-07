import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeModels
import RectangleCLTCompanion.SplitV4.DirectRelativeDerivatives

/-! Exact full-coordinate rectangle smoothers as arbitrary-face logistic
smooth functions. The face seminorm is precisely the original maximum norm. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def signedCoordinateFaceEquiv (p : ℕ) : Fin (2*p) ≃ Face p :=
  Fintype.equivOfCardEq (by simp [Face, mul_comm])

def signedCoordinateRows (p : ℕ) : Matrix (Fin (2*p)) (Fin p) ℝ := fun α =>
  if (signedCoordinateFaceEquiv p α).2 then
    FaceSmoother.coordinateDirection (signedCoordinateFaceEquiv p α).1
  else -FaceSmoother.coordinateDirection (signedCoordinateFaceEquiv p α).1

def signedCoordinateThresholds {p : ℕ} (s : FaceSmoother p) : Vector (2*p) :=
  fun α => s.offsets (signedCoordinateFaceEquiv p α)

theorem signedCoordinateRows_projection {p : ℕ} (α : Fin (2*p)) (x : Vector p) :
    faceDot (signedCoordinateRows p α) x = FaceSmoother.normalDot (signedCoordinateFaceEquiv p α) x := by
  cases hb : (signedCoordinateFaceEquiv p α).2 <;>
    simp [signedCoordinateRows, hb, faceDot, FaceSmoother.coordinateDirection, FaceSmoother.normalDot]

theorem signedCoordinateRows_faceProjectionNorm {p : ℕ} (x : Vector p) :
    faceProjectionNorm (signedCoordinateRows p) x = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro α
    rw [Real.norm_eq_abs]
    change |faceDot (signedCoordinateRows p α) x| ≤ ‖x‖
    rw [signedCoordinateRows_projection]
    exact FaceSmoother.abs_normalDot_le_of_norm_le _ (le_refl ‖x‖)
  · apply (pi_norm_le_iff_of_nonneg (show 0 ≤ faceProjectionNorm (signedCoordinateRows p) x from norm_nonneg _)).mpr
    intro j
    let α := (signedCoordinateFaceEquiv p).symm (j, true)
    have he : (signedCoordinateRows p).mulVec x α = x j := by
      change faceDot (signedCoordinateRows p α) x = x j
      rw [signedCoordinateRows_projection]
      simp only [α, Equiv.apply_symm_apply, FaceSmoother.normalDot, if_true]
    have hn := norm_le_pi_norm ((signedCoordinateRows p).mulVec x) α
    rw [he] at hn
    exact hn

theorem logistic_signedCoordinateRows_eq_F {p : ℕ} (s : FaceSmoother p)
    (hfaces : s.faces = Finset.univ) (x : Vector p) :
    logisticNullWeight (signedCoordinateRows p) (signedCoordinateThresholds s) s.bandwidth x = s.F x := by
  have hsum : (∑ α : Fin (2*p), Real.exp
      ((faceDot (signedCoordinateRows p α) x-signedCoordinateThresholds s α)/s.bandwidth)) = (s.weights x).T := by
    calc
      _ = ∑ α : Fin (2*p), Real.exp (s.faceScore (signedCoordinateFaceEquiv p α) x/s.bandwidth) := by
        apply Finset.sum_congr rfl
        intro α _
        rw [signedCoordinateRows_projection]
        rfl
      _ = ∑ f : Face p, Real.exp (s.faceScore f x/s.bandwidth) :=
        (signedCoordinateFaceEquiv p).sum_comp (fun f : Face p => Real.exp (s.faceScore f x/s.bandwidth))
      _ = _ := by simp only [FaceWeights.T, FaceSmoother.weights, hfaces, Finset.mem_univ, if_true]
  change 1/(1+_) = 1/(1+_)
  rw [hsum]

theorem integral_smallerEnvelope_full_smoother_component
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p) (hfaces : s.faces = Finset.univ)
    (X : Ω → Vector p) {δ v : ℝ}
    (hmodel : DerivativeEnvelopeComponent μ (signedCoordinateRows p) X δ v)
    (hδ : 0 ≤ δ) (hv : 1/2 ≤ v) (hband : 4*δ ≤ s.bandwidth) :
    (∫ ω, s.F (X ω)*(1-s.F (X ω)) ∂μ) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p) := by
  have he := integral_logisticEnvelope_component_signed_faces μ (signedCoordinateRows p) X
    hmodel hδ hv s.bandwidth_pos hband (signedCoordinateThresholds s)
  simpa only [logistic_signedCoordinateRows_eq_F s hfaces] using he

theorem integral_relativeCubicContraction_full_smoother_component
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) {s₃ s₄ δ v : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (X : Γ → Vector p)
    (hmodel : DerivativeEnvelopeComponent ν (signedCoordinateRows p) X δ v)
    (hδ : 0 ≤ δ) (hv : 1/2 ≤ v) (hband : 4*δ ≤ s.bandwidth) :
    |∫ ω, relativeCubicContraction s μ ξ (X ω) ∂ν| ≤
      (13*derivativeEnvelopeSignedAverageConstant)*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2 := by
  have hc := (integrable_relativeCubicContraction_and_integral_bound μ ν ξ s h hunit X hmodel.measurable).2
  have hcoef : 0 ≤ 13*s₃/s.bandwidth^3 :=
    div_nonneg (mul_nonneg (by norm_num) h.s₃_nonneg) (pow_nonneg s.bandwidth_pos.le _)
  have he := mul_le_mul_of_nonneg_left
    (integral_smallerEnvelope_full_smoother_component ν s hfaces X hmodel hδ hv hband) hcoef
  apply hc.trans (he.trans_eq ?_)
  field_simp [s.bandwidth_pos.ne']
  ring

end
end RectangleCLT.Companion.SplitV4
