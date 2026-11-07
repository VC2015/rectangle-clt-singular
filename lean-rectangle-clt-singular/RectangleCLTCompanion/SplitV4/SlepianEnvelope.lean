import RectangleCLTCompanion.SplitV4.SignedCoordinateMoments
import RectangleCLTCompanion.SplitV4.DirectFourthAveraging
import RectangleCLT.GaussianHeat

/-! Actual smaller-envelope averaging along the Slepian initialization
path. At every time, one actual independent component has variance at
least one half. Conditioning changes only the finite thresholds. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem smallerEnvelope_scaled_bounded_component
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (hav : 1/2 ≤ a^2) (r : Vector p) :
    (∫ ω, s.F (a • sumVector ξ ω+r)*(1-s.F (a • sumVector ξ ω+r)) ∂μ) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p) := by
  let η : Fin n → Ω → Vector p := fun i ω => a • ξ i ω
  have hη : BoundedIndependentHypotheses μ η (a*δ) := h.smul_of_nonneg a ha
  have hi (i : Fin n) : Integrable (η i) μ :=
    (integrable_const (a*δ)).mono' (hη.measurable i).aestronglyMeasurable (hη.bounded i)
  have hc (i : Fin n) : (∫ ω, η i ω ∂μ) = 0 := by
    ext j
    have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm (hi i)
    change (∫ ω, η i ω j ∂μ) = (∫ ω, η i ω ∂μ) j at he
    change (∫ ω, η i ω ∂μ) j = 0
    rw [← he]
    exact hη.centered i j
  have hb (i : Fin n) : ∀ᵐ ω ∂μ, faceProjectionNorm (signedCoordinateRows p) (η i ω) ≤ 2*δ := by
    filter_upwards [hη.bounded i] with ω hω
    rw [signedCoordinateRows_faceProjectionNorm]
    exact hω.trans (mul_le_mul_of_nonneg_right ha2 h.delta_nonneg)
  have hv (α : Fin (2*p)) : variance
      (fun ω => dotProduct (signedCoordinateRows p α) (sumVector η ω)) μ = a^2 := by
    rw [signedCoordinateRows_variance_sum μ η hη]
    simpa only [η, mul_one] using h.covariance_sum_smul_diagonal a 1 hunit (signedCoordinateFaceEquiv p α).1
  have hmodel : DerivativeEnvelopeComponent μ (signedCoordinateRows p)
      (fun ω => a • sumVector ξ ω+r) δ (a^2) := by
    refine .bounded η hη.measurable hη.independent hi hc hb hv (fun _ => r) measurable_const
      (indepFun_constant_right μ (sumVector η) r) ?_
    funext ω
    simp only [η, sumVector_smul]
  exact integral_smallerEnvelope_full_smoother_component μ s hfaces _ hmodel h.delta_nonneg hav hband

theorem smallerEnvelope_scaled_gaussian_component
    {p : ℕ} [NeZero p] (A : Matrix (Fin p) (Fin p) ℝ)
    (hunit : ∀ j, (A*A.transpose) j j = 1)
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ)
    (a : ℝ) (hav : 1/2 ≤ a^2) (r : Vector p) :
    (∫ g, s.F (a • g+r)*(1-s.F (a • g+r)) ∂gaussianLaw A) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p) := by
  let B := a • A
  have hdiag (j : Fin p) : (B*B.transpose) j j = a^2 := by
    calc
      _ = a^2*(A*A.transpose) j j := by
        simp only [B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hunit j, mul_one]
  have hv (α : Fin (2*p)) : dotProduct (signedCoordinateRows p α)
      ((B*B.transpose).mulVec (signedCoordinateRows p α)) = a^2 := by
    rw [signedCoordinateRows_quadratic, hdiag]
  have hmodel : DerivativeEnvelopeComponent (gaussianLaw B) (signedCoordinateRows p)
      (fun g => g+r) 0 (a^2) :=
    .gaussian id (fun _ => r) measurable_id measurable_const (indepFun_constant_right _ id r) B
      (by simp only [Measure.map_id]) hv rfl
  have hh := integral_smallerEnvelope_full_smoother_component (gaussianLaw B) s hfaces _ hmodel le_rfl hav
    (by simpa using s.bandwidth_pos.le)
  have hm : Measurable (fun y => s.F (y+r)*(1-s.F (y+r))) :=
    (s.continuous_F.measurable.comp (measurable_id.add measurable_const)).mul
      (measurable_const.sub (s.continuous_F.measurable.comp (measurable_id.add measurable_const)))
  rw [FaceSmoother.integral_gaussianLaw_smul A a _ hm]
  exact hh

def directSlepianPoint {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (v : ℝ) (z : Ω × Vector p) : Vector p :=
  Real.sqrt (1-v) • sumVector ξ z.1+Real.sqrt v • z.2

theorem measurable_directSlepianPoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (v : ℝ) :
    Measurable (directSlepianPoint ξ v) :=
  (measurable_const.smul ((Finset.measurable_sum _ (fun i _ => hξ i)).comp measurable_fst)).add
    (measurable_const.smul measurable_snd)

theorem integral_smallerEnvelope_directSlepian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z)*(1-s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p) := by
  have hi := integrable_smallerEnvelope_comp (μ.prod (gaussianLaw A)) s _
    (measurable_directSlepianPoint ξ h.measurable v)
  by_cases hvhalf : v ≤ 1/2
  · have hav : 1/2 ≤ (Real.sqrt (1-v))^2 := by rw [Real.sq_sqrt (by linarith)]; linarith
    have ha2 : Real.sqrt (1-v) ≤ 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> linarith
    rw [integral_prod_symm _ hi]
    have hm := integral_mono_ae hi.integral_prod_right (integrable_const
      (derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p)))
      (ae_of_all _ (fun g => smallerEnvelope_scaled_bounded_component μ ξ h hunit s hfaces hband
        (Real.sqrt (1-v)) (Real.sqrt_nonneg _) ha2 hav (Real.sqrt v • g)))
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hm
  · have hav : 1/2 ≤ (Real.sqrt v)^2 := by rw [Real.sq_sqrt hv0]; linarith
    have hdiag (j : Fin p) : (A*A.transpose) j j = 1 := by rw [hA, hunit j]
    rw [integral_prod _ hi]
    have hm := integral_mono_ae hi.integral_prod_left (integrable_const
      (derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p)))
      (ae_of_all _ (fun ω => by
        have hh := smallerEnvelope_scaled_gaussian_component A hdiag s hfaces (Real.sqrt v) hav
          (Real.sqrt (1-v) • sumVector ξ ω)
        simpa only [directSlepianPoint, add_comm] using hh))
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hm

end
end RectangleCLT.Companion.SplitV4
