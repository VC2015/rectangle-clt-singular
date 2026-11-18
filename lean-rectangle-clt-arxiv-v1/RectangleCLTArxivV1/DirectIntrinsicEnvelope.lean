import RectangleCLTArxivV1.BoundedRectangleIntrinsic
import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import RectangleCLTArxivV1.GaussianWidthOrder
import RectangleCLTArxivV1.IntrinsicInputs
import RectangleCLTCompanion.SplitV4.SlepianEnvelope

/-! Intrinsic envelope averaging on the actual direct Slepian path.
One of its two independent components has variance at least one half.
The intrinsic C.1 bounds and the existing logarithmic bound are proved
separately, then combined into the paper's actual minimum coefficient. -/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section
set_option autoImplicit false

theorem smallerEnvelope_scaled_bounded_intrinsic_maximum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 4*δ ≤ s.bandwidth)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hav : 1/2 ≤ a^2) (r : Vector p) :
    (∫ ω, s.F (a • sumVector ξ ω+r)*(1-s.F (a • sumVector ξ ω+r)) ∂μ) ≤
      512*s.bandwidth*(∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
  let η : Fin n → Ω → Vector p := fun i ω => a • ξ i ω
  have hη : BoundedIndependentHypotheses μ η (a*δ) := h.smul_of_nonneg a ha
  have hv : 0 < a^2 := by linarith only [hav]
  have hdiag : ∀ j, covariance μ (sumVector η) j j = a^2 := by
    intro j
    simpa only [η, mul_one] using h.covariance_sum_smul_diagonal a 1 hunit j
  let W : Ω → Vector p := fun ω => sumVector η ω+r
  have hW : Measurable W := hη.measurable_sum.add_const r
  let ν := μ.map W
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hW.aemeasurable
  let d := s.bandwidth*Real.log 2
  have hd : 0 < d := mul_pos s.bandwidth_pos (Real.log_pos (by norm_num))
  have hbound (t : FaceSmoother p) :
      ν.real {x | (∀ f ∈ t.faces, t.faceScore f x ≤ d) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -d)} ≤
      64*((d+a*δ)/(a^2)*(∫ ω, ‖sumVector η ω‖ ∂μ)) := by
    have hset : {x | (∀ f ∈ t.faces, t.faceScore f x ≤ d) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -d)} = t.boundaryLayer d := by
      ext x
      exact (t.mem_boundaryLayer_iff_score d x).symm
    rw [hset]
    have hh := boundedRectangleBoundary_map_intrinsic μ η hη hv hdiag t r hd
    change (μ.map W).real (t.boundaryLayer d) ≤ _
    rw [Measure.real, Measure.map_apply hW (t.measurableSet_boundaryLayer d)]
    have hE : MeasurableSet {x : Vector p | x+r ∈ t.boundaryLayer d} :=
      (t.measurableSet_boundaryLayer d).preimage (measurable_id.add_const r)
    rw [map_measureReal_apply hη.measurable_sum hE] at hh
    exact hh
  have hb := s.integral_smallerEnvelope_le_of_boundary ν hbound
  rw [integral_map hW.aemeasurable
    (s.continuous_F.mul (continuous_const.sub s.continuous_F)).aestronglyMeasurable] at hb
  have heq : sumVector η = fun ω => a • sumVector ξ ω := by
    funext ω
    exact sumVector_smul ξ a ω
  have hmean : (∫ ω, ‖sumVector η ω‖ ∂μ) = a*(∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
    simp_rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact integral_const_mul _ _
  rw [hmean] at hb
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hdle : d ≤ s.bandwidth := by
    simpa only [d, mul_one] using mul_le_mul_of_nonneg_left hlog s.bandwidth_pos.le
  have haδ : a*δ ≤ δ := by simpa using mul_le_mul_of_nonneg_right ha1 h.delta_nonneg
  have hδh : δ ≤ s.bandwidth := by linarith only [hband, h.delta_nonneg]
  have hnum : d+a*δ ≤ 2*s.bandwidth := by linarith only [hdle,haδ,hδh]
  have hquot : (d+a*δ)/(a^2) ≤ 4*s.bandwidth := by
    apply (div_le_iff₀ hv).mpr
    nlinarith only [hnum, mul_le_mul_of_nonneg_left hav s.bandwidth_pos.le]
  have hE : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have haE : a*(∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := by
    simpa using mul_le_mul_of_nonneg_right ha1 hE
  have hprod := mul_le_mul hquot haE (mul_nonneg ha hE)
    (mul_nonneg (by norm_num : (0:ℝ)≤4) s.bandwidth_pos.le)
  change (∫ ω, s.F (sumVector η ω+r)*(1-s.F (sumVector η ω+r)) ∂μ) ≤ _ at hb
  rw [heq] at hb
  exact hb.trans (by nlinarith only [hprod])

theorem smallerEnvelope_scaled_gaussian_intrinsic_maximum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hunit : ∀ j, (A*A.transpose) j j = 1)
    (s : FaceSmoother p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hav : 1/2 ≤ a^2) (r : Vector p) :
    (∫ g, s.F (a • g+r)*(1-s.F (a • g+r)) ∂gaussianLaw A) ≤
      8*s.bandwidth*gaussianMaximumMean A := by
  let B := a • A
  have hv : 0 < a^2 := by linarith only [hav]
  have hdiag (j : Fin p) : (B*B.transpose) j j = a^2 := by
    calc
      _ = a^2*(A*A.transpose) j j := by
        simp only [B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hunit j, mul_one]
  let W : Vector p → Vector p := fun x => x+r
  have hW : Measurable W := measurable_id.add_const r
  let ν := (gaussianLaw B).map W
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hW.aemeasurable
  let d := s.bandwidth*Real.log 2
  have hd : 0 < d := mul_pos s.bandwidth_pos (Real.log_pos (by norm_num))
  have hbound (t : FaceSmoother p) :
      ν.real {x | (∀ f ∈ t.faces, t.faceScore f x ≤ d) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -d)} ≤
      (2*d/(a^2))*gaussianMaximumMean B := by
    have hset : {x | (∀ f ∈ t.faces, t.faceScore f x ≤ d) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -d)} = t.boundaryLayer d := by
      ext x
      exact (t.mem_boundaryLayer_iff_score d x).symm
    rw [hset]
    change ((gaussianLaw B).map W).real (t.boundaryLayer d) ≤ _
    rw [Measure.real, Measure.map_apply hW (t.measurableSet_boundaryLayer d)]
    exact gaussianRectangleBoundary_intrinsic_fixed_shift t B r hv hd hdiag
  have hb := s.integral_smallerEnvelope_le_of_boundary ν hbound
  rw [integral_map hW.aemeasurable
    (s.continuous_F.mul (continuous_const.sub s.continuous_F)).aestronglyMeasurable] at hb
  have hm : Measurable (fun y => s.F (y+r)*(1-s.F (y+r))) :=
    (s.continuous_F.measurable.comp (measurable_id.add_const r)).mul
      (measurable_const.sub (s.continuous_F.measurable.comp (measurable_id.add_const r)))
  rw [FaceSmoother.integral_gaussianLaw_smul A a _ hm]
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hdle : d ≤ s.bandwidth := by
    simpa only [d,mul_one] using mul_le_mul_of_nonneg_left hlog s.bandwidth_pos.le
  have hquot : 2*d/(a^2) ≤ 4*s.bandwidth := by
    apply (div_le_iff₀ hv).mpr
    nlinarith only [hdle, mul_le_mul_of_nonneg_left hav s.bandwidth_pos.le]
  have hmean : gaussianMaximumMean B ≤ gaussianMaximumMean A := by
    change gaussianMaximumMean (a • A) ≤ gaussianMaximumMean A
    rw [gaussianMaximumMean_smul, abs_of_nonneg ha]
    simpa using mul_le_mul_of_nonneg_right ha1 (gaussianMaximumMean_nonneg A)
  have hp := mul_le_mul hquot hmean (gaussianMaximumMean_nonneg B)
    (mul_nonneg (by norm_num : (0:ℝ)≤4) s.bandwidth_pos.le)
  exact hb.trans (by nlinarith only [hp])

/-- Actual envelope supplier used by direct initialization. All analytic
premises have been discharged from the original bounded independent array
and its covariance factor. -/
theorem integral_smallerEnvelope_directSlepian_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z)*(1-s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*intrinsicBoundaryCoefficient μ ξ A := by
  have hi := integrable_smallerEnvelope_comp (μ.prod (gaussianLaw A)) s _
    (measurable_directSlepianPoint ξ h.measurable v)
  let M := 1+max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)
  have hE : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hM : 0 ≤ M := by dsimp [M]; linarith [le_max_left (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
  have hEM : (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤ M := by
    dsimp [M]; linarith [le_max_left (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
  have hgM : gaussianMaximumMean A ≤ M := by
    dsimp [M]; linarith [le_max_right (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
  have hmax : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z)*(1-s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant*s.bandwidth*M := by
    by_cases hvhalf : v ≤ 1/2
    · have hav : 1/2 ≤ (Real.sqrt (1-v))^2 := by rw [Real.sq_sqrt (by linarith)]; linarith
      have ha1 : Real.sqrt (1-v) ≤ 1 := by apply Real.sqrt_le_one.mpr; linarith
      have hcoef : 512*s.bandwidth*(∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
          derivativeEnvelopeSignedAverageConstant*s.bandwidth*M := by
        have hh := mul_le_mul_of_nonneg_left hEM s.bandwidth_pos.le
        unfold derivativeEnvelopeSignedAverageConstant derivativeEnvelopeAverageConstant
        nlinarith only [hh, mul_nonneg s.bandwidth_pos.le hM]
      rw [integral_prod_symm _ hi]
      have hh := integral_mono_ae hi.integral_prod_right (integrable_const
          (derivativeEnvelopeSignedAverageConstant*s.bandwidth*M))
        (ae_of_all _ (fun g => (smallerEnvelope_scaled_bounded_intrinsic_maximum μ ξ h hunit s hband
          (Real.sqrt (1-v)) (Real.sqrt_nonneg _) ha1 hav (Real.sqrt v • g)).trans hcoef))
      simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh
    · have hav : 1/2 ≤ (Real.sqrt v)^2 := by rw [Real.sq_sqrt hv0]; linarith
      have ha1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.mpr hv1
      have hdiag (j : Fin p) : (A*A.transpose) j j = 1 := by rw [hA, hunit j]
      have hcoef : 8*s.bandwidth*gaussianMaximumMean A ≤
          derivativeEnvelopeSignedAverageConstant*s.bandwidth*M := by
        have hh := mul_le_mul_of_nonneg_left hgM s.bandwidth_pos.le
        unfold derivativeEnvelopeSignedAverageConstant derivativeEnvelopeAverageConstant
        nlinarith only [hh, mul_nonneg s.bandwidth_pos.le hM]
      rw [integral_prod _ hi]
      have hh := integral_mono_ae hi.integral_prod_left (integrable_const
          (derivativeEnvelopeSignedAverageConstant*s.bandwidth*M))
        (ae_of_all _ (fun ω => by
          have hh := (smallerEnvelope_scaled_gaussian_intrinsic_maximum A hdiag s
            (Real.sqrt v) (Real.sqrt_nonneg _) ha1 hav
            (Real.sqrt (1-v) • sumVector ξ ω)).trans hcoef
          simpa only [directSlepianPoint, add_comm] using hh))
      simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh
  have hlog := integral_smallerEnvelope_directSlepian μ ξ h hunit A hA s hfaces hband hv0 hv1
  unfold intrinsicBoundaryCoefficient
  change _ ≤ derivativeEnvelopeSignedAverageConstant*s.bandwidth*min (Real.sqrt (dimensionLog p)) M
  by_cases hm : Real.sqrt (dimensionLog p) ≤ M
  · simpa only [min_eq_left hm] using hlog
  · simpa only [min_eq_right (le_of_not_ge hm)] using hmax

end
end RectangleCLTArxivV1
