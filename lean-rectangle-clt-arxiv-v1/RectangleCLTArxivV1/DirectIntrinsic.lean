import RectangleCLTArxivV1.IntrinsicInputs
import RectangleCLTCompanion.SplitV4.DirectInitialization

/-!
# Direct initialization retaining the intrinsic coefficient

The only analytic input of these intermediate estimates is the explicitly
stated integral of the actual smaller logistic envelope on the actual
Slepian path. The signed cubic tensor and all three restored fourth-copy
patterns are the original ones. A completed comparison must derive the
envelope input from actual bounded/Gaussian concentration.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false

theorem abs_directSlepianCubicTerm_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (_hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (_hfaces : s.faces = Finset.univ) (_hband : 4*δ ≤ s.bandwidth)
    {v κ : ℝ} (_hv0 : 0 ≤ v) (_hv1 : v ≤ 1)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |directSlepianCubicTerm s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*κ/s.bandwidth^2 := by
  have hc := (integrable_relativeCubicContraction_and_integral_bound μ (μ.prod (gaussianLaw A)) ξ s hmom hunit
    (directSlepianPoint ξ v) (measurable_directSlepianPoint ξ h.measurable v)).2
  have hcoef : 0 ≤ 13*s₃/s.bandwidth^3 :=
    div_nonneg (mul_nonneg (by norm_num) hmom.s₃_nonneg) (pow_nonneg s.bandwidth_pos.le _)
  have he := mul_le_mul_of_nonneg_left
    henv0 hcoef
  unfold directSlepianCubicTerm
  simp_rw [canonicalSignedCubicContraction_smoother_eq_relative s h hmom]
  apply hc.trans (he.trans_eq ?_)
  unfold directInitializationCubicConstant
  field_simp [s.bandwidth_pos.ne']
  ring
set_option maxHeartbeats 1000000 in
theorem directSlepian_fourth_copy_data_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (_hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (_hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r κ : ℝ} (hv0 : 0 ≤ v) (_hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Fin 4 → Bool)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    (∀ i, Integrable (directSlepianFourthCopyTensor s ξ v r b i)
      (((gaussianLaw A).prod μ).prod (μ.prod μ))) ∧
    (∑ i, ∫ z : (Vector p × Ω) × (Ω × Ω), ‖directSlepianFourthCopyTensor s ξ v r b i z‖
      ∂((gaussianLaw A).prod μ).prod (μ.prod μ)) ≤
        directInitializationFourthConstant*s₄*κ/s.bandwidth^3 := by
  let a := Real.sqrt (1-v)
  let ν := (gaussianLaw A).prod μ
  let X : Vector p × Ω → Vector p := fun z => directSlepianPoint ξ v z.swap
  let V : Fin n → (Vector p × Ω) × (Ω × Ω) → Vector p := fun i z =>
    (a*r) • ξ i z.2.2-a • ξ i z.1.2
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha1 : a ≤ 1 := by dsimp [a]; apply Real.sqrt_le_iff.mpr; constructor <;> linarith
  have har : 0 ≤ a*r := mul_nonneg ha hr0
  have har1 : a*r ≤ 1 := (mul_le_mul_of_nonneg_left hr1 ha).trans (by simpa using ha1)
  have hX : Measurable X := (measurable_directSlepianPoint ξ h.measurable v).comp measurable_swap
  have hV (i : Fin n) : Measurable (V i) :=
    (measurable_const.smul ((h.measurable i).comp (measurable_snd.comp measurable_snd))).sub
      (measurable_const.smul ((h.measurable i).comp (measurable_snd.comp measurable_fst)))
  have hVb (i : Fin n) : ∀ᵐ z ∂ν.prod (μ.prod μ), ‖V i z‖ ≤ s.bandwidth := by
    have hfresh : ∀ᵐ z : (Vector p × Ω) × (Ω × Ω) ∂ν.prod (μ.prod μ), ‖ξ i z.2.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    have horig : ∀ᵐ z : (Vector p × Ω) × (Ω × Ω) ∂ν.prod (μ.prod μ), ‖ξ i z.1.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    filter_upwards [hfresh, horig] with z hf ho
    calc
      _ ≤ ‖(a*r) • ξ i z.2.2‖+‖a • ξ i z.1.2‖ := norm_sub_le _ _
      _ = (a*r)*‖ξ i z.2.2‖+a*‖ξ i z.1.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg har, abs_of_nonneg ha]
      _ ≤ (a*r)*δ+a*δ := add_le_add (mul_le_mul_of_nonneg_left hf har) (mul_le_mul_of_nonneg_left ho ha)
      _ ≤ 2*δ := by nlinarith [mul_le_mul_of_nonneg_right har1 h.delta_nonneg,
        mul_le_mul_of_nonneg_right ha1 h.delta_nonneg]
      _ ≤ _ := by linarith [h.delta_nonneg]
  have hpoint (i : Fin n) (z : (Vector p × Ω) × (Ω × Ω)) :
      directSlepianFourthPoint ξ v r i z = X z.1+V i z := by
    dsimp only [directSlepianFourthPoint, X, directSlepianPoint, V, a, Prod.swap]
    rw [sumVector_eq_leaveOneOut_add ξ i z.1.2, smul_add]
    abel
  have htuple (i : Fin n) (z : Ω × Ω) :
      (![directCopyVector ξ i (b 0) z, directCopyVector ξ i (b 1) z,
        directCopyVector ξ i (b 2) z, directCopyVector ξ i (b 3) z] : Fin 4 → Vector p) =
        (fun a => directCopyVector ξ i (b a) z) := by
    funext a
    fin_cases a <;> rfl
  have he (i : Fin n) (z : (Vector p × Ω) × (Ω × Ω)) :
      directSlepianFourthCopyTensor s ξ v r b i z = iteratedFDeriv ℝ 4 s.F (X z.1+V i z)
        (fun a => directCopyVector ξ i (b a) z.2) := by
    unfold directSlepianFourthCopyTensor canonicalFourthTensor
    rw [hpoint, htuple]
  have hd := sum_integral_norm_fourth_shift_copies_common_base_le ν μ ξ hmom hunit s X hX V hV hVb b
  have henv : (∫ z : Vector p × Ω, s.F (X z)*(1-s.F (X z)) ∂ν) ≤
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*κ := by
    have hs := integral_prod_swap (μ := μ) (ν := gaussianLaw A)
      (fun z : Ω × Vector p => s.F (directSlepianPoint ξ v z)*(1-s.F (directSlepianPoint ξ v z)))
    change (∫ z : Vector p × Ω, s.F (X z)*(1-s.F (X z)) ∂ν) = _ at hs
    rw [hs]
    exact henv0
  have hC : 0 ≤ fourthDerivativeEnvelopeConstant*s₄/s.bandwidth^4 := by
    exact div_nonneg (mul_nonneg (by unfold fourthDerivativeEnvelopeConstant; positivity) hmom.s₄_nonneg)
      (pow_nonneg s.bandwidth_pos.le _)
  refine ⟨?_, ?_⟩
  · intro i
    exact (hd.1 i).congr (ae_of_all _ (fun z => (he i z).symm))
  · simp_rw [he]
    apply hd.2.trans ((mul_le_mul_of_nonneg_left henv hC).trans_eq ?_)
    unfold directInitializationFourthConstant
    field_simp [s.bandwidth_pos.ne']
    ring

theorem abs_directSlepianCopyFourthIntegrand_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r κ : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Fin 4 → Bool)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |directSlepianCopyFourthIntegrand s μ ξ A v r b| ≤
      directInitializationFourthConstant*s₄*κ/s.bandwidth^3 := by
  have hd := directSlepian_fourth_copy_data_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 b henv0
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)).trans hd.2
theorem abs_directSlepianFourthPathIntegrand_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r κ : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0 1
      (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r| ≤
      directInitializationRemainderConstant*s₄*κ/s.bandwidth^3 := by
  let M := directInitializationFourthConstant*s₄*κ/s.bandwidth^3
  have hcopy (b : Fin 4 → Bool) : |directSlepianCopyFourthIntegrand s μ ξ A v r b| ≤ M :=
    abs_directSlepianCopyFourthIntegrand_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 b henv0
  have hk := direct_slepian_scalar_kernel_bounds hv0 hv1 hr0 hr1
  have hmul (a J : ℝ) (ha : |a| ≤ 1) (hJ : |J| ≤ M) : |a*J| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul ha hJ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [directSlepianFourthPathIntegrand_eq_copy_patterns μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1]
  have hA' := hmul _ _ hk.1 (hcopy directSlepianFourthFlagsA)
  have hB' := hmul _ _ hk.2.1 (hcopy directSlepianFourthFlagsB)
  have hC' := hmul _ _ hk.2.2 (hcopy directSlepianFourthFlagsC)
  have htri := (abs_add_le
    (seededFourthKernel (Real.sqrt (1-v)) (-(1/2 : ℝ)) r*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsA +
      ((1-v)/2*(1-r))*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsB)
    (((1-v)/4)*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsC)).trans
      (add_le_add_right (abs_add_le _ _) _)
  calc
    _ ≤ 3*M := by linarith
    _ = _ := by dsimp [M, directInitializationRemainderConstant]; ring

theorem abs_directSlepianFourthRemainder_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v κ : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |directSlepianFourthRemainder s μ ξ A v| ≤
      directInitializationRemainderConstant*s₄*κ/s.bandwidth^3 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun r => genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0 1
      (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r)
    (C := directInitializationRemainderConstant*s₄*κ/s.bandwidth^3)
    (fun r hr => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      simpa only [Real.norm_eq_abs] using
        abs_directSlepianFourthPathIntegrand_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr.1.le hr.2 henv0)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, directSlepianFourthRemainder] using hh
theorem abs_directSlepianDerivative_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v κ : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (henv0 : (∫ z : Ω × Vector p,
      s.F (directSlepianPoint ξ v z) * (1 - s.F (directSlepianPoint ξ v z))
      ∂μ.prod (gaussianLaw A)) ≤ derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v+
      directSlepianFourthRemainder s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*κ/s.bandwidth^2+
      directInitializationRemainderConstant*s₄*κ/s.bandwidth^3 := by
  have hc := abs_directSlepianCubicTerm_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 henv0
  have hr := abs_directSlepianFourthRemainder_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 henv0
  have ha : |-Real.sqrt (1-v)/4| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
    have hh : Real.sqrt (1-v) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
    linarith
  have hm : |-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*κ/s.bandwidth^2 := by
    rw [abs_mul]
    exact (mul_le_mul ha hc (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (abs_add_le _ _).trans (add_le_add hm hr)

theorem directSlepian_increment_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {u κ : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (henv0 : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) *
        (1 - s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
        derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |directSlepianExpectation s μ ξ A u-(∫ ω, s.F (sumVector ξ ω) ∂μ)| ≤
      (directInitializationCubicConstant*s₃*κ/s.bandwidth^2+
        directInitializationRemainderConstant*s₄*κ/s.bandwidth^3)*u := by
  have hh := direct_time_increment_le hu0
    (continuous_directSlepianExpectation s μ ξ h.measurable A).continuousOn
    (fun v hv => hasDerivAt_directSlepianExpectation s μ ξ h A hA hv.1 (hv.2.trans_le hu1))
    (fun v hv => abs_directSlepianDerivative_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband
      hv.1.le (hv.2.le.trans hu1) (henv0 v hv.1.le (hv.2.le.trans hu1)))
  simpa only [directSlepianExpectation_zero] using hh

/-- The initialization estimate holds before the small-seed restriction
used for choosing the final bandwidth. -/
theorem direct_initialization_intrinsic_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth) {κ : ℝ} (hκ : 0 ≤ κ)
    (henv0 : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) *
        (1 - s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
        derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-directSlepianExpectation s μ ξ A
      (seededInitializationTime (dimensionLog p*s.bandwidth^2))| ≤
      directInitializationConstant*s₃*(dimensionLog p * κ)+
        directInitializationConstant*s₄*(dimensionLog p * κ)/s.bandwidth := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hLp : 0 < dimensionLog p := lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp)
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0 ≤ ε := mul_nonneg hL (sq_nonneg _)
  have hu := seededInitializationTime_mem_Icc hε
  have hue : seededInitializationTime ε ≤ ε := by
    unfold seededInitializationTime
    apply (div_le_iff₀ (by linarith : 0 < 1+ε)).mpr
    nlinarith [sq_nonneg ε]
  have hB : 0 ≤ directInitializationCubicConstant*s₃*κ/s.bandwidth^2+
      directInitializationRemainderConstant*s₄*κ/s.bandwidth^3 := by
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg directInitializationCubicConstant_pos.le hmom.s₃_nonneg)
        hκ) (sq_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg directInitializationRemainderConstant_pos.le hmom.s₄_nonneg)
        hκ) (pow_nonneg s.bandwidth_pos.le _))
  have hh := (directSlepian_increment_intrinsic_of_envelope μ ξ h hmom hunit A hA s hfaces hband hu.1 hu.2 henv0).trans
    (mul_le_mul_of_nonneg_left hue hB)
  rw [abs_sub_comm] at hh
  apply hh.trans
  have he :
      (directInitializationCubicConstant*s₃*κ/s.bandwidth^2+
        directInitializationRemainderConstant*s₄*κ/s.bandwidth^3)*ε =
      directInitializationCubicConstant*(s₃*(dimensionLog p*κ))+
        directInitializationRemainderConstant*(s₄*(dimensionLog p*κ)/s.bandwidth) := by
    dsimp [ε]
    field_simp [s.bandwidth_pos.ne']
    ring
  rw [he]
  have hT₃ : 0 ≤ s₃*(dimensionLog p*κ) :=
    mul_nonneg hmom.s₃_nonneg (mul_nonneg hL hκ)
  have hT₄ : 0 ≤ s₄*(dimensionLog p*κ)/s.bandwidth :=
    div_nonneg (mul_nonneg hmom.s₄_nonneg (mul_nonneg hL hκ)) s.bandwidth_pos.le
  have hcross₃ := mul_nonneg directInitializationRemainderConstant_pos.le hT₃
  have hcross₄ := mul_nonneg directInitializationCubicConstant_pos.le hT₄
  unfold directInitializationConstant
  calc
    _ ≤ (directInitializationCubicConstant+directInitializationRemainderConstant)*
        (s₃*(dimensionLog p*κ))+
      (directInitializationCubicConstant+directInitializationRemainderConstant)*
        (s₄*(dimensionLog p*κ)/s.bandwidth) := by nlinarith
    _ = _ := by ring

end
end RectangleCLTArxivV1
