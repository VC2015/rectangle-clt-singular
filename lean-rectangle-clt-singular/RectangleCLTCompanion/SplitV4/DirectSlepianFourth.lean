import RectangleCLTCompanion.SplitV4.DirectSlepianCubic

/-! Actual restored fourth tensors on the Slepian initialization path.
The three copy patterns share the genuine full evaluation point before
the independent copies are averaged. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem maskObservationSum_all_true_deleted {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (ω : Ω) :
    maskObservationSum ξ (Function.update (fun _ => true) i false) ω = leaveOneOut ξ i ω := by
  classical
  unfold maskObservationSum leaveOneOut
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => if Function.update (fun _ : Fin n => true) i false j then ξ j ω else 0) (Finset.mem_univ i)]
  simp only [Function.update_self, Bool.false_eq_true, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rfl

def directSlepianFourthPoint {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (v r : ℝ) (i : Fin n)
    (z : (Vector p × Ω) × (Ω × Ω)) : Vector p :=
  Real.sqrt v • z.1.1+Real.sqrt (1-v) • leaveOneOut ξ i z.1.2+
    (Real.sqrt (1-v)*r) • ξ i z.2.2

def directSlepianFourthCopyTensor {Ω : Type*} {p n : ℕ}
    (s : FaceSmoother p) (ξ : Fin n → Ω → Vector p) (v r : ℝ) (b : Fin 4 → Bool)
    (i : Fin n) (z : (Vector p × Ω) × (Ω × Ω)) : ℝ :=
  canonicalFourthTensor s.F (directSlepianFourthPoint ξ v r i z)
    (directCopyVector ξ i (b 0) z.2) (directCopyVector ξ i (b 1) z.2)
    (directCopyVector ξ i (b 2) z.2) (directCopyVector ξ i (b 3) z.2)

def directSlepianCopyFourthIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (v r : ℝ) (b : Fin 4 → Bool) : ℝ :=
  ∑ i, ∫ z : (Vector p × Ω) × (Ω × Ω), directSlepianFourthCopyTensor s ξ v r b i z
    ∂((gaussianLaw A).prod μ).prod (μ.prod μ)

def directInitializationFourthConstant : ℝ :=
  fourthDerivativeEnvelopeConstant*derivativeEnvelopeSignedAverageConstant

set_option maxHeartbeats 1000000 in
theorem directSlepian_fourth_copy_data
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Fin 4 → Bool) :
    (∀ i, Integrable (directSlepianFourthCopyTensor s ξ v r b i)
      (((gaussianLaw A).prod μ).prod (μ.prod μ))) ∧
    (∑ i, ∫ z : (Vector p × Ω) × (Ω × Ω), ‖directSlepianFourthCopyTensor s ξ v r b i z‖
      ∂((gaussianLaw A).prod μ).prod (μ.prod μ)) ≤
        directInitializationFourthConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
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
      derivativeEnvelopeSignedAverageConstant*s.bandwidth*Real.sqrt (dimensionLog p) := by
    have hs := integral_prod_swap (μ := μ) (ν := gaussianLaw A)
      (fun z : Ω × Vector p => s.F (directSlepianPoint ξ v z)*(1-s.F (directSlepianPoint ξ v z)))
    change (∫ z : Vector p × Ω, s.F (X z)*(1-s.F (X z)) ∂ν) = _ at hs
    rw [hs]
    exact integral_smallerEnvelope_directSlepian μ ξ h hunit A hA s hfaces hband hv0 hv1
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

theorem abs_directSlepianCopyFourthIntegrand_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Fin 4 → Bool) :
    |directSlepianCopyFourthIntegrand s μ ξ A v r b| ≤
      directInitializationFourthConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
  have hd := directSlepian_fourth_copy_data μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 b
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)).trans hd.2

end
end RectangleCLT.Companion.SplitV4
