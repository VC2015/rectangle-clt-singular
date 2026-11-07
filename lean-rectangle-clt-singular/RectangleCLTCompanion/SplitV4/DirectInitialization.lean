import RectangleCLTCompanion.SplitV4.DirectSlepianRemainder
import RectangleCLTCompanion.SplitV4.NormalizedSeededEndpoints
import RectangleCLTCompanion.SplitV4.DirectTimeIntegration
import RectangleCLTCompanion.Rates

/-! Initialization by the genuine Slepian derivative. The cubic term is
aggregated with its sign before its absolute value is taken. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def directInitializationConstant : ℝ :=
  directInitializationCubicConstant+directInitializationRemainderConstant

theorem directInitializationCubicConstant_pos : 0 < directInitializationCubicConstant := by
  norm_num [directInitializationCubicConstant, derivativeEnvelopeSignedAverageConstant,
    derivativeEnvelopeAverageConstant]

theorem directInitializationRemainderConstant_pos : 0 < directInitializationRemainderConstant := by
  unfold directInitializationRemainderConstant directInitializationFourthConstant
    fourthDerivativeEnvelopeConstant derivativeEnvelopeSignedAverageConstant derivativeEnvelopeAverageConstant
  positivity

theorem directInitializationConstant_pos : 0 < directInitializationConstant :=
  add_pos directInitializationCubicConstant_pos directInitializationRemainderConstant_pos

theorem abs_directSlepianDerivative_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v+
      directSlepianFourthRemainder s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2+
      directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
  have hc := abs_directSlepianCubicTerm_le μ ξ h hmom hunit A hA s hfaces hband hv0 hv1
  have hr := abs_directSlepianFourthRemainder_le μ ξ h hmom hunit A hA s hfaces hband hv0 hv1
  have ha : |-Real.sqrt (1-v)/4| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
    have hh : Real.sqrt (1-v) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
    linarith
  have hm : |-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v| ≤
      directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2 := by
    rw [abs_mul]
    exact (mul_le_mul ha hc (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (abs_add_le _ _).trans (add_le_add hm hr)

theorem directSlepian_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |directSlepianExpectation s μ ξ A u-(∫ ω, s.F (sumVector ξ ω) ∂μ)| ≤
      (directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2+
        directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3)*u := by
  have hh := direct_time_increment_le hu0
    (continuous_directSlepianExpectation s μ ξ h.measurable A).continuousOn
    (fun v hv => hasDerivAt_directSlepianExpectation s μ ξ h A hA hv.1 (hv.2.trans_le hu1))
    (fun v hv => abs_directSlepianDerivative_le μ ξ h hmom hunit A hA s hfaces hband
      hv.1.le (hv.2.le.trans hu1))
  simpa only [directSlepianExpectation_zero] using hh

/-- The initialization estimate holds before the small-seed restriction
used for choosing the final bandwidth. -/
theorem direct_initialization_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-directSlepianExpectation s μ ξ A
      (seededInitializationTime (dimensionLog p*s.bandwidth^2))| ≤
      directInitializationConstant*s₃*(dimensionLog p)^(3/2 : ℝ)+
        directInitializationConstant*s₄*(dimensionLog p)^(3/2 : ℝ)/s.bandwidth := by
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
  have hB : 0 ≤ directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2+
      directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg directInitializationCubicConstant_pos.le hmom.s₃_nonneg)
        (Real.sqrt_nonneg _)) (sq_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg directInitializationRemainderConstant_pos.le hmom.s₄_nonneg)
        (Real.sqrt_nonneg _)) (pow_nonneg s.bandwidth_pos.le _))
  have hh := (directSlepian_increment_le μ ξ h hmom hunit A hA s hfaces hband hu.1 hu.2).trans
    (mul_le_mul_of_nonneg_left hue hB)
  rw [abs_sub_comm] at hh
  apply hh.trans
  have he :
      (directInitializationCubicConstant*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2+
        directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3)*ε =
      directInitializationCubicConstant*(s₃*(dimensionLog p*Real.sqrt (dimensionLog p)))+
        directInitializationRemainderConstant*(s₄*(dimensionLog p*Real.sqrt (dimensionLog p))/s.bandwidth) := by
    dsimp [ε]
    field_simp [s.bandwidth_pos.ne']
    ring
  rw [he, rpow_three_halves_eq_mul_sqrt hLp]
  have hT₃ : 0 ≤ s₃*(dimensionLog p*Real.sqrt (dimensionLog p)) :=
    mul_nonneg hmom.s₃_nonneg (mul_nonneg hL (Real.sqrt_nonneg _))
  have hT₄ : 0 ≤ s₄*(dimensionLog p*Real.sqrt (dimensionLog p))/s.bandwidth :=
    div_nonneg (mul_nonneg hmom.s₄_nonneg (mul_nonneg hL (Real.sqrt_nonneg _))) s.bandwidth_pos.le
  have hcross₃ := mul_nonneg directInitializationRemainderConstant_pos.le hT₃
  have hcross₄ := mul_nonneg directInitializationCubicConstant_pos.le hT₄
  unfold directInitializationConstant
  calc
    _ ≤ (directInitializationCubicConstant+directInitializationRemainderConstant)*
        (s₃*(dimensionLog p*Real.sqrt (dimensionLog p)))+
      (directInitializationCubicConstant+directInitializationRemainderConstant)*
        (s₄*(dimensionLog p*Real.sqrt (dimensionLog p))/s.bandwidth) := by nlinarith
    _ = _ := by ring

def directInitializationGap {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : ℝ) (hh : 0 < h) (bounds : Vector p × Vector p) : ℝ :=
  let s := FaceSmoother.closedBox bounds.1 bounds.2 h hh
  |(∫ ω, s.F (sumVector ξ ω) ∂μ)-directSlepianExpectation s μ ξ A
    (seededInitializationTime (dimensionLog p*h^2))|

/-- The actual supremum over all finite lower and upper face thresholds. -/
def initializationDiscrepancy {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : ℝ) (hh : 0 < h) : ℝ := sSup (range (directInitializationGap μ ξ A h hh))

theorem initializationDiscrepancy_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (h₀ : ℝ) (hh₀ : 0 < h₀) (hband : 4*δ ≤ h₀) :
    initializationDiscrepancy μ ξ A h₀ hh₀ ≤
      directInitializationConstant*s₃*(dimensionLog p)^(3/2 : ℝ)+
        directInitializationConstant*s₄*(dimensionLog p)^(3/2 : ℝ)/h₀ := by
  unfold initializationDiscrepancy
  have hne : (range (directInitializationGap μ ξ A h₀ hh₀)).Nonempty :=
    ⟨directInitializationGap μ ξ A h₀ hh₀ (0,0), ⟨(0,0), rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨⟨lo,hi⟩,rfl⟩
  exact direct_initialization_bound μ ξ h hmom hunit A hA
    (FaceSmoother.closedBox lo hi h₀ hh₀) rfl hband

end
end RectangleCLT.Companion.SplitV4
