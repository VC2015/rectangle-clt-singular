import RectangleCLTArxivV1.IntrinsicMain

/-!
# Proposition 1 with the actual intrinsic coefficient

The original bounded observations supply the direct envelope and seeded
base concentration. The contract records signed aggregate cubic terms,
actual fourth remainders, the threshold supremum and the normalized seeded
derivative. Universal constants precede every probability model.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
universe u

def intrinsicDerivativeConstant : ℝ := intrinsicComparisonConstant intrinsicBoundaryConstant

theorem intrinsicDerivativeConstant_pos : 0 < intrinsicDerivativeConstant :=
  intrinsicComparisonConstant_pos intrinsicBoundaryConstant_pos

theorem intrinsicDerivativeConstant_ge_direct : directInitializationConstant ≤ intrinsicDerivativeConstant :=
  le_add_of_nonneg_right (intrinsicSeededDerivativeConstant_pos intrinsicBoundaryConstant_pos).le

theorem intrinsicDerivativeConstant_ge_seeded :
    intrinsicSeededDerivativeConstant intrinsicBoundaryConstant ≤ intrinsicDerivativeConstant :=
  le_add_of_nonneg_left directInitializationConstant_pos.le

/-- The genuine supremum over finite rectangle thresholds in the direct
stage, bounded with its intrinsic coefficient. -/
theorem initializationDiscrepancy_intrinsic_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (h₀ : ℝ) (hh₀ : 0 < h₀) (hband : 4 * δ ≤ h₀) :
    initializationDiscrepancy μ ξ A h₀ hh₀ ≤
      directInitializationConstant * s₃ * (dimensionLog p * intrinsicBoundaryCoefficient μ ξ A) +
      directInitializationConstant * s₄ * (dimensionLog p * intrinsicBoundaryCoefficient μ ξ A) / h₀ := by
  unfold initializationDiscrepancy
  have hne : (range (directInitializationGap μ ξ A h₀ hh₀)).Nonempty :=
    ⟨directInitializationGap μ ξ A h₀ hh₀ (0, 0), ⟨(0, 0), rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨⟨lo, hi⟩, rfl⟩
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  exact direct_initialization_intrinsic_of_envelope μ ξ h hmom hunit A hA
    (FaceSmoother.closedBox lo hi h₀ hh₀) rfl hband
    (zero_le_one.trans (one_le_intrinsicBoundaryCoefficient μ ξ A hp))
    (fun v hv0 hv1 => integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA
      (FaceSmoother.closedBox lo hi h₀ hh₀) rfl hband hv0 hv1)

/-- Literal Proposition 1: complete signed cubic terms, actual integral
remainders, the threshold supremum, and the normalized path derivative. -/
def IntrinsicDerivativePropositionContract (A₀ C : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ) [NeZero p] (ξ : Fin n → Ω → Vector p) (δ s₃ s₄ : ℝ),
    BoundedIndependentHypotheses μ ξ δ → RelativeMomentBounds μ ξ s₃ s₄ →
    (∀ j, covariance μ (sumVector ξ) j j = 1) →
    ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose = covariance μ (sumVector ξ) →
    let κ := intrinsicBoundaryCoefficient μ ξ A
    ∀ s : FaceSmoother p, s.faces = Finset.univ → A₀*δ ≤ s.bandwidth →
    (∀ v ∈ Ioo (0 : ℝ) 1,
      |directSlepianCubicTerm s μ ξ A v| ≤ C*s₃*κ/s.bandwidth^2 ∧
      |directSlepianFourthRemainder s μ ξ A v| ≤ C*s₄*κ/s.bandwidth^3) ∧
    (dimensionLog p*s.bandwidth^2 < 1/4 →
      initializationDiscrepancy μ ξ A s.bandwidth s.bandwidth_pos ≤
        C*s₃*(dimensionLog p * κ)+C*s₄*(dimensionLog p * κ)/s.bandwidth ∧
      let ε := dimensionLog p*s.bandwidth^2
      let hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
      let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (normalizedSeededExpectation s μ ξ A ε)
          (-(t/(3*(1+ε)^(3/2 : ℝ)))*normalizedSeededCubicTerm s μ ξ A ε t+
            normalizedSeededFourthRemainder s μ ξ A ε hε t) t ∧
        |t/(3*(1+ε)^(3/2 : ℝ))*normalizedSeededCubicTerm s μ ξ A ε t| ≤
          C*s₃*(dimensionLog p * κ)*t/(t+ε) ∧
        |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
          C*s₄*(dimensionLog p * κ)/(s.bandwidth*(t+ε)))

theorem intrinsic_derivative_proposition :
    IntrinsicDerivativePropositionContract relativeDerivativeBandwidth intrinsicDerivativeConstant := by
  intro Ω _ μ _ p n _ ξ δ s₃ s₄ h hrel hunit A hA
  dsimp only
  intro s hfaces hband
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hLp : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hL : 0 ≤ dimensionLog p := hLp.le
  have hs₃ := hrel.s₃_nonneg
  have hs₄ := hrel.s₄_nonneg
  have hwidth := s.bandwidth_pos.le
  let κ := intrinsicBoundaryCoefficient μ ξ A
  have hsqrt : 0 ≤ κ := zero_le_one.trans (one_le_intrinsicBoundaryCoefficient μ ξ A hp)
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hCinit := intrinsicDerivativeConstant_ge_direct
  have hCseed := intrinsicDerivativeConstant_ge_seeded
  have hC₃ : directInitializationCubicConstant ≤ intrinsicDerivativeConstant :=
    (le_add_of_nonneg_right directInitializationRemainderConstant_pos.le).trans hCinit
  have hC₄ : directInitializationRemainderConstant ≤ intrinsicDerivativeConstant :=
    (le_add_of_nonneg_left directInitializationCubicConstant_pos.le).trans hCinit
  constructor
  · intro v hv
    constructor
    · apply (abs_directSlepianCubicTerm_intrinsic_of_envelope μ ξ h hrel hunit A hA s hfaces hb.1 hv.1.le hv.2.le
        (integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA s hfaces hb.1 hv.1.le hv.2.le)).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₃ hs₃) hsqrt) (sq_nonneg _)
    · apply (abs_directSlepianFourthRemainder_intrinsic_of_envelope μ ξ h hrel hunit A hA s hfaces hb.1 hv.1.le hv.2.le
        (integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA s hfaces hb.1 hv.1.le hv.2.le)).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₄ hs₄) hsqrt) (pow_nonneg hwidth _)
  · intro _
    constructor
    · apply (initializationDiscrepancy_intrinsic_le μ ξ h hrel hunit A hA s.bandwidth s.bandwidth_pos hb.1).trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCinit hs₃) (mul_nonneg hL hsqrt)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCinit hs₄) (mul_nonneg hL hsqrt)) hwidth
    · dsimp only
      intro t ht
      let ε := dimensionLog p*s.bandwidth^2
      have hε : 0 ≤ ε := mul_nonneg hL (sq_nonneg _)
      have htime : 0 ≤ t+ε := add_nonneg ht.1.le hε
      have hd := hasDerivAt_normalizedSeededExpectation s μ ξ h hrel A hA hε ht
      have hc := intrinsic_seeded_derivative_bounds μ ξ h hrel hp hunit A hA s hb.2
        intrinsicBoundaryConstant_pos (zero_lt_one.trans_le (one_le_intrinsicBoundaryCoefficient μ ξ A hp)) ht
        (intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0 hε ht.1.le ht.2.le)
      dsimp only at hc
      rw [seededNormalization_cube_eq_rpow hε] at hd hc
      refine ⟨hd, ?_, ?_⟩
      · apply hc.1.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCseed hs₃) (mul_nonneg hL hsqrt)) ht.1.le) htime
      · apply hc.2.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCseed hs₄) (mul_nonneg hL hsqrt))
          (mul_nonneg hwidth htime)

/-- Constants are existentially chosen before every model and budget. -/
theorem proposition_1_intrinsic_derivatives :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, 0 < C ∧ IntrinsicDerivativePropositionContract A₀ C :=
  ⟨relativeDerivativeBandwidth, relativeDerivativeBandwidth_pos,
    intrinsicDerivativeConstant, intrinsicDerivativeConstant_pos, intrinsic_derivative_proposition⟩

end
end RectangleCLTArxivV1
