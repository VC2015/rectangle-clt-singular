import RectangleCLTCompanion.SplitV4.DirectInitialization
import RectangleCLTCompanion.SplitV4.SeededPropositionOne
import RectangleCLTCompanion.SplitV4.RelativePathJoin

/-! Whole Proposition 1, with its two universal constants fixed before
all dimensions, probability models, moment budgets and thresholds. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

universe u

def relativeDerivativeBandwidth : ℝ := max 4 seededRestorationBandwidth

def relativeDerivativeConstant : ℝ := directInitializationConstant+seededDerivativeConstant

theorem relativeDerivativeBandwidth_ge_four : 4 ≤ relativeDerivativeBandwidth := le_max_left _ _

theorem relativeDerivativeBandwidth_pos : 0 < relativeDerivativeBandwidth :=
  lt_of_lt_of_le (by norm_num) relativeDerivativeBandwidth_ge_four

theorem relativeDerivativeBandwidth_ge_one : 1 ≤ relativeDerivativeBandwidth :=
  (by norm_num : (1:ℝ) ≤ 4).trans relativeDerivativeBandwidth_ge_four

theorem relativeDerivativeConstant_pos : 0 < relativeDerivativeConstant :=
  add_pos directInitializationConstant_pos seededDerivativeConstant_pos

theorem relativeDerivativeConstant_ge_direct : directInitializationConstant ≤ relativeDerivativeConstant :=
  le_add_of_nonneg_right seededDerivativeConstant_pos.le

theorem relativeDerivativeConstant_ge_seeded : seededDerivativeConstant ≤ relativeDerivativeConstant :=
  le_add_of_nonneg_left directInitializationConstant_pos.le

theorem relative_derivative_bandwidth_conditions {δ h : ℝ} (hδ : 0 ≤ δ)
    (hh : relativeDerivativeBandwidth*δ ≤ h) : 4*δ ≤ h ∧ seededRestorationBandwidth*δ ≤ h :=
  ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) hδ).trans hh,
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ).trans hh⟩

/-- The actual complete smooth comparison bound used in Theorem 1. -/
theorem relative_smooth_comparison_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ s₃ s₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ)
    (hband : relativeDerivativeBandwidth*δ ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      relativeDerivativeConstant*(dimensionLog p*Real.sqrt (dimensionLog p))*
        (s₃+s₄/s.bandwidth*(1+Real.log (1+1/(dimensionLog p*s.bandwidth^2)))) := by
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0 < ε := mul_pos hL (sq_pos_of_pos s.bandwidth_pos)
  have hlog : 0 ≤ Real.log (1+1/ε) := Real.log_nonneg (by
    have hh : 0 ≤ 1/ε := div_nonneg zero_le_one hε.le
    linarith)
  have hi := direct_initialization_bound μ ξ h hrel hunit A hA s hfaces hb.1
  rw [rpow_three_halves_eq_mul_sqrt hL] at hi
  have hs := seeded_time_comparison_bound μ ξ h hrel hp hunit A hA s hb.2
  have ht := smoother_gap_le_actual_two_stage_gaps s μ ξ h.measurable A hε.le
  have hh := ht.trans (add_le_add hi hs)
  change _ ≤ directInitializationConstant*s₃*(dimensionLog p*Real.sqrt (dimensionLog p))+
    directInitializationConstant*s₄*(dimensionLog p*Real.sqrt (dimensionLog p))/s.bandwidth+
    seededDerivativeConstant*(dimensionLog p*Real.sqrt (dimensionLog p))*
      (s₃+s₄/s.bandwidth*Real.log (1+1/ε)) at hh
  apply hh.trans
  have hB : 0 ≤ s₄/s.bandwidth := div_nonneg hrel.s₄_nonneg s.bandwidth_pos.le
  have hextra₁ := mul_nonneg seededDerivativeConstant_pos.le hB
  have hextra₂ := mul_nonneg directInitializationConstant_pos.le (mul_nonneg hB hlog)
  have hLS : 0 ≤ dimensionLog p*Real.sqrt (dimensionLog p) := mul_nonneg hL.le (Real.sqrt_nonneg _)
  have hnum : directInitializationConstant*s₃+directInitializationConstant*(s₄/s.bandwidth)+
      seededDerivativeConstant*(s₃+s₄/s.bandwidth*Real.log (1+1/ε)) ≤
      relativeDerivativeConstant*(s₃+s₄/s.bandwidth*(1+Real.log (1+1/ε))) := by
    unfold relativeDerivativeConstant
    nlinarith
  convert mul_le_mul_of_nonneg_left hnum hLS using 1 <;> dsimp only [ε] <;> ring

/-- Literal Proposition 1: complete signed cubic terms, actual integral
remainders, the threshold supremum, and the normalized path derivative. -/
def RelativeDerivativePropositionContract (A₀ C : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ) [NeZero p] (ξ : Fin n → Ω → Vector p) (δ s₃ s₄ : ℝ),
    BoundedIndependentHypotheses μ ξ δ → RelativeMomentBounds μ ξ s₃ s₄ →
    (∀ j, covariance μ (sumVector ξ) j j = 1) →
    ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose = covariance μ (sumVector ξ) →
    ∀ s : FaceSmoother p, s.faces = Finset.univ → A₀*δ ≤ s.bandwidth →
    (∀ v ∈ Ioo (0 : ℝ) 1,
      |directSlepianCubicTerm s μ ξ A v| ≤ C*s₃*Real.sqrt (dimensionLog p)/s.bandwidth^2 ∧
      |directSlepianFourthRemainder s μ ξ A v| ≤ C*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3) ∧
    (dimensionLog p*s.bandwidth^2 < 1/4 →
      initializationDiscrepancy μ ξ A s.bandwidth s.bandwidth_pos ≤
        C*s₃*(dimensionLog p)^(3/2 : ℝ)+C*s₄*(dimensionLog p)^(3/2 : ℝ)/s.bandwidth ∧
      let ε := dimensionLog p*s.bandwidth^2
      let hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
      let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (normalizedSeededExpectation s μ ξ A ε)
          (-(t/(3*(1+ε)^(3/2 : ℝ)))*normalizedSeededCubicTerm s μ ξ A ε t+
            normalizedSeededFourthRemainder s μ ξ A ε hε t) t ∧
        |t/(3*(1+ε)^(3/2 : ℝ))*normalizedSeededCubicTerm s μ ξ A ε t| ≤
          C*s₃*(dimensionLog p)^(3/2 : ℝ)*t/(t+ε) ∧
        |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
          C*s₄*(dimensionLog p)^(3/2 : ℝ)/(s.bandwidth*(t+ε)))

theorem relative_derivative_proposition :
    RelativeDerivativePropositionContract relativeDerivativeBandwidth relativeDerivativeConstant := by
  intro Ω _ μ _ p n _ ξ δ s₃ s₄ h hrel hunit A hA s hfaces hband
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hLp : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hL : 0 ≤ dimensionLog p := hLp.le
  have hs₃ := hrel.s₃_nonneg
  have hs₄ := hrel.s₄_nonneg
  have hwidth := s.bandwidth_pos.le
  have hsqrt := Real.sqrt_nonneg (dimensionLog p)
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hCinit := relativeDerivativeConstant_ge_direct
  have hCseed := relativeDerivativeConstant_ge_seeded
  have hC₃ : directInitializationCubicConstant ≤ relativeDerivativeConstant :=
    (le_add_of_nonneg_right directInitializationRemainderConstant_pos.le).trans hCinit
  have hC₄ : directInitializationRemainderConstant ≤ relativeDerivativeConstant :=
    (le_add_of_nonneg_left directInitializationCubicConstant_pos.le).trans hCinit
  constructor
  · intro v hv
    constructor
    · apply (abs_directSlepianCubicTerm_le μ ξ h hrel hunit A hA s hfaces hb.1 hv.1.le hv.2.le).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₃ hs₃) hsqrt) (sq_nonneg _)
    · apply (abs_directSlepianFourthRemainder_le μ ξ h hrel hunit A hA s hfaces hb.1 hv.1.le hv.2.le).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₄ hs₄) hsqrt) (pow_nonneg hwidth _)
  · intro _
    constructor
    · apply (initializationDiscrepancy_le μ ξ h hrel hunit A hA s.bandwidth s.bandwidth_pos hb.1).trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCinit hs₃) (Real.rpow_nonneg hL _)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCinit hs₄) (Real.rpow_nonneg hL _)) hwidth
    · dsimp only
      intro t ht
      let ε := dimensionLog p*s.bandwidth^2
      have hε : 0 ≤ ε := mul_nonneg hL (sq_nonneg _)
      have htime : 0 ≤ t+ε := add_nonneg ht.1.le hε
      have hd := hasDerivAt_normalizedSeededExpectation s μ ξ h hrel A hA hε ht
      have hc := seeded_derivative_bounds μ ξ h hrel hp hunit A hA s hb.2 ht
      dsimp only at hc
      rw [seededNormalization_cube_eq_rpow hε] at hd hc
      rw [← rpow_three_halves_eq_mul_sqrt hLp] at hc
      refine ⟨hd, ?_, ?_⟩
      · apply hc.1.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCseed hs₃) (Real.rpow_nonneg hL _)) ht.1.le) htime
      · apply hc.2.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCseed hs₄) (Real.rpow_nonneg hL _))
          (mul_nonneg hwidth htime)

/-- Constants are existentially chosen before every model and budget. -/
theorem proposition_relative_derivatives :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, 0 < C ∧ RelativeDerivativePropositionContract A₀ C :=
  ⟨relativeDerivativeBandwidth, relativeDerivativeBandwidth_pos,
    relativeDerivativeConstant, relativeDerivativeConstant_pos, relative_derivative_proposition⟩

end
end RectangleCLT.Companion.SplitV4
