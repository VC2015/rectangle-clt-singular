import RectangleCLTArxivV1.DirectIntrinsic
import RectangleCLTArxivV1.SeededIntrinsic
import RectangleCLTArxivV1.IntrinsicOptimization
import RectangleCLTArxivV1.SmoothingIntrinsic
import RectangleCLTCompanion.SplitV4.RelativeDerivativeProposition

/-!
# Assembly of the two actual interpolation paths

This is an intermediate reduction: its concentration and smaller-envelope
premises must be supplied from the actual bounded array before any complete
CLT statement is claimed. The probability-law derivative, copy restoration,
time integration, smoothing, and scalar optimization have no additional
comparison or remainder hypotheses.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def intrinsicComparisonConstant (C₀ : ℝ) : ℝ :=
  directInitializationConstant + intrinsicSeededDerivativeConstant C₀

theorem intrinsicComparisonConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < intrinsicComparisonConstant C₀ :=
  add_pos directInitializationConstant_pos (intrinsicSeededDerivativeConstant_pos hC₀)

theorem intrinsic_smooth_comparison_of_boundary_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ s₃ s₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ)
    (hband : relativeDerivativeBandwidth*δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (henv : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) *
        (1 - s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
        derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p * s.bandwidth ^ 2) t) C₀ δ κ) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      (intrinsicComparisonConstant C₀)*(dimensionLog p*κ)*
        (s₃+s₄/s.bandwidth*(1+Real.log (1+1/(dimensionLog p*s.bandwidth^2)))) := by
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0 < ε := mul_pos hL (sq_pos_of_pos s.bandwidth_pos)
  have hlog : 0 ≤ Real.log (1+1/ε) := Real.log_nonneg (by
    have hh : 0 ≤ 1/ε := div_nonneg zero_le_one hε.le
    linarith)
  have hi := direct_initialization_intrinsic_of_envelope μ ξ h hrel hunit A hA s hfaces hb.1 hκ.le henv
  have hs := intrinsic_seeded_time_comparison_bound μ ξ h hrel hp hunit A hA s hb.2 hC₀ hκ hc
  have ht := smoother_gap_le_actual_two_stage_gaps s μ ξ h.measurable A hε.le
  have hh := ht.trans (add_le_add hi hs)
  change _ ≤ directInitializationConstant*s₃*(dimensionLog p*κ)+
    directInitializationConstant*s₄*(dimensionLog p*κ)/s.bandwidth+
    (intrinsicSeededDerivativeConstant C₀)*(dimensionLog p*κ)*
      (s₃+s₄/s.bandwidth*Real.log (1+1/ε)) at hh
  apply hh.trans
  have hB : 0 ≤ s₄/s.bandwidth := div_nonneg hrel.s₄_nonneg s.bandwidth_pos.le
  have hextra₁ := mul_nonneg (intrinsicSeededDerivativeConstant_pos hC₀).le hB
  have hextra₂ := mul_nonneg directInitializationConstant_pos.le (mul_nonneg hB hlog)
  have hLS : 0 ≤ dimensionLog p*κ := mul_nonneg hL.le hκ.le
  have hnum : directInitializationConstant*s₃+directInitializationConstant*(s₄/s.bandwidth)+
      (intrinsicSeededDerivativeConstant C₀)*(s₃+s₄/s.bandwidth*Real.log (1+1/ε)) ≤
      (intrinsicComparisonConstant C₀)*(s₃+s₄/s.bandwidth*(1+Real.log (1+1/ε))) := by
    unfold intrinsicComparisonConstant
    nlinarith
  convert mul_le_mul_of_nonneg_left hnum hLS using 1 <;> dsimp only [ε] <;> ring


/-- Conditional assembly only: each supplier is an actual layer/envelope
bound for one of the actual probability laws, and remains visible until a
separate bounded-array theorem discharges it. -/
theorem intrinsicCLT_of_uniform_boundary_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ s₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hr : IntrinsicFourthBounds μ ξ s₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hb : IntrinsicRectangleConcentration (μ.map (sumVector ξ)) C₀ δ κ)
    (hg : IntrinsicRectangleConcentration (gaussianLaw A) C₀ 0 κ)
    (henv : ∀ s : FaceSmoother p, s.faces = Finset.univ → 4 * δ ≤ s.bandwidth →
      ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) *
        (1 - s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
        derivativeEnvelopeSignedAverageConstant * s.bandwidth * κ)
    (hc : ∀ ε : ℝ, 0 ≤ ε → ∀ t ∈ Icc (0 : ℝ) 1,
      IntrinsicRectangleConcentration
        (seededSplitBaseDistribution μ ξ A 0 ε t) C₀ δ κ) :
    rectangleDistance μ (sumVector ξ) A ≤
      intrinsicOptimizationConstant relativeDerivativeBandwidth
        (intrinsicComparisonConstant C₀ + 9 * C₀) *
      min 1 (intrinsicRelativeRate κ δ s₄ (dimensionLog p)) := by
  letI : NeZero p := ⟨by omega⟩
  let L := dimensionLog p
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hδ : 0 < δ := h.delta_pos hp hunit
  have hK : 1 ≤ relativeDerivativeBandwidth := relativeDerivativeBandwidth_ge_one
  have hC : 0 ≤ intrinsicComparisonConstant C₀ + 9 * C₀ := by
    linarith [intrinsicComparisonConstant_pos hC₀]
  let b := intrinsicBandwidth relativeDerivativeBandwidth δ s₄ L
  have hbpos : 0 < b := intrinsicBandwidth_pos
    (s₄ := s₄) (L := L) (zero_lt_one.trans_le hK) hδ
  have hband : relativeDerivativeBandwidth * δ ≤ b :=
    intrinsicBandwidth_admissible (zero_le_one.trans hK)
  have hδb : δ ≤ b := (le_mul_of_one_le_left hδ.le hK).trans hband
  apply intrinsic_rate_of_small_bandwidth_estimate hK hC hκ hδ hL hr.nonneg
    (rectangleDistance_le_one μ (sumVector ξ) A)
  intro _
  have hsmooth : smoothingDiscrepancy μ (sumVector ξ) A b hbpos ≤
      intrinsicComparisonConstant C₀ * (L * κ) *
        (δ + s₄ / b * intrinsicComparisonLog L b) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) h.measurable_sum A b hbpos _).mpr
    intro lo hi
    let s := FaceSmoother.closedBox lo hi b hbpos
    have hband4 : 4 * δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right relativeDerivativeBandwidth_ge_four h.delta_nonneg).trans hband
    have ht := intrinsic_smooth_comparison_of_boundary_suppliers μ ξ h
      (hr.relativeMomentBounds h) hp hunit A hA s rfl hband hC₀
      (zero_lt_one.trans_le hκ) (henv s rfl hband4)
      (fun t ht => hc (L * b ^ 2) (mul_nonneg hLp.le (sq_nonneg _)) t ⟨ht.1.le, ht.2.le⟩)
    exact ht
  have hrho := (rectangleDistance_le_smoothingDiscrepancy_intrinsic hp μ (sumVector ξ)
    h.measurable_sum A hC₀.le h.delta_nonneg (zero_le_one.trans hκ) hbpos hδb hb hg).trans
      (add_le_add_right hsmooth _)
  change rectangleDistance μ (sumVector ξ) A ≤
    (intrinsicComparisonConstant C₀ + 9 * C₀) * κ * L *
      (b + δ + s₄ / b * intrinsicComparisonLog L b)
  apply hrho.trans
  have hlog : 0 ≤ intrinsicComparisonLog L b := by
    unfold intrinsicComparisonLog
    have hx : 0 ≤ Real.log (1 + 1 / (L * b ^ 2)) := Real.log_nonneg (by
      have hInv : 0 ≤ 1 / (L * b ^ 2) := by positivity
      linarith)
    linarith
  have hF : 0 ≤ δ + s₄ / b * intrinsicComparisonLog L b :=
    add_nonneg hδ.le (mul_nonneg (div_nonneg hr.nonneg hbpos.le) hlog)
  have hKL : 0 ≤ κ * L := mul_nonneg (zero_le_one.trans hκ) hLp.le
  have hcross₁ := mul_nonneg (mul_nonneg (intrinsicComparisonConstant_pos hC₀).le hKL) hbpos.le
  have hcross₂ := mul_nonneg (mul_nonneg (show 0 ≤ 9 * C₀ by positivity) hKL) hF
  change intrinsicComparisonConstant C₀ * (L * κ) *
    (δ + s₄ / b * intrinsicComparisonLog L b) + 9 * C₀ * b * κ * L ≤ _
  nlinarith only [hcross₁, hcross₂]

end
end RectangleCLTArxivV1
