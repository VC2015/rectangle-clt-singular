import RectangleCLTArxivV1.RestorationIntrinsic
import RectangleCLTCompanion.SplitV4.SeededPropositionOne

/-!
# Seeded interpolation and time integration retaining the intrinsic coefficient

These intermediate bounds consume actual layer concentration for the seeded
base. The derivative identity, all original/fresh copy patterns, normalized
endpoint laws, and scalar time integration are proved/imported, rather than
assumed as a comparison remainder.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology Interval
noncomputable section

def intrinsicSeededDerivativeConstant (C₀ : ℝ) : ℝ := 6 * intrinsicRestorationConstant C₀

theorem intrinsicSeededDerivativeConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < intrinsicSeededDerivativeConstant C₀ :=
  mul_pos (by norm_num) (intrinsicRestorationConstant_pos hC₀)

theorem intrinsic_seeded_relative_cubic_product_rate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A x (dimensionLog p * h₀ ^ 2) t) C₀ δ κ) :
    |(-(t / 3)) * restorationThirdExpectation s
      ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x (dimensionLog p * h₀ ^ 2) t z.1)
      (seededCopyWhitened A ξ) (seededCopyOriginal ξ) (fun _ _ => 0)
      (seededSplitGaussianScale (dimensionLog p * h₀ ^ 2) t)| ≤
        (intrinsicSeededDerivativeConstant C₀) * M₃ * (dimensionLog p * κ) *
          t / (t + dimensionLog p * h₀ ^ 2) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1.le ht.2.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ dimensionLog p * h₀ ^ 2 := mul_nonneg hL (sq_nonneg _)
  have hcond := seeded_width_scale_conditions hp h.delta_nonneg hh₀ ht.1.le hband
  have hb := intrinsic_seeded_relative_cubic_product_bound μ ξ h hrel hp hunit A hA s x hε
    ⟨ht.1.le, ht.2.le⟩ (hcond.1.trans hwidth) hcond.2.1 hC₀ hκ hc
  have hsq := seededSplitGaussianScale_sq hε ht.1.le
  have hsum : 0 < t + dimensionLog p * h₀ ^ 2 := add_pos_of_pos_of_nonneg ht.1 hε
  rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg ht.1.le (by norm_num))]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg ht.1.le (by norm_num))).trans
  rw [hsq]
  have hrhs : 0 ≤ (intrinsicRestorationConstant C₀) * M₃ *
      (dimensionLog p * κ) * t :=
    mul_nonneg (mul_nonneg (mul_nonneg (intrinsicRestorationConstant_pos hC₀).le hrel.s₃_nonneg)
      (mul_nonneg hL hκ.le)) ht.1.le
  unfold intrinsicSeededDerivativeConstant
  calc
    _ = ((2 / 3 : ℝ) * ((intrinsicRestorationConstant C₀) * M₃ *
        (dimensionLog p * κ) * t)) /
          (t + dimensionLog p * h₀ ^ 2) := by field_simp; ring
    _ ≤ (6 * ((intrinsicRestorationConstant C₀) * M₃ *
        (dimensionLog p * κ) * t)) /
          (t + dimensionLog p * h₀ ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hrhs) hsum.le
    _ = _ := by ring

theorem intrinsic_seeded_relative_fourth_product_rate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t r : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀) (freshY freshW freshShift : Bool)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A x (dimensionLog p * h₀ ^ 2) t) C₀ δ κ) :
    |restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x (dimensionLog p * h₀ ^ 2) t z.1)
      (seededCopyWhitened A ξ) (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
      (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale (dimensionLog p * h₀ ^ 2) t)| ≤
        (2 * (intrinsicRestorationConstant C₀)) * M₄ * (dimensionLog p * κ) /
          (h₀ * (t + dimensionLog p * h₀ ^ 2)) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1.le ht.2.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ dimensionLog p * h₀ ^ 2 := mul_nonneg hL (sq_nonneg _)
  have hcond := seeded_width_scale_conditions hp h.delta_nonneg hh₀ ht.1.le hband
  have hb := intrinsic_seeded_relative_fourth_product_bound μ ξ h hrel hp hunit A hA s x hε
    ⟨ht.1.le, ht.2.le⟩ hr hcond.2.1 (hcond.2.2.trans hwidth) freshY freshW freshShift hC₀ hκ hc
  have hsq := seededSplitGaussianScale_sq hε ht.1.le
  have hsum : 0 < t + dimensionLog p * h₀ ^ 2 := add_pos_of_pos_of_nonneg ht.1 hε
  apply hb.trans
  rw [hsq]
  have hnum : 0 ≤ (2 * (intrinsicRestorationConstant C₀)) * M₄ *
      (dimensionLog p * κ) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (intrinsicRestorationConstant_pos hC₀).le)
      hrel.s₄_nonneg) (mul_nonneg hL hκ.le)
  have hh := div_le_div_of_nonneg_left hnum hh₀ (hwidth)
  have hh' := div_le_div_of_nonneg_right hh hsum.le
  convert hh' using 1
  · field_simp
    ring
  · field_simp
theorem intrinsic_seeded_fourth_remainder_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A x (dimensionLog p * h₀ ^ 2) t) C₀ δ κ) :
    |seededFourthRemainder s μ ξ A x (dimensionLog p * h₀ ^ 2) t| ≤
      (intrinsicSeededDerivativeConstant C₀) * M₄ * (dimensionLog p * κ) /
        (h₀ * (t + dimensionLog p * h₀ ^ 2)) := by
  let ε := dimensionLog p * h₀ ^ 2
  let N := (2 * (intrinsicRestorationConstant C₀)) * M₄ * (dimensionLog p * κ) /
    (h₀ * (t + ε))
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL (sq_nonneg _)
  have hsum : 0 < t + ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hN : 0 ≤ N := div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (intrinsicRestorationConstant_pos hC₀).le) hrel.s₄_nonneg)
      (mul_nonneg hL hκ.le)) (mul_nonneg hh₀.le hsum.le)
  have hA' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandA_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact intrinsic_seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband false false false hC₀ hκ hc
  have hB' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandB_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact intrinsic_seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband true true true hC₀ hκ hc
  have hC' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandC_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact intrinsic_seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband false true true hC₀ hκ hc
  have hIA : |∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
      s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    apply abs_unit_intervalIntegral_le_const
    intro r hr
    rw [abs_mul]
    exact (mul_le_mul (calibrated_fourth_kernel_abs_le_one ⟨ht.1.le, ht.2.le⟩ hr)
      (hA' r hr) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIB : |∫ r in (0 : ℝ)..1, (1 - r) *
      s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    apply abs_unit_intervalIntegral_le_const
    intro r hr
    rw [abs_mul]
    exact (mul_le_mul (show |1 - r| ≤ 1 by rw [abs_le]; constructor <;> linarith [hr.1, hr.2])
      (hB' r hr) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIC : |∫ r in (0 : ℝ)..1, s.variableFourthPathIntegrandC
      (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x (thinningProbability t) (1 + t) r| ≤ N :=
    abs_unit_intervalIntegral_le_const hC'
  have hb : |(1 - t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hc : |t * (1 - t) / (3 * (1 + t))| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg ht.1.le (by linarith [ht.2])) (by linarith [ht.1]))]
    apply (div_le_one (by linarith [ht.1] : 0 < 3 * (1 + t))).mpr
    nlinarith [sq_nonneg t]
  have htriangle (a b c : ℝ) : |(a + b) + c| ≤ (|a| + |b|) + |c| :=
    (abs_add (a + b) c).trans (add_le_add_right (abs_add a b) |c|)
  unfold seededFourthRemainder
  change |(_ + _) + _| ≤ _
  calc
    _ ≤ |∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
        s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| +
      |(1 - t) / 2| * |∫ r in (0 : ℝ)..1, (1 - r) *
        s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| +
      |t * (1 - t) / (3 * (1 + t))| * |∫ r in (0 : ℝ)..1,
        s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| := by
      simpa only [abs_mul] using htriangle
        (∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
          s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r)
        ((1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) *
          s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r))
        ((t * (1 - t) / (3 * (1 + t))) * (∫ r in (0 : ℝ)..1,
          s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r))
    _ ≤ N + 1 * N + 1 * N := add_le_add
      (add_le_add hIA (mul_le_mul hb hIB (abs_nonneg _) zero_le_one))
      (mul_le_mul hc hIC (abs_nonneg _) zero_le_one)
    _ = _ := by unfold N ε intrinsicSeededDerivativeConstant; ring
theorem intrinsic_seeded_derivative_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth * δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p * s.bandwidth ^ 2) t) C₀ δ κ) :
    let ε := dimensionLog p * s.bandwidth ^ 2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |t / (3 * (seededNormalization ε) ^ 3) * normalizedSeededCubicTerm s μ ξ A ε t| ≤
        (intrinsicSeededDerivativeConstant C₀) * M₃ * (dimensionLog p * κ) * t / (t + ε) ∧
    |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
        (intrinsicSeededDerivativeConstant C₀) * M₄ * (dimensionLog p * κ) /
          (s.bandwidth * (t + ε)) := by
  let ε := dimensionLog p * s.bandwidth ^ 2
  have hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  have hw : s.bandwidth ≤ f.bandwidth := seededRescaledSmoother_bandwidth_ge s hε
  constructor
  · have hb := intrinsic_seeded_relative_cubic_product_rate μ ξ h hrel hp hunit A hA f 0
      s.bandwidth_pos hw ht hband hC₀ hκ hc
    rw [← seeded_relative_cubic_law_eq_product f μ ξ h hrel A hA 0 hε ht.1.le ht.2.le] at hb
    simp only [zero_add] at hb
    rw [integral_normalizedSeeded_cubic s μ ξ A hε t] at hb
    have he : t / (3 * (seededNormalization ε) ^ 3) * normalizedSeededCubicTerm s μ ξ A ε t =
        - (-(t / 3) * ((∫ y, relativeCubicContraction s μ ξ y
          ∂normalizedSeededInterpolationLaw μ ξ A ε t) / (seededNormalization ε) ^ 3)) := by
      unfold normalizedSeededCubicTerm
      ring
    rw [he, abs_neg]
    exact hb
  · exact intrinsic_seeded_fourth_remainder_bound μ ξ h hrel hp hunit A hA f 0 s.bandwidth_pos hw ht hband hC₀ hκ hc

/-- Actual seeded comparison cost, after integrating the proved cubic
and fourth-order estimates. No derivative-bound hypothesis is supplied by
the caller. -/
theorem intrinsic_seeded_time_comparison_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth * δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p * s.bandwidth ^ 2) t) C₀ δ κ) :
    let ε := dimensionLog p * s.bandwidth ^ 2
    |normalizedSeededExpectation s μ ξ A ε 1 - normalizedSeededExpectation s μ ξ A ε 0| ≤
      (intrinsicSeededDerivativeConstant C₀) * (dimensionLog p * κ) *
        (M₃ + M₄ / s.bandwidth * Real.log (1 + 1 / ε)) := by
  let ε := dimensionLog p * s.bandwidth ^ 2
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 < ε := mul_pos hL (sq_pos_of_pos s.bandwidth_pos)
  let f := seededRescaledSmoother s ε hε.le
  let P := normalizedSeededExpectation s μ ξ A ε
  let D : ℝ → ℝ := fun t => -(t / (3 * (seededNormalization ε) ^ 3)) *
    normalizedSeededCubicTerm s μ ξ A ε t + normalizedSeededFourthRemainder s μ ξ A ε hε.le t
  have hP : ContinuousOn P (Icc (0 : ℝ) 1) :=
    (continuousOn_seeded_test_expectation f μ ξ h.measurable A ε 0).congr
      (fun t ht => normalizedSeededExpectation_eq_seeded_test s μ ξ h.measurable A hε.le ht)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt P (D t) t :=
    hasDerivAt_normalizedSeededExpectation s μ ξ h hrel A hA hε.le ht
  let a := (intrinsicSeededDerivativeConstant C₀) * M₃ * (dimensionLog p * κ)
  let b := (intrinsicSeededDerivativeConstant C₀) * M₄ * (dimensionLog p * κ) / s.bandwidth
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg (intrinsicSeededDerivativeConstant_pos hC₀).le hrel.s₃_nonneg)
    (mul_nonneg hL.le hκ.le)
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |D t| ≤ a * t / (t + ε) + b / (t + ε) := by
    have hx := intrinsic_seeded_derivative_bounds μ ξ h hrel hp hunit A hA s hband hC₀ hκ ht (hc t ht)
    change |-(t / (3 * (seededNormalization ε) ^ 3)) * normalizedSeededCubicTerm s μ ξ A ε t +
      normalizedSeededFourthRemainder s μ ξ A ε hε.le t| ≤ _
    apply (abs_add _ _).trans
    exact add_le_add (by simpa only [abs_mul, abs_neg, a] using hx.1)
      (by simpa only [b, div_div, mul_assoc] using hx.2)
  have hh := seeded_time_increment_le hε ha hP hd hb
  convert hh using 1
  dsimp only [a, b]
  ring

end
end RectangleCLTArxivV1
