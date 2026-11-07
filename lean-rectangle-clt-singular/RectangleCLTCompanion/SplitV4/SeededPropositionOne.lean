import RectangleCLTCompanion.SplitV4.SeededPathIdentity
import RectangleCLTCompanion.SplitV4.SeededCubicSelectorLaw
import RectangleCLTCompanion.SplitV4.SeededCubicLaw
import RectangleCLTCompanion.SplitV4.SeededTimeIntegration

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem seededNormalization_cube_eq_rpow {ε : ℝ} (hε : 0 ≤ ε) :
    seededNormalization ε ^ 3 = (1 + ε) ^ ((3 : ℝ) / 2) := by
  rw [seededNormalization, Real.sqrt_eq_rpow,
    ← Real.rpow_mul_natCast (show 0 ≤ 1 + ε by linarith) (1 / 2 : ℝ) 3]
  norm_num

def normalizedSeededCubicTerm {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε t : ℝ) : ℝ :=
  ∫ y, relativeCubicContraction s μ ξ y ∂normalizedSeededInterpolationLaw μ ξ A ε t

def normalizedSeededFourthRemainder {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) : ℝ :=
  seededFourthRemainder (seededRescaledSmoother s ε hε) μ ξ A 0 ε t

def normalizedSeededExpectation {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε t : ℝ) : ℝ :=
  ∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε t

theorem normalizedSeededExpectation_eq_seeded_test
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    normalizedSeededExpectation s μ ξ A ε t =
      (seededRescaledSmoother s ε hε).seededSelectorHeatExpectation μ ξ A ε 0 t := by
  rw [normalizedSeededExpectation, integral_normalizedSeeded_test s μ ξ A hε t,
    ← (seededRescaledSmoother s ε hε).integral_seededInterpolationLaw_eq_seededSelectorHeatExpectation
      μ ξ hξ A ε 0 ht.1 ht.2]
  simp only [zero_add]

theorem hasDerivAt_normalizedSeededExpectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (normalizedSeededExpectation s μ ξ A ε)
      (-(t / (3 * (seededNormalization ε) ^ 3)) * normalizedSeededCubicTerm s μ ξ A ε t +
        normalizedSeededFourthRemainder s μ ξ A ε hε t) t := by
  let f := seededRescaledSmoother s ε hε
  have hd := hasDerivAt_seeded_test_manuscript f μ ξ h A hA hε 0 ht
  rw [variableSignedCubicPathTerm_eq_seeded_integral f μ ξ h hrel A 0 hε ht.1.le ht.2.le] at hd
  simp only [zero_add] at hd
  rw [integral_normalizedSeeded_cubic s μ ξ A hε t] at hd
  have he : -(t / 3) * ((∫ y, relativeCubicContraction s μ ξ y
      ∂normalizedSeededInterpolationLaw μ ξ A ε t) / (seededNormalization ε) ^ 3) +
        seededFourthRemainder f μ ξ A 0 ε t =
      -(t / (3 * (seededNormalization ε) ^ 3)) * normalizedSeededCubicTerm s μ ξ A ε t +
        normalizedSeededFourthRemainder s μ ξ A ε hε t := by
    unfold normalizedSeededCubicTerm normalizedSeededFourthRemainder f
    ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact normalizedSeededExpectation_eq_seeded_test s μ ξ h.measurable A hε ⟨hr.1.le, hr.2.le⟩

theorem seeded_derivative_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth * δ ≤ s.bandwidth)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let ε := dimensionLog p * s.bandwidth ^ 2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |t / (3 * (seededNormalization ε) ^ 3) * normalizedSeededCubicTerm s μ ξ A ε t| ≤
        seededDerivativeConstant * M₃ * (dimensionLog p * Real.sqrt (dimensionLog p)) * t / (t + ε) ∧
    |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
        seededDerivativeConstant * M₄ * (dimensionLog p * Real.sqrt (dimensionLog p)) /
          (s.bandwidth * (t + ε)) := by
  let ε := dimensionLog p * s.bandwidth ^ 2
  have hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  have hw : s.bandwidth ≤ f.bandwidth := seededRescaledSmoother_bandwidth_ge s hε
  constructor
  · have hb := seeded_relative_cubic_product_rate μ ξ h hrel hp hunit A hA f 0
      s.bandwidth_pos hw ht hband
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
  · exact seeded_fourth_remainder_bound μ ξ h hrel hp hunit A hA f 0 s.bandwidth_pos hw ht hband

/-- Actual seeded comparison cost, after integrating the proved cubic
and fourth-order estimates. No derivative-bound hypothesis is supplied by
the caller. -/
theorem seeded_time_comparison_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth * δ ≤ s.bandwidth) :
    let ε := dimensionLog p * s.bandwidth ^ 2
    |normalizedSeededExpectation s μ ξ A ε 1 - normalizedSeededExpectation s μ ξ A ε 0| ≤
      seededDerivativeConstant * (dimensionLog p * Real.sqrt (dimensionLog p)) *
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
  let a := seededDerivativeConstant * M₃ * (dimensionLog p * Real.sqrt (dimensionLog p))
  let b := seededDerivativeConstant * M₄ * (dimensionLog p * Real.sqrt (dimensionLog p)) / s.bandwidth
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg seededDerivativeConstant_pos.le hrel.s₃_nonneg)
    (mul_nonneg hL.le (Real.sqrt_nonneg _))
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |D t| ≤ a * t / (t + ε) + b / (t + ε) := by
    have hx := seeded_derivative_bounds μ ξ h hrel hp hunit A hA s hband ht
    change |-(t / (3 * (seededNormalization ε) ^ 3)) * normalizedSeededCubicTerm s μ ξ A ε t +
      normalizedSeededFourthRemainder s μ ξ A ε hε.le t| ≤ _
    apply (abs_add _ _).trans
    exact add_le_add (by simpa only [abs_mul, abs_neg, a] using hx.1)
      (by simpa only [b, div_div, mul_assoc] using hx.2)
  have hh := seeded_time_increment_le hε ha hP hd hb
  convert hh using 1 <;> dsimp only [a, b] <;> ring

end

end RectangleCLT.Companion.SplitV4
