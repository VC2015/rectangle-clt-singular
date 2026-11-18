import RectangleCLTArxivV1.PairedIntrinsicBennett

/-!
# Paired comparison endpoints with the frozen paper's numbering

The proof implementations retain internal compatibility names. These public
aliases use the labels of arXiv v1: E.2 is the large-increment comparison,
E.3 is Gaussian-endpoint smoothing, E.4 is paired Slepian interpolation,
and E.5 is the truncated Bennett maximum. Theorem 2(ii) is
`theorem_2_ii_intrinsic` from the imported implementation.
-/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
universe u

theorem lemma_E2_intrinsic_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ), 1 ≤ p → 1 ≤ n →
      ∀ (X : Fin n → Ω → Vector p), (∀ i, Measurable (X i)) →
      ProbabilityTheory.iIndepFun X μ →
      (∀ i j, (∫ ω, X i ω j ∂μ) = 0) →
      (∀ i j, Integrable (fun ω => X i ω j ^ 4) μ) →
      (∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) →
      ∀ φ : ℝ, 0 < φ →
      rectangleDistance μ (normalizedObservationSum X) A ≤ C *
        (gaussianMaximumMean A / Real.sqrt (dimensionLog p)) *
        largeIncrementMasterRate (dimensionLog p) (deltaOne μ X)
          (pairedTailVariance μ (normalizedSummands X) (φ * dimensionLog p)⁻¹)
          (pairedTailExpectedMaximum μ (normalizedSummands X) (φ * dimensionLog p)⁻¹) φ := by
  exact lemma_E1_intrinsic_comparison.{u}

theorem lemma_E3_intrinsic_smoothing
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) :
    rectangleDistance μ V A ≤ intrinsicGaussianSmoothingConstant *
      (smoothingDiscrepancy μ V A h hh + h * gaussianMaximumMean A * dimensionLog p) := by
  exact gaussianEndpointSmoothing_intrinsic hp μ V hV A hdiag h hh

open RectangleCLT.Companion.SplitV4.C4Test in
theorem lemma_E4_paired_slepian {p : ℕ} (f : C4Test p)
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 ≤ h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      ((1 / 2 : ℝ) * (∫ z : Ω × Vector p, f.hessianTrace
          (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
          (slepianPoint (sumVector ξ) t z) ∂μ.prod (gaussianLaw A)) -
        (1 / (2 * Real.sqrt t)) * (∫ z : Ω × Vector p,
          f.gradient (slepianPoint (sumVector ξ) t z) (copyArrayLargeMean μ ξ z.1 h)
            ∂μ.prod (gaussianLaw A)) -
        t / 8 * (∑ i, ∫ z, f.trapezoidalRemainder
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ))) t := by
  exact lemma_E3_paired_slepian f μ ξ hξ hind hfourth hcenter A h hh ht ht1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem lemma_E5_truncated_bennett_maximum {p n : ℕ} (T : Fin n → Ω → Vector p)
    (hp : 1 ≤ p) (hT : ∀ i, Measurable (T i)) (hind : iIndepFun T μ)
    (hsym : ∀ i, IdentDistrib (T i) (fun ω => -T i ω) μ μ)
    {q u v A : ℝ} (hq : 1 < q) (hu : 0 < u) (hv : 0 < v)
    (hsecond : ∀ i j, Integrable (fun ω => T i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v)
    (hmoment : ∀ i, Integrable (fun ω => ‖T i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖T i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      2 * u * dimensionLog p / Real.log (1 + u ^ 2 * dimensionLog p / v) +
        A ^ q / u ^ (q - 1) := by
  exact lemma_E4_truncated_bennett_maximum T hp hT hind hsym hq hu hv hsecond hvariance hmoment hbudget

theorem lemma_E5_truncated_bennett_maximum_zero_variance {p n : ℕ}
    (T : Fin n → Ω → Vector p)
    (hsecond : ∀ i j, Integrable (fun ω => T i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ 0) :
    sumVector T =ᵐ[μ] 0 := by
  exact lemma_E4_truncated_bennett_maximum_zero_variance T hsecond hvariance

end
end RectangleCLTArxivV1
