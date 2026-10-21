import RectangleCLT.RefinedSubexponentialSubstitution
import RectangleCLT.GeneralProxyBounded

/-! Proposition 5: truncation and covariance-proxy assembly retaining the
independently selected global and local coefficients. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 K : ℝ}

theorem refinedBoundedProxyRectangleCLT
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hQ : LocalCovarianceHypotheses (A * A.transpose)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ generalProxyConstant * min 1
      (refinedProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
        (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose))
        (dimensionLog p) (fullCovarianceScale (A * A.transpose))
        (pairGap (A * A.transpose)) (a3 (A * A.transpose)) (a4 (A * A.transpose))) := by
  obtain ⟨A_S, hfactor⟩ := gaussianComparison_factor_exists hdata.covariance_posSemidef
  have hb := generalBoundedCovarianceProxyCLT μ p n hp hn ξ δ A_S A hdata hunit
    hQ.unit_diagonal (hQ.pairGap_pos hp) hfactor R
  apply ((le_max_right _ _).trans hb).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans generalProxyConstant_ge_one)
  exact min_le_min_left 1 (generalProxyCoefficientRate_le_refined
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) (zero_le_one.trans (log_exp_mul_nat_ge_one hp))
    (hQ.pairGap_pos hp) (hQ.a3_pos hp) hQ.a4_pos)

/-- One universal constant for the standardized sub-exponential proxy bound. -/
def refinedSubexponentialProxyConstant : ℝ := 512 * generalProxyConstant

theorem refinedSubexponentialProxyConstant_ge_one : 1 ≤ refinedSubexponentialProxyConstant := by
  have hc := generalProxyConstant_ge_one
  unfold refinedSubexponentialProxyConstant
  linarith

/-- Sub-exponential approximation to the unchanged covariance proxy.
Every hypothesis is a property of the original random observations or
the original covariance proxy. -/
theorem refinedSubexponentialProxyRectangleCLT (h : SubexponentialHypotheses μ Y B4 K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hQ : LocalCovarianceHypotheses (A * A.transpose)) (R : Rect p) :
    rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      refinedSubexponentialProxyConstant * min 1
        (refinedSubexponentialRate n B4 K (A * A.transpose) +
          proxyCovarianceDiscrepancy
            (covariance μ (sumVector (sampleNormalizedObservations Y)))
            (A * A.transpose) * dimensionLog p * gaussianComparisonCoefficient (fullCovarianceScale (A * A.transpose))
              (pairGap (A * A.transpose))) := by
  let Q := A * A.transpose
  let E := refinedSubexponentialRate n B4 K Q
  let L := dimensionLog p
  let c := pairGap Q
  let Δ := proxyCovarianceDiscrepancy
    (covariance μ (sumVector (sampleNormalizedObservations Y))) Q
  let D := Δ * L * gaussianComparisonCoefficient (fullCovarianceScale Q) c
  let T0 := K * truncationLog n p * Real.sqrt L / (c * Real.sqrt (n : ℝ))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.sample_size_pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.dimension_pos
  have hnR : (0 : ℝ) < n := by linarith
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos
  have hB : 0 ≤ B4 := le_trans (by norm_num) h.fourth_scale_ge_one
  have hK : 0 ≤ K := le_trans (by norm_num) h.tail_scale_ge_one
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) h.tail_scale_ge_one
  have hH : 1 ≤ truncationLog n p := (subexponentialCutoffHeight_bounds hn1 hp1).1
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one h.dimension_pos
  have hLH : L ≤ truncationLog n p := subexponentialCutoffHeight_ge_dimensionLog hn1 hp1
  have hc : 0 < c := hQ.pairGap_pos h.dimension_pos
  have ha3 := hQ.a3_pos h.dimension_pos
  have ha4 := hQ.a4_pos
  have hE : 0 ≤ E := refinedSubexponentialRate_nonneg h Q hQ
  have hD : 0 ≤ D :=
    mul_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
      (zero_le_one.trans hL)) (gaussianComparisonCoefficient_nonneg hc)
  have hC : 1 ≤ generalProxyConstant := le_trans (by norm_num) generalProxyConstant_ge_one
  have hC0 : 0 ≤ generalProxyConstant := zero_le_one.trans hC
  have hCfinal : 1 ≤ refinedSubexponentialProxyConstant := refinedSubexponentialProxyConstant_ge_one
  have hone := rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A R
  have hlinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      refinedSubexponentialProxyConstant * (E + D) := by
    by_cases hsmallRate : E < 1
    · have hscales := refinedSubexponentialRate_small_scales h.dimension_pos h.sample_size_pos
        hB hK Q hQ hH hsmallRate
      let u := 64 * K * truncationLog n p
      let q := subexponentialCutoffProbability (n : ℝ) (p : ℝ) K
      let d := truncationStandardDeviations μ Y u
      let ξ := normalizedCenteredTruncation μ Y u d
      let r := Real.sqrt (n : ℝ) * Real.sqrt q +
        (4 * B4 * Real.sqrt q) * (2 * n * u / Real.sqrt (n : ℝ))
      let v := (4 * B4 * Real.sqrt q) * L / c
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have hq : 0 ≤ q := subexponentialCutoffProbability_nonneg hnR.le (by linarith)
      have htail : μ.real {ω | ∃ i, u < ‖Y i ω‖} ≤ q := by
        simpa only [u, q, subexponentialCutoffProbability, subexponentialCutoff,
          subexponentialCutoffHeight, truncationLog] using
            observations_norm_subexponential_tail hu h.exponential_moment
      have hprob (i : Fin n) : μ.real {ω | ‖Y i ω‖ ≤ u}ᶜ ≤ q := by
        apply (measureReal_mono (μ := μ) (show {ω | ‖Y i ω‖ ≤ u}ᶜ ⊆
          {ω | ∃ i, u < ‖Y i ω‖} from ?_)).trans htail
        intro ω hω
        exact ⟨i, lt_of_not_ge hω⟩
      have hsmall : 2 * B4 * Real.sqrt q < 1 / 2 :=
        subexponentialCutoff_epsilon_small hn1 hp1 hKpos hB hscales.1.le
      have hdata := h.normalized_truncation_bounded hq hu hprob hsmall
      have hunit := h.normalized_truncation_unit_diagonal hq hu hprob (by linarith : 2 * B4 * Real.sqrt q < 1)
      have hr : 0 ≤ r := by dsimp [r]; positivity
      have hcoupling : μ.real {ω | r <
          ‖sumVector (sampleNormalizedObservations Y) ω - sumVector ξ ω‖} ≤ q := by
        simpa only [r, ξ, d, u, q, subexponentialCutoffProbability,
          subexponentialCutoff, subexponentialCutoffHeight, truncationLog] using
            h.normalized_truncation_coupling hq hu hprob hsmall
      have hbase : ∀ lo hi : Vector p, rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
          generalProxyConstant * (256 * E + D + v) := by
        intro lo hi
        have hb := refinedBoundedProxyRectangleCLT μ ξ (4 * u / Real.sqrt (n : ℝ)) hdata
          h.dimension_pos h.sample_size_pos hunit A hQ (Rect.closedBox lo hi)
        have hrate := normalized_truncation_refinedProxyRate_le h Q hQ hq hprob hsmall
        exact hb.trans ((mul_le_mul_of_nonneg_left (min_le_right 1 _) hC0).trans
          (mul_le_mul_of_nonneg_left hrate hC0))
      have hW : Measurable (sumVector (sampleNormalizedObservations Y)) := by
        apply measurable_pi_lambda
        intro j
        simpa only [sumVector, sampleNormalizedObservations, Finset.sum_apply] using
          (Finset.measurable_sum Finset.univ fun i _ =>
            ((measurable_pi_apply j).comp (h.measurable i)).div_const (Real.sqrt (n : ℝ)))
      have hb := rectangleError_le_of_gaussian_norm_coupling μ h.dimension_pos
        (sumVector (sampleNormalizedObservations Y)) (sumVector ξ) hW A hQ.unit_diagonal
        hr hcoupling hbase R
      have hcost : v + q + 4 * p * r ≤ 256 * T0 := by
        convert subexponentialCutoff_extra_cost_le hn1 hp1 h.tail_scale_ge_one hB
          hscales.1.le hscales.2.le hL hLH hc (pairGap_le_one Q) using 1 <;>
          dsimp [v, r, u, q, T0, subexponentialCutoffProbability,
            subexponentialCutoff, subexponentialCutoffHeight, truncationLog] <;> ring
      have hT0 : T0 ≤ E := by
        have h3 : 0 ≤ B4 * L * Real.sqrt L *
            combinedThirdCoefficient (fullCovarianceScale Q) c (a3 Q) / Real.sqrt (n : ℝ) := by
          have hβ := combinedThirdCoefficient_nonneg (b := fullCovarianceScale Q) hc ha3
          positivity
        have h4 : 0 ≤ B4 * L / Real.sqrt c *
            combinedFourthCoefficient (fullCovarianceScale Q) c (a3 Q) (a4 Q) /
              Real.sqrt (n : ℝ) := by
          have hβ := combinedFourthCoefficient_nonneg (b := fullCovarianceScale Q) hc ha3 ha4
          positivity
        change T0 ≤ B4 * L * Real.sqrt L *
            combinedThirdCoefficient (fullCovarianceScale Q) c (a3 Q) / Real.sqrt (n : ℝ) +
          B4 * L / Real.sqrt c *
            combinedFourthCoefficient (fullCovarianceScale Q) c (a3 Q) (a4 Q) /
              Real.sqrt (n : ℝ) + T0
        linarith only [h3, h4]
      have hrest0 : 0 ≤ q + 4 * p * r := by positivity
      have hweight : q + 4 * p * r ≤ generalProxyConstant * (q + 4 * p * r) := by
        nlinarith only [mul_le_mul_of_nonneg_right hC hrest0]
      have hcostC := mul_le_mul_of_nonneg_left hcost hC0
      have hT0C := mul_le_mul_of_nonneg_left hT0 (show 0 ≤ 256 * generalProxyConstant by positivity)
      have hED := mul_nonneg hC0 hD
      change rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
        (512 * generalProxyConstant) * (E + D)
      nlinarith only [hb, hweight, hcostC, hT0C, hED]
    · have hsum : 1 ≤ E + D := by linarith
      exact hone.trans (one_le_mul_of_one_le_of_one_le hCfinal hsum)
  have hmin := le_max_mul_min_of_le_one (add_nonneg hE hD) hone hlinear
  simpa only [max_eq_right hCfinal, E, D, Δ, L, c, Q] using hmin

def refinedSubexponentialBothTargetsConstant : ℝ :=
  refinedSubexponentialProxyConstant + gaussianComparisonFullConstant

theorem refinedSubexponentialBothTargetsConstant_ge_one : 1 ≤ refinedSubexponentialBothTargetsConstant := by
  unfold refinedSubexponentialBothTargetsConstant
  linarith [refinedSubexponentialProxyConstant_ge_one, gaussianComparisonFullConstant_ge_one]

/-- Corollary 2: approximation to both the true Gaussian and the Gaussian
with the fixed proxy covariance. -/
theorem refinedSubexponentialBothTargets (h : SubexponentialHypotheses μ Y B4 K)
    (A_S A_Q : Matrix (Fin p) (Fin p) ℝ)
    (hQ : LocalCovarianceHypotheses (A_Q * A_Q.transpose))
    (hfactor : A_S * A_S.transpose = covariance μ (sumVector (sampleNormalizedObservations Y)))
    (R : Rect p) :
    max (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R) ≤
      refinedSubexponentialBothTargetsConstant * min 1
        (refinedSubexponentialRate n B4 K (A_Q * A_Q.transpose) +
          proxyCovarianceDiscrepancy
            (covariance μ (sumVector (sampleNormalizedObservations Y)))
            (A_Q * A_Q.transpose) * dimensionLog p * gaussianComparisonCoefficient (fullCovarianceScale (A_Q * A_Q.transpose))
              (pairGap (A_Q * A_Q.transpose))) := by
  let rate := refinedSubexponentialRate n B4 K (A_Q * A_Q.transpose) +
    proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y)))
      (A_Q * A_Q.transpose) * dimensionLog p * gaussianComparisonCoefficient (fullCovarianceScale (A_Q * A_Q.transpose))
        (pairGap (A_Q * A_Q.transpose))
  let d := proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y)))
    (A_Q * A_Q.transpose) * dimensionLog p * gaussianComparisonCoefficient (fullCovarianceScale (A_Q * A_Q.transpose))
        (pairGap (A_Q * A_Q.transpose))
  have hd : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
      (zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)))
        (gaussianComparisonCoefficient_nonneg (hQ.pairGap_pos h.dimension_pos))
  have hE := refinedSubexponentialRate_nonneg h (A_Q * A_Q.transpose) hQ
  have hr : 0 ≤ rate := add_nonneg hE hd
  have hdr : d ≤ rate := by dsimp [rate, d]; linarith only [hE]
  have hC0 : 0 ≤ refinedSubexponentialProxyConstant := zero_le_one.trans refinedSubexponentialProxyConstant_ge_one
  have hG0 : 0 ≤ gaussianComparisonFullConstant :=
    le_trans (by norm_num) gaussianComparisonFullConstant_ge_one
  have hproxy := refinedSubexponentialProxyRectangleCLT h A_Q hQ R
  have hproxyLinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R ≤
      refinedSubexponentialProxyConstant * rate :=
    hproxy.trans (mul_le_mul_of_nonneg_left (min_le_right 1 rate) hC0)
  have hcomparison := gaussianComparisonFull h.dimension_pos A_S A_Q
    (fun j => by rw [hfactor]; exact h.unit_diagonal j) hQ.unit_diagonal
    (hQ.pairGap_pos h.dimension_pos) R
  rw [hfactor] at hcomparison
  have hcomparisonLinear : |(gaussianLaw A_S).real R.carrier - (gaussianLaw A_Q).real R.carrier| ≤
      gaussianComparisonFullConstant * rate :=
    hcomparison.trans ((mul_le_mul_of_nonneg_left (min_le_right 1 d) hG0).trans
      (mul_le_mul_of_nonneg_left hdr hG0))
  have htrueLinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R ≤
      refinedSubexponentialBothTargetsConstant * rate := by
    have htri := abs_sub_le
      (μ.real (sumVector (sampleNormalizedObservations Y) ⁻¹' R.carrier))
      ((gaussianLaw A_Q).real R.carrier) ((gaussianLaw A_S).real R.carrier)
    rw [abs_sub_comm ((gaussianLaw A_Q).real R.carrier)] at htri
    change rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R ≤
      rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R + _ at htri
    exact (htri.trans (add_le_add hproxyLinear hcomparisonLinear)).trans_eq
      (by unfold refinedSubexponentialBothTargetsConstant; ring)
  have hproxyLinear' : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R ≤
      refinedSubexponentialBothTargetsConstant * rate :=
    hproxyLinear.trans (mul_le_mul_of_nonneg_right
      (by unfold refinedSubexponentialBothTargetsConstant; linarith) hr)
  have hone : max (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R) ≤ 1 :=
    max_le (rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A_Q R)
  have hmin := le_max_mul_min_of_le_one hr hone (max_le htrueLinear hproxyLinear')
  simpa only [max_eq_right refinedSubexponentialBothTargetsConstant_ge_one, rate] using hmin


/-- The matched standardized form of Proposition 5. -/
theorem refinedSubexponentialRectangleCLT (h : SubexponentialHypotheses μ Y B4 K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hlocal : LocalCovarianceHypotheses (covariance μ (sumVector (sampleNormalizedObservations Y))))
    (hfactor : A * A.transpose = covariance μ (sumVector (sampleNormalizedObservations Y)))
    (R : Rect p) :
    rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      refinedSubexponentialProxyConstant * min 1
        (refinedSubexponentialRate n B4 K (covariance μ (sumVector (sampleNormalizedObservations Y)))) := by
  have hQ : LocalCovarianceHypotheses (A * A.transpose) := by rw [hfactor]; exact hlocal
  have hb := refinedSubexponentialProxyRectangleCLT h A hQ R
  simpa only [hfactor, proxyCovarianceDiscrepancy_self, zero_mul, add_zero] using hb

end
end RectangleCLT
