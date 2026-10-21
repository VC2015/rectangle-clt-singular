import RectangleCLT.SubexponentialTruncation
import RectangleCLT.SubexponentialRateBounds
import RectangleCLT.SubexponentialCutoffScales
import RectangleCLT.ProxyBounded
import RectangleCLT.GaussianMarginalCoupling
import RectangleCLT.CoordinateRescaling

/-! Quantitative assembly of the actual truncation and covariance-proxy
estimates. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 K : ℝ}

theorem subexponentialRate_nonneg (h : SubexponentialHypotheses μ Y B4 K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q) :
    0 ≤ subexponentialRate n B4 K Q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast h.dimension_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.sample_size_pos
  have hH : 0 ≤ truncationLog n p :=
    zero_le_one.trans (subexponentialCutoffHeight_bounds hn1 hp).1
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)
  have hB : 0 ≤ B4 := le_trans (by norm_num) h.fourth_scale_ge_one
  have hK : 0 ≤ K := le_trans (by norm_num) h.tail_scale_ge_one
  have hc := hQ.pairGap_pos h.dimension_pos
  have ha3 := hQ.a3_pos h.dimension_pos
  have ha4 := hQ.a4_pos
  unfold subexponentialRate
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact div_nonneg (mul_nonneg (mul_nonneg hB hL) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg hc.le ha3.le) (Real.sqrt_nonneg _))
  · exact div_nonneg (mul_nonneg hB hL)
      (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hc _).le
        (Real.rpow_pos_of_pos (mul_pos ha3 ha4) _).le) (Real.sqrt_nonneg _))
  · exact div_nonneg (mul_nonneg (mul_nonneg hK hH) (Real.sqrt_nonneg _))
      (mul_nonneg hc.le (Real.sqrt_nonneg _))

/-- Quantitative substitution of the actual normalized moments and fixed
proxy discrepancy into the bounded theorem's rate. -/
theorem normalized_truncation_boundedProxyRate_le (h : SubexponentialHypotheses μ Y B4 K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q)
    {q : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ 64 * K * truncationLog n p}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    boundedProxyLocalRate μ
      (normalizedCenteredTruncation μ Y (64 * K * truncationLog n p)
        (truncationStandardDeviations μ Y (64 * K * truncationLog n p)))
      (4 * (64 * K * truncationLog n p) / Real.sqrt (n : ℝ)) Q ≤
      256 * subexponentialRate n B4 K Q +
        proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y))) Q *
          dimensionLog p / pairGap Q +
        (4 * B4 * Real.sqrt q) * dimensionLog p / pairGap Q := by
  let u := 64 * K * truncationLog n p
  let ξ := normalizedCenteredTruncation μ Y u (truncationStandardDeviations μ Y u)
  let Δ := proxyCovarianceDiscrepancy
    (covariance μ (sumVector (sampleNormalizedObservations Y))) Q
  let L := dimensionLog p
  let c := pairGap Q
  let a := a3 Q
  let b := a4 Q
  let D := Real.rpow c (5 / 6 : ℝ) * Real.rpow (a * b) (1 / 3 : ℝ)
  let sn := Real.sqrt (n : ℝ)
  let T3 := B4 * L * Real.sqrt L / (c * a * sn)
  let T4 := B4 * L / (D * sn)
  let T0 := K * truncationLog n p * Real.sqrt L / (c * sn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
  have hs : 0 < sn := Real.sqrt_pos.mpr hnR
  have hc : 0 < c := hQ.pairGap_pos h.dimension_pos
  have ha : 0 < a := hQ.a3_pos h.dimension_pos
  have hb : 0 < b := hQ.a4_pos
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos (mul_pos ha hb) _)
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)
  have hH : 0 ≤ truncationLog n p := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.sample_size_pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.dimension_pos
    exact zero_le_one.trans (subexponentialCutoffHeight_bounds hn1 hp1).1
  have hB : 0 ≤ B4 := le_trans (by norm_num) h.fourth_scale_ge_one
  have hK : 0 ≤ K := le_trans (by norm_num) h.tail_scale_ge_one
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h3 : gamma3 μ ξ ≤ 8 * B4 / sn := h.normalized_truncation_gamma3 hq hu hprob hsmall
  have h4 : Real.sqrt (gamma4 μ ξ) ≤ 8 * B4 / sn :=
    h.normalized_truncation_sqrt_gamma4 hq hu hprob hsmall
  have hdis : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q ≤
      Δ + 4 * B4 * Real.sqrt q :=
    h.normalized_truncation_fixed_proxy_error Q hq hu hprob (by linarith)
  have hraw : boundedProxyLocalRate μ ξ (4 * u / sn) Q ≤
      (8 * B4 / sn) * L * Real.sqrt L / (c * a) +
        (8 * B4 / sn) * L / D + (4 * u / sn) * Real.sqrt L / c +
          (Δ + 4 * B4 * Real.sqrt q) * L / c := by
    unfold boundedProxyLocalRate localRateWithParameters
    change _ ≤ _
    gcongr <;> assumption
  have heq : (8 * B4 / sn) * L * Real.sqrt L / (c * a) +
      (8 * B4 / sn) * L / D + (4 * u / sn) * Real.sqrt L / c +
        (Δ + 4 * B4 * Real.sqrt q) * L / c =
      8 * T3 + 8 * T4 + 256 * T0 + Δ * L / c +
        (4 * B4 * Real.sqrt q) * L / c := by
    dsimp [T3, T4, T0, u]
    field_simp [ne_of_gt hs, ne_of_gt hc, ne_of_gt ha, ne_of_gt hD]
    <;> ring
  have hT3 : 0 ≤ T3 := by dsimp [T3]; positivity
  have hT4 : 0 ≤ T4 := by dsimp [T4]; positivity
  have hE : subexponentialRate n B4 K Q = T3 + T4 + T0 := rfl
  change boundedProxyLocalRate μ ξ (4 * u / sn) Q ≤ _
  rw [hE]
  exact (hraw.trans_eq heq).trans (by
    change _ ≤ 256 * (T3 + T4 + T0) + Δ * L / c + (4 * B4 * Real.sqrt q) * L / c
    nlinarith only [hT3, hT4])

/-- One universal constant for the standardized sub-exponential proxy bound. -/
def subexponentialProxyConstant : ℝ := 512 * boundedProxyConstant

theorem subexponentialProxyConstant_ge_one : 1 ≤ subexponentialProxyConstant := by
  have hc := boundedProxyConstant_ge_two
  unfold subexponentialProxyConstant
  linarith

/-- Sub-exponential approximation to the unchanged covariance proxy.
Every hypothesis is a property of the original random observations or
the original covariance proxy. -/
theorem subexponentialProxyRectangleCLT (h : SubexponentialHypotheses μ Y B4 K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hQ : LocalCovarianceHypotheses (A * A.transpose)) (R : Rect p) :
    rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      subexponentialProxyConstant * min 1
        (subexponentialRate n B4 K (A * A.transpose) +
          proxyCovarianceDiscrepancy
            (covariance μ (sumVector (sampleNormalizedObservations Y)))
            (A * A.transpose) * dimensionLog p / pairGap (A * A.transpose)) := by
  let Q := A * A.transpose
  let E := subexponentialRate n B4 K Q
  let L := dimensionLog p
  let c := pairGap Q
  let Δ := proxyCovarianceDiscrepancy
    (covariance μ (sumVector (sampleNormalizedObservations Y))) Q
  let D := Δ * L / c
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
  have hE : 0 ≤ E := subexponentialRate_nonneg h Q hQ
  have hD : 0 ≤ D :=
    div_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
      (zero_le_one.trans hL)) hc.le
  have hC : 1 ≤ boundedProxyConstant := le_trans (by norm_num) boundedProxyConstant_ge_two
  have hC0 : 0 ≤ boundedProxyConstant := zero_le_one.trans hC
  have hCfinal : 1 ≤ subexponentialProxyConstant := subexponentialProxyConstant_ge_one
  have hone := rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A R
  have hlinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      subexponentialProxyConstant * (E + D) := by
    by_cases hsmallRate : E < 1
    · have hscales := subexponentialRate_small_scales h.dimension_pos h.sample_size_pos
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
          boundedProxyConstant * (256 * E + D + v) := by
        intro lo hi
        have hb := boundedProxyRectangleCLT μ ξ (4 * u / Real.sqrt (n : ℝ)) hdata
          h.dimension_pos hunit A hQ (Rect.closedBox lo hi)
        have hrate := normalized_truncation_boundedProxyRate_le h Q hQ hq hprob hsmall
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
        have h3 : 0 ≤ B4 * L * Real.sqrt L / (c * a3 Q * Real.sqrt (n : ℝ)) := by positivity
        have h4 : 0 ≤ B4 * L /
            (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a3 Q * a4 Q) (1 / 3 : ℝ) *
              Real.sqrt (n : ℝ)) :=
          div_nonneg (mul_nonneg hB (zero_le_one.trans hL))
            (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hc _).le
              (Real.rpow_pos_of_pos (mul_pos ha3 ha4) _).le) (Real.sqrt_nonneg _))
        change T0 ≤ B4 * L * Real.sqrt L / (c * a3 Q * Real.sqrt (n : ℝ)) +
          B4 * L / (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a3 Q * a4 Q) (1 / 3 : ℝ) *
            Real.sqrt (n : ℝ)) + T0
        linarith only [h3, h4]
      have hrest0 : 0 ≤ q + 4 * p * r := by positivity
      have hweight : q + 4 * p * r ≤ boundedProxyConstant * (q + 4 * p * r) := by
        nlinarith only [mul_le_mul_of_nonneg_right hC hrest0]
      have hcostC := mul_le_mul_of_nonneg_left hcost hC0
      have hT0C := mul_le_mul_of_nonneg_left hT0 (show 0 ≤ 256 * boundedProxyConstant by positivity)
      have hED := mul_nonneg hC0 hD
      change rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
        (512 * boundedProxyConstant) * (E + D)
      nlinarith only [hb, hweight, hcostC, hT0C, hED]
    · have hsum : 1 ≤ E + D := by linarith
      exact hone.trans (one_le_mul_of_one_le_of_one_le hCfinal hsum)
  have hmin := le_max_mul_min_of_le_one (add_nonneg hE hD) hone hlinear
  simpa only [max_eq_right hCfinal, E, D, Δ, L, c, Q] using hmin

def subexponentialBothTargetsConstant : ℝ :=
  subexponentialProxyConstant + gaussianComparisonLocalConstant

theorem subexponentialBothTargetsConstant_ge_one : 1 ≤ subexponentialBothTargetsConstant := by
  unfold subexponentialBothTargetsConstant
  linarith [subexponentialProxyConstant_ge_one, gaussianComparisonLocalConstant_ge_two]

/-- Corollary 2: approximation to both the true Gaussian and the Gaussian
with the fixed proxy covariance. -/
theorem subexponentialBothTargets (h : SubexponentialHypotheses μ Y B4 K)
    (A_S A_Q : Matrix (Fin p) (Fin p) ℝ)
    (hQ : LocalCovarianceHypotheses (A_Q * A_Q.transpose))
    (hfactor : A_S * A_S.transpose = covariance μ (sumVector (sampleNormalizedObservations Y)))
    (R : Rect p) :
    max (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R) ≤
      subexponentialBothTargetsConstant * min 1
        (subexponentialRate n B4 K (A_Q * A_Q.transpose) +
          proxyCovarianceDiscrepancy
            (covariance μ (sumVector (sampleNormalizedObservations Y)))
            (A_Q * A_Q.transpose) * dimensionLog p / pairGap (A_Q * A_Q.transpose)) := by
  let rate := subexponentialRate n B4 K (A_Q * A_Q.transpose) +
    proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y)))
      (A_Q * A_Q.transpose) * dimensionLog p / pairGap (A_Q * A_Q.transpose)
  let d := proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y)))
    (A_Q * A_Q.transpose) * dimensionLog p / pairGap (A_Q * A_Q.transpose)
  have hd : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
      (zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)))
        (hQ.pairGap_pos h.dimension_pos).le
  have hE := subexponentialRate_nonneg h (A_Q * A_Q.transpose) hQ
  have hr : 0 ≤ rate := add_nonneg hE hd
  have hdr : d ≤ rate := by dsimp [rate, d]; linarith only [hE]
  have hC0 : 0 ≤ subexponentialProxyConstant := zero_le_one.trans subexponentialProxyConstant_ge_one
  have hG0 : 0 ≤ gaussianComparisonLocalConstant :=
    le_trans (by norm_num) gaussianComparisonLocalConstant_ge_two
  have hproxy := subexponentialProxyRectangleCLT h A_Q hQ R
  have hproxyLinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R ≤
      subexponentialProxyConstant * rate :=
    hproxy.trans (mul_le_mul_of_nonneg_left (min_le_right 1 rate) hC0)
  have hcomparison := gaussianComparisonLocal h.dimension_pos A_S A_Q
    (fun j => by rw [hfactor]; exact h.unit_diagonal j) hQ.unit_diagonal
    (hQ.pairGap_pos h.dimension_pos) R
  rw [hfactor] at hcomparison
  have hcomparisonLinear : |(gaussianLaw A_S).real R.carrier - (gaussianLaw A_Q).real R.carrier| ≤
      gaussianComparisonLocalConstant * rate :=
    hcomparison.trans ((mul_le_mul_of_nonneg_left (min_le_right 1 d) hG0).trans
      (mul_le_mul_of_nonneg_left hdr hG0))
  have htrueLinear : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R ≤
      subexponentialBothTargetsConstant * rate := by
    have htri := abs_sub_le
      (μ.real (sumVector (sampleNormalizedObservations Y) ⁻¹' R.carrier))
      ((gaussianLaw A_Q).real R.carrier) ((gaussianLaw A_S).real R.carrier)
    rw [abs_sub_comm ((gaussianLaw A_Q).real R.carrier)] at htri
    change rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R ≤
      rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R + _ at htri
    exact (htri.trans (add_le_add hproxyLinear hcomparisonLinear)).trans_eq
      (by unfold subexponentialBothTargetsConstant; ring)
  have hproxyLinear' : rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R ≤
      subexponentialBothTargetsConstant * rate :=
    hproxyLinear.trans (mul_le_mul_of_nonneg_right
      (by unfold subexponentialBothTargetsConstant; linarith) hr)
  have hone : max (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError μ (sumVector (sampleNormalizedObservations Y)) A_Q R) ≤ 1 :=
    max_le (rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A_S R)
      (rectangleError_le_one μ (sumVector (sampleNormalizedObservations Y)) A_Q R)
  have hmin := le_max_mul_min_of_le_one hr hone (max_le htrueLinear hproxyLinear')
  simpa only [max_eq_right subexponentialBothTargetsConstant_ge_one, rate] using hmin

theorem proxyCovarianceDiscrepancy_self {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    proxyCovarianceDiscrepancy S S = 0 := by
  apply le_antisymm _ (proxyCovarianceDiscrepancy_nonneg S S)
  apply (Finset.fold_max_le _).mpr
  exact ⟨le_rfl, fun _ _ => by simp⟩

/-- The standardized matched-covariance form of Corollary 1. -/
theorem subexponentialRectangleCLT (h : SubexponentialHypotheses μ Y B4 K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hlocal : LocalCovarianceHypotheses (covariance μ (sumVector (sampleNormalizedObservations Y))))
    (hfactor : A * A.transpose = covariance μ (sumVector (sampleNormalizedObservations Y)))
    (R : Rect p) :
    rectangleError μ (sumVector (sampleNormalizedObservations Y)) A R ≤
      subexponentialProxyConstant * min 1
        (subexponentialRate n B4 K (covariance μ (sumVector (sampleNormalizedObservations Y)))) := by
  have hQ : LocalCovarianceHypotheses (A * A.transpose) := by rw [hfactor]; exact hlocal
  have hb := subexponentialProxyRectangleCLT h A hQ R
  simpa only [hfactor, proxyCovarianceDiscrepancy_self, zero_mul, zero_div, add_zero] using hb

end

end RectangleCLT
