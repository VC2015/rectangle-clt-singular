import RectangleCLT.ProxySharpAssembly
import RectangleCLT.ProxyStatement
import RectangleCLT.GaussianComparisonLocal

/-! Covariance-proxy master estimate for the actual bounded sum. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology Interval

namespace RectangleCLT

noncomputable section

def proxyMasterConstant : ℝ :=
  1 + FaceSmoother.gaussianThirdConstant + 18 * gaussianFourthConstant +
    (16 * Real.exp 4 + 4) + FaceSmoother.proxySecondConstant

theorem proxyMasterConstant_ge_one : 1 ≤ proxyMasterConstant := by
  unfold proxyMasterConstant
  have h3 := FaceSmoother.gaussianThirdConstant_pos
  have h4 := gaussianFourthConstant_pos
  have h2 := FaceSmoother.proxySecondConstant_pos
  have he : 0 ≤ (16 : ℝ) * Real.exp 4 + 4 := by positivity
  linarith

/-- The real bandwidth bound, imposing nondegeneracy only on the proxy.
The small-discrepancy condition controls endpoint smoothing of the true sum. -/
theorem boundedProxyMasterEstimate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hproxy : LocalCovarianceHypotheses (A * A.transpose))
    (hdiscrepancy : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ))
      (A * A.transpose) ≤ pairGap (A * A.transpose) / 2)
    (R : Rect p) (h : ℝ) (hband : 12 * δ ≤ h) :
    rectangleError μ (sumVector ξ) A R ≤ proxyMasterConstant *
      (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) /
        (pairGap (A * A.transpose) * a3 (A * A.transpose)) +
      gamma4 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) /
        (h * Real.rpow (pairGap (A * A.transpose) * a3 (A * A.transpose) *
          a4 (A * A.transpose)) (2 / 3 : ℝ)) +
      h * Real.sqrt (dimensionLog p) / pairGap (A * A.transpose) +
      proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose) *
        dimensionLog p / pairGap (A * A.transpose)) := by
  let Q := A * A.transpose
  let L := dimensionLog p
  let c := pairGap Q
  let a₃ := a3 Q
  let a₄ := a4 Q
  let cost := c * a₃ * a₄
  have hc : 0 < c := hproxy.pairGap_pos hp
  have ha₃ : 0 < a₃ := hproxy.a3_pos hp
  have ha₄ : 0 < a₄ := hproxy.a4_pos
  have hcost : 0 < cost := mul_pos (mul_pos hc ha₃) ha₄
  have hδ : 0 < δ := hdata.delta_pos hp hunit
  have hh : 0 < h := by linarith only [hband, hδ]
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hLsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  let T₃ := gamma3 μ ξ * L * Real.sqrt L / (c * a₃)
  let T₄ := gamma4 μ ξ * L * Real.sqrt L / (h * Real.rpow cost (2 / 3 : ℝ))
  let T₀ := h * Real.sqrt L / c
  let TΔ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q * L / c
  have hTΔ : 0 ≤ TΔ := by
    dsimp [TΔ]
    exact div_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _) hL.le) hc.le
  have hT₃ : 0 ≤ T₃ := div_nonneg
    (mul_nonneg (mul_nonneg (gamma3_nonneg μ ξ) hL.le) hLsqrt) (mul_pos hc ha₃).le
  have hT₄ : 0 ≤ T₄ := div_nonneg
    (mul_nonneg (mul_nonneg (gamma4_nonneg μ ξ) hL.le) hLsqrt)
    (mul_pos hh (Real.rpow_pos_of_pos hcost _)).le
  have hT₀ : 0 ≤ T₀ := div_nonneg (mul_nonneg hh.le hLsqrt) hc.le
  change rectangleError μ (sumVector ξ) A R ≤ proxyMasterConstant * (T₃ + T₄ + T₀ + TΔ)
  by_cases hsmall : h * Real.sqrt L ≤ 1
  · apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
    intro lo hi
    let s := FaceSmoother.closedBox lo hi h hh
    have h3 := s.integral_time_mul_sharpThirdAverage_le μ ξ hdata.measurable hp A hproxy rfl
    have h4 := s.integral_sharpFourthAverage_le_proxy μ ξ hdata hp hunit A hproxy hband
    have hgap := s.interpolation_smoother_gap_le_proxy_timeIntegrals μ ξ hdata hp hunit A hproxy.unit_diagonal hc hband
    have hb : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
    have herr := hdata.closedBox_error_le_smoother_gap_proxy hp hunit A hproxy.unit_diagonal hc hdiscrepancy lo hi hh hb
    have hI := add_le_add
      (add_le_add_left
        (mul_le_mul_of_nonneg_left h3
          (div_nonneg (gamma3_nonneg μ ξ) (show (0 : ℝ) ≤ 3 by norm_num)))
        (FaceSmoother.proxySecondConstant *
          proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q * L / c))
      (mul_le_mul_of_nonneg_left h4 (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) (gamma4_nonneg μ ξ)))
    have hraw := herr.trans (add_le_add_right (hgap.trans hI) _)
    have hraw' : rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
        ((2 : ℝ) / 3 * FaceSmoother.gaussianThirdConstant) * T₃ +
          (18 * gaussianFourthConstant) * T₄ + (16 * Real.exp 4 + 4) * T₀ +
          FaceSmoother.proxySecondConstant * TΔ := by
      convert hraw using 1; dsimp [s, FaceSmoother.closedBox, T₃, T₄, T₀, L, c, a₃, a₄, cost, Q, TΔ]; ring
    have hK3 : (2 : ℝ) / 3 * FaceSmoother.gaussianThirdConstant ≤ proxyMasterConstant := by
      unfold proxyMasterConstant
      have h3 := FaceSmoother.gaussianThirdConstant_pos
      have h4 := gaussianFourthConstant_pos
      have h2 := FaceSmoother.proxySecondConstant_pos
      have he : 0 ≤ (16 : ℝ) * Real.exp 4 + 4 := by positivity
      linarith
    have hK4 : 18 * gaussianFourthConstant ≤ proxyMasterConstant := by
      unfold proxyMasterConstant
      have h3 := FaceSmoother.gaussianThirdConstant_pos
      have h2 := FaceSmoother.proxySecondConstant_pos
      have he : 0 ≤ (16 : ℝ) * Real.exp 4 + 4 := by positivity
      linarith
    have hK0 : 16 * Real.exp 4 + 4 ≤ proxyMasterConstant := by
      unfold proxyMasterConstant
      have h3 := FaceSmoother.gaussianThirdConstant_pos
      have h4 := gaussianFourthConstant_pos
      have h2 := FaceSmoother.proxySecondConstant_pos
      linarith
    have hKΔ : FaceSmoother.proxySecondConstant ≤ proxyMasterConstant := by
      unfold proxyMasterConstant
      have h3 := FaceSmoother.gaussianThirdConstant_pos
      have h4 := gaussianFourthConstant_pos
      have he : 0 ≤ (16 : ℝ) * Real.exp 4 + 4 := by positivity
      linarith
    exact hraw'.trans ((add_le_add
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hK3 hT₃)
        (mul_le_mul_of_nonneg_right hK4 hT₄)) (mul_le_mul_of_nonneg_right hK0 hT₀))
        (mul_le_mul_of_nonneg_right hKΔ hTΔ)).trans_eq (by ring))
  · have hT₀one : 1 ≤ T₀ := by
      apply (le_div_iff₀ hc).mpr
      have hc1 : c ≤ 1 := pairGap_le_one Q
      linarith only [hc1, le_of_lt (lt_of_not_ge hsmall)]
    have hsum : 1 ≤ T₃ + T₄ + T₀ + TΔ := by linarith only [hT₃, hT₄, hT₀one, hTΔ]
    exact (rectangleError_le_one μ (sumVector ξ) A R).trans
      (one_le_mul_of_one_le_of_one_le proxyMasterConstant_ge_one hsum)

/-- The exact covariance-proxy rate for a bounded sum. -/
def boundedProxyLocalRate {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  localRateWithParameters μ ξ δ (pairGap Q) (a3 Q) (a4 Q) +
    proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q * dimensionLog p / pairGap Q

def boundedProxyConstant : ℝ := max 2 (13 * proxyMasterConstant)

theorem boundedProxyConstant_ge_two : 2 ≤ boundedProxyConstant := le_max_left _ _

theorem boundedProxyConstant_ge_master : proxyMasterConstant ≤ boundedProxyConstant := by
  have hm := proxyMasterConstant_ge_one
  have hk : 13 * proxyMasterConstant ≤ boundedProxyConstant := le_max_right _ _
  linarith

/-- The local covariance-proxy CLT for the actual bounded independent sum,
with no condition on the local eigenvalues of its true covariance. -/
theorem boundedProxyRectangleCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hproxy : LocalCovarianceHypotheses (A * A.transpose)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤
      boundedProxyConstant * min 1 (boundedProxyLocalRate μ ξ δ (A * A.transpose)) := by
  let Q := A * A.transpose
  let c := pairGap Q
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q
  let d := Δ * dimensionLog p / c
  let r := localRateWithParameters μ ξ δ c (a3 Q) (a4 Q)
  let M := proxyMasterConstant
  let K := boundedProxyConstant
  have hc : 0 < c := hproxy.pairGap_pos hp
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hΔ : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hΔ (zero_le_one.trans hL)) hc.le
  have hr : 0 ≤ r := localRateWithParameters_nonneg μ ξ hp hdata.delta_nonneg hc
    (hproxy.a3_pos hp) hproxy.a4_pos
  have hM : 0 ≤ M := zero_le_one.trans proxyMasterConstant_ge_one
  have hK2 : 2 ≤ K := boundedProxyConstant_ge_two
  have hK1 : 1 ≤ K := by linarith
  have hMK : M ≤ K := boundedProxyConstant_ge_master
  have hone := rectangleError_le_one μ (sumVector ξ) A R
  have hlinear : rectangleError μ (sumVector ξ) A R ≤ K * (r + d) := by
    by_cases hsmall : Δ ≤ c / 2
    · have heunit : rectangleError μ (sumVector ξ) A R - M * d ≤ 1 := by
        nlinarith [mul_nonneg hM hd]
      have hmaster : ∀ h : ℝ, 12 * δ ≤ h →
          rectangleError μ (sumVector ξ) A R - M * d ≤ M *
            (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) / (c * a3 Q) +
              gamma4 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) /
                (h * Real.rpow (c * a3 Q * a4 Q) (2 / 3 : ℝ)) +
              h * Real.sqrt (dimensionLog p) / c) := by
        intro h hh
        have hm := boundedProxyMasterEstimate μ ξ δ hdata hp hunit A hproxy hsmall R h hh
        change rectangleError μ (sumVector ξ) A R ≤ M * (_ + d) at hm
        nlinarith only [hm]
      have hb := local_rate_of_master (hdata.delta_pos hp hunit)
        (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) hL hc
        (hproxy.a3_pos hp) hproxy.a4_pos hM heunit hmaster
      have hKsmall : max 1 (13 * M) ≤ K := by
        apply max_le hK1
        exact le_max_right _ _
      have hbound : rectangleError μ (sumVector ξ) A R - M * d ≤ K * r := by
        exact hb.trans ((mul_le_mul_of_nonneg_left (min_le_right 1 r) (by positivity)).trans
          (mul_le_mul_of_nonneg_right hKsmall hr))
      have hmd := mul_le_mul_of_nonneg_right hMK hd
      nlinarith only [hbound, hmd]
    · have hhalf : 1 ≤ 2 * d := by
        dsimp [d]
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hc).mpr
        have hprod : Δ ≤ Δ * dimensionLog p := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hΔ
        nlinarith [lt_of_not_ge hsmall]
      have hkd := mul_le_mul_of_nonneg_right hK2 hd
      have hkr := mul_nonneg (by linarith : 0 ≤ K) hr
      nlinarith only [hone, hhalf, hkd, hkr]
  have hmin := le_max_mul_min_of_le_one (add_nonneg hr hd) hone hlinear
  simpa only [max_eq_right hK1, boundedProxyLocalRate, r, d, Δ, c, Q, K] using hmin

def boundedProxyBothTargetsConstant : ℝ := boundedProxyConstant + gaussianComparisonLocalConstant

/-- Both Gaussian targets of Theorem 2 for the bounded (`Q=0`) case. -/
theorem boundedProxyBothTargets
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A_S A_Q : Matrix (Fin p) (Fin p) ℝ)
    (hproxy : LocalCovarianceHypotheses (A_Q * A_Q.transpose))
    (hfactor : A_S * A_S.transpose = covariance μ (sumVector ξ)) (R : Rect p) :
    max (rectangleError μ (sumVector ξ) A_S R) (rectangleError μ (sumVector ξ) A_Q R) ≤
      boundedProxyBothTargetsConstant *
        min 1 (boundedProxyLocalRate μ ξ δ (A_Q * A_Q.transpose)) := by
  let rate := boundedProxyLocalRate μ ξ δ (A_Q * A_Q.transpose)
  let d := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A_Q * A_Q.transpose) *
    dimensionLog p / pairGap (A_Q * A_Q.transpose)
  have hd : 0 ≤ d := div_nonneg
    (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _) (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))
    (hproxy.pairGap_pos hp).le
  have hr : 0 ≤ rate := add_nonneg
    (localRateWithParameters_nonneg μ ξ hp hdata.delta_nonneg (hproxy.pairGap_pos hp)
      (hproxy.a3_pos hp) hproxy.a4_pos) hd
  have hdr : d ≤ rate := by
    change d ≤ localRateWithParameters μ ξ δ _ _ _ + d
    linarith [localRateWithParameters_nonneg μ ξ hp hdata.delta_nonneg (hproxy.pairGap_pos hp)
      (hproxy.a3_pos hp) hproxy.a4_pos]
  have hB0 : 0 ≤ boundedProxyConstant := le_trans (by norm_num) boundedProxyConstant_ge_two
  have hG0 : 0 ≤ gaussianComparisonLocalConstant :=
    le_trans (by norm_num) gaussianComparisonLocalConstant_ge_two
  have hproxyBound := boundedProxyRectangleCLT μ ξ δ hdata hp hunit A_Q hproxy R
  have hproxyLinear : rectangleError μ (sumVector ξ) A_Q R ≤ boundedProxyConstant * rate :=
    hproxyBound.trans (mul_le_mul_of_nonneg_left (min_le_right 1 rate) hB0)
  have hcomparison := gaussianComparisonLocal hp A_S A_Q
    (fun j => by rw [hfactor]; exact hunit j) hproxy.unit_diagonal (hproxy.pairGap_pos hp) R
  rw [hfactor] at hcomparison
  have hcomparisonLinear : |(gaussianLaw A_S).real R.carrier - (gaussianLaw A_Q).real R.carrier| ≤
      gaussianComparisonLocalConstant * rate :=
    hcomparison.trans ((mul_le_mul_of_nonneg_left (min_le_right 1 d) hG0).trans
      (mul_le_mul_of_nonneg_left hdr hG0))
  have htrueLinear : rectangleError μ (sumVector ξ) A_S R ≤
      boundedProxyBothTargetsConstant * rate := by
    have htri := abs_sub_le
      (μ.real (sumVector ξ ⁻¹' R.carrier)) ((gaussianLaw A_Q).real R.carrier)
      ((gaussianLaw A_S).real R.carrier)
    rw [abs_sub_comm ((gaussianLaw A_Q).real R.carrier)] at htri
    change rectangleError μ (sumVector ξ) A_S R ≤
      rectangleError μ (sumVector ξ) A_Q R + _ at htri
    have hh := htri.trans (add_le_add hproxyLinear hcomparisonLinear)
    exact hh.trans_eq (by unfold boundedProxyBothTargetsConstant; ring)
  have hproxyLinear' : rectangleError μ (sumVector ξ) A_Q R ≤
      boundedProxyBothTargetsConstant * rate := hproxyLinear.trans
    (mul_le_mul_of_nonneg_right (by unfold boundedProxyBothTargetsConstant; linarith) hr)
  have hone : max (rectangleError μ (sumVector ξ) A_S R) (rectangleError μ (sumVector ξ) A_Q R) ≤ 1 :=
    max_le (rectangleError_le_one μ (sumVector ξ) A_S R) (rectangleError_le_one μ (sumVector ξ) A_Q R)
  have hh := le_max_mul_min_of_le_one hr hone (max_le htrueLinear hproxyLinear')
  have hC : 1 ≤ boundedProxyBothTargetsConstant := by
    unfold boundedProxyBothTargetsConstant
    linarith [boundedProxyConstant_ge_two]
  simpa only [max_eq_right hC, rate] using hh

end
end RectangleCLT
