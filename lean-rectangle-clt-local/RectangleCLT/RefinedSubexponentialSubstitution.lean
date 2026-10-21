import RectangleCLT.RefinedSubexponentialRates

/-! Quantitative substitution of the actual truncated moments into the
combined proxy coefficients. The original proxy remains unchanged. -/

open MeasureTheory

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 K : ℝ}

theorem normalized_truncation_refinedProxyRate_le (h : SubexponentialHypotheses μ Y B4 K)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : LocalCovarianceHypotheses Q)
    {q : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ i, μ.real {ω | ‖Y i ω‖ ≤ 64 * K * truncationLog n p}ᶜ ≤ q)
    (hsmall : 2 * B4 * Real.sqrt q < 1 / 2) :
    let ξ := normalizedCenteredTruncation μ Y (64 * K * truncationLog n p)
      (truncationStandardDeviations μ Y (64 * K * truncationLog n p))
    refinedProxyCoefficientRate (4 * (64 * K * truncationLog n p) / Real.sqrt (n : ℝ))
      (gamma3 μ ξ) (gamma4 μ ξ)
      (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q)
      (dimensionLog p) (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q) ≤
      256 * refinedSubexponentialRate n B4 K Q +
        proxyCovarianceDiscrepancy (covariance μ (sumVector (sampleNormalizedObservations Y))) Q *
          dimensionLog p * gaussianComparisonCoefficient (fullCovarianceScale Q) (pairGap Q) +
        (4 * B4 * Real.sqrt q) * dimensionLog p / pairGap Q := by
  let u := 64 * K * truncationLog n p
  let ξ := normalizedCenteredTruncation μ Y u (truncationStandardDeviations μ Y u)
  let Δ := proxyCovarianceDiscrepancy
    (covariance μ (sumVector (sampleNormalizedObservations Y))) Q
  let L := dimensionLog p
  let c := pairGap Q
  let b := fullCovarianceScale Q
  let β3 := combinedThirdCoefficient b c (a3 Q)
  let β4 := combinedFourthCoefficient b c (a3 Q) (a4 Q)
  let β2 := gaussianComparisonCoefficient b c
  let sn := Real.sqrt (n : ℝ)
  let T3 := B4 * L * Real.sqrt L * β3 / sn
  let T4 := B4 * L / Real.sqrt c * β4 / sn
  let T0 := K * truncationLog n p * Real.sqrt L / (c * sn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
  have hs : 0 < sn := Real.sqrt_pos.mpr hnR
  have hc : 0 < c := hQ.pairGap_pos h.dimension_pos
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one h.dimension_pos)
  have hH : 0 ≤ truncationLog n p := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.sample_size_pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.dimension_pos
    exact zero_le_one.trans (subexponentialCutoffHeight_bounds hn1 hp1).1
  have hB : 0 ≤ B4 := zero_le_one.trans h.fourth_scale_ge_one
  have hK : 0 ≤ K := zero_le_one.trans h.tail_scale_ge_one
  have hβ3 : 0 ≤ β3 := combinedThirdCoefficient_nonneg hc (hQ.a3_pos h.dimension_pos)
  have hβ4 : 0 ≤ β4 := combinedFourthCoefficient_nonneg hc
    (hQ.a3_pos h.dimension_pos) hQ.a4_pos
  have hβ2 : 0 ≤ β2 := gaussianComparisonCoefficient_nonneg hc
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h3 : gamma3 μ ξ ≤ 8 * B4 / sn := h.normalized_truncation_gamma3 hq hu hprob hsmall
  have h4 : Real.sqrt (gamma4 μ ξ) ≤ 8 * B4 / sn :=
    h.normalized_truncation_sqrt_gamma4 hq hu hprob hsmall
  have hdis : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q ≤
      Δ + 4 * B4 * Real.sqrt q :=
    h.normalized_truncation_fixed_proxy_error Q hq hu hprob (by linarith)
  have hraw : refinedProxyCoefficientRate (4 * u / sn) (gamma3 μ ξ) (gamma4 μ ξ)
      (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q) L b c (a3 Q) (a4 Q) ≤
      (8 * B4 / sn) * L * Real.sqrt L * β3 +
        (8 * B4 / sn) * L / Real.sqrt c * β4 + (4 * u / sn) * Real.sqrt L / c +
          (Δ + 4 * B4 * Real.sqrt q) * L * β2 := by
    unfold refinedProxyCoefficientRate combinedCoefficientRate
    change _ ≤ _
    gcongr <;> assumption
  have heq : (8 * B4 / sn) * L * Real.sqrt L * β3 +
      (8 * B4 / sn) * L / Real.sqrt c * β4 + (4 * u / sn) * Real.sqrt L / c +
        (Δ + 4 * B4 * Real.sqrt q) * L * β2 =
      8 * T3 + 8 * T4 + 256 * T0 + Δ * L * β2 +
        (4 * B4 * Real.sqrt q) * L * β2 := by
    dsimp [T3, T4, T0, u]
    ring
  have hepsilon : (4 * B4 * Real.sqrt q) * L * β2 ≤
      (4 * B4 * Real.sqrt q) * L / c := by
    exact (mul_le_mul_of_nonneg_left gaussianComparisonCoefficient_le_pair
      (show 0 ≤ (4 * B4 * Real.sqrt q) * L by positivity)).trans_eq (by ring)
  have hT3 : 0 ≤ T3 := by dsimp [T3]; positivity
  have hT4 : 0 ≤ T4 := by dsimp [T4]; positivity
  have hE : refinedSubexponentialRate n B4 K Q = T3 + T4 + T0 := rfl
  change refinedProxyCoefficientRate (4 * u / sn) (gamma3 μ ξ) (gamma4 μ ξ)
    (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q) L b c (a3 Q) (a4 Q) ≤ _
  rw [hE]
  exact (hraw.trans_eq heq).trans (by
    change _ ≤ 256 * (T3 + T4 + T0) + Δ * L * β2 + (4 * B4 * Real.sqrt q) * L / c
    nlinarith only [hT3, hT4, hepsilon])

end

end RectangleCLT
