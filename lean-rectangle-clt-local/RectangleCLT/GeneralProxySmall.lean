import RectangleCLT.GeneralMain
import RectangleCLT.RefinedProxyStatement

/-! The bounded small-discrepancy branch of the full general proxy theorem.
All global/local/short-scale alternatives come from the proved unequal
master estimate. No local eigenvalue positivity is imposed. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

theorem masterSecondCoefficient_le_comparison (L b c h : ℝ) :
    masterSecondCoefficient L b c h ≤
      Real.sqrt L * gaussianComparisonCoefficient b c := by
  unfold masterSecondCoefficient optionalMin gaussianComparisonCoefficient
  split_ifs with hb
  · rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg L)]
    simpa only [div_eq_mul_inv, one_mul] using
      (min_le_min (le_rfl : Real.sqrt L / b ≤ Real.sqrt L / b)
        (min_le_left (Real.sqrt L / c) (1 / h)))
  · simpa only [div_eq_mul_inv, one_mul] using
      (min_le_left (Real.sqrt L / c) (1 / h))

def generalProxySmallConstant : ℝ := max 1 (24 * unequalMasterConstant)

theorem generalProxySmallConstant_ge_one : 1 ≤ generalProxySmallConstant :=
  le_max_left _ _

theorem generalProxySmallConstant_ge_master :
    unequalMasterConstant ≤ generalProxySmallConstant := by
  have hm := unequalMasterConstant_ge_one
  have hlarge := le_max_right (1 : ℝ) (24 * unequalMasterConstant)
  unfold generalProxySmallConstant
  linarith

/-- The exact general proxy rate for a bounded sum, when the covariance
discrepancy is at most half the proxy pair gap. -/
theorem generalProxyBounded_small
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose))
    (hsmall : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ))
      (A * A.transpose) ≤ pairGap (A * A.transpose) / 2) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ generalProxySmallConstant * min 1
      (generalProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
        (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A * A.transpose))
        (dimensionLog p) (fullCovarianceScale (A * A.transpose))
        (pairGap (A * A.transpose)) (a3 (A * A.transpose)) (a4 (A * A.transpose))) := by
  let Q := A * A.transpose
  let S := covariance μ (sumVector ξ)
  let L := dimensionLog p
  let c := pairGap Q
  let b := fullCovarianceScale Q
  let Δ := proxyCovarianceDiscrepancy S Q
  let D := Δ * L * gaussianComparisonCoefficient b c
  let M := unequalMasterConstant
  let K := generalProxySmallConstant
  let r := generalCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) L b c (a3 Q) (a4 Q)
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hΔ : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hΔ hL0)
    (gaussianComparisonCoefficient_nonneg hc)
  have hM : 0 ≤ M := zero_le_one.trans unequalMasterConstant_ge_one
  have hK : 0 ≤ K := zero_le_one.trans generalProxySmallConstant_ge_one
  have hr : 0 ≤ r := generalCoefficientRate_nonneg hdata.delta_nonneg
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) hL0 hc
  have hgap : c / 2 ≤ pairGap S := by
    have hh := gaussianComparisonCovariance_pairGap_ge_half S Q hsmall
      (t := 0) (by norm_num) (by norm_num)
    simpa only [gaussianComparisonCovariance_zero] using hh
  have hcstar : 0 < min (pairGap S) c :=
    (half_pos hc).trans_le (le_min hgap (by linarith only [hc]))
  have hunit' : rectangleError μ (sumVector ξ) A R - M * D ≤ 1 := by
    have he := rectangleError_le_one μ (sumVector ξ) A R
    linarith [mul_nonneg hM hD]
  have hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      rectangleError μ (sumVector ξ) A R - M * D ≤ 2 * M * Real.sqrt L *
        (gamma3 μ ξ * masterThirdCoefficient L b c (a3 Q) h +
          gamma4 μ ξ * masterFourthCoefficient L b c (a3 Q) (a4 Q) h + h / c) := by
    intro h hband
    have hh : 0 < h := by linarith only [hband, hdata.delta_pos hp hunit]
    have hcs : c / 2 ≤ min (pairGap S) c :=
      le_min hgap (by linarith only [hc])
    have hden : 1 / min (pairGap S) c ≤ 2 / c := by
      apply (div_le_div_iff₀ hcstar hc).mpr
      linarith only [hcs]
    have hend : Real.sqrt L * (h / min (pairGap S) c) ≤
        2 * Real.sqrt L * (h / c) := by
      have hh' := mul_le_mul_of_nonneg_left hden (mul_nonneg (Real.sqrt_nonneg L) hh.le)
      convert hh' using 1 <;> ring
    have hquad : Real.sqrt L * (Δ * masterSecondCoefficient L b c h) ≤ D := by
      have hcoef := masterSecondCoefficient_le_comparison L b c h
      have hb := mul_le_mul_of_nonneg_left hcoef (mul_nonneg (Real.sqrt_nonneg L) hΔ)
      calc
        _ ≤ Real.sqrt L * Δ * (Real.sqrt L * gaussianComparisonCoefficient b c) := by
          convert hb using 1 <;> ring
        _ = D := by
          calc
            _ = Δ * (Real.sqrt L) ^ 2 * gaussianComparisonCoefficient b c := by ring
            _ = D := by rw [Real.sq_sqrt hL0]
    have h3 : 0 ≤ Real.sqrt L *
        (gamma3 μ ξ * masterThirdCoefficient L b c (a3 Q) h) :=
      mul_nonneg (Real.sqrt_nonneg L)
        (mul_nonneg (gamma3_nonneg μ ξ) (masterThirdCoefficient_nonneg hL0 hc hh))
    have h4 : 0 ≤ Real.sqrt L *
        (gamma4 μ ξ * masterFourthCoefficient L b c (a3 Q) (a4 Q) h) :=
      mul_nonneg (Real.sqrt_nonneg L)
        (mul_nonneg (gamma4_nonneg μ ξ) (masterFourthCoefficient_nonneg hL0 hc hh))
    have hm := unequalMasterEstimate μ p n hp hn ξ δ A hdata hunit hdiag hcstar R h hband
    have hm' : rectangleError μ (sumVector ξ) A R ≤ M *
        (Real.sqrt L * (Δ * masterSecondCoefficient L b c h) +
          Real.sqrt L * (gamma3 μ ξ * masterThirdCoefficient L b c (a3 Q) h) +
          Real.sqrt L * (gamma4 μ ξ * masterFourthCoefficient L b c (a3 Q) (a4 Q) h) +
          Real.sqrt L * (h / min (pairGap S) c)) := by
      convert hm using 1 <;>
        dsimp [unequalMasterDataRate, unequalMasterRate, M, L, b, c, Δ, S, Q] <;> ring
    have hraw := hm'.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add_right (add_le_add_right hquad _) _) hend) hM)
    have hpos := mul_nonneg hM (add_nonneg h3 h4)
    nlinarith only [hraw, hpos]
  have hb := general_rate_of_master (hdata.delta_pos hp hunit)
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) hL hc
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) hunit' hmaster
  have hb' : rectangleError μ (sumVector ξ) A R - M * D ≤ K * r := by
    have hh := hb.trans (mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) r)
      (show 0 ≤ max 1 (12 * (2 * M)) by positivity))
    convert hh using 1 <;> dsimp [K, M, generalProxySmallConstant, r] <;> ring
  have hlinear : rectangleError μ (sumVector ξ) A R ≤ K * (r + D) := by
    have hMD := mul_le_mul_of_nonneg_right generalProxySmallConstant_ge_master hD
    change M * D ≤ K * D at hMD
    nlinarith only [hb', hMD]
  have hout := le_max_mul_min_of_le_one (add_nonneg hr hD)
    (rectangleError_le_one μ (sumVector ξ) A R) hlinear
  rw [max_eq_right generalProxySmallConstant_ge_one] at hout
  exact hout

end

end RectangleCLT
