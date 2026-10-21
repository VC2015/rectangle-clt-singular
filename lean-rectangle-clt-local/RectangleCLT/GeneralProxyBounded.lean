import RectangleCLT.GeneralProxyLarge
import RectangleCLT.GeneralProxySmall
import RectangleCLT.GeneralProxyClosure

/-! The bounded general proxy theorem combines the small-discrepancy
unequal-covariance master estimate with isotropic regularization for the
remaining covariances. Its hypotheses concern the actual bounded data and
the fixed proxy, and its conclusion controls both Gaussian targets. -/

open MeasureTheory
universe u
namespace RectangleCLT
noncomputable section

def generalProxyConstant : ℝ :=
  generalProxySmallConstant + generalProxyLargeConstant + gaussianComparisonFullConstant

theorem generalProxyConstant_ge_one : 1 ≤ generalProxyConstant := by
  have hs := generalProxySmallConstant_ge_one
  have hl := generalProxyLargeConstant_ge_one
  have hg := gaussianComparisonFullConstant_ge_one
  unfold generalProxyConstant
  linarith

/-- Proposition 4 for bounded observations. In particular the actual
covariance need not have any positive local or global eigenvalue. -/
theorem generalBoundedCovarianceProxyCLT :
    GeneralBoundedCovarianceProxyCLT.{u} generalProxyConstant := by
  intro Ω _ μ _ p n hp hn ξ δ A_S A_Q hdata hunit hdiag hc hfactor R
  let Q := A_Q*A_Q.transpose
  let L := dimensionLog p
  let c := pairGap Q
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q
  let r := generalCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) L
    (fullCovarianceScale Q) c (a3 Q) (a4 Q)
  let d := Δ*L*gaussianComparisonCoefficient (fullCovarianceScale Q) c
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hr : 0 ≤ r := generalCoefficientRate_nonneg hdata.delta_nonneg
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) hL hc
  have hd : 0 ≤ d := mul_nonneg
    (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _) hL)
    (gaussianComparisonCoefficient_nonneg hc)
  have hrate : 0 ≤ min 1 (r+d) := le_min zero_le_one (add_nonneg hr hd)
  change max (rectangleError μ (sumVector ξ) A_S R) (rectangleError μ (sumVector ξ) A_Q R) ≤
    generalProxyConstant*min 1 (r+d)
  by_cases hsmall : Δ ≤ c/2
  · have hproxy := generalProxyBounded_small μ hp hn ξ δ A_Q hdata hunit hdiag hc hsmall R
    have hproxylinear : rectangleError μ (sumVector ξ) A_Q R ≤
        generalProxySmallConstant*(r+d) := hproxy.trans
      (mul_le_mul_of_nonneg_left (min_le_right 1 (r+d))
        (zero_le_one.trans generalProxySmallConstant_ge_one))
    have hASdiag : ∀j,(A_S*A_S.transpose) j j=1 := by
      intro j
      rw [hfactor]
      exact hunit j
    have hcomparison := gaussianComparisonFull hp A_S A_Q hASdiag hdiag hc R
    rw [hfactor] at hcomparison
    have hcomparisonlinear :
        |(gaussianLaw A_S).real R.carrier-(gaussianLaw A_Q).real R.carrier| ≤
          gaussianComparisonFullConstant*(r+d) := by
      apply hcomparison.trans
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans gaussianComparisonFullConstant_ge_one)
      exact (min_le_right 1 d).trans (by linarith only [hr])
    have htrue : rectangleError μ (sumVector ξ) A_S R ≤
        generalProxyConstant*(r+d) := by
      have ht := abs_sub_le (μ.real (sumVector ξ ⁻¹' R.carrier))
        ((gaussianLaw A_Q).real R.carrier) ((gaussianLaw A_S).real R.carrier)
      rw [abs_sub_comm ((gaussianLaw A_Q).real R.carrier)] at ht
      change rectangleError μ (sumVector ξ) A_S R ≤
        rectangleError μ (sumVector ξ) A_Q R+_ at ht
      have hh := ht.trans (add_le_add hproxylinear hcomparisonlinear)
      have hnon := mul_nonneg (zero_le_one.trans generalProxyLargeConstant_ge_one)
        (add_nonneg hr hd)
      dsimp [generalProxyConstant]
      nlinarith only [hh, hnon]
    have hproxy' : rectangleError μ (sumVector ξ) A_Q R ≤
        generalProxyConstant*(r+d) := hproxylinear.trans
      (mul_le_mul_of_nonneg_right (by
        unfold generalProxyConstant
        linarith [generalProxyLargeConstant_ge_one, gaussianComparisonFullConstant_ge_one])
        (add_nonneg hr hd))
    have hone := max_le (rectangleError_le_one μ (sumVector ξ) A_S R)
      (rectangleError_le_one μ (sumVector ξ) A_Q R)
    have hout := le_max_mul_min_of_le_one (add_nonneg hr hd) hone (max_le htrue hproxy')
    simpa only [max_eq_right generalProxyConstant_ge_one] using hout
  · have hlarge : c/2 ≤ Δ := le_of_lt (lt_of_not_ge hsmall)
    have hb := generalProxyBounded_large μ hp hn ξ δ A_S A_Q hdata hunit hdiag hc hfactor hlarge R
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      unfold generalProxyConstant
      linarith [generalProxySmallConstant_ge_one, gaussianComparisonFullConstant_ge_one]) hrate)

end
end RectangleCLT
