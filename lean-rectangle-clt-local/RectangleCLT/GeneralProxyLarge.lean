import RectangleCLT.RefinedProxyRegularizedData
import RectangleCLT.RefinedProxyRegularizedGeometry
import RectangleCLT.RefinedProxyUnscaling
import RectangleCLT.GeneralGaussianComponentMain
import RectangleCLT.GaussianComparisonFull

/-! The large-discrepancy branch uses actual isotropic Gaussian noise.
The regularized observation covariance is uniformly positive, while every
coefficient in the final rate is computed from the fixed proxy. -/

open MeasureTheory
universe u
namespace RectangleCLT
noncomputable section

def generalProxyNoiseConstant : ℝ := 4*1073741824

def generalProxyLargeConstant : ℝ :=
  2*generalCLTConstant + 5*generalProxyNoiseConstant + gaussianComparisonFullConstant

theorem generalProxyLargeConstant_ge_one : 1 ≤ generalProxyLargeConstant := by
  have hg := generalCLTConstant_ge_one
  have hc := gaussianComparisonFullConstant_ge_one
  unfold generalProxyLargeConstant generalProxyNoiseConstant
  linarith

theorem regularized_factor_covariance {p : ℕ}
    (A D : Matrix (Fin p) (Fin p) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hD : D*D.transpose=refinedProxyRegularizedCovariance (A*A.transpose) c) :
    D*D.transpose = (Real.sqrt (1+c))⁻¹^2 • (A*A.transpose) +
      ((Real.sqrt (1+c))⁻¹*Real.sqrt c)^2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hn : (Real.sqrt (1+c))⁻¹^2=(1+c)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by linarith)]
  rw [hD, refinedProxyRegularizedCovariance, mul_pow, hn, Real.sq_sqrt hc,
    smul_add, smul_smul]

/-- The large-discrepancy branch, for both Gaussian targets. The true
covariance is allowed to be singular and to have zero pair gap. -/
theorem generalProxyBounded_large
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (A_S A_Q : Matrix (Fin p) (Fin p) ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hdiag : ∀ j, (A_Q*A_Q.transpose) j j=1)
    (hc : 0 < pairGap (A_Q*A_Q.transpose))
    (hfactor : A_S*A_S.transpose=covariance μ (sumVector ξ))
    (hlarge : pairGap (A_Q*A_Q.transpose)/2 ≤
      proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A_Q*A_Q.transpose))
    (R : Rect p) :
    max (rectangleError μ (sumVector ξ) A_S R) (rectangleError μ (sumVector ξ) A_Q R) ≤
      generalProxyLargeConstant * min 1
        (generalProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
          (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A_Q*A_Q.transpose))
          (dimensionLog p) (fullCovarianceScale (A_Q*A_Q.transpose))
          (pairGap (A_Q*A_Q.transpose)) (a3 (A_Q*A_Q.transpose)) (a4 (A_Q*A_Q.transpose))) := by
  let Q := A_Q*A_Q.transpose
  let S := covariance μ (sumVector ξ)
  let c := pairGap Q
  let b := fullCovarianceScale Q
  let L := dimensionLog p
  let Δ := proxyCovarianceDiscrepancy S Q
  let r := generalCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) L b c (a3 Q) (a4 Q)
  let d := Δ*L*gaussianComparisonCoefficient b c
  let V := refinedProxyRegularizedArray ξ c
  let G := refinedProxyRegularizedGaussian (Ω := Ω) (p := p) c
  let ν := μ.prod (standardGaussian p)
  let t := refinedProxyNormalization c
  let δ' := t*δ
  let T := refinedProxyRegularizedCovariance S c
  have hc0 : 0 < c := hc
  have hc1 : c ≤ 1 := pairGap_le_one Q
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hQ : Q.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A_Q
  have hS : S.PosSemidef := hdata.covariance_posSemidef
  have hT : T.PosSemidef := refinedProxyRegularizedCovariance_posSemidef hS hc0.le
  obtain ⟨D,hD⟩ := gaussianComparison_factor_exists hT
  have hTdiag : ∀ j, T j j=1 := refinedProxyRegularizedCovariance_unitDiagonal hunit hc0.le
  have hTgap : 0 < pairGap T := (half_pos hc0).trans_le
    (refinedProxyRegularizedCovariance_half_le_pairGap hp hS hunit hc0 hc1)
  have hASdiag : ∀j,(A_S*A_S.transpose) j j=1 := by intro j; rw [hfactor]; exact hunit j
  have hbc : b^2 ≤ c := by
    rw [fullCovarianceScale_sq (by omega) hQ]
    exact fullEigenvalue_le_pairGap (by omega) hQ hdiag
  have ha4 : 0 ≤ a4 Q := a4_nonneg (by omega) hQ
  have ha43 : a4 Q ≤ a3 Q := a4_le_a3 (by omega) hQ
  have ha3c : a3 Q ≤ c := a3_le_pairGap (by omega) hQ hdiag
  have hδ : 0 ≤ δ := hdata.delta_nonneg
  have hr : 0 ≤ r := generalCoefficientRate_nonneg hδ
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) hL hc0
  have hd : 0 ≤ d := mul_nonneg
    (mul_nonneg (proxyCovarianceDiscrepancy_nonneg S Q) hL)
    (gaussianComparisonCoefficient_nonneg hc0)
  have hnoise : Real.sqrt c*L ≤ 2*d :=
    large_discrepancy_regularization_cost hL hc0 hc1 (Real.sqrt_nonneg _) hbc hlarge
  have henv : δ*Real.sqrt L ≤ r := by
    have hthird := generalThirdRate_nonneg (b := b) (a₃ := a3 Q) (gamma3_nonneg μ ξ) hL hc0
    have hfourth := generalFourthRate_nonneg (b := b) (a₃ := a3 Q) (a₄ := a4 Q)
      (gamma4_nonneg μ ξ) hL hc0
    have he : δ*Real.sqrt L ≤ δ*Real.sqrt L/c :=
      (le_div_iff₀ hc0).mpr (by nlinarith [mul_nonneg hδ (Real.sqrt_nonneg L)])
    dsimp [r, generalCoefficientRate]
    linarith
  -- The actual product data, exact covariance and moment normalization
  -- are supplied by the independent regularization module.
  have hreg := refinedProxyRegularized_proxyHypotheses μ ξ hdata hc0.le
  have hregcov := refinedProxyRegularized_covariance μ ξ hdata hc0.le
  have hregunit : ∀j,covariance ν (sumWithGaussian V G) j j=1 := by
    rw [hregcov]
    exact hTdiag
  have hreggap : 0 < pairGap (covariance ν (sumWithGaussian V G)) := by
    rw [hregcov]
    exact hTgap
  have hregfactor : D*D.transpose=covariance ν (sumWithGaussian V G) := by
    rw [hregcov]
    exact hD
  have ha : 0 < Real.sqrt (1+c) := Real.sqrt_pos.mpr (by linarith)
  let R' := R.preimageCoordinateScale (fun _ => Real.sqrt (1+c)) (fun _ => ha)
  have happrox := generalGaussianRectangleCLT ν p n hp hn V G δ'
    (refinedProxyRegularizedFactor p c) D hreg hregunit hreggap hregfactor R'
  have ht0 : 0 ≤ t := (refinedProxyNormalization_pos hc0.le).le
  have ht1 : t ≤ 1 := refinedProxyNormalization_le_one hc0.le
  have hδ' : δ' ≤ δ := by dsimp [δ']; nlinarith
  have hγ3 : gamma3 ν V ≤ gamma3 μ ξ := by
    rw [refinedProxyRegularizedArray_gamma3 μ ξ hc0.le]
    have ht3 : t^3 ≤ 1 := pow_le_one₀ ht0 ht1
    exact (mul_le_mul_of_nonneg_right ht3 (gamma3_nonneg μ ξ)).trans_eq (one_mul _)
  have hγ4 : gamma4 ν V ≤ gamma4 μ ξ := by
    rw [refinedProxyRegularizedArray_gamma4 μ ξ c]
    have ht4 : t^4 ≤ 1 := pow_le_one₀ ht0 ht1
    exact (mul_le_mul_of_nonneg_right ht4 (gamma4_nonneg μ ξ)).trans_eq (one_mul _)
  have hmon : generalBoundedRate ν V δ' T ≤ generalBoundedRate μ ξ δ T :=
    generalCoefficientRate_mono_all hδ' (gamma3_nonneg ν V) hγ3
      (gamma4_nonneg ν V) hγ4 hL hTgap
  have hrate : generalBoundedRate μ ξ δ T ≤ 2*r :=
    generalCoefficientRate_regularized hδ (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ)
      hL hc0 hc1 (Real.sqrt_nonneg _) hbc (ha4.trans ha43) ha3c ha4 (ha43.trans ha3c)
      (refinedProxyRegularizedCovariance_fullScale_pos hp hS hc0 hc1)
      (refinedProxyRegularizedCovariance_half_le_fullScale_sq hp hS hc0 hc1)
      (refinedProxyRegularizedCovariance_half_le_pairGap hp hS hunit hc0 hc1)
  have hreglinear : rectangleError ν (sumWithGaussian V G) D R' ≤
      generalCLTConstant*(2*r) := by
    rw [hregcov] at happrox
    exact happrox.trans (mul_le_mul_of_nonneg_left
      ((min_le_right 1 _).trans (hmon.trans hrate))
      (zero_le_one.trans generalCLTConstant_ge_one))
  have hsum : sumWithGaussian V G =
      fun z : Ω × Vector p => (Real.sqrt (1+c))⁻¹ •
        (sumVector ξ z.1+Real.sqrt c • z.2) := by
    funext z
    exact sumWithGaussian_refinedProxyRegularized ξ c z
  rw [hsum] at hreglinear
  have hDc : D*D.transpose=refinedProxyRegularizedCovariance (A_S*A_S.transpose) c := by
    rw [hfactor]
    exact hD
  have htransfer := bounded_regularized_error_transfer μ ξ hdata hp hunit A_S D hASdiag
    ha hc0.le (regularized_factor_covariance A_S D hc0.le hDc) R
  have htrue : rectangleError μ (sumVector ξ) A_S R ≤
      (2*generalCLTConstant+5*generalProxyNoiseConstant)*(r+d) := by
    have hb := htransfer.trans (add_le_add_right hreglinear _)
    have hN : 0 ≤ generalProxyNoiseConstant := by norm_num [generalProxyNoiseConstant]
    change rectangleError μ (sumVector ξ) A_S R ≤
      generalCLTConstant*(2*r)+generalProxyNoiseConstant*
        (2*Real.sqrt c*L+δ*Real.sqrt L) at hb
    have hn := mul_le_mul_of_nonneg_left (by nlinarith only [hnoise, henv] :
      2*Real.sqrt c*L+δ*Real.sqrt L ≤ 4*d+r) hN
    have hCr := mul_nonneg (zero_le_one.trans generalCLTConstant_ge_one) hd
    have hNr := mul_nonneg hN hr
    have hNd := mul_nonneg hN hd
    nlinarith only [hb, hn, hCr, hNr, hNd]
  have hcomparison := gaussianComparisonFull hp A_S A_Q hASdiag hdiag hc R
  rw [hfactor] at hcomparison
  have hcomparisonlinear : |(gaussianLaw A_S).real R.carrier-(gaussianLaw A_Q).real R.carrier| ≤
      gaussianComparisonFullConstant*d := hcomparison.trans
    (mul_le_mul_of_nonneg_left (min_le_right 1 d)
      (zero_le_one.trans gaussianComparisonFullConstant_ge_one))
  have htrue' : rectangleError μ (sumVector ξ) A_S R ≤ generalProxyLargeConstant*(r+d) :=
    htrue.trans (mul_le_mul_of_nonneg_right
      (by dsimp [generalProxyLargeConstant]; linarith [gaussianComparisonFullConstant_ge_one])
      (add_nonneg hr hd))
  have hproxy : rectangleError μ (sumVector ξ) A_Q R ≤ generalProxyLargeConstant*(r+d) := by
    have ht := abs_sub_le (μ.real (sumVector ξ ⁻¹' R.carrier))
      ((gaussianLaw A_S).real R.carrier) ((gaussianLaw A_Q).real R.carrier)
    change rectangleError μ (sumVector ξ) A_Q R ≤
      rectangleError μ (sumVector ξ) A_S R+_ at ht
    have hb := ht.trans (add_le_add htrue hcomparisonlinear)
    have hCr := mul_nonneg (zero_le_one.trans gaussianComparisonFullConstant_ge_one) hr
    dsimp [generalProxyLargeConstant]
    nlinarith only [hb, hCr]
  have hone := max_le (rectangleError_le_one μ (sumVector ξ) A_S R)
    (rectangleError_le_one μ (sumVector ξ) A_Q R)
  have hout := le_max_mul_min_of_le_one (add_nonneg hr hd) hone (max_le htrue' hproxy)
  rw [max_eq_right generalProxyLargeConstant_ge_one] at hout
  exact hout

end
end RectangleCLT
