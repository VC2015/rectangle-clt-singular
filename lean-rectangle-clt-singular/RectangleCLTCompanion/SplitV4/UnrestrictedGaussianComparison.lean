import RectangleCLT.GaussianComparisonLocal
import RectangleCLT.GaussianFourthVarianceBounds
import RectangleCLTCompanion.GaussianConcentration
import RectangleCLTCompanion.SplitV4.TimeWeights
import RectangleCLTCompanion.SplitV4.Smoothing
import RectangleCLTCompanion.SubexponentialBounded
import RectangleCLTCompanion.SplitV4.GaussianEndpointSmoothing

/-!
Unrestricted Gaussian comparison for Appendix E. The smooth interpolation
uses only the unit marginal variances of the reference Gaussian. Both
covariances may be singular, and the other Gaussian has no variance
normalization or positive spectral/gap hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def unrestrictedGaussianSmoothConstant : ℝ := 6 * Real.exp (3 / 2 : ℝ)

theorem unrestrictedGaussianSmoothConstant_pos : 0 < unrestrictedGaussianSmoothConstant := by
  unfold unrestrictedGaussianSmoothConstant
  positivity

/-- The reference Gaussian component supplies concentration along the
whole interpolation, even if the other endpoint is degenerate. -/
theorem gaussianComparison_expected_variance_le {p : ℕ}
    (hp : 1 ≤ p) (s : FaceSmoother p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ z, s.F (FaceSmoother.gaussianComparisonPoint t z) *
      (1 - s.F (FaceSmoother.gaussianComparisonPoint t z))
      ∂(gaussianLaw B).prod (gaussianLaw A)) ≤
        Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / (1 - t)) := by
  have hv : 0 < 1 - t := sub_pos.mpr ht1
  have hm : Measurable (FaceSmoother.gaussianComparisonPoint (p := p) t) :=
    (FaceSmoother.continuous_gaussianComparisonPoint t).measurable
  have hi := s.integrable_smallerEnvelope
    (FaceSmoother.gaussianComparisonPoint (p := p) t) hm
    (μ := (gaussianLaw B).prod (gaussianLaw A))
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _y : Vector p,
        Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / (1 - t))
        ∂gaussianLaw A := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      apply ae_of_all
      intro y
      let r := Real.sqrt t • y
      have hg : Measurable (fun x : Vector p => s.F (x + r) * (1 - s.F (x + r))) := by
        exact (s.continuous_F.measurable.comp (measurable_id.add measurable_const)).mul
          (measurable_const.sub (s.continuous_F.measurable.comp
            (measurable_id.add measurable_const)))
      change (∫ x, s.F (Real.sqrt (1 - t) • x + r) *
        (1 - s.F (Real.sqrt (1 - t) • x + r)) ∂gaussianLaw B) ≤ _
      rw [FaceSmoother.integral_gaussianLaw_smul B (Real.sqrt (1 - t)) _ hg]
      exact s.gaussian_expected_variance_le_of_diagonal hp _ hv
        (sqrt_smul_mul_transpose_diagonal B hB hv.le) r
    _ = _ := by simp

/-- The expected Hessian sum has the bandwidth-dependent bound needed
for unrestricted covariance comparison. There is no pair-gap denominator. -/
theorem gaussianComparison_second_sum_le {p : ℕ}
    (hp : 1 ≤ p) (s : FaceSmoother p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∑ j, ∑ k, |s.gaussianComparisonSecond B A t j k|) ≤
      (3 * Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p) / s.bandwidth) *
        gaussianTimeWeight t := by
  let ν := (gaussianLaw B).prod (gaussianLaw A)
  let W := FaceSmoother.gaussianComparisonPoint (p := p) t
  have hm : Measurable W := (FaceSmoother.continuous_gaussianComparisonPoint t).measurable
  have hv := s.integrable_smallerEnvelope W hm (μ := ν)
  have hsecond (j k : Fin p) : Integrable (fun z => s.mixedSecondDerivativeF (W z) j k) ν :=
    s.integrable_gaussianComparisonSecond B A t j k
  have hsum : Integrable (fun z => ∑ j, ∑ k, |s.mixedSecondDerivativeF (W z) j k|) ν :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (hsecond j k).abs))
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  calc
    _ ≤ ∑ j, ∑ k, ∫ z, |s.mixedSecondDerivativeF (W z) j k| ∂ν := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact abs_integral_le_integral_abs
    _ = ∫ z, ∑ j, ∑ k, |s.mixedSecondDerivativeF (W z) j k| ∂ν := by
      rw [integral_finset_sum Finset.univ (fun j _ =>
        integrable_finset_sum Finset.univ (fun k _ => (hsecond j k).abs))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finset_sum Finset.univ (fun k _ => (hsecond j k).abs)]
    _ ≤ ∫ z, (3 / s.bandwidth ^ 2) * (s.F (W z) * (1 - s.F (W z))) ∂ν := by
      apply integral_mono hsum (hv.const_mul _)
      intro z
      convert s.sum_abs_mixedSecondDerivativeF_le_variance (W z) using 1 <;> ring
    _ = (3 / s.bandwidth ^ 2) * ∫ z, s.F (W z) * (1 - s.F (W z)) ∂ν :=
      integral_const_mul _ _
    _ ≤ (3 / s.bandwidth ^ 2) *
        (Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / (1 - t))) :=
      mul_le_mul_of_nonneg_left (gaussianComparison_expected_variance_le hp s A B hB ht0 ht1)
        (div_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by
      rw [Real.sqrt_div hL]
      unfold gaussianTimeWeight
      field_simp [s.bandwidth_pos.ne', (Real.sqrt_pos.mpr (sub_pos.mpr ht1)).ne']
      ring

/-- The exact singular Gaussian interpolation derivative is controlled
by entrywise covariance discrepancy and the reference Gaussian component. -/
theorem unrestrictedGaussianComparison_derivative_le {p : ℕ}
    (hp : 1 ≤ p) (s : FaceSmoother p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    |(1 / 2 : ℝ) * ∑ j, ∑ k,
      ((A * A.transpose) j k - (B * B.transpose) j k) *
        s.gaussianComparisonSecond B A t j k| ≤
      (3 * Real.exp (3 / 2 : ℝ) *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          Real.sqrt (dimensionLog p) / s.bandwidth) * gaussianTimeWeight t := by
  let d := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  have hd : 0 ≤ d := proxyCovarianceDiscrepancy_nonneg _ _
  have hs : 0 ≤ ∑ j, ∑ k, |s.gaussianComparisonSecond B A t j k| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ j, ∑ k,
        |((A * A.transpose) j k - (B * B.transpose) j k) *
          s.gaussianComparisonSecond B A t j k| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 / 2 : ℝ) * (d * ∑ j, ∑ k, |s.gaussianComparisonSecond B A t j k|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_entry_sub_le_proxyCovarianceDiscrepancy _ _ j k) (abs_nonneg _)
    _ ≤ d * ∑ j, ∑ k, |s.gaussianComparisonSecond B A t j k| := by
      nlinarith [mul_nonneg hd hs]
    _ ≤ d * ((3 * Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p) / s.bandwidth) *
        gaussianTimeWeight t) :=
      mul_le_mul_of_nonneg_left (gaussianComparison_second_sum_le hp s A B hB ht0.le ht1) hd
    _ = _ := by dsimp [d]; ring

/-- A genuine smooth Gaussian comparison with no desired analytic estimate
as a hypothesis. All integrability and endpoint limits are proved inputs. -/
theorem unrestrictedGaussianComparison_smooth_le {p : ℕ}
    (hp : 1 ≤ p) (s : FaceSmoother p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1) :
    |(∫ x, s.F x ∂gaussianLaw A) - (∫ y, s.F y ∂gaussianLaw B)| ≤
      unrestrictedGaussianSmoothConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          Real.sqrt (dimensionLog p) / s.bandwidth := by
  let K := 3 * Real.exp (3 / 2 : ℝ) *
    proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
      Real.sqrt (dimensionLog p) / s.bandwidth
  have hi : IntegrableOn (fun t => K * gaussianTimeWeight t) (Icc (0 : ℝ) 1) := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_gaussianTimeWeight.const_mul K)
  have hh := abs_sub_le_integral_of_derivative_bound
    (s.continuous_gaussianComparisonExpectation B A).continuousOn
    (fun t ht => s.hasDerivAt_gaussianComparisonExpectation B A ht.1 ht.2) hi
    (fun t ht => unrestrictedGaussianComparison_derivative_le hp s A B hB ht.1 ht.2)
  rw [s.gaussianComparisonExpectation_one, s.gaussianComparisonExpectation_zero,
    intervalIntegral.integral_const_mul, integral_gaussianTimeWeight] at hh
  convert hh using 1
  unfold unrestrictedGaussianSmoothConstant K
  ring

/-- The actual supremum of smooth comparison errors is bounded by the
proved Gaussian interpolation estimate, uniformly over all thresholds. -/
theorem unrestrictedGaussianComparison_smoothingDiscrepancy_le {p : ℕ}
    (hp : 1 ≤ p) (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1) (h : ℝ) (hh : 0 < h) :
    smoothingDiscrepancy (gaussianLaw A) id B h hh ≤
      unrestrictedGaussianSmoothConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          Real.sqrt (dimensionLog p) / h := by
  apply (smoothingDiscrepancy_le_iff (gaussianLaw A) id measurable_id B h hh _).mpr
  intro lo hi
  simpa only [id_eq, FaceSmoother.closedBox] using
    unrestrictedGaussianComparison_smooth_le hp (FaceSmoother.closedBox lo hi h hh) A B hB

/-- Zero entrywise covariance discrepancy means equality of the actual
Gaussian laws, including singular factors. -/
theorem gaussianLaw_eq_of_zero_discrepancy {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hz : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) = 0) :
    gaussianLaw A = gaussianLaw B := by
  apply gaussianLaw_eq_of_factor_covariance
  ext j k
  have hb := abs_entry_sub_le_proxyCovarianceDiscrepancy
    (A * A.transpose) (B * B.transpose) j k
  rw [hz] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))

theorem gaussianRectangleDistance_eq_zero_of_zero_discrepancy {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hz : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) = 0) :
    rectangleDistance (gaussianLaw A) id B = 0 := by
  apply le_antisymm _ (rectangleDistance_nonneg _ _ _)
  apply rectangleDistance_le
  intro R
  simp only [rectangleError, Set.preimage_id, gaussianLaw_eq_of_zero_discrepancy A B hz,
    sub_self, abs_zero, le_refl]

/-- Positive marginal standardization amplifies entrywise covariance
discrepancy by at most the reciprocal squared lower standard deviation. -/
theorem standardizedGaussian_discrepancy_le {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (d : Vector p) {b : ℝ}
    (hb : 0 < b) (hd : ∀ j, b ≤ d j) :
    proxyCovarianceDiscrepancy
      (scaledFactor (fun j => (d j)⁻¹) A * (scaledFactor (fun j => (d j)⁻¹) A).transpose)
      (scaledFactor (fun j => (d j)⁻¹) B * (scaledFactor (fun j => (d j)⁻¹) B).transpose) ≤
      proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) / b ^ 2 := by
  have hdpos (j : Fin p) : 0 < d j := hb.trans_le (hd j)
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  unfold proxyCovarianceDiscrepancy
  apply (Finset.fold_max_le _).mpr
  refine ⟨div_nonneg (proxyCovarianceDiscrepancy_nonneg _ _) hb2.le, ?_⟩
  intro jk _
  rcases jk with ⟨j, k⟩
  rw [scaledFactor_gram, scaledFactor_gram]
  have hprod : b ^ 2 ≤ d j * d k := by
    simpa only [pow_two] using mul_le_mul (hd j) (hd k) hb.le (hdpos j).le
  have heq : (d j)⁻¹ * (d k)⁻¹ * (A * A.transpose) j k -
      (d j)⁻¹ * (d k)⁻¹ * (B * B.transpose) j k =
      ((A * A.transpose) j k - (B * B.transpose) j k) / (d j * d k) := by
    field_simp [(hdpos j).ne', (hdpos k).ne']
  rw [heq, abs_div, abs_of_pos (mul_pos (hdpos j) (hdpos k))]
  exact (div_le_div_of_nonneg_right
    (abs_entry_sub_le_proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) j k)
    (mul_pos (hdpos j) (hdpos k)).le).trans
      (div_le_div_of_nonneg_left (proxyCovarianceDiscrepancy_nonneg _ _) hb2 hprod)

/-- Standardizing an actual Gaussian observation law is exactly the
Gaussian law with its factor rows scaled, for every endpoint convention. -/
theorem gaussianRectangleError_diagonalScale {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (d : Vector p) (R : Rect p) :
    rectangleError (gaussianLaw A) (diagonalScale d) B R =
      rectangleError (gaussianLaw (scaledFactor d A)) id B R := by
  unfold rectangleError
  rw [← gaussianLaw_map_diagonalScale d A]
  simp only [Set.preimage_id, Measure.real,
    Measure.map_apply (measurable_diagonalScale d) R.measurableSet_carrier]

private theorem optimizedGaussianBandwidth (a d L : ℝ) (hd : 0 < d) (hL : 0 < L) :
    a * d * Real.sqrt L / (Real.sqrt d / Real.sqrt L) +
      (Real.sqrt d / Real.sqrt L) * Real.sqrt L * L =
      (a + 1) * L * Real.sqrt d := by
  have hx : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hy : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  field_simp [hx, hy]
  ring_nf
  rw [Real.sq_sqrt hd.le, Real.sq_sqrt hL.le]

/-- One universal constant is fixed before dimensions and Gaussian models. -/
def unrestrictedGaussianComparisonConstant : ℝ :=
  max 1 (gaussianSmoothingConstant * (unrestrictedGaussianSmoothConstant + 1))

theorem one_le_unrestrictedGaussianComparisonConstant :
    1 ≤ unrestrictedGaussianComparisonConstant := le_max_left _ _

/-- The Appendix E Gaussian comparison with unit reference marginal
variances and completely unrestricted other covariance. This is the actual
full rectangle distance, saturated by one. Both factors may be singular. -/
theorem unrestrictedGaussianComparison {p : ℕ}
    (hp : 1 ≤ p) (A B : Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ j, (B * B.transpose) j j = 1) :
    rectangleDistance (gaussianLaw A) id B ≤
      unrestrictedGaussianComparisonConstant * min 1
        (dimensionLog p * Real.sqrt
          (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose))) := by
  let d := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  let L := dimensionLog p
  have hd : 0 ≤ d := proxyCovarianceDiscrepancy_nonneg _ _
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  change rectangleDistance (gaussianLaw A) id B ≤
    unrestrictedGaussianComparisonConstant * min 1 (L * Real.sqrt d)
  by_cases hz : d = 0
  · rw [gaussianRectangleDistance_eq_zero_of_zero_discrepancy A B hz, hz]
    simp
  have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
  let h := Real.sqrt d / Real.sqrt L
  have hh : 0 < h := div_pos (Real.sqrt_pos.mpr hdp) (Real.sqrt_pos.mpr hL)
  have hc : 0 ≤ gaussianSmoothingConstant := by linarith [gaussianSmoothingConstant_ge_two]
  have hg := unrestrictedGaussianComparison_smoothingDiscrepancy_le hp A B hB h hh
  have hr := (gaussianEndpointSmoothing hp (gaussianLaw A) id measurable_id B hB h hh).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hg _) hc)
  change rectangleDistance (gaussianLaw A) id B ≤ gaussianSmoothingConstant *
    (unrestrictedGaussianSmoothConstant * d * Real.sqrt L / (Real.sqrt d / Real.sqrt L) +
      (Real.sqrt d / Real.sqrt L) * Real.sqrt L * L) at hr
  rw [optimizedGaussianBandwidth unrestrictedGaussianSmoothConstant d L hdp hL] at hr
  have hraw : rectangleDistance (gaussianLaw A) id B ≤
      unrestrictedGaussianComparisonConstant * (L * Real.sqrt d) := by
    calc
      _ ≤ gaussianSmoothingConstant *
          ((unrestrictedGaussianSmoothConstant + 1) * L * Real.sqrt d) := hr
      _ = (gaussianSmoothingConstant * (unrestrictedGaussianSmoothConstant + 1)) *
          (L * Real.sqrt d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg hL.le (Real.sqrt_nonneg _))
  by_cases hsat : 1 ≤ L * Real.sqrt d
  · rw [min_eq_left hsat, mul_one]
    exact (rectangleDistance_le_one _ _ _).trans one_le_unrestrictedGaussianComparisonConstant
  · rw [min_eq_right (le_of_not_ge hsat)]
    exact hraw

/-- The same comparison with an arbitrary positive lower bound on the
reference marginal standard deviations. The constant is universal; only
the explicit factor `1/b` depends on the supplied lower bound. -/
theorem unrestrictedGaussianComparison_of_marginal_lower_bound {p : ℕ}
    (hp : 1 ≤ p) (A B : Matrix (Fin p) (Fin p) ℝ) {b : ℝ}
    (hb : 0 < b) (hB : ∀ j, b ^ 2 ≤ (B * B.transpose) j j) :
    rectangleDistance (gaussianLaw A) id B ≤
      unrestrictedGaussianComparisonConstant * min 1
        (dimensionLog p * Real.sqrt
          (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)) / b) := by
  let d : Vector p := fun j => Real.sqrt ((B * B.transpose) j j)
  have hd (j : Fin p) : b ≤ d j := by
    calc
      b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb.le).symm
      _ ≤ d j := Real.sqrt_le_sqrt (hB j)
  have hdpos (j : Fin p) : 0 < d j := hb.trans_le (hd j)
  let A' := scaledFactor (fun j => (d j)⁻¹) A
  let B' := scaledFactor (fun j => (d j)⁻¹) B
  have hdiag (j : Fin p) : (B' * B'.transpose) j j = 1 := by
    rw [scaledFactor_gram]
    have hs : d j ^ 2 = (B * B.transpose) j j :=
      Real.sq_sqrt ((sq_nonneg b).trans (hB j))
    rw [← hs]
    field_simp [(hdpos j).ne']
    ring
  have hc := unrestrictedGaussianComparison hp A' B' hdiag
  have hdisc := standardizedGaussian_discrepancy_le A B d hb hd
  have hsqrt := Real.sqrt_le_sqrt hdisc
  rw [Real.sqrt_div (proxyCovarianceDiscrepancy_nonneg _ _), Real.sqrt_sq hb.le] at hsqrt
  have hrate :
      dimensionLog p * Real.sqrt (proxyCovarianceDiscrepancy (A' * A'.transpose) (B' * B'.transpose)) ≤
        dimensionLog p * Real.sqrt
          (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)) / b := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsqrt
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp))
  have hnew := hc.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate)
    (zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant))
  apply rectangleDistance_le
  apply rectangleError_undo_standardization_le (gaussianLaw A) id d hdpos B
  intro R
  change rectangleError (gaussianLaw A) (diagonalScale (fun j => (d j)⁻¹)) B' R ≤ _
  rw [gaussianRectangleError_diagonalScale]
  exact (rectangleError_le_rectangleDistance _ _ _ R).trans hnew

/-- The universal comparison constant precedes every dimension, Gaussian
law, covariance matrix and positive marginal lower bound. -/
theorem unrestrictedGaussianComparisonExists :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ), 1 ≤ p →
      ∀ (A B : Matrix (Fin p) (Fin p) ℝ) (b : ℝ), 0 < b →
        (∀ j, b ^ 2 ≤ (B * B.transpose) j j) →
        rectangleDistance (gaussianLaw A) id B ≤ C * min 1
          (dimensionLog p * Real.sqrt
            (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)) / b) := by
  refine ⟨unrestrictedGaussianComparisonConstant,
    one_le_unrestrictedGaussianComparisonConstant, ?_⟩
  intro p hp A B b hb hB
  exact unrestrictedGaussianComparison_of_marginal_lower_bound hp A B hb hB

end

end RectangleCLT.Companion.SplitV4
