import RectangleCLT.SmootherConvolution
import RectangleCLT.GaussianStein
import RectangleCLT.GaussianMaximum
import RectangleCLT.TranslationTaylor
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Gaussian heat identity for the actual rectangle smoother

The Gaussian factor may be singular. Differentiation under the integral uses
the actual bounded smoother derivatives and integrability of the Gaussian
maximum norm, rather than an assumed heat equation.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT
namespace FaceWeights

theorem abs_directionalMean_le_norm_heat {p : ℕ} (w : FaceWeights p) (y : Vector p) :
    |w.directionalMean y| ≤ ‖y‖ := by
  rw [w.directionalMean_eq]
  calc
    _ ≤ ∑ j, |w.v j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w.v j| * ‖y‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j) (abs_nonneg _)
    _ = (∑ j, |w.v j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right w.sum_abs_v_le_one (norm_nonneg _)
    _ = _ := one_mul _

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The actual derivative along an arbitrary line is the contraction of the
actual first coordinate derivatives. -/
theorem hasDerivAt_F_line_sum (x y : Vector p) (t : ℝ) :
    HasDerivAt (fun r => s.F (line x y r))
      (∑ j, y j * s.coordinateDerivativeF (line x y t) j) t := by
  have heq : (∑ j, y j * s.coordinateDerivativeF (line x y t) j) =
      -(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y := by
    rw [(s.weights (line x y t)).directionalMean_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [s.coordinateDerivativeF_eq]
    ring
  rw [heq]
  exact s.hasDerivAt_F_line x y t

/-- The actual derivative of a coordinate gradient along any line is the
contraction of the actual mixed second derivatives. -/
theorem hasDerivAt_firstDerivative_line_sum (x y : Vector p) (j : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.coordinateDerivativeF (line x y r) j)
      (∑ k, y k * s.mixedSecondDerivativeF (line x y t) j k) t := by
  have hdiag : (∑ k, y k * (s.weights (line x y t)).diagonalMass j k) =
      (s.weights (line x y t)).coordinateMass j * y j := by
    simp [FaceWeights.diagonalMass, mul_comm]
  have heq : (∑ k, y k * s.mixedSecondDerivativeF (line x y t) j k) =
      (s.F (line x y t) / s.bandwidth ^ 2) *
        (2 * (s.weights (line x y t)).v j *
          (s.weights (line x y t)).directionalMean y -
          (s.weights (line x y t)).coordinateMass j * y j) := by
    simp_rw [s.mixedSecondDerivativeF_eq]
    rw [(s.weights (line x y t)).directionalMean_eq]
    calc
      _ = (s.F (line x y t) / s.bandwidth ^ 2) *
          (2 * (s.weights (line x y t)).v j *
            (∑ k, (s.weights (line x y t)).v k * y k) -
            ∑ k, y k * (s.weights (line x y t)).diagonalMass j k) := by
        simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hdiag]
  rw [heq]
  exact s.hasDerivAt_coordinateDerivativeF_line x y j t

theorem abs_F_line_derivative_le (x y : Vector p) (t : ℝ) :
    |-(s.F (line x y t) / s.bandwidth) *
      (s.weights (line x y t)).directionalMean y| ≤ ‖y‖ / s.bandwidth := by
  rw [abs_mul, abs_neg, abs_of_nonneg
    (div_nonneg (s.F_pos _).le s.bandwidth_pos.le)]
  calc
    _ ≤ (1 / s.bandwidth) * ‖y‖ :=
      mul_le_mul
        (div_le_div_of_nonneg_right (s.F_le_one _) s.bandwidth_pos.le)
        ((s.weights (line x y t)).abs_directionalMean_le_norm_heat y)
        (abs_nonneg _) (div_nonneg (by norm_num) s.bandwidth_pos.le)
    _ = _ := by ring

/-- Gaussian convolution parametrized by the amplitude, before taking a
square root of the heat-time parameter. -/
noncomputable def gaussianAmplitude (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) : ℝ :=
  ∫ y, s.F (line x y t) ∂gaussianLaw A

/-- A first differentiation under the actual Gaussian integral. The
dominating function is `‖y‖ / h`, which is integrable for every factor. -/
theorem hasDerivAt_gaussianAmplitude (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) :
    HasDerivAt (s.gaussianAmplitude A x)
      (∫ y, -(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y ∂gaussianLaw A) t := by
  have hcont (r : ℝ) : Continuous (fun y : Vector p => s.F (line x y r)) := by
    apply s.continuous_F.comp
    change Continuous (fun y : Vector p => x + r • y)
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun y : Vector p => -(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y) (gaussianLaw A) := by
    have hline : Continuous (fun y : Vector p => line x y t) := by
      change Continuous (fun y : Vector p => x + t • y)
      fun_prop
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (((s.continuous_F.comp hline).div_const _).neg)
    · simp only [FaceWeights.directionalMean_eq]
      exact continuous_finset_sum _ (fun j _ =>
        ((s.continuous_v j).comp hline).mul (continuous_apply j))
  have hi : Integrable (fun y : Vector p => s.F (line x y t)) (gaussianLaw A) :=
    (integrable_const (1 : ℝ)).mono' (hcont t).aestronglyMeasurable
      (ae_of_all _ (fun y => s.norm_F_le_one _))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianLaw A) (bound := fun y : Vector p => ‖y‖ / s.bandwidth)
    (ε := 1) (F := fun r y => s.F (line x y r))
    (F' := fun r y => -(s.F (line x y r) / s.bandwidth) *
      (s.weights (line x y r)).directionalMean y)
    (x₀ := t) (by norm_num)
    (Filter.Eventually.of_forall (fun r => (hcont r).aestronglyMeasurable)) hi hmeas
    (ae_of_all _ (fun y r _ => by
      simpa only [Real.norm_eq_abs] using s.abs_F_line_derivative_le x y r))
    ((gaussianLaw_integrable_norm A).div_const s.bandwidth)
    (ae_of_all _ (fun y r _ => s.hasDerivAt_F_line x y r))
  exact h.2

private theorem amplitude_firstDerivative_stein
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) (j : Fin p) :
    (∫ y, y j * s.coordinateDerivativeF (line x y t) j ∂gaussianLaw A) =
      ∑ k, (A * A.transpose) j k *
        ∫ y, t * s.mixedSecondDerivativeF (line x y t) j k ∂gaussianLaw A := by
  have hline : Continuous (fun y : Vector p => line x y t) := by
    change Continuous (fun y : Vector p => x + t • y)
    fun_prop
  apply gaussianLaw_stein A j
  · intro y a
    have hd := s.hasDerivAt_firstDerivative_line_sum (line x y t)
      (t • (fun k => A k a)) j 0
    convert hd using 1
    · funext r
      congr 1
      ext k
      simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [line_zero, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
  · exact ((s.continuous_firstDerivative j).comp hline).measurable
  · intro k
    exact (continuous_const.mul ((s.continuous_secondDerivative j k).comp hline)).measurable
  · exact ⟨1 / s.bandwidth, fun y => by
      simpa only [Real.norm_eq_abs] using s.norm_firstDerivative_le (line x y t) j⟩
  · refine ⟨|t| * (3 / s.bandwidth ^ 2), fun y k => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using s.norm_secondDerivative_le (line x y t) j k)
      (abs_nonneg t)

/-- The amplitude derivative becomes a covariance contraction by the proved
Stein identity. All test-function assumptions are discharged for the smoother. -/
theorem gaussianAmplitude_derivative_eq_covariance
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    (∫ y, -(s.F (line x y t) / s.bandwidth) *
      (s.weights (line x y t)).directionalMean y ∂gaussianLaw A) =
      t * ∑ j, ∑ k, (A * A.transpose) j k *
        ∫ y, s.mixedSecondDerivativeF (line x y t) j k ∂gaussianLaw A := by
  have hline : Continuous (fun y : Vector p => line x y t) := by
    change Continuous (fun y : Vector p => x + t • y)
    fun_prop
  have hi (j : Fin p) :
      Integrable (fun y => y j * s.coordinateDerivativeF (line x y t) j) (gaussianLaw A) := by
    have hh := (gaussianLaw_integrable_coordinate A j).bdd_mul
      (((s.continuous_firstDerivative j).comp hline).measurable.aestronglyMeasurable)
      ⟨1 / s.bandwidth, fun y => s.norm_firstDerivative_le (line x y t) j⟩
    simpa only [mul_comm] using hh
  have heq (y : Vector p) :
      -(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y =
      ∑ j, y j * s.coordinateDerivativeF (line x y t) j := by
    rw [(s.weights (line x y t)).directionalMean_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [s.coordinateDerivativeF_eq]
    ring
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ => hi j)]
  simp_rw [s.amplitude_firstDerivative_stein A x t, integral_const_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hasDerivAt_gaussianAmplitude_covariance
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    HasDerivAt (s.gaussianAmplitude A x)
      (t * ∑ j, ∑ k, (A * A.transpose) j k *
        ∫ y, s.mixedSecondDerivativeF (line x y t) j k ∂gaussianLaw A) t := by
  rw [← s.gaussianAmplitude_derivative_eq_covariance A x t]
  exact s.hasDerivAt_gaussianAmplitude A x t

/-- The concrete Gaussian heat convolution, parametrized by its variance
multiplier. No positive-definite inverse is used. -/
noncomputable def gaussianHeat (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (τ : ℝ) : ℝ := s.gaussianAmplitude A x (Real.sqrt τ)

/-- The heat function is the literal integral against independent standard
Gaussian coordinates from the interpolation construction. -/
theorem gaussianHeat_eq_standardIntegral (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (τ : ℝ) :
    s.gaussianHeat A x τ =
      ∫ z, s.F (x + Real.sqrt τ • A.mulVec z) ∂standardGaussian p := by
  unfold gaussianHeat gaussianAmplitude gaussianLaw
  have hcont : Continuous (fun y : Vector p => s.F (line x y (Real.sqrt τ))) := by
    apply s.continuous_F.comp
    change Continuous (fun y : Vector p => x + Real.sqrt τ • y)
    fun_prop
  exact integral_map (measurable_mulVec A).aemeasurable hcont.aestronglyMeasurable

theorem integral_gaussianLaw_smul (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) (g : Vector p → ℝ) (hg : Measurable g) :
    (∫ y, g (t • y) ∂gaussianLaw A) = ∫ y, g y ∂gaussianLaw (t • A) := by
  rw [gaussianLaw, integral_map (f := fun y : Vector p => g (t • y))
    (measurable_mulVec A).aemeasurable
    (hg.comp (measurable_const.smul measurable_id)).aestronglyMeasurable,
    gaussianLaw, integral_map (measurable_mulVec (t • A)).aemeasurable hg.aestronglyMeasurable]
  apply integral_congr_ae
  refine ae_of_all _ (fun y => congrArg g ?_)
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The time-parametrized function is exactly the existing concrete Gaussian
probability convolution. -/
theorem gaussianHeat_eq_convolution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (τ : ℝ) :
    s.gaussianHeat A x τ =
      s.convolution (gaussianLaw (Real.sqrt τ • A)) x := by
  unfold gaussianHeat gaussianAmplitude convolution shiftIntegral
  change (∫ y, s.F (x + Real.sqrt τ • y) ∂gaussianLaw A) = _
  exact integral_gaussianLaw_smul A (Real.sqrt τ) (fun y => s.F (x + y))
    ((s.continuous_F.comp (continuous_const.add continuous_id)).measurable)

/-- Actual Gaussian heat differentiation for every positive time. The right
side consists of the actual second coordinate derivatives of the convolution.
Singular covariance factors are allowed. -/
theorem hasDerivAt_gaussianHeat (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (s.gaussianHeat A x)
      ((1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) x j k) τ := by
  have hd := (s.hasDerivAt_gaussianAmplitude_covariance A x (Real.sqrt τ)).comp τ
    (Real.hasDerivAt_sqrt (ne_of_gt hτ))
  have heq (j k : Fin p) :
      (∫ y, s.mixedSecondDerivativeF (line x y (Real.sqrt τ)) j k ∂gaussianLaw A) =
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) x j k := by
    rw [s.convolutionSecondDerivative_eq_integral]
    exact integral_gaussianLaw_smul A (Real.sqrt τ)
      (fun y => s.mixedSecondDerivativeF (x + y) j k)
      (((s.continuous_secondDerivative j k).comp
        (continuous_const.add continuous_id)).measurable)
  change HasDerivAt (fun r => s.gaussianAmplitude A x (Real.sqrt r)) _ τ
  convert hd using 1
  simp_rw [heq]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hτ)]
  ring

/-- The same heat identity stated directly for the existing convolution API. -/
theorem hasDerivAt_gaussian_convolution_time (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun r => s.convolution (gaussianLaw (Real.sqrt r • A)) x)
      ((1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) x j k) τ := by
  have heq : s.gaussianHeat A x =
      (fun r => s.convolution (gaussianLaw (Real.sqrt r • A)) x) :=
    funext (fun r => s.gaussianHeat_eq_convolution A x r)
  rw [← heq]
  exact s.hasDerivAt_gaussianHeat A x hτ

/-- Chain rule for the actual smoother along a differentiable vector curve. -/
theorem hasDerivAt_F_curve {g : ℝ → Vector p} {g' : Vector p} {t : ℝ}
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun r => s.F (g r))
      (∑ j, g' j * s.coordinateDerivativeF (g t) j) t := by
  have hdiff := (s.contDiff_F_translation.differentiable (by simp))
  have hline : HasDerivAt (line (g t) g') g' (0 : ℝ) := by
    change HasDerivAt (fun r : ℝ => g t + r • g') g' (0 : ℝ)
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const g').const_add (g t)
  have hid : (fderiv ℝ s.F (g t)) g' =
      ∑ j, g' j * s.coordinateDerivativeF (g t) j := by
    have hd := (hdiff (line (g t) g' 0)).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [line_zero] using hd.unique (s.hasDerivAt_F_line_sum (g t) g' 0)
  simpa only [hid] using (hdiff (g t)).hasFDerivAt.comp_hasDerivAt t hg

private theorem abs_F_directional_sum_le (x y : Vector p) :
    |∑ j, y j * s.coordinateDerivativeF x j| ≤ ‖y‖ / s.bandwidth := by
  have heq : (∑ j, y j * s.coordinateDerivativeF x j) =
      -(s.F x / s.bandwidth) * (s.weights x).directionalMean y := by
    simpa only [line_zero] using
      (s.hasDerivAt_F_line_sum x y 0).unique (s.hasDerivAt_F_line x y 0)
  rw [heq]
  simpa only [line_zero] using s.abs_F_line_derivative_le x y 0

/-- The unsimplified derivative of the actual Gaussian integral when both the
base point and the heat time move. This supplies domination for the complete
Bernoulli--Gaussian path, rather than assuming a time-dependent heat identity. -/
theorem hasDerivAt_gaussianHeat_line_raw
    (A : Matrix (Fin p) (Fin p) ℝ) (x v : Vector p)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t => s.gaussianHeat A (line x v t) t)
      (∫ y, ∑ j, (v j + (1 / (2 * Real.sqrt τ)) * y j) *
        s.coordinateDerivativeF (line x v τ + Real.sqrt τ • y) j ∂gaussianLaw A) τ := by
  let c : ℝ := 1 / (2 * Real.sqrt (τ / 2))
  have hc : 0 ≤ c := by positivity
  have hrpos {r : ℝ} (hr : r ∈ Metric.ball τ (τ / 2)) : 0 < r := by
    have habs : |r - τ| < τ / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hlo := (abs_lt.mp habs).1
    linarith
  have hcr {r : ℝ} (hr : r ∈ Metric.ball τ (τ / 2)) :
      0 ≤ 1 / (2 * Real.sqrt r) ∧ 1 / (2 * Real.sqrt r) ≤ c := by
    have habs : |r - τ| < τ / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hlo : τ / 2 ≤ r := by have := (abs_lt.mp habs).1; linarith
    refine ⟨by positivity, ?_⟩
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hlo) (by norm_num : (0 : ℝ) ≤ 2))
  have hpoint (r : ℝ) : Continuous (fun y : Vector p => line x v r + Real.sqrt r • y) := by
    change Continuous (fun y : Vector p => (x + r • v) + Real.sqrt r • y)
    fun_prop
  have hF (r : ℝ) : Continuous
      (fun y : Vector p => s.F (line x v r + Real.sqrt r • y)) :=
    s.continuous_F.comp (hpoint r)
  have hD (r : ℝ) : Continuous
      (fun y : Vector p => ∑ j, (v j + (1 / (2 * Real.sqrt r)) * y j) *
        s.coordinateDerivativeF (line x v r + Real.sqrt r • y) j) := by
    exact continuous_finset_sum _ (fun j _ =>
      (continuous_const.add (continuous_const.mul (continuous_apply j))).mul
        ((s.continuous_firstDerivative j).comp (hpoint r)))
  have hbound (y : Vector p) (r : ℝ) (hr : r ∈ Metric.ball τ (τ / 2)) :
      ‖∑ j, (v j + (1 / (2 * Real.sqrt r)) * y j) *
        s.coordinateDerivativeF (line x v r + Real.sqrt r • y) j‖ ≤
        (‖v‖ + c * ‖y‖) / s.bandwidth := by
    have hh := s.abs_F_directional_sum_le (line x v r + Real.sqrt r • y)
      (v + (1 / (2 * Real.sqrt r)) • y)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
    have hnorm : ‖∑ j, (v j + (1 / (2 * Real.sqrt r)) * y j) *
        s.coordinateDerivativeF (line x v r + Real.sqrt r • y) j‖ ≤
          ‖v + (1 / (2 * Real.sqrt r)) • y‖ / s.bandwidth := by
      simpa only [Real.norm_eq_abs] using hh
    apply hnorm.trans
    apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
    calc
      ‖v + (1 / (2 * Real.sqrt r)) • y‖ ≤ ‖v‖ + ‖(1 / (2 * Real.sqrt r)) • y‖ :=
        norm_add_le _ _
      _ = ‖v‖ + (1 / (2 * Real.sqrt r)) * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (hcr hr).1]
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right (hcr hr).2 (norm_nonneg _)) _
  have hi : Integrable (fun y : Vector p => (‖v‖ + c * ‖y‖) / s.bandwidth)
      (gaussianLaw A) :=
    ((integrable_const ‖v‖).add ((gaussianLaw_integrable_norm A).const_mul c)).div_const _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianLaw A) (bound := fun y : Vector p => (‖v‖ + c * ‖y‖) / s.bandwidth)
    (ε := τ / 2) (F := fun r y => s.F (line x v r + Real.sqrt r • y))
    (F' := fun r y => ∑ j, (v j + (1 / (2 * Real.sqrt r)) * y j) *
      s.coordinateDerivativeF (line x v r + Real.sqrt r • y) j) (x₀ := τ)
    (by positivity)
    (Filter.Eventually.of_forall (fun r => (hF r).aestronglyMeasurable))
    ((integrable_const (1 : ℝ)).mono' (hF τ).aestronglyMeasurable
      (ae_of_all _ (fun y => s.norm_F_le_one _)))
    (hD τ).aestronglyMeasurable
    (ae_of_all _ hbound) hi
    (ae_of_all _ (fun y r hr => by
      have hg := (((hasDerivAt_id r).smul_const v).const_add x).add
        ((Real.hasDerivAt_sqrt (ne_of_gt (hrpos hr))).smul_const y)
      simpa only [line, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        s.hasDerivAt_F_curve hg))
  exact hd.2

/-- Actual joint differentiation in heat time and an affine base point. The
Gaussian contribution is a covariance contraction and remains valid for
singular factors. -/
theorem hasDerivAt_gaussianHeat_line
    (A : Matrix (Fin p) (Fin p) ℝ) (x v : Vector p)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t => s.gaussianHeat A (line x v t) t)
      ((∑ j, v j * s.convolutionFirstDerivative
          (gaussianLaw (Real.sqrt τ • A)) (line x v τ) j) +
        (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
          s.convolutionSecondDerivative
            (gaussianLaw (Real.sqrt τ • A)) (line x v τ) j k) τ := by
  let b := line x v τ
  let c := 1 / (2 * Real.sqrt τ)
  have hpoint : Continuous (fun y : Vector p => b + Real.sqrt τ • y) := by
    fun_prop
  have hcD (j : Fin p) : Continuous
      (fun y : Vector p => s.coordinateDerivativeF (b + Real.sqrt τ • y) j) :=
    (s.continuous_firstDerivative j).comp hpoint
  have hiD (j : Fin p) : Integrable
      (fun y : Vector p => s.coordinateDerivativeF (b + Real.sqrt τ • y) j) (gaussianLaw A) :=
    (integrable_const (1 / s.bandwidth : ℝ)).mono' (hcD j).aestronglyMeasurable
      (ae_of_all _ (fun y => s.norm_firstDerivative_le _ j))
  have hiY (j : Fin p) : Integrable
      (fun y : Vector p => y j * s.coordinateDerivativeF (b + Real.sqrt τ • y) j)
      (gaussianLaw A) := by
    have h := (gaussianLaw_integrable_coordinate A j).bdd_mul
      (hcD j).aestronglyMeasurable
      ⟨1 / s.bandwidth, fun y => s.norm_firstDerivative_le _ j⟩
    simpa only [mul_comm] using h
  have heqD (j : Fin p) :
      (∫ y, s.coordinateDerivativeF (b + Real.sqrt τ • y) j ∂gaussianLaw A) =
        s.convolutionFirstDerivative (gaussianLaw (Real.sqrt τ • A)) b j := by
    rw [s.convolutionFirstDerivative_eq_integral]
    exact integral_gaussianLaw_smul A (Real.sqrt τ)
      (fun y => s.coordinateDerivativeF (b + y) j)
      (((s.continuous_firstDerivative j).comp (continuous_const.add continuous_id)).measurable)
  have heqDD (j k : Fin p) :
      (∫ y, s.mixedSecondDerivativeF (b + Real.sqrt τ • y) j k ∂gaussianLaw A) =
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) b j k := by
    rw [s.convolutionSecondDerivative_eq_integral]
    exact integral_gaussianLaw_smul A (Real.sqrt τ)
      (fun y => s.mixedSecondDerivativeF (b + y) j k)
      (((s.continuous_secondDerivative j k).comp
        (continuous_const.add continuous_id)).measurable)
  have hamp : (∫ y, ∑ j, y j *
      s.coordinateDerivativeF (b + Real.sqrt τ • y) j ∂gaussianLaw A) =
      Real.sqrt τ * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) b j k := by
    have h := s.gaussianAmplitude_derivative_eq_covariance A b (Real.sqrt τ)
    have heq (y : Vector p) :
        -(s.F (line b y (Real.sqrt τ)) / s.bandwidth) *
          (s.weights (line b y (Real.sqrt τ))).directionalMean y =
        ∑ j, y j * s.coordinateDerivativeF (b + Real.sqrt τ • y) j := by
      have hh := (s.hasDerivAt_F_line b y (Real.sqrt τ)).unique
        (s.hasDerivAt_F_line_sum b y (Real.sqrt τ))
      exact hh
    simp_rw [heq] at h
    change (∫ y, ∑ j, y j *
      s.coordinateDerivativeF (b + Real.sqrt τ • y) j ∂gaussianLaw A) =
        Real.sqrt τ * ∑ j, ∑ k, (A * A.transpose) j k *
          ∫ y, s.mixedSecondDerivativeF (b + Real.sqrt τ • y) j k ∂gaussianLaw A at h
    simpa only [heqDD] using h
  have hint :
      (∫ y, ∑ j, (v j + c * y j) *
        s.coordinateDerivativeF (b + Real.sqrt τ • y) j ∂gaussianLaw A) =
      (∑ j, v j * s.convolutionFirstDerivative
        (gaussianLaw (Real.sqrt τ • A)) b j) +
      (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) b j k := by
    have hsplit (y : Vector p) :
        (∑ j, (v j + c * y j) * s.coordinateDerivativeF (b + Real.sqrt τ • y) j) =
          (∑ j, v j * s.coordinateDerivativeF (b + Real.sqrt τ • y) j) +
            c * (∑ j, y j * s.coordinateDerivativeF (b + Real.sqrt τ • y) j) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    simp_rw [hsplit]
    rw [integral_add
      (integrable_finset_sum Finset.univ (fun j _ => (hiD j).const_mul (v j)))
      ((integrable_finset_sum Finset.univ (fun j _ => hiY j)).const_mul c),
      integral_finset_sum Finset.univ (fun j _ => (hiD j).const_mul (v j)),
      integral_const_mul]
    simp_rw [integral_const_mul, heqD]
    rw [hamp]
    dsimp [c]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hτ)]
    ring
  convert s.hasDerivAt_gaussianHeat_line_raw A x v hτ using 1
  exact hint.symm

end FaceSmoother
end RectangleCLT
