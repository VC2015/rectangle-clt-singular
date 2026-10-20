import RectangleCLTCompanion.TiltContractionSelector
import RectangleCLT.GaussianProjectionMaximum
import RectangleCLTCompanion.GaussianEntropy
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Actual Gaussian tilts and their covariance derivatives

The weight is represented by an actual `withDensity` measure. Every
exponential moment is discharged from its boundedness. The final covariance
contraction additionally needs concavity of the Gaussian convolution;
that marginalization theorem is developed separately.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion

noncomputable section

variable {r : ℕ}

/-- The unnormalized, actual Gaussian measure with selector density. -/
def gaussianTilt (w : Vector r → ℝ) : Measure (Vector r) :=
  (standardGaussian r).withDensity (fun g => ENNReal.ofReal (w g))

theorem gaussianTilt_integral (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (f : Vector r → ℝ) :
    (∫ g, f g ∂gaussianTilt w) = ∫ g, w g * f g ∂standardGaussian r := by
  rw [gaussianTilt, integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw₀ _), smul_eq_mul]

theorem gaussianTilt_integrable_iff (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (f : Vector r → ℝ) :
    Integrable f (gaussianTilt w) ↔
      Integrable (fun g => w g * f g) (standardGaussian r) := by
  rw [gaussianTilt, integrable_withDensity_iff_integrable_smul'
    hw.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw₀ _), smul_eq_mul]

theorem gaussianTilt_finite (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1) :
    IsFiniteMeasure (gaussianTilt w) := by
  apply isFiniteMeasure_withDensity
  have hi := standardGaussian_integrable_bounded_weight w hw
    (fun g => by simpa only [abs_of_nonneg (hw₀ g)] using hw₁ g)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hw₀)]
  exact ENNReal.ofReal_ne_top

theorem gaussianTilt_real_univ (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) :
    (gaussianTilt w).real univ = weightMass (standardGaussian r) w := by
  simpa only [integral_const, smul_eq_mul, mul_one, weightMass] using
    gaussianTilt_integral w hw hw₀ (fun _ => (1 : ℝ))

/-- Bounded Gaussian weights preserve every exponential moment of every
linear projection, without a rank or dimension restriction. -/
theorem gaussianTilt_integrableExpSet (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1) (u : Vector r) :
    integrableExpSet (fun g => faceDot u g) (gaussianTilt w) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  change Integrable (fun g => Real.exp (t * faceDot u g)) (gaussianTilt w)
  rw [gaussianTilt_integrable_iff w hw hw₀]
  exact (integrable_exp_linearProjection u t).bdd_mul hw.aestronglyMeasurable
    ⟨1, fun g => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hw₀ g)] using hw₁ g⟩

private theorem antitone_hasDerivAt_nonpos {f : ℝ → ℝ} {d : ℝ}
    (hf : Antitone f) (hd : HasDerivAt f d 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
    (sub_nonpos.mpr (hf ht.le))

/-- A concave Gaussian-corrected cumulant generating function bounds its
actual normalized second central moment. This is the calculus step after
Prékopa, with no moment or derivative formulas left as hypotheses. -/
theorem normalized_variance_le_of_cgf_sub_quadratic_concave
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : integrableExpSet X μ = univ) {v : ℝ}
    (hc : ConcaveOn ℝ univ (fun t => cgf X μ t - t ^ 2 * v / 2)) :
    (∫ x, X x ^ 2 ∂μ) / μ.real univ -
      ((∫ x, X x ∂μ) / μ.real univ) ^ 2 ≤ v := by
  have hi (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by
    rw [hX, interior_univ]
    trivial
  let P : ℝ → ℝ := fun t => cgf X μ t - t ^ 2 * v / 2
  have hcg (t : ℝ) : DifferentiableAt ℝ (cgf X μ) t :=
    (analyticAt_cgf (hi t)).differentiableAt
  have hdP (t : ℝ) : HasDerivAt P (deriv (cgf X μ) t - t * v) t := by
    convert (hcg t).hasDerivAt.sub
      ((((hasDerivAt_id t).pow 2).mul_const v).div_const 2) using 1
    dsimp [P]
    ring
  have hm : Antitone (deriv P) := fun a b hab =>
    hc.antitoneOn_deriv (fun t _ => (hdP t).differentiableAt) (mem_univ a) (mem_univ b) hab
  have hfun : deriv P = fun t => deriv (cgf X μ) t - t * v :=
    funext (fun t => (hdP t).deriv)
  have hcg2 : DifferentiableAt ℝ (deriv (cgf X μ)) 0 := by
    have ha := (analyticAt_cgf (hi 0)).deriv
    exact ha.differentiableAt
  have hdd : HasDerivAt (deriv P) (deriv (deriv (cgf X μ)) 0 - v) 0 := by
    rw [hfun]
    convert hcg2.hasDerivAt.sub ((hasDerivAt_id (0 : ℝ)).mul_const v) using 1
    simp
  have hn := antitone_hasDerivAt_nonpos hm hdd
  have hmoment := iteratedDeriv_two_cgf (hi 0)
  simp only [iteratedDeriv_succ, iteratedDeriv_one, zero_mul, Real.exp_zero, mul_one,
    iteratedDeriv_zero, mgf_zero', deriv_cgf_zero (hi 0)] at hmoment
  linarith

theorem gaussian_integral_shift_pos (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 < w g) (hw₁ : ∀ g, w g ≤ 1) (z : Vector r) :
    0 < ∫ g, w (g + z) ∂standardGaussian r := by
  have hwm : Measurable (fun g => w (g + z)) := hw.comp (measurable_id.add_const z)
  have hwi := standardGaussian_integrable_bounded_weight _ hwm
    (fun g => by rw [abs_of_pos (hw₀ _)]; exact hw₁ _)
  rw [integral_pos_iff_support_of_nonneg (fun g => (hw₀ (g + z)).le) hwi]
  have hs : Function.support (fun g : Vector r => w (g + z)) = univ := by
    ext g
    simp only [Function.mem_support, ne_eq, (hw₀ _).ne', not_false_eq_true, mem_univ]
  rw [hs]
  simp

/-- The Gaussian-corrected cumulant generating function is exactly the
logarithm of the actual translated-selector mass. -/
theorem gaussianTilt_cgf_sub_quadratic_eq (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 < w g) (hw₁ : ∀ g, w g ≤ 1) (u : Vector r) (t : ℝ) :
    cgf (fun g => faceDot u g) (gaussianTilt w) t - t ^ 2 * vectorNormSq u / 2 =
      Real.log (∫ g, w (g + t • u) ∂standardGaussian r) := by
  unfold cgf mgf
  rw [gaussianTilt_integral w hw (fun g => (hw₀ g).le)]
  have hdot (g : Vector r) : t * faceDot u g = faceDot (t • u) g := by
    simp only [faceDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hdot]
  rw [gaussian_exponential_translation,
    Real.log_mul (Real.exp_pos _).ne' (gaussian_integral_shift_pos w hw hw₀ hw₁ _).ne',
    Real.log_exp]
  have hnorm : vectorNormSq (t • u) = t ^ 2 * vectorNormSq u := by
    simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hnorm]
  ring

/-- Concavity of the actual Gaussian convolution bounds every actual
normalized directional variance. The analytic Prékopa theorem supplies
`hc`; no covariance statement is assumed here. -/
theorem gaussianTilt_directional_variance_le_of_log_convolution_concave
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 < w g) (hw₁ : ∀ g, w g ≤ 1)
    (hc : ConcaveOn ℝ univ
      (fun z : Vector r => Real.log (∫ g, w (g + z) ∂standardGaussian r)))
    (u : Vector r) :
    (∫ g, w g * (faceDot u g) ^ 2 ∂standardGaussian r) / weightMass (standardGaussian r) w -
      ((∫ g, w g * faceDot u g ∂standardGaussian r) /
        weightMass (standardGaussian r) w) ^ 2 ≤ vectorNormSq u := by
  have hconc : ConcaveOn ℝ univ (fun t : ℝ =>
      cgf (fun g => faceDot u g) (gaussianTilt w) t - t ^ 2 * vectorNormSq u / 2) := by
    simp_rw [gaussianTilt_cgf_sub_quadratic_eq w hw hw₀ hw₁ u]
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ c d hc₀ hd₀ hcd
    have hh := hc.2 (mem_univ (a • u)) (mem_univ (b • u)) hc₀ hd₀ hcd
    have heq : (c • a + d • b) • u = c • (a • u) + d • (b • u) := by
      simp only [smul_eq_mul, add_smul, mul_smul]
    simpa only [heq] using hh
  letI := gaussianTilt_finite w hw (fun g => (hw₀ g).le) hw₁
  have hh := normalized_variance_le_of_cgf_sub_quadratic_concave (gaussianTilt w)
    (fun g => faceDot u g) (gaussianTilt_integrableExpSet w hw (fun g => (hw₀ g).le) hw₁ u) hconc
  rw [gaussianTilt_integral w hw (fun g => (hw₀ g).le),
    gaussianTilt_integral w hw (fun g => (hw₀ g).le),
    gaussianTilt_real_univ w hw (fun g => (hw₀ g).le)] at hh
  exact hh

end

end RectangleCLT.Companion
