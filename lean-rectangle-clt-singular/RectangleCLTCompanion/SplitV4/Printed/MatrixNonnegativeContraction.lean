import RectangleCLTCompanion.TiltContraction

/-!
# Printed B.4: nonnegative log-concave Gaussian weights

The frozen paper allows a bounded log-concave weight to vanish.  Unlike the
older selector-specific proof, this file assumes positivity only of its
Gaussian integral.  Prékopa is applied directly to the nonnegative kernel;
no positive approximation or covariance estimate is an input.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed

noncomputable section

/-- Multiplicative log-concavity, including weights with zeros.  Endpoint
parameters are omitted because their inequalities are identities. -/
def NonnegativeLogConcave {r : ℕ} (w : Vector r → ℝ) : Prop :=
  ∀ (x y : Vector r) (t : ℝ), 0 < t → t < 1 →
    w x ^ (1 - t) * w y ^ t ≤ w ((1 - t) • x + t • y)

private theorem convexOn_vectorNormSq {r : ℕ} :
    ConvexOn ℝ univ (vectorNormSq : Vector r → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [vectorNormSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hgap : a * (x i) ^ 2 + b * (y i) ^ 2 - (a * x i + b * y i) ^ 2 =
      a * b * (x i - y i) ^ 2 := by
    rw [show a = 1 - b by linarith]
    ring
  have hh := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i - y i))
  linarith

private theorem log_standardGaussianDensity {r : ℕ} (x : Vector r) :
    Real.log (standardGaussianDensity r x) =
      (r : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - vectorNormSq x / 2 := by
  have hC : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  rw [standardGaussianDensity_eq_kernel]
  unfold gaussianKernel
  rw [Real.log_mul (pow_ne_zero _ hC) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
  ring

private theorem concaveOn_log_standardGaussianDensity {r : ℕ} :
    ConcaveOn ℝ univ (fun x : Vector r => Real.log (standardGaussianDensity r x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := (convexOn_vectorNormSq (r := r)).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  simp_rw [log_standardGaussianDensity]
  have hconst := congrArg
    (fun t : ℝ => t * ((r : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹))) hab
  nlinarith

private def convolutionKernel {r : ℕ} (w : Vector r → ℝ) (z x : Vector r) : ℝ :=
  standardGaussianDensity r (x - z) * w x

private theorem convolutionKernel_measurable {r : ℕ} (w : Vector r → ℝ)
    (hw : Measurable w) (z : Vector r) : Measurable (convolutionKernel w z) :=
  ((standardGaussianDensity_measurable r).comp (measurable_id.sub_const z)).mul hw

private theorem convolutionKernel_integrable {r : ℕ} (w : Vector r → ℝ)
    (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) (z : Vector r) :
    Integrable (convolutionKernel w z) := by
  have hi := (standardGaussianDensity_integrable r).comp_sub_right z
  apply hi.mono' (convolutionKernel_measurable w hw z).aestronglyMeasurable
  filter_upwards [] with x
  change ‖standardGaussianDensity r (x - z) * w x‖ ≤ standardGaussianDensity r (x - z)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (standardGaussianDensity_pos r _).le (hw₀ x))]
  exact mul_le_of_le_one_right (standardGaussianDensity_pos r _).le (hw₁ x)

private theorem convolutionKernel_integral {r : ℕ} (w : Vector r → ℝ) (z : Vector r) :
    (∫ x, convolutionKernel w z x) = ∫ g, w (g + z) ∂standardGaussian r := by
  rw [standardGaussian_integral_density_mul]
  have hh := integral_add_right_eq_self (μ := volume) (convolutionKernel w z) z
  simpa only [convolutionKernel, add_sub_cancel_right] using hh.symm

/-- Positive original mass implies positive mass after every deterministic
Gaussian translation, even when the weight vanishes on a nontrivial set. -/
theorem gaussian_integral_shift_pos_of_mass {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (z : Vector r) :
    0 < ∫ g, w (g + z) ∂standardGaussian r := by
  have hi := standardGaussian_integrable_bounded_weight w hw
    (fun g => by rw [abs_of_nonneg (hw₀ g)]; exact hw₁ g)
  have hie : Integrable (fun g => w g * Real.exp (faceDot z g)) (standardGaussian r) := by
    have hh := (integrable_exp_linearProjection z 1).bdd_mul hw.aestronglyMeasurable
      ⟨1, fun g => by rw [Real.norm_eq_abs, abs_of_nonneg (hw₀ g)]; exact hw₁ g⟩
    simpa only [one_mul] using hh
  have hs : Function.support (fun g => w g * Real.exp (faceDot z g)) =
      Function.support w := by
    ext g
    simp only [Function.mem_support, ne_eq, mul_eq_zero, (Real.exp_pos _).ne',
      or_false]
  have hpos : 0 < ∫ g, w g * Real.exp (faceDot z g) ∂standardGaussian r := by
    rw [integral_pos_iff_support_of_nonneg
      (fun g => mul_nonneg (hw₀ g) (Real.exp_pos _).le) hie, hs]
    exact (integral_pos_iff_support_of_nonneg hw₀ hi).mp hp
  rw [gaussian_exponential_translation] at hpos
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hpos

private theorem convolutionKernel_geometric {r : ℕ} (w : Vector r → ℝ)
    (hw₀ : ∀ x, 0 ≤ w x) (hc : NonnegativeLogConcave w)
    (x y z v : Vector r) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    (convolutionKernel w z x) ^ (1 - t) * (convolutionKernel w v y) ^ t ≤
      convolutionKernel w ((1 - t) • z + t • v) ((1 - t) • x + t • y) := by
  have hρ := (concaveOn_log_standardGaussianDensity (r := r)).2
    (mem_univ (x - z)) (mem_univ (y - v)) (by linarith : 0 ≤ 1 - t) ht₀.le (by ring)
  have hmix : ((1 - t) • x + t • y) - ((1 - t) • z + t • v) =
      (1 - t) • (x - z) + t • (y - v) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgauss : standardGaussianDensity r (x - z) ^ (1 - t) *
      standardGaussianDensity r (y - v) ^ t ≤
      standardGaussianDensity r (((1 - t) • x + t • y) - ((1 - t) • z + t • v)) := by
    rw [Real.rpow_def_of_pos (standardGaussianDensity_pos _ _),
      Real.rpow_def_of_pos (standardGaussianDensity_pos _ _), ← Real.exp_add]
    apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log (standardGaussianDensity_pos _ _))
    simpa only [hmix, smul_eq_mul, mul_comm] using hρ
  simp only [convolutionKernel]
  rw [Real.mul_rpow (standardGaussianDensity_pos _ _).le (hw₀ x),
    Real.mul_rpow (standardGaussianDensity_pos _ _).le (hw₀ y)]
  calc
    _ = (standardGaussianDensity r (x - z) ^ (1 - t) *
        standardGaussianDensity r (y - v) ^ t) * (w x ^ (1 - t) * w y ^ t) := by ring
    _ ≤ standardGaussianDensity r (((1 - t) • x + t • y) - ((1 - t) • z + t • v)) *
        w ((1 - t) • x + t • y) :=
      mul_le_mul hgauss (hc x y t ht₀ ht₁)
        (mul_nonneg (Real.rpow_nonneg (hw₀ x) _) (Real.rpow_nonneg (hw₀ y) _))
        (standardGaussianDensity_pos _ _).le

/-- The generic Prékopa step printed in B.4, allowing a zero set. -/
theorem concaveOn_log_gaussian_convolution_nonnegative {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (hc : NonnegativeLogConcave w) :
    ConcaveOn ℝ univ
      (fun z : Vector r => Real.log (∫ g, w (g + z) ∂standardGaussian r)) := by
  cases r with
  | zero =>
      have hconst : (fun z : Vector 0 => Real.log (∫ g, w (g + z) ∂standardGaussian 0)) =
          (fun _ => Real.log (∫ g, w g ∂standardGaussian 0)) := by
        funext z
        rw [show z = 0 from Subsingleton.elim _ _]
        simp only [add_zero]
      rw [hconst]
      exact concaveOn_const _ convex_univ
  | succ d =>
      refine ⟨convex_univ, ?_⟩
      intro z _ v _ a b ha hb hab
      by_cases hb₀ : b = 0
      · subst b
        simp only [add_zero] at hab
        subst a
        simp
      by_cases ha₀ : a = 0
      · subst a
        simp only [zero_add] at hab
        subst b
        simp
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb₀)
      have hb1 : b < 1 := by linarith [lt_of_le_of_ne ha (Ne.symm ha₀)]
      have hPL := Prekopa.prekopa_leindler_integral
        (f := convolutionKernel w z) (g := convolutionKernel w v)
        (h := convolutionKernel w ((1 - b) • z + b • v)) hbpos hb1
        (convolutionKernel_measurable w hw z) (convolutionKernel_measurable w hw v)
        (convolutionKernel_measurable w hw _)
        (fun x => mul_nonneg (standardGaussianDensity_pos _ _).le (hw₀ x))
        (fun x => mul_nonneg (standardGaussianDensity_pos _ _).le (hw₀ x))
        (fun x => mul_nonneg (standardGaussianDensity_pos _ _).le (hw₀ x))
        (convolutionKernel_integrable w hw hw₀ hw₁ z)
        (convolutionKernel_integrable w hw hw₀ hw₁ v)
        (convolutionKernel_integrable w hw hw₀ hw₁ _)
        (fun x y => convolutionKernel_geometric w hw₀ hc x y z v hbpos hb1)
      simp_rw [convolutionKernel_integral] at hPL
      have hz := gaussian_integral_shift_pos_of_mass w hw hw₀ hw₁ hp z
      have hv := gaussian_integral_shift_pos_of_mass w hw hw₀ hw₁ hp v
      have hh := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hv _)) hPL
      rw [Real.log_mul (Real.rpow_pos_of_pos hz _).ne' (Real.rpow_pos_of_pos hv _).ne',
        Real.log_rpow hz, Real.log_rpow hv] at hh
      rw [show a = 1 - b by linarith]
      simpa only [smul_eq_mul, mul_comm] using hh

/-- The moment-generating identity printed in B.4, with positivity proved
from the original mass instead of pointwise positivity. -/
theorem gaussianTilt_cgf_sub_quadratic_eq_nonnegative {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (u : Vector r) (t : ℝ) :
    cgf (fun g => faceDot u g) (gaussianTilt w) t - t ^ 2 * vectorNormSq u / 2 =
      Real.log (∫ g, w (g + t • u) ∂standardGaussian r) := by
  unfold cgf mgf
  rw [gaussianTilt_integral w hw hw₀]
  have hdot (g : Vector r) : t * faceDot u g = faceDot (t • u) g := by
    simp only [faceDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hdot]
  rw [gaussian_exponential_translation,
    Real.log_mul (Real.exp_pos _).ne'
      (gaussian_integral_shift_pos_of_mass w hw hw₀ hw₁ hp _).ne', Real.log_exp]
  have hnorm : vectorNormSq (t • u) = t ^ 2 * vectorNormSq u := by
    simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hnorm]
  ring

/-- The actual directional covariance inequality for the full nonnegative
weight class printed in B.4. The second derivative is the actual CGF
second derivative, not an assumed variance estimate. -/
theorem gaussianTilt_directional_variance_le_nonnegative {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (hc : NonnegativeLogConcave w)
    (u : Vector r) :
    (∫ g, w g * (faceDot u g) ^ 2 ∂standardGaussian r) / weightMass (standardGaussian r) w -
      ((∫ g, w g * faceDot u g ∂standardGaussian r) /
        weightMass (standardGaussian r) w) ^ 2 ≤ vectorNormSq u := by
  have hconv := concaveOn_log_gaussian_convolution_nonnegative w hw hw₀ hw₁ hp hc
  have hconc : ConcaveOn ℝ univ (fun t : ℝ =>
      cgf (fun g => faceDot u g) (gaussianTilt w) t - t ^ 2 * vectorNormSq u / 2) := by
    simp_rw [gaussianTilt_cgf_sub_quadratic_eq_nonnegative w hw hw₀ hw₁ hp u]
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ c d hc₀ hd₀ hcd
    have hh := hconv.2 (mem_univ (a • u)) (mem_univ (b • u)) hc₀ hd₀ hcd
    have heq : (c • a + d • b) • u = c • (a • u) + d • (b • u) := by
      simp only [smul_eq_mul, add_smul, mul_smul]
    simpa only [heq] using hh
  letI := gaussianTilt_finite w hw hw₀ hw₁
  have hh := normalized_variance_le_of_cgf_sub_quadratic_concave (gaussianTilt w)
    (fun g => faceDot u g) (gaussianTilt_integrableExpSet w hw hw₀ hw₁ u) hconc
  rw [gaussianTilt_integral w hw hw₀, gaussianTilt_integral w hw hw₀,
    gaussianTilt_real_univ w hw hw₀] at hh
  exact hh

/-- Generic covariance contraction claimed before the selector specialization
in the printed B.4 proof. Zeros of the log-concave weight are permitted. -/
theorem gaussian_weightCovariance_contraction_nonnegative {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (hc : NonnegativeLogConcave w) :
    (1 - weightCovariance (standardGaussian r) id w).PosSemidef := by
  refine ⟨Matrix.isHermitian_one.sub (weightCovariance_isHermitian _ w), ?_⟩
  intro u
  have hb (g : Vector r) : |w g| ≤ 1 := by rw [abs_of_nonneg (hw₀ g)]; exact hw₁ g
  have hmass : weightMass (standardGaussian r) w ≠ 0 := hp.ne'
  have hh := gaussianTilt_directional_variance_le_nonnegative w hw hw₀ hw₁ hp hc u
  rw [← gaussian_weightCovariance_quadratic w hw hb hmass u] at hh
  have hnorm : matrixQuadratic (1 : Matrix (Fin r) (Fin r) ℝ) u = vectorNormSq u := by
    simp [matrixQuadratic, Matrix.one_apply, vectorNormSq, pow_two]
  have hquad : matrixQuadratic (1 - weightCovariance (standardGaussian r) id w) u =
      vectorNormSq u - matrixQuadratic (weightCovariance (standardGaussian r) id w) u := by
    simp only [matrixQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    exact congrArg (fun t => t - matrixQuadratic (weightCovariance (standardGaussian r) id w) u) hnorm
  have hnonneg : 0 ≤ matrixQuadratic
      (1 - weightCovariance (standardGaussian r) id w) u := by rw [hquad]; linarith
  simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hnonneg

/-- A convex-cell indicator has multiplicative log-concavity. -/
theorem nonnegativeLogConcave_indicator {r : ℕ} (K : Set (Vector r))
    (hK : Convex ℝ K) : NonnegativeLogConcave (K.indicator (fun _ => (1 : ℝ))) := by
  intro x y t ht₀ ht₁
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hm := hK hx hy (by linarith : 0 ≤ 1 - t) ht₀.le (by ring)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_mem hm, Real.one_rpow, one_mul, le_refl]
    · simp only [Set.indicator_of_not_mem hy, Real.zero_rpow ht₀.ne', mul_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · simp only [Set.indicator_of_not_mem hx, Real.zero_rpow (by linarith : 1 - t ≠ 0), zero_mul]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The convex-cell indicator case specifically asserted in the remark
following printed B.4. -/
theorem gaussian_convex_indicator_covariance_contraction {r : ℕ}
    (K : Set (Vector r)) (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hp : 0 < (standardGaussian r).real K) :
    (1 - weightCovariance (standardGaussian r) id (K.indicator (fun _ => (1 : ℝ)))).PosSemidef := by
  apply gaussian_weightCovariance_contraction_nonnegative _ (measurable_const.indicator hm)
    (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun g => by by_cases hg : g ∈ K <;> simp [hg])
  · rw [show (∫ g, K.indicator (fun _ => (1 : ℝ)) g ∂standardGaussian r) =
        (standardGaussian r).real K from integral_indicator_one hm]
    exact hp
  · exact nonnegativeLogConcave_indicator K hc

end
end RectangleCLT.Companion.SplitV4.Printed
