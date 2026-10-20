import RectangleCLTCompanion.TiltContractionCovariance
import RectangleCLTCompanion.Prekopa.ConvexCombination

/-!
# Covariance contraction for the actual Gaussian selector tilts

The Prékopa--Leindler theorem is applied to the actual Gaussian convolution.
Its logarithmic concavity is then differentiated through the genuine
cumulant-generating function. No contraction, marginalization, or moment
estimate is assumed for the final selector theorem.
-/

open MeasureTheory Set
open scoped BigOperators Topology

namespace RectangleCLT.Companion

noncomputable section

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

private theorem convolutionKernel_geometric {r : ℕ} (w : Vector r → ℝ)
    (hw₀ : ∀ x, 0 < w x)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x)))
    (x y z v : Vector r) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (convolutionKernel w z x) ^ (1 - t) * (convolutionKernel w v y) ^ t ≤
      convolutionKernel w ((1 - t) • z + t • v) ((1 - t) • x + t • y) := by
  have hρ := (concaveOn_log_standardGaussianDensity (r := r)).2
    (mem_univ (x - z)) (mem_univ (y - v)) (by linarith : 0 ≤ 1 - t) ht₀ (by ring)
  have hw := hc.2 (mem_univ x) (mem_univ y) (by linarith : 0 ≤ 1 - t) ht₀ (by ring)
  have hmix : ((1 - t) • x + t • y) - ((1 - t) • z + t • v) =
      (1 - t) • (x - z) + t • (y - v) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpos (a b : Vector r) : 0 < convolutionKernel w a b :=
    mul_pos (standardGaussianDensity_pos r _) (hw₀ b)
  rw [Real.rpow_def_of_pos (hpos z x), Real.rpow_def_of_pos (hpos v y), ← Real.exp_add]
  apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log (hpos _ _))
  simp only [convolutionKernel, Real.log_mul (standardGaussianDensity_pos r _).ne'
    (hw₀ _).ne', hmix, smul_eq_mul] at hρ hw ⊢
  linarith

/-- Prékopa applied to the actual Gaussian convolution. Covariance
invertibility, a pair gap, and a covariance-contraction premise are absent. -/
theorem concaveOn_log_gaussian_convolution {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 < w x) (hw₁ : ∀ x, w x ≤ 1)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) :
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
        (fun x => (mul_pos (standardGaussianDensity_pos _ _) (hw₀ x)).le)
        (fun x => (mul_pos (standardGaussianDensity_pos _ _) (hw₀ x)).le)
        (fun x => (mul_pos (standardGaussianDensity_pos _ _) (hw₀ x)).le)
        (convolutionKernel_integrable w hw (fun x => (hw₀ x).le) hw₁ z)
        (convolutionKernel_integrable w hw (fun x => (hw₀ x).le) hw₁ v)
        (convolutionKernel_integrable w hw (fun x => (hw₀ x).le) hw₁ _)
        (fun x y => convolutionKernel_geometric w hw₀ hc x y z v hbpos.le hb1.le)
      simp_rw [convolutionKernel_integral] at hPL
      have hz := gaussian_integral_shift_pos w hw hw₀ hw₁ z
      have hv := gaussian_integral_shift_pos w hw hw₀ hw₁ v
      have hm := gaussian_integral_shift_pos w hw hw₀ hw₁ ((1 - b) • z + b • v)
      have hh := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hv _)) hPL
      rw [Real.log_mul (Real.rpow_pos_of_pos hz _).ne' (Real.rpow_pos_of_pos hv _).ne',
        Real.log_rpow hz, Real.log_rpow hv] at hh
      rw [show a = 1 - b by linarith]
      simpa only [smul_eq_mul, mul_comm] using hh

/-- General Gaussian covariance contraction for an actual positive bounded
log-concave weight, proved through Prékopa and exact moment derivatives. -/
theorem gaussian_weightCovariance_contraction {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 < w x) (hw₁ : ∀ x, w x ≤ 1)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) :
    (1 - weightCovariance (standardGaussian r) id w).PosSemidef :=
  gaussian_weightCovariance_contraction_of_log_convolution_concave w hw hw₀ hw₁
    (concaveOn_log_gaussian_convolution w hw hw₀ hw₁ hc)

/-- The companion's covariance contraction for every concrete affine
selector tilt. Repeated faces and arbitrary singular rectangular factors
are permitted; every probabilistic and log-concavity premise is discharged. -/
theorem selectorWeight_covariance_contraction {p k r : ℕ}
    (s : FaceSmoother p) (faces : Fin k → Face p)
    (hactive : ∀ i, faces i ∈ s.faces)
    (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    (1 - weightCovariance (standardGaussian r) id
      (fun g => selectorWeight s faces (B.mulVec g + v))).PosSemidef :=
  gaussian_weightCovariance_contraction _
    (continuous_selectorWeight_affine s faces B v).measurable
    (fun g => selectorWeight_pos s faces hactive (B.mulVec g + v))
    (fun g => selectorWeight_le_one s faces (B.mulVec g + v))
    (concaveOn_log_selectorWeight_affine s faces hactive B v)

/-- Omitted faces give the identically zero selector. Thus the concrete
covariance contraction also holds for every indexed face family, without
an active-face premise or a positive-mass side condition. -/
theorem selectorWeight_covariance_contraction_all {p k r : ℕ}
    (s : FaceSmoother p) (faces : Fin k → Face p)
    (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    (1 - weightCovariance (standardGaussian r) id
      (fun g => selectorWeight s faces (B.mulVec g + v))).PosSemidef := by
  classical
  by_cases hactive : ∀ i, faces i ∈ s.faces
  · exact selectorWeight_covariance_contraction s faces hactive B v
  push_neg at hactive
  obtain ⟨i, hi⟩ := hactive
  have hzero (g : Vector r) : selectorWeight s faces (B.mulVec g + v) = 0 := by
    unfold selectorWeight
    have hpi : s.pi (B.mulVec g + v) (faces i) = 0 := by
      simp only [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hi, ↓reduceIte,
        zero_div]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hpi, mul_zero]
  have hfun : (fun g => selectorWeight s faces (B.mulVec g + v)) = (fun _ => (0 : ℝ)) :=
    funext hzero
  rw [hfun]
  have hcov : weightCovariance (standardGaussian r) id (fun _ => (0 : ℝ)) = 0 := by
    ext j l
    simp [weightCovariance, weightMean, weightMass]
  rw [hcov, sub_zero]
  refine ⟨Matrix.isHermitian_one, fun u => ?_⟩
  rw [Matrix.one_mulVec]
  simpa only [dotProduct, star_trivial, pow_two] using
    Finset.sum_nonneg (fun j _ => sq_nonneg (u j))

end

end RectangleCLT.Companion
