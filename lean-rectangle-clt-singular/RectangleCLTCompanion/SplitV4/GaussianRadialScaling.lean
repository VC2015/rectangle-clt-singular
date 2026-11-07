import RectangleCLTCompanion.SplitV4.GaussianThresholdData
import RectangleCLTCompanion.SplitV4.GaussianThresholdDerivatives
import RectangleCLTCompanion.SplitV4.ContinuousPartials
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Radial differentiation for actual bounded measurable Gaussian tests.
The test itself need not be differentiable; differentiation is performed
on the genuine scaled Gaussian Lebesgue density. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {r : ℕ}

def gaussianLogScaleDensity (r : ℕ) (t : ℝ) (g : Vector r) : ℝ :=
  ((Real.sqrt (2 * Real.pi))⁻¹) ^ r *
    Real.exp (-(r : ℝ) * t - Real.exp (-2 * t) * vectorNormSq g / 2)

theorem gaussianLogScaleDensity_eq (t : ℝ) (g : Vector r) :
    gaussianLogScaleDensity r t g =
      Real.exp (-(r : ℝ) * t) * standardGaussianDensity r (Real.exp (-t) • g) := by
  have hq : vectorNormSq (Real.exp (-t) • g) = Real.exp (-2 * t) * vectorNormSq g := by
    simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      ← Real.exp_nat_mul]
    congr 2
    ring
  rw [standardGaussianDensity_eq_kernel]
  unfold gaussianKernel gaussianLogScaleDensity
  rw [hq, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem gaussianLogScaleDensity_zero (g : Vector r) :
    gaussianLogScaleDensity r 0 g = standardGaussianDensity r g := by
  rw [gaussianLogScaleDensity_eq]
  simp

theorem hasDerivAt_gaussianLogScaleDensity (t : ℝ) (g : Vector r) :
    HasDerivAt (fun s => gaussianLogScaleDensity r s g)
      (gaussianLogScaleDensity r t g * (Real.exp (-2 * t) * vectorNormSq g - r)) t := by
  have he := ((hasDerivAt_id t).const_mul (-2)).exp
  have hd := (((hasDerivAt_id t).const_mul (-(r : ℝ))).sub
    ((he.mul_const (vectorNormSq g)).div_const 2)).exp
  convert hd.const_mul (((Real.sqrt (2 * Real.pi))⁻¹) ^ r) using 1 <;>
    dsimp only [gaussianLogScaleDensity, id_eq] <;> ring

theorem measurable_gaussianLogScaleDensity (t : ℝ) :
    Measurable (gaussianLogScaleDensity r t) := by
  unfold gaussianLogScaleDensity vectorNormSq
  fun_prop

theorem gaussianLogScaleDensity_derivative_bound
    {t : ℝ} (ht : |t| < Real.log 2 / 2) (g : Vector r) :
    |gaussianLogScaleDensity r t g * (Real.exp (-2 * t) * vectorNormSq g - r)| ≤
      Real.exp ((r : ℝ) * Real.log 2) *
        ((2 * vectorNormSq g + r) * standardGaussianDensity r ((1 / 2 : ℝ) • g)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htlow : -Real.log 2 / 2 < t := by simpa only [neg_div] using (abs_lt.mp ht).1
  have hthigh : t < Real.log 2 / 2 := (abs_lt.mp ht).2
  have hq : 0 ≤ vectorNormSq g := vectorNormSq_nonneg g
  have hdim : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have heupper : Real.exp (-2 * t) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by norm_num)
  have helower : (1 / 2 : ℝ) ≤ Real.exp (-2 * t) := by
    have he : Real.exp (-Real.log 2) ≤ Real.exp (-2 * t) := by
      apply Real.exp_le_exp.mpr
      linarith
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using he
  have hcoeff : Real.exp (-(r : ℝ) * t) ≤ Real.exp ((r : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hkernel : standardGaussianDensity r (Real.exp (-t) • g) ≤
      standardGaussianDensity r ((1 / 2 : ℝ) • g) := by
    rw [standardGaussianDensity_eq_kernel, standardGaussianDensity_eq_kernel]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    unfold gaussianKernel
    apply Real.exp_le_exp.mpr
    have hqexp : vectorNormSq (Real.exp (-t) • g) = Real.exp (-2 * t) * vectorNormSq g := by
      simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
        ← Real.exp_nat_mul]
      congr 2
      ring
    have hqhalf : vectorNormSq ((1 / 2 : ℝ) • g) = vectorNormSq g / 4 := by
      simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      ring
    rw [hqexp, hqhalf]
    nlinarith
  have hdensity : gaussianLogScaleDensity r t g ≤
      Real.exp ((r : ℝ) * Real.log 2) * standardGaussianDensity r ((1 / 2 : ℝ) • g) := by
    rw [gaussianLogScaleDensity_eq]
    exact mul_le_mul hcoeff hkernel (standardGaussianDensity_pos _ _).le (Real.exp_pos _).le
  have habs : |Real.exp (-2 * t) * vectorNormSq g - r| ≤ 2 * vectorNormSq g + r := by
    calc
      _ ≤ |Real.exp (-2 * t) * vectorNormSq g| + |(r : ℝ)| := abs_sub _ _
      _ = Real.exp (-2 * t) * vectorNormSq g + r := by
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hq), abs_of_nonneg hdim]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right heupper hq) _
  have hnonneg : 0 ≤ gaussianLogScaleDensity r t g := by
    rw [gaussianLogScaleDensity_eq]
    exact mul_nonneg (Real.exp_pos _).le (standardGaussianDensity_pos _ _).le
  rw [abs_mul, abs_of_nonneg hnonneg]
  exact (mul_le_mul hdensity habs (abs_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (standardGaussianDensity_pos _ _).le)).trans_eq (by ring)

theorem integrable_gaussianLogScaleMajorant (r : ℕ) :
    Integrable (fun g : Vector r =>
      (2 * vectorNormSq g + r) * standardGaussianDensity r ((1 / 2 : ℝ) • g)) := by
  have hi : Integrable (fun g : Vector r => 8 * vectorNormSq g + r) (standardGaussian r) :=
    (SignedSurface.standardGaussian_integrable_vectorNormSq r).const_mul 8 |>.add (integrable_const _)
  have hd := (standardGaussian_integrable_density_mul_iff _).mp hi
  have hs := hd.comp_smul (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hqhalf (g : Vector r) : vectorNormSq ((1 / 2 : ℝ) • g) = vectorNormSq g / 4 := by
    simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    ring
  convert hs using 1
  funext g
  dsimp only
  rw [hqhalf]
  ring

/-- Differentiation of a genuine scaled density against a bounded hard
test. All domination is supplied by explicit Gaussian moments. -/
theorem hasDerivAt_gaussianLogScaleIntegral
    (f : Vector r → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ g, |f g| ≤ M) :
    HasDerivAt (fun t => ∫ g : Vector r, gaussianLogScaleDensity r t g * f g)
      (∫ g, (vectorNormSq g - r) * f g ∂standardGaussian r) 0 := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbound 0)
  have hfi : Integrable f (standardGaussian r) :=
    (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using hbound g)
  have hF0 : Integrable (fun g => gaussianLogScaleDensity r 0 g * f g) := by
    simpa only [gaussianLogScaleDensity_zero] using
      (standardGaussian_integrable_density_mul_iff f).mp hfi
  have hDmeas : Measurable (fun g : Vector r =>
      gaussianLogScaleDensity r 0 g * (Real.exp (-2 * 0) * vectorNormSq g - r) * f g) := by
    unfold gaussianLogScaleDensity vectorNormSq
    fun_prop
  have hi : Integrable (fun g : Vector r => M * Real.exp ((r : ℝ) * Real.log 2) *
      ((2 * vectorNormSq g + r) * standardGaussianDensity r ((1 / 2 : ℝ) • g))) :=
    (integrable_gaussianLogScaleMajorant r).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Vector r))) (ε := Real.log 2 / 2)
    (F := fun t g => gaussianLogScaleDensity r t g * f g)
    (F' := fun t g => gaussianLogScaleDensity r t g *
      (Real.exp (-2 * t) * vectorNormSq g - r) * f g)
    (bound := fun g => M * Real.exp ((r : ℝ) * Real.log 2) *
      ((2 * vectorNormSq g + r) * standardGaussianDensity r ((1 / 2 : ℝ) • g)))
    (x₀ := (0 : ℝ)) (by exact div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (Eventually.of_forall (fun t => ((measurable_gaussianLogScaleDensity t).mul hf).aestronglyMeasurable))
    hF0 hDmeas.aestronglyMeasurable
    (ae_of_all _ (fun g t ht => by
      have ht' : |t| < Real.log 2 / 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      rw [Real.norm_eq_abs, abs_mul]
      have hmajor : 0 ≤ Real.exp ((r : ℝ) * Real.log 2) *
          ((2 * vectorNormSq g + r) * standardGaussianDensity r ((1 / 2 : ℝ) • g)) :=
        mul_nonneg (Real.exp_pos _).le (mul_nonneg
          (by nlinarith [vectorNormSq_nonneg g, (show (0 : ℝ) ≤ r from Nat.cast_nonneg r)])
          (standardGaussianDensity_pos _ _).le)
      have hh := mul_le_mul (gaussianLogScaleDensity_derivative_bound ht' g) (hbound g)
        (abs_nonneg (f g)) hmajor
      exact hh.trans_eq (by ring))) hi
    (ae_of_all _ (fun g t _ => (hasDerivAt_gaussianLogScaleDensity t g).mul_const (f g)))
  have hscore : (∫ g : Vector r, gaussianLogScaleDensity r 0 g *
      (Real.exp (-2 * 0) * vectorNormSq g - r) * f g) =
      ∫ g, (vectorNormSq g - r) * f g ∂standardGaussian r := by
    rw [standardGaussian_integral_density_mul]
    apply integral_congr_ae
    filter_upwards [] with g
    simp only [gaussianLogScaleDensity_zero, mul_zero, Real.exp_zero, one_mul]
    ring
  rw [hscore] at hd
  exact hd.2

/-- The scaled density is exactly the pushforward of the actual standard
Gaussian, by a genuine Haar change of variables. -/
theorem gaussianLogScaleIntegral_eq (f : Vector r → ℝ) (t : ℝ) :
    (∫ g : Vector r, gaussianLogScaleDensity r t g * f g) =
      ∫ g, f (Real.exp t • g) ∂standardGaussian r := by
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure (Vector r))
    (fun y : Vector r => standardGaussianDensity r (Real.exp (-t) • y) * f y)
    (Real.exp t) (hR := (Real.exp_pos t).le)
  simp only [smul_smul, he, one_smul, Module.finrank_fin_fun, ← Real.exp_nat_mul,
    ← Real.exp_neg, smul_eq_mul] at hs
  calc
    _ = Real.exp (-(r : ℝ) * t) *
        ∫ g : Vector r, standardGaussianDensity r (Real.exp (-t) • g) * f g := by
      simp_rw [gaussianLogScaleDensity_eq, mul_assoc]
      exact integral_const_mul _ _
    _ = ∫ g : Vector r, standardGaussianDensity r g * f (Real.exp t • g) := by
      convert hs.symm using 1
      congr 2
      ring
    _ = _ := (standardGaussian_integral_density_mul _).symm

theorem hasDerivAt_standardGaussian_logScale
    (f : Vector r → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ g, |f g| ≤ M) :
    HasDerivAt (fun t => ∫ g, f (Real.exp t • g) ∂standardGaussian r)
      (∫ g, (vectorNormSq g - r) * f g ∂standardGaussian r) 0 := by
  simpa only [gaussianLogScaleIntegral_eq] using hasDerivAt_gaussianLogScaleIntegral f hf M hbound

/-- Actual radial threshold differentiation. This is the Gaussian side of
the radial trace identity; the CDF chain rule supplies its face expansion. -/
theorem hasDerivAt_gaussianThresholdCDF_logScale
    {m : ℕ} (u : Fin m → Vector r) (b : Vector m) :
    HasDerivAt (fun t => gaussianThresholdCDF u (fun j => Real.exp (-t) * b j))
      (gaussianThresholdTrace u b) 0 := by
  let P : Set (Vector r) := {g | ∀ j, faceDot (u j) g ≤ b j}
  let f : Vector r → ℝ := P.indicator (fun _ => 1)
  have hP : MeasurableSet P := by
    simp only [P, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    exact Finset.measurable_sum _ (fun k _ => measurable_const.mul (measurable_pi_apply k))
  have hf : Measurable f := measurable_const.indicator hP
  have hbnd : ∀ g, |f g| ≤ (1 : ℝ) := by
    intro g
    by_cases hg : g ∈ P <;> simp [f, hg]
  have hscale (t : ℝ) : (∫ g, f (Real.exp t • g) ∂standardGaussian r) =
      gaussianThresholdCDF u (fun j => Real.exp (-t) * b j) := by
    have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have hdot (j : Fin m) (g : Vector r) :
        faceDot (u j) (Real.exp t • g) = Real.exp t * faceDot (u j) g := by
      simp only [faceDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hev (g : Vector r) : Real.exp t • g ∈ P ↔
        ∀ j, faceDot (u j) g ≤ Real.exp (-t) * b j := by
      simp only [P, Set.mem_setOf_eq, hdot]
      apply forall_congr'
      intro j
      constructor
      · intro hj
        have hh := mul_le_mul_of_nonneg_left hj (Real.exp_pos (-t)).le
        simpa only [← mul_assoc, he, one_mul] using hh
      · intro hj
        have hh := mul_le_mul_of_nonneg_left hj (Real.exp_pos t).le
        have he' : Real.exp t * Real.exp (-t) = 1 := by rw [mul_comm]; exact he
        simpa only [← mul_assoc, he', one_mul] using hh
    have hm : MeasurableSet {g : Vector r | ∀ j, faceDot (u j) g ≤ Real.exp (-t) * b j} := by
      simp only [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro j
      apply measurableSet_le _ measurable_const
      exact Finset.measurable_sum _ (fun k _ => measurable_const.mul (measurable_pi_apply k))
    have hfun : (fun g => f (Real.exp t • g)) =
        ({g : Vector r | ∀ j, faceDot (u j) g ≤ Real.exp (-t) * b j}).indicator (fun _ => (1 : ℝ)) := by
      funext g
      simp only [f, Set.indicator_apply, hev, Set.mem_setOf_eq]
    rw [hfun, integral_indicator_const _ hm, smul_eq_mul, mul_one]
    rfl
  have hscore : (∫ g, (vectorNormSq g - r) * f g ∂standardGaussian r) =
      gaussianThresholdTrace u b := by
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      change (vectorNormSq g - r) * P.indicator (fun _ => (1 : ℝ)) g =
        P.indicator (fun g => vectorNormSq g - r) g
      by_cases hg : g ∈ P <;> simp [hg])
  have hd := hasDerivAt_standardGaussian_logScale f hf 1 hbnd
  simp_rw [hscale] at hd
  rwa [hscore] at hd

/-- The actual radial trace identity of B.5. The face derivatives are the
genuine partial derivatives of the hard Gaussian distribution function. -/
theorem gaussianThresholdTrace_eq_radial_first
    {m n : ℕ} (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdTrace u b = -∑ j, b j * gaussianThresholdFirst u b j := by
  have hC := hasFDerivAt_of_continuous_coordinate_derivatives (gaussianThresholdCDF u)
    (fun a j => gaussianThresholdFirst u a j)
    (fun a j c => hasDerivAt_gaussianThresholdCDF_update_first u a j (hu j) hi c)
    (fun j => continuous_gaussianThresholdFirst u j (hu j) hi) b
  have hp : HasDerivAt (fun t : ℝ => fun j : Fin m => Real.exp (-t) * b j)
      (fun j => -b j) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (((hasDerivAt_id (0 : ℝ)).neg).exp).mul_const (b j)
  have hC' : HasFDerivAt (gaussianThresholdCDF u)
      (∑ j, gaussianThresholdFirst u b j • (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ))
      (fun j => Real.exp (-(0 : ℝ)) * b j) := by simpa using hC
  have hd := hC'.comp_hasDerivAt 0 hp
  have he := (hasDerivAt_gaussianThresholdCDF_logScale u b).unique hd
  rw [he]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end RectangleCLT.Companion.SplitV4
