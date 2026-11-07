import RectangleCLTCompanion.SplitV4.PairedSlepian
import RectangleCLT.GaussianComparisonInterpolation
import Mathlib.Analysis.Calculus.MeanValue

/-! Differentiation and Gaussian integration by parts for an actual
independent Slepian path. The observation law needs a finite first moment;
bounded first and second derivatives provide all domination. The Gaussian
factor may be singular. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

namespace C4Test

variable {p : ℕ} (f : C4Test p)

def coordinateVector (j : Fin p) : Vector p := Pi.single j 1

@[simp] theorem norm_coordinateVector (j : Fin p) : ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector, Pi.norm_single]

private theorem linearMap_coordinates (L : Vector p →L[ℝ] ℝ) (v : Vector p) :
    L v = ∑ j, v j * L (coordinateVector j) := by
  classical
  have hv : v = ∑ j : Fin p, v j • coordinateVector j := by
    ext k
    simp [coordinateVector, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]

def hessianCoordinate (x : Vector p) (j k : Fin p) : ℝ :=
  f.hessian x (Function.update (fun _ : Fin 2 => coordinateVector j) 0 (coordinateVector k))

def hessianTrace (cov : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) : ℝ :=
  ∑ j, ∑ k, cov j k * f.hessianCoordinate x j k

theorem continuous_value : Continuous f.value :=
  continuous_iff_continuousAt.mpr (fun x => (f.has_gradient x).continuousAt)

theorem continuous_gradient_eval :
    Continuous (fun z : Vector p × Vector p => f.gradient z.1 z.2) :=
  (f.continuous_gradient.comp continuous_fst).clm_apply continuous_snd

theorem continuous_hessianCoordinate (j k : Fin p) : Continuous (fun x => f.hessianCoordinate x j k) := by
  unfold hessianCoordinate
  exact f.continuous_hessian.eval continuous_const

theorem norm_hessianCoordinate_le (x : Vector p) (j k : Fin p) :
    ‖f.hessianCoordinate x j k‖ ≤ f.bound := by
  have hn := (f.hessian x).le_opNorm
    (Function.update (fun _ : Fin 2 => coordinateVector j) 0 (coordinateVector k))
  have hprod : (∏ i : Fin 2, ‖Function.update (fun _ : Fin 2 => coordinateVector j)
      0 (coordinateVector k) i‖) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp only [Function.update_apply]
    split_ifs <;> exact norm_coordinateVector _
  rw [hprod, mul_one] at hn
  exact hn.trans (f.norm_hessian_le x)

theorem norm_value_le (x : Vector p) :
    ‖f.value x‖ ≤ f.bound * ‖x‖ + ‖f.value 0‖ := by
  have hh := (convex_univ : Convex ℝ (Set.univ : Set (Vector p))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (f.has_gradient x).hasFDerivWithinAt)
    (fun x _ => f.norm_gradient_le x) (mem_univ (0 : Vector p)) (mem_univ x)
  calc
    _ = ‖f.value x - f.value 0 + f.value 0‖ := by congr 1; ring
    _ ≤ ‖f.value x - f.value 0‖ + ‖f.value 0‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_right (by simpa only [sub_zero] using hh) _

theorem integrable_value_of_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (hi : Integrable (fun ω => ‖X ω‖) μ) : Integrable (fun ω => f.value (X ω)) μ := by
  apply ((hi.const_mul f.bound).add (integrable_const ‖f.value 0‖)).mono'
    (f.continuous_value.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ (fun ω => f.norm_value_le (X ω))

theorem integrable_gradient_direction_of_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → Vector p) (hX : Measurable X) (hY : Measurable Y)
    (hi : Integrable (fun ω => ‖Y ω‖) μ) :
    Integrable (fun ω => f.gradient (X ω) (Y ω)) μ := by
  apply (hi.const_mul f.bound).mono'
    (f.continuous_gradient_eval.measurable.comp (hX.prodMk hY)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => f.norm_gradient_eval_le _ _)

def slepianPoint {Ω : Type*} (W : Ω → Vector p) (t : ℝ) (z : Ω × Vector p) : Vector p :=
  Real.sqrt t • W z.1 + Real.sqrt (1 - t) • z.2

def slepianVelocity {Ω : Type*} (W : Ω → Vector p) (t : ℝ) (z : Ω × Vector p) : Vector p :=
  (1 / (2 * Real.sqrt t)) • W z.1 - (1 / (2 * Real.sqrt (1 - t))) • z.2

theorem measurable_slepianPoint {Ω : Type*} [MeasurableSpace Ω]
    (W : Ω → Vector p) (hW : Measurable W) (t : ℝ) : Measurable (slepianPoint W t) :=
  (measurable_const.smul (hW.comp measurable_fst)).add (measurable_const.smul measurable_snd)

theorem measurable_slepianVelocity {Ω : Type*} [MeasurableSpace Ω]
    (W : Ω → Vector p) (hW : Measurable W) (t : ℝ) : Measurable (slepianVelocity W t) :=
  (measurable_const.smul (hW.comp measurable_fst)).sub (measurable_const.smul measurable_snd)

theorem hasDerivAt_slepianPoint {Ω : Type*} (W : Ω → Vector p)
    (z : Ω × Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => slepianPoint W r z) (slepianVelocity W t z) t := by
  have hd := FaceSmoother.hasDerivAt_gaussianComparisonPoint (z.2, W z.1) ht ht1
  convert hd using 1 <;>
    simp only [slepianPoint, slepianVelocity, FaceSmoother.gaussianComparisonPoint,
      FaceSmoother.gaussianComparisonVelocity, sub_eq_add_neg, neg_smul, add_comm]

def slepianExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : ℝ :=
  ∫ z, f.value (slepianPoint W t z) ∂μ.prod (gaussianLaw A)

theorem hasDerivAt_slepianExpectation_raw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (hWnorm : Integrable (fun ω => ‖W ω‖) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ W A)
      (∫ z, f.gradient (slepianPoint W t z) (slepianVelocity W t z)
        ∂μ.prod (gaussianLaw A)) t := by
  have htcomp : 0 < 1 - t := by linarith
  let ε := min t (1 - t) / 2
  let a := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let b := 1 / (2 * Real.sqrt (t / 2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεt : ε ≤ t / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hε1 : ε ≤ (1 - t) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlocal {r : ℝ} (hr : r ∈ Metric.ball t ε) :
      t / 2 < r ∧ (1 - t) / 2 < 1 - r := by
    have habs : |r - t| < ε := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hh := abs_lt.mp habs
    constructor <;> linarith [hh.1, hh.2]
  have hrpos {r : ℝ} (hr : r ∈ Metric.ball t ε) : 0 < r :=
    lt_trans (by positivity : 0 < t / 2) (hlocal hr).1
  have hrone {r : ℝ} (hr : r ∈ Metric.ball t ε) : r < 1 := by
    linarith [(hlocal hr).2]
  have hca {r : ℝ} (hr : r ∈ Metric.ball t ε) : 1 / (2 * Real.sqrt (1 - r)) ≤ a := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlocal hr).2.le) (by norm_num))
  have hcb {r : ℝ} (hr : r ∈ Metric.ball t ε) : 1 / (2 * Real.sqrt r) ≤ b := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlocal hr).1.le) (by norm_num))
  have hiW : Integrable (fun z : Ω × Vector p => ‖W z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hWnorm.mul_prod (integrable_const (1 : ℝ))
  have hiZ : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_norm A)
  have hiX : Integrable (fun z => ‖slepianPoint W t z‖) (μ.prod (gaussianLaw A)) := by
    apply ((hiW.const_mul (Real.sqrt t)).add (hiZ.const_mul (Real.sqrt (1 - t)))).mono'
      (measurable_slepianPoint W hW t).norm.aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_add_le _ _).trans_eq (by simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)])
  have hi : Integrable (fun z : Ω × Vector p => f.bound * (b * ‖W z.1‖ + a * ‖z.2‖))
      (μ.prod (gaussianLaw A)) := ((hiW.const_mul b).add (hiZ.const_mul a)).const_mul f.bound
  have hbound (z : Ω × Vector p) (r : ℝ) (hr : r ∈ Metric.ball t ε) :
      ‖f.gradient (slepianPoint W r z) (slepianVelocity W r z)‖ ≤
        f.bound * (b * ‖W z.1‖ + a * ‖z.2‖) := by
    apply (f.norm_gradient_eval_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ f.bound_nonneg
    calc
      _ ≤ ‖(1 / (2 * Real.sqrt r)) • W z.1‖ +
          ‖(1 / (2 * Real.sqrt (1 - r))) • z.2‖ := norm_sub_le _ _
      _ = (1 / (2 * Real.sqrt r)) * ‖W z.1‖ +
          (1 / (2 * Real.sqrt (1 - r))) * ‖z.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (hcb hr) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hca hr) (norm_nonneg _))
  have hD (r : ℝ) : Measurable (fun z : Ω × Vector p =>
      f.gradient (slepianPoint W r z) (slepianVelocity W r z)) :=
    f.continuous_gradient_eval.measurable.comp
      ((measurable_slepianPoint W hW r).prodMk (measurable_slepianVelocity W hW r))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.prod (gaussianLaw A)) (bound := fun z : Ω × Vector p =>
      f.bound * (b * ‖W z.1‖ + a * ‖z.2‖)) (ε := ε)
    (F := fun r z => f.value (slepianPoint W r z))
    (F' := fun r z => f.gradient (slepianPoint W r z) (slepianVelocity W r z))
    (x₀ := t) hε
    (Filter.Eventually.of_forall (fun r =>
      (f.continuous_value.measurable.comp (measurable_slepianPoint W hW r)).aestronglyMeasurable))
    (f.integrable_value_of_norm _ _ (measurable_slepianPoint W hW t) hiX)
    (hD t).aestronglyMeasurable (ae_of_all _ hbound) hi
    (ae_of_all _ (fun z r hr =>
      (f.has_gradient (slepianPoint W r z)).comp_hasDerivAt r
        (hasDerivAt_slepianPoint W z (hrpos hr) (hrone hr))))
  exact hd.2

private theorem hasDerivAt_gradient_line (x u v : Vector p) :
    HasDerivAt (fun t : ℝ => f.gradient (x + t • v) u)
      ((f.hessian x).toContinuousLinearMap (fun _ => u) 0 v) 0 := by
  have hp := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd := (f.has_hessian (x + (0 : ℝ) • v) u).comp_hasDerivAt 0 hp
  simpa only [zero_smul, add_zero, one_smul] using hd

theorem gaussian_gradient_coordinate_stein
    (A : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (r : Vector p) (j : Fin p) :
    (∫ x, x j * f.gradient (a • x + r) (coordinateVector j) ∂gaussianLaw A) =
      a * ∑ k, (A * A.transpose) j k *
        ∫ x, f.hessianCoordinate (a • x + r) j k ∂gaussianLaw A := by
  have hp : Continuous (fun x : Vector p => a • x + r) := by fun_prop
  have hs : (∫ x, x j * f.gradient (a • x + r) (coordinateVector j) ∂gaussianLaw A) =
      ∑ k, (A * A.transpose) j k *
        ∫ x, a * f.hessianCoordinate (a • x + r) j k ∂gaussianLaw A := by
    apply gaussianLaw_stein A j
    · intro x l
      have hd := f.hasDerivAt_gradient_line (a • x + r) (coordinateVector j) (a • (fun k => A k l))
      convert hd using 1
      · funext t
        apply congrArg (fun y => f.gradient y (coordinateVector j))
        ext k
        change a * (x k + t * A k l) + r k = (a * x k + r k) + t * (a * A k l)
        ring
      · simp only [map_smul, smul_eq_mul]
        rw [linearMap_coordinates]
        simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply, hessianCoordinate,
          Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    · exact ((f.continuous_gradient.clm_apply continuous_const).comp hp).measurable
    · intro k
      exact (continuous_const.mul ((f.continuous_hessianCoordinate j k).comp hp)).measurable
    · refine ⟨f.bound, fun x => ?_⟩
      simpa only [Real.norm_eq_abs, norm_coordinateVector, mul_one] using
        f.norm_gradient_eval_le (a • x + r) (coordinateVector j)
    · refine ⟨|a| * f.bound, fun x k => ?_⟩
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using f.norm_hessianCoordinate_le (a • x + r) j k)
        (abs_nonneg a)
  rw [hs]
  simp only [integral_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

private theorem integrable_gaussian_gradient_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (r : Vector p) (j : Fin p) :
    Integrable (fun x => x j * f.gradient (a • x + r) (coordinateVector j)) (gaussianLaw A) := by
  have hc : Continuous (fun x : Vector p => f.gradient (a • x + r) (coordinateVector j)) :=
    (f.continuous_gradient.clm_apply continuous_const).comp (by fun_prop)
  have hi := (gaussianLaw_integrable_coordinate A j).bdd_mul hc.aestronglyMeasurable
    ⟨f.bound, fun x => by simpa only [norm_coordinateVector, mul_one] using
      f.norm_gradient_eval_le (a • x + r) (coordinateVector j)⟩
  simpa only [mul_comm] using hi

theorem gaussian_gradient_stein
    (A : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (r : Vector p) :
    (∫ x, f.gradient (a • x + r) x ∂gaussianLaw A) =
      a * ∑ j, ∑ k, (A * A.transpose) j k *
        ∫ x, f.hessianCoordinate (a • x + r) j k ∂gaussianLaw A := by
  have heq (x : Vector p) : f.gradient (a • x + r) x =
      ∑ j, x j * f.gradient (a • x + r) (coordinateVector j) :=
    linearMap_coordinates _ _
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ => f.integrable_gaussian_gradient_coordinate A a r j)]
  simp_rw [f.gaussian_gradient_coordinate_stein A a r]
  rw [Finset.mul_sum]

theorem integrable_hessianCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (j k : Fin p) : Integrable (fun ω => f.hessianCoordinate (X ω) j k) μ := by
  apply (integrable_const f.bound).mono'
    ((f.continuous_hessianCoordinate j k).measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ (fun ω => f.norm_hessianCoordinate_le _ _ _)

theorem integrable_hessianTrace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (cov : Matrix (Fin p) (Fin p) ℝ) : Integrable (fun ω => f.hessianTrace cov (X ω)) μ := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  exact (f.integrable_hessianCoordinate μ X hX j k).const_mul (cov j k)

theorem integral_hessianTrace_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (cov : Matrix (Fin p) (Fin p) ℝ) :
    (∫ ω, f.hessianTrace cov (X ω) ∂μ) =
      ∑ j, ∑ k, cov j k * ∫ ω, f.hessianCoordinate (X ω) j k ∂μ := by
  unfold hessianTrace
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => (f.integrable_hessianCoordinate μ X hX j k).const_mul (cov j k)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ
    (fun k _ => (f.integrable_hessianCoordinate μ X hX j k).const_mul (cov j k))]
  simp only [integral_const_mul]

/-- Integration by parts in the independent Gaussian component, including
every covariance cross term. The original observation law needs no moments
for this bounded-gradient identity. -/
theorem slepian_gaussian_stein
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    (∫ z : Ω × Vector p, f.gradient (slepianPoint W t z) z.2 ∂μ.prod (gaussianLaw A)) =
      Real.sqrt (1 - t) * ∫ z : Ω × Vector p,
        f.hessianTrace (A * A.transpose) (slepianPoint W t z) ∂μ.prod (gaussianLaw A) := by
  have hiZ : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_norm A)
  have hig := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    (slepianPoint W t) Prod.snd (measurable_slepianPoint W hW t) measurable_snd hiZ
  have hiH := f.integrable_hessianTrace (μ.prod (gaussianLaw A))
    (slepianPoint W t) (measurable_slepianPoint W hW t) (A * A.transpose)
  have hs (ω : Ω) :
      (∫ z : Vector p, f.gradient (slepianPoint W t (ω, z)) z ∂gaussianLaw A) =
        Real.sqrt (1 - t) * ∫ z : Vector p,
          f.hessianTrace (A * A.transpose) (slepianPoint W t (ω, z)) ∂gaussianLaw A := by
    have hm : Measurable (fun z : Vector p => slepianPoint W t (ω, z)) := by
      unfold slepianPoint
      fun_prop
    rw [f.integral_hessianTrace_eq _ _ hm]
    simpa only [slepianPoint, add_comm] using
      f.gaussian_gradient_stein A (Real.sqrt (1 - t)) (Real.sqrt t • W ω)
  calc
    _ = ∫ ω, ∫ z : Vector p, f.gradient (slepianPoint W t (ω, z)) z ∂gaussianLaw A ∂μ :=
      integral_prod _ hig
    _ = ∫ ω, Real.sqrt (1 - t) * ∫ z : Vector p,
        f.hessianTrace (A * A.transpose) (slepianPoint W t (ω, z)) ∂gaussianLaw A ∂μ :=
      integral_congr_ae (ae_of_all _ hs)
    _ = Real.sqrt (1 - t) * ∫ ω, ∫ z : Vector p,
        f.hessianTrace (A * A.transpose) (slepianPoint W t (ω, z)) ∂gaussianLaw A ∂μ :=
      integral_const_mul _ _
    _ = _ := congrArg (fun a => Real.sqrt (1 - t) * a) (integral_prod _ hiH).symm

/-- The full initial Slepian derivative in Lemma G.3. The independent
Gaussian has the concrete covariance `A Aᵀ`, with no rank assumption.
A finite first moment of `W` suffices; in particular no zero-skewness or
bounded-observation hypothesis appears. -/
theorem hasDerivAt_slepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (hWnorm : Integrable (fun ω => ‖W ω‖) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ W A)
      ((1 / (2 * Real.sqrt t)) *
        (∫ z : Ω × Vector p, f.gradient (slepianPoint W t z) (W z.1) ∂μ.prod (gaussianLaw A)) -
      (1 / 2 : ℝ) * ∫ z : Ω × Vector p,
        f.hessianTrace (A * A.transpose) (slepianPoint W t z) ∂μ.prod (gaussianLaw A)) t := by
  have hiW : Integrable (fun z : Ω × Vector p => ‖W z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hWnorm.mul_prod (integrable_const (1 : ℝ))
  have hiZ : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_norm A)
  have higW := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    (slepianPoint W t) (fun z => W z.1) (measurable_slepianPoint W hW t)
    (hW.comp measurable_fst) hiW
  have higZ := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    (slepianPoint W t) Prod.snd (measurable_slepianPoint W hW t) measurable_snd hiZ
  have hsplit (z : Ω × Vector p) :
      f.gradient (slepianPoint W t z) (slepianVelocity W t z) =
        (1 / (2 * Real.sqrt t)) * f.gradient (slepianPoint W t z) (W z.1) -
          (1 / (2 * Real.sqrt (1 - t))) * f.gradient (slepianPoint W t z) z.2 := by
    simp only [slepianVelocity, map_sub, map_smul, smul_eq_mul]
  have heq : (∫ z, f.gradient (slepianPoint W t z) (slepianVelocity W t z)
      ∂μ.prod (gaussianLaw A)) =
      (1 / (2 * Real.sqrt t)) * (∫ z : Ω × Vector p,
        f.gradient (slepianPoint W t z) (W z.1) ∂μ.prod (gaussianLaw A)) -
      (1 / 2 : ℝ) * ∫ z : Ω × Vector p,
        f.hessianTrace (A * A.transpose) (slepianPoint W t z) ∂μ.prod (gaussianLaw A) := by
    simp_rw [hsplit]
    rw [integral_sub (higW.const_mul _) (higZ.const_mul _),
      integral_const_mul, integral_const_mul, f.slepian_gaussian_stein μ W hW A t]
    have ha : Real.sqrt (1 - t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    field_simp [ha]
    ring
  rw [← heq]
  exact f.hasDerivAt_slepianExpectation_raw μ W hW hWnorm A ht ht1

/-- Endpoint continuity under the same genuine first moment, so subsequent
time integration does not need to assume limits of the Slepian expectations. -/
theorem continuousOn_slepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (hWnorm : Integrable (fun ω => ‖W ω‖) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ContinuousOn (f.slepianExpectation μ W A) (Set.Icc (0 : ℝ) 1) := by
  have hiW : Integrable (fun z : Ω × Vector p => ‖W z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hWnorm.mul_prod (integrable_const (1 : ℝ))
  have hiZ : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_norm A)
  apply continuousOn_of_dominated (bound := fun z : Ω × Vector p =>
    f.bound * (‖W z.1‖ + ‖z.2‖) + ‖f.value 0‖)
  · intro t _
    exact (f.continuous_value.measurable.comp (measurable_slepianPoint W hW t)).aestronglyMeasurable
  · intro t ht
    apply ae_of_all
    intro z
    apply (f.norm_value_le _).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ f.bound_nonneg
    calc
      _ ≤ Real.sqrt t * ‖W z.1‖ + Real.sqrt (1 - t) * ‖z.2‖ := by
        exact (norm_add_le _ _).trans_eq (by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
      _ ≤ 1 * ‖W z.1‖ + 1 * ‖z.2‖ := add_le_add
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr ht.2) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr (by linarith [ht.1])) (norm_nonneg _))
      _ = _ := by ring
  · exact ((hiW.add hiZ).const_mul f.bound).add (integrable_const _)
  · exact ae_of_all _ (fun z => (f.continuous_value.comp
      (show Continuous (fun t : ℝ => slepianPoint W t z) by unfold slepianPoint; fun_prop)).continuousOn)

theorem slepianExpectation_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    f.slepianExpectation μ W A 0 = ∫ x, f.value x ∂gaussianLaw A := by
  simp only [slepianExpectation, slepianPoint, Real.sqrt_zero, sub_zero,
    Real.sqrt_one, zero_smul, one_smul, zero_add, integral_fun_snd, measureReal_univ_eq_one, one_smul]

theorem slepianExpectation_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    f.slepianExpectation μ W A 1 = ∫ ω, f.value (W ω) ∂μ := by
  simp only [slepianExpectation, slepianPoint, sub_self, Real.sqrt_zero,
    Real.sqrt_one, zero_smul, one_smul, add_zero]
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := μ) (ν := gaussianLaw A) (fun ω => f.value (W ω)))

end C4Test
end
end RectangleCLT.Companion.SplitV4
