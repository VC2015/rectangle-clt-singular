import RectangleCLT.BoundedMaximum
import RectangleCLT.GaussianCurvature
import RectangleCLT.SmootherStability
import RectangleCLT.IndependentCovariance
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Expected curvature for actual bounded independent centered observations.
The leave-one-out argument uses actual gradient derivatives and covariance
stability, followed by independence of one observation from the remaining sum. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

/-- The actual sum with one observation removed. -/
def leaveOneOut {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (ω : Ω) : Vector p := ∑ l ∈ Finset.univ.erase i, ξ l ω

theorem sumVector_eq_leaveOneOut_add {Ω : Type u} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (ω : Ω) :
    sumVector ξ ω = leaveOneOut ξ i ω + ξ i ω := by
  exact (Finset.sum_erase_add Finset.univ (fun l => ξ l ω) (Finset.mem_univ i)).symm

namespace FaceWeights

/-- Coordinate expansion of the positive covariance quadratic form. -/
theorem directionalCovariance_eq_double_sum {p : ℕ} (w : FaceWeights p)
    (y : Vector p) :
    w.directionalCovariance y = ∑ j, ∑ k, (y j * y k) * w.covarianceEntry j k := by
  have hrow (j : Fin p) :
      (∑ k, (y j * y k) * w.covarianceEntry j k) =
        w.coordinateMass j * y j ^ 2 - (w.v j * y j) * w.directionalMean y := by
    calc
      _ = y j * ∑ k, y k * w.covarianceEntry j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [w.covarianceEntry_mul_sum]; ring
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← w.directionalMean_eq]
  simp only [directionalCovariance, w.directionalSecondMoment_eq, coordinateMass]
  ring

/-- Integrating the actual directional quadratic form gives contraction with
the actual second-moment matrix. -/
theorem integral_directionalCovariance {Ω : Type u} [MeasurableSpace Ω]
    {p : ℕ} {μ : Measure Ω} (w : FaceWeights p) {Y : Ω → Vector p}
    (hprod : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ) :
    (∫ ω, w.directionalCovariance (Y ω) ∂μ) =
      w.covarianceContraction (fun j k => ∫ ω, Y ω j * Y ω k ∂μ) := by
  simp_rw [w.directionalCovariance_eq_double_sum]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (hprod j k).mul_const _))]
  unfold covarianceContraction
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => (hprod j k).mul_const _)]
  simp only [integral_mul_const]

theorem integrable_directionalCovariance {Ω : Type u} [MeasurableSpace Ω]
    {p : ℕ} {μ : Measure Ω} (w : FaceWeights p) {Y : Ω → Vector p}
    (hprod : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ) :
    Integrable (fun ω => w.directionalCovariance (Y ω)) μ := by
  simp_rw [w.directionalCovariance_eq_double_sum]
  exact integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (hprod j k).mul_const _))

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem continuous_covarianceEntry (j k : Fin p) :
    Continuous (fun x => (s.weights x).covarianceEntry j k) :=
  (s.continuous_diagonalMass j k).sub ((s.continuous_v j).mul (s.continuous_v k))

theorem integrable_covarianceEntry {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {W : Ω → Vector p}
    (hW : Measurable W) (j k : Fin p) :
    Integrable (fun ω => (s.weights (W ω)).covarianceEntry j k) μ := by
  apply (integrable_const (2 : ℝ)).mono'
    (((s.continuous_covarianceEntry j k).measurable.comp hW).aestronglyMeasurable)
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using (s.weights (W ω)).abs_covarianceEntry_le_two j k

theorem integrable_v {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {W : Ω → Vector p}
    (hW : Measurable W) (j : Fin p) : Integrable (fun ω => s.v (W ω) j) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((s.continuous_v j).measurable.comp hW).aestronglyMeasurable)
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, v] using (s.weights (W ω)).abs_v_le_one j

theorem integrable_contraction {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {W : Ω → Vector p}
    (hW : Measurable W) (Q : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun ω => (s.weights (W ω)).covarianceContraction Q) μ :=
  integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (s.integrable_covarianceEntry hW j k).const_mul (Q j k)))

theorem integrable_kappa {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {W : Ω → Vector p}
    (hW : Measurable W) : Integrable (fun ω => s.kappa (W ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((s.continuous_kappa.measurable.comp hW).aestronglyMeasurable)
  exact ae_of_all _ fun ω => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, kappa,
      abs_of_nonneg (s.weights (W ω)).kappa_nonneg] using (s.weights (W ω)).kappa_le_one

theorem integral_kappa_le_one {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Vector p}
    (hW : Measurable W) : (∫ ω, s.kappa (W ω) ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫ _ω : Ω, (1 : ℝ) ∂μ := integral_mono (s.integrable_kappa hW)
      (integrable_const _) (fun ω => (s.weights (W ω)).kappa_le_one)
    _ = _ := by simp

/-- Covariance stability may be contracted with the actual second moments
of any vector. This preserves positivity without an entrywise Hessian claim. -/
theorem momentContraction_shift_le {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → Vector p}
    (hprod : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ)
    (x : Vector p) {z : Vector p} {δ : ℝ} (hz : ‖z‖ ≤ δ) :
    (s.weights (x + z)).covarianceContraction
        (fun j k => ∫ ω, Y ω j * Y ω k ∂μ) ≤
      Real.exp (2 * δ / s.bandwidth) * (s.weights x).covarianceContraction
        (fun j k => ∫ ω, Y ω j * Y ω k ∂μ) := by
  rw [← FaceWeights.integral_directionalCovariance _ hprod,
    ← FaceWeights.integral_directionalCovariance _ hprod, ← integral_const_mul]
  exact integral_mono ((s.weights (x + z)).integrable_directionalCovariance hprod)
    (((s.weights x).integrable_directionalCovariance hprod).const_mul _)
    (fun ω => s.directionalCovariance_shift_le x (Y ω) hz)

theorem momentContraction_shift_lower {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → Vector p}
    (hprod : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ)
    (x : Vector p) {z : Vector p} {δ : ℝ} (hz : ‖z‖ ≤ δ) :
    Real.exp (-2 * δ / s.bandwidth) *
        (s.weights (x + z)).covarianceContraction
          (fun j k => ∫ ω, Y ω j * Y ω k ∂μ) ≤
      (s.weights x).covarianceContraction
        (fun j k => ∫ ω, Y ω j * Y ω k ∂μ) := by
  have hh := mul_le_mul_of_nonneg_left (s.momentContraction_shift_le hprod x hz)
    (Real.exp_nonneg (-2 * δ / s.bandwidth))
  have he : Real.exp (-2 * δ / s.bandwidth) * Real.exp (2 * δ / s.bandwidth) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  simpa only [← mul_assoc, he, one_mul] using hh

/-- The actual potential gradient increment controls its positive Hessian
quadratic form at the initial point. A mean-value argument avoids introducing
an additional integration parameter. -/
theorem gradient_increment_ge (x y : Vector p) {δ : ℝ} (hy : ‖y‖ ≤ δ) :
    Real.exp (-2 * δ / s.bandwidth) / s.bandwidth *
        (s.weights x).directionalCovariance y ≤
      ∑ j, y j * (s.v (x + y) j - s.v x j) := by
  let f := fun t => (s.weights (line x y t)).directionalMean y
  let f' := fun t => (s.weights (line x y t)).directionalCovariance y / s.bandwidth
  have hderiv (t : ℝ) : HasDerivAt f (f' t) t := s.hasDerivAt_directionalMean_line x y t
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f f' (by norm_num : (0 : ℝ) < 1)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => hderiv t)
  have hz : ‖t • y‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    calc
      t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
      _ ≤ δ := by simpa using hy
  have hstable := (s.directionalCovariance_stability x y hz).1
  have hbound := div_le_div_of_nonneg_right hstable s.bandwidth_pos.le
  have hline : line x y t = x + t • y := rfl
  rw [← hline] at hbound
  change (Real.exp (-2 * δ / s.bandwidth) *
    (s.weights x).directionalCovariance y) / s.bandwidth ≤ f' t at hbound
  rw [heq] at hbound
  have hzero : line x y 0 = x := line_zero _ _
  have hone : line x y 1 = x + y := by ext j; simp [line]
  have hmeans : f 1 - f 0 = ∑ j, y j * (s.v (x + y) j - s.v x j) := by
    dsimp [f]
    rw [hone, hzero, FaceWeights.directionalMean_eq, FaceWeights.directionalMean_eq,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [v]; ring)
  simpa only [sub_zero, div_one, hmeans, div_mul_eq_mul_div] using hbound

end FaceSmoother

namespace BoundedIndependentHypotheses

variable {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

omit [IsProbabilityMeasure μ] in
theorem measurable_leaveOneOut (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) :
    Measurable (leaveOneOut ξ i) :=
  Finset.measurable_sum _ (fun l _ => h.measurable l)

omit [IsProbabilityMeasure μ] in
theorem indepFun_leaveOneOut (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) :
    IndepFun (ξ i) (leaveOneOut ξ i) μ := by
  have hh := (h.independent.indepFun_finset_sum_of_not_mem h.measurable
    (Finset.not_mem_erase i Finset.univ)).symm
  convert hh using 1
  funext ω
  simp only [leaveOneOut, Finset.sum_apply]

theorem integrable_coordinate_pair (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (j k : Fin p) : Integrable (fun ω => ξ i ω j * ξ i ω k) μ := by
  apply (integrable_const (δ ^ 2)).mono'
    ((((measurable_pi_apply j).comp (h.measurable i)).mul
      ((measurable_pi_apply k).comp (h.measurable i))).aestronglyMeasurable)
  filter_upwards [h.abs_coordinate_le i j, h.abs_coordinate_le i k] with ω hj hk
  simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
    mul_le_mul hj hk (abs_nonneg _) h.delta_nonneg

theorem integrable_coordinate_v (h : BoundedIndependentHypotheses μ ξ δ)
    (s : FaceSmoother p) (i : Fin n) (j : Fin p) {W : Ω → Vector p}
    (hW : Measurable W) : Integrable (fun ω => ξ i ω j * s.v (W ω) j) μ := by
  have hi : Integrable (fun ω => ξ i ω j) μ := by
    simpa only [pow_one] using
      integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
  have hh := hi.bdd_mul (((s.continuous_v j).measurable.comp hW).aestronglyMeasurable)
    ⟨1, fun ω => by
      simpa only [Real.norm_eq_abs] using (s.weights (W ω)).abs_v_le_one j⟩
  simpa only [mul_comm] using hh

theorem integrable_coordinate_pair_covarianceEntry
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (i : Fin n) (j k : Fin p) {W : Ω → Vector p} (hW : Measurable W) :
    Integrable (fun ω => (ξ i ω j * ξ i ω k) *
      (s.weights (W ω)).covarianceEntry j k) μ := by
  have hh := (h.integrable_coordinate_pair i j k).bdd_mul
    (((s.continuous_covarianceEntry j k).measurable.comp hW).aestronglyMeasurable)
    ⟨2, fun ω => by
      simpa only [Real.norm_eq_abs] using (s.weights (W ω)).abs_covarianceEntry_le_two j k⟩
  simpa only [mul_comm] using hh

/-- The centered observation is independent of the actual remaining sum,
so its contribution at the unperturbed gradient has expectation zero. -/
theorem integral_leaveOneOut_coordinate_v_eq_zero
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (i : Fin n) (j : Fin p) (r : Vector p) :
    (∫ ω, ξ i ω j * s.v (leaveOneOut ξ i ω + r) j ∂μ) = 0 := by
  have hW : Measurable (fun ω => leaveOneOut ξ i ω + r) :=
    (h.measurable_leaveOneOut i).add measurable_const
  have hψ : Measurable (fun x : Vector p => s.v (x + r) j) :=
    ((s.continuous_v j).comp (continuous_id.add continuous_const)).measurable
  have hind := (h.indepFun_leaveOneOut i).comp (measurable_pi_apply j) hψ
  have hi : Integrable (fun ω => ξ i ω j) μ := by
    simpa only [pow_one] using
      integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
  have hh := hind.integral_mul_of_integrable hi (s.integrable_v hW j)
  change (∫ ω, ξ i ω j * s.v (leaveOneOut ξ i ω + r) j ∂μ) =
    (∫ ω, ξ i ω j ∂μ) * (∫ ω, s.v (leaveOneOut ξ i ω + r) j ∂μ) at hh
  simpa only [h.centered i j, zero_mul] using hh

/-- Independence factors the quadratic directional term against the actual
second-moment matrix of the removed observation. -/
theorem integral_leaveOneOut_directionalCovariance
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (i : Fin n) (r : Vector p) :
    (∫ ω, (s.weights (leaveOneOut ξ i ω + r)).directionalCovariance (ξ i ω) ∂μ) =
      ∫ ω, (s.weights (leaveOneOut ξ i ω + r)).covarianceContraction
        (fun j k => ∫ ω', ξ i ω' j * ξ i ω' k ∂μ) ∂μ := by
  have hW : Measurable (fun ω => leaveOneOut ξ i ω + r) :=
    (h.measurable_leaveOneOut i).add measurable_const
  have hterm (j k : Fin p) := h.integrable_coordinate_pair_covarianceEntry s i j k hW
  have hC (j k : Fin p) : Integrable
      (fun ω => (s.weights (leaveOneOut ξ i ω + r)).covarianceEntry j k) μ :=
    s.integrable_covarianceEntry hW j k
  simp_rw [FaceWeights.directionalCovariance_eq_double_sum,
    FaceWeights.covarianceContraction]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hterm j k)),
    integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (hC j k).const_mul _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => hterm j k),
    integral_finset_sum Finset.univ (fun k _ => (hC j k).const_mul _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  have hψ : Measurable (fun x : Vector p => (s.weights (x + r)).covarianceEntry j k) :=
    ((s.continuous_covarianceEntry j k).comp
      (continuous_id.add continuous_const)).measurable
  have hind := (h.indepFun_leaveOneOut i).comp
    ((measurable_pi_apply j).mul (measurable_pi_apply k)) hψ
  exact hind.integral_mul_of_integrable (h.integrable_coordinate_pair i j k) (hC j k)

/-- One leave-one-out contribution dominates the expected contraction at the
unperturbed remaining sum. All random-vector independence is discharged. -/
theorem integral_coordinate_dot_v_ge_leaveOneOut
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (i : Fin n) (r : Vector p) :
    Real.exp (-2 * δ / s.bandwidth) / s.bandwidth *
        (∫ ω, (s.weights (leaveOneOut ξ i ω + r)).covarianceContraction
          (fun j k => ∫ ω', ξ i ω' j * ξ i ω' k ∂μ) ∂μ) ≤
      ∫ ω, ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j ∂μ := by
  have hW : Measurable (fun ω => leaveOneOut ξ i ω + r) :=
    (h.measurable_leaveOneOut i).add measurable_const
  have hS : Measurable (fun ω => sumVector ξ ω + r) := h.measurable_sum.add measurable_const
  have hfull : Integrable (fun ω => ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j) μ :=
    integrable_finset_sum Finset.univ (fun j _ => h.integrable_coordinate_v s i j hS)
  have hbase : Integrable (fun ω => ∑ j, ξ i ω j * s.v (leaveOneOut ξ i ω + r) j) μ :=
    integrable_finset_sum Finset.univ (fun j _ => h.integrable_coordinate_v s i j hW)
  have hdifference : Integrable (fun ω => ∑ j, ξ i ω j *
      (s.v (sumVector ξ ω + r) j - s.v (leaveOneOut ξ i ω + r) j)) μ := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    exact hfull.sub hbase
  have hquadratic : Integrable (fun ω =>
      (s.weights (leaveOneOut ξ i ω + r)).directionalCovariance (ξ i ω)) μ := by
    simp_rw [FaceWeights.directionalCovariance_eq_double_sum]
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        h.integrable_coordinate_pair_covarianceEntry s i j k hW))
  have hpwise : ∀ᵐ ω ∂μ,
      Real.exp (-2 * δ / s.bandwidth) / s.bandwidth *
          (s.weights (leaveOneOut ξ i ω + r)).directionalCovariance (ξ i ω) ≤
        ∑ j, ξ i ω j *
          (s.v (sumVector ξ ω + r) j - s.v (leaveOneOut ξ i ω + r) j) := by
    filter_upwards [h.bounded i] with ω hω
    have hh := s.gradient_increment_ge (leaveOneOut ξ i ω + r) (ξ i ω) hω
    have harg : leaveOneOut ξ i ω + r + ξ i ω = sumVector ξ ω + r := by
      rw [sumVector_eq_leaveOneOut_add ξ i ω]
      exact add_right_comm _ _ _
    simpa only [harg] using hh
  have hh := integral_mono_ae (hquadratic.const_mul _) hdifference hpwise
  rw [integral_const_mul, h.integral_leaveOneOut_directionalCovariance s i r] at hh
  have hzero : (∫ ω, ∑ j, ξ i ω j * s.v (leaveOneOut ξ i ω + r) j ∂μ) = 0 := by
    rw [integral_finset_sum Finset.univ (fun j _ => h.integrable_coordinate_v s i j hW)]
    simp_rw [h.integral_leaveOneOut_coordinate_v_eq_zero s i]
    simp
  simpa only [mul_sub, Finset.sum_sub_distrib, integral_sub hfull hbase,
    hzero, sub_zero] using hh

/-- A second positive-quadratic-form comparison transfers the contraction
back to the full sum. The resulting exponent four improves the paper's eight. -/
theorem integral_coordinate_dot_v_ge_full
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (i : Fin n) (r : Vector p) :
    Real.exp (-4 * δ / s.bandwidth) / s.bandwidth *
        (∫ ω, (s.weights (sumVector ξ ω + r)).covarianceContraction
          (fun j k => ∫ ω', ξ i ω' j * ξ i ω' k ∂μ) ∂μ) ≤
      ∫ ω, ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j ∂μ := by
  let Q := fun j k => ∫ ω', ξ i ω' j * ξ i ω' k ∂μ
  have hW : Measurable (fun ω => leaveOneOut ξ i ω + r) :=
    (h.measurable_leaveOneOut i).add measurable_const
  have hS : Measurable (fun ω => sumVector ξ ω + r) := h.measurable_sum.add measurable_const
  have hpwise : ∀ᵐ ω ∂μ,
      Real.exp (-2 * δ / s.bandwidth) *
        (s.weights (sumVector ξ ω + r)).covarianceContraction Q ≤
      (s.weights (leaveOneOut ξ i ω + r)).covarianceContraction Q := by
    filter_upwards [h.bounded i] with ω hω
    have hh := s.momentContraction_shift_lower (h.integrable_coordinate_pair i)
      (leaveOneOut ξ i ω + r) hω
    have harg : leaveOneOut ξ i ω + r + ξ i ω = sumVector ξ ω + r := by
      rw [sumVector_eq_leaveOneOut_add ξ i ω]
      exact add_right_comm _ _ _
    simpa only [harg] using hh
  have hcompare := integral_mono_ae
    ((s.integrable_contraction (μ := μ) hS Q).const_mul _)
    (s.integrable_contraction hW Q) hpwise
  rw [integral_const_mul] at hcompare
  have he : Real.exp (-2 * δ / s.bandwidth) * Real.exp (-2 * δ / s.bandwidth) =
      Real.exp (-4 * δ / s.bandwidth) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-2 * δ / s.bandwidth) / s.bandwidth) *
        (Real.exp (-2 * δ / s.bandwidth) *
          ∫ ω, (s.weights (sumVector ξ ω + r)).covarianceContraction Q ∂μ) := by
      rw [← he]
      dsimp only [Q]
      ring
    _ ≤ (Real.exp (-2 * δ / s.bandwidth) / s.bandwidth) *
        (∫ ω, (s.weights (leaveOneOut ξ i ω + r)).covarianceContraction Q ∂μ) :=
      mul_le_mul_of_nonneg_left hcompare (div_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le)
    _ ≤ _ := h.integral_coordinate_dot_v_ge_leaveOneOut s i r

/-- Actual bounded-array leave-one-out identity and comparison, with every
observation's covariance contribution summed back to the sum covariance. -/
theorem integral_dot_v_ge_covariance_contraction
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p) (r : Vector p) :
    Real.exp (-4 * δ / s.bandwidth) / s.bandwidth *
        (∫ ω, (s.weights (sumVector ξ ω + r)).covarianceContraction
          (covariance μ (sumVector ξ)) ∂μ) ≤
      ∫ ω, ∑ j, sumVector ξ ω j * s.v (sumVector ξ ω + r) j ∂μ := by
  let Q := fun (i : Fin n) j k => ∫ ω, ξ i ω j * ξ i ω k ∂μ
  have hS : Measurable (fun ω => sumVector ξ ω + r) := h.measurable_sum.add measurable_const
  have hC (i : Fin n) := s.integrable_contraction (μ := μ) hS (Q i)
  have hdot (i : Fin n) : Integrable
      (fun ω => ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j) μ :=
    integrable_finset_sum Finset.univ (fun j _ => h.integrable_coordinate_v s i j hS)
  have hsum (x : Vector p) :
      (∑ i, (s.weights x).covarianceContraction (Q i)) =
        (s.weights x).covarianceContraction (covariance μ (sumVector ξ)) := by
    dsimp [Q]
    unfold FaceWeights.covarianceContraction
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← h.covariance_sum j]
  have hdot_sum (ω : Ω) :
      (∑ i, ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j) =
        ∑ j, sumVector ξ ω j * s.v (sumVector ξ ω + r) j := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sumVector, Finset.sum_apply]
  calc
    _ = ∑ i : Fin n, Real.exp (-4 * δ / s.bandwidth) / s.bandwidth *
        ∫ ω, (s.weights (sumVector ξ ω + r)).covarianceContraction (Q i) ∂μ := by
      rw [← Finset.mul_sum, ← integral_finset_sum Finset.univ (fun i _ => hC i)]
      simp_rw [hsum]
    _ ≤ ∑ i : Fin n, ∫ ω, ∑ j, ξ i ω j * s.v (sumVector ξ ω + r) j ∂μ :=
      Finset.sum_le_sum (fun i _ => h.integral_coordinate_dot_v_ge_full s i r)
    _ = _ := by
      rw [← integral_finset_sum Finset.univ (fun i _ => hdot i)]
      simp_rw [hdot_sum]

/-- Expected curvature controlled by the actual expected maximum of the
bounded independent sum. The shift is arbitrary and deterministic. -/
theorem integral_kappa_le_norm
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p) (r : Vector p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hc : 0 < pairGap (covariance μ (sumVector ξ))) :
    (∫ ω, s.kappa (sumVector ξ ω + r) ∂μ) ≤
      Real.exp (4 * δ / s.bandwidth) * s.bandwidth /
        pairGap (covariance μ (sumVector ξ)) * (∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
  let Q := covariance μ (sumVector ξ)
  have hS : Measurable (fun ω => sumVector ξ ω + r) := h.measurable_sum.add measurable_const
  have hgap : pairGap Q * (∫ ω, s.kappa (sumVector ξ ω + r) ∂μ) ≤
      ∫ ω, (s.weights (sumVector ξ ω + r)).covarianceContraction Q ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono ((s.integrable_kappa hS).const_mul _)
      (s.integrable_contraction hS Q) (fun ω =>
        (s.weights (sumVector ξ ω + r)).covarianceContraction_ge_pairGap Q hunit)
  have hdot : Integrable
      (fun ω => ∑ j, sumVector ξ ω j * s.v (sumVector ξ ω + r) j) μ := by
    apply integrable_finset_sum Finset.univ
    intro j _
    have hi : Integrable (fun ω => sumVector ξ ω j) μ :=
      h.integrable_norm_sum.mono'
        (((measurable_pi_apply j).comp h.measurable_sum).aestronglyMeasurable)
        (ae_of_all _ fun ω => norm_le_pi_norm (sumVector ξ ω) j)
    have hh := hi.bdd_mul (((s.continuous_v j).measurable.comp hS).aestronglyMeasurable)
      ⟨1, fun ω => by
        simpa only [Real.norm_eq_abs] using (s.weights (sumVector ξ ω + r)).abs_v_le_one j⟩
    simpa only [mul_comm] using hh
  have hnorm : (∫ ω, ∑ j, sumVector ξ ω j * s.v (sumVector ξ ω + r) j ∂μ) ≤
      ∫ ω, ‖sumVector ξ ω‖ ∂μ :=
    integral_mono hdot h.integrable_norm_sum
      (fun ω => s.coordinate_dot_v_le_norm (sumVector ξ ω) (sumVector ξ ω + r))
  have hbound := (mul_le_mul_of_nonneg_left hgap
    (div_nonneg (Real.exp_nonneg (-4 * δ / s.bandwidth)) s.bandwidth_pos.le)).trans
      ((h.integral_dot_v_ge_covariance_contraction s r).trans hnorm)
  have he : Real.exp (4 * δ / s.bandwidth) * Real.exp (-4 * δ / s.bandwidth) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  calc
    _ = (Real.exp (4 * δ / s.bandwidth) * s.bandwidth / pairGap Q) *
        (Real.exp (-4 * δ / s.bandwidth) / s.bandwidth *
          (pairGap Q * ∫ ω, s.kappa (sumVector ξ ω + r) ∂μ)) := by
      field_simp [ne_of_gt hc, ne_of_gt s.bandwidth_pos]
      simp only [neg_mul] at he
      have hm := congrArg (fun a : ℝ => a * s.bandwidth * pairGap Q *
        (∫ ω, s.kappa (sumVector ξ ω + r) ∂μ)) he
      nlinarith only [hm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound
      (div_nonneg (mul_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le) hc.le)

/-- The bounded expected-curvature estimate with a universal explicit
constant. It needs only the pair gap, not a positive full-matrix eigenvalue. -/
theorem integral_kappa_le
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p) (r : Vector p)
    (hp : 1 ≤ p) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hc : 0 < pairGap (covariance μ (sumVector ξ))) (hband : δ ≤ s.bandwidth) :
    (∫ ω, s.kappa (sumVector ξ ω + r) ∂μ) ≤
      (4 * Real.exp 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) := by
  let c := pairGap (covariance μ (sumVector ξ))
  let a := Real.sqrt (dimensionLog p)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hL : 0 ≤ dimensionLog p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (log_exp_mul_nat_ge_one hp)
  have ha2 : a ^ 2 = dimensionLog p := Real.sq_sqrt hL
  have he : Real.exp (4 * δ / s.bandwidth) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ s.bandwidth_pos).mpr
    nlinarith
  by_cases hsmall : δ * a ≤ 1
  · have hδL : δ * dimensionLog p ≤ a := by
      calc
        _ = (δ * a) * a := by rw [← ha2]; ring
        _ ≤ 1 * a := mul_le_mul_of_nonneg_right hsmall ha
        _ = a := one_mul _
    have hmax : (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤ 4 * a :=
      (h.integral_norm_sum_le hp hunit).trans (by change 2 * a + 2 * δ * dimensionLog p ≤ _; nlinarith)
    have hcoef : Real.exp (4 * δ / s.bandwidth) * s.bandwidth / c ≤
        Real.exp 4 * s.bandwidth / c :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he s.bandwidth_pos.le) hc.le
    calc
      _ ≤ Real.exp (4 * δ / s.bandwidth) * s.bandwidth / c *
          (∫ ω, ‖sumVector ξ ω‖ ∂μ) := h.integral_kappa_le_norm s r hunit hc
      _ ≤ (Real.exp 4 * s.bandwidth / c) * (4 * a) :=
        mul_le_mul hcoef hmax (integral_nonneg (fun _ => norm_nonneg _))
          (div_nonneg (mul_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le) hc.le)
      _ = _ := by ring
  · have hlarge : 1 ≤ s.bandwidth * a :=
      (le_of_lt (lt_of_not_ge hsmall)).trans (mul_le_mul_of_nonneg_right hband ha)
    have hconstant : 1 ≤ 4 * Real.exp 4 := by
      have he4 : 1 ≤ Real.exp (4 : ℝ) := Real.one_le_exp (by norm_num)
      nlinarith
    have htarget : 1 ≤ (4 * Real.exp 4) * s.bandwidth * a / c := by
      apply (le_div_iff₀ hc).mpr
      have hh := mul_le_mul_of_nonneg_right hconstant (mul_nonneg s.bandwidth_pos.le ha)
      have hcle : c ≤ 1 := pairGap_le_one _
      nlinarith
    exact (s.integral_kappa_le_one (μ := μ)
      (h.measurable_sum.add measurable_const)).trans htarget

/-- An arbitrary independent shift is represented by its probability law.
Its moments need not exist, since the smoother curvature is bounded. -/
theorem integral_kappa_independent_shift_le
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (hp : 1 ≤ p) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hc : 0 < pairGap (covariance μ (sumVector ξ))) (hband : δ ≤ s.bandwidth) :
    (∫ z : Ω × Vector p, s.kappa (sumVector ξ z.1 + z.2) ∂μ.prod ν) ≤
      (4 * Real.exp 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) := by
  have hW : Measurable (fun z : Ω × Vector p => sumVector ξ z.1 + z.2) :=
    (h.measurable_sum.comp measurable_fst).add measurable_snd
  have hi := s.integrable_kappa (μ := μ.prod ν) hW
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _r : Vector p, (4 * Real.exp 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) ∂ν :=
      integral_mono_ae hi.integral_prod_right (integrable_const _)
        (ae_of_all _ (fun r => h.integral_kappa_le s r hp hunit hc hband))
    _ = _ := by simp

end BoundedIndependentHypotheses
end RectangleCLT
