import RectangleCLT.GaussianHeat
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-Gaussian interpolation

The path and its derivatives below are literal integrals. Both covariance
factors may be singular.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT
namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

noncomputable def gaussianComparisonPoint (t : ℝ) (z : Vector p × Vector p) : Vector p :=
  Real.sqrt (1 - t) • z.1 + Real.sqrt t • z.2

noncomputable def gaussianComparisonExpectation
    (A B : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : ℝ :=
  ∫ z, s.F (gaussianComparisonPoint t z) ∂(gaussianLaw A).prod (gaussianLaw B)

noncomputable def gaussianComparisonSecond
    (A B : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (j k : Fin p) : ℝ :=
  ∫ z, s.mixedSecondDerivativeF (gaussianComparisonPoint t z) j k
    ∂(gaussianLaw A).prod (gaussianLaw B)

theorem continuous_gaussianComparisonPoint (t : ℝ) :
    Continuous (gaussianComparisonPoint (p := p) t) := by
  unfold gaussianComparisonPoint
  fun_prop

theorem integrable_gaussianComparisonSecond
    (A B : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (j k : Fin p) :
    Integrable (fun z => s.mixedSecondDerivativeF (gaussianComparisonPoint t z) j k)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
  apply (integrable_const (3 / s.bandwidth ^ 2 : ℝ)).mono'
    (((s.continuous_secondDerivative j k).comp
      (continuous_gaussianComparisonPoint t)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => s.norm_secondDerivative_le _ j k)

/-- The exact Stein contraction for a scaled Gaussian plus a fixed shift. -/
theorem gaussianComparison_scaled_stein
    (A : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (r : Vector p) (j : Fin p) :
    (∫ x, x j * s.coordinateDerivativeF (a • x + r) j ∂gaussianLaw A) =
      ∑ k, (A * A.transpose) j k *
        ∫ x, a * s.mixedSecondDerivativeF (a • x + r) j k ∂gaussianLaw A := by
  have hpoint : Continuous (fun x : Vector p => a • x + r) := by fun_prop
  apply gaussianLaw_stein A j
  · intro x l
    have hd := s.hasDerivAt_firstDerivative_line_sum (a • x + r)
      (a • (fun k => A k l)) j 0
    convert hd using 1
    · funext t
      congr 1
      ext k
      simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [line_zero, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
  · exact ((s.continuous_firstDerivative j).comp hpoint).measurable
  · intro k
    exact (continuous_const.mul ((s.continuous_secondDerivative j k).comp hpoint)).measurable
  · exact ⟨1 / s.bandwidth, fun x => by
      simpa only [Real.norm_eq_abs] using s.norm_firstDerivative_le (a • x + r) j⟩
  · refine ⟨|a| * (3 / s.bandwidth ^ 2), fun x k => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using s.norm_secondDerivative_le (a • x + r) j k)
      (abs_nonneg a)

noncomputable def gaussianComparisonVelocity (t : ℝ) (z : Vector p × Vector p) : Vector p :=
  -(1 / (2 * Real.sqrt (1 - t))) • z.1 +
    (1 / (2 * Real.sqrt t)) • z.2

theorem hasDerivAt_gaussianComparisonPoint (z : Vector p × Vector p)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => gaussianComparisonPoint r z)
      (gaussianComparisonVelocity t z) t := by
  have hleft := ((Real.hasDerivAt_sqrt (by linarith : 1 - t ≠ 0)).comp t
    ((hasDerivAt_id t).const_sub 1)).smul_const z.1
  have hright := (Real.hasDerivAt_sqrt (ne_of_gt ht0)).smul_const z.2
  convert hleft.add hright using 1 <;>
    simp [gaussianComparisonPoint, gaussianComparisonVelocity, neg_div]

private theorem abs_gaussianComparison_direction_le
    (x v : Vector p) :
    |∑ j, v j * s.coordinateDerivativeF x j| ≤ ‖v‖ / s.bandwidth := by
  have heq := (s.hasDerivAt_F_line_sum x v 0).unique (s.hasDerivAt_F_line x v 0)
  have h := s.abs_F_line_derivative_le x v 0
  simp only [line_zero] at heq h
  rwa [← heq] at h

/-- Differentiate the actual product Gaussian integral. The domination uses
only the integrable maximum norms of the two Gaussian vectors. -/
theorem hasDerivAt_gaussianComparisonExpectation_raw
    (A B : Matrix (Fin p) (Fin p) ℝ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (s.gaussianComparisonExpectation A B)
      (∫ z, ∑ j, gaussianComparisonVelocity t z j *
        s.coordinateDerivativeF (gaussianComparisonPoint t z) j
        ∂(gaussianLaw A).prod (gaussianLaw B)) t := by
  let ε := min t (1 - t) / 2
  let a := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let b := 1 / (2 * Real.sqrt (t / 2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεt : ε ≤ t / 2 := by
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hε1 : ε ≤ (1 - t) / 2 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlocal {r : ℝ} (hr : r ∈ Metric.ball t ε) :
      t / 2 < r ∧ (1 - t) / 2 < 1 - r := by
    have habs : |r - t| < ε := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hh := abs_lt.mp habs
    constructor <;> linarith
  have hrpos {r : ℝ} (hr : r ∈ Metric.ball t ε) : 0 < r :=
    lt_trans (by positivity : 0 < t / 2) (hlocal hr).1
  have hrone {r : ℝ} (hr : r ∈ Metric.ball t ε) : r < 1 := by
    have := (hlocal hr).2
    linarith
  have hca {r : ℝ} (hr : r ∈ Metric.ball t ε) :
      1 / (2 * Real.sqrt (1 - r)) ≤ a := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlocal hr).2.le) (by norm_num))
  have hcb {r : ℝ} (hr : r ∈ Metric.ball t ε) :
      1 / (2 * Real.sqrt r) ≤ b := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlocal hr).1.le) (by norm_num))
  have hF (r : ℝ) : Continuous
      (fun z : Vector p × Vector p => s.F (gaussianComparisonPoint r z)) :=
    s.continuous_F.comp (continuous_gaussianComparisonPoint r)
  have hD (r : ℝ) : Continuous
      (fun z : Vector p × Vector p => ∑ j, gaussianComparisonVelocity r z j *
        s.coordinateDerivativeF (gaussianComparisonPoint r z) j) := by
    apply continuous_finset_sum
    intro j _
    apply Continuous.mul
    · unfold gaussianComparisonVelocity
      fun_prop
    · exact (s.continuous_firstDerivative j).comp (continuous_gaussianComparisonPoint r)
  have hinormA : Integrable (fun z : Vector p × Vector p => ‖z.1‖)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
    simpa only [mul_one] using
      (gaussianLaw_integrable_norm A).mul_prod (integrable_const (1 : ℝ))
  have hinormB : Integrable (fun z : Vector p × Vector p => ‖z.2‖)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_norm B)
  have hi : Integrable (fun z : Vector p × Vector p =>
      (a * ‖z.1‖ + b * ‖z.2‖) / s.bandwidth)
      ((gaussianLaw A).prod (gaussianLaw B)) :=
    ((hinormA.const_mul a).add (hinormB.const_mul b)).div_const s.bandwidth
  have hbound (z : Vector p × Vector p) (r : ℝ) (hr : r ∈ Metric.ball t ε) :
      ‖∑ j, gaussianComparisonVelocity r z j *
        s.coordinateDerivativeF (gaussianComparisonPoint r z) j‖ ≤
      (a * ‖z.1‖ + b * ‖z.2‖) / s.bandwidth := by
    rw [Real.norm_eq_abs]
    apply (s.abs_gaussianComparison_direction_le _ _).trans
    apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
    calc
      _ ≤ ‖-(1 / (2 * Real.sqrt (1 - r))) • z.1‖ +
          ‖(1 / (2 * Real.sqrt r)) • z.2‖ := norm_add_le _ _
      _ = (1 / (2 * Real.sqrt (1 - r))) * ‖z.1‖ +
          (1 / (2 * Real.sqrt r)) * ‖z.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (hca hr) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hcb hr) (norm_nonneg _))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (gaussianLaw A).prod (gaussianLaw B))
    (bound := fun z : Vector p × Vector p =>
      (a * ‖z.1‖ + b * ‖z.2‖) / s.bandwidth)
    (ε := ε) (F := fun r z => s.F (gaussianComparisonPoint r z))
    (F' := fun r z => ∑ j, gaussianComparisonVelocity r z j *
      s.coordinateDerivativeF (gaussianComparisonPoint r z) j)
    (x₀ := t) hε
    (Filter.Eventually.of_forall (fun r => (hF r).aestronglyMeasurable))
    ((integrable_const (1 : ℝ)).mono' (hF t).aestronglyMeasurable
      (ae_of_all _ (fun z => s.norm_F_le_one _)))
    (hD t).aestronglyMeasurable (ae_of_all _ hbound) hi
    (ae_of_all _ (fun z r hr => s.hasDerivAt_F_curve
      (hasDerivAt_gaussianComparisonPoint z (hrpos hr) (hrone hr))))
  exact hd.2

private theorem integrable_scaled_second_product
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (j k : Fin p) :
    Integrable (fun z : Vector p × Vector p =>
      s.mixedSecondDerivativeF (a • z.1 + b • z.2) j k)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
  have hpoint : Continuous (fun z : Vector p × Vector p => a • z.1 + b • z.2) := by
    fun_prop
  apply (integrable_const (3 / s.bandwidth ^ 2 : ℝ)).mono'
    (((s.continuous_secondDerivative j k).comp hpoint).aestronglyMeasurable)
  exact ae_of_all _ (fun z => s.norm_secondDerivative_le _ j k)

private theorem integrable_scaled_first_coordinate_product
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (j : Fin p) :
    Integrable (fun z : Vector p × Vector p =>
      z.1 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
  have hx : Integrable (fun z : Vector p × Vector p => z.1 j)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
    simpa only [mul_one] using
      (gaussianLaw_integrable_coordinate A j).mul_prod (integrable_const (1 : ℝ))
  have hpoint : Continuous (fun z : Vector p × Vector p => a • z.1 + b • z.2) := by
    fun_prop
  have h := hx.bdd_mul
    (((s.continuous_firstDerivative j).comp hpoint).aestronglyMeasurable)
    ⟨1 / s.bandwidth, fun z => s.norm_firstDerivative_le _ j⟩
  simpa only [mul_comm] using h

private theorem integrable_scaled_second_coordinate_product
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (j : Fin p) :
    Integrable (fun z : Vector p × Vector p =>
      z.2 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
  have hx : Integrable (fun z : Vector p × Vector p => z.2 j)
      ((gaussianLaw A).prod (gaussianLaw B)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ)).mul_prod (gaussianLaw_integrable_coordinate B j)
  have hpoint : Continuous (fun z : Vector p × Vector p => a • z.1 + b • z.2) := by
    fun_prop
  have h := hx.bdd_mul
    (((s.continuous_firstDerivative j).comp hpoint).aestronglyMeasurable)
    ⟨1 / s.bandwidth, fun z => s.norm_firstDerivative_le _ j⟩
  simpa only [mul_comm] using h

/-- Stein contraction in the first of two independent Gaussian vectors. -/
theorem gaussianComparison_first_product_stein
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (j : Fin p) :
    (∫ z : Vector p × Vector p,
      z.1 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j
      ∂(gaussianLaw A).prod (gaussianLaw B)) =
      a * ∑ k, (A * A.transpose) j k *
        ∫ z : Vector p × Vector p,
          s.mixedSecondDerivativeF (a • z.1 + b • z.2) j k
          ∂(gaussianLaw A).prod (gaussianLaw B) := by
  have hDD (k : Fin p) := s.integrable_scaled_second_product A B a b j k
  rw [integral_prod_symm _
    (s.integrable_scaled_first_coordinate_product A B a b j)]
  simp_rw [s.gaussianComparison_scaled_stein A a, integral_const_mul]
  rw [integral_finset_sum Finset.univ
    (fun k _ => ((hDD k).integral_prod_right.const_mul a).const_mul ((A * A.transpose) j k))]
  simp_rw [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_prod_symm _ (hDD k)]
  ring

/-- Stein contraction in the second of two independent Gaussian vectors. -/
theorem gaussianComparison_second_product_stein
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (j : Fin p) :
    (∫ z : Vector p × Vector p,
      z.2 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j
      ∂(gaussianLaw A).prod (gaussianLaw B)) =
      b * ∑ k, (B * B.transpose) j k *
        ∫ z : Vector p × Vector p,
          s.mixedSecondDerivativeF (a • z.1 + b • z.2) j k
          ∂(gaussianLaw A).prod (gaussianLaw B) := by
  have hDD (k : Fin p) := s.integrable_scaled_second_product A B a b j k
  rw [integral_prod _ (s.integrable_scaled_second_coordinate_product A B a b j)]
  have hstein (x : Vector p) :
      (∫ y, y j * s.coordinateDerivativeF (a • x + b • y) j ∂gaussianLaw B) =
        ∑ k, (B * B.transpose) j k *
          ∫ y, b * s.mixedSecondDerivativeF (a • x + b • y) j k ∂gaussianLaw B := by
    simpa only [add_comm] using s.gaussianComparison_scaled_stein B b (a • x) j
  simp_rw [hstein, integral_const_mul]
  rw [integral_finset_sum Finset.univ
    (fun k _ => ((hDD k).integral_prod_left.const_mul b).const_mul ((B * B.transpose) j k))]
  simp_rw [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_prod _ (hDD k)]
  ring

/-- The actual two-covariance heat identity, including singular endpoints. -/
theorem hasDerivAt_gaussianComparisonExpectation
    (A B : Matrix (Fin p) (Fin p) ℝ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (s.gaussianComparisonExpectation A B)
      ((1 / 2 : ℝ) * ∑ j, ∑ k,
        ((B * B.transpose) j k - (A * A.transpose) j k) *
          s.gaussianComparisonSecond A B t j k) t := by
  let a := Real.sqrt (1 - t)
  let b := Real.sqrt t
  let u := 1 / (2 * a)
  let v := 1 / (2 * b)
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith : 0 < 1 - t))
  have hb : b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht0)
  have hiX (j : Fin p) := s.integrable_scaled_first_coordinate_product A B a b j
  have hiY (j : Fin p) := s.integrable_scaled_second_coordinate_product A B a b j
  have hsplit (z : Vector p × Vector p) :
      (∑ j, gaussianComparisonVelocity t z j *
        s.coordinateDerivativeF (gaussianComparisonPoint t z) j) =
      ∑ j, (-u * (z.1 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j) +
        v * (z.2 j * s.coordinateDerivativeF (a • z.1 + b • z.2) j)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [gaussianComparisonVelocity, gaussianComparisonPoint,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [a, b, u, v]
    ring
  have hraw :
      (∫ z, ∑ j, gaussianComparisonVelocity t z j *
        s.coordinateDerivativeF (gaussianComparisonPoint t z) j
        ∂(gaussianLaw A).prod (gaussianLaw B)) =
      (1 / 2 : ℝ) * ∑ j, ∑ k,
        ((B * B.transpose) j k - (A * A.transpose) j k) *
          s.gaussianComparisonSecond A B t j k := by
    simp_rw [hsplit]
    rw [integral_finset_sum Finset.univ
      (fun j _ => ((hiX j).const_mul (-u)).add ((hiY j).const_mul v))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_add ((hiX j).const_mul (-u)) ((hiY j).const_mul v),
      integral_const_mul, integral_const_mul,
      s.gaussianComparison_first_product_stein A B a b,
      s.gaussianComparison_second_product_stein A B a b]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    change -u * (a * ((A * A.transpose) j k *
      s.gaussianComparisonSecond A B t j k)) +
      v * (b * ((B * B.transpose) j k *
        s.gaussianComparisonSecond A B t j k)) = _
    dsimp [u, v]
    field_simp [ha, hb]
    ring
  rw [← hraw]
  exact s.hasDerivAt_gaussianComparisonExpectation_raw A B ht0 ht1

theorem continuous_gaussianComparisonExpectation
    (A B : Matrix (Fin p) (Fin p) ℝ) :
    Continuous (s.gaussianComparisonExpectation A B) := by
  unfold gaussianComparisonExpectation
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (F := fun t : ℝ => fun z : Vector p × Vector p =>
      s.F (gaussianComparisonPoint t z))
  · intro t
    exact (s.continuous_F.comp (continuous_gaussianComparisonPoint t)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun z => s.norm_F_le_one _)
  · exact integrable_const _
  · filter_upwards [] with z
    apply s.continuous_F.comp
    unfold gaussianComparisonPoint
    fun_prop

theorem gaussianComparisonExpectation_zero
    (A B : Matrix (Fin p) (Fin p) ℝ) :
    s.gaussianComparisonExpectation A B 0 = ∫ x, s.F x ∂gaussianLaw A := by
  simp only [gaussianComparisonExpectation, gaussianComparisonPoint, sub_zero,
    Real.sqrt_one, Real.sqrt_zero, one_smul, zero_smul, add_zero,
    integral_fun_fst, measureReal_univ_eq_one]

theorem gaussianComparisonExpectation_one
    (A B : Matrix (Fin p) (Fin p) ℝ) :
    s.gaussianComparisonExpectation A B 1 = ∫ x, s.F x ∂gaussianLaw B := by
  simp only [gaussianComparisonExpectation, gaussianComparisonPoint, sub_self,
    Real.sqrt_one, Real.sqrt_zero, one_smul, zero_smul, zero_add,
    integral_fun_snd, measureReal_univ_eq_one]

end FaceSmoother
end RectangleCLT
