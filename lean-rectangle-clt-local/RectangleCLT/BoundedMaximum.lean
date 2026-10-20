import RectangleCLT.GaussianMaximum
import RectangleCLT.LocalMoments

/-! A variance-sensitive expected maximum estimate for the actual sum of
independent centered bounded observations. Exponential moments are proved
from the scalar Taylor bound and independence, rather than assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

theorem integrable_exp_mul_of_abs_le {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {δ : ℝ}
    (hf : Measurable f) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ δ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * f ω)) μ := by
  apply (integrable_const (Real.exp (|t| * δ))).mono'
    (hf.const_mul t).exp.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * f ω ≤ |t * f ω| := le_abs_self _
    _ = |t| * |f ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- A centered variable has the variance-sensitive exponential bound in the
range where its tilted envelope is at most one. -/
theorem mgf_le_exp_second_moment_of_bounded
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {δ t : ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (hf2 : Integrable (fun ω => (f ω) ^ 2) μ)
    (hcenter : (∫ ω, f ω ∂μ) = 0) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ δ)
    (ht : |t| * δ ≤ 1) :
    mgf f μ t ≤ Real.exp (t ^ 2 * ∫ ω, (f ω) ^ 2 ∂μ) := by
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (t * f ω) ≤ 1 + t * f ω + t ^ 2 * (f ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hu : |t * f ω| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans ht
    have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hu)).2
    nlinarith
  have hipoly : Integrable (fun ω => 1 + t * f ω + t ^ 2 * (f ω) ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hfi.const_mul t)).add (hf2.const_mul _)
  calc
    _ ≤ ∫ ω, 1 + t * f ω + t ^ 2 * (f ω) ^ 2 ∂μ :=
      integral_mono_ae (integrable_exp_mul_of_abs_le hf hbound t) hipoly hpoint
    _ = 1 + t ^ 2 * ∫ ω, (f ω) ^ 2 ∂μ := by
      have hi1 : Integrable (fun ω => 1 + t * f ω) μ :=
        (integrable_const (1 : ℝ)).add (hfi.const_mul t)
      rw [integral_add hi1 (hf2.const_mul (t ^ 2)),
        integral_add (integrable_const (1 : ℝ)) (hfi.const_mul t)]
      simp only [integral_const_mul, hcenter, mul_zero, add_zero,
        integral_const, measureReal_univ_eq_one, one_smul]
    _ ≤ _ := by linarith [Real.add_one_le_exp (t ^ 2 * ∫ ω, (f ω) ^ 2 ∂μ)]

namespace BoundedIndependentHypotheses

variable {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

omit [IsProbabilityMeasure μ] in
theorem measurable_sum (h : BoundedIndependentHypotheses μ ξ δ) :
    Measurable (sumVector ξ) := by
  exact Finset.measurable_sum Finset.univ fun i _ => h.measurable i

omit [IsProbabilityMeasure μ] in
theorem sum_norm_bound (h : BoundedIndependentHypotheses μ ξ δ) :
    ∀ᵐ ω ∂μ, ‖sumVector ξ ω‖ ≤ (n : ℝ) * δ := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, ‖ξ i ω‖ ≤ δ := ae_all_iff.mpr h.bounded
  filter_upwards [hall] with ω hω
  calc
    _ ≤ ∑ i, ‖ξ i ω‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hω i
    _ = _ := by simp

theorem integrable_norm_sum (h : BoundedIndependentHypotheses μ ξ δ) :
    Integrable (fun ω => ‖sumVector ξ ω‖) μ := by
  apply (integrable_const ((n : ℝ) * δ)).mono'
    h.measurable_sum.norm.aestronglyMeasurable
  simpa only [Real.norm_eq_abs, abs_norm] using h.sum_norm_bound

theorem integrable_exp_norm_sum (h : BoundedIndependentHypotheses μ ξ δ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * ‖sumVector ξ ω‖)) μ :=
  integrable_exp_mul_of_abs_le h.measurable_sum.norm
    (by simpa only [abs_norm] using h.sum_norm_bound) t

/-- The coordinate MGF uses the actual normalized sum of second moments. -/
theorem mgf_coordinate_sum_le (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (j : Fin p) {t : ℝ} (ht : |t| * δ ≤ 1) :
    mgf (fun ω => sumVector ξ ω j) μ t ≤ Real.exp (t ^ 2) := by
  classical
  have hmeas (i : Fin n) : Measurable (fun ω => ξ i ω j) :=
    (measurable_pi_apply j).comp (h.measurable i)
  have hind : iIndepFun (fun i ω => ξ i ω j) μ :=
    h.independent.comp (fun _ x => x j) (fun _ => measurable_pi_apply j)
  have hfun : (fun ω => sumVector ξ ω j) =
      ∑ i ∈ Finset.univ, fun ω => ξ i ω j := by
    funext ω
    simp only [sumVector, Finset.sum_apply]
  rw [hfun, hind.mgf_sum hmeas]
  calc
    _ ≤ ∏ i : Fin n, Real.exp (t ^ 2 * ∫ ω, (ξ i ω j) ^ 2 ∂μ) := by
      apply Finset.prod_le_prod (fun i _ => mgf_nonneg)
      intro i _
      have hi := integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
      apply mgf_le_exp_second_moment_of_bounded (hmeas i)
        (by simpa only [pow_one] using hi)
        (integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 2)
        (h.centered i j) (h.abs_coordinate_le i j) ht
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum, h.coordinate_second_moments hunit j, mul_one]

theorem integral_exp_norm_sum_le (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    {t : ℝ} (ht : |t| * δ ≤ 1) :
    (∫ ω, Real.exp (t * ‖sumVector ξ ω‖) ∂μ) ≤
      (2 * (p : ℝ)) * Real.exp (t ^ 2) := by
  have hi (j : Fin p) (a : ℝ) : Integrable
      (fun ω => Real.exp (a * sumVector ξ ω j)) μ := by
    have hcoord : ∀ᵐ ω ∂μ, |sumVector ξ ω j| ≤ (n : ℝ) * δ := by
      filter_upwards [h.sum_norm_bound] with ω hω
      have hn : |sumVector ξ ω j| ≤ ‖sumVector ξ ω‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (sumVector ξ ω) j
      exact hn.trans hω
    exact integrable_exp_mul_of_abs_le
      ((measurable_pi_apply j).comp h.measurable_sum) hcoord a
  have hij (j : Fin p) : Integrable
      (fun ω => Real.exp (t * sumVector ξ ω j) + Real.exp (-t * sumVector ξ ω j)) μ :=
    (hi j t).add (hi j (-t))
  have hisum := integrable_finset_sum Finset.univ (fun j _ => hij j)
  calc
    _ ≤ ∫ ω, ∑ j, (Real.exp (t * sumVector ξ ω j) + Real.exp (-t * sumVector ξ ω j)) ∂μ :=
      integral_mono (h.integrable_exp_norm_sum t) hisum
        (fun ω => exp_mul_norm_le_sum hp (sumVector ξ ω) t)
    _ = ∑ j : Fin p, (mgf (fun ω => sumVector ξ ω j) μ t +
        mgf (fun ω => sumVector ξ ω j) μ (-t)) := by
      rw [integral_finset_sum Finset.univ (fun j _ => hij j)]
      exact Finset.sum_congr rfl (fun j _ => integral_add (hi j t) (hi j (-t)))
    _ ≤ ∑ _j : Fin p, (Real.exp (t ^ 2) + Real.exp (t ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      apply add_le_add (h.mgf_coordinate_sum_le hunit j ht)
      simpa only [neg_sq] using h.mgf_coordinate_sum_le hunit j
        (by simpa only [abs_neg] using ht : |-t| * δ ≤ 1)
    _ = _ := by simp; ring

/-- Explicit Bernstein-type maximum estimate, derived from the actual
bounded independent array. The coefficient is independent of the array,
the envelope, the dimension, and the number of observations. -/
theorem integral_norm_sum_le (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
      2 * Real.sqrt (dimensionLog p) + 2 * δ * dimensionLog p := by
  let L := dimensionLog p
  let a := Real.sqrt L
  let d := 1 + δ * a
  let t := a / d
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ L := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = L := Real.sq_sqrt hL0
  have hδ := h.delta_nonneg
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 < t := div_pos ha hd
  have htle : t ≤ a := by
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    nlinarith [mul_nonneg h.delta_nonneg (sq_nonneg a)]
  have ht2 : t ^ 2 ≤ L := by
    rw [← ha2]
    exact pow_le_pow_left₀ ht.le htle 2
  have htd : |t| * δ ≤ 1 := by
    rw [abs_of_pos ht]
    change (a / d) * δ ≤ 1
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    nlinarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh ⊢
    exact hh
  have hcard : 2 * (p : ℝ) ≤ Real.exp L := by
    rw [show L = Real.log (Real.exp 1 * (p : ℝ)) from rfl,
      Real.exp_log (mul_pos (Real.exp_pos _) hpR)]
    exact mul_le_mul_of_nonneg_right htwo hpR.le
  have hj := exp_integral_le_integral_exp ((h.integrable_norm_sum).const_mul t)
    (h.integrable_exp_norm_sum t)
  rw [integral_const_mul] at hj
  have hexp : Real.exp (t * (∫ ω, ‖sumVector ξ ω‖ ∂μ)) ≤ Real.exp (2 * L) := by
    calc
      _ ≤ ∫ ω, Real.exp (t * ‖sumVector ξ ω‖) ∂μ := hj
      _ ≤ (2 * (p : ℝ)) * Real.exp (t ^ 2) := h.integral_exp_norm_sum_le hp hunit htd
      _ ≤ Real.exp L * Real.exp L :=
        mul_le_mul hcard (Real.exp_le_exp.mpr ht2) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmoment := Real.exp_le_exp.mp hexp
  have hdivide : (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤ 2 * L / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hvalue : 2 * L / t = 2 * a + 2 * δ * L := by
    dsimp [t]
    field_simp [ne_of_gt ha, ne_of_gt hd]
    dsimp [d]
    nlinarith [ha2]
  exact hdivide.trans_eq hvalue

end BoundedIndependentHypotheses
end RectangleCLT
