import RectangleCLT.GaussianComparisonHessian
import RectangleCLT.GlobalDerivativeAveragedCaps

/-! The full-eigenvalue alternative for the actual Gaussian Hessian.
The Gaussian score remains in its own independent half of the experiment.
All estimates are uniform in translations and in the smoother bandwidth. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def gaussianSecondGlobalConstant : ℝ := 128 * 1073741824 * Real.exp 10

theorem gaussianSecondGlobalConstant_pos : 0 < gaussianSecondGlobalConstant := by
  unfold gaussianSecondGlobalConstant
  positivity

namespace FaceSmoother

open GaussianTube

variable {p : ℕ} (s : FaceSmoother p)

/-- A positive second-order majorant with the full dual score. -/
theorem sum_abs_convolutionSecond_fullDual_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      ((Real.sqrt ν)⁻¹ / s.bandwidth) * s.fullDualFaceMomentSum A ν x 1 1 +
      (2 / s.bandwidth ^ 2) * s.fullDualFaceMomentSum A ν x 2 0 := by
  classical
  have hsingle := Finset.sum_le_sum (s := Finset.univ)
    (fun (T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1) _ =>
      mul_le_mul_of_nonneg_left
        (s.abs_softFaceDirectional_fullDual_le_moment hp A hν hlower x
          T.val.activeFaceSet (T.val.face 0).1)
        (div_nonneg zero_le_one s.bandwidth_pos.le))
  calc
    _ ≤ (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * ((Real.sqrt ν)⁻¹ *
          s.fullDualGaussianSoftFaceMoment A ν x T.val.activeFaceSet 1)) +
        ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
          (2 / s.bandwidth ^ 2) *
            (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) :=
      (s.sum_abs_convolutionSecondDerivative_le_ordered_soft_faces A x).trans
        (add_le_add hsingle le_rfl)
    _ = _ := by
      simp only [← s.fullDualFaceMomentSumAll_eq,
        fullDualFaceMomentSumAll, fullDualGaussianSoftFaceMoment_zero,
        ← Finset.mul_sum]
      ring

theorem integral_sum_abs_convolutionSecond_fullDual_le_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V)
    (hi : ∀ q k, Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ) :
    (∫ ω, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) (V ω) j k| ∂μ) ≤
      ((Real.sqrt ν)⁻¹ / s.bandwidth) *
        (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 1 1 ∂μ) +
      (2 / s.bandwidth ^ 2) *
        (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 2 0 ∂μ) := by
  have hleft : Integrable (fun ω => ∑ j, ∑ k,
      |s.convolutionSecondDerivative (gaussianLaw A) (V ω) j k|) μ := by
    exact integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun k _ =>
        (integrable_bounded_test_comp μ V hV _
          (s.continuous_convolutionSecondDerivative (gaussianLaw A) j k) _
          (fun x => s.norm_convolutionSecondDerivative_le (gaussianLaw A) x j k)).abs
  have h1 := (hi 1 1).const_mul ((Real.sqrt ν)⁻¹ / s.bandwidth)
  have h2 := (hi 2 0).const_mul (2 / s.bandwidth ^ 2)
  have hh := integral_mono hleft (h1.add h2)
    (fun ω => s.sum_abs_convolutionSecond_fullDual_le_moments hp A hν hlower (V ω))
  simp only [Pi.add_apply] at hh
  rw [integral_add h1 h2] at hh
  simpa only [integral_const_mul] using hh

private theorem second_common_width_face_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V) {q k : ℕ}
    (hq0 : 0 < q) (hq : q ≤ 2) (hk : k ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hboundary : ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer
        ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))))} ≤ B) :
    (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) ^ q *
      ((∫ ω, s.fullDualFaceMomentSum A ν (V ω) q k ∂μ) / s.bandwidth ^ q) ≤
      (2 : ℝ) ^ k * B * (Real.sqrt (dimensionLog p)) ^ k * Real.exp 10 := by
  have ha := Real.sqrt_pos.mpr hν
  have hb : 0 < Real.sqrt (dimensionLog p) := Real.sqrt_pos.mpr
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (log_exp_mul_nat_ge_one hp))
  have hw : 0 < Real.sqrt ν / (4 * Real.sqrt (dimensionLog p)) :=
    div_pos ha (by positivity)
  have hwidth : (q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) /
      Real.sqrt ν ≤ 1 / Real.sqrt (dimensionLog p) := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ ≤ 4 * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show q ≤ 4 by omega)) hw.le
      _ = _ := by field_simp; ring
  have hh := s.integral_fullDualFaceMomentSum_div_le A V hV hp hq0 hν hw.le hlower
    (le_refl (Real.sqrt (dimensionLog p))) hwidth k B hboundary
  have hkR : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he : Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) ≤ Real.exp 10 := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left he
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hB)
      (pow_nonneg hb.le _)))

private theorem second_full_score_coefficient_le
    {a b h B M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (q k : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hm : (a / (4 * b)) ^ q * (M / h ^ q) ≤
      (2 : ℝ) ^ k * B * b ^ k * Real.exp 10) :
    c * a⁻¹ ^ k / h ^ q * M ≤
      (c * 2 ^ k * 4 ^ q) * Real.exp 10 * B * b ^ (q + k) / a ^ (q + k) := by
  have hw : 0 < a / (4 * b) := div_pos ha (by positivity)
  have hh : M / h ^ q ≤ (2 ^ k * B * b ^ k * Real.exp 10) / (a / (4 * b)) ^ q :=
    (le_div_iff₀ (pow_pos hw q)).mpr (by rw [mul_comm]; exact hm)
  calc
    _ = (c * a⁻¹ ^ k) * (M / h ^ q) := by ring
    _ ≤ (c * a⁻¹ ^ k) *
        ((2 ^ k * B * b ^ k * Real.exp 10) / (a / (4 * b)) ^ q) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg hc (pow_nonneg (inv_nonneg.mpr ha.le) k))
    _ = _ := by
      simp only [pow_add, div_pow, mul_pow, inv_pow]
      field_simp [ha.ne', hb.ne']
      <;> ring

/-- The independent-base concentration premise is a genuine boundary
probability estimate. The Gaussian-half application below proves it. -/
theorem integral_sum_abs_convolutionSecond_fullDual_le_of_boundary
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V) {B : ℝ} (hB : 0 ≤ B)
    (hboundary : ∀ q : ℕ, 0 < q → q ≤ 2 →
      ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer
        ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))))} ≤ B) :
    (∫ ω, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) (V ω) j k| ∂μ) ≤
      40 * Real.exp 10 * B * (Real.sqrt (dimensionLog p)) ^ 2 / (Real.sqrt ν) ^ 2 := by
  have ha := Real.sqrt_pos.mpr hν
  have hb := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (log_exp_mul_nat_ge_one hp))
  have hm (q k : ℕ) (hq : 0 < q) (hqk : q + k = 2) :=
    s.second_common_width_face_moment_le (q := q) (k := k) hp A hν hlower V hV hq (by omega)
      (by omega) hB (hboundary q hq (by omega))
  have h1 := second_full_score_coefficient_le ha hb 1 1 (by norm_num : (0 : ℝ) ≤ 1)
    (hm 1 1 (by decide) (by decide))
  have h2 := second_full_score_coefficient_le ha hb 2 0 (by norm_num : (0 : ℝ) ≤ 2)
    (hm 2 0 (by decide) (by decide))
  norm_num only [Nat.reduceAdd, pow_one, pow_zero, one_mul, mul_one,
    show (4 : ℝ) ^ 2 = 16 by norm_num] at h1 h2
  exact (s.integral_sum_abs_convolutionSecond_fullDual_le_moments μ hp A hν hlower V hV
    (s.integrable_fullDualFaceMomentSum_comp A V hV hp hν hlower)).trans
      ((add_le_add h1 h2).trans_eq (by dsimp [dimensionLog]; ring))

theorem convolutionSecondDerivative_gaussian_sum
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (x : Vector p) (j k : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw C) x j k =
      ∫ v, s.convolutionSecondDerivative (gaussianLaw A) (x + v) j k ∂gaussianLaw B := by
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  exact integral_gaussianLaw_sum_eq_iterated A B C hcov _
    (s.continuous_secondDerivative j k) _ (fun y => s.norm_secondDerivative_le y j k) x

theorem sum_abs_convolutionSecond_gaussian_sum_le
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C * C.transpose = A * A.transpose + B * B.transpose)
    (x : Vector p) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw C) x j k|) ≤
      ∫ v, (∑ j, ∑ k,
        |s.convolutionSecondDerivative (gaussianLaw A) (x + v) j k|) ∂gaussianLaw B := by
  have hi (j k : Fin p) : Integrable
      (fun v => |s.convolutionSecondDerivative (gaussianLaw A) (x + v) j k|)
      (gaussianLaw B) :=
    (integrable_bounded_test_comp (gaussianLaw B) (fun v => x + v)
      (measurable_const.add measurable_id) _
      (s.continuous_convolutionSecondDerivative (gaussianLaw A) j k) _
      (fun y => s.norm_convolutionSecondDerivative_le (gaussianLaw A) y j k)).abs
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hi j k)),
    integral_finset_sum Finset.univ (fun k _ => hi _ k)]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  rw [s.convolutionSecondDerivative_gaussian_sum A B C hcov]
  exact abs_integral_le_integral_abs

private theorem second_half_lower
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ}
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) (v : Vector p) :
    (ν / 2) * vectorNormSq v ≤
      matrixQuadratic (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) v := by
  rw [gaussianHalfFactor_covariance, matrixQuadratic_smul]
  convert mul_le_mul_of_nonneg_left (hlower v) (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1 <;> ring

private theorem second_half_diagonal
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1) (j : Fin p) :
    (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) j j = 1 / 2 := by
  rw [gaussianHalfFactor_covariance, Matrix.smul_apply, smul_eq_mul, hA, mul_one]

private theorem second_half_boundary_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (x : Vector p) {q : ℕ} (hq : 0 < q) (hq2 : q ≤ 2)
    (R : FaceSmoother p) (r : Vector p) :
    (gaussianLaw (gaussianHalfFactor A)).real
      {v | (x + v) + r ∈ R.boundaryLayer
        ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))))} ≤
      1073741824 * Real.sqrt (ν / 2) * Real.sqrt 2 := by
  have hL : 0 < dimensionLog p :=
    lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hw : 0 < (q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))) :=
    mul_pos (by exact_mod_cast hq) (div_pos (Real.sqrt_pos.mpr (by positivity)) (by positivity))
  have hh := R.gaussian_boundary_probability_le_of_variance hp (gaussianHalfFactor A)
    (by norm_num : (0 : ℝ) < 1 / 2) (second_half_diagonal A hA) (x + r) hw
  have heq : {v : Vector p | (x + v) + r ∈ R.boundaryLayer
      ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))))} =
      {v | v + (x + r) ∈ R.boundaryLayer
        ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))))} := by
    ext v
    simp only [Set.mem_setOf_eq]
    rw [show (x + v) + r = v + (x + r) by abel]
  rw [heq]
  exact hh.trans (global_gaussian_half_boundary_scale_le hν.le hL (by norm_num) (by omega))

/-- The actual Hessian tensor has the full-eigenvalue coefficient
`log(ep)/sqrt ν`, uniformly in the bandwidth and translation. -/
theorem sum_abs_convolutionSecondDerivative_global_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      gaussianSecondGlobalConstant * dimensionLog p / Real.sqrt ν := by
  let H := gaussianHalfFactor A
  have hhalf : 0 < ν / 2 := by positivity
  have hsplit := s.sum_abs_convolutionSecond_gaussian_sum_le H H A (by
    simp only [H, gaussianHalfFactor_covariance, ← add_smul]
    norm_num) x
  have hbound := s.integral_sum_abs_convolutionSecond_fullDual_le_of_boundary
    (gaussianLaw H) hp H hhalf (second_half_lower A hlower)
    (fun v => x + v) (measurable_const.add measurable_id)
    (show 0 ≤ (1073741824 : ℝ) * Real.sqrt (ν / 2) * Real.sqrt 2 by positivity)
    (fun q hq hq2 R r => second_half_boundary_le hp A hA hν x hq hq2 R r)
  apply (hsplit.trans hbound).trans
  have hn := Real.sqrt_pos.mpr hν
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  rw [global_half_boundary_scale hν.le, Real.sq_sqrt (show 0 ≤ ν / 2 by positivity),
    Real.sq_sqrt hL]
  have he : 40 * Real.exp 10 * ((1073741824 : ℝ) * Real.sqrt ν) * dimensionLog p /
      (ν / 2) = (80 * 1073741824 * Real.exp 10) * dimensionLog p / Real.sqrt ν := by
    field_simp [hν.ne', hn.ne']
    ring_nf
    rw [Real.sq_sqrt hν.le]
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hn.le
  apply mul_le_mul_of_nonneg_right _ hL
  unfold gaussianSecondGlobalConstant
  have hh : (0 : ℝ) ≤ Real.exp 10 := (Real.exp_pos _).le
  nlinarith

end FaceSmoother

end

end RectangleCLT
