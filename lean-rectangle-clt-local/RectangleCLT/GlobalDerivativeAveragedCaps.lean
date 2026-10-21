import RectangleCLT.GlobalDerivativeAssembly
import RectangleCLT.GlobalGaussianHalfSup
import RectangleCLT.ProxyDerivativeCaps
import RectangleCLT.GlobalDerivativeTubeMomentSum
import RectangleCLT.GlobalDerivativeMomentRates
import RectangleCLT.GlobalGaussianBoundary

/-! Averaging the genuine full-dual derivative majorants.  The Gaussian
score moments stay under their independent expectations throughout. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def globalThirdAverageConstant : ℝ := 8192 * 1073741824 * Real.exp 10

def globalFourthAverageConstant : ℝ :=
  gaussianFourthConstant + 262144 * 1073741824 * Real.exp 19

theorem globalThirdAverageConstant_pos : 0 < globalThirdAverageConstant := by
  unfold globalThirdAverageConstant
  positivity

theorem globalFourthAverageConstant_pos : 0 < globalFourthAverageConstant := by
  unfold globalFourthAverageConstant
  exact add_pos gaussianFourthConstant_pos (by positivity)

theorem globalFourthAverageConstant_ge_short :
    gaussianFourthConstant ≤ globalFourthAverageConstant := by
  unfold globalFourthAverageConstant
  exact le_add_of_nonneg_right (by positivity)

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

private theorem half_factor_full_lower
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ}
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) (v : Vector p) :
    (ν / 2) * vectorNormSq v ≤
      matrixQuadratic (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) v := by
  rw [gaussianHalfFactor_covariance, matrixQuadratic_smul]
  exact (by convert mul_le_mul_of_nonneg_left (hlower v) (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1 <;> ring)

private theorem half_factor_diagonal
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1) (j : Fin p) :
    (gaussianHalfFactor A * (gaussianHalfFactor A).transpose) j j = 1 / 2 := by
  rw [gaussianHalfFactor_covariance, Matrix.smul_apply, smul_eq_mul, hA, mul_one]

private theorem common_half_boundary_scale_le {L a : ℝ} {q : ℕ}
    (hL : 0 < L) (ha : 0 ≤ a) (hq : q ≤ 4) :
    (1073741824 : ℝ) * ((q : ℝ) * (a / (4 * Real.sqrt L))) *
      Real.sqrt (L / (1 / 2 : ℝ)) ≤ 1073741824 * a * Real.sqrt 2 := by
  have hb := Real.sqrt_pos.mpr hL
  have hs : Real.sqrt (L / (1 / 2 : ℝ)) = Real.sqrt L * Real.sqrt 2 := by
    rw [show L / (1 / 2 : ℝ) = L * 2 by ring, Real.sqrt_mul hL.le]
  rw [hs]
  have hqR : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hinner : (q : ℝ) * (a / (4 * Real.sqrt L)) * Real.sqrt L ≤ a := by
    have he : (q : ℝ) * (a / (4 * Real.sqrt L)) * Real.sqrt L = (q : ℝ) * a / 4 := by
      field_simp
      <;> ring
    rw [he]
    nlinarith
  calc
    _ = (1073741824 * ((q : ℝ) * (a / (4 * Real.sqrt L)) * Real.sqrt L)) * Real.sqrt 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 1073741824)) (Real.sqrt_nonneg 2)

private theorem common_width_face_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V) {q k : ℕ}
    (hq0 : 0 < q) (hq : q ≤ 4) (hk : k ≤ 3) {B : ℝ} (hB : 0 ≤ B)
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
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hw.le
      _ = _ := by field_simp; ring
  have hh := s.integral_fullDualFaceMomentSum_div_le A V hV hp hq0 hν hw.le hlower
    (le_refl (Real.sqrt (dimensionLog p))) hwidth k B hboundary
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he : Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) ≤ Real.exp 10 := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left he
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hB)
      (pow_nonneg hb.le _)))

private theorem full_score_coefficient_le
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

/-- The finite third tensor is averaged before its concrete score moments
are estimated by the independent tube argument. -/
theorem integral_sum_abs_convolutionThird_fullDual_le_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V)
    (hi : ∀ q k, Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ) :
    (∫ ω, ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw A) (V ω) j k l| ∂μ) ≤
      (2 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth) *
        (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 1 2 ∂μ) +
      (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 2) *
        (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 2 1 ∂μ) +
      (6 / s.bandwidth ^ 3) *
        (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 3 0 ∂μ) := by
  have hleft : Integrable (fun ω => ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw A) (V ω) j k l|) μ := by
    exact integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun k _ =>
        integrable_finset_sum Finset.univ fun l _ =>
          (integrable_bounded_test_comp μ V hV _
            (s.continuous_convolutionThirdDerivative_commonPoint (gaussianLaw A) j k l) _
            (fun x => s.norm_convolutionThirdDerivative_le (gaussianLaw A) x j k l)).abs
  have hright := (((hi 1 2).const_mul (2 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth)).add
    ((hi 2 1).const_mul (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 2))).add
    ((hi 3 0).const_mul (6 / s.bandwidth ^ 3))
  have hh := integral_mono hleft hright
    (fun ω => s.sum_abs_convolutionThird_fullDual_le_moments hp A hν hlower (V ω))
  let f1 : Ω → ℝ := fun ω => (2 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth) *
    s.fullDualFaceMomentSum A ν (V ω) 1 2
  let f2 : Ω → ℝ := fun ω => (6 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 2) *
    s.fullDualFaceMomentSum A ν (V ω) 2 1
  let f3 : Ω → ℝ := fun ω => (6 / s.bandwidth ^ 3) *
    s.fullDualFaceMomentSum A ν (V ω) 3 0
  have h1 : Integrable f1 μ := (hi 1 2).const_mul _
  have h2 : Integrable f2 μ := (hi 2 1).const_mul _
  have h3 : Integrable f3 μ := (hi 3 0).const_mul _
  change _ ≤ ∫ ω, f1 ω + f2 ω + f3 ω ∂μ at hh
  rw [integral_add (f := fun ω => f1 ω + f2 ω) (g := f3) (h1.add h2) h3,
    integral_add (f := f1) (g := f2) h1 h2] at hh
  simpa only [f1, f2, f3, integral_const_mul] using hh

/-- The sum of the separate local fourth suprema is kept inside its actual
expectation and bounded by four positive ordered score moments. -/
theorem integral_sum_localConvolutionFourthSup_fullDual_le_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V)
    (hi : ∀ q k, Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) :
    (∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
      s.localConvolutionFourthSup A r (V ω) 1 j k l m ∂μ) ≤
      Real.exp 9 *
        ((4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) *
          (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 1 3 ∂μ) +
        (28 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) *
          (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 2 2 ∂μ) +
        (36 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) *
          (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 3 1 ∂μ) +
        (24 / s.bandwidth ^ 4) *
          (∫ ω, s.fullDualFaceMomentSum A ν (V ω) 4 0 ∂μ)) := by
  have hleft := integrable_finset_sum Finset.univ fun j _ =>
    integrable_finset_sum Finset.univ fun k _ =>
      integrable_finset_sum Finset.univ fun l _ =>
        integrable_finset_sum Finset.univ fun m _ =>
          s.integrable_localConvolutionFourthSup_comp A hr0 1 μ V hV j k l m
  have hright := (((((hi 1 3).const_mul (4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth)).add
    ((hi 2 2).const_mul (28 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2))).add
    ((hi 3 1).const_mul (36 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3))).add
    ((hi 4 0).const_mul (24 / s.bandwidth ^ 4))).const_mul (Real.exp 9)
  have hh := integral_mono hleft hright
    (fun ω => s.sum_localConvolutionFourthSup_fullDual_le_moments hp A hν hlower (V ω) hr0 hr)
  let f1 : Ω → ℝ := fun ω => (4 * (Real.sqrt ν)⁻¹ ^ 3 / s.bandwidth) *
    s.fullDualFaceMomentSum A ν (V ω) 1 3
  let f2 : Ω → ℝ := fun ω => (28 * (Real.sqrt ν)⁻¹ ^ 2 / s.bandwidth ^ 2) *
    s.fullDualFaceMomentSum A ν (V ω) 2 2
  let f3 : Ω → ℝ := fun ω => (36 * (Real.sqrt ν)⁻¹ / s.bandwidth ^ 3) *
    s.fullDualFaceMomentSum A ν (V ω) 3 1
  let f4 : Ω → ℝ := fun ω => (24 / s.bandwidth ^ 4) *
    s.fullDualFaceMomentSum A ν (V ω) 4 0
  have h1 : Integrable f1 μ := (hi 1 3).const_mul _
  have h2 : Integrable f2 μ := (hi 2 2).const_mul _
  have h3 : Integrable f3 μ := (hi 3 1).const_mul _
  have h4 : Integrable f4 μ := (hi 4 0).const_mul _
  change _ ≤ ∫ ω, Real.exp 9 * (f1 ω + f2 ω + f3 ω + f4 ω) ∂μ at hh
  rw [integral_const_mul,
    integral_add (f := fun ω => f1 ω + f2 ω + f3 ω) (g := f4) ((h1.add h2).add h3) h4,
    integral_add (f := fun ω => f1 ω + f2 ω) (g := f3) (h1.add h2) h3,
    integral_add (f := f1) (g := f2) h1 h2] at hh
  simpa only [f1, f2, f3, f4, integral_const_mul] using hh

/-- A common physical tube width combines the third-order face classes.
The premises are estimates of the explicit score integrals, before any
derivative tensor or local supremum is summed. -/
theorem integral_sum_abs_convolutionThird_fullDual_le_of_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V)
    (hi : ∀ q k, Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ)
    {B : ℝ}
    (hm : ∀ q k : ℕ, 0 < q → q + k = 3 →
      (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) ^ q *
        ((∫ ω, s.fullDualFaceMomentSum A ν (V ω) q k ∂μ) / s.bandwidth ^ q) ≤
        (2 : ℝ) ^ k * B * (Real.sqrt (dimensionLog p)) ^ k * Real.exp 10) :
    (∫ ω, ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw A) (V ω) j k l| ∂μ) ≤
      608 * Real.exp 10 * B * (Real.sqrt (dimensionLog p)) ^ 3 / (Real.sqrt ν) ^ 3 := by
  have ha := Real.sqrt_pos.mpr hν
  have hb := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (log_exp_mul_nat_ge_one hp))
  have h1 := full_score_coefficient_le ha hb 1 2 (by norm_num : (0 : ℝ) ≤ 2)
    (hm 1 2 (by decide) (by decide))
  have h2 := full_score_coefficient_le ha hb 2 1 (by norm_num : (0 : ℝ) ≤ 6)
    (hm 2 1 (by decide) (by decide))
  have h3 := full_score_coefficient_le ha hb 3 0 (by norm_num : (0 : ℝ) ≤ 6)
    (hm 3 0 (by decide) (by decide))
  norm_num only [Nat.reduceAdd, pow_one, pow_zero, one_mul, mul_one,
    show (2 : ℝ) ^ 2 = 4 by norm_num, show (4 : ℝ) ^ 2 = 16 by norm_num,
    show (4 : ℝ) ^ 3 = 64 by norm_num] at h1 h2 h3
  exact (s.integral_sum_abs_convolutionThird_fullDual_le_moments μ hp A hν hlower V hV hi).trans
    ((add_le_add (add_le_add h1 h2) h3).trans_eq (by dsimp [dimensionLog]; ring))

/-- The fourth-order counterpart, for the genuine sum of separate local
suprema, has the full spectral power and no local determinant cost. -/
theorem integral_sum_localConvolutionFourthSup_fullDual_le_of_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V)
    (hi : ∀ q k, Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ)
    {r B : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth)
    (hm : ∀ q k : ℕ, 0 < q → q + k = 4 →
      (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) ^ q *
        ((∫ ω, s.fullDualFaceMomentSum A ν (V ω) q k ∂μ) / s.bandwidth ^ q) ≤
        (2 : ℝ) ^ k * B * (Real.sqrt (dimensionLog p)) ^ k * Real.exp 10) :
    (∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
      s.localConvolutionFourthSup A r (V ω) 1 j k l m ∂μ) ≤
      12672 * Real.exp 19 * B * (Real.sqrt (dimensionLog p)) ^ 4 / (Real.sqrt ν) ^ 4 := by
  have ha := Real.sqrt_pos.mpr hν
  have hb := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (log_exp_mul_nat_ge_one hp))
  have h1 := full_score_coefficient_le ha hb 1 3 (by norm_num : (0 : ℝ) ≤ 4)
    (hm 1 3 (by decide) (by decide))
  have h2 := full_score_coefficient_le ha hb 2 2 (by norm_num : (0 : ℝ) ≤ 28)
    (hm 2 2 (by decide) (by decide))
  have h3 := full_score_coefficient_le ha hb 3 1 (by norm_num : (0 : ℝ) ≤ 36)
    (hm 3 1 (by decide) (by decide))
  have h4 := full_score_coefficient_le ha hb 4 0 (by norm_num : (0 : ℝ) ≤ 24)
    (hm 4 0 (by decide) (by decide))
  norm_num only [Nat.reduceAdd, pow_one, pow_zero, one_mul, mul_one,
    show (2 : ℝ) ^ 2 = 4 by norm_num, show (2 : ℝ) ^ 3 = 8 by norm_num,
    show (4 : ℝ) ^ 2 = 16 by norm_num, show (4 : ℝ) ^ 3 = 64 by norm_num,
    show (4 : ℝ) ^ 4 = 256 by norm_num] at h1 h2 h3 h4
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (Real.exp_nonneg 9)
  have he : Real.exp 19 = Real.exp 9 * Real.exp 10 := by
    rw [← Real.exp_add]
    norm_num
  exact (s.integral_sum_localConvolutionFourthSup_fullDual_le_moments
    μ hp A hν hlower V hV hi hr0 hr).trans (hh.trans_eq (by rw [he]; dsimp [dimensionLog]; ring))

/-- Third derivatives localized by a proved boundary probability for an
independent base vector.  The face moments and their integrability are
derived from the concrete Gaussian/exponential tube experiment. -/
theorem integral_sum_abs_convolutionThird_fullDual_le_of_boundary
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V) {B : ℝ} (hB : 0 ≤ B)
    (hboundary : ∀ q : ℕ, 0 < q → q ≤ 3 →
      ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer
        ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))))} ≤ B) :
    (∫ ω, ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative (gaussianLaw A) (V ω) j k l| ∂μ) ≤
      608 * Real.exp 10 * B * (Real.sqrt (dimensionLog p)) ^ 3 / (Real.sqrt ν) ^ 3 := by
  apply s.integral_sum_abs_convolutionThird_fullDual_le_of_moments μ hp A hν hlower V hV
    (s.integrable_fullDualFaceMomentSum_comp A V hV hp hν hlower)
  intro q k hq hqk
  exact s.common_width_face_moment_le hp A hν hlower V hV hq (by omega)
    (by omega) hB (hboundary q hq (by omega))

/-- Fourth derivatives localized by an independent base boundary bound.
Separate coordinate suprema remain inside the expectation. -/
theorem integral_sum_localConvolutionFourthSup_fullDual_le_of_boundary
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (V : Ω → Vector p) (hV : Measurable V) {r B : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) (hB : 0 ≤ B)
    (hboundary : ∀ q : ℕ, 0 < q → q ≤ 4 →
      ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer
        ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))))} ≤ B) :
    (∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
      s.localConvolutionFourthSup A r (V ω) 1 j k l m ∂μ) ≤
      12672 * Real.exp 19 * B * (Real.sqrt (dimensionLog p)) ^ 4 / (Real.sqrt ν) ^ 4 := by
  apply s.integral_sum_localConvolutionFourthSup_fullDual_le_of_moments μ hp A hν hlower V hV
    (s.integrable_fullDualFaceMomentSum_comp A V hV hp hν hlower) hr0 hr
  intro q k hq hqk
  exact s.common_width_face_moment_le hp A hν hlower V hV hq (by omega)
    (by omega) hB (hboundary q hq (by omega))

/-- The bounded part of the Bernoulli experiment is used as the independent
base of the full-dual tubes. Its covariance and envelope are the actual
normalized retained-array values. -/
theorem normalizedFourthSupAverage_global_bounded_base_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    s.normalizedFourthSupAverage μ ξ A δ t ht ≤
      12672 * Real.exp 19 *
        (1073741824 *
          (4 * (Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))) + 2 * δ / Real.sqrt t) *
          Real.sqrt (dimensionLog p / ((1 - t) / t))) *
        (Real.sqrt (dimensionLog p)) ^ 4 / (Real.sqrt ν) ^ 4 := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  let W := GaussianTube.normalizedThinnedShift (p := p) (n := n) t
  let w := Real.sqrt ν / (4 * Real.sqrt (dimensionLog p))
  let B := 1073741824 * (4 * w + 2 * δ / Real.sqrt t) *
    Real.sqrt (dimensionLog p / ((1 - t) / t))
  have hδ := h.delta_nonneg
  have hw : 0 < w := div_pos (Real.sqrt_pos.mpr hν)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (log_exp_mul_nat_ge_one hp))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : Measurable W := measurable_const.smul (measurable_arraySum p n)
  have hr0 : 0 ≤ 4 * δ / Real.sqrt t := by positivity
  have hr : 4 * δ / Real.sqrt t ≤ sn.bandwidth := by
    exact div_le_div_of_nonneg_right (by linarith [h.delta_nonneg]) (Real.sqrt_nonneg t)
  have hboundary (q : ℕ) (hq : 0 < q) (hq4 : q ≤ 4)
      (R : FaceSmoother p) (r : Vector p) :
      (bernoulliArrayLaw μ ξ t).real
        {b | W b + r ∈ R.boundaryLayer ((q : ℝ) * w)} ≤ B := by
    have hv : 0 < (1 - t) / t := div_pos (sub_pos.mpr ht1) ht
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hh := (h.normalized_thinned t ht ht1.le).boundary_probability_le hp hv
      (h.normalized_thinned_sum_unit_diagonal hunit t ht ht1.le) R r
      (mul_pos hqR hw)
    rw [GaussianTube.sumVector_normalizedThinned] at hh
    apply hh.trans
    dsimp only [B]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1073741824)
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hq4) hw.le) _
  exact sn.integral_sum_localConvolutionFourthSup_fullDual_le_of_boundary
    (bernoulliArrayLaw μ ξ t) hp A hν hlower W hW hr0 hr hB hboundary

theorem sharpFourthAverage_global_early_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hlarge : (1 / ν) * dimensionLog p * s.bandwidth ^ 2 ≤ t) :
    s.sharpFourthAverage μ ξ A δ t ≤
      globalFourthAverageConstant * (1 / Real.sqrt ν) ^ 3 *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht1 : t < 1 := by linarith
  have ha := Real.sqrt_pos.mpr hν
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  let a := 25344 * 1073741824 * Real.exp 19 * (1 / Real.sqrt ν) ^ 3 * (dimensionLog p) ^ 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb := global_early_boundary_scale_le hν hL s.bandwidth_pos h.delta_nonneg
    hband ht ht1 hlarge (by norm_num : (0 : ℝ) ≤ 1073741824) (by decide : 4 ≤ 4)
  have hn0 := s.normalizedFourthSupAverage_global_bounded_base_le h hp hunit A hν hlower hband ht ht1
  have hn : s.normalizedFourthSupAverage μ ξ A δ t ht ≤ a / Real.sqrt ((1 - t) / t) := by
    apply hn0.trans
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
        (by positivity : 0 ≤ 12672 * Real.exp 19))
          (pow_nonneg (Real.sqrt_nonneg (dimensionLog p)) 4))
      (pow_nonneg (Real.sqrt_nonneg ν) 4)
    apply hh.trans_eq
    rw [show (Real.sqrt (dimensionLog p)) ^ 4 = (dimensionLog p) ^ 2 by
      nlinarith only [Real.sq_sqrt hL0]]
    have hc : Real.sqrt ν / (Real.sqrt ν) ^ 4 = (1 / Real.sqrt ν) ^ 3 := by
      field_simp [ha.ne']
      <;> ring
    calc
      _ = (25344 * 1073741824 * Real.exp 19 * (dimensionLog p) ^ 2 /
          Real.sqrt ((1 - t) / t)) * (Real.sqrt ν / (Real.sqrt ν) ^ 4) := by ring
      _ = _ := by rw [hc]; dsimp [a]; ring
  have hscale := s.sharpFourthAverage_le_normalizedFourthSupAverage μ ξ h.measurable A
    h.delta_nonneg ht ht1.le
  have htime := global_early_fourth_time_scale_le ha0 ht ht2
  have hC : 50688 * 1073741824 * Real.exp 19 ≤ globalFourthAverageConstant := by
    unfold globalFourthAverageConstant
    nlinarith [gaussianFourthConstant_pos, Real.exp_pos 19]
  calc
    _ ≤ (a / Real.sqrt ((1 - t) / t)) / t ^ 2 :=
      hscale.trans (div_le_div_of_nonneg_right hn (sq_nonneg t))
    _ ≤ 2 * a * t ^ (-(3 / 2 : ℝ)) := htime
    _ = (50688 * 1073741824 * Real.exp 19) * (1 / Real.sqrt ν) ^ 3 *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by dsimp [a]; ring
    _ ≤ _ := by
      gcongr

private theorem half_base_boundary_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (x : Vector p) {q : ℕ} (hq : 0 < q) (hq4 : q ≤ 4)
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
    (by norm_num : (0 : ℝ) < 1 / 2) (half_factor_diagonal A hA) (x + r) hw
  have heq : {v : Vector p | (x + v) + r ∈ R.boundaryLayer
      ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))))} =
      {v | v + (x + r) ∈ R.boundaryLayer
        ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt (dimensionLog p))))} := by
    ext v
    simp only [Set.mem_setOf_eq]
    rw [show (x + v) + r = v + (x + r) by abel]
  rw [heq]
  exact hh.trans (common_half_boundary_scale_le hL (Real.sqrt_nonneg _) hq4)

/-- Uniform full-spectral third-derivative cap.  The second Gaussian half
is an independent base for the score of the first half. -/
theorem sum_abs_convolutionThird_global_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      globalThirdAverageConstant * (dimensionLog p * Real.sqrt (dimensionLog p)) / ν := by
  let H := gaussianHalfFactor A
  have hhalf : 0 < ν / 2 := by positivity
  have hsplit := s.sum_abs_convolutionThird_gaussian_sum_le H H A (by
    simp only [H, gaussianHalfFactor_covariance, ← add_smul]
    norm_num) x
  have hbound := s.integral_sum_abs_convolutionThird_fullDual_le_of_boundary
    (gaussianLaw H) hp H hhalf (half_factor_full_lower A hlower)
    (fun v => x + v) (measurable_const.add measurable_id)
    (show 0 ≤ (1073741824 : ℝ) * Real.sqrt (ν / 2) * Real.sqrt 2 by positivity)
    (fun q hq hq3 R r => half_base_boundary_le hp A hA hν x hq (by omega) R r)
  exact (hsplit.trans hbound).trans (by
    simpa only [globalThirdAverageConstant] using
      (global_half_third_scale_le hν (by norm_num : (0 : ℝ) ≤ 1073741824)
        (zero_le_one.trans (log_exp_mul_nat_ge_one hp))))

/-- A uniform fourth cap with each local coordinate supremum taken before
the tensor sum. Independent Gaussian splitting supplies the boundary law. -/
theorem sum_localConvolutionFourthSup_global_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ s.bandwidth) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x 1 j k l m) ≤
      (65536 * 1073741824 * Real.exp 19) * (1 / Real.sqrt ν) ^ 3 * (dimensionLog p) ^ 2 := by
  let H := gaussianHalfFactor A
  have hhalf : 0 < ν / 2 := by positivity
  have hsplit := s.sum_localConvolutionFourthSup_gaussian_halves_le A hr0 x
  have hbound := s.integral_sum_localConvolutionFourthSup_fullDual_le_of_boundary
    (gaussianLaw H) hp H hhalf (half_factor_full_lower A hlower)
    (fun v => x + v) (measurable_const.add measurable_id) hr0 hr
    (show 0 ≤ (1073741824 : ℝ) * Real.sqrt (ν / 2) * Real.sqrt 2 by positivity)
    (fun q hq hq4 R r => half_base_boundary_le hp A hA hν x hq hq4 R r)
  exact (hsplit.trans hbound).trans
    (global_half_fourth_scale_le hν (by norm_num : (0 : ℝ) ≤ 1073741824)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))

/-- The concrete Bernoulli third tensor satisfies the full-spectral bound
at every positive Gaussian time, including unequal observation laws. -/
theorem sharpThirdAverage_global_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    s.sharpThirdAverage μ ξ A t ≤
      globalThirdAverageConstant * (dimensionLog p * Real.sqrt (dimensionLog p)) / ν *
        t ^ (-(3 / 2 : ℝ)) := by
  let B := globalThirdAverageConstant * (dimensionLog p * Real.sqrt (dimensionLog p)) / ν *
    t ^ (-(3 / 2 : ℝ))
  have hpoint (x : Vector p) :
      (∑ j, ∑ k, ∑ l,
        |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l|) ≤ B := by
    have hh := (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).sum_abs_convolutionThird_global_le
      hp A hA hν hlower ((Real.sqrt t)⁻¹ • x)
    rw [s.sum_abs_convolutionThirdDerivative_gaussian_scaleDown (Real.sqrt t)
      (Real.sqrt_pos.mpr ht)]
    have he : (Real.sqrt t) ^ 3 = t ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le (1 / 2 : ℝ) 3]
      norm_num
    rw [he]
    apply (div_le_div_of_nonneg_right hh (Real.rpow_nonneg ht.le _)).trans_eq
    dsimp [B]
    rw [Real.rpow_neg ht.le]
    ring
  have hi (mask : Kane.Cube n) := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        (s.integrable_convolutionThirdDerivative_mask (gaussianLaw (Real.sqrt t • A))
          μ ξ hξ 0 (thinningScale t) mask j k l).abs)))
  have hm (mask : Kane.Cube n) :
      (∫ ω, ∑ j, ∑ k, ∑ l,
        |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A))
          (0 + thinningScale t • maskObservationSum ξ mask ω) j k l| ∂μ) ≤ B := by
    have hh := integral_mono (hi mask) (integrable_const B) (fun ω => hpoint _)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh
  unfold sharpThirdAverage selectorThirdAbsoluteAverage
  calc
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask * B :=
      Finset.sum_le_sum (fun mask _ => mul_le_mul_of_nonneg_left (hm mask)
        (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht.le) mask))
    _ = B := by rw [← Finset.sum_mul, Kane.maskWeight_sum, one_mul]

/-- The late Gaussian-time fourth cap uses actual independent halves,
then averages the uniform bound over the Bernoulli law. -/
theorem sharpFourthAverage_global_late_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht2 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    s.sharpFourthAverage μ ξ A δ t ≤
      globalFourthAverageConstant * (1 / Real.sqrt ν) ^ 3 *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht : 0 < t := by linarith
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  let a := (65536 * 1073741824 * Real.exp 19) * (1 / Real.sqrt ν) ^ 3 * (dimensionLog p) ^ 2
  have hr0 : 0 ≤ 4 * δ / Real.sqrt t :=
    div_nonneg (mul_nonneg (by norm_num) h.delta_nonneg) (Real.sqrt_nonneg t)
  have hr : 4 * δ / Real.sqrt t ≤ sn.bandwidth :=
    div_le_div_of_nonneg_right (by linarith [h.delta_nonneg]) (Real.sqrt_nonneg t)
  have hpoint (x : Vector p) := sn.sum_localConvolutionFourthSup_global_le hp A hA hν hlower x hr0 hr
  have hnorm := s.normalizedFourthSupAverage_le_of_uniform μ ξ A h.delta_nonneg ht hpoint h.measurable ht1
  have hscale := s.sharpFourthAverage_le_normalizedFourthSupAverage μ ξ h.measurable A h.delta_nonneg ht ht1
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have htime := inverse_square_le_four_mul_neg_three_halves ht2 ht1
  have hC : 262144 * 1073741824 * Real.exp 19 ≤ globalFourthAverageConstant := by
    unfold globalFourthAverageConstant
    linarith [gaussianFourthConstant_pos]
  calc
    _ ≤ a / t ^ 2 := hscale.trans (div_le_div_of_nonneg_right hnorm (sq_nonneg t))
    _ = a * (1 / t ^ 2) := by ring
    _ ≤ a * (4 * t ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left htime ha0
    _ = (262144 * 1073741824 * Real.exp 19) * (1 / Real.sqrt ν) ^ 3 *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by dsimp [a]; ring
    _ ≤ _ := by gcongr

/-- The genuine full-spectral large-time derivative cap, with the exact
threshold used in the scalar time integration. -/
theorem sharpFourthAverage_global_largeTime_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hlarge : (1 / ν) * dimensionLog p * s.bandwidth ^ 2 ≤ t) :
    s.sharpFourthAverage μ ξ A δ t ≤
      globalFourthAverageConstant * (1 / Real.sqrt ν) ^ 3 *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by
  by_cases ht2 : t ≤ 1 / 2
  · exact s.sharpFourthAverage_global_early_le h hp hunit A hν hlower hband ht ht2 hlarge
  · exact s.sharpFourthAverage_global_late_le h hp A hA hν hlower hband (by linarith) ht1.le

end FaceSmoother

end

end RectangleCLT
