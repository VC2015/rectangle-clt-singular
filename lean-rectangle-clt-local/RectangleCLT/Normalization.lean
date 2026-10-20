import RectangleCLT.Moments
import Mathlib.Probability.Variance

/-! Independence and centering identify the summed coordinate second moments
with the covariance diagonal of the actual sum. No spectral lower bound is
needed for the resulting aggregate moment estimates. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

/-- Unit covariance diagonal of the actual sum normalizes the sum of the
coordinate second moments. The hypotheses involve no spectral parameter. -/
theorem coordinate_second_moments_eq {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)}
    (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hLp : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1 := by
  intro j
  have hfun : (∑ i : Fin n, fun ω => ξ i ω j) = (fun ω => ∑ i, ξ i ω j) := by
    funext ω
    simp only [Finset.sum_apply]
  have hsum : MemLp (fun ω => ∑ i, ξ i ω j) 2 μ := by
    rw [← hfun]
    exact memLp_finset_sum' Finset.univ (fun i _ => hLp i j)
  have hvar : variance (fun ω => ∑ i, ξ i ω j) μ =
      ∑ i, variance (fun ω => ξ i ω j) μ := by
    rw [← hfun]
    exact IndepFun.variance_sum (s := Finset.univ) (X := fun i ω => ξ i ω j)
        (fun i _ => hLp i j)
        (fun i _ k _ hik => (hind.indepFun hik).comp
          (measurable_pi_apply j) (measurable_pi_apply j))
  have hsecond : (∑ i, variance (fun ω => ξ i ω j) μ) =
      ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [variance_def' (hLp i j), hcenter i j]
    simp
  have hcov : variance (fun ω => ∑ i, ξ i ω j) μ =
      covariance μ (sumVector ξ) j j := by
    rw [variance_def' hsum]
    simp only [covariance, sumVector, Finset.sum_apply, Pi.pow_apply, pow_two]
  calc
    _ = ∑ i, variance (fun ω => ξ i ω j) μ := hsecond.symm
    _ = variance (fun ω => ∑ i, ξ i ω j) μ := hvar.symm
    _ = covariance μ (sumVector ξ) j j := hcov
    _ = 1 := hunit j

/-- An elementary pointwise form of the Cauchy--Schwarz/AM--GM estimate used
for aggregate third moments. -/
theorem abs_triple_le_envelope (a b c δ : ℝ) (hδ : 0 ≤ δ) (hc : |c| ≤ δ) :
    |a * b * c| ≤ δ / 2 * (a ^ 2 + b ^ 2) := by
  have hab : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩
  calc
    _ = |a * b| * |c| := abs_mul _ _
    _ ≤ |a * b| * δ := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ ≤ ((a ^ 2 + b ^ 2) / 2) * δ := mul_le_mul_of_nonneg_right hab hδ
    _ = _ := by ring

/-- A generic aggregate third-moment estimate. This uses only the envelope,
integrability, and summed second moments; independence and covariance have
already been accounted for by the normalization theorem above. -/
theorem gamma3_le_delta_of_second_moments {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (hsquare : ∀ i j, Integrable (fun ω => (ξ i ω j) ^ 2) μ)
    (htriple : ∀ i j k l, Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) μ)
    (hsecond : ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1) :
    gamma3 μ ξ ≤ δ := by
  have hterm (i : Fin n) (j k l : Fin p) :
      |∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ| ≤
        δ / 2 * ((∫ ω, (ξ i ω j) ^ 2 ∂μ) + ∫ ω, (ξ i ω k) ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ ω, |ξ i ω j * ξ i ω k * ξ i ω l| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, δ / 2 * ((ξ i ω j) ^ 2 + (ξ i ω k) ^ 2) ∂μ := by
        apply integral_mono_ae (htriple i j k l).abs
          (((hsquare i j).add (hsquare i k)).const_mul (δ / 2))
        filter_upwards [hbound i l] with ω hω
        exact abs_triple_le_envelope _ _ _ δ hδ hω
      _ = _ := by
        rw [integral_const_mul, integral_add (hsquare i j) (hsquare i k)]
  unfold gamma3
  apply (Finset.fold_max_le δ).mpr
  refine ⟨hδ, ?_⟩
  intro jkl _
  calc
    _ ≤ ∑ i : Fin n, |∫ ω, ξ i ω jkl.1 * ξ i ω jkl.2.1 * ξ i ω jkl.2.2 ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, δ / 2 *
        ((∫ ω, (ξ i ω jkl.1) ^ 2 ∂μ) + ∫ ω, (ξ i ω jkl.2.1) ^ 2 ∂μ) :=
      Finset.sum_le_sum (fun i _ => hterm i _ _ _)
    _ = δ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsecond jkl.1, hsecond jkl.2.1]
      ring

/-- Finite powers of bounded measurable coordinates are integrable. This
form is independent of either the global or the local covariance hypotheses. -/
theorem integrable_coordinate_pow_of_bounded {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i))
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (i : Fin n) (j : Fin p) (r : ℕ) : Integrable (fun ω => (ξ i ω j) ^ r) μ := by
  apply (integrable_const (δ ^ r)).mono'
    (((measurable_pi_apply j).comp (hmeas i)).pow_const r).aestronglyMeasurable
  filter_upwards [hbound i j] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg (ξ i ω j)) hω r

/-- Mixed third moments have no separate integrability assumption when the
measurable observations satisfy a common coordinate envelope. -/
theorem integrable_coordinate_triple_of_bounded {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i))
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (hδ : 0 ≤ δ) (i : Fin n) (j k l : Fin p) :
    Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) μ := by
  have hmeastriple : Measurable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) :=
    ((((measurable_pi_apply j).comp (hmeas i)).mul
      ((measurable_pi_apply k).comp (hmeas i))).mul
        ((measurable_pi_apply l).comp (hmeas i)))
  apply (integrable_const (δ ^ 3)).mono' hmeastriple.aestronglyMeasurable
  filter_upwards [hbound i j, hbound i k, hbound i l] with ω hj hk hl
  have hjk : |ξ i ω j| * |ξ i ω k| ≤ δ * δ :=
    mul_le_mul hj hk (abs_nonneg _) hδ
  have hprod := mul_le_mul hjk hl (abs_nonneg _) (mul_nonneg hδ hδ)
  simpa only [Real.norm_eq_abs, abs_mul, pow_succ, pow_zero, one_mul] using hprod

/-- Fourth moments are controlled by a coordinate envelope and summed second
moments, without any covariance nondegeneracy assumption. -/
theorem gamma4_le_delta_sq_of_second_moments {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i))
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (hsecond : ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1) :
    gamma4 μ ξ ≤ δ ^ 2 := by
  have hmoment (i : Fin n) (j : Fin p) :
      (∫ ω, (ξ i ω j) ^ 4 ∂μ) ≤ δ ^ 2 * ∫ ω, (ξ i ω j) ^ 2 ∂μ := by
    have hfour := integrable_coordinate_pow_of_bounded hmeas hbound i j 4
    have htwo := integrable_coordinate_pow_of_bounded hmeas hbound i j 2
    rw [← integral_const_mul]
    apply integral_mono_ae hfour (htwo.const_mul (δ ^ 2))
    filter_upwards [hbound i j] with ω hω
    have hsq : (ξ i ω j) ^ 2 ≤ δ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ξ i ω j)) hω 2
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (ξ i ω j))
    nlinarith
  unfold gamma4
  apply (Finset.fold_max_le (δ ^ 2)).mpr
  refine ⟨sq_nonneg δ, ?_⟩
  intro j _
  calc
    (∑ i, ∫ ω, (ξ i ω j) ^ 4 ∂μ) ≤
        ∑ i, δ ^ 2 * ∫ ω, (ξ i ω j) ^ 2 ∂μ :=
      Finset.sum_le_sum (fun i _ => hmoment i j)
    _ = δ ^ 2 := by rw [← Finset.mul_sum, hsecond j, mul_one]

/-- Bounded measurable independent observations with centered coordinates and
unit covariance diagonal have normalized summed coordinate second moments. -/
theorem coordinate_second_moments_eq_of_independent_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1 := by
  apply coordinate_second_moments_eq hind hcenter _ hunit
  intro i j
  apply MemLp.of_bound (((measurable_pi_apply j).comp (hmeas i)).aestronglyMeasurable) δ
  simpa only [Real.norm_eq_abs] using hbound i j

/-- The aggregate fourth-moment conclusion with only bounded independent
array data and a unit covariance diagonal; no global spectral bound appears. -/
theorem gamma4_le_delta_sq_of_independent_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) : gamma4 μ ξ ≤ δ ^ 2 :=
  gamma4_le_delta_sq_of_second_moments hmeas hbound
    (coordinate_second_moments_eq_of_independent_bounded hmeas hind hcenter hbound hunit)

/-- The aggregate third-moment conclusion with only bounded independent
array data and a unit covariance diagonal; singular full covariance is allowed. -/
theorem gamma3_le_delta_of_independent_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → (Fin p → ℝ)} {δ : ℝ}
    (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ) (hδ : 0 ≤ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) : gamma3 μ ξ ≤ δ :=
  gamma3_le_delta_of_second_moments hδ hbound
    (fun i j => integrable_coordinate_pow_of_bounded hmeas hbound i j 2)
    (integrable_coordinate_triple_of_bounded hmeas hbound hδ)
    (coordinate_second_moments_eq_of_independent_bounded hmeas hind hcenter hbound hunit)

namespace BoundedHypotheses

variable {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ b : ℝ}

/-- Bounded measurable coordinates belong to `L²`. -/
theorem memLp_coordinate [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => ξ i ω j) 2 μ := by
  apply MemLp.of_bound (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable) δ
  simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j

/-- The second-moment normalization follows from the existing bounded-array
hypotheses, rather than being an additional assumption. -/
theorem coordinate_second_moments [IsProbabilityMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) :
    ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1 :=
  coordinate_second_moments_eq h.independent h.centered h.memLp_coordinate h.unit_diagonal

/-- The aggregate fourth-moment sum is bounded by the squared envelope. -/
theorem gamma4_le_delta_sq [IsProbabilityMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) : gamma4 μ ξ ≤ δ ^ 2 :=
  h.gamma4_le_delta_sq_of_second_moments h.coordinate_second_moments

/-- The aggregate third-moment tensor is bounded by the envelope. Absolute
values are taken after summing over observations, as in the paper. -/
theorem gamma3_le_delta [IsProbabilityMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) : gamma3 μ ξ ≤ δ :=
  gamma3_le_delta_of_second_moments h.delta_nonneg h.abs_coordinate_le
    (fun i j => h.integrable_coordinate_pow i j 2)
    h.integrable_coordinate_triple h.coordinate_second_moments

end BoundedHypotheses

end RectangleCLT
