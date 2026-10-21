import RectangleCLTCompanion.SubexponentialArray
import Mathlib.MeasureTheory.Function.L2Space

/-! Second moments of the actual residual sum and stability of the marginal
standard deviations.  Every covariance below is the covariance of a random
vector, with square integrability proved from its exponential moments. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}

theorem SubexponentialIndependentHypotheses.coordinate_memLp_two
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => X i ω j) 2 μ :=
  (h.coordinate_exponentialMomentBound i j).memLp_two

theorem centeredResidualRows_coordinate_memLp_two [IsFiniteMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (i : Fin n) (j : Fin p) :
    MemLp (fun ω => centeredResidualRows μ X (K * u) i ω j) 2 μ := by
  exact ((h.coordinate_exponentialMomentBound i j).residual_memLp_two hu).sub
    (memLp_const _)

theorem integral_centered_sq_le [IsProbabilityMeasure μ]
    {R : Ω → ℝ} (hR : MemLp R 2 μ) :
    (∫ ω, (R ω - ∫ a, R a ∂μ) ^ 2 ∂μ) ≤ ∫ ω, R ω ^ 2 ∂μ := by
  rw [← variance_eq_integral hR.aestronglyMeasurable.aemeasurable]
  exact variance_le_expectation_sq hR.aestronglyMeasurable

theorem centeredResidualRows_integral_sq_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (i : Fin n) (j : Fin p) :
    (∫ ω, centeredResidualRows μ X (K * u) i ω j ^ 2 ∂μ) ≤
      4 * K ^ 2 * Real.exp (-u) := by
  exact (integral_centered_sq_le
    ((h.coordinate_exponentialMomentBound i j).residual_memLp_two hu)).trans
    ((h.coordinate_exponentialMomentBound i j).integral_residual_sq_le hu)

theorem memLp_sumVector_coordinate
    {ξ : Fin n → Ω → Vector p}
    (hξ : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ) (j : Fin p) :
    MemLp (fun ω => sumVector ξ ω j) 2 μ := by
  have he : (fun ω => sumVector ξ ω j) = (∑ i : Fin n, fun ω => ξ i ω j) := by
    funext ω
    simp only [sumVector, Finset.sum_apply]
  rw [he]
  exact memLp_finset_sum' Finset.univ (fun i _ => hξ i j)

theorem integral_sumVector_coordinate_zero
    {ξ : Fin n → Ω → Vector p}
    (hi : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (hc : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (j : Fin p) :
    (∫ ω, sumVector ξ ω j ∂μ) = 0 := by
  simp only [sumVector, Finset.sum_apply]
  rw [integral_finset_sum Finset.univ (fun i _ => hi i j)]
  simp only [hc, Finset.sum_const_zero]

theorem covariance_diagonal_eq_variance [IsProbabilityMeasure μ]
    {W : Ω → Vector p} (j : Fin p)
    (hW : MemLp (fun ω => W ω j) 2 μ) :
    covariance μ W j j = variance (fun ω => W ω j) μ := by
  rw [variance_def' hW]
  simp only [covariance, Pi.pow_apply, pow_two]

theorem normalizedResidualRows_coordinate_memLp_two [IsFiniteMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (i : Fin n) (j : Fin p) :
    MemLp (fun ω => normalizedResidualRows μ X (K * u) i ω j) 2 μ := by
  exact (centeredResidualRows_coordinate_memLp_two h hu i j).const_mul _

theorem normalizedResidualRows_sum_covariance_diagonal_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (j : Fin p) :
    covariance μ (sumVector (normalizedResidualRows μ X (K * u))) j j ≤
      4 * K ^ 2 * Real.exp (-u) := by
  let U := centeredResidualRows μ X (K * u)
  have hLp (i : Fin n) : MemLp (fun ω => U i ω j) 2 μ :=
    centeredResidualRows_coordinate_memLp_two h hu i j
  have hsLp : MemLp (fun ω => sumVector U ω j) 2 μ :=
    memLp_sumVector_coordinate (fun i j => centeredResidualRows_coordinate_memLp_two h hu i j) j
  have hind := centeredResidualRows_independent h.independent (K * u)
  have hvar : variance (fun ω => sumVector U ω j) μ =
      ∑ i, variance (fun ω => U i ω j) μ := by
    simp only [sumVector, Finset.sum_apply]
    rw [show (fun ω => ∑ i : Fin n, U i ω j) = (∑ i : Fin n, fun ω => U i ω j) by
      funext ω
      simp only [Finset.sum_apply]]
    exact IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
      (fun i _ k _ hik => (hind.indepFun hik).comp
        (measurable_pi_apply j) (measurable_pi_apply j))
  have hvarle : variance (fun ω => sumVector U ω j) μ ≤
      (n : ℝ) * (4 * K ^ 2 * Real.exp (-u)) := by
    rw [hvar]
    calc
      _ ≤ ∑ _i : Fin n, (4 * K ^ 2 * Real.exp (-u)) :=
        Finset.sum_le_sum (fun i _ =>
          (variance_le_expectation_sq (hLp i).aestronglyMeasurable).trans
            (centeredResidualRows_integral_sq_le h hu i j))
      _ = _ := by simp
  have hnlp := memLp_sumVector_coordinate
    (fun i j => normalizedResidualRows_coordinate_memLp_two h hu i j) j
  rw [covariance_diagonal_eq_variance j hnlp]
  have hfun : (fun ω => sumVector (normalizedResidualRows μ X (K * u)) ω j) =
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ * sumVector U ω j) := by
    funext ω
    simp only [sumVector, Finset.sum_apply, normalizedResidualRows,
      Pi.smul_apply, smul_eq_mul, U, Finset.mul_sum]
  rw [hfun, variance_mul]
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hscale : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * (n : ℝ) = 1 := by
    rw [inv_pow, Real.sq_sqrt hnp.le]
    exact inv_mul_cancel₀ hnp.ne'
  calc
    _ ≤ ((Real.sqrt (n : ℝ))⁻¹) ^ 2 *
        ((n : ℝ) * (4 * K ^ 2 * Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left hvarle (sq_nonneg _)
    _ = _ := by rw [← mul_assoc, hscale, one_mul]

/-- The second moment is the square of the actual Hilbert-space norm. -/
theorem integral_sq_eq_norm_toLp_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    _ = ∫ ω, (hf.toLp f ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with ω hω
      rw [hω]
    _ = @inner ℝ (Lp ℝ 2 μ) _ (hf.toLp f) (hf.toLp f) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs])
    _ = _ := real_inner_self_eq_norm_sq _

theorem sqrt_integral_sq_eq_norm_toLp {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [integral_sq_eq_norm_toLp_sq hf, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

theorem sqrt_integral_sub_sq_eq_norm_toLp {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ ω, (f ω - g ω) ^ 2 ∂μ) = ‖hf.toLp f - hg.toLp g‖ := by
  change Real.sqrt (∫ ω, (f - g) ω ^ 2 ∂μ) = _
  rw [sqrt_integral_sq_eq_norm_toLp (hf.sub hg), MemLp.toLp_sub]

theorem sqrt_integral_const_mul_sub_sq_eq_norm_toLp {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (a : ℝ) :
    Real.sqrt (∫ ω, (a * f ω - g ω) ^ 2 ∂μ) = ‖a • hf.toLp f - hg.toLp g‖ := by
  change Real.sqrt (∫ ω, (a • f - g) ω ^ 2 ∂μ) = _
  rw [sqrt_integral_sq_eq_norm_toLp ((hf.const_smul a).sub hg),
    MemLp.toLp_sub, MemLp.toLp_const_smul]

/-- The reverse triangle inequality in `L²`, stated for actual scalar
functions, including arbitrary dependence between the two functions. -/
theorem abs_sqrt_integral_sq_sub_le
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |Real.sqrt (∫ ω, f ω ^ 2 ∂μ) - Real.sqrt (∫ ω, g ω ^ 2 ∂μ)| ≤
      Real.sqrt (∫ ω, (f ω - g ω) ^ 2 ∂μ) := by
  rw [sqrt_integral_sq_eq_norm_toLp hf, sqrt_integral_sq_eq_norm_toLp hg,
    sqrt_integral_sub_sq_eq_norm_toLp hf hg]
  exact abs_norm_sub_norm_le _ _

theorem normalizedObservationSum_coordinate_memLp_two [IsFiniteMeasure μ]
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (j : Fin p) :
    MemLp (fun ω => normalizedObservationSum X ω j) 2 μ := by
  exact (memLp_sumVector_coordinate h.coordinate_memLp_two j).const_mul _

theorem normalizedObservationSum_coordinate_centered [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (j : Fin p) :
    (∫ ω, normalizedObservationSum X ω j ∂μ) = 0 := by
  simp only [normalizedObservationSum, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  rw [integral_sumVector_coordinate_zero
    (fun i j => (h.coordinate_exponentialMomentBound i j).integrable) h.centered j,
    mul_zero]

/-- The actual normalized-sum covariance is the average observation second
moment.  This bridges the manuscript's normalization hypothesis to the
concrete Gaussian comparison contract. -/
theorem normalizedObservationSum_covariance_diagonal [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (j : Fin p) :
    covariance μ (normalizedObservationSum X) j j =
      (1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 2 ∂μ := by
  have hLp (i : Fin n) : MemLp (fun ω => X i ω j) 2 μ := h.coordinate_memLp_two i j
  have hvar : variance (fun ω => sumVector X ω j) μ =
      ∑ i, variance (fun ω => X i ω j) μ := by
    simp only [sumVector, Finset.sum_apply]
    rw [show (fun ω => ∑ i : Fin n, X i ω j) = (∑ i : Fin n, fun ω => X i ω j) by
      funext ω
      simp only [Finset.sum_apply]]
    exact IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
      (fun i _ k _ hik => (h.independent.indepFun hik).comp
        (measurable_pi_apply j) (measurable_pi_apply j))
  have hsecond : (∑ i, variance (fun ω => X i ω j) μ) =
      ∑ i, ∫ ω, X i ω j ^ 2 ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [variance_def' (hLp i), h.centered i j]
    simp
  rw [covariance_diagonal_eq_variance j (normalizedObservationSum_coordinate_memLp_two h j)]
  change variance (fun ω => (Real.sqrt (n : ℝ))⁻¹ * sumVector X ω j) μ = _
  rw [variance_mul, hvar, hsecond, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_div]

theorem normalizedObservationSum_unit_diagonal_of_average_secondMoments
    [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K)
    (haverage : ∀ j, (1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 2 ∂μ = 1)
    (j : Fin p) : covariance μ (normalizedObservationSum X) j j = 1 := by
  rw [normalizedObservationSum_covariance_diagonal h, haverage]

theorem normalizedClippedRows_coordinate_memLp_two [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {T : ℝ} (hT : 0 ≤ T) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => normalizedClippedRows μ X T i ω j) 2 μ := by
  have hb := normalizedClippedRows_boundedHypotheses hX hind hT
  apply (memLp_two_iff_integrable_sq
    ((measurable_pi_apply j).comp (hb.measurable i)).aestronglyMeasurable).mpr
  exact integrable_coordinate_pow_of_bounded hb.measurable hb.abs_coordinate_le i j 2

/-- Clipping changes each marginal standard deviation by at most the
standard deviation of the residual sum.  No independence between those
two sums is used. -/
theorem clipped_standardDeviation_sub_one_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (j : Fin p) :
    |Real.sqrt (covariance μ
      (sumVector (normalizedClippedRows μ X (K * u))) j j) - 1| ≤
      2 * K * Real.exp (-u / 2) := by
  let W := normalizedObservationSum X
  let C := sumVector (normalizedClippedRows μ X (K * u))
  let V := sumVector (normalizedResidualRows μ X (K * u))
  have hT : 0 ≤ K * u := mul_nonneg (zero_le_one.trans h.one_le_scale) hu
  have hcdata := normalizedClippedRows_boundedHypotheses h.measurable h.independent hT
  have hC : MemLp (fun ω => C ω j) 2 μ :=
    memLp_sumVector_coordinate
      (normalizedClippedRows_coordinate_memLp_two h.measurable h.independent hT) j
  have hV : MemLp (fun ω => V ω j) 2 μ :=
    memLp_sumVector_coordinate (normalizedResidualRows_coordinate_memLp_two h hu) j
  have hW : MemLp (fun ω => W ω j) 2 μ := normalizedObservationSum_coordinate_memLp_two h j
  have hc0 : (∫ ω, C ω j ∂μ) = 0 :=
    integral_sumVector_coordinate_zero
      (fun i j => (normalizedClippedRows_coordinate_memLp_two h.measurable h.independent hT i j).integrable one_le_two)
      hcdata.centered j
  have hv0 : (∫ ω, V ω j ∂μ) = 0 := by
    apply integral_sumVector_coordinate_zero
      (fun i j => (normalizedResidualRows_coordinate_memLp_two h hu i j).integrable one_le_two)
    intro i j
    simp only [normalizedResidualRows, Pi.smul_apply, smul_eq_mul, integral_const_mul,
      centeredResidualRows_centered h hu, mul_zero]
  have hw0 : (∫ ω, W ω j ∂μ) = 0 := normalizedObservationSum_coordinate_centered h j
  have hceq : covariance μ C j j = ∫ ω, C ω j ^ 2 ∂μ := by
    simp only [covariance, hc0, zero_mul, sub_zero, pow_two]
  have hveq : covariance μ V j j = ∫ ω, V ω j ^ 2 ∂μ := by
    simp only [covariance, hv0, zero_mul, sub_zero, pow_two]
  have hweq : (∫ ω, W ω j ^ 2 ∂μ) = 1 := by
    have hh := hunit j
    change covariance μ W j j = 1 at hh
    simpa only [covariance, hw0, zero_mul, sub_zero, pow_two] using hh
  have hdiff : (∫ ω, (C ω j - W ω j) ^ 2 ∂μ) = ∫ ω, V ω j ^ 2 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by
      have hsum := congrFun (normalizedObservationSum_eq_clipped_add_residual h hu ω) j
      change W ω j = C ω j + V ω j at hsum
      change (C ω j - W ω j) ^ 2 = V ω j ^ 2
      rw [hsum]
      ring)
  have htriangle := abs_sqrt_integral_sq_sub_le hC hW
  rw [← hceq, hweq, Real.sqrt_one, hdiff] at htriangle
  have hvle : (∫ ω, V ω j ^ 2 ∂μ) ≤ 4 * K ^ 2 * Real.exp (-u) := by
    rw [← hveq]
    exact normalizedResidualRows_sum_covariance_diagonal_le h hu hn j
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  have hexp : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : (2 * K * Real.exp (-u / 2)) ^ 2 = 4 * K ^ 2 * Real.exp (-u) := by
    calc
      _ = 4 * K ^ 2 * (Real.exp (-u / 2) * Real.exp (-u / 2)) := by ring
      _ = _ := by rw [hexp]
  apply htriangle.trans
  have hh := Real.sqrt_le_sqrt hvle
  rw [← hsq, Real.sqrt_sq (by positivity)] at hh
  exact hh

theorem normalizedClippedSum_coordinate_memLp_two [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (j : Fin p) :
    MemLp (fun ω => sumVector (normalizedClippedRows μ X (K * u)) ω j) 2 μ :=
  memLp_sumVector_coordinate
    (normalizedClippedRows_coordinate_memLp_two h.measurable h.independent
      (mul_nonneg (zero_le_one.trans h.one_le_scale) hu)) j

theorem normalizedResidualSum_coordinate_memLp_two [IsFiniteMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (j : Fin p) :
    MemLp (fun ω => sumVector (normalizedResidualRows μ X (K * u)) ω j) 2 μ :=
  memLp_sumVector_coordinate (normalizedResidualRows_coordinate_memLp_two h hu) j

theorem normalizedClippedSum_coordinate_centered [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (j : Fin p) :
    (∫ ω, sumVector (normalizedClippedRows μ X (K * u)) ω j ∂μ) = 0 := by
  have hh := normalizedClippedRows_boundedHypotheses h.measurable h.independent
    (mul_nonneg (zero_le_one.trans h.one_le_scale) hu)
  exact integral_sumVector_coordinate_zero
    (fun i j => (normalizedClippedRows_coordinate_memLp_two h.measurable h.independent
      (mul_nonneg (zero_le_one.trans h.one_le_scale) hu) i j).integrable one_le_two)
    hh.centered j

theorem normalizedResidualSum_coordinate_centered [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (j : Fin p) :
    (∫ ω, sumVector (normalizedResidualRows μ X (K * u)) ω j ∂μ) = 0 := by
  apply integral_sumVector_coordinate_zero
    (fun i j => (normalizedResidualRows_coordinate_memLp_two h hu i j).integrable one_le_two)
  intro i j
  simp only [normalizedResidualRows, Pi.smul_apply, smul_eq_mul, integral_const_mul,
    centeredResidualRows_centered h hu, mul_zero]

theorem clipped_standardDeviation_ge_half [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (hsmall : 2 * K * Real.exp (-u / 2) ≤ 1 / 2) (j : Fin p) :
    1 / 2 ≤ Real.sqrt (covariance μ
      (sumVector (normalizedClippedRows μ X (K * u))) j j) := by
  have hh := (abs_le.mp (clipped_standardDeviation_sub_one_le h hu hn hunit j)).1
  linarith

theorem clipped_coordinate_L2_distance_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (j : Fin p) :
    Real.sqrt (∫ ω,
      (sumVector (normalizedClippedRows μ X (K * u)) ω j -
        normalizedObservationSum X ω j) ^ 2 ∂μ) ≤
      2 * K * Real.exp (-u / 2) := by
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  let C := sumVector (normalizedClippedRows μ X (K * u))
  let V := sumVector (normalizedResidualRows μ X (K * u))
  have hv0 : (∫ ω, V ω j ∂μ) = 0 := normalizedResidualSum_coordinate_centered h hu j
  have hveq : covariance μ V j j = ∫ ω, V ω j ^ 2 ∂μ := by
    simp only [covariance, hv0, zero_mul, sub_zero, pow_two]
  have heq : (∫ ω, (C ω j - normalizedObservationSum X ω j) ^ 2 ∂μ) =
      ∫ ω, V ω j ^ 2 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by
      have hh := congrFun (normalizedObservationSum_eq_clipped_add_residual h hu ω) j
      change normalizedObservationSum X ω j = C ω j + V ω j at hh
      change (C ω j - normalizedObservationSum X ω j) ^ 2 = V ω j ^ 2
      rw [hh]
      ring)
  change Real.sqrt (∫ ω, (C ω j - normalizedObservationSum X ω j) ^ 2 ∂μ) ≤ _
  rw [heq, ← hveq]
  have hh := Real.sqrt_le_sqrt (normalizedResidualRows_sum_covariance_diagonal_le h hu hn j)
  have hexp : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : (2 * K * Real.exp (-u / 2)) ^ 2 = 4 * K ^ 2 * Real.exp (-u) := by
    calc
      _ = 4 * K ^ 2 * (Real.exp (-u / 2) * Real.exp (-u / 2)) := by ring
      _ = _ := by rw [hexp]
  rw [← hsq, Real.sqrt_sq (by positivity)] at hh
  exact hh

end
end RectangleCLT.Companion
