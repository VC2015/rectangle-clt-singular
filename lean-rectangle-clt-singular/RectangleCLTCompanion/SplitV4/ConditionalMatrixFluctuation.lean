import RectangleCLTCompanion.SplitV4.EnvelopeMaximum
import RectangleCLTCompanion.SplitV4.ProductConditional
import RectangleCLTCompanion.SplitV4.PairedCoefficients
import RectangleCLTCompanion.SplitV4.PairedMoments
import Mathlib.Logic.Equiv.Fin.Basic

/-!
The actual independent centered matrix fluctuation used in Appendix G.
Matrix entries are coordinates of one vector per summand, so their internal
dependence is retained. Its variance budget is obtained from the actual
coordinate fourth moments before applying the proved Bernstein maximum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def matrixFluctuationConstant : ℝ := 4 * (1 + Real.exp 1)

/-- Flatten a matrix into one vector; the norm is the maximum entry norm. -/
def matrixEntriesVector {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) : Vector (p * p) :=
  fun a => M (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

/-- The explicit maximum-entry norm, avoiding a choice of matrix operator norm. -/
def matrixMaxEntryNorm {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ‖fun j : Fin p => fun k : Fin p => M j k‖

theorem norm_matrixEntriesVector {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) :
    ‖matrixEntriesVector M‖ = matrixMaxEntryNorm M := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j : Fin p => fun k : Fin p => M j k))).mpr
    intro a
    exact (norm_le_pi_norm (M (finProdFinEquiv.symm a).1)
      (finProdFinEquiv.symm a).2).trans
      (norm_le_pi_norm (fun j : Fin p => fun k : Fin p => M j k) (finProdFinEquiv.symm a).1)
  · unfold matrixMaxEntryNorm
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (matrixEntriesVector M))).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (matrixEntriesVector M))).mpr
    intro k
    simpa only [matrixEntriesVector, Equiv.symm_apply_apply] using
      norm_le_pi_norm (matrixEntriesVector M) (finProdFinEquiv (j, k))

def rankOneEntries {p : ℕ} (x : Vector p) : Vector (p * p) :=
  matrixEntriesVector (fun j k => x j * x k)

theorem measurable_rankOneEntries {p : ℕ} : Measurable (rankOneEntries (p := p)) := by
  apply measurable_pi_iff.mpr
  intro a
  exact (measurable_pi_apply (finProdFinEquiv.symm a).1).mul
    (measurable_pi_apply (finProdFinEquiv.symm a).2)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {h D : ℝ}

def centeredRankOneEntries (μ : Measure Ω) (Y : Fin n → Ω → Vector p) :
    Fin n → Ω → Vector (p * p) :=
  fun i ω a => rankOneEntries (Y i ω) a - ∫ z, rankOneEntries (Y i z) a ∂μ

/-- The actual centered sum, with no coordinate-independence premise. -/
def centeredRankOneSum (μ : Measure Ω) (Y : Fin n → Ω → Vector p)
    (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∑ i, (Y i ω j * Y i ω k - ∫ z, Y i z j * Y i z k ∂μ)

omit [IsProbabilityMeasure μ] in
theorem sum_centeredRankOneEntries_eq (ω : Ω) :
    sumVector (centeredRankOneEntries μ Y) ω = matrixEntriesVector (centeredRankOneSum μ Y ω) := by
  ext a
  simp only [sumVector, centeredRankOneEntries, matrixEntriesVector, centeredRankOneSum,
    rankOneEntries, Finset.sum_apply]

omit [IsProbabilityMeasure μ] in
theorem bounded_rankOneEntries_coordinate
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h) (hh : 0 ≤ h)
    (i : Fin n) (a : Fin (p * p)) :
    ∀ᵐ ω ∂μ, |rankOneEntries (Y i ω) a| ≤ h ^ 2 := by
  filter_upwards [hbound i] with ω hω
  have hj := (norm_le_pi_norm (Y i ω) (finProdFinEquiv.symm a).1).trans hω
  have hk := (norm_le_pi_norm (Y i ω) (finProdFinEquiv.symm a).2).trans hω
  simp only [Real.norm_eq_abs] at hj hk
  simpa only [rankOneEntries, matrixEntriesVector, abs_mul, pow_two] using
    mul_le_mul hj hk (abs_nonneg _) hh

theorem integrable_rankOneEntries_coordinate
    (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h) (hh : 0 ≤ h)
    (i : Fin n) (a : Fin (p * p)) :
    Integrable (fun ω => rankOneEntries (Y i ω) a) μ := by
  apply (integrable_const (h ^ 2)).mono'
    ((measurable_pi_apply a).comp (measurable_rankOneEntries.comp (hY i))).aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using bounded_rankOneEntries_coordinate hbound hh i a

theorem centeredRankOneEntries_boundedHypotheses
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h) (hh : 0 ≤ h) :
    BoundedIndependentHypotheses μ (centeredRankOneEntries μ Y) (2 * h ^ 2) := by
  have hm (i : Fin n) : Measurable (centeredRankOneEntries μ Y i) := by
    apply measurable_pi_iff.mpr
    intro a
    exact ((measurable_pi_apply a).comp (measurable_rankOneEntries.comp (hY i))).sub_const _
  refine ⟨hm, ?_, ?_, ?_, by positivity⟩
  · exact hind.comp (fun i (x : Vector p) => fun a => rankOneEntries x a -
      ∫ z, rankOneEntries (Y i z) a ∂μ) (fun i =>
        measurable_pi_iff.mpr (fun a =>
          ((measurable_pi_apply a).comp measurable_rankOneEntries).sub_const _))
  · intro i a
    change (∫ ω, (rankOneEntries (Y i ω) a - ∫ z, rankOneEntries (Y i z) a ∂μ) ∂μ) = 0
    rw [integral_sub (integrable_rankOneEntries_coordinate hY hbound hh i a) (integrable_const _)]
    simp
  · intro i
    have hmean (a : Fin (p * p)) : |∫ ω, rankOneEntries (Y i ω) a ∂μ| ≤ h ^ 2 := by
      have hb := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun ω => rankOneEntries (Y i ω) a)
        (by simpa only [Real.norm_eq_abs] using bounded_rankOneEntries_coordinate hbound hh i a)
      simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using hb
    filter_upwards [ae_all_iff.mpr (fun a => bounded_rankOneEntries_coordinate hbound hh i a)] with ω hω
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * h ^ 2)).mpr
    intro a
    change |rankOneEntries (Y i ω) a - ∫ z, rankOneEntries (Y i z) a ∂μ| ≤ _
    have ht := (abs_sub _ _).trans (add_le_add (hω a) (hmean a))
    linarith

theorem centeredRankOneEntries_variance_budget
    (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h) (hh : 0 ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ D)
    (a : Fin (p * p)) :
    (∑ i, ∫ ω, centeredRankOneEntries μ Y i ω a ^ 2 ∂μ) ≤ D := by
  let j := (finProdFinEquiv.symm a).1
  let k := (finProdFinEquiv.symm a).2
  have hc (i : Fin n) (l : Fin p) : ∀ᵐ ω ∂μ, |Y i ω l| ≤ h := by
    filter_upwards [hbound i] with ω hω
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (Y i ω) l).trans hω
  have hi4 (i : Fin n) (l : Fin p) : Integrable (fun ω => Y i ω l ^ 4) μ :=
    integrable_coordinate_pow_of_bounded hY hc i l 4
  have hip2 (i : Fin n) : Integrable (fun ω => rankOneEntries (Y i ω) a ^ 2) μ := by
    apply (integrable_const ((h ^ 2) ^ 2)).mono'
      (((measurable_pi_apply a).comp (measurable_rankOneEntries.comp (hY i))).pow_const 2).aestronglyMeasurable
    filter_upwards [bounded_rankOneEntries_coordinate hbound hh i a] with ω hω
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hmixed (i : Fin n) : (∫ ω, rankOneEntries (Y i ω) a ^ 2 ∂μ) ≤
      ((∫ ω, Y i ω j ^ 4 ∂μ) + ∫ ω, Y i ω k ^ 4 ∂μ) / 2 := by
    have hcross (x y : ℝ) : (x * y) ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    calc
      _ ≤ ∫ ω, (Y i ω j ^ 4 + Y i ω k ^ 4) / 2 ∂μ :=
        integral_mono (hip2 i) (((hi4 i j).add (hi4 i k)).div_const 2) (fun ω => by
          exact hcross _ _)
      _ = _ := by rw [integral_div, integral_add (hi4 i j) (hi4 i k)]
  have hvar (i : Fin n) : (∫ ω, centeredRankOneEntries μ Y i ω a ^ 2 ∂μ) ≤
      ((∫ ω, Y i ω j ^ 4 ∂μ) + ∫ ω, Y i ω k ^ 4 ∂μ) / 2 := by
    have hm : AEStronglyMeasurable (fun ω => rankOneEntries (Y i ω) a) μ :=
      ((measurable_pi_apply a).comp (measurable_rankOneEntries.comp (hY i))).aestronglyMeasurable
    change (∫ ω, (rankOneEntries (Y i ω) a - ∫ z, rankOneEntries (Y i z) a ∂μ) ^ 2 ∂μ) ≤ _
    rw [← variance_eq_integral hm.aemeasurable]
    exact (variance_le_expectation_sq hm).trans (hmixed i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hvar i)
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hs
  linarith [hfourth j, hfourth k]

theorem dimensionLog_square_le {p : ℕ} (hp : 1 ≤ p) :
    dimensionLog (p * p) ≤ 2 * dimensionLog p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  unfold dimensionLog
  rw [Nat.cast_mul, Real.log_mul (Real.exp_pos 1).ne' (mul_pos hp0 hp0).ne',
    Real.log_mul hp0.ne' hp0.ne', Real.log_exp,
    Real.log_mul (Real.exp_pos 1).ne' hp0.ne', Real.log_exp]
  linarith

/-- The actual centered matrix fluctuation of the independent bounded
increments, with a universal constant fixed before every probability model. -/
theorem expected_centeredRankOneSum_norm_le
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ D) :
    (∫ ω, matrixMaxEntryNorm (centeredRankOneSum μ Y ω) ∂μ) ≤
      matrixFluctuationConstant *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hp2 : 1 ≤ p * p := by simpa using Nat.mul_le_mul hp hp
  have hZ := centeredRankOneEntries_boundedHypotheses hY hind hbound hh.le
  have hb := bounded_vector_bernstein_maximum hZ hp2 (by positivity : 0 < 2 * h ^ 2) hD
    (centeredRankOneEntries_variance_budget hY hbound hh.le hfourth)
  have hnorm (ω : Ω) : ‖sumVector (centeredRankOneEntries μ Y) ω‖ =
      matrixMaxEntryNorm (centeredRankOneSum μ Y ω) := by
    rw [sum_centeredRankOneEntries_eq, norm_matrixEntriesVector]
  simp_rw [hnorm] at hb
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hL2 := dimensionLog_square_le hp
  have hsqrt : Real.sqrt (D * dimensionLog (p * p)) ≤ 2 * Real.sqrt (D * dimensionLog p) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hL2 hD
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hD hL)]
    nlinarith [mul_nonneg hD hL]
  have hm := mul_le_mul_of_nonneg_left hL2 (sq_nonneg h)
  have hC : 0 ≤ 1 + Real.exp 1 := by positivity
  unfold matrixFluctuationConstant
  apply hb.trans
  have hs := mul_le_mul_of_nonneg_left hsqrt hC
  have hl := mul_le_mul_of_nonneg_left hm hC
  have hpos := mul_nonneg hC (Real.sqrt_nonneg (D * dimensionLog p))
  nlinarith

/-- The same matrix as a finite function space, with its canonical maximum
norm and genuine Bochner conditional expectations. -/
def centeredRankOnePiSum (μ : Measure Ω) (Y : Fin n → Ω → Vector p)
    (ω : Ω) : Fin p → Fin p → ℝ :=
  fun j k => centeredRankOneSum μ Y ω j k

omit [IsProbabilityMeasure μ] in
theorem measurable_centeredRankOnePiSum (hY : ∀ i, Measurable (Y i)) :
    Measurable (centeredRankOnePiSum μ Y) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro k
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    (((measurable_pi_apply j).comp (hY i)).mul
      ((measurable_pi_apply k).comp (hY i))).sub_const _)

theorem integrable_centeredRankOnePiSum
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h) (hh : 0 ≤ h) :
    Integrable (centeredRankOnePiSum μ Y) μ := by
  have hZ := centeredRankOneEntries_boundedHypotheses hY hind hbound hh
  have hi (i : Fin n) : Integrable (centeredRankOneEntries μ Y i) μ :=
    (integrable_const (2 * h ^ 2)).mono' (hZ.measurable i).aestronglyMeasurable (hZ.bounded i)
  apply (integrable_finset_sum Finset.univ (fun i _ => hi i)).congr'
    (measurable_centeredRankOnePiSum hY).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    change ‖sumVector (centeredRankOneEntries μ Y) ω‖ =
      ‖centeredRankOnePiSum μ Y ω‖
    rw [sum_centeredRankOneEntries_eq, norm_matrixEntriesVector]
    rfl)

/-- Conditional Jensen for the actual centered matrix: averaging over the
independent copy does not increase the expected maximum-entry fluctuation.
The copy average is the proved version of conditional expectation given the
whole original sample, as established in `ProductConditional`. -/
theorem expected_copyAverage_centeredRankOneSum_norm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Fin n → α × β → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y (μ.prod ν))
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ z ∂μ.prod ν, ‖Y i z‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ z, Y i z j ^ 4 ∂μ.prod ν) ≤ D) :
    (∫ x, ‖copyAverage ν (centeredRankOnePiSum (μ.prod ν) Y) x‖ ∂μ) ≤
      matrixFluctuationConstant *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hi := integrable_centeredRankOnePiSum hY hind hbound hh.le
  have hj := integral_norm_copyAverage_le μ ν (centeredRankOnePiSum (μ.prod ν) Y) hi
  exact hj.trans (expected_centeredRankOneSum_norm_le hY hind hp hh hD hbound hfourth)

/-- The actual half covariance normalization of `T_h-E T_h`, retained as a
factor one half rather than absorbed into an unspecified constant. -/
theorem expected_half_copyAverage_centeredRankOneSum_norm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Fin n → α × β → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y (μ.prod ν))
    (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hbound : ∀ i, ∀ᵐ z ∂μ.prod ν, ‖Y i z‖ ≤ h)
    (hfourth : ∀ j, (∑ i, ∫ z, Y i z j ^ 4 ∂μ.prod ν) ≤ D) :
    (∫ x, ‖(1 / 2 : ℝ) • copyAverage ν (centeredRankOnePiSum (μ.prod ν) Y) x‖ ∂μ) ≤
      (matrixFluctuationConstant / 2) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hb := expected_copyAverage_centeredRankOneSum_norm_le μ ν hY hind hp hh hD hbound hfourth
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [integral_const_mul]
  nlinarith

/-- Every entry of the actual `T_h` is its copy integral. Boundedness of
the paired cutoff justifies finite summation and every integral exchange. -/
theorem copyArrayTruncatedCovariance_eq_copy_integral
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hh : 0 ≤ h) (x : Ω) (j k : Fin p) :
    copyArrayTruncatedCovariance μ ξ x h j k =
      ∫ y, arrayCovarianceIntegrand ξ h j k (x, y) ∂μ := by
  unfold copyArrayTruncatedCovariance arrayCovarianceIntegrand copyTruncatedCovariance copyCovarianceIntegrand
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (C4Test.integrable_truncated_copy_coordinate_product μ (ξ i) (hξ i) (ξ i x) hh j k).const_mul
      (1 / 2 : ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_const_mul (1 / 2 : ℝ)
    (fun y => pairedTruncatedIncrement (ξ i x) (ξ i y) h j *
      pairedTruncatedIncrement (ξ i x) (ξ i y) h k)).symm

/-- Full measurability of the actual conditional matrix entries, rather
than only the a.e. measurability of a conditional-expectation version. -/
theorem measurable_copyArrayTruncatedCovariance_entry
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hh : 0 ≤ h) (j k : Fin p) :
    Measurable (fun x => copyArrayTruncatedCovariance μ ξ x h j k) := by
  have hm : Measurable (arrayCovarianceIntegrand ξ h j k) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_copyCovarianceIntegrand (ξ i) (hξ i) h j k)
  have hf := hm.stronglyMeasurable.integral_prod_right' (ν := μ)
  have heq : (fun x => copyArrayTruncatedCovariance μ ξ x h j k) =
      fun x => ∫ y, arrayCovarianceIntegrand ξ h j k (x, y) ∂μ :=
    funext (fun x => copyArrayTruncatedCovariance_eq_copy_integral ξ hξ hh x j k)
  rw [heq]
  exact hf.measurable

/-- The mean of the actual conditional matrix equals the unconditional
mean of the half rank-one sum; this is the precise centering in G.1. -/
theorem integral_copyArrayTruncatedCovariance_eq
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hh : 0 ≤ h) (j k : Fin p) :
    (∫ x, copyArrayTruncatedCovariance μ ξ x h j k ∂μ) =
      ∫ z, arrayCovarianceIntegrand ξ h j k z ∂μ.prod μ := by
  have hi : Integrable (arrayCovarianceIntegrand ξ h j k) (μ.prod μ) :=
    integrable_finset_sum Finset.univ (fun i _ =>
      integrable_copyCovarianceIntegrand μ (ξ i) (hξ i) hh j k)
  simp_rw [copyArrayTruncatedCovariance_eq_copy_integral ξ hξ hh]
  exact (integral_prod _ hi).symm

/-- The matrix `T_h-E T_h`, entry by entry and with its actual removed
mean, is exactly the conditional half-centered rank-one expression. -/
theorem half_copyAverage_centeredRankOnePiSum_paired_ae_eq
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hh : 0 ≤ h) :
    (fun x => (1 / 2 : ℝ) • copyAverage μ
      (centeredRankOnePiSum (μ.prod μ) (pairedTruncatedArray ξ h)) x) =ᵐ[μ]
    (fun x => fun j k => copyArrayTruncatedCovariance μ ξ x h j k -
      ∫ w, copyArrayTruncatedCovariance μ ξ w h j k ∂μ) := by
  let Y := pairedTruncatedArray ξ h
  have hY (i : Fin n) : Measurable (Y i) :=
    C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h
  have hbound (i : Fin n) : ∀ᵐ z ∂μ.prod μ, ‖Y i z‖ ≤ h :=
    ae_of_all _ (fun z => C4Test.norm_pairedTruncatedIncrement_le _ _ hh)
  have hfi := integrable_centeredRankOnePiSum hY
    (iIndepFun_pairedTruncatedArray μ ξ hξ hind h) hbound hh
  filter_upwards [hfi.prod_right_ae] with x hx
  ext j k
  have hproj := ((ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj j : (Fin p → Fin p → ℝ) →L[ℝ] (Fin p → ℝ))).integral_comp_comm hx
  change (∫ y, centeredRankOnePiSum (μ.prod μ) Y (x, y) j k ∂μ) =
    (copyAverage μ (centeredRankOnePiSum (μ.prod μ) Y) x) j k at hproj
  change (1 / 2 : ℝ) * (copyAverage μ (centeredRankOnePiSum (μ.prod μ) Y) x) j k = _
  rw [← hproj, integral_copyArrayTruncatedCovariance_eq ξ hξ hh]
  change (1 / 2 : ℝ) *
    (∫ y, ∑ i, (Y i (x, y) j * Y i (x, y) k -
      ∫ z, Y i z j * Y i z k ∂μ.prod μ) ∂μ) = _
  have hsection (i : Fin n) : Integrable (fun y => Y i (x, y) j * Y i (x, y) k) μ :=
    C4Test.integrable_truncated_copy_coordinate_product μ (ξ i) (hξ i) (ξ i x) hh j k
  have hglobal (i : Fin n) : Integrable (fun z => Y i z j * Y i z k) (μ.prod μ) := by
    have hh' := integrable_copyCovarianceIntegrand μ (ξ i) (hξ i) hh j k
    have heq : (fun z => Y i z j * Y i z k) =
        fun z => (2 : ℝ) * copyCovarianceIntegrand (ξ i) h j k z := by
      funext z
      dsimp [Y, pairedTruncatedArray, copyCovarianceIntegrand]
      ring
    rw [heq]
    exact hh'.const_mul 2
  rw [integral_finset_sum
    (f := fun i y => Y i (x, y) j * Y i (x, y) k -
      ∫ z, Y i z j * Y i z k ∂μ.prod μ)
    Finset.univ (fun i _ => (hsection i).sub
      (integrable_const (∫ z, Y i z j * Y i z k ∂μ.prod μ)))]
  have heach (i : Fin n) :
      (∫ y, (Y i (x, y) j * Y i (x, y) k -
        ∫ z, Y i z j * Y i z k ∂μ.prod μ) ∂μ) =
      (∫ y, Y i (x, y) j * Y i (x, y) k ∂μ) -
        ∫ z, Y i z j * Y i z k ∂μ.prod μ := by
    rw [integral_sub (hsection i) (integrable_const _)]
    simp
  simp_rw [heach]
  rw [copyArrayTruncatedCovariance_eq_copy_integral ξ hξ hh]
  simp_rw [arrayCovarianceIntegrand_eq_half_sum]
  rw [integral_const_mul, integral_const_mul]
  change (1 / 2 : ℝ) * (∑ i, ((∫ y, Y i (x, y) j * Y i (x, y) k ∂μ) -
      ∫ z, Y i z j * Y i z k ∂μ.prod μ)) =
    (1 / 2 : ℝ) * (∫ y, ∑ i, Y i (x, y) j * Y i (x, y) k ∂μ) -
    (1 / 2 : ℝ) * (∫ z, ∑ i, Y i z j * Y i z k ∂μ.prod μ)
  rw [
    integral_finset_sum Finset.univ (fun i _ => hsection i),
    integral_finset_sum Finset.univ (fun i _ => hglobal i)]
  simp only [Finset.sum_sub_distrib, mul_sub]

/-- The actual matrix fluctuation is genuinely Bochner integrable. -/
theorem integrable_copyArrayTruncatedCovariance_fluctuation
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hh : 0 ≤ h) :
    Integrable (fun x => fun j k => copyArrayTruncatedCovariance μ ξ x h j k -
      ∫ w, copyArrayTruncatedCovariance μ ξ w h j k ∂μ) μ := by
  have hY (i : Fin n) : Measurable (pairedTruncatedArray ξ h i) :=
    C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h
  have hbound (i : Fin n) : ∀ᵐ z ∂μ.prod μ, ‖pairedTruncatedArray ξ h i z‖ ≤ h :=
    ae_of_all _ (fun z => C4Test.norm_pairedTruncatedIncrement_le _ _ hh)
  have hi := integrable_centeredRankOnePiSum hY
    (iIndepFun_pairedTruncatedArray μ ξ hξ hind h) hbound hh
  have hca : Integrable (fun x => (1 / 2 : ℝ) • copyAverage μ
      (centeredRankOnePiSum (μ.prod μ) (pairedTruncatedArray ξ h)) x) μ :=
    hi.integral_prod_left.smul (1 / 2 : ℝ)
  exact hca.congr (half_copyAverage_centeredRankOnePiSum_paired_ae_eq ξ hξ hind hh)

/-- Adding the deterministic covariance bias keeps the actual matrix
coefficient genuinely integrable, including for singular target matrices. -/
theorem integrable_copyArrayTruncatedCovariance_sub_const
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hh : 0 ≤ h) (S : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun x => fun j k => copyArrayTruncatedCovariance μ ξ x h j k - S j k) μ := by
  have hi := integrable_copyArrayTruncatedCovariance_fluctuation ξ hξ hind hh
  have hc : Integrable (fun _ : Ω => fun j k =>
      (∫ w, copyArrayTruncatedCovariance μ ξ w h j k ∂μ) - S j k) μ := integrable_const _
  apply (hi.add hc).congr
  exact ae_of_all _ (fun x => by
    ext j k
    dsimp
    ring)

theorem integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hh : 0 ≤ h) (S : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun x => matrixMaxEntryNorm (copyArrayTruncatedCovariance μ ξ x h - S)) μ := by
  simpa only [matrixMaxEntryNorm, Matrix.sub_apply] using
    (integrable_copyArrayTruncatedCovariance_sub_const ξ hξ hind hh S).norm

/-- Truncation preserves the actual fourth-moment budget of the paired
increments, and the independent-copy estimate contributes its factor 16. -/
theorem pairedTruncatedArray_fourth_budget
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hh : 0 ≤ h)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (j : Fin p) :
    (∑ i, ∫ z, pairedTruncatedArray ξ h i z j ^ 4 ∂μ.prod μ) ≤ 16 * D := by
  have hY (i : Fin n) : Measurable (pairedTruncatedArray ξ h i) :=
    C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h
  have hc (i : Fin n) (k : Fin p) :
      ∀ᵐ z ∂μ.prod μ, |pairedTruncatedArray ξ h i z k| ≤ h := by
    apply ae_of_all
    intro z
    calc
      _ ≤ ‖pairedTruncatedArray ξ h i z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (pairedTruncatedArray ξ h i z) k
      _ ≤ h := C4Test.norm_pairedTruncatedIncrement_le _ _ hh
  have hs (i : Fin n) :
      (∫ z, pairedTruncatedArray ξ h i z j ^ 4 ∂μ.prod μ) ≤
        16 * ∫ ω, ξ i ω j ^ 4 ∂μ := by
    calc
      _ ≤ ∫ z, pairedIncrement ξ i z j ^ 4 ∂μ.prod μ :=
        integral_mono (integrable_coordinate_pow_of_bounded hY hc i j 4)
          (integrable_pairedIncrement_fourth μ ξ hξ i j (hi4 i j)) (fun z => by
            dsimp [pairedTruncatedArray, pairedTruncatedIncrement, pairedIncrement]
            split_ifs
            · exact le_rfl
            · simp only [Pi.zero_apply, zero_pow (by decide : 4 ≠ 0)]
              positivity)
      _ ≤ _ := integral_pairedIncrement_fourth_le μ ξ hξ i j (hi4 i j)
  calc
    _ ≤ ∑ i, 16 * ∫ ω, ξ i ω j ^ 4 ∂μ := Finset.sum_le_sum (fun i _ => hs i)
    _ = 16 * (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hfourth j) (by norm_num)

/-- The fluctuation estimate now starts from the actual original summands
and ends at the paper's actual matrix `T_h-E T_h`. -/
theorem expected_copyArrayTruncatedCovariance_fluctuation_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) :
    (∫ x, ‖fun j k => copyArrayTruncatedCovariance μ ξ x h j k -
      ∫ w, copyArrayTruncatedCovariance μ ξ w h j k ∂μ‖ ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
  have hY (i : Fin n) : Measurable (pairedTruncatedArray ξ h i) :=
    C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h
  have hbound (i : Fin n) : ∀ᵐ z ∂μ.prod μ, ‖pairedTruncatedArray ξ h i z‖ ≤ h :=
    ae_of_all _ (fun z => C4Test.norm_pairedTruncatedIncrement_le _ _ hh.le)
  have hb := expected_half_copyAverage_centeredRankOneSum_norm_le μ μ hY
    (iIndepFun_pairedTruncatedArray μ ξ hξ hind h) hp hh (by positivity : 0 ≤ 16 * D)
    hbound (pairedTruncatedArray_fourth_budget ξ hξ hh.le hi4 hfourth)
  have he := half_copyAverage_centeredRankOnePiSum_paired_ae_eq ξ hξ hind hh.le
  have henorm := he.fun_comp (fun M : Fin p → Fin p → ℝ => ‖M‖)
  simp only [Function.comp_def] at henorm
  rw [integral_congr_ae henorm] at hb
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hsqrt : Real.sqrt ((16 * D) * dimensionLog p) = 4 * Real.sqrt (D * dimensionLog p) := by
    have hs16 : Real.sqrt (16 : ℝ) = 4 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    rw [show (16 * D) * dimensionLog p = 16 * (D * dimensionLog p) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), hs16]
  rw [hsqrt] at hb
  have hC : 0 ≤ matrixFluctuationConstant := by unfold matrixFluctuationConstant; positivity
  have hn := mul_nonneg hC (mul_nonneg (sq_nonneg h) hL)
  nlinarith

end
end RectangleCLT.Companion.SplitV4
