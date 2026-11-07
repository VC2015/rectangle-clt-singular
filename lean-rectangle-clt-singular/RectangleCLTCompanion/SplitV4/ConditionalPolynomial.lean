import RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds
import RectangleCLTCompanion.SplitV4.ConditionalExceptionalMaximum
import RectangleCLTCompanion.SplitV4.UnrestrictedGaussianComparison
import RectangleCLTCompanion.SubexponentialBounded
import RectangleCLTCompanion.SubexponentialTransfer
import RectangleCLTCompanion.SubexponentialScales
import RectangleCLTCompanion.SplitV4.PairedNormalization

/-!
Conditional bounded approximation for the polynomial-moment truncation.
All conditional laws and covariance matrices below are the concrete laws
constructed from the nonidentical original marginal distributions.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Rect

/-- Translation pulls back every interval convention exactly. -/
def pullbackAdd {p : ℕ} (R : Rect p) (r : Vector p) : Rect p where
  interval j := (fun x : ℝ => x + r j) ⁻¹' R.interval j
  ordConnected j := (R.ordConnected j).preimage_mono (fun _ _ h => add_le_add_right h _)
  measurable j := (R.measurable j).preimage (measurable_id.add measurable_const)

@[simp] theorem carrier_pullbackAdd {p : ℕ} (R : Rect p) (r : Vector p) :
    (R.pullbackAdd r).carrier = (fun x : Vector p => x + r) ⁻¹' R.carrier := rfl

end RectangleCLT.Rect

namespace RectangleCLT.Companion.SplitV4
noncomputable section

set_option autoImplicit false

/-- Only a positive lower marginal variance bound is needed to standardize
the bounded theorem. Off-diagonal gaps and covariance rank are unrestricted. -/
theorem boundedRectangleDistanceCLT_of_marginal_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlower : ∀ j, (1 / 4 : ℝ) ≤ covariance μ (sumVector ξ) j j)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤
      (2 * companionUniversalConstant) * min 1 (unrestrictedRate (2 * δ) (dimensionLog p)) := by
  let d : Vector p := fun j => Real.sqrt (covariance μ (sumVector ξ) j j)
  have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j := by
    have hs := Real.sqrt_le_sqrt (hlower j)
    have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
    simpa only [hquarter] using hs
  have hvar (j : Fin p) : covariance μ (sumVector ξ) j j = d j ^ 2 :=
    (Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (hlower j))).symm
  exact rectangleDistance_le μ (sumVector ξ) A
    (bounded_unrestrictedCLT_after_standardization h hp hn d hd hvar A hA)

/-- Normalize the actual retained array before invoking the bounded CLT. -/
theorem conditionalRetained_normalized_boundedIndependent {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) :
    BoundedIndependentHypotheses (conditionalGoodProductLaw μ T)
      (normalizedSummands (conditionalRetainedSummand μ T mask))
      (2 * T / Real.sqrt (n : ℝ)) := by
  have hh := (conditionalRetained_boundedIndependent μ hT mask).smul_of_nonneg
    (Real.sqrt (n : ℝ))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  simpa only [normalizedSummands, div_eq_mul_inv, mul_comm] using hh

/-- Entrywise covariance closeness to unit reference marginals is enough
to place the retained component within the bounded theorem's scope. -/
theorem conditionalRetained_marginal_lower_bound {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - S) ≤ 1 / 2)
    (j : Fin p) :
    (1 / 4 : ℝ) ≤ covariance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T mask)) j j := by
  have he : |conditionalCovarianceForMask μ T mask j j - S j j| ≤ 1 / 2 := by
    have he := ((norm_le_pi_norm (fun k =>
      (conditionalCovarianceForMask μ T mask - S) j k) j).trans
      (norm_le_pi_norm (fun j k => (conditionalCovarianceForMask μ T mask - S) j k) j)).trans hgood
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using he
  rw [hS j] at he
  rw [conditionalRetained_normalized_covariance μ hT mask]
  change (1 / 4 : ℝ) ≤ conditionalCovarianceForMask μ T mask j j
  linarith [(abs_le.mp he).1]

theorem conditionalRetainedRectangleDistanceCLT {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - S) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T mask) :
    rectangleDistance (conditionalGoodProductLaw μ T)
      (normalizedObservationSum (conditionalRetainedSummand μ T mask)) A ≤
      (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  have hc : covariance (conditionalGoodProductLaw μ T)
      (sumVector (normalizedSummands (conditionalRetainedSummand μ T mask))) =
        conditionalCovarianceForMask μ T mask := by
    rw [sumVector_normalizedSummands]
    ext j k
    exact conditionalRetained_normalized_covariance μ hT mask j k
  have hl := conditionalRetained_marginal_lower_bound μ hT mask S hS hgood
  rw [← sumVector_normalizedSummands] at hl
  have hh := boundedRectangleDistanceCLT_of_marginal_lower_bound
    (conditionalRetained_normalized_boundedIndependent μ hT mask) hp hn hl A (hA.trans hc.symm)
  rw [sumVector_normalizedSummands] at hh
  convert hh using 1
  congr 3
  ring

/-- The actual fixed exceptional contribution, normalized and summed. -/
def conditionalNormalizedShift {p n : ℕ} (μ : Fin n → Measure (Vector p))
    (T : ℝ) (tag : TruncationTag p n) : Vector p :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, conditionalExceptionalShift μ T tag.1 tag.2 i

theorem normalized_selectConditionalArrays {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (tag : TruncationTag p n)
    (g : Fin n → Vector p) :
    normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
      (selectConditionalArrays tag.1 (tag.2, g)) =
      normalizedObservationSum (conditionalRetainedSummand μ T tag.1) g +
        conditionalNormalizedShift μ T tag := by
  rw [selectConditionalArrays_eq_retained_add_shift μ T tag.1 tag.2 g]
  simp only [normalizedObservationSum, sumVector, conditionalNormalizedShift,
    Finset.sum_add_distrib, smul_add]

/-- Exact full-rectangle identity for every actual kernel draw. The Gaussian
is shifted by the same observed exceptional data, before any shell bound. -/
theorem conditionalKernel_rectangle_error_eq {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (tag : TruncationTag p n) (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    |(conditionalTruncationKernel μ T tag).real
        ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier) -
      (gaussianLaw A).real ((fun x => x + conditionalNormalizedShift μ T tag) ⁻¹' R.carrier)| =
      rectangleError (conditionalGoodProductLaw μ T)
        (normalizedObservationSum (conditionalRetainedSummand μ T tag.1)) A
        (R.pullbackAdd (conditionalNormalizedShift μ T tag)) := by
  have hm : Measurable (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) := by
    unfold normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  rw [conditionalTruncationKernel_apply]
  have hsel : Measurable (fun g => selectConditionalArrays tag.1 (tag.2, g)) :=
    (measurable_selectConditionalArrays tag.1).comp (measurable_const.prodMk measurable_id)
  rw [Measure.real, Measure.map_apply hsel (R.measurableSet_carrier.preimage hm)]
  have hpre : (fun g => selectConditionalArrays tag.1 (tag.2, g)) ⁻¹'
      ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier) =
      (normalizedObservationSum (conditionalRetainedSummand μ T tag.1)) ⁻¹'
        (R.pullbackAdd (conditionalNormalizedShift μ T tag)).carrier := by
    ext g
    simp only [Set.mem_preimage, Rect.carrier_pullbackAdd]
    rw [normalized_selectConditionalArrays μ T tag g]
  simp only [hpre, rectangleError, Measure.real, Rect.carrier_pullbackAdd]

/-- The exact good-kernel shifted comparison applies to all measurable
rectangle endpoint conventions and arbitrary fixed exceptional values. -/
theorem conditionalGoodKernel_shifted_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀ j, S j j = 1)
    (hgood : matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - S) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T tag.1) (R : Rect p) :
    |(conditionalTruncationKernel μ T tag).real
        ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier) -
      (gaussianLaw A).real ((fun x => x + conditionalNormalizedShift μ T tag) ⁻¹' R.carrier)| ≤
      (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
  rw [conditionalKernel_rectangle_error_eq]
  exact (rectangleError_le_rectangleDistance _ _ _ _).trans
    (conditionalRetainedRectangleDistanceCLT μ hT tag.1 hp hn S hS hgood A hA)

theorem proxyCovarianceDiscrepancy_eq_matrixMaxEntryNorm {p : ℕ}
    (S Q : Matrix (Fin p) (Fin p) ℝ) :
    proxyCovarianceDiscrepancy Q S = matrixMaxEntryNorm (Q - S) := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨norm_nonneg _, ?_⟩
    intro jk _
    have he := (norm_le_pi_norm (fun k => (Q - S) jk.1 k) jk.2).trans
      (norm_le_pi_norm (fun j k => (Q - S) j k) jk.1)
    simpa only [matrixMaxEntryNorm, Matrix.sub_apply, Real.norm_eq_abs] using he
  · apply (pi_norm_le_iff_of_nonneg (proxyCovarianceDiscrepancy_nonneg Q S)).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (proxyCovarianceDiscrepancy_nonneg Q S)).mpr
    intro k
    simpa only [Real.norm_eq_abs] using abs_entry_sub_le_proxyCovarianceDiscrepancy Q S j k

/-- A deterministic translation of the actual singular Gaussian costs
only its maximum-coordinate displacement and the Gaussian shell constant. -/
theorem gaussian_translation_rectangle_error_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1)
    (r : Vector p) (R : Rect p) :
    rectangleError (gaussianLaw B) (fun x => x + r) B R ≤
      12 * Real.exp (3 / 2 : ℝ) * ‖r‖ * Real.sqrt (dimensionLog p) := by
  by_cases hr : ‖r‖ = 0
  · have hr0 : r = 0 := norm_eq_zero.mp hr
    simp only [hr0, add_zero, rectangleError, Set.preimage_id, Set.preimage_id', sub_self, abs_zero,
      norm_zero, mul_zero, zero_mul, le_refl]
  have hrp : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
  have hbad : (gaussianLaw B).real {x : Vector p | ‖r‖ < ‖(x + r) - x‖} ≤ 0 := by
    simp only [add_sub_cancel_left, lt_self_iff_false, Set.setOf_false,
      measureReal_empty, le_refl]
  have hbad0 : (gaussianLaw B).real {x : Vector p | (0 : ℝ) < ‖x - x‖} ≤ 0 := by simp
  have hc := rectangleError_le_of_two_couplings hp (gaussianLaw B) (gaussianLaw B)
    (fun x => x + r) id id id (measurable_id.add measurable_const) measurable_id B
    Measure.map_id hB (r₁ := ‖r‖) (r₂ := 0) (ε₁ := 0) (ε₂ := 0) (B := 0)
    (by simpa only [add_zero] using hrp) (fun Q => by simp) hbad hbad0 R
  simpa only [zero_add, add_zero] using hc

/-- For each good exceptional tag, the actual conditional probability is
compared with the original reference Gaussian. The three terms are the
bounded CLT, covariance comparison and deterministic exceptional shift. -/
theorem conditionalGoodKernel_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1)
    (hgood : matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T tag.1 - B * B.transpose) ≤ 1 / 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = conditionalCovarianceForMask μ T tag.1) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ≤
      (2 * companionUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant * min 1
          (dimensionLog p * Real.sqrt
            (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose))) +
        12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ * Real.sqrt (dimensionLog p) := by
  let r := conditionalNormalizedShift μ T tag
  have hc := conditionalGoodKernel_shifted_rectangle_error_le μ hT tag hp hn
    (B * B.transpose) hB hgood A hA R
  have hg := (rectangleError_le_rectangleDistance (gaussianLaw A) id B
    (R.pullbackAdd r)).trans (unrestrictedGaussianComparison hp A B hB)
  rw [hA, proxyCovarianceDiscrepancy_eq_matrixMaxEntryNorm] at hg
  have hs := gaussian_translation_rectangle_error_le hp B hB r R
  have ht := abs_sub_le
    ((conditionalTruncationKernel μ T tag).real
      ((normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) ⁻¹' R.carrier))
    ((gaussianLaw A).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw B).real R.carrier)
  have ht' := abs_sub_le ((gaussianLaw A).real ((fun x => x + r) ⁻¹' R.carrier))
    ((gaussianLaw B).real ((fun x => x + r) ⁻¹' R.carrier)) ((gaussianLaw B).real R.carrier)
  simp only [rectangleError, Rect.carrier_pullbackAdd, Set.preimage_id] at hg hs ⊢
  exact ht.trans ((add_le_add hc (ht'.trans (add_le_add hg hs))).trans_eq (by ring))

/-- The retained covariance has an actual square Gaussian factor, chosen
from its positive semidefinite covariance rather than supplied analytically. -/
theorem conditionalRetained_gaussian_factor_exists {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = conditionalCovarianceForMask μ T mask := by
  have hb := conditionalRetained_normalized_boundedIndependent μ hT mask
  have hL2 (i : Fin n) (j : Fin p) : MemLp
      (fun x => normalizedSummands (conditionalRetainedSummand μ T mask) i x j)
      (2 : ℝ≥0∞) (conditionalGoodProductLaw μ T) := by
    apply (memLp_two_iff_integrable_sq
      ((measurable_pi_apply j).comp (hb.measurable i)).aestronglyMeasurable).mpr
    exact integrable_coordinate_pow_of_bounded hb.measurable hb.abs_coordinate_le i j 2
  obtain ⟨A, hA⟩ := gaussian_factor_exists_of_centered_array hL2 hb.centered
  refine ⟨A, hA.trans ?_⟩
  rw [sumVector_normalizedSummands]
  ext j k
  exact conditionalRetained_normalized_covariance μ hT mask j k

/-- A pointwise estimate on every exceptional tag. The term `2 Delta`
pays for bad covariance tags, so later averaging uses the actual expected
covariance discrepancy without postulating a conditional approximation. -/
theorem conditionalKernel_rectangle_error_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (tag : TruncationTag p n) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1) (R : Rect p) :
    rectangleError (conditionalTruncationKernel μ T tag)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ≤
      (2 * companionUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant *
          (dimensionLog p * Real.sqrt
            (matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose))) +
        12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ * Real.sqrt (dimensionLog p) +
        2 * matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose) := by
  let d := matrixMaxEntryNorm (conditionalCovarianceForMask μ T tag.1 - B * B.transpose)
  have hd : 0 ≤ d := norm_nonneg _
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hC : 0 ≤ unrestrictedGaussianComparisonConstant :=
    zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant
  by_cases hgood : d ≤ 1 / 2
  · obtain ⟨A, hA⟩ := conditionalRetained_gaussian_factor_exists μ hT tag.1
    have hc := conditionalGoodKernel_rectangle_error_le μ hT tag hp hn B hB hgood A hA R
    have hmin := mul_le_mul_of_nonneg_left
      (min_le_right (1 : ℝ) (dimensionLog p * Real.sqrt d)) hC
    dsimp only [d] at hmin
    exact (hc.trans (add_le_add_right (add_le_add_left hmin _) _)).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) hd))
  · have hbad : 1 ≤ 2 * d := by linarith [lt_of_not_ge hgood]
    have hbounded : 0 ≤ (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) := by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (zero_le_one.trans one_le_companionUniversalConstant))
        (le_min (by norm_num)
          (unrestrictedRate_nonneg (div_nonneg (mul_nonneg (by norm_num) hT)
            (Real.sqrt_nonneg _)) hL))
    have hcov := mul_nonneg hC (mul_nonneg hL (Real.sqrt_nonneg d))
    have hshift : 0 ≤ 12 * Real.exp (3 / 2 : ℝ) * ‖conditionalNormalizedShift μ T tag‖ *
        Real.sqrt (dimensionLog p) := by positivity
    exact (rectangleError_le_one _ _ _ R).trans
      (hbad.trans (le_add_of_nonneg_left (add_nonneg (add_nonneg hbounded hcov) hshift)))

/-- The concrete exceptional-data kernel obeys the total probability
identity under the original product law, for every measurable array event. -/
theorem integral_conditionalKernel_probability {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (S : Set (Fin n → Vector p)) (hS : MeasurableSet S) :
    (Measure.pi μ).real S =
      ∫ x, (conditionalTruncationKernel μ T
        (observedTruncationMask T x, observedExceptionalArray T x)).real S ∂Measure.pi μ := by
  let K := conditionalTruncationKernel μ T
  let F : TruncationTag p n × (Fin n → Vector p) → ℝ :=
    fun z => S.indicator (fun _ => (1 : ℝ)) z.2
  let G : TruncationTag p n × (Fin n → Vector p) → ℝ :=
    fun z => (K z.1).real S
  have hF : Measurable F := (measurable_const.indicator hS).comp measurable_snd
  have hG : Measurable G := (K.measurable_coe hS).ennreal_toReal.comp measurable_fst
  have hFb (z) : |F z| ≤ 1 := by
    dsimp only [F]
    by_cases hz : z.2 ∈ S <;> simp [hz]
  have hGb (z) : |G z| ≤ 1 := by
    dsimp only [G]
    rw [abs_of_nonneg (measureReal_nonneg)]
    exact measureReal_le_one
  have heF := integral_product_conditionalTruncationKernel μ T F hF 1 hFb
  have heG := integral_product_conditionalTruncationKernel μ T G hG 1 hGb
  have hiF : (∫ x, F ((observedTruncationMask T x, observedExceptionalArray T x), x)
      ∂Measure.pi μ) = (Measure.pi μ).real S := by
    exact integral_indicator_one hS
  rw [hiF] at heF
  rw [heF, heG]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun b => by
    simp only [F, G, integral_indicator_one hS, integral_const,
      measureReal_univ_eq_one, one_smul]
    exact integral_indicator_one hS

theorem integrable_observedConditionalCovarianceDeviation {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun x => matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T (observedTruncationMask T x) - S)) (Measure.pi μ) := by
  let f : (Fin n → Bool) → ℝ := fun mask =>
    matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - S)
  have hm : Measurable (fun x : Fin n → Vector p => f (observedTruncationMask T x)) :=
    (measurable_of_countable f).comp (measurable_observedTruncationMask T)
  have hfn (mask) : 0 ≤ f mask := norm_nonneg _
  apply (integrable_const (∑ mask, f mask)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]
    exact Finset.single_le_sum (fun (mask : Fin n → Bool) _ => hfn mask)
      (Finset.mem_univ (observedTruncationMask T x))

theorem integrable_sqrt_of_integrable_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) :
    Integrable (fun x => Real.sqrt (f x)) μ := by
  apply (hf.add (integrable_const 1)).mono'
    (Real.continuous_sqrt.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    have hs := Real.sq_sqrt (hfn x)
    have hn := Real.sqrt_nonneg (f x)
    simp only [Function.comp_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    nlinarith [sq_nonneg (Real.sqrt (f x) - 1)]

/-- Square-root Jensen with all Bochner integrability obligations explicit. -/
theorem integral_sqrt_le_sqrt_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) :
    (∫ x, Real.sqrt (f x) ∂μ) ≤ Real.sqrt (∫ x, f x ∂μ) := by
  have his := integrable_sqrt_of_integrable_nonneg μ f hf hfn
  let m := ∫ x, f x ∂μ
  have hm : 0 ≤ m := integral_nonneg hfn
  by_cases hmz : m = 0
  · have hzero : ∀ᵐ x ∂μ, f x = 0 := (integral_eq_zero_iff_of_nonneg hfn hf).mp hmz
    have hs0 : (fun x => Real.sqrt (f x)) =ᵐ[μ] 0 := hzero.mono (fun _ hx => by simp [hx])
    rw [integral_congr_ae hs0]
    simp only [Pi.zero_apply, integral_zero, ← show m = ∫ x, f x ∂μ from rfl, hmz,
      Real.sqrt_zero, le_refl]
  have hmp : 0 < m := hm.lt_of_ne' hmz
  have hsmp : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmp
  have hbound (x : Ω) : Real.sqrt (f x) ≤ (f x + m) / (2 * Real.sqrt m) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsmp)).mpr
    have hs := Real.sq_sqrt (hfn x)
    have hsm := Real.sq_sqrt hm
    nlinarith [sq_nonneg (Real.sqrt (f x) - Real.sqrt m)]
  have hb := integral_mono his ((hf.add (integrable_const m)).div_const _) hbound
  have he : (∫ x, (f x + m) / (2 * Real.sqrt m) ∂μ) = Real.sqrt m := by
    rw [integral_div, integral_add hf (integrable_const m), integral_const]
    simp only [measureReal_univ_eq_one, one_smul]
    change (m + m) / (2 * Real.sqrt m) = Real.sqrt m
    apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) hsmp))).mpr
    nlinarith [Real.sq_sqrt hm]
  exact hb.trans_eq he

theorem rectangleError_le_integral_conditionalKernel_rectangleError {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ≤
      ∫ x, rectangleError (conditionalTruncationKernel μ T
        (observedTruncationMask T x, observedExceptionalArray T x))
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R ∂Measure.pi μ := by
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hW : Measurable W := by
    unfold W normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  let S := W ⁻¹' R.carrier
  have hS : MeasurableSet S := R.measurableSet_carrier.preimage hW
  let k : (Fin n → Vector p) → ℝ := fun x =>
    (conditionalTruncationKernel μ T (observedTruncationMask T x, observedExceptionalArray T x)).real S
  have hkm : Measurable k :=
    ((conditionalTruncationKernel μ T).measurable_coe hS).ennreal_toReal.comp
      ((measurable_observedTruncationMask T).prodMk (measurable_observedExceptionalArray T))
  have hki : Integrable k (Measure.pi μ) := (integrable_const (1 : ℝ)).mono'
    hkm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  let c := (gaussianLaw B).real R.carrier
  have he := integral_sub hki (integrable_const c)
  simp only [Pi.sub_apply, integral_const, measureReal_univ_eq_one, one_smul] at he
  have ht := integral_conditionalKernel_probability μ T S hS
  have hn := norm_integral_le_integral_norm (fun x => k x - c) (μ := Measure.pi μ)
  rw [he, ← ht] at hn
  simpa only [rectangleError, Real.norm_eq_abs, W, k, S, c] using hn

/-- The logarithmic correction of the bounded input is at most `log(en)`
at the conditional threshold scale. The threshold lower bound follows
from the paper's `B ≥ 1` and `T ≥ 2 B`. -/
theorem conditionalBoundedRate_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {T : ℝ} (hT : (1 / 4 : ℝ) ≤ T) :
    unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p) ≤
      4 * (T / Real.sqrt (n : ℝ) * dimensionLog p ^ (3 / 2 : ℝ) *
        Real.sqrt (dimensionLog n)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hsL : 1 ≤ Real.sqrt (dimensionLog p) := Real.one_le_sqrt.mpr hL
  have hTp : 0 < T := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hT
  have hden : 0 < (4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p) := by positivity
  have hprod : 1 ≤ ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) *
      Real.sqrt (n : ℝ) := by
    have he : ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) *
        Real.sqrt (n : ℝ) = (4 * T) * Real.sqrt (dimensionLog p) := by field_simp
    rw [he]
    nlinarith
  have hrecip : 1 / ((4 * T / Real.sqrt (n : ℝ)) * Real.sqrt (dimensionLog p)) ≤ n := by
    have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnR
    have hs2 := Real.sq_sqrt hnpos.le
    have hsle : Real.sqrt (n : ℝ) ≤ n := by nlinarith
    exact ((div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hprod)).trans hsle
  have hD : D_L (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p) ≤ dimensionLog n := by
    rw [dimensionLog_eq_one_add_log hn]
    unfold D_L
    have hl := logPlus_mono (one_div_pos.mpr hden) hrecip
    have hlog : logPlus (n : ℝ) = Real.log (n : ℝ) :=
      max_eq_right (Real.log_nonneg hnR)
    rw [hlog] at hl
    exact add_le_add_left hl 1
  have hsqrt := Real.sqrt_le_sqrt hD
  unfold unrestrictedRate
  calc
    _ ≤ (4 * T / Real.sqrt (n : ℝ)) * dimensionLog p ^ (3 / 2 : ℝ) *
        Real.sqrt (dimensionLog n) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = _ := by ring

/-- Averaging the actual exceptional-data kernel gives a full rectangle
distance bound in terms of its genuine shift expectation and covariance
deviation. No conditional approximation estimate is an input. -/
theorem conditionalPolynomial_raw_rectangleDistance_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : ∀ j, (B * B.transpose) j j = 1)
    (hR : Integrable (fun x => ‖conditionalNormalizedShift μ T
      (observedTruncationMask T x, observedExceptionalArray T x)‖) (Measure.pi μ)) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B ≤
      (2 * companionUniversalConstant) *
          min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p)) +
        unrestrictedGaussianComparisonConstant * dimensionLog p * Real.sqrt
          (∫ x, matrixMaxEntryNorm
            (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose) ∂Measure.pi μ) +
        12 * Real.exp (3 / 2 : ℝ) *
          (∫ x, ‖conditionalNormalizedShift μ T
            (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) *
              Real.sqrt (dimensionLog p) +
        2 * (∫ x, matrixMaxEntryNorm
          (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose) ∂Measure.pi μ) := by
  let d : (Fin n → Vector p) → ℝ := fun x => matrixMaxEntryNorm
    (conditionalCovarianceForMask μ T (observedTruncationMask T x) - B * B.transpose)
  let r : (Fin n → Vector p) → ℝ := fun x => ‖conditionalNormalizedShift μ T
    (observedTruncationMask T x, observedExceptionalArray T x)‖
  let a := (2 * companionUniversalConstant) *
    min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) (dimensionLog p))
  let c := unrestrictedGaussianComparisonConstant
  let k := 12 * Real.exp (3 / 2 : ℝ)
  let L := dimensionLog p
  have hiD := integrable_observedConditionalCovarianceDeviation μ T (B * B.transpose)
  have hiS := integrable_sqrt_of_integrable_nonneg (Measure.pi μ) d hiD (fun _ => norm_nonneg _)
  have hi1 : Integrable (fun x => a + c * (L * Real.sqrt (d x))) (Measure.pi μ) :=
    (integrable_const a).add ((hiS.const_mul L).const_mul c)
  have hi2 : Integrable (fun x => a + c * (L * Real.sqrt (d x)) + k * r x * Real.sqrt L)
      (Measure.pi μ) := hi1.add ((hR.const_mul k).mul_const (Real.sqrt L))
  have hi3 : Integrable (fun x => a + c * (L * Real.sqrt (d x)) + k * r x * Real.sqrt L + 2 * d x)
      (Measure.pi μ) := hi2.add (hiD.const_mul 2)
  have he1 := integral_add (integrable_const a) ((hiS.const_mul L).const_mul c)
  have he2 := integral_add hi1 ((hR.const_mul k).mul_const (Real.sqrt L))
  have he3 := integral_add hi2 (hiD.const_mul 2)
  simp only [Pi.add_apply, integral_const, measureReal_univ_eq_one, one_smul,
    integral_const_mul, integral_mul_const] at he1 he2 he3
  have hj := integral_sqrt_le_sqrt_integral (Measure.pi μ) d hiD (fun _ => norm_nonneg _)
  have hjc := mul_le_mul_of_nonneg_left hj
    (mul_nonneg (zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))
  apply rectangleDistance_le
  intro R
  have hiE : Integrable (fun x => rectangleError (conditionalTruncationKernel μ T
      (observedTruncationMask T x, observedExceptionalArray T x))
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) B R) (Measure.pi μ) := by
    let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
    have hW : Measurable W := by
      unfold W normalizedObservationSum sumVector
      exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
    have hm : Measurable (fun x : Fin n → Vector p =>
        |(conditionalTruncationKernel μ T (observedTruncationMask T x,
          observedExceptionalArray T x)).real (W ⁻¹' R.carrier) - (gaussianLaw B).real R.carrier|) :=
      (((conditionalTruncationKernel μ T).measurable_coe
      (R.measurableSet_carrier.preimage hW)).ennreal_toReal.comp
        ((measurable_observedTruncationMask T).prodMk (measurable_observedExceptionalArray T))).sub
      measurable_const |>.abs
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact rectangleError_le_one _ _ _ R
  have hb := integral_mono hiE hi3 (fun x => conditionalKernel_rectangle_error_le
    μ hT (observedTruncationMask T x, observedExceptionalArray T x) hp hn B hB R)
  rw [he3, he2, he1] at hb
  have hdist := (rectangleError_le_integral_conditionalKernel_rectangleError μ T B R).trans hb
  have hjc' : c * (L * ∫ x, Real.sqrt (d x) ∂Measure.pi μ) ≤
      c * L * Real.sqrt (∫ x, d x ∂Measure.pi μ) := by
    change c * L * (∫ x, Real.sqrt (d x) ∂Measure.pi μ) ≤
      c * L * Real.sqrt (∫ x, d x ∂Measure.pi μ) at hjc
    simpa only [mul_assoc] using hjc
  exact hdist.trans (add_le_add_right (add_le_add_right (add_le_add_left hjc' a) _) _)

/-- A fixed universal constant for the Appendix E threshold transfer. -/
def conditionalPolynomialConstant : ℝ :=
  1 + 8 * companionUniversalConstant + 3 * unrestrictedGaussianComparisonConstant +
    24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12

theorem one_le_conditionalPolynomialConstant : 1 ≤ conditionalPolynomialConstant := by
  have hc := one_le_companionUniversalConstant
  have hg := one_le_unrestrictedGaussianComparisonConstant
  have he := one_le_envelopeMaximumConstant
  have hep : 0 ≤ 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant := by positivity
  unfold conditionalPolynomialConstant
  linarith

/-- The actual threshold rate in Appendix E, before saturation by one. -/
def conditionalPolynomialThresholdRate (n p : ℕ) (B T q : ℝ) : ℝ :=
  T / Real.sqrt (n : ℝ) * dimensionLog p ^ (3 / 2 : ℝ) * Real.sqrt (dimensionLog n) +
    dimensionLog p * Real.sqrt (truncationVarianceBudget B T q) + polynomialEnvelopeV n p B q

/-- Appendix E's threshold estimate for the actual nonidentical product
array. It uses only genuine envelope moments, centering and unit average
marginal variances; no coordinate fourth-moment bound is imposed. -/
theorem conditionalPolynomial_threshold {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (A : Matrix (Fin p) (Fin p) ℝ) (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hfactor : A * A.transpose = covariance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i))) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let i : Fin n := ⟨0, by omega⟩
  let v := truncationVarianceBudget B T q
  let L := dimensionLog p
  let t := T / Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ) * Real.sqrt (dimensionLog n)
  let z := L * Real.sqrt v
  let w := polynomialEnvelopeV n p B q
  have hv : 0 ≤ v := (h i).varianceBudget_nonneg
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hT : 0 ≤ T := (h i).threshold_pos.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hz : 0 ≤ z := mul_nonneg (zero_le_one.trans hL) (Real.sqrt_nonneg _)
  have hw : 0 ≤ w := by unfold w polynomialEnvelopeV; positivity
  have hTquarter : (1 / 4 : ℝ) ≤ T := by linarith [(h i).threshold]
  have hC : 1 ≤ conditionalPolynomialConstant := one_le_conditionalPolynomialConstant
  change rectangleDistance (Measure.pi μ)
    (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalPolynomialConstant * min 1 (t + z + w)
  by_cases hvone : v ≤ 1
  · have hiR : Integrable (fun x => ‖conditionalNormalizedShift μ T
        (observedTruncationMask T x, observedExceptionalArray T x)‖) (Measure.pi μ) := by
      simpa only [conditionalNormalizedShift] using observed_exceptional_shift_norm_integrable μ h
    have hraw := conditionalPolynomial_raw_rectangleDistance_le μ hT hp hn A hunit hiR
    have hd := expected_conditional_covariance_deviation_actual μ h hn
    rw [← hfactor] at hd
    have hds : Real.sqrt (∫ x, matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
        3 * Real.sqrt v := by
      apply (Real.sqrt_le_sqrt hd).trans
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt hv]
    have hvz : v ≤ z := by
      have hs : v ≤ Real.sqrt v := by
        nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
      exact hs.trans (by dsimp only [z]; nlinarith [Real.sqrt_nonneg v])
    have hbounded : (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) L) ≤
        (8 * companionUniversalConstant) * t := by
      have hb := (min_le_right (1 : ℝ) (unrestrictedRate (4 * T / Real.sqrt (n : ℝ)) L)).trans
        (conditionalBoundedRate_le hp hn hTquarter)
      have hm := mul_le_mul_of_nonneg_left hb
        (by linarith [one_le_companionUniversalConstant] : 0 ≤ 2 * companionUniversalConstant)
      convert hm using 1
      ring
    have hgaussian := mul_le_mul_of_nonneg_left hds
      (mul_nonneg (zero_le_one.trans one_le_unrestrictedGaussianComparisonConstant) (zero_le_one.trans hL))
    have hshift := observed_exceptional_shift_maximum_le μ h hp hn
    have hshift' : 12 * Real.exp (3 / 2 : ℝ) *
        (∫ x, ‖conditionalNormalizedShift μ T
          (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) * Real.sqrt L ≤
        (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * (z + w) := by
      have hm := mul_le_mul_of_nonneg_left hshift
        (by positivity : 0 ≤ 12 * Real.exp (3 / 2 : ℝ))
      dsimp only [conditionalNormalizedShift, L, z, w, v]
      convert hm using 1 <;> ring
    have hbias1 : 2 * (∫ x, matrixMaxEntryNorm
        (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
        12 * v := by linarith [hd]
    have hbias := hbias1.trans (mul_le_mul_of_nonneg_left hvz (by norm_num : (0 : ℝ) ≤ 12))
    have hraw' : rectangleDistance (Measure.pi μ)
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
        (8 * companionUniversalConstant) * t +
          (3 * unrestrictedGaussianComparisonConstant) * z +
          (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * (z + w) + 12 * z := by
      have hg : unrestrictedGaussianComparisonConstant * L *
          Real.sqrt (∫ x, matrixMaxEntryNorm
            (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose) ∂Measure.pi μ) ≤
            (3 * unrestrictedGaussianComparisonConstant) * z := by
        convert hgaussian using 1
        ring
      exact hraw.trans (add_le_add (add_le_add (add_le_add hbounded hg) hshift') hbias)
    have hc1 : 8 * companionUniversalConstant ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      have hg := one_le_unrestrictedGaussianComparisonConstant
      have he := one_le_envelopeMaximumConstant
      have hep : 0 ≤ 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant := by positivity
      linarith
    have hc2 : 3 * unrestrictedGaussianComparisonConstant +
        24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12 ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      linarith [one_le_companionUniversalConstant]
    have hc3 : 24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant ≤ conditionalPolynomialConstant := by
      unfold conditionalPolynomialConstant
      linarith [one_le_companionUniversalConstant, one_le_unrestrictedGaussianComparisonConstant]
    have hrho : rectangleDistance (Measure.pi μ)
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
        conditionalPolynomialConstant * (t + z + w) := by
      calc
        _ ≤ _ := hraw'
        _ = (8 * companionUniversalConstant) * t +
            (3 * unrestrictedGaussianComparisonConstant +
              24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant + 12) * z +
            (24 * Real.exp (3 / 2 : ℝ) * envelopeMaximumConstant) * w := by ring
        _ ≤ conditionalPolynomialConstant * t + conditionalPolynomialConstant * z +
            conditionalPolynomialConstant * w := add_le_add
              (add_le_add (mul_le_mul_of_nonneg_right hc1 ht) (mul_le_mul_of_nonneg_right hc2 hz))
              (mul_le_mul_of_nonneg_right hc3 hw)
        _ = _ := by ring
    by_cases hs : 1 ≤ t + z + w
    · rw [min_eq_left hs, mul_one]
      exact (rectangleDistance_le_one _ _ _).trans hC
    · rw [min_eq_right (le_of_not_ge hs)]
      exact hrho
  · have hsqrt : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr (le_of_not_ge hvone)
    have hz1 : 1 ≤ z := by dsimp only [z]; nlinarith
    rw [min_eq_left (by linarith : 1 ≤ t + z + w), mul_one]
    exact (rectangleDistance_le_one _ _ _).trans hC

/-- The genuine marginal laws of a measurable independent array satisfy
the conditional-truncation moment contract. -/
theorem conditionalTruncationMomentHypotheses_marginal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    {B T q : ℝ} (hB : 1 ≤ B) (hT : 2 * B ≤ T) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0) (i : Fin n) :
    ConditionalTruncationMomentHypotheses (μ.map (X i)) B T q := by
  have hm : Measurable (fun x : Vector p => ‖x‖ ^ q) := measurable_norm.pow_const q
  refine ⟨zero_lt_one.trans_le hB, hT, hq, ?_, ?_, ?_⟩
  · exact (integrable_map_measure hm.aestronglyMeasurable (hX i).aemeasurable).mpr (hmoment i)
  · rw [integral_map (hX i).aemeasurable hm.aestronglyMeasurable]
    exact hbudget i
  · intro j
    rw [integral_map (hX i).aemeasurable (measurable_pi_apply j).aestronglyMeasurable]
    exact hcenter i j

theorem covariance_map_of_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (μ : Measure Ω) (F : Ω → E) (hF : Measurable F)
    (W : E → Vector p) (hW : Measurable W) :
    covariance (μ.map F) W = covariance μ (fun ω => W (F ω)) := by
  ext j k
  simp only [covariance]
  have hpair := integral_map (μ := μ) (f := fun x => W x j * W x k) hF.aemeasurable
    ((((measurable_pi_apply j).comp hW).mul ((measurable_pi_apply k).comp hW)).aestronglyMeasurable)
  have hj := integral_map (μ := μ) (f := fun x => W x j) hF.aemeasurable
    ((measurable_pi_apply j).comp hW).aestronglyMeasurable
  have hk := integral_map (μ := μ) (f := fun x => W x k) hF.aemeasurable
    ((measurable_pi_apply k).comp hW).aestronglyMeasurable
  rw [hpair, hj, hk]

/-- Exact transfer of normalized full rectangle errors to the actual
product of marginal laws. This uses nonidentical independence only. -/
theorem normalized_product_rectangleDistance_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (A : Matrix (Fin p) (Fin p) ℝ) :
    rectangleDistance (Measure.pi (fun i => μ.map (X i)))
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A =
      rectangleDistance μ (normalizedObservationSum X) A := by
  have htuple : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hind
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hW : Measurable W := by
    unfold W normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  have he (R : Rect p) : rectangleError (Measure.pi (fun i => μ.map (X i))) W A R =
      rectangleError μ (normalizedObservationSum X) A R := by
    rw [← hmap]
    unfold rectangleError Measure.real
    rw [Measure.map_apply htuple (R.measurableSet_carrier.preimage hW)]
    rfl
  unfold rectangleDistance
  congr 1
  exact congrArg Set.range (funext he)

/-- The threshold estimate on an arbitrary original probability space.
All moment assumptions concern the actual observations, and the Gaussian
uses the covariance of their actual normalized sum. -/
theorem polynomialEnvelope_threshold
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B T q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hT : 2 * B ≤ T) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hX i).aemeasurable
  have hm := conditionalTruncationMomentHypotheses_marginal μ X hX hB hT hq hmoment hbudget hcenter
  have htuple : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hind
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hW : Measurable W := by
    unfold W normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  have hcov : covariance (Measure.pi ν) W = covariance μ (normalizedObservationSum X) := by
    rw [← hmap, covariance_map_of_measurable μ _ htuple W hW]
    rfl
  have hh := conditionalPolynomial_threshold ν hm hp hn hB A hunit (hfactor.trans hcov.symm)
  rw [normalized_product_rectangleDistance_eq μ X hX hind] at hh
  exact hh

/-- The paper's original-observation formulation: unit average coordinate
second moments supply the target marginal variances, while the actual
Gaussian covariance remains unrestricted off its diagonal. -/
theorem polynomialEnvelope_threshold_of_average_variances
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B T q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hT : 2 * B ≤ T) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      conditionalPolynomialConstant * min 1 (conditionalPolynomialThresholdRate n p B T q) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hX i).aemeasurable
  have hm := conditionalTruncationMomentHypotheses_marginal μ X hX hB hT hq hmoment hbudget hcenter
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ := by
    apply (memLp_two_iff_integrable_sq
      ((measurable_pi_apply j).comp (hX i)).aestronglyMeasurable).mpr
    exact (integrable_map_measure ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
      (hX i).aemeasurable).mp ((hm i).integrable_coordinate_sq j)
  have hunit (j : Fin p) : (A * A.transpose) j j = 1 := by
    rw [hfactor]
    have hh := normalizedSummands_unit_covariance hind hL2 hcenter haverage j
    rw [sumVector_normalizedSummands] at hh
    exact hh
  exact polynomialEnvelope_threshold μ X hX hind hp hn hB hT hq hmoment hbudget hcenter A hunit hfactor

end
end RectangleCLT.Companion.SplitV4
