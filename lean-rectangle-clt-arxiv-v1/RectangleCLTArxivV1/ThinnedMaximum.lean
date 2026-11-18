import RectangleCLTArxivV1.SignedObservations
import RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration
import RectangleCLT.GaussianFourthSelectorBounds

/-! Expected maxima of the actual retained array. Removing independent
centered summands decreases the expected norm; the retained amplitude is
at most two on the comparison path. -/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- Adding an independent centered vector can only increase the expected norm. -/
theorem integral_norm_le_independent_add {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S X : Ω → Vector p) (hS : Measurable S) (hX : Measurable X)
    (hiS : Integrable S μ) (hiX : Integrable X μ)
    (hmX : (∫ ω, X ω ∂μ) = 0) (hind : IndepFun S X μ) :
    (∫ ω, ‖S ω‖ ∂μ) ≤ ∫ ω, ‖S ω + X ω‖ ∂μ := by
  have hid := independent_sum_shift_identDistrib μ (fun _ : Fin 1 => S)
    (fun _ => hS) X hX (by simpa [sumVector] using hind)
  have hh : IdentDistrib (fun ω => S ω + X ω)
      (fun z : Ω × Ω => S z.1 + X z.2) μ (μ.prod μ) := by
    simpa [sumVector] using hid
  have hi : Integrable (fun z : Ω × Ω => S z.1 + X z.2) (μ.prod μ) :=
    (integrable_fst_probability μ μ S hiS).add (integrable_snd_probability μ μ X hiX)
  rw [(hh.norm).integral_eq, integral_prod _ hi.norm]
  apply integral_mono hiS.norm hi.integral_norm_prod_left
  intro ω
  have heq : (∫ z, S ω + X z ∂μ) = S ω := by
    rw [integral_add (integrable_const _) hiX, hmX, integral_const]
    simp
  change ‖S ω‖ ≤ ∫ z, ‖S ω + X z‖ ∂μ
  calc
    ‖S ω‖ = ‖∫ z, S ω + X z ∂μ‖ := congrArg norm heq.symm
    _ ≤ _ := norm_integral_le_integral_norm _

theorem integral_norm_finset_sum_mono {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hmeas : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂μ) = 0)
    (S T : Finset (Fin n)) (hST : S ⊆ T) :
    (∫ ω, ‖∑ i ∈ S, ξ i ω‖ ∂μ) ≤ ∫ ω, ‖∑ i ∈ T, ξ i ω‖ ∂μ := by
  have hstep (R : Finset (Fin n)) (i : Fin n) (hi : i ∉ R) :
      (∫ ω, ‖∑ j ∈ R, ξ j ω‖ ∂μ) ≤ ∫ ω, ‖∑ j ∈ insert i R, ξ j ω‖ ∂μ := by
    have hh := integral_norm_le_independent_add μ (fun ω => ∑ j ∈ R, ξ j ω) (ξ i)
      (Finset.measurable_sum _ (fun j _ => hmeas j)) (hmeas i)
      (integrable_finset_sum _ (fun j _ => hint j)) (hint i) (hmean i)
      (by
        convert hind.indepFun_finset_sum_of_not_mem hmeas hi using 1
        ext ω
        simp only [Finset.sum_apply])
    simpa [Finset.sum_insert hi, add_comm] using hh
  have haux (R : Finset (Fin n)) :
      (∫ ω, ‖∑ i ∈ S, ξ i ω‖ ∂μ) ≤ ∫ ω, ‖∑ i ∈ S ∪ R, ξ i ω‖ ∂μ := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert i R hi ih =>
      by_cases his : i ∈ S ∪ R
      · simpa [Finset.union_insert, Finset.insert_eq_of_mem his] using ih
      · exact ih.trans (by simpa [Finset.union_insert] using hstep (S ∪ R) i his)
  simpa [Finset.union_eq_right.mpr hST] using haux T

theorem bounded_independent_integral_vector_zero {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) :
    (∫ ω, ξ i ω ∂μ) = 0 := by
  have hi : Integrable (ξ i) μ :=
    (integrable_const δ).mono' (h.measurable i).aestronglyMeasurable (h.bounded i)
  ext j
  have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hi
  simpa only [ContinuousLinearMap.proj_apply, h.centered i j] using he.symm

theorem integral_norm_maskObservationSum_le {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (mask : Kane.Cube n) :
    (∫ ω, ‖maskObservationSum ξ mask ω‖ ∂μ) ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := by
  have hmask (ω : Ω) : maskObservationSum ξ mask ω =
      ∑ i ∈ Finset.univ.filter (fun i => mask i = true), ξ i ω := by
    simp [maskObservationSum, Finset.sum_filter]
  simp_rw [hmask]
  exact integral_norm_finset_sum_mono μ ξ h.measurable h.independent
    (fun i => (integrable_const δ).mono' (h.measurable i).aestronglyMeasurable (h.bounded i))
    (bounded_independent_integral_vector_zero h) _ _ (Finset.filter_subset _ _)

/-- The actual unconditional retained-array law, without fixing its mask. -/
theorem integral_norm_bernoulliArraySum_le {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ b, ‖arraySum b‖ ∂bernoulliArrayLaw μ ξ t) ≤
      2 * ∫ ω, ‖sumVector ξ ω‖ ∂μ := by
  have hi (mask : Kane.Cube n) :
      Integrable (fun b : Fin n → Vector p => ‖arraySum b‖) (μ.map (retainedArray ξ t mask)) := by
    change Integrable (norm ∘ arraySum) (μ.map (retainedArray ξ t mask))
    rw [integrable_map_measure (measurable_norm.comp (measurable_arraySum p n)).aestronglyMeasurable
      (measurable_retainedArray ξ h.measurable t mask).aemeasurable]
    apply (integrable_const (2 * n * δ)).mono'
      ((measurable_norm.comp (measurable_arraySum p n)).comp
        (measurable_retainedArray ξ h.measurable t mask)).aestronglyMeasurable
    filter_upwards [maskObservationSum_bounded μ ξ h.delta_nonneg h.bounded mask] with ω hω
    simp only [Function.comp_apply]
    rw [arraySum_retainedArray_eq_maskObservationSum, norm_norm,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (thinningScale_pos ht).le]
    have hh := mul_le_mul_of_nonneg_left hω (thinningScale_pos ht).le
    have hnn := mul_nonneg (show (0 : ℝ) ≤ n by positivity) h.delta_nonneg
    nlinarith [mul_le_mul_of_nonneg_right (thinningScale_le_two ht1) hnn]
  rw [integral_bernoulliArrayLaw_comp_arraySum_eq_sum μ ξ h.measurable ht ht1
    _ measurable_norm hi]
  have hE : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask *
        (2 * ∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
      apply Finset.sum_le_sum
      intro mask _
      apply mul_le_mul_of_nonneg_left _
        (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (thinningScale_pos ht).le]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (integral_norm_maskObservationSum_le h mask)
        (thinningScale_pos ht).le).trans
        (mul_le_mul_of_nonneg_right (thinningScale_le_two ht1) hE)
    _ = _ := by rw [← Finset.sum_mul, Kane.maskWeight_sum, one_mul]

end RectangleCLTArxivV1
