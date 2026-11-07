import RectangleCLTCompanion.SplitV4.ConditionalTruncation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Constructive mask and exceptional-value disintegration

All conditional laws below are the actual normalized good/bad restrictions.
The finite mask mixture is obtained by expanding the actual product law.
Independent bad and good draws then give a concrete reconstruction kernel;
no regular-conditional-distribution statement is postulated.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def selectedConditionalLaw {p : ℕ} (μ : Measure (Vector p)) (T : ℝ) (bad : Bool) :
    Measure (Vector p) := conditionalVectorLaw μ (truncationMaskSet T bad)

instance selectedConditionalLaw_isProbability {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] (T : ℝ) (bad : Bool) :
    IsProbabilityMeasure (selectedConditionalLaw μ T bad) := inferInstanceAs
      (IsProbabilityMeasure (conditionalVectorLaw μ (truncationMaskSet T bad)))

def truncationMaskWeight {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool) : ℝ≥0∞ :=
  ∏ i, μ i (truncationMaskSet T (mask i))

def selectedConditionalProduct {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool) :
    Measure (Fin n → Vector p) := Measure.pi (fun i => selectedConditionalLaw (μ i) T (mask i))

instance selectedConditionalProduct_isProbability {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (mask : Fin n → Bool) : IsProbabilityMeasure (selectedConditionalProduct μ T mask) := by
  unfold selectedConditionalProduct
  infer_instance

def truncationMaskMixture {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) : Measure (Fin n → Vector p) :=
  ∑ mask : Fin n → Bool, truncationMaskWeight μ T mask • selectedConditionalProduct μ T mask

theorem truncationMaskWeight_ne_top {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (mask : Fin n → Bool) : truncationMaskWeight μ T mask ≠ ∞ :=
  ENNReal.prod_ne_top (fun i _ => measure_ne_top (μ i) _)

set_option maxHeartbeats 500000 in
/-- Tensor expansion into actual conditional product laws. Zero-probability
masks retain zero weight, so no positivity hypothesis is added to the array. -/
theorem productLaw_eq_truncationMaskMixture {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    Measure.pi μ = truncationMaskMixture μ T := by
  apply Measure.pi_eq
  intro S hS
  unfold truncationMaskMixture
  rw [Measure.finset_sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, selectedConditionalProduct, Measure.pi_pi,
    truncationMaskWeight]
  calc
    _ = ∑ mask : Fin n → Bool,
        ∏ i, μ i (truncationMaskSet T (mask i)) * (selectedConditionalLaw (μ i) T (mask i)) (S i) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, μ i (truncationMaskSet T b) * (selectedConditionalLaw (μ i) T b) (S i) :=
      (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
        μ i (truncationMaskSet T b) * (selectedConditionalLaw (μ i) T b) (S i))).symm
    _ = ∏ i, μ i (S i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hh := congrArg (fun ν : Measure (Vector p) => ν (S i))
        (conditional_good_bad_mixture (μ i) (goodTruncationSet T) (measurableSet_goodTruncationSet T))
      simpa [selectedConditionalLaw, truncationMaskSet, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, add_comm] using hh

def selectConditionalArrays {p n : ℕ} (mask : Fin n → Bool)
    (z : (Fin n → Vector p) × (Fin n → Vector p)) : Fin n → Vector p :=
  fun i => if mask i then z.1 i else z.2 i

theorem measurable_selectConditionalArrays {p n : ℕ} (mask : Fin n → Bool) :
    Measurable (selectConditionalArrays (p := p) mask) := by
  apply measurable_pi_lambda
  intro i
  unfold selectConditionalArrays
  split_ifs
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp measurable_snd

def badConditionalProduct {p n : ℕ} (μ : Fin n → Measure (Vector p)) (T : ℝ) :
    Measure (Fin n → Vector p) := Measure.pi (fun i => selectedConditionalLaw (μ i) T true)

instance badConditionalProduct_isProbability {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    IsProbabilityMeasure (badConditionalProduct μ T) := by unfold badConditionalProduct; infer_instance

/-- Bad draws and good draws live on an actual independent product space. -/
theorem conditionalArrays_select_law {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (mask : Fin n → Bool) :
    ((badConditionalProduct μ T).prod (conditionalGoodProductLaw μ T)).map
      (selectConditionalArrays mask) = selectedConditionalProduct μ T mask := by
  let νb := fun i => selectedConditionalLaw (μ i) T true
  let νg := fun i => selectedConditionalLaw (μ i) T false
  have hs := measurePreserving_arrowProdEquivProdArrow (Vector p) (Vector p) (Fin n) νb νg
  have hrow (i : Fin n) : MeasurePreserving
      (fun z : Vector p × Vector p => if mask i then z.1 else z.2)
      ((νb i).prod (νg i)) (selectedConditionalLaw (μ i) T (mask i)) := by
    by_cases hi : mask i = true
    · refine ⟨by simpa only [hi, if_true] using (measurable_fst : Measurable (Prod.fst : Vector p × Vector p → Vector p)), ?_⟩
      simp only [hi, if_true, Measure.map_fst_prod, measure_univ, one_smul, νb]
    · have hi' : mask i = false := Bool.eq_false_iff.mpr hi
      refine ⟨by simpa only [hi', Bool.false_eq_true, if_false] using
        (measurable_snd : Measurable (Prod.snd : Vector p × Vector p → Vector p)), ?_⟩
      simp only [hi', Bool.false_eq_true, if_false, Measure.map_snd_prod, measure_univ, one_smul, νg]
  have hp := measurePreserving_pi (fun i => (νb i).prod (νg i))
    (fun i => selectedConditionalLaw (μ i) T (mask i)) hrow
  change ((Measure.pi νb).prod (Measure.pi νg)).map (selectConditionalArrays mask) = _
  rw [← hs.map_eq, Measure.map_map (measurable_selectConditionalArrays mask) hs.measurable]
  convert hp.map_eq using 1

/-- Integrating an arbitrary bounded measurable test against the original
array is exactly the finite mask mixture with independent bad and good draws. -/
theorem integral_product_eq_mask_bad_good {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (f : (Fin n → Vector p) → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂Measure.pi μ) =
      ∑ mask : Fin n → Bool, (truncationMaskWeight μ T mask).toReal *
        ∫ b, ∫ g, f (selectConditionalArrays mask (b, g))
          ∂conditionalGoodProductLaw μ T ∂badConditionalProduct μ T := by
  have hi (mask : Fin n → Bool) : Integrable f (selectedConditionalProduct μ T mask) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hbound x)
  rw [productLaw_eq_truncationMaskMixture μ T]
  unfold truncationMaskMixture
  rw [integral_finset_sum_measure (fun mask _ =>
    (hi mask).smul_measure (truncationMaskWeight_ne_top μ T mask))]
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_smul_measure]
  congr 1
  rw [← conditionalArrays_select_law μ T mask,
    integral_map (measurable_selectConditionalArrays mask).aemeasurable hf.aestronglyMeasurable]
  apply integral_prod
  exact (integrable_const C).mono'
    (hf.comp (measurable_selectConditionalArrays mask)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound _)

def observedTruncationMask {p n : ℕ} (T : ℝ) (x : Fin n → Vector p) : Fin n → Bool :=
  fun i => if ‖x i‖ ≤ T then false else true

def maskedExceptionalArray {p n : ℕ} (mask : Fin n → Bool) (b : Fin n → Vector p) :
    Fin n → Vector p := fun i => if mask i then b i else 0

def observedExceptionalArray {p n : ℕ} (T : ℝ) (x : Fin n → Vector p) : Fin n → Vector p :=
  fun i => if ‖x i‖ ≤ T then 0 else x i

theorem measurable_observedTruncationMask {p n : ℕ} (T : ℝ) :
    Measurable (observedTruncationMask (p := p) (n := n) T) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i).norm measurable_const)
    measurable_const measurable_const

theorem measurable_maskedExceptionalArray {p n : ℕ} (mask : Fin n → Bool) :
    Measurable (maskedExceptionalArray (p := p) mask) := by
  apply measurable_pi_lambda
  intro i
  unfold maskedExceptionalArray
  split_ifs
  · exact measurable_pi_apply i
  · exact measurable_const

theorem measurable_observedExceptionalArray {p n : ℕ} (T : ℝ) :
    Measurable (observedExceptionalArray (p := p) (n := n) T) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i).norm measurable_const)
    measurable_const (measurable_pi_apply i)

theorem selectedConditionalProduct_ae_mask {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (mask : Fin n → Bool) (hw : truncationMaskWeight μ T mask ≠ 0) :
    ∀ᵐ x ∂selectedConditionalProduct μ T mask, ∀ i, x i ∈ truncationMaskSet T (mask i) := by
  have hpos (i : Fin n) : μ i (truncationMaskSet T (mask i)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  apply ae_all_iff.mpr
  intro i
  have hr : ∀ᵐ x ∂selectedConditionalLaw (μ i) T (mask i), x ∈ truncationMaskSet T (mask i) := by
    rw [selectedConditionalLaw, conditionalVectorLaw_eq_cond (μ i) _ (hpos i)]
    exact ProbabilityTheory.ae_cond_mem (measurableSet_truncationMaskSet T (mask i))
  exact ae_iff.mpr (Measure.pi_eval_preimage_null
    (fun j => selectedConditionalLaw (μ j) T (mask j)) (ae_iff.mp hr))

/-- Positive-weight selections have precisely the original observed mask
and exceptional values. Zero-weight masks need no support assertion. -/
theorem observed_selected_tag_ae {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (mask : Fin n → Bool) (hw : truncationMaskWeight μ T mask ≠ 0) :
    ∀ᵐ z ∂(badConditionalProduct μ T).prod (conditionalGoodProductLaw μ T),
      (observedTruncationMask T (selectConditionalArrays mask z),
        observedExceptionalArray T (selectConditionalArrays mask z)) =
      (mask, maskedExceptionalArray mask z.1) := by
  have ha : ∀ᵐ z ∂(badConditionalProduct μ T).prod (conditionalGoodProductLaw μ T),
      ∀ i, (selectConditionalArrays mask z) i ∈ truncationMaskSet T (mask i) := by
    have hmap : ∀ᵐ x ∂((badConditionalProduct μ T).prod (conditionalGoodProductLaw μ T)).map
        (selectConditionalArrays mask), ∀ i, x i ∈ truncationMaskSet T (mask i) := by
      rw [conditionalArrays_select_law]
      exact selectedConditionalProduct_ae_mask μ T mask hw
    exact ae_of_ae_map (measurable_selectConditionalArrays mask).aemeasurable hmap
  filter_upwards [ha] with z hz
  have hmask : observedTruncationMask T (selectConditionalArrays mask z) = mask := by
    funext i
    by_cases hi : mask i = true
    · have hx : ¬ ‖z.1 i‖ ≤ T := by
        simpa only [selectConditionalArrays, truncationMaskSet, hi, if_true,
          goodTruncationSet, Set.mem_compl_iff, Set.mem_setOf_eq] using hz i
      simp only [observedTruncationMask, selectConditionalArrays, hi, if_true, if_neg hx]
    · have hi' : mask i = false := Bool.eq_false_iff.mpr hi
      have hx : ‖z.2 i‖ ≤ T := by
        simpa only [selectConditionalArrays, truncationMaskSet, hi', Bool.false_eq_true,
          if_false, goodTruncationSet, Set.mem_setOf_eq] using hz i
      simp only [observedTruncationMask, selectConditionalArrays, hi', Bool.false_eq_true,
        if_false, if_pos hx]
  refine Prod.ext hmask ?_
  funext i
  by_cases hi : mask i = true
  · have hx : ¬ ‖z.1 i‖ ≤ T := by
      simpa only [selectConditionalArrays, truncationMaskSet, hi, if_true,
        goodTruncationSet, Set.mem_compl_iff, Set.mem_setOf_eq] using hz i
    simp only [observedExceptionalArray, maskedExceptionalArray, selectConditionalArrays,
      hi, if_true, if_neg hx]
  · have hi' : mask i = false := Bool.eq_false_iff.mpr hi
    have hx : ‖z.2 i‖ ≤ T := by
      simpa only [selectConditionalArrays, truncationMaskSet, hi', Bool.false_eq_true,
        if_false, goodTruncationSet, Set.mem_setOf_eq] using hz i
    simp only [observedExceptionalArray, maskedExceptionalArray, selectConditionalArrays,
      hi', Bool.false_eq_true, if_false, if_pos hx]

/-- Concrete disintegration reconstruction for every bounded measurable
joint test of the exceptional mask, exceptional values, and original array.
The inner good-law integral is the explicit conditional reconstruction kernel. -/
theorem integral_tagged_product_eq_mask_bad_good {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (F : ((Fin n → Bool) × (Fin n → Vector p)) × (Fin n → Vector p) → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ z, |F z| ≤ C) :
    (∫ x, F ((observedTruncationMask T x, observedExceptionalArray T x), x) ∂Measure.pi μ) =
      ∑ mask : Fin n → Bool, (truncationMaskWeight μ T mask).toReal *
        ∫ b, ∫ g, F ((mask, maskedExceptionalArray mask b), selectConditionalArrays mask (b, g))
          ∂conditionalGoodProductLaw μ T ∂badConditionalProduct μ T := by
  have hf : Measurable (fun x : Fin n → Vector p =>
      F ((observedTruncationMask T x, observedExceptionalArray T x), x)) :=
    hF.comp (((measurable_observedTruncationMask T).prodMk
      (measurable_observedExceptionalArray T)).prodMk measurable_id)
  rw [integral_product_eq_mask_bad_good μ T _ hf C (fun x => hbound _)]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hw : truncationMaskWeight μ T mask = 0
  · simp only [hw, ENNReal.toReal_zero, zero_mul]
  · congr 1
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod (observed_selected_tag_ae μ T mask hw)] with b hb
    apply integral_congr_ae
    filter_upwards [hb] with g hg
    rw [hg]

abbrev TruncationTag (p n : ℕ) := (Fin n → Bool) × (Fin n → Vector p)

def reconstructConditionalArray {p n : ℕ}
    (z : TruncationTag p n × (Fin n → Vector p)) : Fin n → Vector p :=
  selectConditionalArrays z.1.1 (z.1.2, z.2)

theorem measurable_reconstructConditionalArray {p n : ℕ} :
    Measurable (reconstructConditionalArray (p := p) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  have hmask : Measurable (fun z : TruncationTag p n × (Fin n → Vector p) => z.1.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  exact Measurable.ite (hmask (measurableSet_singleton true))
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
    ((measurable_pi_apply i).comp measurable_snd)

/-- An actual measurable Markov kernel: the exceptional data stay fixed
and the independent good coordinates are freshly drawn from their true laws. -/
def conditionalTruncationKernel {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    Kernel (TruncationTag p n) (Fin n → Vector p) :=
  ((Kernel.id : Kernel (TruncationTag p n) (TruncationTag p n)).prod
    (Kernel.const (TruncationTag p n) (conditionalGoodProductLaw μ T))).map reconstructConditionalArray

instance conditionalTruncationKernel_isMarkov {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    IsMarkovKernel (conditionalTruncationKernel μ T) :=
  Kernel.IsMarkovKernel.map _ measurable_reconstructConditionalArray

theorem conditionalTruncationKernel_apply {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (tag : TruncationTag p n) :
    conditionalTruncationKernel μ T tag =
      (conditionalGoodProductLaw μ T).map (fun g => selectConditionalArrays tag.1 (tag.2, g)) := by
  unfold conditionalTruncationKernel
  rw [Kernel.map_apply _ measurable_reconstructConditionalArray, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map measurable_reconstructConditionalArray measurable_prodMk_left]
  rfl

theorem selectConditionalArrays_masked_bad {p n : ℕ}
    (mask : Fin n → Bool) (b g : Fin n → Vector p) :
    selectConditionalArrays mask (maskedExceptionalArray mask b, g) =
      selectConditionalArrays mask (b, g) := by
  funext i
  by_cases hi : mask i = true <;> simp [selectConditionalArrays, maskedExceptionalArray, hi]

/-- Exact disintegration against every bounded measurable joint test.
This identifies the concrete Markov kernel from the actual exceptional
mask and values; it is not an assumed regular conditional law. -/
theorem integral_product_conditionalTruncationKernel {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (F : TruncationTag p n × (Fin n → Vector p) → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ z, |F z| ≤ C) :
    (∫ x, F ((observedTruncationMask T x, observedExceptionalArray T x), x) ∂Measure.pi μ) =
      ∑ mask : Fin n → Bool, (truncationMaskWeight μ T mask).toReal *
        ∫ b, ∫ x, F ((mask, maskedExceptionalArray mask b), x)
          ∂conditionalTruncationKernel μ T (mask, maskedExceptionalArray mask b)
          ∂badConditionalProduct μ T := by
  rw [integral_tagged_product_eq_mask_bad_good μ T F hF C hbound]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun b => by
    dsimp only
    rw [conditionalTruncationKernel_apply]
    have hmSel : Measurable (fun g : Fin n → Vector p =>
        selectConditionalArrays mask (maskedExceptionalArray mask b, g)) :=
      (measurable_selectConditionalArrays mask).comp (measurable_const.prodMk measurable_id)
    have hmF : Measurable (fun x : Fin n → Vector p => F ((mask, maskedExceptionalArray mask b), x)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have he := integral_map (μ := conditionalGoodProductLaw μ T) hmSel.aemeasurable hmF.aestronglyMeasurable
    simpa only [selectConditionalArrays_masked_bad] using he.symm

def conditionalExceptionalShift {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool)
    (b : Fin n → Vector p) : Fin n → Vector p :=
  fun i => if mask i then b i else conditionalGoodMean (μ i) T

/-- Every kernel draw is the bounded centered good array plus an actual
fixed exceptional shift, before normalizing and summing the observations. -/
theorem selectConditionalArrays_eq_retained_add_shift {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool)
    (b g : Fin n → Vector p) :
    selectConditionalArrays mask (b, g) =
      fun i => conditionalRetainedSummand μ T mask i g + conditionalExceptionalShift μ T mask b i := by
  funext i
  unfold selectConditionalArrays conditionalRetainedSummand conditionalExceptionalShift
  split_ifs <;> simp

end

end RectangleCLT.Companion.SplitV4
