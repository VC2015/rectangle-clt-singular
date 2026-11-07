import RectangleCLTCompanion.SplitV4.ProductConditional
import RectangleCLTCompanion.SplitV4.PairedMoments
import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import RectangleCLT.ThinningMoments

/-!
Actual large-increment and truncated covariance budgets for Appendix G.
The mean is averaged after summing the large increments, retaining the
expected maximum of the sum. Covariance bias is measured against the actual
covariance of the centered independent original sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)

/-- The paper's `M_h`: an expected maximum of the summed actual large
increments, not a sum of expected individual norms. -/
def pairedTailExpectedMaximum (h : ℝ) : ℝ :=
  ∫ z, ‖arrayLargeIncrementIntegrand ξ h z‖ ∂μ.prod μ

/-- Coordinate tail second moments, retaining the full independent-copy
increment before the truncation event is imposed. -/
def pairedTailCoordinateSecond (h : ℝ) (j : Fin p) : ℝ :=
  ∑ i, ∫ z, copyLargeIncrementIntegrand (ξ i) h z j ^ 2 ∂μ.prod μ

/-- The exact `v_h` maximum, including a harmless zero value in dimension
zero. Every coordinate tail second moment is nonnegative. -/
def pairedTailVariance (h : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin p)).fold max 0 (pairedTailCoordinateSecond μ ξ h)

def meanTruncatedCovariance (h : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ x, copyArrayTruncatedCovariance μ ξ x h j k ∂μ

theorem pairedTailVariance_nonneg (h : ℝ) : 0 ≤ pairedTailVariance μ ξ h :=
  (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem pairedTailCoordinateSecond_le (h : ℝ) (j : Fin p) :
    pairedTailCoordinateSecond μ ξ h j ≤ pairedTailVariance μ ξ h :=
  (Finset.le_fold_max (pairedTailCoordinateSecond μ ξ h j)).mpr
    (Or.inr ⟨j, Finset.mem_univ j, le_rfl⟩)

/-- Exact correspondence with the manuscript's coordinate tail second
moment, expressed with its strict large-increment event. -/
theorem pairedTailCoordinateSecond_eq_tail_integrals (h : ℝ) (j : Fin p) :
    pairedTailCoordinateSecond μ ξ h j =
      ∑ i, ∫ z, (if h < ‖pairedIncrement ξ i z‖ then pairedIncrement ξ i z j ^ 2 else 0)
        ∂μ.prod μ := by
  unfold pairedTailCoordinateSecond
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change copyLargeIncrementIntegrand (ξ i) h z j ^ 2 = _
  rw [copyLargeIncrementIntegrand_eq_tail]
  simp only [pairedIncrement]
  split_ifs <;> simp

theorem pairedTailExpectedMaximum_eq_tail_sum (h : ℝ) :
    pairedTailExpectedMaximum μ ξ h =
      ∫ z, ‖∑ i, (if h < ‖pairedIncrement ξ i z‖ then pairedIncrement ξ i z else 0)‖ ∂μ.prod μ := by
  simp only [pairedTailExpectedMaximum, arrayLargeIncrementIntegrand,
    copyLargeIncrementIntegrand_eq_tail, pairedIncrement]

theorem integrable_vector_of_coordinate_memLp_two
    (hξ : ∀ i, Measurable (ξ i))
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ) (i : Fin n) :
    Integrable (ξ i) μ := by
  have hi (j : Fin p) : Integrable (fun ω => ξ i ω j) μ := (hL2 i j).integrable (by norm_num)
  apply (integrable_finset_sum Finset.univ (fun j _ => (hi j).norm)).mono'
    (hξ i).aestronglyMeasurable
  apply ae_of_all
  intro ω
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro j
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- Conditional averaging preserves the full large-increment expected
maximum. The actual conditional coefficient is identified in
`ProductConditional`, and the contraction is applied to the sum itself. -/
theorem expected_copyArrayLargeMean_norm_le
    (hξ : ∀ i, Measurable (ξ i)) (hξi : ∀ i, Integrable (ξ i) μ)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ x, ‖copyArrayLargeMean μ ξ x h‖ ∂μ) ≤ pairedTailExpectedMaximum μ ξ h := by
  let F := arrayLargeIncrementIntegrand ξ h
  have hi : Integrable F (μ.prod μ) :=
    integrable_finset_sum Finset.univ (fun i _ =>
      integrable_copyLargeIncrementIntegrand μ (ξ i) (hξ i) (hξi i) hh)
  have hm : StronglyMeasurable F :=
    (Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) h)).stronglyMeasurable
  have hmean := copyArrayLargeMean_ae_eq_condExp μ ξ hξ hξi hh
  have havg := copyAverage_ae_eq_condExp μ μ F hm hi
  have heq := hmean.trans havg.symm
  have hf := integral_fun_fst (μ := μ) (ν := μ) (fun x => ‖copyArrayLargeMean μ ξ x h‖)
  simp only [measureReal_univ_eq_one, one_smul] at hf
  calc
    _ = ∫ z : Ω × Ω, ‖copyArrayLargeMean μ ξ z.1 h‖ ∂μ.prod μ := hf.symm
    _ = ∫ z : Ω × Ω, ‖copyAverage μ F z.1‖ ∂μ.prod μ :=
      integral_congr_ae (heq.mono (fun _ hz => congrArg norm hz))
    _ ≤ _ := integral_norm_copyAverage_fst_le μ μ F hi

theorem expected_copyArrayLargeMean_norm_le_of_memLp_two
    (hξ : ∀ i, Measurable (ξ i))
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ x, ‖copyArrayLargeMean μ ξ x h‖ ∂μ) ≤ pairedTailExpectedMaximum μ ξ h :=
  expected_copyArrayLargeMean_norm_le μ ξ hξ
    (integrable_vector_of_coordinate_memLp_two μ ξ hξ hL2) hh

/-- The conditional tail mean itself is genuinely Bochner integrable. -/
theorem measurable_copyArrayLargeMean
    (hξ : ∀ i, Measurable (ξ i)) (h : ℝ) :
    Measurable (fun x => copyArrayLargeMean μ ξ x h) := by
  change Measurable (fun x => ∑ i, ∫ y, copyLargeIncrementIntegrand (ξ i) h (x, y) ∂μ)
  apply Finset.measurable_sum Finset.univ
  intro i _
  exact (measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) h).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_copyArrayLargeMean
    (hξ : ∀ i, Measurable (ξ i)) (hξi : ∀ i, Integrable (ξ i) μ)
    {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun x => copyArrayLargeMean μ ξ x h) μ := by
  let F := arrayLargeIncrementIntegrand ξ h
  have hi : Integrable F (μ.prod μ) :=
    integrable_finset_sum Finset.univ (fun i _ =>
      integrable_copyLargeIncrementIntegrand μ (ξ i) (hξ i) (hξi i) hh)
  have hm : StronglyMeasurable F :=
    (Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) h)).stronglyMeasurable
  have hmean := copyArrayLargeMean_ae_eq_condExp μ ξ hξ hξi hh
  have havg := copyAverage_ae_eq_condExp μ μ F hm hi
  have heq := hmean.trans havg.symm
  have hmp : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hmeas := measurable_copyArrayLargeMean μ ξ hξ h
  have ha : Integrable (fun x => copyAverage μ F x) μ := hi.integral_prod_left
  have halift : Integrable (fun z : Ω × Ω => copyAverage μ F z.1) (μ.prod μ) :=
    (hmp.integrable_comp ha.aestronglyMeasurable).mpr ha
  have hlift : Integrable (fun z : Ω × Ω => copyArrayLargeMean μ ξ z.1 h) (μ.prod μ) :=
    halift.congr heq.symm
  exact (hmp.integrable_comp hmeas.aestronglyMeasurable).mp hlift

theorem pairedIncrement_coordinate_memLp_two
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ) (i : Fin n) (j : Fin p) :
    MemLp (fun z : Ω × Ω => pairedIncrement ξ i z j) (2 : ℝ≥0∞) (μ.prod μ) := by
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hs : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  exact ((hL2 i j).comp_measurePreserving hs).sub ((hL2 i j).comp_measurePreserving hf)

theorem pairedTail_coordinate_memLp_two
    (hξ : ∀ i, Measurable (ξ i))
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (h : ℝ) (i : Fin n) (j : Fin p) :
    MemLp (fun z : Ω × Ω => copyLargeIncrementIntegrand (ξ i) h z j)
      (2 : ℝ≥0∞) (μ.prod μ) := by
  apply (pairedIncrement_coordinate_memLp_two μ ξ hL2 i j).mono
    (((measurable_pi_apply j).comp
      (measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) h)).aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖copyLargeIncrementIntegrand (ξ i) h z j‖ ≤ ‖pairedIncrement ξ i z j‖
  rw [copyLargeIncrementIntegrand_eq_tail]
  split_ifs <;> simp only [pairedIncrement, Pi.sub_apply, Pi.zero_apply, norm_zero, norm_nonneg, le_refl]

private theorem integrable_coordinate_product
    {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    {f g : Λ → ℝ} (hf : MemLp f (2 : ℝ≥0∞) ν) (hg : MemLp g (2 : ℝ≥0∞) ν) :
    Integrable (fun ω => f ω * g ω) ν := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  exact hf.integrable_mul hg

/-- The centered independent-copy second moment is exactly twice the
original second moment; it is not a covariance assumption. -/
theorem integral_pairedIncrement_product
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (i : Fin n) (j k : Fin p) :
    (∫ z, pairedIncrement ξ i z j * pairedIncrement ξ i z k ∂μ.prod μ) =
      2 * ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hs : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  have hi := integrable_coordinate_product μ (hL2 i j) (hL2 i k)
  have hi₀ : Integrable (fun z : Ω × Ω => ξ i z.1 j * ξ i z.1 k) (μ.prod μ) :=
    (hf.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hi₁ : Integrable (fun z : Ω × Ω => ξ i z.2 j * ξ i z.2 k) (μ.prod μ) :=
    (hs.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hj := (hL2 i j).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hk := (hL2 i k).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcross₀ : Integrable (fun z : Ω × Ω => ξ i z.1 j * ξ i z.2 k) (μ.prod μ) := hj.mul_prod hk
  have hcross₁ : Integrable (fun z : Ω × Ω => ξ i z.1 k * ξ i z.2 j) (μ.prod μ) := hk.mul_prod hj
  have hfst : (∫ z : Ω × Ω, ξ i z.1 j * ξ i z.1 k ∂μ.prod μ) =
      ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
    simpa only [measureReal_univ_eq_one, one_smul] using
      integral_fun_fst (μ := μ) (ν := μ) (fun ω => ξ i ω j * ξ i ω k)
  have hsnd : (∫ z : Ω × Ω, ξ i z.2 j * ξ i z.2 k ∂μ.prod μ) =
      ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
    simpa only [measureReal_univ_eq_one, one_smul] using
      integral_fun_snd (μ := μ) (ν := μ) (fun ω => ξ i ω j * ξ i ω k)
  have hc₀ : (∫ z : Ω × Ω, ξ i z.1 j * ξ i z.2 k ∂μ.prod μ) = 0 := by
    simpa only [hcenter, zero_mul] using
      integral_prod_mul (μ := μ) (ν := μ) (fun ω => ξ i ω j) (fun ω => ξ i ω k)
  have hc₁ : (∫ z : Ω × Ω, ξ i z.1 k * ξ i z.2 j ∂μ.prod μ) = 0 := by
    simpa only [hcenter, zero_mul] using
      integral_prod_mul (μ := μ) (ν := μ) (fun ω => ξ i ω k) (fun ω => ξ i ω j)
  have hp (z : Ω × Ω) : pairedIncrement ξ i z j * pairedIncrement ξ i z k =
      (ξ i z.2 j * ξ i z.2 k + ξ i z.1 j * ξ i z.1 k) -
        ξ i z.1 j * ξ i z.2 k - ξ i z.1 k * ξ i z.2 j := by
    dsimp [pairedIncrement]
    ring
  simp_rw [hp]
  have he₁ := integral_sub ((hi₁.add hi₀).sub hcross₀) hcross₁
  have he₂ := integral_sub (hi₁.add hi₀) hcross₀
  have he₃ := integral_add hi₁ hi₀
  simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
  rw [he₁, he₂, he₃, hfst, hsnd, hc₀, hc₁]
  ring

/-- The half paired-copy covariance budget equals the actual covariance
of the original centered independent sum, including singular directions. -/
theorem half_sum_pairedIncrement_product_eq_covariance
    (hind : iIndepFun ξ μ)
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (j k : Fin p) :
    (1 / 2 : ℝ) * (∑ i, ∫ z,
      pairedIncrement ξ i z j * pairedIncrement ξ i z k ∂μ.prod μ) =
      covariance μ (sumVector ξ) j k := by
  have hint (i : Fin n) (a : Fin p) : Integrable (fun ω => ξ i ω a) μ :=
    (hL2 i a).integrable (by norm_num)
  have hprod (i l : Fin n) (a b : Fin p) :
      Integrable (fun ω => ξ i ω a * ξ l ω b) μ :=
    integrable_coordinate_product μ (hL2 i a) (hL2 l b)
  rw [covariance_sum_of_centered_cross hint hprod hcenter
    (independent_centered_cross_zero hind hint hcenter)]
  simp_rw [integral_pairedIncrement_product μ ξ hL2 hcenter]
  rw [← Finset.mul_sum]
  ring

theorem meanTruncatedCovariance_eq_half_sum
    (hξ : ∀ i, Measurable (ξ i)) {h : ℝ} (hh : 0 ≤ h) (j k : Fin p) :
    meanTruncatedCovariance μ ξ h j k = (1 / 2 : ℝ) * ∑ i,
      ∫ z, pairedTruncatedArray ξ h i z j * pairedTruncatedArray ξ h i z k ∂μ.prod μ := by
  have hCE := copyArrayTruncatedCovariance_ae_eq_condExp μ ξ hξ hh j k
  have hfst := integral_fun_fst (μ := μ) (ν := μ)
    (fun x => copyArrayTruncatedCovariance μ ξ x h j k)
  simp only [measureReal_univ_eq_one, one_smul] at hfst
  change (∫ x, copyArrayTruncatedCovariance μ ξ x h j k ∂μ) = _
  rw [← hfst, integral_congr_ae hCE, integral_condExp originalSigma_le]
  rw [show arrayCovarianceIntegrand ξ h j k =
      ∑ i, copyCovarianceIntegrand (ξ i) h j k by
    funext z
    simp only [arrayCovarianceIntegrand, Finset.sum_apply]]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_copyCovarianceIntegrand μ (ξ i) (hξ i) hh j k)]
  simp only [copyCovarianceIntegrand, pairedTruncatedArray, integral_const_mul, Finset.mul_sum]

private theorem tail_product_integrable
    (hξ : ∀ i, Measurable (ξ i))
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (h : ℝ) (i : Fin n) (j k : Fin p) :
    Integrable (fun z => copyLargeIncrementIntegrand (ξ i) h z j *
      copyLargeIncrementIntegrand (ξ i) h z k) (μ.prod μ) :=
  integrable_coordinate_product (μ.prod μ)
    (pairedTail_coordinate_memLp_two μ ξ hξ hL2 h i j)
    (pairedTail_coordinate_memLp_two μ ξ hξ hL2 h i k)

/-- Exact partition of the raw paired second moment into small and large
increments. Cross terms vanish pointwise on the two truncation events. -/
theorem pairedIncrement_product_eq_small_add_large
    (h : ℝ) (i : Fin n) (z : Ω × Ω) (j k : Fin p) :
    pairedIncrement ξ i z j * pairedIncrement ξ i z k =
      pairedTruncatedArray ξ h i z j * pairedTruncatedArray ξ h i z k +
        copyLargeIncrementIntegrand (ξ i) h z j * copyLargeIncrementIntegrand (ξ i) h z k := by
  unfold pairedIncrement pairedTruncatedArray copyLargeIncrementIntegrand pairedTruncatedIncrement
  split_ifs <;> simp only [Pi.sub_apply, Pi.zero_apply, sub_self, sub_zero, zero_mul, add_zero, zero_add]

/-- The bias is exactly minus one half of the summed tail rank-one
moments. The reference matrix is the actual covariance, not an input bound. -/
theorem meanTruncatedCovariance_sub_covariance
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    {h : ℝ} (hh : 0 ≤ h) (j k : Fin p) :
    meanTruncatedCovariance μ ξ h j k - covariance μ (sumVector ξ) j k =
      -(1 / 2 : ℝ) * ∑ i, ∫ z,
        copyLargeIncrementIntegrand (ξ i) h z j * copyLargeIncrementIntegrand (ξ i) h z k
          ∂μ.prod μ := by
  have hsplit : (∑ i, ∫ z,
      pairedIncrement ξ i z j * pairedIncrement ξ i z k ∂μ.prod μ) =
      (∑ i, ∫ z, pairedTruncatedArray ξ h i z j * pairedTruncatedArray ξ h i z k ∂μ.prod μ) +
        ∑ i, ∫ z, copyLargeIncrementIntegrand (ξ i) h z j *
          copyLargeIncrementIntegrand (ξ i) h z k ∂μ.prod μ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_add]
    · apply integral_congr_ae
      exact ae_of_all _ (fun z => pairedIncrement_product_eq_small_add_large ξ h i z j k)
    · have hi := integrable_copyCovarianceIntegrand μ (ξ i) (hξ i) hh j k
      exact (integrable_const_mul_iff
        (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 2 : ℝ) ≠ 0))
        (fun z : Ω × Ω => pairedTruncatedArray ξ h i z j * pairedTruncatedArray ξ h i z k)).mp hi
    · exact tail_product_integrable μ ξ hξ hL2 h i j k
  rw [meanTruncatedCovariance_eq_half_sum μ ξ hξ hh]
  have hc := half_sum_pairedIncrement_product_eq_covariance μ ξ hind hL2 hcenter j k
  linarith

/-- The summed tail cross-products are controlled by the maximum of the
actual summed coordinate tail second moments. -/
theorem abs_tail_product_sum_le_variance
    (hξ : ∀ i, Measurable (ξ i))
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (h : ℝ) (j k : Fin p) :
    |∑ i, ∫ z, copyLargeIncrementIntegrand (ξ i) h z j *
      copyLargeIncrementIntegrand (ξ i) h z k ∂μ.prod μ| ≤ pairedTailVariance μ ξ h := by
  have hs (i : Fin n) (a : Fin p) :
      Integrable (fun z => copyLargeIncrementIntegrand (ξ i) h z a ^ 2) (μ.prod μ) := by
    simpa only [pow_two] using tail_product_integrable μ ξ hξ hL2 h i a a
  calc
    _ ≤ ∑ i, |∫ z, copyLargeIncrementIntegrand (ξ i) h z j *
        copyLargeIncrementIntegrand (ξ i) h z k ∂μ.prod μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((∫ z, copyLargeIncrementIntegrand (ξ i) h z j ^ 2 ∂μ.prod μ) +
        ∫ z, copyLargeIncrementIntegrand (ξ i) h z k ^ 2 ∂μ.prod μ) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∫ z, |copyLargeIncrementIntegrand (ξ i) h z j *
            copyLargeIncrementIntegrand (ξ i) h z k| ∂μ.prod μ := abs_integral_le_integral_abs
        _ ≤ ∫ z, (copyLargeIncrementIntegrand (ξ i) h z j ^ 2 +
            copyLargeIncrementIntegrand (ξ i) h z k ^ 2) / 2 ∂μ.prod μ := by
          apply integral_mono (tail_product_integrable μ ξ hξ hL2 h i j k).abs
            (((hs i j).add (hs i k)).div_const 2)
          intro z
          change |copyLargeIncrementIntegrand (ξ i) h z j * copyLargeIncrementIntegrand (ξ i) h z k| ≤
            (copyLargeIncrementIntegrand (ξ i) h z j ^ 2 + copyLargeIncrementIntegrand (ξ i) h z k ^ 2) / 2
          rw [abs_mul]
          nlinarith [sq_nonneg (|copyLargeIncrementIntegrand (ξ i) h z j| -
            |copyLargeIncrementIntegrand (ξ i) h z k|),
            sq_abs (copyLargeIncrementIntegrand (ξ i) h z j),
            sq_abs (copyLargeIncrementIntegrand (ξ i) h z k)]
        _ = _ := by rw [integral_div, integral_add (hs i j) (hs i k)]
    _ = (pairedTailCoordinateSecond μ ξ h j + pairedTailCoordinateSecond μ ξ h k) / 2 := by
      unfold pairedTailCoordinateSecond
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := by
      linarith [pairedTailCoordinateSecond_le μ ξ h j, pairedTailCoordinateSecond_le μ ξ h k]

/-- Actual truncation bias in maximum-entry norm: the precise factor
`v_h/2` is retained before adding the conditional matrix fluctuation. -/
theorem meanTruncatedCovariance_bias_norm_le
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    {h : ℝ} (hh : 0 ≤ h) :
    matrixMaxEntryNorm (meanTruncatedCovariance μ ξ h - covariance μ (sumVector ξ)) ≤
      pairedTailVariance μ ξ h / 2 := by
  have hv : 0 ≤ pairedTailVariance μ ξ h / 2 := div_nonneg (pairedTailVariance_nonneg μ ξ h) (by norm_num)
  apply (pi_norm_le_iff_of_nonneg hv).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hv).mpr
  intro k
  change |meanTruncatedCovariance μ ξ h j k - covariance μ (sumVector ξ) j k| ≤ _
  rw [meanTruncatedCovariance_sub_covariance μ ξ hξ hind hL2 hcenter hh,
    abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hb := mul_le_mul_of_nonneg_left
    (abs_tail_product_sum_le_variance μ ξ hξ hL2 h j k) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb

end

end RectangleCLT.Companion.SplitV4
