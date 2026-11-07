import RectangleCLTCompanion.SplitV4.BennettMaximum
import RectangleCLTCompanion.SplitV4.PairedTailBudgets
import RectangleCLTCompanion.SplitV4.LargeIncrementComparison
import RectangleCLTCompanion.SplitV4.BennettOptimization
import RectangleCLTCompanion.SplitV4.BennettCalibration
import RectangleCLTCompanion.SplitV4.BennettNormalization
import Mathlib.Analysis.MeanInequalitiesPow
import RectangleCLT.TruncationTailMoments

/-!
Actual polynomial-moment inputs to the Bennett application in Appendix G.
The independent copies, the large-increment event, and all expectations are
those of the original array. Scalar optimizer helpers do not by themselves
assert the final polynomial CLT.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- The strict large-increment part of one vector. -/
def bennettLargeCutoff {p : ℕ} (t : ℝ) (x : Vector p) : Vector p :=
  x - bennettTruncate t x

theorem measurable_bennettLargeCutoff {p : ℕ} (t : ℝ) :
    Measurable (bennettLargeCutoff (p := p) t) :=
  measurable_id.sub (measurable_bennettTruncate t)

theorem bennettLargeCutoff_neg {p : ℕ} (t : ℝ) (x : Vector p) :
    bennettLargeCutoff t (-x) = -bennettLargeCutoff t x := by
  simp only [bennettLargeCutoff, bennettTruncate_neg]
  abel

theorem norm_bennettLargeCutoff_le {p : ℕ} (t : ℝ) (x : Vector p) :
    ‖bennettLargeCutoff t x‖ ≤ ‖x‖ := by
  unfold bennettLargeCutoff bennettTruncate
  split_ifs <;> simp

theorem copyLargeIncrementIntegrand_eq_bennettLargeCutoff
    {Ω : Type*} {p : ℕ} (X : Ω → Vector p) (t : ℝ) (z : Ω × Ω) :
    copyLargeIncrementIntegrand X t z = bennettLargeCutoff t (X z.2 - X z.1) := rfl

theorem norm_sub_rpow_le {p : ℕ} (x y : Vector p) {q : ℝ} (hq : 1 ≤ q) :
    ‖y - x‖ ^ q ≤ (2 : ℝ) ^ (q - 1) * (‖x‖ ^ q + ‖y‖ ^ q) := by
  have hmean := NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ hq
  have hr : (‖x‖ + ‖y‖) ^ q ≤ (2 : ℝ) ^ (q - 1) * (‖x‖ ^ q + ‖y‖ ^ q) := by
    exact_mod_cast hmean
  exact (Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le y x).trans_eq (add_comm _ _))
    (zero_le_one.trans hq)).trans hr

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {q A t u : ℝ}

theorem integrable_pairedIncrement_norm_rpow
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hq : 1 ≤ q) (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ) (i : Fin n) :
    Integrable (fun z => ‖pairedIncrement ξ i z‖ ^ q) (μ.prod μ) := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hsnd : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  have hi₁ := (hfst.integrable_comp (hmoment i).aestronglyMeasurable).mpr (hmoment i)
  have hi₂ := (hsnd.integrable_comp (hmoment i).aestronglyMeasurable).mpr (hmoment i)
  have hm : Measurable (fun z : Ω × Ω => ‖pairedIncrement ξ i z‖ ^ q) := by
    exact (((hξ i).comp measurable_snd).sub ((hξ i).comp measurable_fst)).norm.pow_const q
  apply ((hi₁.add hi₂).const_mul ((2 : ℝ) ^ (q - 1))).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact norm_sub_rpow_le (ξ i z.1) (ξ i z.2) hq)

theorem integral_pairedIncrement_norm_rpow_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hq : 1 ≤ q) (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ) (i : Fin n) :
    (∫ z, ‖pairedIncrement ξ i z‖ ^ q ∂μ.prod μ) ≤
      (2 : ℝ) ^ q * ∫ ω, ‖ξ i ω‖ ^ q ∂μ := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hsnd : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  have hi₁ := (hfst.integrable_comp (hmoment i).aestronglyMeasurable).mpr (hmoment i)
  have hi₂ := (hsnd.integrable_comp (hmoment i).aestronglyMeasurable).mpr (hmoment i)
  have htwo : (2 : ℝ) ^ (q - 1) * 2 = (2 : ℝ) ^ q := by
    calc
      _ = (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((q - 1) + 1) := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ ∫ z : Ω × Ω, (2 : ℝ) ^ (q - 1) * (‖ξ i z.1‖ ^ q + ‖ξ i z.2‖ ^ q) ∂μ.prod μ :=
      integral_mono (integrable_pairedIncrement_norm_rpow ξ hξ hq hmoment i)
        ((hi₁.add hi₂).const_mul _) (fun z => norm_sub_rpow_le _ _ hq)
    _ = _ := by
      rw [integral_const_mul,
        integral_add (f := fun z : Ω × Ω => ‖ξ i z.1‖ ^ q)
          (g := fun z : Ω × Ω => ‖ξ i z.2‖ ^ q) hi₁ hi₂,
        integral_fun_fst (μ := μ) (ν := μ) (fun ω => ‖ξ i ω‖ ^ q),
        integral_fun_snd (μ := μ) (ν := μ) (fun ω => ‖ξ i ω‖ ^ q)]
      simp only [measureReal_univ_eq_one, one_smul]
      rw [show (∫ ω, ‖ξ i ω‖ ^ q ∂μ) + (∫ ω, ‖ξ i ω‖ ^ q ∂μ) =
        2 * (∫ ω, ‖ξ i ω‖ ^ q ∂μ) by ring, ← mul_assoc, htwo]

theorem pairedIncrement_norm_moment_budget
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∑ i, ∫ z, ‖pairedIncrement ξ i z‖ ^ q ∂μ.prod μ) ≤ (2 * A) ^ q := by
  calc
    _ ≤ ∑ i, (2 : ℝ) ^ q * ∫ ω, ‖ξ i ω‖ ^ q ∂μ :=
      Finset.sum_le_sum (fun i _ => integral_pairedIncrement_norm_rpow_le ξ hξ hq hmoment i)
    _ = (2 : ℝ) ^ q * (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) := (Finset.mul_sum ..).symm
    _ ≤ (2 : ℝ) ^ q * A ^ q :=
      mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg (by norm_num) _)
    _ = _ := (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA).symm

theorem identDistrib_pairedIncrement_neg
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) :
    IdentDistrib (pairedIncrement ξ i) (fun z => -pairedIncrement ξ i z) (μ.prod μ) (μ.prod μ) := by
  have hm : Measurable (pairedIncrement ξ i) :=
    ((hξ i).comp measurable_snd).sub ((hξ i).comp measurable_fst)
  have heq : (fun z => -pairedIncrement ξ i z) = pairedIncrement ξ i ∘ Prod.swap := by
    funext z
    dsimp [pairedIncrement]
    abel
  refine ⟨hm.aemeasurable, hm.neg.aemeasurable, ?_⟩
  have hs : Measure.map (Prod.swap : Ω × Ω → Ω × Ω) (μ.prod μ) = μ.prod μ :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).map_eq
  rw [heq, ← Measure.map_map hm measurable_swap, hs]

theorem identDistrib_copyLargeIncrement_neg
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ) (i : Fin n) :
    IdentDistrib (copyLargeIncrementIntegrand (ξ i) t)
      (fun z => -copyLargeIncrementIntegrand (ξ i) t z) (μ.prod μ) (μ.prod μ) := by
  have hh := (identDistrib_pairedIncrement_neg (μ := μ) ξ hξ i).comp (measurable_bennettLargeCutoff t)
  change IdentDistrib (fun z => bennettLargeCutoff t (pairedIncrement ξ i z))
    (fun z => bennettLargeCutoff t (-pairedIncrement ξ i z)) (μ.prod μ) (μ.prod μ) at hh
  simpa only [bennettLargeCutoff_neg, copyLargeIncrementIntegrand_eq_bennettLargeCutoff, pairedIncrement] using hh

theorem iIndepFun_copyLargeIncrementIntegrand
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (t : ℝ) :
    iIndepFun (fun i => copyLargeIncrementIntegrand (ξ i) t) (μ.prod μ) :=
  (iIndepFun_pairedIncrement μ ξ hξ hind).comp
    (fun _ => bennettLargeCutoff t) (fun _ => measurable_bennettLargeCutoff t)

theorem pairedTailExpectedMaximum_direct_bound
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hq : 1 < q) (hA : 0 ≤ A) (ht : 0 < t)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    pairedTailExpectedMaximum μ ξ t ≤ (2 * A) ^ q / t ^ (q - 1) := by
  have hY (i : Fin n) : Measurable (pairedIncrement ξ i) :=
    ((hξ i).comp measurable_snd).sub ((hξ i).comp measurable_fst)
  exact integral_norm_sum_bennettRemainder_le_budget hY ht hq
    (integrable_pairedIncrement_norm_rpow ξ hξ hq.le hmoment) (2 * A)
    (pairedIncrement_norm_moment_budget ξ hξ hq.le hA hmoment hbudget)

theorem integrable_copyLargeIncrement_norm_rpow
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ)
    (hq : 1 ≤ q) (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ) (i : Fin n) :
    Integrable (fun z => ‖copyLargeIncrementIntegrand (ξ i) t z‖ ^ q) (μ.prod μ) := by
  apply (integrable_pairedIncrement_norm_rpow ξ hξ hq hmoment i).mono'
    ((measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) t).norm.pow_const q).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    copyLargeIncrementIntegrand_eq_bennettLargeCutoff]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_bennettLargeCutoff_le t _) (zero_le_one.trans hq)

theorem copyLargeIncrement_norm_moment_budget
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ)
    (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∑ i, ∫ z, ‖copyLargeIncrementIntegrand (ξ i) t z‖ ^ q ∂μ.prod μ) ≤ (2 * A) ^ q := by
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans
    (pairedIncrement_norm_moment_budget ξ hξ hq hA hmoment hbudget)
  apply integral_mono (integrable_copyLargeIncrement_norm_rpow ξ hξ t hq hmoment i)
    (integrable_pairedIncrement_norm_rpow ξ hξ hq hmoment i)
  intro z
  change ‖copyLargeIncrementIntegrand (ξ i) t z‖ ^ q ≤ ‖pairedIncrement ξ i z‖ ^ q
  rw [copyLargeIncrementIntegrand_eq_bennettLargeCutoff]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_bennettLargeCutoff_le t _) (zero_le_one.trans hq)

private theorem polynomial_coordinate_memLp_two
    (X : Ω → ℝ) (hX : Measurable X)
    (hfourth : Integrable (fun ω => X ω ^ 4) μ) : MemLp X (2 : ℝ≥0∞) μ := by
  apply (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr
  apply ((integrable_const (1 : ℝ)).add hfourth).mono' (hX.pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change X ω ^ 2 ≤ 1 + X ω ^ 4
  nlinarith [sq_nonneg (X ω ^ 2 - 1 / 2)]

theorem integrable_copyLargeIncrement_coordinate_sq_of_fourth
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ) (i : Fin n) (j : Fin p) :
    Integrable (fun z => copyLargeIncrementIntegrand (ξ i) t z j ^ 2) (μ.prod μ) := by
  have hL2 (k : Fin n) (l : Fin p) : MemLp (fun ω => ξ k ω l) (2 : ℝ≥0∞) μ :=
    polynomial_coordinate_memLp_two _ ((measurable_pi_apply l).comp (hξ k)) (hi4 k l)
  exact (pairedTail_coordinate_memLp_two μ ξ hξ hL2 t i j).integrable_sq

/-- The zero-tail-variance alternative is an assertion about the actual
large-increment sum, rather than a convention in the Bennett denominator. -/
theorem pairedTailExpectedMaximum_zero_of_variance_zero
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hv : pairedTailVariance μ ξ t = 0) : pairedTailExpectedMaximum μ ξ t = 0 := by
  have hz := truncated_bennett_maximum_zero_variance
    (fun i => copyLargeIncrementIntegrand (ξ i) t)
    (integrable_copyLargeIncrement_coordinate_sq_of_fourth ξ hξ t hi4)
    (fun j => by simpa only [hv] using pairedTailCoordinateSecond_le μ ξ t j)
  have hn : (fun z => ‖arrayLargeIncrementIntegrand ξ t z‖) =ᵐ[μ.prod μ] 0 := by
    filter_upwards [hz] with z hz
    change ‖sumVector (fun i => copyLargeIncrementIntegrand (ξ i) t) z‖ = 0
    rw [hz]
    simp only [Pi.zero_apply, norm_zero]
  exact (integral_congr_ae hn).trans (integral_zero _ _)

/-- Applying the fully proved G.4 to the actual centrally symmetric large
increments. The original observations need not themselves be symmetric.
The v_t=0 case is proved separately before using totalized division. -/
theorem pairedTailExpectedMaximum_bennett_bound
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hp : 1 ≤ p) (t : ℝ)
    (hq : 1 < q) (hA : 0 ≤ A) (hu : 0 < u)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    pairedTailExpectedMaximum μ ξ t ≤
      2 * u * dimensionLog p /
        Real.log (1 + u ^ 2 * dimensionLog p / pairedTailVariance μ ξ t) +
          (2 * A) ^ q / u ^ (q - 1) := by
  by_cases hv : pairedTailVariance μ ξ t = 0
  · rw [pairedTailExpectedMaximum_zero_of_variance_zero ξ hξ t hi4 hv, hv]
    simp only [div_zero, add_zero, Real.log_one, zero_add]
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hu.le _)
  have hvpos : 0 < pairedTailVariance μ ξ t :=
    (pairedTailVariance_nonneg μ ξ t).lt_of_ne' hv
  exact truncated_bennett_maximum
    (fun i => copyLargeIncrementIntegrand (ξ i) t) hp
    (fun i => measurable_copyLargeIncrementIntegrand (ξ i) (hξ i) t)
    (iIndepFun_copyLargeIncrementIntegrand ξ hξ hind t)
    (identDistrib_copyLargeIncrement_neg ξ hξ t) hq hu hvpos
    (integrable_copyLargeIncrement_coordinate_sq_of_fourth ξ hξ t hi4)
    (pairedTailCoordinateSecond_le μ ξ t)
    (integrable_copyLargeIncrement_norm_rpow ξ hξ t hq.le hmoment)
    (copyLargeIncrement_norm_moment_budget ξ hξ t hq.le hA hmoment hbudget)

/-- Markov's bound for the actual strict whole-vector tail event. -/
theorem probability_norm_gt_le_moment
    {T : Ω → Vector p} (hT : Measurable T) (ht : 0 < t) (hq : 0 < q)
    (hmoment : Integrable (fun ω => ‖T ω‖ ^ q) μ) :
    μ.real {ω | t < ‖T ω‖} ≤ (∫ ω, ‖T ω‖ ^ q ∂μ) / t ^ q := by
  let E : Set Ω := {ω | t < ‖T ω‖}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hT.norm
  have hind : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hident : (∫ ω, E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = μ.real E := by
    rw [integral_indicator hE]
    simp
  have hpoint (ω : Ω) : E.indicator (fun _ : Ω => (1 : ℝ)) ω ≤ ‖T ω‖ ^ q / t ^ q := by
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he, one_le_div (Real.rpow_pos_of_pos ht _)]
      exact Real.rpow_le_rpow ht.le (le_of_lt he) hq.le
    · rw [Set.indicator_of_not_mem he]
      exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg ht.le _)
  rw [← hident]
  exact (integral_mono hind (hmoment.div_const _) hpoint).trans_eq (integral_div _ _)

theorem pairedIncrement_tail_probability_sum_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hq : 1 ≤ q) (hA : 0 ≤ A) (ht : 0 < t)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∑ i, (μ.prod μ).real {z | t < ‖pairedIncrement ξ i z‖}) ≤ (2 * A) ^ q / t ^ q := by
  calc
    _ ≤ ∑ i, (∫ z, ‖pairedIncrement ξ i z‖ ^ q ∂μ.prod μ) / t ^ q :=
      Finset.sum_le_sum (fun i _ => probability_norm_gt_le_moment
        (((hξ i).comp measurable_snd).sub ((hξ i).comp measurable_fst)) ht
        (zero_lt_one.trans_le hq) (integrable_pairedIncrement_norm_rpow ξ hξ hq hmoment i))
    _ = (∑ i, ∫ z, ‖pairedIncrement ξ i z‖ ^ q ∂μ.prod μ) / t ^ q := (Finset.sum_div ..).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      (pairedIncrement_norm_moment_budget ξ hξ hq hA hmoment hbudget) (Real.rpow_nonneg ht.le _)

/-- Cauchy--Schwarz is applied to each expectation and then to the sum
over summands. The coordinate fourth-moment budget remains a distinct input. -/
theorem pairedTailCoordinateSecond_sq_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (t : ℝ)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ) (j : Fin p) :
    pairedTailCoordinateSecond μ ξ t j ^ 2 ≤
      (∑ i, ∫ z, pairedIncrement ξ i z j ^ 4 ∂μ.prod μ) *
        (∑ i, (μ.prod μ).real {z | t < ‖pairedIncrement ξ i z‖}) := by
  let E : Fin n → Set (Ω × Ω) := fun i => {z | t < ‖pairedIncrement ξ i z‖}
  have hE (i : Fin n) : MeasurableSet (E i) :=
    measurableSet_lt measurable_const
      (((hξ i).comp measurable_snd).sub ((hξ i).comp measurable_fst)).norm
  have hL2 (i : Fin n) (k : Fin p) : MemLp (fun ω => ξ i ω k) (2 : ℝ≥0∞) μ :=
    polynomial_coordinate_memLp_two _ ((measurable_pi_apply k).comp (hξ i)) (hi4 i k)
  have hi2 (i : Fin n) : Integrable (fun z => pairedIncrement ξ i z j ^ 2) (μ.prod μ) :=
    (pairedIncrement_coordinate_memLp_two μ ξ hL2 i j).integrable_sq
  have hi22 (i : Fin n) : Integrable (fun z => (pairedIncrement ξ i z j ^ 2) ^ 2) (μ.prod μ) := by
    simpa only [← pow_mul, Nat.reduceMul] using integrable_pairedIncrement_fourth μ ξ hξ i j (hi4 i j)
  have hs := sum_indicator_integral_sq_le hE hi2 hi22
  have heq : (∑ i, ∫ z, (E i).indicator (fun z => pairedIncrement ξ i z j ^ 2) z ∂μ.prod μ) =
      pairedTailCoordinateSecond μ ξ t j := by
    rw [pairedTailCoordinateSecond_eq_tail_integrals]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by rfl)
  rw [heq] at hs
  simpa only [← pow_mul, Nat.reduceMul, E] using hs

theorem pairedTailVariance_polynomial_bound
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {D : ℝ} (hD : 0 ≤ D) (hq : 1 ≤ q) (hA : 0 ≤ A) (ht : 0 < t)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    pairedTailVariance μ ξ t ≤ Real.sqrt (16 * D * ((2 * A) ^ q / t ^ q)) := by
  have hr : 0 ≤ 16 * D * ((2 * A) ^ q / t ^ q) := by positivity
  have hp := pairedIncrement_tail_probability_sum_le ξ hξ hq hA ht hmoment hbudget
  have hraw4 (j : Fin p) : (∑ i, ∫ z, pairedIncrement ξ i z j ^ 4 ∂μ.prod μ) ≤ 16 * D := by
    calc
      _ ≤ ∑ i, 16 * ∫ ω, ξ i ω j ^ 4 ∂μ := Finset.sum_le_sum
        (fun i _ => integral_pairedIncrement_fourth_le μ ξ hξ i j (hi4 i j))
      _ = 16 * (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfourth j) (by norm_num)
  unfold pairedTailVariance
  apply (Finset.fold_max_le _).mpr
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  intro j _
  have hs := (pairedTailCoordinateSecond_sq_le ξ hξ t hi4 j).trans
    (mul_le_mul (hraw4 j) hp (Finset.sum_nonneg (fun i _ => measureReal_nonneg)) (by positivity : 0 ≤ 16 * D))
  have hn : 0 ≤ pairedTailCoordinateSecond μ ξ t j :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun z => sq_nonneg _))
  exact (Real.le_sqrt hn hr).mpr hs

/-- The precise rate form of the mixed tail estimate in Appendix G. The
constant depends only on q; the fourth-moment scale is the distinct d². -/
theorem pairedTailVariance_polynomial_rate
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {d : ℝ} (hd : 0 ≤ d) (hq : 1 ≤ q) (hA : 0 ≤ A) (ht : 0 < t)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    pairedTailVariance μ ξ t ≤ 4 * (2 : ℝ) ^ (q / 2) * d * (A / t) ^ (q / 2) := by
  have hb := pairedTailVariance_polynomial_bound ξ hξ (sq_nonneg d) hq hA ht hi4 hfourth hmoment hbudget
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  have hbase : 0 ≤ (2 * A) / t := by positivity
  have hr : Real.sqrt ((2 * A) ^ q / t ^ q) =
      (2 : ℝ) ^ (q / 2) * (A / t) ^ (q / 2) := by
    calc
      _ = Real.sqrt (((2 * A) / t) ^ q) :=
        congrArg Real.sqrt (Real.div_rpow (by positivity : 0 ≤ 2 * A) ht.le q).symm
      _ = (((2 * A) / t) ^ q) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = ((2 * A) / t) ^ (q / 2) := by
        rw [← Real.rpow_mul hbase]
        congr 1
        ring
      _ = (2 * (A / t)) ^ (q / 2) := by congr 1; ring
      _ = _ := Real.mul_rpow (by norm_num) (div_nonneg hA ht.le)
  rw [Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg d)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), h16, Real.sqrt_sq hd, hr] at hb
  nlinarith

/-- The U scale written through its exact squared calibration. -/
def bennettBaseScale (d L : ℝ) : ℝ := Real.sqrt (d * L ^ (5 / 2 : ℝ))

def bennettEnvelopeScale (q A L : ℝ) : ℝ := A * L ^ (3 / 2 - 1 / q : ℝ)

def bennettPolynomialParameter (q d A L : ℝ) : ℝ :=
  (bennettEnvelopeScale q A L / bennettBaseScale d L) ^ 2

def bennettPolynomialLog (q d A L : ℝ) : ℝ :=
  Real.log (Real.exp 1 + bennettPolynomialParameter q d A L)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettBaseScale_sq {d L : ℝ} (hd : 0 ≤ d) (hL : 0 ≤ L) :
    bennettBaseScale d L ^ 2 = d * L ^ (5 / 2 : ℝ) :=
  Real.sq_sqrt (mul_nonneg hd (Real.rpow_nonneg hL _))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettBaseScale_pos {d L : ℝ} (hd : 0 < d) (hL : 0 < L) :
    0 < bennettBaseScale d L :=
  Real.sqrt_pos.mpr (mul_pos hd (Real.rpow_pos_of_pos hL _))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettPolynomialParameter_eq {q d A L : ℝ} (hd : 0 < d) (hL : 0 < L) :
    bennettPolynomialParameter q d A L = (A ^ 2 / d) * L ^ (1 / 2 - 2 / q : ℝ) := by
  unfold bennettPolynomialParameter bennettEnvelopeScale
  rw [div_pow, mul_pow, bennettBaseScale_sq hd.le hL.le,
    ← Real.rpow_mul_natCast hL.le (3 / 2 - 1 / q : ℝ) 2]
  simp only [Nat.cast_ofNat]
  have hexp : (3 / 2 - 1 / q : ℝ) * 2 = 3 - 2 / q := by ring
  have hratio : L ^ (1 / 2 - 2 / q : ℝ) = L ^ (3 - 2 / q : ℝ) / L ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_sub hL]
    congr 1
    ring
  rw [hexp, hratio]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem one_le_bennettPolynomialLog (q d A L : ℝ) :
    1 ≤ bennettPolynomialLog q d A L := by
  have hn : 0 ≤ bennettPolynomialParameter q d A L := sq_nonneg _
  have hh := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hn)
  simpa only [Real.log_exp, bennettPolynomialLog] using hh

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The first three terms of G.1 have exactly the same scale in the
small-parameter calibration. This is scalar algebra, not a CLT assumption. -/
theorem bennett_small_calibration_identities {d L : ℝ} (hd : 0 < d) (hL : 0 < L) :
    let U := bennettBaseScale d L
    let t := U / L ^ (3 / 2 : ℝ)
    t * L ^ (3 / 2 : ℝ) = U ∧ d * L / t = U ∧
      d ^ 2 * Real.sqrt L / t ^ 3 = U := by
  let U := bennettBaseScale d L
  have hU : 0 < U := bennettBaseScale_pos hd hL
  have hcal : U ^ 2 = d * L ^ (5 / 2 : ℝ) := bennettBaseScale_sq hd.le hL.le
  have hLp : L ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hpow : L * L ^ (3 / 2 : ℝ) = L ^ (5 / 2 : ℝ) := by
    calc
      _ = L ^ (1 : ℝ) * L ^ (3 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + 3 / 2) := (Real.rpow_add hL _ _).symm
      _ = _ := by congr 1; ring
  have hpow3 : Real.sqrt L * (L ^ (3 / 2 : ℝ)) ^ 3 = (L ^ (5 / 2 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hL.le (3 / 2 : ℝ) 3,
      ← Real.rpow_mul_natCast hL.le (5 / 2 : ℝ) 2, ← Real.rpow_add hL]
    congr 1
    ring
  change (U / L ^ (3 / 2 : ℝ)) * L ^ (3 / 2 : ℝ) = U ∧
    d * L / (U / L ^ (3 / 2 : ℝ)) = U ∧
    d ^ 2 * Real.sqrt L / (U / L ^ (3 / 2 : ℝ)) ^ 3 = U
  refine ⟨div_mul_cancel₀ U hLp, ?_, ?_⟩
  · rw [div_div_eq_mul_div]
    apply (div_eq_iff hU.ne').mpr
    calc
      _ = d * (L * L ^ (3 / 2 : ℝ)) := by ring
      _ = U ^ 2 := by rw [hpow, hcal]
      _ = _ := by ring
  · rw [div_pow, div_div_eq_mul_div]
    apply (div_eq_iff (pow_ne_zero 3 hU.ne')).mpr
    calc
      _ = d ^ 2 * (Real.sqrt L * (L ^ (3 / 2 : ℝ)) ^ 3) := by ring
      _ = (d * L ^ (5 / 2 : ℝ)) ^ 2 := by rw [hpow3]; ring
      _ = U * U ^ 3 := by rw [← hcal]; ring

def bennettSmallRegimeConstant (q : ℝ) : ℝ :=
  largeIncrementMasterConstant * (3 + 4 * (2 : ℝ) ^ (q / 2) + (2 : ℝ) ^ q)

def bennettTailConstant (q : ℝ) : ℝ := 4 * (2 : ℝ) ^ (q / 2)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettTailConstant_pos (q : ℝ) : 0 < bennettTailConstant q := by
  unfold bennettTailConstant
  positivity

/-- The logarithmic comparison constant is selected before the varying
parameter or any probability model. -/
def bennettLogComparisonConstant (q : ℝ) : ℝ :=
  Classical.choose (exists_bennett_log_denominator_lower
    (2 / q - (q - 1) / 2) (1 / bennettTailConstant q)
    (one_div_pos.mpr (bennettTailConstant_pos q)))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettLogComparisonConstant_pos (q : ℝ) : 0 < bennettLogComparisonConstant q :=
  (Classical.choose_spec (exists_bennett_log_denominator_lower
    (2 / q - (q - 1) / 2) (1 / bennettTailConstant q)
    (one_div_pos.mpr (bennettTailConstant_pos q)))).1

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettLogComparisonConstant_bound (q : ℝ) (K : ℝ) (hK : 1 ≤ K) :
    bennettLogComparisonConstant q * bennettParameterLog K ≤
      Real.log (1 + (1 / bennettTailConstant q) * K *
        (bennettParameterLog K) ^ (2 / q - (q - 1) / 2)) :=
  (Classical.choose_spec (exists_bennett_log_denominator_lower
    (2 / q - (q - 1) / 2) (1 / bennettTailConstant q)
    (one_div_pos.mpr (bennettTailConstant_pos q)))).2 K hK

def bennettRatioConstant (q : ℝ) : ℝ :=
  Classical.choose (bennett_large_regime_ratio_bounds q)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettRatioConstant_pos (q : ℝ) : 0 < bennettRatioConstant q :=
  (Classical.choose_spec (bennett_large_regime_ratio_bounds q)).1

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem bennettRatioConstant_bound (q K : ℝ) (hK : 1 ≤ K) :
    (bennettParameterLog K) ^ (2 * (1 - 1 / q)) / K ≤ bennettRatioConstant q ∧
      (bennettParameterLog K) ^ (4 * (1 - 1 / q)) / K ^ (2 : ℝ) ≤ bennettRatioConstant q ∧
      (bennettParameterLog K) ^ (2 * (1 - 1 / q) + (q - 1) / 2) / K ≤ bennettRatioConstant q :=
  (Classical.choose_spec (bennett_large_regime_ratio_bounds q)).2 K hK

def bennettLargeRegimeConstant (q : ℝ) : ℝ := largeIncrementMasterConstant *
  (1 + (2 + bennettTailConstant q) * bennettRatioConstant q +
    2 / bennettLogComparisonConstant q + (2 : ℝ) ^ q)

def bennettPolynomialConstant (q : ℝ) : ℝ :=
  1 + max (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem one_le_bennettPolynomialConstant (q : ℝ) : 1 ≤ bennettPolynomialConstant q := by
  have hC : 0 ≤ largeIncrementMasterConstant := zero_le_one.trans one_le_largeIncrementMasterConstant
  have hs : 0 ≤ bennettSmallRegimeConstant q := by
    unfold bennettSmallRegimeConstant
    positivity
  have hm : 0 ≤ max (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q) :=
    hs.trans (le_max_left _ _)
  unfold bennettPolynomialConstant
  linarith

/-- The small-parameter half of the Bennett polynomial bound is already
an unconditional comparison for the actual array and exact Gaussian law.
It retains the separate coordinate fourth-moment requirement. -/
theorem bennett_polynomial_small_regime
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 ≤ A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q)
    (hK : bennettPolynomialParameter q d A (dimensionLog p) ≤ 1) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettSmallRegimeConstant q * bennettBaseScale d (dimensionLog p) := by
  let L := dimensionLog p
  let U := bennettBaseScale d L
  let V := bennettEnvelopeScale q A L
  let t := U / L ^ (3 / 2 : ℝ)
  let Ctail := 4 * (2 : ℝ) ^ (q / 2)
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 < U := bennettBaseScale_pos hd hL
  have ht : 0 < t := div_pos hU (Real.rpow_pos_of_pos hL _)
  have hV : 0 ≤ V := mul_nonneg hA (Real.rpow_nonneg hL.le _)
  have hVU : V ≤ U := by
    have hr : 0 ≤ V / U := div_nonneg hV hU.le
    have hk : (V / U) ^ 2 ≤ 1 := hK
    exact (div_le_one hU).mp (by nlinarith)
  have hLp : 0 < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hpow : L ^ (3 / 2 - 1 / q : ℝ) * L ^ (1 / q) = L ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hratio : A / t ≤ L ^ (1 / q) := by
    apply (div_le_iff₀ ht).mpr
    change A ≤ L ^ (1 / q) * (U / L ^ (3 / 2 : ℝ))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_right hVU (Real.rpow_nonneg hL.le (1 / q))
    change (A * L ^ (3 / 2 - 1 / q : ℝ)) * L ^ (1 / q) ≤ U * L ^ (1 / q) at hh
    calc
      _ = (A * L ^ (3 / 2 - 1 / q : ℝ)) * L ^ (1 / q) := by rw [mul_assoc, hpow]
      _ ≤ U * L ^ (1 / q) := hh
      _ = _ := mul_comm _ _
  have hcal := bennett_small_calibration_identities hd hL
  have h32 : L ^ (3 / 2 : ℝ) = Real.sqrt L * L := by
    calc
      _ = L ^ ((1 / 2 : ℝ) + 1) := by congr 1; ring
      _ = L ^ (1 / 2 : ℝ) * L ^ (1 : ℝ) := Real.rpow_add hL _ _
      _ = _ := by rw [← Real.sqrt_eq_rpow, Real.rpow_one]
  have hfirst : t * Real.sqrt L * L = U := by
    calc
      _ = t * L ^ (3 / 2 : ℝ) := by rw [h32]; ring
      _ = U := hcal.1
  have hsecond : L * Real.sqrt (d ^ 2) / t = U := by
    rw [Real.sqrt_sq hd.le]
    simpa only [mul_comm] using hcal.2.1
  have hthird : Real.sqrt L * d ^ 2 / t ^ 3 = U := by
    simpa only [mul_comm] using hcal.2.2
  have hLhalf : (L ^ (1 / q)) ^ (q / 2) = Real.sqrt L := by
    rw [← Real.rpow_mul hL.le, Real.sqrt_eq_rpow]
    congr 1
    field_simp
  have hv := pairedTailVariance_polynomial_rate ξ hξ hd.le (by linarith : 1 ≤ q)
    hA ht hi4 hfourth hmoment hbudget
  have hv' : pairedTailVariance μ ξ t ≤ Ctail * d * Real.sqrt L := by
    have hr := Real.rpow_le_rpow (div_nonneg hA ht.le) hratio (by linarith : 0 ≤ q / 2)
    rw [hLhalf] at hr
    exact hv.trans (mul_le_mul_of_nonneg_left hr (by positivity))
  have htermv : Real.sqrt L * pairedTailVariance μ ξ t / t ≤ Ctail * U := by
    calc
      _ ≤ Real.sqrt L * (Ctail * d * Real.sqrt L) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' (Real.sqrt_nonneg _)) ht.le
      _ = Ctail * (d * L / t) := by
        have heq : Real.sqrt L * (Ctail * d * Real.sqrt L) = Ctail * d * L := by
          calc
            _ = Ctail * d * (Real.sqrt L) ^ 2 := by ring
            _ = _ := by rw [Real.sq_sqrt hL.le]
        rw [heq]
        ring
      _ = _ := by rw [hcal.2.1]
  have hLq : (L ^ (1 / q)) ^ q = L := by
    rw [← Real.rpow_mul hL.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hApow : A ^ q ≤ t ^ q * L := by
    have ha : A ≤ t * L ^ (1 / q) := by
      simpa only [mul_comm] using (div_le_iff₀ ht).mp hratio
    have hh := Real.rpow_le_rpow hA ha hq0.le
    rw [Real.mul_rpow ht.le (Real.rpow_nonneg hL.le _), hLq] at hh
    exact hh
  have htpow : t ^ q / t ^ (q - 1) = t := by
    rw [← Real.rpow_sub ht, show q - (q - 1) = 1 by ring, Real.rpow_one]
  have hM := pairedTailExpectedMaximum_direct_bound ξ hξ hq1 hA ht hmoment hbudget
  have hM' : pairedTailExpectedMaximum μ ξ t ≤ (2 : ℝ) ^ q * t * L := by
    calc
      _ ≤ (2 * A) ^ q / t ^ (q - 1) := hM
      _ = (2 : ℝ) ^ q * A ^ q / t ^ (q - 1) := by rw [Real.mul_rpow (by norm_num) hA]
      _ ≤ (2 : ℝ) ^ q * (t ^ q * L) / t ^ (q - 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hApow (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg ht.le _)
      _ = (2 : ℝ) ^ q * (t ^ q / t ^ (q - 1)) * L := by ring
      _ = _ := by rw [htpow]
  have htermM : Real.sqrt L * pairedTailExpectedMaximum μ ξ t ≤ (2 : ℝ) ^ q * U := by
    have hh := mul_le_mul_of_nonneg_left hM' (Real.sqrt_nonneg L)
    have heq : Real.sqrt L * ((2 : ℝ) ^ q * t * L) = (2 : ℝ) ^ q * U := by
      calc
        _ = (2 : ℝ) ^ q * (t * Real.sqrt L * L) := by ring
        _ = _ := by rw [hfirst]
    exact hh.trans_eq heq
  have hrate : largeIncrementBandwidthRate L (d ^ 2)
      (pairedTailVariance μ ξ t) (pairedTailExpectedMaximum μ ξ t) t ≤
        (3 + Ctail + (2 : ℝ) ^ q) * U := by
    unfold largeIncrementBandwidthRate
    rw [hfirst, hsecond, hthird]
    linarith
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hi4 hunit G hG
    (sq_nonneg d) hfourth ht
  have hC : 0 ≤ largeIncrementMasterConstant := zero_le_one.trans one_le_largeIncrementMasterConstant
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hrate hC
  convert hh using 1 <;> unfold bennettSmallRegimeConstant <;> dsimp [Ctail, U] <;> ring

set_option maxHeartbeats 2000000 in
/-- The large-parameter half of Proposition 3, with the actual paired-copy
budgets discharged and the logarithmic gain in its stated normalization. -/
theorem bennett_polynomial_large_regime
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 < A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q)
    (hK : 1 < bennettPolynomialParameter q d A (dimensionLog p)) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettLargeRegimeConstant q *
        (bennettEnvelopeScale q A (dimensionLog p) /
          bennettPolynomialLog q d A (dimensionLog p) ^ (1 - 1 / q)) := by
  let L := dimensionLog p
  let U := bennettBaseScale d L
  let V := bennettEnvelopeScale q A L
  let K := bennettPolynomialParameter q d A L
  let ell := bennettParameterLog K
  let r := V / ell ^ (1 - 1 / q)
  let t := r / L ^ (3 / 2 : ℝ)
  let u := ell * t
  let Ct := bennettTailConstant q
  let α := bennettLogComparisonConstant q
  let Cr := bennettRatioConstant q
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 < U := bennettBaseScale_pos hd hL
  have hV : 0 < V := mul_pos hA (Real.rpow_pos_of_pos hL _)
  have hK1 : 1 < K := hK
  have hK0 : 0 < K := zero_lt_one.trans hK1
  have hell1 : 1 ≤ ell := bennettParameterLog_ge_one hK1.le
  have hell : 0 < ell := zero_lt_one.trans_le hell1
  have hr : 0 < r := div_pos hV (Real.rpow_pos_of_pos hell _)
  have ht : 0 < t := div_pos hr (Real.rpow_pos_of_pos hL _)
  have hu : 0 < u := mul_pos hell ht
  have hCt : 0 < Ct := bennettTailConstant_pos q
  have hα : 0 < α := bennettLogComparisonConstant_pos q
  have hCr : 0 < Cr := bennettRatioConstant_pos q
  have hUcal : U ^ 2 = d * L ^ (5 / 2 : ℝ) := bennettBaseScale_sq hd.le hL.le
  have hKV : V ^ 2 = K * U ^ 2 := by
    change V ^ 2 = (V / U) ^ 2 * U ^ 2
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hU.ne')]
  have hVdef : V = A * L ^ (3 / 2 - 1 / q : ℝ) := rfl
  have hrV : r * ell ^ (1 - 1 / q) = V := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hell _).ne'
  have htR : t * L ^ (3 / 2 : ℝ) = r := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hL _).ne'
  have huDef : u = ell * t := rfl
  have hcal := bennett_large_calibration_identities hq0 hL hell hK0 hr ht hUcal hKV hVdef hrV htR huDef
  have htail := bennett_large_tail_identities hq0 hL hell hK0 hr ht hUcal hKV hVdef hrV htR huDef
  have hv : pairedTailVariance μ ξ t ≤ Ct * d * (A / t) ^ (q / 2) := by
    exact pairedTailVariance_polynomial_rate ξ hξ hd.le (by linarith : 1 ≤ q)
      hA.le ht hi4 hfourth hmoment hbudget
  have hvarcost : Real.sqrt L * pairedTailVariance μ ξ t / t ≤
      Ct * (r * ell ^ (2 * (1 - 1 / q) + (q - 1) / 2) / K) := by
    calc
      _ ≤ Real.sqrt L * (Ct * d * (A / t) ^ (q / 2)) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg _)) ht.le
      _ = Ct * (Real.sqrt L * d * (A / t) ^ (q / 2) / t) := by ring
      _ = _ := by rw [hcal.2.2.2]
  have hMcost : Real.sqrt L * pairedTailExpectedMaximum μ ξ t ≤
      (2 / α + (2 : ℝ) ^ q) * r := by
    by_cases hvzero : pairedTailVariance μ ξ t = 0
    · rw [pairedTailExpectedMaximum_zero_of_variance_zero ξ hξ t hi4 hvzero, mul_zero]
      positivity
    have hvpos : 0 < pairedTailVariance μ ξ t := (pairedTailVariance_nonneg μ ξ t).lt_of_ne' hvzero
    have hvbar : 0 < Ct * d * (A / t) ^ (q / 2) := by positivity
    have hnum : 0 ≤ u ^ 2 * L := by positivity
    have hratioEq : u ^ 2 * L / (Ct * d * (A / t) ^ (q / 2)) =
        (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) := by
      calc
        _ = (1 / Ct) * (u ^ 2 * L / (d * (A / t) ^ (q / 2))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by rw [htail.2.2]; ring
    have hratio : (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) ≤
        u ^ 2 * L / pairedTailVariance μ ξ t := by
      rw [← hratioEq]
      apply (div_le_div_iff₀ hvbar hvpos).mpr
      exact mul_le_mul_of_nonneg_left hv hnum
    have hlog := Real.log_le_log
      (show 0 < 1 + (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) by positivity)
      (add_le_add_left hratio 1)
    have hdenlower : α * ell ≤ Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) :=
      (bennettLogComparisonConstant_bound q K hK1.le).trans hlog
    have hdenpos : 0 < Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) :=
      (mul_pos hα hell).trans_le hdenlower
    have hfrac : (2 * Real.sqrt L * u * L) /
        Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) ≤ (2 / α) * r := by
      calc
        _ ≤ (2 * Real.sqrt L * u * L) / (α * ell) := by
          apply (div_le_div_iff₀ hdenpos (mul_pos hα hell)).mpr
          exact mul_le_mul_of_nonneg_left hdenlower (by positivity)
        _ = _ := by
          have heq : 2 * Real.sqrt L * u * L = 2 * (r * ell) := by
            calc
              _ = 2 * (Real.sqrt L * u * L) := by ring
              _ = _ := by rw [htail.1]
          rw [heq]
          field_simp [hα.ne', hell.ne']
          ring
    have hrem : Real.sqrt L * ((2 * A) ^ q / u ^ (q - 1)) = (2 : ℝ) ^ q * r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le]
      calc
        _ = (2 : ℝ) ^ q * (Real.sqrt L * A ^ q / u ^ (q - 1)) := by ring
        _ = _ := by rw [htail.2.1]
    have hM := pairedTailExpectedMaximum_bennett_bound ξ hξ hind hp t hq1 hA.le hu hi4 hmoment hbudget
    calc
      _ ≤ Real.sqrt L * (2 * u * L / Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) +
          (2 * A) ^ q / u ^ (q - 1)) :=
        mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
      _ = (2 * Real.sqrt L * u * L) / Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) +
          Real.sqrt L * ((2 * A) ^ q / u ^ (q - 1)) := by ring
      _ ≤ (2 / α) * r + (2 : ℝ) ^ q * r := add_le_add hfrac hrem.le
      _ = _ := by ring
  have hratios := bennettRatioConstant_bound q K hK1.le
  simp only [Real.rpow_two] at hratios
  have h32 : L ^ (3 / 2 : ℝ) = Real.sqrt L * L := by
    calc
      _ = L ^ ((1 / 2 : ℝ) + 1) := by congr 1; ring
      _ = L ^ (1 / 2 : ℝ) * L ^ (1 : ℝ) := Real.rpow_add hL _ _
      _ = _ := by rw [← Real.sqrt_eq_rpow, Real.rpow_one]
  have hfirst : t * Real.sqrt L * L = r := by
    calc
      _ = t * L ^ (3 / 2 : ℝ) := by rw [h32]; ring
      _ = _ := htR
  have hsecond : L * Real.sqrt (d ^ 2) / t ≤ Cr * r := by
    rw [Real.sqrt_sq hd.le, show L * d = d * L by ring, hcal.2.1]
    convert mul_le_mul_of_nonneg_left hratios.1 hr.le using 1 <;> ring
  have hthird : Real.sqrt L * d ^ 2 / t ^ 3 ≤ Cr * r := by
    rw [show Real.sqrt L * d ^ 2 = d ^ 2 * Real.sqrt L by ring, hcal.2.2.1]
    convert mul_le_mul_of_nonneg_left hratios.2.1 hr.le using 1 <;> ring
  have hvarfinal : Real.sqrt L * pairedTailVariance μ ξ t / t ≤ Ct * Cr * r := by
    apply hvarcost.trans
    convert mul_le_mul_of_nonneg_left hratios.2.2 (mul_nonneg hCt.le hr.le) using 1 <;> ring
  have hrate : largeIncrementBandwidthRate L (d ^ 2)
      (pairedTailVariance μ ξ t) (pairedTailExpectedMaximum μ ξ t) t ≤
        (1 + (2 + Ct) * Cr + 2 / α + (2 : ℝ) ^ q) * r := by
    unfold largeIncrementBandwidthRate
    rw [hfirst]
    nlinarith
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hi4 hunit G hG
    (sq_nonneg d) hfourth ht
  have hC : 0 ≤ largeIncrementMasterConstant := zero_le_one.trans one_le_largeIncrementMasterConstant
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hrate hC
  convert hh using 1 <;>
    simp only [bennettLargeRegimeConstant, Ct, Cr, α, r, ell, K, L, V,
      bennettPolynomialLog, bennettParameterLog] <;> ring

def bennettPolynomialRate (q d A L : ℝ) : ℝ :=
  bennettBaseScale d L +
    bennettEnvelopeScale q A L / bennettPolynomialLog q d A L ^ (1 - 1 / q)

/-- Both parameter regimes and saturation by one, for the actual normalized
array. The constant is the fixed function of q defined above; no analytic
estimate occurs among the hypotheses. -/
theorem bennettPolynomialCLT
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 < A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettPolynomialConstant q * min 1 (bennettPolynomialRate q d A (dimensionLog p)) := by
  let L := dimensionLog p
  let R := bennettPolynomialRate q d A L
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 ≤ bennettBaseScale d L := Real.sqrt_nonneg _
  have htail : 0 ≤ bennettEnvelopeScale q A L / bennettPolynomialLog q d A L ^ (1 - 1 / q) :=
    div_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hL.le _))
      (Real.rpow_nonneg (zero_le_one.trans (one_le_bennettPolynomialLog q d A L)) _)
  have hC := one_le_bennettPolynomialConstant q
  have hC0 : 0 ≤ bennettPolynomialConstant q := zero_le_one.trans hC
  have hCs : bennettSmallRegimeConstant q ≤ bennettPolynomialConstant q := by
    have hh := le_max_left (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q)
    unfold bennettPolynomialConstant
    linarith
  have hCl : bennettLargeRegimeConstant q ≤ bennettPolynomialConstant q := by
    have hh := le_max_right (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q)
    unfold bennettPolynomialConstant
    linarith
  have hb : rectangleDistance μ (sumVector ξ) G ≤ bennettPolynomialConstant q * R := by
    by_cases hK : bennettPolynomialParameter q d A L ≤ 1
    · have hs := bennett_polynomial_small_regime hp ξ hξ hind hcenter hi4 hunit G hG hd hq hA.le
        hfourth hmoment hbudget hK
      have hh := mul_le_mul_of_nonneg_right hCs hU
      have hUR : bennettBaseScale d L ≤ R := le_add_of_nonneg_right htail
      exact hs.trans (hh.trans (mul_le_mul_of_nonneg_left hUR hC0))
    · have hl := bennett_polynomial_large_regime hp ξ hξ hind hcenter hi4 hunit G hG hd hq hA
        hfourth hmoment hbudget (lt_of_not_ge hK)
      have hh := mul_le_mul_of_nonneg_right hCl htail
      have hTR : bennettEnvelopeScale q A L / bennettPolynomialLog q d A L ^ (1 - 1 / q) ≤ R :=
        le_add_of_nonneg_left hU
      exact hl.trans (hh.trans (mul_le_mul_of_nonneg_left hTR hC0))
  change rectangleDistance μ (sumVector ξ) G ≤ bennettPolynomialConstant q * min 1 R
  by_cases hR : R ≤ 1
  · rw [min_eq_right hR]
    exact hb
  · rw [min_eq_left (le_of_not_ge hR), mul_one]
    exact (rectangleDistance_le_one μ (sumVector ξ) G).trans hC

/-- Proposition 3 in the manuscript's original-observation normalization,
with both genuine moment assumptions, exact covariance, and all measurable
rectangles, including atomic laws and singular covariance. -/
theorem bennettPolynomialCLT_observations
    (hp : 1 ≤ p) (hn : 1 ≤ n) (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (normalizedObservationSum X))
    {B : ℝ} (hB : 1 ≤ B) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hfourth : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 4 ∂μ) ≤ B ^ 2) :
    rectangleDistance μ (normalizedObservationSum X) G ≤
      bennettPolynomialConstant q * min 1
        (B ^ (1 / 2 : ℝ) * dimensionLog p ^ (5 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) +
          (B * dimensionLog p ^ (3 / 2 - 1 / q)) /
            ((n : ℝ) ^ (1 / 2 - 1 / q) *
              Real.log (Real.exp 1 + B * ((n : ℝ) / dimensionLog p) ^ (2 / q - 1 / 2)) ^ (1 - 1 / q))) := by
  let d := rawPolynomialFourthScale n B
  let A := rawPolynomialEnvelopeScale n B q
  let L := dimensionLog p
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hd : 0 < d := div_pos hBpos (Real.sqrt_pos.mpr hN)
  have hApos : 0 < A := mul_pos hBpos (Real.rpow_pos_of_pos hN _)
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    polynomial_coordinate_memLp_two _ ((measurable_pi_apply j).comp (hX i)) (hi4 i j)
  have hG' : G * G.transpose = covariance μ (sumVector (normalizedSummands X)) := by
    simpa only [sumVector_normalizedSummands] using hG
  have hb := bennettPolynomialCLT hp (normalizedSummands X)
    (normalizedSummands_measurable hX) (normalizedSummands_independent hind)
    (normalizedSummands_centered hcenter) (normalizedSummands_fourth_integrable hi4)
    (normalizedSummands_unit_covariance hind hL2 hcenter haverage) G hG' hd hq hApos
    (normalized_coordinate_fourth_budget X hn hfourth)
    (normalized_q_envelope_integrable X q hmoment)
    (normalized_q_envelope_budget X hn hBpos.le (by linarith : 0 < q) hbudget)
  have hK : bennettPolynomialParameter q d A L = B * ((n : ℝ) / L) ^ (2 / q - 1 / 2) := by
    rw [bennettPolynomialParameter_eq hd hL]
    exact rawPolynomialParameter_eq hn hBpos hL
  have hrate : bennettPolynomialRate q d A L =
      B ^ (1 / 2 : ℝ) * L ^ (5 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) +
        (B * L ^ (3 / 2 - 1 / q)) / ((n : ℝ) ^ (1 / 2 - 1 / q) *
          Real.log (Real.exp 1 + B * ((n : ℝ) / L) ^ (2 / q - 1 / 2)) ^ (1 - 1 / q)) := by
    unfold bennettPolynomialRate bennettBaseScale bennettEnvelopeScale bennettPolynomialLog
    rw [hK, rawPolynomialBaseScale_eq hn hBpos.le hL, rawPolynomialEnvelopeTerm_eq hn]
    rw [div_div]
  rw [sumVector_normalizedSummands] at hb
  change rectangleDistance μ (normalizedObservationSum X) G ≤
    bennettPolynomialConstant q * min 1 (bennettPolynomialRate q d A L) at hb
  rw [hrate] at hb
  exact hb

end
end RectangleCLT.Companion.SplitV4
