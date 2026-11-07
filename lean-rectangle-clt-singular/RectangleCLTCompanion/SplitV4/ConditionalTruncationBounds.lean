import RectangleCLTCompanion.SplitV4.ConditionalTruncationKernel
import RectangleCLTCompanion.SplitV4.BennettTruncation
import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import RectangleCLT.TruncationSampleCovariance

/-!
# Numeric conditional-truncation covariance bounds

The budget is the manuscript's `v_T = B^q T^(2-q)`. Moment and covariance
estimates below refer to the actual normalized restricted good laws and
the actual exceptional event, with genuine integrability throughout.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def truncationVarianceBudget (B T q : ℝ) : ℝ := B ^ q * T ^ (2 - q)

theorem truncationVarianceBudget_eq_div {B T q : ℝ} (hT : 0 ≤ T) :
    truncationVarianceBudget B T q = B ^ q / T ^ (q - 2) := by
  unfold truncationVarianceBudget
  rw [show 2 - q = -(q - 2) by ring, Real.rpow_neg hT]
  rfl

theorem bad_norm_pow_le_moment {p : ℕ} (x : Vector p)
    {T q : ℝ} (hT : 0 < T) (r : ℕ) (hrq : (r : ℝ) < q) :
    (goodTruncationSet T)ᶜ.indicator (fun x : Vector p => ‖x‖ ^ r) x ≤
      ‖x‖ ^ q / T ^ (q - r) := by
  classical
  by_cases hx : x ∈ (goodTruncationSet T)ᶜ
  · rw [Set.indicator_of_mem hx]
    have hx' : ¬ ‖x‖ ≤ T := hx
    have hnorm : 0 < ‖x‖ := hT.trans (lt_of_not_ge hx')
    have hpow : T ^ (q - r) ≤ ‖x‖ ^ (q - r) :=
      Real.rpow_le_rpow hT.le (lt_of_not_ge hx').le (sub_pos.mpr hrq).le
    have he : ‖x‖ ^ r * ‖x‖ ^ (q - r) = ‖x‖ ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hnorm]
      congr 1
      ring
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).mpr
      ((mul_le_mul_of_nonneg_left hpow (pow_nonneg (norm_nonneg x) r)).trans_eq he)
  · rw [Set.indicator_of_not_mem hx]
    exact div_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (Real.rpow_nonneg hT.le _)

theorem integrable_bad_norm_pow {p : ℕ}
    (μ : Measure (Vector p)) {T q : ℝ} (hT : 0 < T) (r : ℕ) (hrq : (r : ℝ) < q)
    (hmoment : Integrable (fun x : Vector p => ‖x‖ ^ q) μ) :
    Integrable ((goodTruncationSet T)ᶜ.indicator (fun x : Vector p => ‖x‖ ^ r)) μ := by
  apply (hmoment.div_const (T ^ (q - r))).mono'
    (((measurable_norm.pow_const r).indicator (measurableSet_goodTruncationSet T).compl).aestronglyMeasurable)
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun y _ => pow_nonneg (norm_nonneg y) r) x)]
    exact bad_norm_pow_le_moment x hT r hrq

theorem integral_bad_norm_pow_le {p : ℕ}
    (μ : Measure (Vector p)) {B T q : ℝ} (hT : 0 < T) (r : ℕ) (hrq : (r : ℝ) < q)
    (hmoment : Integrable (fun x : Vector p => ‖x‖ ^ q) μ)
    (hbudget : (∫ x : Vector p, ‖x‖ ^ q ∂μ) ≤ B ^ q) :
    (∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ^ r ∂μ) ≤ B ^ q / T ^ (q - r) := by
  rw [← integral_indicator (measurableSet_goodTruncationSet T).compl]
  calc
    _ ≤ ∫ x : Vector p, ‖x‖ ^ q / T ^ (q - r) ∂μ :=
      integral_mono (integrable_bad_norm_pow μ hT r hrq hmoment)
        (hmoment.div_const _) (fun x => bad_norm_pow_le_moment x hT r hrq)
    _ = (∫ x : Vector p, ‖x‖ ^ q ∂μ) / T ^ (q - r) := integral_div _ _
    _ ≤ B ^ q / T ^ (q - r) := div_le_div_of_nonneg_right hbudget
      (Real.rpow_nonneg hT.le _)

theorem integral_bad_norm_sq_le_varianceBudget {p : ℕ}
    (μ : Measure (Vector p)) {B T q : ℝ} (hT : 0 < T) (hq : 2 < q)
    (hmoment : Integrable (fun x : Vector p => ‖x‖ ^ q) μ)
    (hbudget : (∫ x : Vector p, ‖x‖ ^ q ∂μ) ≤ B ^ q) :
    (∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ^ 2 ∂μ) ≤ truncationVarianceBudget B T q := by
  rw [truncationVarianceBudget_eq_div hT.le]
  exact integral_bad_norm_pow_le μ hT 2 hq hmoment hbudget

theorem norm_pow_two_le_one_add_rpow {p : ℕ} (x : Vector p) {q : ℝ} (hq : 2 ≤ q) :
    ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ q := by
  by_cases hx : ‖x‖ ≤ 1
  · nlinarith [norm_nonneg x, Real.rpow_nonneg (norm_nonneg x) q]
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hq
    rw [Real.rpow_two] at hh
    linarith

theorem integrable_norm_sq_of_envelope_moment {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {q : ℝ} (hq : 2 ≤ q)
    (hmoment : Integrable (fun x : Vector p => ‖x‖ ^ q) μ) :
    Integrable (fun x : Vector p => ‖x‖ ^ 2) μ := by
  apply ((integrable_const (1 : ℝ)).add hmoment).mono'
    (measurable_norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all μ fun x => by
    simpa only [Real.norm_eq_abs, abs_sq] using norm_pow_two_le_one_add_rpow x hq

theorem integrable_coordinate_pair_of_envelope_moment {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {q : ℝ} (hq : 2 ≤ q)
    (hmoment : Integrable (fun x : Vector p => ‖x‖ ^ q) μ) (j k : Fin p) :
    Integrable (fun x : Vector p => x j * x k) μ := by
  apply (integrable_norm_sq_of_envelope_moment μ hq hmoment).mono'
    ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable
  exact ae_of_all μ fun x => by
    simpa only [norm_mul, pow_two] using
      mul_le_mul (norm_le_pi_norm x j) (norm_le_pi_norm x k) (norm_nonneg _) (norm_nonneg x)

/-- The moment input needed only for the Appendix E covariance estimates.
The polynomial CLT's separate coordinate-fourth condition is not discarded
by this helper contract; it is not needed to prove these covariance bounds. -/
structure ConditionalTruncationMomentHypotheses {p : ℕ}
    (μ : Measure (Vector p)) (B T q : ℝ) : Prop where
  B_pos : 0 < B
  threshold : 2 * B ≤ T
  q_gt_two : 2 < q
  integrable_q : Integrable (fun x : Vector p => ‖x‖ ^ q) μ
  moment_le : (∫ x : Vector p, ‖x‖ ^ q ∂μ) ≤ B ^ q
  centered : ∀ j, (∫ x : Vector p, x j ∂μ) = 0

namespace ConditionalTruncationMomentHypotheses

variable {p : ℕ} {μ : Measure (Vector p)} [IsProbabilityMeasure μ] {B T q : ℝ}

omit [IsProbabilityMeasure μ] in
theorem threshold_pos (h : ConditionalTruncationMomentHypotheses μ B T q) : 0 < T :=
  lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 2) h.B_pos) h.threshold

theorem bad_probability_lt_quarter (h : ConditionalTruncationMomentHypotheses μ B T q) :
    μ.real (goodTruncationSet T)ᶜ < 1 / 4 :=
  exceptional_probability_lt_quarter μ B T q h.B_pos h.threshold h.q_gt_two h.integrable_q h.moment_le

theorem good_mass_ne_zero (h : ConditionalTruncationMomentHypotheses μ B T q) :
    μ (goodTruncationSet T) ≠ 0 :=
  goodTruncation_mass_ne_zero_of_bad_probability_lt_one μ T
    (h.bad_probability_lt_quarter.trans (by norm_num))

theorem good_probability_ge_half (h : ConditionalTruncationMomentHypotheses μ B T q) :
    (1 / 2 : ℝ) ≤ μ.real (goodTruncationSet T) := by
  have hh := measureReal_add_measureReal_compl (μ := μ) (measurableSet_goodTruncationSet T)
  rw [measureReal_univ_eq_one] at hh
  linarith [h.bad_probability_lt_quarter]

theorem integrable_coordinate (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    Integrable (fun x : Vector p => x j) μ := by
  have hi := integrable_of_bennett_norm_moment (T := id) measurable_id
    (by linarith [h.q_gt_two] : 1 < q) h.integrable_q
  exact hi.norm.mono' (measurable_pi_apply j).aestronglyMeasurable
    (ae_of_all μ fun x => norm_le_pi_norm x j)

theorem integrable_coordinate_pair (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    Integrable (fun x : Vector p => x j * x k) μ :=
  integrable_coordinate_pair_of_envelope_moment μ h.q_gt_two.le h.integrable_q j k

theorem integrable_coordinate_sq (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    Integrable (fun x : Vector p => x j ^ 2) μ := by
  simpa only [pow_two] using h.integrable_coordinate_pair j j

/-- The conditional mean uses the original centered law and the actual
discarded expectation, divided by the nonzero good-event probability. -/
theorem mean_mul_good_probability (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    μ.real (goodTruncationSet T) * conditionalGoodMean μ T j =
      -(∫ x in (goodTruncationSet T)ᶜ, x j ∂μ) := by
  have he : conditionalGoodMean μ T j = (μ.real (goodTruncationSet T))⁻¹ *
      (∫ x in goodTruncationSet T, x j ∂μ) := by
    unfold conditionalGoodMean goodConditionalLaw
    rw [conditionalVectorLaw_eq_cond μ _ h.good_mass_ne_zero, ProbabilityTheory.cond,
      integral_smul_measure]
    simp only [ENNReal.toReal_inv, smul_eq_mul, Measure.real]
  have hp : μ.real (goodTruncationSet T) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h.good_probability_ge_half).ne'
  have hh := integral_add_compl (measurableSet_goodTruncationSet T) (h.integrable_coordinate j)
  rw [h.centered j] at hh
  rw [he]
  calc
    _ = ∫ x in goodTruncationSet T, x j ∂μ := by rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    _ = _ := by linarith

theorem abs_bad_coordinate_integral_le_norm_tail
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    |∫ x in (goodTruncationSet T)ᶜ, x j ∂μ| ≤
      ∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ∂μ := by
  have hi := integrable_of_bennett_norm_moment (T := id) measurable_id
    (by linarith [h.q_gt_two] : 1 < q) h.integrable_q
  exact abs_integral_le_integral_abs.trans
    (integral_mono (h.integrable_coordinate j).restrict.norm hi.norm.restrict
      (fun x => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j))

theorem norm_mean_le_polynomial_tail (h : ConditionalTruncationMomentHypotheses μ B T q) :
    ‖conditionalGoodMean μ T‖ ≤ 2 * B ^ q * T ^ (1 - q) := by
  have htail := integral_bad_norm_pow_le μ h.threshold_pos 1
    (by norm_num; linarith [h.q_gt_two]) h.integrable_q h.moment_le
  simp only [pow_one, Nat.cast_one] at htail
  have hnonneg : 0 ≤ B ^ q / T ^ (q - 1) :=
    div_nonneg (Real.rpow_nonneg h.B_pos.le _) (Real.rpow_nonneg h.threshold_pos.le _)
  have heq : 2 * B ^ q * T ^ (1 - q) = 2 * (B ^ q / T ^ (q - 1)) := by
    rw [show 1 - q = -(q - 1) by ring, Real.rpow_neg h.threshold_pos.le]
    ring
  rw [heq]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hm : μ.real (goodTruncationSet T) * |conditionalGoodMean μ T j| ≤
      B ^ q / T ^ (q - 1) := by
    calc
      _ = |μ.real (goodTruncationSet T) * conditionalGoodMean μ T j| := by
        rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      _ = |∫ x in (goodTruncationSet T)ᶜ, x j ∂μ| := by rw [h.mean_mul_good_probability j, abs_neg]
      _ ≤ _ := (h.abs_bad_coordinate_integral_le_norm_tail j).trans htail
  have hh := mul_le_mul_of_nonneg_right h.good_probability_ge_half
    (abs_nonneg (conditionalGoodMean μ T j))
  rw [Real.norm_eq_abs]
  linarith

theorem bad_coordinate_sq_integral_le (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    (∫ x in (goodTruncationSet T)ᶜ, x j ^ 2 ∂μ) ≤ truncationVarianceBudget B T q := by
  have hh : (∫ x in (goodTruncationSet T)ᶜ, x j ^ 2 ∂μ) ≤
      ∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ^ 2 ∂μ := by
    apply integral_mono (h.integrable_coordinate_sq j).restrict
      (integrable_norm_sq_of_envelope_moment μ h.q_gt_two.le h.integrable_q).restrict
    intro x
    have habs : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (x j)) habs
  exact hh.trans (integral_bad_norm_sq_le_varianceBudget μ h.threshold_pos h.q_gt_two h.integrable_q h.moment_le)

theorem mean_coordinate_sq_le_varianceBudget
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    conditionalGoodMean μ T j ^ 2 ≤ truncationVarianceBudget B T q := by
  have hv : 0 ≤ truncationVarianceBudget B T q :=
    mul_nonneg (Real.rpow_nonneg h.B_pos.le _) (Real.rpow_nonneg h.threshold_pos.le _)
  have hc := discarded_mean_sq_le_second_mul_probability
    (measurableSet_goodTruncationSet T).compl (h.integrable_coordinate j) (h.integrable_coordinate_sq j)
  simp_rw [integral_indicator (measurableSet_goodTruncationSet T).compl] at hc
  have hs : (μ.real (goodTruncationSet T)) ^ 2 * conditionalGoodMean μ T j ^ 2 =
      (∫ x in (goodTruncationSet T)ᶜ, x j ∂μ) ^ 2 := by
    rw [← mul_pow, h.mean_mul_good_probability j, neg_sq]
  have hprod : (μ.real (goodTruncationSet T)) ^ 2 * conditionalGoodMean μ T j ^ 2 ≤
      truncationVarianceBudget B T q * (1 / 4) := by
    rw [hs]
    exact hc.trans ((mul_le_mul_of_nonneg_right (h.bad_coordinate_sq_integral_le j) measureReal_nonneg).trans
      (mul_le_mul_of_nonneg_left h.bad_probability_lt_quarter.le hv))
  have hp2 : (1 / 4 : ℝ) ≤ (μ.real (goodTruncationSet T)) ^ 2 := by
    nlinarith [h.good_probability_ge_half]
  have hh := mul_le_mul_of_nonneg_right hp2 (sq_nonneg (conditionalGoodMean μ T j))
  linarith

omit [IsProbabilityMeasure μ] in
theorem varianceBudget_nonneg (h : ConditionalTruncationMomentHypotheses μ B T q) :
    0 ≤ truncationVarianceBudget B T q :=
  mul_nonneg (Real.rpow_nonneg h.B_pos.le _) (Real.rpow_nonneg h.threshold_pos.le _)

theorem bad_probability_mul_threshold_sq_le (h : ConditionalTruncationMomentHypotheses μ B T q) :
    μ.real (goodTruncationSet T)ᶜ * T ^ 2 ≤ truncationVarianceBudget B T q := by
  have hp := exceptional_probability_le_rpow μ B T q h.B_pos.le h.threshold_pos
    (by linarith [h.q_gt_two]) h.integrable_q h.moment_le
  calc
    _ ≤ (B / T) ^ q * T ^ 2 := mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = truncationVarianceBudget B T q := by
      rw [Real.div_rpow h.B_pos.le h.threshold_pos.le, truncationVarianceBudget,
        Real.rpow_sub h.threshold_pos, Real.rpow_two]
      ring

theorem abs_mean_coordinate_mul_le_varianceBudget
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |conditionalGoodMean μ T j * conditionalGoodMean μ T k| ≤ truncationVarianceBudget B T q := by
  rw [abs_mul]
  have hj := h.mean_coordinate_sq_le_varianceBudget j
  have hk := h.mean_coordinate_sq_le_varianceBudget k
  have hh := sq_nonneg (|conditionalGoodMean μ T j| - |conditionalGoodMean μ T k|)
  rw [sub_sq, sq_abs, sq_abs] at hh
  nlinarith

theorem abs_bad_coordinate_pair_integral_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ| ≤ truncationVarianceBudget B T q := by
  have hi2 := integrable_norm_sq_of_envelope_moment μ h.q_gt_two.le h.integrable_q
  have hh : |∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ| ≤
      ∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ^ 2 ∂μ := by
    apply abs_integral_le_integral_abs.trans
    apply integral_mono (h.integrable_coordinate_pair j k).restrict.norm hi2.restrict
    intro x
    simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
      mul_le_mul (norm_le_pi_norm x j) (norm_le_pi_norm x k) (norm_nonneg _) (norm_nonneg x)
  exact hh.trans (integral_bad_norm_sq_le_varianceBudget μ h.threshold_pos h.q_gt_two h.integrable_q h.moment_le)

theorem abs_good_covariance_le_threshold_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance (goodConditionalLaw μ T) id j k| ≤ 2 * T ^ 2 := by
  have hprod : |∫ x : Vector p, x j * x k ∂goodConditionalLaw μ T| ≤ T ^ 2 := by
    have hb : ∀ᵐ x ∂goodConditionalLaw μ T, ‖x j * x k‖ ≤ T ^ 2 := by
      filter_upwards [goodConditionalLaw_ae_norm_le μ h.threshold_pos.le] with x hx
      simpa only [norm_mul, pow_two] using mul_le_mul
        ((norm_le_pi_norm x j).trans hx) ((norm_le_pi_norm x k).trans hx)
          (norm_nonneg _) h.threshold_pos.le
    simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const hb
  have hj : |conditionalGoodMean μ T j| ≤ T := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (conditionalGoodMean μ T) j).trans (norm_conditionalGoodMean_le μ h.threshold_pos.le)
  have hk : |conditionalGoodMean μ T k| ≤ T := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (conditionalGoodMean μ T) k).trans (norm_conditionalGoodMean_le μ h.threshold_pos.le)
  have hmean : |conditionalGoodMean μ T j * conditionalGoodMean μ T k| ≤ T ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hj hk (abs_nonneg _) h.threshold_pos.le
  change |(∫ x : Vector p, x j * x k ∂goodConditionalLaw μ T) -
    conditionalGoodMean μ T j * conditionalGoodMean μ T k| ≤ _
  exact (abs_sub _ _).trans ((add_le_add hprod hmean).trans_eq (by ring))

theorem good_covariance_bias_identity
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    covariance (goodConditionalLaw μ T) id j k - covariance μ id j k =
      μ.real (goodTruncationSet T)ᶜ * covariance (goodConditionalLaw μ T) id j k -
      μ.real (goodTruncationSet T) * (conditionalGoodMean μ T j * conditionalGoodMean μ T k) -
      (∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ) := by
  have hf := goodConditional_covariance_restrict μ T h.good_mass_ne_zero j k
  have hp : μ.real (goodTruncationSet T) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h.good_probability_ge_half).ne'
  have hscaled : μ.real (goodTruncationSet T) * covariance (goodConditionalLaw μ T) id j k =
      (∫ x in goodTruncationSet T, x j * x k ∂μ) -
      μ.real (goodTruncationSet T) * (conditionalGoodMean μ T j * conditionalGoodMean μ T k) := by
    rw [hf]
    field_simp
  have hh := integral_add_compl (measurableSet_goodTruncationSet T) (h.integrable_coordinate_pair j k)
  have hCi : covariance μ id j k = ∫ x : Vector p, x j * x k ∂μ := by
    simp only [covariance, id_eq, h.centered, mul_zero, sub_zero]
  have hprob := measureReal_add_measureReal_compl (μ := μ) (measurableSet_goodTruncationSet T)
  rw [measureReal_univ_eq_one] at hprob
  have hprobC := congrArg (fun a => a * covariance (goodConditionalLaw μ T) id j k) hprob
  dsimp only at hprobC
  rw [hCi]
  nlinarith only [hscaled, hh, hprobC]

/-- A direct covariance-bias estimate with an absolute constant. The proof
uses the conditional `2*T²` support bound and the actual tail moments. -/
theorem abs_good_covariance_bias_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    |covariance (goodConditionalLaw μ T) id j k - covariance μ id j k| ≤
      4 * truncationVarianceBudget B T q := by
  rw [h.good_covariance_bias_identity j k]
  have hpT := h.bad_probability_mul_threshold_sq_le
  have hpmean := mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ)
    (s := goodTruncationSet T)) h.varianceBudget_nonneg
  calc
    _ ≤ |μ.real (goodTruncationSet T)ᶜ * covariance (goodConditionalLaw μ T) id j k| +
        |μ.real (goodTruncationSet T) * (conditionalGoodMean μ T j * conditionalGoodMean μ T k)| +
        |∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ μ.real (goodTruncationSet T)ᶜ * (2 * T ^ 2) +
        μ.real (goodTruncationSet T) * truncationVarianceBudget B T q + truncationVarianceBudget B T q := by
      simp only [abs_mul, abs_of_nonneg measureReal_nonneg]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (h.abs_good_covariance_le_threshold_sq j k) measureReal_nonneg)
        (mul_le_mul_of_nonneg_left
          (by simpa only [abs_mul] using h.abs_mean_coordinate_mul_le_varianceBudget j k) measureReal_nonneg))
        (h.abs_bad_coordinate_pair_integral_le j k)
    _ ≤ 4 * truncationVarianceBudget B T q := by nlinarith

theorem norm_mean_le_envelope_scale (h : ConditionalTruncationMomentHypotheses μ B T q) :
    ‖conditionalGoodMean μ T‖ ≤ B := by
  have hratioPos : 0 < B / T := div_pos h.B_pos h.threshold_pos
  have hratio : B / T ≤ (1 / 2 : ℝ) := (div_le_iff₀ h.threshold_pos).mpr (by linarith [h.threshold])
  have hpow := Real.rpow_le_rpow_of_exponent_ge hratioPos
    (hratio.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
    (by linarith [h.q_gt_two] : (1 : ℝ) ≤ q - 1)
  rw [Real.rpow_one] at hpow
  have hBexp : B ^ q = B * B ^ (q - 1) := by
    calc
      B ^ q = B ^ ((1 : ℝ) + (q - 1)) := by congr 1; ring
      _ = B ^ (1 : ℝ) * B ^ (q - 1) := Real.rpow_add h.B_pos _ _
      _ = _ := by rw [Real.rpow_one]
  have heq : 2 * B ^ q * T ^ (1 - q) = 2 * B * (B / T) ^ (q - 1) := by
    rw [show 1 - q = -(q - 1) by ring, Real.rpow_neg h.threshold_pos.le,
      Real.div_rpow h.B_pos.le h.threshold_pos.le, hBexp]
    ring
  calc
    _ ≤ 2 * B ^ q * T ^ (1 - q) := h.norm_mean_le_polynomial_tail
    _ = 2 * B * (B / T) ^ (q - 1) := heq
    _ ≤ 2 * B * (B / T) := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) h.B_pos.le)
    _ ≤ 2 * B * (1 / 2) := mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) h.B_pos.le)
    _ = B := by ring

omit [IsProbabilityMeasure μ] in
theorem exceptionalPart_coordinate_sq_identity
    (_h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) (x : Vector p) :
    conditionalExceptionalPart μ T x j ^ 2 =
      (goodTruncationSet T).indicator (fun _ => conditionalGoodMean μ T j ^ 2) x +
      (goodTruncationSet T)ᶜ.indicator (fun x : Vector p => x j ^ 2) x := by
  by_cases hx : ‖x‖ ≤ T <;> simp [conditionalExceptionalPart, goodTruncationSet, hx]

theorem integrable_exceptionalPart_coordinate_sq
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    Integrable (fun x : Vector p => conditionalExceptionalPart μ T x j ^ 2) μ := by
  simp_rw [h.exceptionalPart_coordinate_sq_identity j]
  exact ((integrable_const _).indicator (measurableSet_goodTruncationSet T)).add
    ((h.integrable_coordinate_sq j).indicator (measurableSet_goodTruncationSet T).compl)

theorem integral_exceptionalPart_coordinate_sq_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j : Fin p) :
    (∫ x : Vector p, conditionalExceptionalPart μ T x j ^ 2 ∂μ) ≤
      2 * truncationVarianceBudget B T q := by
  simp_rw [h.exceptionalPart_coordinate_sq_identity j]
  rw [integral_add ((integrable_const _).indicator (measurableSet_goodTruncationSet T))
    ((h.integrable_coordinate_sq j).indicator (measurableSet_goodTruncationSet T).compl),
    integral_indicator (measurableSet_goodTruncationSet T),
    integral_indicator (measurableSet_goodTruncationSet T).compl]
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hp := mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ) (s := goodTruncationSet T))
    h.varianceBudget_nonneg
  have hm := mul_le_mul_of_nonneg_left (h.mean_coordinate_sq_le_varianceBudget j)
    (measureReal_nonneg (μ := μ) (s := goodTruncationSet T))
  nlinarith [h.bad_coordinate_sq_integral_le j]

omit [IsProbabilityMeasure μ] in
theorem exceptionalPart_q_identity
    (_h : ConditionalTruncationMomentHypotheses μ B T q) (x : Vector p) :
    ‖conditionalExceptionalPart μ T x‖ ^ q =
      (goodTruncationSet T).indicator (fun _ => ‖conditionalGoodMean μ T‖ ^ q) x +
      (goodTruncationSet T)ᶜ.indicator (fun x : Vector p => ‖x‖ ^ q) x := by
  by_cases hx : ‖x‖ ≤ T <;> simp [conditionalExceptionalPart, goodTruncationSet, hx]

theorem integrable_exceptionalPart_q
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    Integrable (fun x : Vector p => ‖conditionalExceptionalPart μ T x‖ ^ q) μ := by
  simp_rw [h.exceptionalPart_q_identity]
  exact ((integrable_const _).indicator (measurableSet_goodTruncationSet T)).add
    (h.integrable_q.indicator (measurableSet_goodTruncationSet T).compl)

theorem integral_exceptionalPart_q_le
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    (∫ x : Vector p, ‖conditionalExceptionalPart μ T x‖ ^ q ∂μ) ≤ 2 * B ^ q := by
  have hmean : ‖conditionalGoodMean μ T‖ ^ q ≤ B ^ q :=
    Real.rpow_le_rpow (norm_nonneg _) h.norm_mean_le_envelope_scale (by linarith [h.q_gt_two])
  have htail : (∫ x in (goodTruncationSet T)ᶜ, ‖x‖ ^ q ∂μ) ≤ B ^ q :=
    (integral_mono_measure Measure.restrict_le_self
      (ae_of_all μ fun x : Vector p => Real.rpow_nonneg (norm_nonneg x) q) h.integrable_q).trans h.moment_le
  simp_rw [h.exceptionalPart_q_identity]
  rw [integral_add ((integrable_const _).indicator (measurableSet_goodTruncationSet T))
    (h.integrable_q.indicator (measurableSet_goodTruncationSet T).compl),
    integral_indicator (measurableSet_goodTruncationSet T),
    integral_indicator (measurableSet_goodTruncationSet T).compl]
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hp := mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ) (s := goodTruncationSet T))
    (Real.rpow_nonneg h.B_pos.le q)
  have hm := mul_le_mul_of_nonneg_left hmean (measureReal_nonneg (μ := μ) (s := goodTruncationSet T))
  nlinarith

end ConditionalTruncationMomentHypotheses

def conditionalCovarianceForMask {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (1 / (n : ℝ)) *
    ∑ i, if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k

def originalAverageCovariance {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (1 / (n : ℝ)) * ∑ i, covariance (μ i) id j k

def exceptionalCount {n : ℕ} (mask : Fin n → Bool) : ℝ :=
  ∑ i, if mask i then 1 else 0

theorem conditional_covariance_entry_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (mask : Fin n → Bool) (j k : Fin p) :
    |(conditionalCovarianceForMask μ T mask - originalAverageCovariance μ) j k| ≤
      4 * truncationVarianceBudget B T q + (2 * T ^ 2 / (n : ℝ)) * exceptionalCount mask := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint (i : Fin n) :
      |(if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k| ≤
        4 * truncationVarianceBudget B T q + 2 * T ^ 2 * (if mask i then 1 else 0) := by
    have he : (if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k =
        (covariance (goodConditionalLaw (μ i) T) id j k - covariance (μ i) id j k) -
          (if mask i then covariance (goodConditionalLaw (μ i) T) id j k else 0) := by
      split_ifs <;> ring
    rw [he]
    apply (abs_sub _ _).trans
    apply add_le_add ((h i).abs_good_covariance_bias_le j k)
    by_cases hi : mask i = true
    · simpa only [hi, if_true, mul_one] using (h i).abs_good_covariance_le_threshold_sq j k
    · have hi' : mask i = false := Bool.eq_false_iff.mpr hi
      simp only [hi', Bool.false_eq_true, if_false, abs_zero, mul_zero, le_refl]
  unfold conditionalCovarianceForMask originalAverageCovariance
  simp only [Matrix.sub_apply, ← mul_sub, ← Finset.sum_sub_distrib]
  calc
    _ = (1 / (n : ℝ)) * |∑ i,
      ((if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k)| := by
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hnR)]
    _ ≤ (1 / (n : ℝ)) * ∑ i,
      |(if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id j k) - covariance (μ i) id j k| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (one_div_pos.mpr hnR).le
    _ ≤ (1 / (n : ℝ)) * ∑ i,
      (4 * truncationVarianceBudget B T q + 2 * T ^ 2 * (if mask i then 1 else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpoint i) (one_div_pos.mpr hnR).le
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, exceptionalCount]
      field_simp
      ring

theorem conditional_covariance_max_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (mask : Fin n → Bool) :
    matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - originalAverageCovariance μ) ≤
      4 * truncationVarianceBudget B T q + (2 * T ^ 2 / (n : ℝ)) * exceptionalCount mask := by
  let i : Fin n := ⟨0, by omega⟩
  have hv := (h i).varianceBudget_nonneg
  have hcount : 0 ≤ exceptionalCount mask := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hnonneg : 0 ≤ 4 * truncationVarianceBudget B T q + (2 * T ^ 2 / (n : ℝ)) * exceptionalCount mask := by
    positivity
  unfold matrixMaxEntryNorm
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro k
  simpa only [Real.norm_eq_abs] using conditional_covariance_entry_deviation_le μ h hn mask j k

theorem vectorProduct_map_eval {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    (Measure.pi μ).map (fun x => x i) = μ i := by
  classical
  ext S hS
  rw [Measure.map_apply (measurable_pi_apply i) hS]
  have he : (fun x : Fin n → Vector p => x i) ⁻¹' S =
      Set.pi Set.univ (fun k => if k = i then S else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx k
      by_cases hk : k = i
      · subst k; simpa using hx
      · simp [hk]
    · intro hx
      simpa using hx i
  rw [he, Measure.pi_pi]
  simp [apply_ite, measure_univ]

theorem integral_observed_exceptional_indicator {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) (i : Fin n) :
    (∫ x, (if (observedTruncationMask T x) i then (1 : ℝ) else 0) ∂Measure.pi μ) =
      (μ i).real (goodTruncationSet T)ᶜ := by
  have hm : Measurable (fun x : Vector p => if ‖x‖ ≤ T then (0 : ℝ) else 1) :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_const measurable_const
  have he := integral_map (μ := Measure.pi μ) (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable
  rw [vectorProduct_map_eval] at he
  have hi : (fun x : Vector p => if ‖x‖ ≤ T then (0 : ℝ) else 1) =
      (goodTruncationSet T)ᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : ‖x‖ ≤ T <;> simp [goodTruncationSet, hx]
  have hz : (∫ x : Vector p, (if ‖x‖ ≤ T then (0 : ℝ) else 1) ∂μ i) =
      (μ i).real (goodTruncationSet T)ᶜ := by
    rw [hi, integral_indicator (measurableSet_goodTruncationSet T).compl]
    simp
  have hf (x : Fin n → Vector p) :
      (if (observedTruncationMask T x) i then (1 : ℝ) else 0) = if ‖x i‖ ≤ T then 0 else 1 := by
    by_cases hx : ‖x i‖ ≤ T <;> simp [observedTruncationMask, hx]
  simp_rw [hf]
  exact he.symm.trans hz

theorem integrable_observed_exceptional_indicator {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) (i : Fin n) :
    Integrable (fun x => if (observedTruncationMask T x) i then (1 : ℝ) else 0) (Measure.pi μ) := by
  have hm : Measurable (fun x : Fin n → Vector p => if (observedTruncationMask T x) i then (1 : ℝ) else 0) :=
    Measurable.ite (((measurable_pi_apply i).comp (measurable_observedTruncationMask T))
      (measurableSet_singleton true)) measurable_const measurable_const
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by split_ifs <;> norm_num

/-- The actual expected maximum-entry conditional covariance discrepancy.
No rank, eigenvalue, correlation-gap or coordinate-independence condition
appears; all observations may have different laws. -/
theorem expected_conditional_covariance_deviation_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    (∫ x, matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T (observedTruncationMask T x) - originalAverageCovariance μ)
      ∂Measure.pi μ) ≤ 6 * truncationVarianceBudget B T q := by
  let i : Fin n := ⟨0, by omega⟩
  have hv := (h i).varianceBudget_nonneg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let D : (Fin n → Vector p) → ℝ := fun x => matrixMaxEntryNorm
    (conditionalCovarianceForMask μ T (observedTruncationMask T x) - originalAverageCovariance μ)
  let R : (Fin n → Vector p) → ℝ := fun x =>
    4 * truncationVarianceBudget B T q + (2 * T ^ 2 / (n : ℝ)) * exceptionalCount (observedTruncationMask T x)
  have hR : Integrable R (Measure.pi μ) :=
    (integrable_const _).add ((integrable_finset_sum Finset.univ
      (fun i _ => integrable_observed_exceptional_indicator μ T i)).const_mul _)
  have hmD : Measurable D :=
    (measurable_of_countable (fun mask : Fin n → Bool =>
      matrixMaxEntryNorm (conditionalCovarianceForMask μ T mask - originalAverageCovariance μ))).comp
        (measurable_observedTruncationMask T)
  have hD : Integrable D (Measure.pi μ) := hR.mono' hmD.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ D x from norm_nonneg _)]
      exact conditional_covariance_max_deviation_le μ h hn _)
  have hs : (∑ i, (μ i).real (goodTruncationSet T)ᶜ * T ^ 2) ≤ (n : ℝ) * truncationVarianceBudget B T q := by
    calc
      _ ≤ ∑ _i : Fin n, truncationVarianceBudget B T q :=
        Finset.sum_le_sum (fun i _ => (h i).bad_probability_mul_threshold_sq_le)
      _ = _ := by simp
  have hcost : (2 * T ^ 2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ) ≤
      2 * truncationVarianceBudget B T q := by
    calc
      _ = (2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ * T ^ 2) := by
        simp only [← Finset.sum_mul]
        ring
      _ ≤ (2 / (n : ℝ)) * ((n : ℝ) * truncationVarianceBudget B T q) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp; ring
  calc
    (∫ x, D x ∂Measure.pi μ) ≤ ∫ x, R x ∂Measure.pi μ :=
      integral_mono hD hR (fun x => conditional_covariance_max_deviation_le μ h hn _)
    _ = 4 * truncationVarianceBudget B T q +
        (2 * T ^ 2 / (n : ℝ)) * (∑ i, (μ i).real (goodTruncationSet T)ᶜ) := by
      dsimp only [R, exceptionalCount]
      rw [integral_add (integrable_const _)
        ((integrable_finset_sum Finset.univ (fun i _ => integrable_observed_exceptional_indicator μ T i)).const_mul _)]
      simp only [integral_const_mul]
      rw [integral_finset_sum Finset.univ (fun i _ => integrable_observed_exceptional_indicator μ T i)]
      simp only [integral_const, measureReal_univ_eq_one, one_smul, integral_observed_exceptional_indicator]
    _ ≤ 6 * truncationVarianceBudget B T q := by linarith

theorem vectorProduct_independent {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] :
    iIndepFun (fun i (x : Fin n → Vector p) => x i) (Measure.pi μ) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  change (Measure.pi μ).map id = _
  rw [Measure.map_id]
  simp only [vectorProduct_map_eval]

/-- The reference matrix in the expected-discrepancy estimate is the
actual covariance of the normalized original product array. -/
theorem product_normalized_covariance_eq_average {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    covariance (Measure.pi μ) (normalizedObservationSum (fun i x => x i)) = originalAverageCovariance μ := by
  have hLp (i : Fin n) (j : Fin p) : MemLp (fun x : Fin n → Vector p => x i j) 2 (Measure.pi μ) := by
    have hs : Integrable (fun x : Vector p => x j ^ 2) ((Measure.pi μ).map (fun x => x i)) := by
      rw [vectorProduct_map_eval]
      exact (h i).integrable_coordinate_sq j
    have hi := (integrable_map_measure ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).mp hs
    have hm : Measurable (fun x : Fin n → Vector p => x i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  have hc (i : Fin n) (j : Fin p) : (∫ x : Fin n → Vector p, x i j ∂Measure.pi μ) = 0 := by
    have he := integral_map (μ := Measure.pi μ) (f := fun x : Vector p => x j)
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aestronglyMeasurable
    rw [vectorProduct_map_eval] at he
    exact he.symm.trans ((h i).centered j)
  have hsum : sumVector (sampleNormalizedObservations (fun i (x : Fin n → Vector p) => x i)) =
      normalizedObservationSum (fun i (x : Fin n → Vector p) => x i) := by
    funext x
    ext j
    simp only [sampleNormalizedObservations, normalizedObservationSum, sumVector, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  ext j k
  have hcov := covariance_sampleNormalizedObservations (vectorProduct_independent μ) hc hLp
    (by omega : 0 < n) j k
  rw [hsum] at hcov
  have hpair (i : Fin n) : (∫ x : Fin n → Vector p, x i j * x i k ∂Measure.pi μ) =
      covariance (μ i) id j k := by
    have he := integral_map (μ := Measure.pi μ) (f := fun x : Vector p => x j * x k)
      (measurable_pi_apply i).aemeasurable
      ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable
    rw [vectorProduct_map_eval] at he
    simpa only [covariance, id_eq, (h i).centered, mul_zero, sub_zero] using he.symm
  rw [hcov]
  simp only [hpair, originalAverageCovariance, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul]

theorem expected_conditional_covariance_deviation_actual {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    (∫ x, matrixMaxEntryNorm
      (conditionalCovarianceForMask μ T (observedTruncationMask T x) -
        covariance (Measure.pi μ) (normalizedObservationSum (fun i x => x i))) ∂Measure.pi μ) ≤
      6 * truncationVarianceBudget B T q := by
  rw [product_normalized_covariance_eq_average μ h hn]
  exact expected_conditional_covariance_deviation_le μ h hn

theorem conditionalExceptionalShift_observed {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (x : Fin n → Vector p) :
    conditionalExceptionalShift μ T (observedTruncationMask T x) (observedExceptionalArray T x) =
      fun i => conditionalExceptionalPart (μ i) T (x i) := by
  funext i
  by_cases hx : ‖x i‖ ≤ T <;>
    simp [conditionalExceptionalShift, observedTruncationMask, observedExceptionalArray,
      conditionalExceptionalPart, hx]

/-- Nonnegative reconstruction also applies to unbounded moment tests,
before genuine integrability is used to pass to real expectations. -/
theorem lintegral_product_eq_mask_bad_good {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : ℝ) (f : (Fin n → Vector p) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∑ mask : Fin n → Bool, truncationMaskWeight μ T mask *
        ∫⁻ b, ∫⁻ g, f (selectConditionalArrays mask (b, g))
          ∂conditionalGoodProductLaw μ T ∂badConditionalProduct μ T := by
  rw [productLaw_eq_truncationMaskMixture μ T]
  unfold truncationMaskMixture
  rw [lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [← conditionalArrays_select_law μ T mask,
    lintegral_map hf (measurable_selectConditionalArrays mask)]
  exact lintegral_prod _ (hf.comp (measurable_selectConditionalArrays mask)).aemeasurable

theorem lintegral_tagged_product_eq_mask_bad_good {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ)
    (F : TruncationTag p n × (Fin n → Vector p) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F ((observedTruncationMask T x, observedExceptionalArray T x), x) ∂Measure.pi μ) =
      ∑ mask : Fin n → Bool, truncationMaskWeight μ T mask *
        ∫⁻ b, ∫⁻ g, F ((mask, maskedExceptionalArray mask b), selectConditionalArrays mask (b, g))
          ∂conditionalGoodProductLaw μ T ∂badConditionalProduct μ T := by
  have hf : Measurable (fun x : Fin n → Vector p =>
      F ((observedTruncationMask T x, observedExceptionalArray T x), x)) :=
    hF.comp (((measurable_observedTruncationMask T).prodMk
      (measurable_observedExceptionalArray T)).prodMk measurable_id)
  rw [lintegral_product_eq_mask_bad_good μ T _ hf]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hw : truncationMaskWeight μ T mask = 0
  · simp only [hw, zero_mul]
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod (observed_selected_tag_ae μ T mask hw)] with b hb
    apply lintegral_congr_ae
    filter_upwards [hb] with g hg
    rw [hg]

end

end RectangleCLT.Companion.SplitV4
