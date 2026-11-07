import RectangleCLTCompanion.FourthIdentityFreshPairs
import RectangleCLTCompanion.SplitV4.SeedCalibration
import RectangleCLT.GaussianComparisonLaw
import Mathlib.MeasureTheory.Group.Convolution

/-!
# The calibrated interpolation with an actual independent Gaussian seed

The seed is supplied by a product probability law. Differentiation of the
seed average is justified by a uniform bound on the actual finite-mask
derivative. The arbitrary continuously differentiable amplitude version of
Lemma B.1 remains a separate statement.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem abs_selectorWeightDerivative_le {n : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (mask : Kane.Cube n) :
    |selectorWeightDerivative a b mask| ≤ (n : ℝ)*|b| := by
  unfold selectorWeightDerivative
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, |b| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, Finset.abs_prod]
      have hp : (∏ j ∈ Finset.univ.erase i, |if mask j then a else 1-a|) ≤ 1 := by
        apply Finset.prod_le_one
        · intro j _
          exact abs_nonneg _
        · intro j _
          split_ifs <;> rw [abs_of_nonneg (by linarith)] <;> linarith
      calc
        _ ≤ 1 * |if mask i then b else -b| :=
          mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ = |b| := by split_ifs <;> simp
    _ = _ := by simp

theorem abs_calibrated_probability_derivative_le {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : |(t-3)/(1+t)^3| ≤ 3 := by
  have hd : (0 : ℝ) < (1+t)^3 := by positivity
  rw [abs_div, abs_of_nonpos (by linarith : t-3 ≤ 0), abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hpow : (1 : ℝ) ≤ (1+t)^3 := one_le_pow₀ (by linarith)
  nlinarith

/-- The seed is independent of the original finite-selector interpolation
under this actual product-law convolution. -/
def seededInterpolationLaw {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε t : ℝ) : Measure (Vector p) :=
  Measure.conv (gaussianLaw (Real.sqrt ε • A)) (interpolationLaw μ ξ A t)

theorem gaussian_seed_conv {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    Measure.conv (gaussianLaw (Real.sqrt ε • A)) (gaussianLaw (Real.sqrt t • A)) =
      gaussianLaw (Real.sqrt (t+ε) • A) := by
  have hs (a : ℝ) (ha : 0 ≤ a) :
      (Real.sqrt a • A)*(Real.sqrt a • A).transpose = a • (A*A.transpose) := by
    have hh := interpolatedGaussian_covariance A ha
    change covariance (gaussianLaw (Real.sqrt a • A)) id = _ at hh
    rw [covariance_gaussianLaw] at hh
    exact hh
  have hcov : (Real.sqrt (t+ε) • A)*(Real.sqrt (t+ε) • A).transpose =
      (1 : ℝ)^2 • ((Real.sqrt ε • A)*(Real.sqrt ε • A).transpose) +
        (1 : ℝ)^2 • ((Real.sqrt t • A)*(Real.sqrt t • A).transpose) := by
    rw [hs (t+ε) (add_nonneg ht hε), hs ε hε, hs t ht]
    simp only [one_pow, one_smul, ← add_smul, add_comm]
  have he : gaussianScaledSum (p := p) 1 1 = (fun z => z.1+z.2) := by
    funext z
    simp only [gaussianScaledSum, one_smul]
  simpa only [Measure.conv, he] using
    gaussianLaw_scaled_sum (Real.sqrt ε • A) (Real.sqrt t • A) (Real.sqrt (t+ε) • A) 1 1 hcov

theorem interpolationLaw_eq_conv_arraySum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    interpolationLaw μ ξ A t = Measure.conv ((bernoulliArrayLaw μ ξ t).map arraySum)
      (gaussianLaw (Real.sqrt t • A)) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have hm : ((bernoulliArrayLaw μ ξ t).map arraySum).prod (gaussianLaw (Real.sqrt t • A)) =
      ((bernoulliArrayLaw μ ξ t).prod (gaussianLaw (Real.sqrt t • A))).map
        (Prod.map arraySum id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (bernoulliArrayLaw μ ξ t)
      (gaussianLaw (Real.sqrt t • A)) (measurable_arraySum p n) measurable_id
  rw [Measure.conv, hm, Measure.map_map (measurable_fst.add measurable_snd)
    ((measurable_arraySum p n).prodMap measurable_id)]
  rfl

/-- The actual seed and heat Gaussian combine to variance `t+ε`, while the
Bernoulli retention and amplitude still use `t`. -/
theorem seededInterpolationLaw_eq_shifted_heat
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    seededInterpolationLaw μ ξ A ε t =
      (((bernoulliArrayLaw μ ξ t).map arraySum).prod
        (gaussianLaw (Real.sqrt (t+ε) • A))).map (fun z => z.1+z.2) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  haveI : IsProbabilityMeasure ((bernoulliArrayLaw μ ξ t).map arraySum) :=
    isProbabilityMeasure_map (measurable_arraySum p n).aemeasurable
  unfold seededInterpolationLaw
  rw [interpolationLaw_eq_conv_arraySum μ ξ hξ A ht ht1, ← Measure.conv_assoc,
    Measure.conv_comm (gaussianLaw (Real.sqrt ε • A)) ((bernoulliArrayLaw μ ξ t).map arraySum),
    Measure.conv_assoc, gaussian_seed_conv A hε ht]
  rfl

theorem seededInterpolationLaw_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (seededInterpolationLaw μ ξ A ε t) := by
  letI := interpolationLaw_isProbability μ ξ hξ A t ht ht1
  exact isProbabilityMeasure_map (measurable_fst.add measurable_snd).aemeasurable

/-- Gaussian heat and an independent Gaussian seed combine under every
bounded continuous derivative kernel, with genuine product integrability. -/
theorem shiftIntegral_gaussian_seed {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ)
    (hb : ∀ y, ‖G y‖ ≤ C) (x : Vector p) :
    shiftIntegral (gaussianLaw (Real.sqrt (t+ε) • A)) G x =
      ∫ z, shiftIntegral (gaussianLaw (Real.sqrt t • A)) G (x+z)
        ∂gaussianLaw (Real.sqrt ε • A) := by
  have hm : Measurable (fun z : Vector p × Vector p => G (x+(z.1+z.2))) :=
    hG.measurable.comp (measurable_const.add (measurable_fst.add measurable_snd))
  have hi : Integrable (fun z : Vector p × Vector p => G (x+(z.1+z.2)))
      ((gaussianLaw (Real.sqrt ε • A)).prod (gaussianLaw (Real.sqrt t • A))) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun _ => hb _)
  unfold shiftIntegral
  rw [← gaussian_seed_conv A hε ht, Measure.conv,
    integral_map (f := fun y => G (x+y)) (measurable_fst.add measurable_snd).aemeasurable
      (hG.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable,
    integral_prod _ hi]
  simp only [add_assoc]

end
end RectangleCLT.Companion.SplitV4

namespace RectangleCLT.FaceSmoother
noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

def seededSelectorHeatExpectation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z, s.selectorHeatExpectation μ ξ A (x+z) t ∂gaussianLaw (Real.sqrt ε • A)

def seededSelectorHeatDerivative {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z, s.selectorHeatDerivative μ ξ A (x+z) t ∂gaussianLaw (Real.sqrt ε • A)

theorem measurable_heatShiftExpectation_x
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) (hζ : Measurable ζ)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Measurable (fun x => s.heatShiftExpectation μ ζ A x t) := by
  unfold heatShiftExpectation
  simp_rw [s.gaussianHeat_eq_convolution]
  have hm : Measurable (fun z : Vector p × Ω =>
      s.convolution (gaussianLaw (Real.sqrt t • A)) (z.1 + thinningScale t • ζ z.2)) :=
    (s.continuous_convolution _).measurable.comp
      (measurable_fst.add (measurable_const.smul (hζ.comp measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_heatShiftDerivative_x
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) (hζ : Measurable ζ)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Measurable (fun x => s.heatShiftDerivative μ ζ A x t) := by
  have hm : Measurable (fun z : Vector p × Ω =>
      (∑ j, ζ z.2 j * s.convolutionFirstDerivative (gaussianLaw (Real.sqrt t • A))
        (z.1 + thinningScale t • ζ z.2) j) +
      (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
        s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A))
          (z.1 + thinningScale t • ζ z.2) j k) := by
    have hx : Measurable (fun z : Vector p × Ω => z.1 + thinningScale t • ζ z.2) :=
      measurable_fst.add (measurable_const.smul (hζ.comp measurable_snd))
    apply Measurable.add
    · exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp (hζ.comp measurable_snd)).mul
          ((s.continuous_convolutionFirstDerivative _ j).measurable.comp hx)
    · apply Measurable.const_mul
      exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
        ((s.continuous_convolutionSecondDerivative _ j k).measurable.comp hx).const_mul _
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def seedDominationHeatConstant (A : Matrix (Fin p) (Fin p) ℝ) (δ : ℝ) : ℝ :=
  (p : ℝ)*(δ*(1/s.bandwidth)) + (1/2 : ℝ)*
    ∑ j, ∑ k, |(A*A.transpose) j k| * (3/s.bandwidth^2)

theorem norm_heatShiftDerivative_le_seedDominationHeatConstant
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ζ ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    ‖s.heatShiftDerivative μ ζ A x t‖ ≤ s.seedDominationHeatConstant A δ := by
  unfold heatShiftDerivative
  apply (norm_integral_le_of_norm_le_const (μ := μ) (C := s.seedDominationHeatConstant A δ) ?_).trans_eq (by simp)
  filter_upwards [hbound] with ω hω
  unfold seedDominationHeatConstant
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin p, δ*(1/s.bandwidth) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (ζ ω) j).trans hω)
          (s.norm_convolutionFirstDerivative_le _ _ j) (norm_nonneg _) hδ
      _ = _ := by simp
  · rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (s.norm_convolutionSecondDerivative_le _ _ j k) (abs_nonneg _)

theorem norm_heatShiftExpectation_le_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    ‖s.heatShiftExpectation μ ζ A x t‖ ≤ 1 := by
  unfold heatShiftExpectation
  apply (norm_integral_le_of_norm_le_const (μ := μ) (C := (1 : ℝ)) ?_).trans_eq (by simp)
  exact ae_of_all _ fun ω => by
    rw [s.gaussianHeat_eq_convolution]
    exact s.norm_convolution_le_one _ _

theorem measurable_selectorHeatExpectation_x
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Measurable (fun x => s.selectorHeatExpectation μ ξ A x t) :=
  Finset.measurable_sum _ fun mask _ =>
    (s.measurable_heatShiftExpectation_x μ _ (measurable_maskObservationSum ξ hξ mask) A t).const_mul _

theorem measurable_selectorHeatDerivative_x
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Measurable (fun x => s.selectorHeatDerivative μ ξ A x t) :=
  Finset.measurable_sum _ fun mask _ =>
    ((s.measurable_heatShiftExpectation_x μ _ (measurable_maskObservationSum ξ hξ mask) A t).const_mul _).add
      ((s.measurable_heatShiftDerivative_x μ _ (measurable_maskObservationSum ξ hξ mask) A t).const_mul _)

theorem norm_selectorHeatExpectation_le_one
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖s.selectorHeatExpectation μ ξ A x t‖ ≤ 1 := by
  unfold selectorHeatExpectation
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask := by
      apply Finset.sum_le_sum
      intro mask _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Kane.maskWeight_nonneg
        (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)]
      exact mul_le_of_le_one_right (Kane.maskWeight_nonneg
        (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
        (s.norm_heatShiftExpectation_le_one μ _ A x t)
    _ = 1 := Kane.maskWeight_sum _

def seedDominationConstant (n : ℕ) (A : Matrix (Fin p) (Fin p) ℝ) (δ : ℝ) : ℝ :=
  (Fintype.card (Kane.Cube n) : ℝ) *
    (3*(n : ℝ) + s.seedDominationHeatConstant A ((n : ℝ)*δ))

theorem norm_selectorHeatDerivative_le_seedDominationConstant
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖s.selectorHeatDerivative μ ξ A x t‖ ≤ s.seedDominationConstant n A δ := by
  have hq := thinningProbability_nonneg ht1
  have hq1 := thinningProbability_le_one ht
  unfold selectorHeatDerivative
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _mask : Kane.Cube n,
        (3*(n : ℝ) + s.seedDominationHeatConstant A ((n : ℝ)*δ)) := by
      apply Finset.sum_le_sum
      intro mask _
      apply (norm_add_le _ _).trans
      apply add_le_add
      · rw [norm_mul, Real.norm_eq_abs]
        apply (mul_le_mul_of_nonneg_left
          (s.norm_heatShiftExpectation_le_one μ _ A x t) (abs_nonneg _)).trans
        rw [mul_one]
        exact (Companion.SplitV4.abs_selectorWeightDerivative_le hq hq1 mask).trans
          (by have hb := Companion.SplitV4.abs_calibrated_probability_derivative_le ht ht1
              have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
              nlinarith)
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Kane.maskWeight_nonneg hq hq1 mask)]
        have hw : Kane.maskWeight (thinningProbability t) mask ≤ 1 := by
          rw [← Kane.maskWeight_sum (thinningProbability t)]
          exact Finset.single_le_sum (fun a _ => Kane.maskWeight_nonneg hq hq1 a) (Finset.mem_univ mask)
        calc
          _ ≤ 1 * ‖s.heatShiftDerivative μ (maskObservationSum ξ mask) A x t‖ :=
            mul_le_mul_of_nonneg_right hw (norm_nonneg _)
          _ ≤ _ := by
            rw [one_mul]
            exact s.norm_heatShiftDerivative_le_seedDominationHeatConstant μ _
              (mul_nonneg (Nat.cast_nonneg _) hδ) (maskObservationSum_bounded μ ξ hδ hbound mask) A x t
    _ = _ := by simp [seedDominationConstant]; ring

theorem hasDerivAt_seededSelectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (s.seededSelectorHeatExpectation μ ξ A ε x)
      (s.seededSelectorHeatDerivative μ ξ A ε x t) t := by
  let radius := min t (1-t) / 2
  have hr : 0 < radius := by dsimp [radius]; exact div_pos (lt_min ht (by linarith)) (by norm_num)
  have htime {r : ℝ} (hrb : r ∈ Metric.ball t radius) : 0 < r ∧ r < 1 := by
    have hh : |r-t| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using hrb
    have hrt : radius ≤ t/2 := by dsimp [radius]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hr1 : radius ≤ (1-t)/2 := by dsimp [radius]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    constructor <;> linarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
  have hF (r : ℝ) : AEStronglyMeasurable
      (fun z => s.selectorHeatExpectation μ ξ A (x+z) r) (gaussianLaw (Real.sqrt ε • A)) :=
    ((s.measurable_selectorHeatExpectation_x μ ξ hξ A r).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
  have hD (r : ℝ) : AEStronglyMeasurable
      (fun z => s.selectorHeatDerivative μ ξ A (x+z) r) (gaussianLaw (Real.sqrt ε • A)) :=
    ((s.measurable_selectorHeatDerivative_x μ ξ hξ A r).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianLaw (Real.sqrt ε • A)) (ε := radius)
    (bound := fun _ : Vector p => s.seedDominationConstant n A δ)
    (F := fun r z => s.selectorHeatExpectation μ ξ A (x+z) r)
    (F' := fun r z => s.selectorHeatDerivative μ ξ A (x+z) r)
    (x₀ := t) hr (Filter.Eventually.of_forall hF)
    ((integrable_const (1 : ℝ)).mono' (hF t)
      (ae_of_all _ fun z => s.norm_selectorHeatExpectation_le_one μ ξ A (x+z) ht.le ht1.le))
    (hD t)
    (ae_of_all _ fun z r hrb => s.norm_selectorHeatDerivative_le_seedDominationConstant
      μ ξ hδ hbound A (x+z) (htime hrb).1.le (htime hrb).2.le)
    (integrable_const _)
    (ae_of_all _ fun z r hrb => s.hasDerivAt_selectorHeatExpectation μ ξ hξ hδ hbound A (x+z)
      (htime hrb).1)
  exact hd.2

theorem integral_interpolationLaw_translate_eq_selectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ y, s.F (x+y) ∂interpolationLaw μ ξ A t) =
      s.selectorHeatExpectation μ ξ A x t := by
  let ν := gaussianLaw (Real.sqrt t • A)
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have hm : Measurable (fun a : (Fin n → Vector p) × Vector p =>
      s.F (x+interpolationSum a)) :=
    s.continuous_F.measurable.comp (measurable_const.add (measurable_interpolationSum p n))
  have hi : Integrable (fun a : (Fin n → Vector p) × Vector p =>
      s.F (x+interpolationSum a)) ((bernoulliArrayLaw μ ξ t).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => s.norm_F_le_one _)
  unfold interpolationLaw
  rw [integral_map (f := fun y => s.F (x+y)) (measurable_interpolationSum p n).aemeasurable
    (s.continuous_F.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable]
  change (∫ a, s.F (x+interpolationSum a) ∂(bernoulliArrayLaw μ ξ t).prod ν) = _
  rw [integral_prod _ hi]
  have hinner (b : Fin n → Vector p) :
      (∫ y, s.F (x+interpolationSum (b,y)) ∂ν) = s.convolution ν (x+arraySum b) := by
    unfold convolution shiftIntegral interpolationSum
    simp only [add_assoc]
  simp_rw [hinner]
  have hmg : Measurable (fun b : Fin n → Vector p => s.convolution ν (x+arraySum b)) :=
    (s.continuous_convolution ν).measurable.comp (measurable_const.add (measurable_arraySum p n))
  have hig (mask : Kane.Cube n) : Integrable
      (fun b : Fin n → Vector p => s.convolution ν (x+arraySum b))
      (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact (integrable_const (1 : ℝ)).mono' hmg.aestronglyMeasurable
      (ae_of_all _ fun _ => s.norm_convolution_le_one ν _)
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _ hig]
  unfold selectorHeatExpectation
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hmg.aestronglyMeasurable]
  unfold heatShiftExpectation
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  change s.convolution ν (x+arraySum (retainedArray ξ t mask ω)) =
    s.gaussianHeat A (x+thinningScale t • maskObservationSum ξ mask ω) t
  rw [s.gaussianHeat_eq_convolution]
  have heq : arraySum (retainedArray ξ t mask ω) =
      thinningScale t • maskObservationSum ξ mask ω := by
    unfold arraySum maskObservationSum
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases hi : mask i <;> simp [retainedArray, hi]
  rw [heq]

theorem integral_seededInterpolationLaw_eq_seededSelectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    (ε : ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ y, s.F (x+y) ∂Companion.SplitV4.seededInterpolationLaw μ ξ A ε t) =
      s.seededSelectorHeatExpectation μ ξ A ε x t := by
  letI := interpolationLaw_isProbability μ ξ hξ A t ht ht1
  have hm : Measurable (fun z : Vector p × Vector p => s.F (x+(z.1+z.2))) :=
    s.continuous_F.measurable.comp (measurable_const.add (measurable_fst.add measurable_snd))
  have hi : Integrable (fun z : Vector p × Vector p => s.F (x+(z.1+z.2)))
      ((gaussianLaw (Real.sqrt ε • A)).prod (interpolationLaw μ ξ A t)) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => s.norm_F_le_one _)
  unfold Companion.SplitV4.seededInterpolationLaw Measure.conv
  rw [integral_map (f := fun y => s.F (x+y)) (measurable_fst.add measurable_snd).aemeasurable
    (s.continuous_F.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable,
    integral_prod _ hi]
  simp_rw [← add_assoc,
    s.integral_interpolationLaw_translate_eq_selectorHeatExpectation μ ξ hξ A _ ht ht1]
  rfl

theorem seededSelectorHeatDerivative_eq_fourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ε : ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.seededSelectorHeatDerivative μ ξ A ε x t =
      ∫ z, -(t/3)*s.signedCubicPathTerm μ ξ A (x+z) t +
        (s.selectorFourthA (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
         s.selectorFourthB (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
         s.selectorFourthC (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t)
        ∂gaussianLaw (Real.sqrt ε • A) := by
  apply integral_congr_ae
  exact ae_of_all _ fun z => s.selectorHeatDerivative_eq_fourthTerms μ ξ h A hA (x+z) ht

theorem hasDerivAt_integral_seededInterpolationLaw_fourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ε : ℝ) (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => ∫ y, s.F (x+y) ∂Companion.SplitV4.seededInterpolationLaw μ ξ A ε r)
      (∫ z, -(t/3)*s.signedCubicPathTerm μ ξ A (x+z) t +
        (s.selectorFourthA (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
         s.selectorFourthB (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
         s.selectorFourthC (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t)
        ∂gaussianLaw (Real.sqrt ε • A)) t := by
  rw [← s.seededSelectorHeatDerivative_eq_fourthTerms μ ξ h A hA ε x ht.le]
  apply (s.hasDerivAt_seededSelectorHeatExpectation μ ξ h.measurable h.delta_nonneg
    h.bounded A ε x ht ht1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with r hr
  exact s.integral_seededInterpolationLaw_eq_seededSelectorHeatExpectation μ ξ h.measurable A ε x hr.1.le hr.2.le

theorem integrable_seededSelectorHeatDerivative
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun z => s.selectorHeatDerivative μ ξ A (x+z) t)
      (gaussianLaw (Real.sqrt ε • A)) :=
  (integrable_const (s.seedDominationConstant n A δ)).mono'
    (((s.measurable_selectorHeatDerivative_x μ ξ hξ A t).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun z => s.norm_selectorHeatDerivative_le_seedDominationConstant
      μ ξ hδ hbound A (x+z) ht ht1)

theorem integrable_seededFourthTerms
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ε : ℝ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun z => -(t/3)*s.signedCubicPathTerm μ ξ A (x+z) t +
      (s.selectorFourthA (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
       s.selectorFourthB (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t +
       s.selectorFourthC (gaussianLaw (Real.sqrt t • A)) μ ξ (x+z) t))
      (gaussianLaw (Real.sqrt ε • A)) :=
  (s.integrable_seededSelectorHeatDerivative μ ξ h.measurable h.delta_nonneg h.bounded A ε x ht ht1).congr
    (ae_of_all _ fun z => s.selectorHeatDerivative_eq_fourthTerms μ ξ h A hA (x+z) ht)

theorem convolutionFirstDerivative_gaussian_seed
    (A : Matrix (Fin p) (Fin p) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (x : Vector p) (j : Fin p) :
    s.convolutionFirstDerivative (gaussianLaw (Real.sqrt (t+ε) • A)) x j =
      ∫ z, s.convolutionFirstDerivative (gaussianLaw (Real.sqrt t • A)) (x+z) j
        ∂gaussianLaw (Real.sqrt ε • A) := by
  simp_rw [s.convolutionFirstDerivative_eq_integral]
  exact Companion.SplitV4.shiftIntegral_gaussian_seed A hε ht _
    (s.continuous_firstDerivative j) _ (fun y => s.norm_firstDerivative_le y j) x

theorem convolutionSecondDerivative_gaussian_seed
    (A : Matrix (Fin p) (Fin p) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (x : Vector p) (j k : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw (Real.sqrt (t+ε) • A)) x j k =
      ∫ z, s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A)) (x+z) j k
        ∂gaussianLaw (Real.sqrt ε • A) := by
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  exact Companion.SplitV4.shiftIntegral_gaussian_seed A hε ht _
    (s.continuous_secondDerivative j k) _ (fun y => s.norm_secondDerivative_le y j k) x

theorem convolutionThirdDerivative_gaussian_seed
    (A : Matrix (Fin p) (Fin p) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw (Real.sqrt (t+ε) • A)) x j k l =
      ∫ z, s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) (x+z) j k l
        ∂gaussianLaw (Real.sqrt ε • A) := by
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact Companion.SplitV4.shiftIntegral_gaussian_seed A hε ht _
    (s.continuous_thirdDerivative j k l) _ (fun y => s.norm_thirdDerivative_le y j k l) x

theorem convolutionFourthDerivative_gaussian_seed
    (A : Matrix (Fin p) (Fin p) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw (Real.sqrt (t+ε) • A)) x j k l m =
      ∫ z, s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x+z) j k l m
        ∂gaussianLaw (Real.sqrt ε • A) := by
  simp_rw [s.convolutionFourthDerivative_eq_integral]
  exact Companion.SplitV4.shiftIntegral_gaussian_seed A hε ht _
    (s.continuous_fourthDerivative j k l m) _ (fun y => s.norm_fourthDerivative_le y j k l m) x

end
end RectangleCLT.FaceSmoother
