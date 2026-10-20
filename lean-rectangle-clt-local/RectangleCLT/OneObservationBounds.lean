import RectangleCLT.BernoulliComparison
import RectangleCLT.MomentProducts

/-! Actual one-observation Taylor remainder bounds with coordinate fourth
moments. Local envelopes concern derivatives of the convolution itself. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable def fourthTensorProduct {p : ℕ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (y : Vector p) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m|

theorem fourthTensorProduct_nonneg {p : ℕ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hH : ∀ j k l m, 0 ≤ H j k l m)
    (y : Vector p) : 0 ≤ fourthTensorProduct H y := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  exact Finset.sum_nonneg fun m _ => mul_nonneg (hH j k l m) (abs_nonneg _)

theorem fourthTensorProduct_smul {p : ℕ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (y : Vector p) (a : ℝ) :
    fourthTensorProduct H (a • y) = |a| ^ 4 * fourthTensorProduct H y := by
  have hp (j k l m : Fin p) : H j k l m *
      |(a • y) j * (a • y) k * (a • y) l * (a • y) m| =
        |a| ^ 4 * (H j k l m * |y j * y k * y l * y m|) := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    ring
  unfold fourthTensorProduct
  simp_rw [hp, ← Finset.mul_sum]

noncomputable def fourthTensorMoment {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (ξ : Ω → Vector p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * (∫ ω, |ξ ω j * ξ ω k * ξ ω l * ξ ω m| ∂μ)

theorem integrable_fourthTensorProduct {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Vector p) (hξ : Measurable ξ)
    {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) :
    Integrable (fun ω => fourthTensorProduct H (ξ ω)) μ := by
  unfold fourthTensorProduct
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have hi : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l * ξ ω m) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l, m] : Fin 4 → Fin p)
  exact hi.abs.const_mul _

theorem integral_fourthTensorProduct {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Vector p) (hξ : Measurable ξ)
    {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) :
    (∫ ω, fourthTensorProduct H (ξ ω) ∂μ) = fourthTensorMoment μ ξ H := by
  have hi (j k l m : Fin p) :
      Integrable (fun ω => H j k l m * |ξ ω j * ξ ω k * ξ ω l * ξ ω m|) μ := by
    have hp : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l * ξ ω m) μ := by
      simpa [Fin.prod_univ_succ, mul_assoc] using
        integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l, m] : Fin 4 → Fin p)
    exact hp.abs.const_mul _
  unfold fourthTensorProduct fourthTensorMoment
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => integrable_finset_sum Finset.univ
      (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ
    (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finset_sum Finset.univ
    (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m))]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finset_sum Finset.univ (fun m _ => hi j k l m)]
  simp only [integral_const_mul]

theorem sum_fourthTensorMoment_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hH : ∀ j k l m, 0 ≤ H j k l m) :
    (∑ i, fourthTensorMoment μ (ξ i) H) ≤
      gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m) := by
  have heq : (∑ i, fourthTensorMoment μ (ξ i) H) =
      ∑ j, ∑ k, ∑ l, ∑ m, H j k l m *
        (∑ i, ∫ ω, |ξ i ω j * ξ i ω k * ξ i ω l * ξ i ω m| ∂μ) := by
    unfold fourthTensorMoment
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * gamma4 μ ξ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
        (summed_abs_fourth_product_le_gamma4 μ ξ hξ hδ hbound j k l m) (hH j k l m)
    _ = _ := by simp only [← Finset.sum_mul]; ring

private theorem abs_integral_le_of_ae_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ g ω) : |∫ ω, f ω ∂μ| ≤ ∫ ω, g ω ∂μ :=
  abs_integral_le_integral_abs.trans (integral_mono_ae hf.abs hg hb)

private theorem abs_integral_sub_const_le_of_linear_remainder
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A L K : Ω → ℝ) (B : ℝ) (hiA : Integrable A μ) (hiL : Integrable L μ)
    (hiK : Integrable K μ) (hL : (∫ ω, L ω ∂μ) = 0)
    (hb : ∀ᵐ ω ∂μ, |A ω - (B + L ω)| ≤ K ω) :
    |(∫ ω, A ω ∂μ) - B| ≤ ∫ ω, K ω ∂μ := by
  have hh := abs_integral_le_of_ae_bound μ (fun ω => A ω - (B + L ω)) K
    (hiA.sub ((integrable_const B).add hiL)) hiK hb
  rw [integral_sub (f := A) (g := fun ω => B + L ω) hiA ((integrable_const B).add hiL),
    integral_add (f := fun _ => B) (g := L) (integrable_const B) hiL, hL] at hh
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, add_zero] using hh

noncomputable def fourthCoordinateMoment {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (ξ : Ω → Vector p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, H j k l m *
    (((∫ ω, ξ ω j ^ 4 ∂μ) + (∫ ω, ξ ω k ^ 4 ∂μ) +
      (∫ ω, ξ ω l ^ 4 ∂μ) + (∫ ω, ξ ω m ^ 4 ∂μ)) / 4)

theorem fourthCoordinateMoment_nonneg {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (ξ : Ω → Vector p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hH : ∀ j k l m, 0 ≤ H j k l m) :
    0 ≤ fourthCoordinateMoment μ ξ H := by
  have hp (j : Fin p) : 0 ≤ ∫ ω, ξ ω j ^ 4 ∂μ := integral_nonneg (fun ω => by positivity)
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  exact Finset.sum_nonneg fun m _ => mul_nonneg (hH j k l m)
    (div_nonneg (add_nonneg (add_nonneg (add_nonneg (hp j) (hp k)) (hp l)) (hp m)) (by norm_num))

theorem sum_fourthCoordinateMoment_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hH : ∀ j k l m, 0 ≤ H j k l m) :
    (∑ i, fourthCoordinateMoment μ (ξ i) H) ≤
      gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m) := by
  have heq : (∑ i, fourthCoordinateMoment μ (ξ i) H) =
      ∑ j, ∑ k, ∑ l, ∑ m, H j k l m *
        (((∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) + (∑ i, ∫ ω, ξ i ω k ^ 4 ∂μ) +
          (∑ i, ∫ ω, ξ i ω l ^ 4 ∂μ) + (∑ i, ∫ ω, ξ i ω m ^ 4 ∂μ)) / 4) := by
    unfold fourthCoordinateMoment
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [heq]
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * gamma4 μ ξ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_left _ (hH j k l m)
      linarith only [coordinate_fourth_sum_le_gamma4 μ ξ j,
        coordinate_fourth_sum_le_gamma4 μ ξ k, coordinate_fourth_sum_le_gamma4 μ ξ l,
        coordinate_fourth_sum_le_gamma4 μ ξ m]
    _ = _ := by simp only [← Finset.sum_mul]; ring

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- The concrete residual in the one-observation Bernoulli derivative is
bounded by fourth coordinate products. No approximation estimate is assumed. -/
theorem abs_oneObservationTaylorResidual_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ 2 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.oneObservationTaylorResidual ν μ ξ x t| ≤ 4 * fourthTensorMoment μ ξ H := by
  let a := thinningScale t
  have ha0 : 0 ≤ a := (thinningScale_pos ht).le
  have ha2 : a ≤ 2 := thinningScale_le_two ht1
  have haabs : |a| = a := abs_of_nonneg ha0
  have hH0 (j k l m : Fin p) : 0 ≤ H j k l m := by
    have hz : ‖(0 : Vector p)‖ ≤ 2 * δ := by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ
    have hh := hH (0 : Vector p) hz j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  let T : Ω → ℝ := fun ω => fourthTensorProduct H (ξ ω)
  have hT0 (ω : Ω) : 0 ≤ T ω := fourthTensorProduct_nonneg H hH0 (ξ ω)
  have hiT : Integrable T μ := integrable_fourthTensorProduct μ ξ hξ hbound H
  let A0 : Ω → ℝ := fun ω => s.convolution ν (line x (ξ ω) a)
  let B0 : Ω → ℝ := fun ω => s.convolutionTaylor3 ν x (a • ξ ω)
  let A1 : Ω → ℝ := fun ω => s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω)
  let B1 : Ω → ℝ := fun ω => s.convolutionGradientTaylor2 ν x (ξ ω) a
  have hline : Measurable (fun ω => line x (ξ ω) a) := by
    change Measurable (fun ω => x + a • ξ ω)
    exact measurable_const.add (measurable_const.smul hξ)
  have hiA0 : Integrable A0 μ := (integrable_const (1 : ℝ)).mono'
    (((s.continuous_convolution ν).measurable.comp hline).aestronglyMeasurable)
    (ae_of_all μ (fun ω => s.norm_convolution_le_one ν _))
  have hiD1 := s.integrable_convolutionTranslationD1_observation ν μ ξ hξ hbound x
  have hiD2 := s.integrable_convolutionTranslationD2_observation ν μ ξ hξ hbound x
  have hiD3 := s.integrable_convolutionTranslationD3_observation ν μ ξ hξ hbound x
  have hiB0 : Integrable B0 μ := by
    dsimp [B0]
    simp_rw [convolutionTaylor3, s.convolutionTranslationD1_smul,
      s.convolutionTranslationD2_smul, s.convolutionTranslationD3_smul]
    exact (((integrable_const _).add (hiD1.const_mul a)).add
      ((hiD2.const_mul (a ^ 2)).div_const 2)).add ((hiD3.const_mul (a ^ 3)).div_const 6)
  have hiB1 : Integrable B1 μ :=
    (hiD1.add (hiD2.const_mul a)).add ((hiD3.const_mul (a ^ 2)).div_const 2)
  have hiA1 : Integrable A1 μ := by
    unfold A1 convolutionTranslationD1
    apply integrable_finset_sum
    intro j _
    apply (integrable_const (δ * (1 / s.bandwidth))).mono'
    · exact (((s.continuous_convolutionFirstDerivative ν j).measurable.comp hline).mul
        ((measurable_pi_apply j).comp hξ)).aestronglyMeasurable
    · filter_upwards [hbound] with ω hω
      rw [norm_mul, Real.norm_eq_abs]
      have hh : ‖s.convolutionFirstDerivative ν (line x (ξ ω) a) j‖ * ‖ξ ω j‖ ≤
          (1 / s.bandwidth) * δ := mul_le_mul (s.norm_convolutionFirstDerivative_le ν _ j)
        ((norm_le_pi_norm (ξ ω) j).trans hω) (norm_nonneg _) (div_pos (by norm_num) s.bandwidth_pos).le
      simpa only [mul_comm, Real.norm_eq_abs] using hh
  have hscale (ω : Ω) (hω : ‖ξ ω‖ ≤ δ) : ‖a • ξ ω‖ ≤ 2 * δ := by
    rw [norm_smul, Real.norm_eq_abs, haabs]
    exact mul_le_mul ha2 hω (norm_nonneg _) (by norm_num)
  have hR0 : |∫ ω, A0 ω - B0 ω ∂μ| ≤ (16 / 24 : ℝ) * ∫ ω, T ω ∂μ := by
    have hp : ∀ᵐ ω ∂μ, |A0 ω - B0 ω| ≤ (16 / 24 : ℝ) * T ω := by
      filter_upwards [hbound] with ω hω
      have hh := s.abs_convolutionTaylor3_remainder_le_tensor_direct ν x (a • ξ ω) H
        (hscale ω hω) hH
      change |s.convolution ν (x + a • ξ ω) - s.convolutionTaylor3 ν x (a • ξ ω)| ≤
        (16 / 24 : ℝ) * T ω
      change _ ≤ fourthTensorProduct H (a • ξ ω) / 24 at hh
      rw [fourthTensorProduct_smul, haabs] at hh
      have ha4 : a ^ 4 ≤ 16 := by
        have hh := pow_le_pow_left₀ ha0 ha2 4
        norm_num at hh
        exact hh
      exact hh.trans (by dsimp [T]; nlinarith [mul_le_mul_of_nonneg_right ha4 (hT0 ω)])
    have hh := abs_integral_le_of_ae_bound μ (fun ω => A0 ω - B0 ω)
      (fun ω => (16 / 24 : ℝ) * T ω) (hiA0.sub hiB0) (hiT.const_mul _) hp
    simpa only [integral_const_mul] using hh
  have hR1 : |∫ ω, A1 ω - B1 ω ∂μ| ≤ (8 / 6 : ℝ) * ∫ ω, T ω ∂μ := by
    have hp : ∀ᵐ ω ∂μ, |A1 ω - B1 ω| ≤ (8 / 6 : ℝ) * T ω := by
      filter_upwards [hbound] with ω hω
      have hh := s.abs_convolutionGradientTaylor2_remainder_le_tensor_direct ν x (ξ ω) a H
        (by simpa only [norm_smul, Real.norm_eq_abs] using hscale ω hω) hH
      change |s.convolutionTranslationD1 ν (x + a • ξ ω) (ξ ω) - B1 ω| ≤ _
      change _ ≤ |a| ^ 3 / 6 * T ω at hh
      rw [haabs] at hh
      have ha3 : a ^ 3 ≤ 8 := by
        have hh := pow_le_pow_left₀ ha0 ha2 3
        norm_num at hh
        exact hh
      exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right ha3 (hT0 ω)])
    have hh := abs_integral_le_of_ae_bound μ (fun ω => A1 ω - B1 ω)
      (fun ω => (8 / 6 : ℝ) * T ω) (hiA1.sub hiB1) (hiT.const_mul _) hp
    simpa only [integral_const_mul] using hh
  have e0 : s.translatedConvolution ν μ ξ x a - s.convolution ν x -
      a ^ 2 / 2 * s.observationSecondTerm ν μ ξ x -
      a ^ 3 / 6 * s.observationThirdTerm ν μ ξ x = ∫ ω, A0 ω - B0 ω ∂μ := by
    rw [integral_sub hiA0 hiB0]
    change _ = (∫ ω, s.convolution ν (line x (ξ ω) a) ∂μ) -
      (∫ ω, s.convolutionTaylor3 ν x (a • ξ ω) ∂μ)
    rw [s.integral_convolutionTaylor3_centered ν μ ξ hξ hbound hcenter x a]
    unfold translatedConvolution observationSecondTerm observationThirdTerm
    ring
  have e1 : (∫ ω, ∑ j, ξ ω j * s.convolutionFirstDerivative ν (line x (ξ ω) a) j ∂μ) -
      a * s.observationSecondTerm ν μ ξ x - a ^ 2 / 2 * s.observationThirdTerm ν μ ξ x =
        ∫ ω, A1 ω - B1 ω ∂μ := by
    rw [integral_sub hiA1 hiB1]
    change _ = (∫ ω, s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω) ∂μ) -
      (∫ ω, s.convolutionGradientTaylor2 ν x (ξ ω) a ∂μ)
    rw [s.integral_convolutionGradientTaylor2_centered ν μ ξ hξ hbound hcenter x a]
    unfold observationSecondTerm observationThirdTerm convolutionTranslationD1
    simp only [mul_comm (ξ _ _) ]
    ring
  have hq : |thinningProbability t| ≤ 1 := by
    rw [abs_of_nonneg (thinningProbability_nonneg ht1)]
    exact thinningProbability_le_one ht
  have hqp := abs_thinningProbability_derivative_le_three ht ht1
  have hT : 0 ≤ ∫ ω, T ω ∂μ := integral_nonneg hT0
  have heq : s.oneObservationTaylorResidual ν μ ξ x t =
      ((t - 3) / (1 + t) ^ 3) * (∫ ω, A0 ω - B0 ω ∂μ) +
        thinningProbability t * (∫ ω, A1 ω - B1 ω ∂μ) := by
    unfold oneObservationTaylorResidual
    rw [e0, e1]
  rw [heq]
  calc
    _ ≤ |(t - 3) / (1 + t) ^ 3| * |∫ ω, A0 ω - B0 ω ∂μ| +
        |thinningProbability t| * |∫ ω, A1 ω - B1 ω ∂μ| := by
      calc
        _ ≤ |((t - 3) / (1 + t) ^ 3) * (∫ ω, A0 ω - B0 ω ∂μ)| +
            |thinningProbability t * (∫ ω, A1 ω - B1 ω ∂μ)| := abs_add _ _
        _ = _ := congrArg₂ (fun b c : ℝ => b + c)
          (abs_mul ((t - 3) / (1 + t) ^ 3) (∫ ω, A0 ω - B0 ω ∂μ))
          (abs_mul (thinningProbability t) (∫ ω, A1 ω - B1 ω ∂μ))
    _ ≤ 3 * ((16 / 24 : ℝ) * ∫ ω, T ω ∂μ) + 1 * ((8 / 6 : ℝ) * ∫ ω, T ω ∂μ) :=
      add_le_add (mul_le_mul hqp hR0 (abs_nonneg _) (by norm_num))
        (mul_le_mul hq hR1 (abs_nonneg _) (by norm_num))
    _ ≤ 4 * ∫ ω, T ω ∂μ := by nlinarith only [hT]
    _ = _ := by rw [show (∫ ω, T ω ∂μ) = fourthTensorMoment μ ξ H from
      integral_fourthTensorProduct μ ξ hξ hbound H]


theorem sum_abs_oneObservationTaylorResidual_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ 2 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    (∑ i, |s.oneObservationTaylorResidual ν μ (ξ i) x t|) ≤
      4 * gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m) := by
  have hH0 (j k l m : Fin p) : 0 ≤ H j k l m := by
    have hh := hH 0 (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  calc
    _ ≤ ∑ i, 4 * fourthTensorMoment μ (ξ i) H := Finset.sum_le_sum
      (fun i _ => s.abs_oneObservationTaylorResidual_le ν μ (ξ i) (hξ i) hδ
        (hbound i) (hcenter i) x ht ht1 H hH)
    _ = 4 * ∑ i, fourthTensorMoment μ (ξ i) H := by rw [Finset.mul_sum]
    _ ≤ 4 * (gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m)) :=
      mul_le_mul_of_nonneg_left (sum_fourthTensorMoment_le_gamma4 μ ξ hξ hδ hbound H hH0)
        (by norm_num)
    _ = _ := by ring


private theorem continuous_secondDerivative_bounds (j k : Fin p) :
    Continuous (fun x => s.convolutionSecondDerivative ν x j k) := by
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν (fun x => s.mixedSecondDerivativeF x j k)
    (s.continuous_secondDerivative j k) (3 / s.bandwidth ^ 2)
    (fun x => s.norm_secondDerivative_le x j k)

private theorem continuous_thirdDerivative_bounds (j k l : Fin p) :
    Continuous (fun x => s.convolutionThirdDerivative ν x j k l) := by
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν (fun x => s.mixedThirdDerivativeF x j k l)
    (s.continuous_thirdDerivative j k l) (13 / s.bandwidth ^ 3)
    (fun x => s.norm_thirdDerivative_le x j k l)

/-- Centering cancels the first-order displacement of each actual convolution
Hessian entry. The remainder retains two coordinate factors. -/
theorem abs_mean_secondDerivative_shift_sub_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r) (j k : Fin p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |(∫ ω, s.convolutionSecondDerivative ν (x + a • ξ ω) j k ∂μ) -
      s.convolutionSecondDerivative ν x j k| ≤
      a ^ 2 / 2 * (∑ l, ∑ m, H j k l m * (∫ ω, |ξ ω l * ξ ω m| ∂μ)) := by
  let A : Ω → ℝ := fun ω => s.convolutionSecondDerivative ν (x + a • ξ ω) j k
  let L : Ω → ℝ := fun ω => ∑ l, (a * s.convolutionThirdDerivative ν x j k l) * ξ ω l
  let K : Ω → ℝ := fun ω => a ^ 2 / 2 * ∑ i : Fin p × Fin p,
    H j k i.1 i.2 * |ξ ω i.1 * ξ ω i.2|
  have hcoord (l : Fin p) : Integrable (fun ω => ξ ω l) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => l)
  have hpair (l m : Fin p) : Integrable (fun ω => ξ ω l * ξ ω m) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![l, m] : Fin 2 → Fin p)
  have hiA : Integrable A μ := (integrable_const (3 / s.bandwidth ^ 2)).mono'
    (((s.continuous_secondDerivative_bounds ν j k).measurable.comp
      (measurable_const.add (measurable_const.smul hξ))).aestronglyMeasurable)
    (ae_of_all μ (fun ω => s.norm_convolutionSecondDerivative_le ν _ j k))
  have hiL : Integrable L μ := integrable_finset_sum Finset.univ
    (fun l _ => (hcoord l).const_mul _)
  have hL : (∫ ω, L ω ∂μ) = 0 := by
    unfold L
    rw [integral_finset_sum Finset.univ (fun l _ => (hcoord l).const_mul _)]
    simp only [integral_const_mul, hcenter, mul_zero, Finset.sum_const_zero]
  have hiK : Integrable K μ :=
    (integrable_finset_sum Finset.univ (fun i _ =>
      (hpair i.1 i.2).abs.const_mul _)).const_mul _
  have hb : ∀ᵐ ω ∂μ, |A ω - (s.convolutionSecondDerivative ν x j k + L ω)| ≤ K ω := by
    filter_upwards [hbound] with ω hω
    have hscale : ‖a • ξ ω‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg a)).trans hr
    have hh := s.abs_convolutionSecondDerivative_remainder_le_tensor ν x (a • ξ ω) j k H hscale hH
    have hlinear : (∑ l, s.convolutionThirdDerivative ν x j k l * (a • ξ ω) l) = L ω := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [L, Pi.smul_apply, smul_eq_mul]
      ring
    have hp (l m : Fin p) : H j k l m * |(a • ξ ω) l * (a • ξ ω) m| =
        a ^ 2 * (H j k l m * |ξ ω l * ξ ω m|) := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [← sq_abs a]
      ring
    rw [hlinear] at hh
    dsimp [A, K]
    convert hh using 1
    simp only [hp, ← Finset.mul_sum, Fintype.sum_prod_type]
    ring
  have hh := abs_integral_sub_const_le_of_linear_remainder μ A L K
    (s.convolutionSecondDerivative ν x j k) hiA hiL hiK hL hb
  have hKI : (∫ ω, K ω ∂μ) =
      a ^ 2 / 2 * (∑ l, ∑ m, H j k l m * (∫ ω, |ξ ω l * ξ ω m| ∂μ)) := by
    unfold K
    rw [integral_const_mul, integral_finset_sum Finset.univ
      (fun i _ => (hpair i.1 i.2).abs.const_mul _)]
    simp only [integral_const_mul, Fintype.sum_prod_type]
  simpa only [A, hKI] using hh

/-- The mean displacement of an actual third convolution derivative retains
one coordinate factor, suitable for the signed third-moment correction. -/
theorem abs_mean_thirdDerivative_shift_sub_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r) (j k l : Fin p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |(∫ ω, s.convolutionThirdDerivative ν (x + a • ξ ω) j k l ∂μ) -
      s.convolutionThirdDerivative ν x j k l| ≤
      |a| * (∑ m, H j k l m * (∫ ω, |ξ ω m| ∂μ)) := by
  let A : Ω → ℝ := fun ω => s.convolutionThirdDerivative ν (x + a • ξ ω) j k l
  let K : Ω → ℝ := fun ω => |a| * ∑ m, H j k l m * |ξ ω m|
  have hcoord (m : Fin p) : Integrable (fun ω => ξ ω m) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => m)
  have hiA : Integrable A μ := (integrable_const (13 / s.bandwidth ^ 3)).mono'
    (((s.continuous_thirdDerivative_bounds ν j k l).measurable.comp
      (measurable_const.add (measurable_const.smul hξ))).aestronglyMeasurable)
    (ae_of_all μ (fun ω => s.norm_convolutionThirdDerivative_le ν _ j k l))
  have hiK : Integrable K μ := (integrable_finset_sum Finset.univ
    (fun m _ => (hcoord m).abs.const_mul _)).const_mul _
  have hb : ∀ᵐ ω ∂μ, |A ω - (s.convolutionThirdDerivative ν x j k l + (0 : ℝ))| ≤ K ω := by
    filter_upwards [hbound] with ω hω
    have hscale : ‖a • ξ ω‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg a)).trans hr
    have hh := s.abs_convolutionThirdDerivative_remainder_le_tensor ν x (a • ξ ω) j k l H hscale hH
    have hp (m : Fin p) : H j k l m * |(a • ξ ω) m| =
        |a| * (H j k l m * |ξ ω m|) := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      ring
    simpa only [A, K, add_zero, hp, ← Finset.mul_sum] using hh
  have hh := abs_integral_sub_const_le_of_linear_remainder μ A (fun _ => 0) K
    (s.convolutionThirdDerivative ν x j k l) hiA (integrable_const _) hiK (by simp) hb
  have hKI : (∫ ω, K ω ∂μ) = |a| * (∑ m, H j k l m * (∫ ω, |ξ ω m| ∂μ)) := by
    unfold K
    rw [integral_const_mul, integral_finset_sum Finset.univ (fun m _ => (hcoord m).abs.const_mul _)]
    simp only [integral_const_mul]
  simpa only [A, hKI] using hh


private theorem integrable_fourth_coordinate_bounds
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (j : Fin p) :
    Integrable (fun ω => ξ ω j ^ 4) μ := by
  have hh := integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 4 => j)
  simpa [Fin.prod_univ_succ, pow_succ, mul_assoc] using hh

/-- The quadratic common-point correction is bounded by individual fourth
coordinate moments, using an actual Hessian displacement and centering. -/
theorem abs_secondMoment_mul_mean_secondDerivative_shift_sub_le_fourth
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r) (j k : Fin p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |∫ ω, ξ ω j * ξ ω k ∂μ| *
      |(∫ ω, s.convolutionSecondDerivative ν (x + a • ξ ω) j k ∂μ) -
        s.convolutionSecondDerivative ν x j k| ≤
      a ^ 2 / 2 * (∑ l, ∑ m, H j k l m *
        (((∫ ω, ξ ω j ^ 4 ∂μ) + (∫ ω, ξ ω k ^ 4 ∂μ) +
          (∫ ω, ξ ω l ^ 4 ∂μ) + (∫ ω, ξ ω m ^ 4 ∂μ)) / 4)) := by
  have hpair (l m : Fin p) : Integrable (fun ω => ξ ω l * ξ ω m) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![l, m] : Fin 2 → Fin p)
  have hpow (l : Fin p) := integrable_fourth_coordinate_bounds μ ξ hξ hbound l
  have hr0 : 0 ≤ r := (mul_nonneg (abs_nonneg a) hδ).trans hr
  have hH0 (l m : Fin p) : 0 ≤ H j k l m := by
    have hh := hH 0 (by simpa using hr0) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  have hmean := s.abs_mean_secondDerivative_shift_sub_le ν μ ξ hξ hbound hcenter x a hr j k H hH
  calc
    _ ≤ |∫ ω, ξ ω j * ξ ω k ∂μ| * (a ^ 2 / 2 *
        (∑ l, ∑ m, H j k l m * (∫ ω, |ξ ω l * ξ ω m| ∂μ))) :=
      mul_le_mul_of_nonneg_left hmean (abs_nonneg _)
    _ = a ^ 2 / 2 * (∑ l, ∑ m, H j k l m *
        (|∫ ω, ξ ω j * ξ ω k ∂μ| * (∫ ω, |ξ ω l * ξ ω m| ∂μ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg a) (by norm_num))
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
        (abs_integral_pair_mul_integral_abs_pair_le_fourth_mean μ
          (fun ω => ξ ω j) (fun ω => ξ ω k) (fun ω => ξ ω l) (fun ω => ξ ω m)
          (hpair j k) (hpair l m) (hpow j) (hpow k) (hpow l) (hpow m)) (hH0 l m)

/-- The cubic common-point correction obeys the same fourth-moment principle
without a fractional Hölder bound or a moment of the coordinate maximum. -/
theorem abs_thirdMoment_mul_mean_thirdDerivative_shift_sub_le_fourth
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r) (j k l : Fin p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ| *
      |(∫ ω, s.convolutionThirdDerivative ν (x + a • ξ ω) j k l ∂μ) -
        s.convolutionThirdDerivative ν x j k l| ≤
      |a| * (∑ m, H j k l m *
        (((∫ ω, ξ ω j ^ 4 ∂μ) + (∫ ω, ξ ω k ^ 4 ∂μ) +
          (∫ ω, ξ ω l ^ 4 ∂μ) + (∫ ω, ξ ω m ^ 4 ∂μ)) / 4)) := by
  have htriple : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l] : Fin 3 → Fin p)
  have hcoord (m : Fin p) : Integrable (fun ω => ξ ω m) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => m)
  have hpow (m : Fin p) := integrable_fourth_coordinate_bounds μ ξ hξ hbound m
  have hr0 : 0 ≤ r := (mul_nonneg (abs_nonneg a) hδ).trans hr
  have hH0 (m : Fin p) : 0 ≤ H j k l m := by
    have hh := hH 0 (by simpa using hr0) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  have hmean := s.abs_mean_thirdDerivative_shift_sub_le ν μ ξ hξ hbound x a hr j k l H hH
  calc
    _ ≤ |∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ| * (|a| *
        (∑ m, H j k l m * (∫ ω, |ξ ω m| ∂μ))) :=
      mul_le_mul_of_nonneg_left hmean (abs_nonneg _)
    _ = |a| * (∑ m, H j k l m *
        (|∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ| * (∫ ω, |ξ ω m| ∂μ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
      exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
        (abs_integral_triple_mul_integral_abs_le_fourth_mean μ
          (fun ω => ξ ω j) (fun ω => ξ ω k) (fun ω => ξ ω l) (fun ω => ξ ω m)
          htriple (hcoord m) (hpow j) (hpow k) (hpow l) (hpow m)) (hH0 m)


omit [IsProbabilityMeasure ν] in
theorem fourthTensorMoment_le_fourthCoordinateMoment
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hH : ∀ j k l m, 0 ≤ H j k l m) :
    fourthTensorMoment μ ξ H ≤ fourthCoordinateMoment μ ξ H := by
  have hprod (j k l m : Fin p) : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l * ξ ω m) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l, m] : Fin 4 → Fin p)
  have hpow (j : Fin p) := integrable_fourth_coordinate_bounds μ ξ hξ hbound j
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
    (integral_abs_four_product_le_fourth_mean μ _ _ _ _ (hprod j k l m)
      (hpow j) (hpow k) (hpow l) (hpow m)) (hH j k l m)

noncomputable def secondCommonPointCorrection {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (a : ℝ) : ℝ :=
  ∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
    ((∫ ω, s.convolutionSecondDerivative ν (x + a • ξ ω) j k ∂μ) -
      s.convolutionSecondDerivative ν x j k)

noncomputable def thirdCommonPointCorrection {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (a : ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
    ((∫ ω, s.convolutionThirdDerivative ν (x + a • ξ ω) j k l ∂μ) -
      s.convolutionThirdDerivative ν x j k l)

theorem abs_secondCommonPointCorrection_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.secondCommonPointCorrection ν μ ξ x a| ≤ a ^ 2 / 2 * fourthCoordinateMoment μ ξ H := by
  unfold secondCommonPointCorrection
  calc
    _ ≤ ∑ j, ∑ k, |(∫ ω, ξ ω j * ξ ω k ∂μ) *
        ((∫ ω, s.convolutionSecondDerivative ν (x + a • ξ ω) j k ∂μ) -
          s.convolutionSecondDerivative ν x j k)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, a ^ 2 / 2 * (∑ l, ∑ m, H j k l m *
        (((∫ ω, ξ ω j ^ 4 ∂μ) + (∫ ω, ξ ω k ^ 4 ∂μ) +
          (∫ ω, ξ ω l ^ 4 ∂μ) + (∫ ω, ξ ω m ^ 4 ∂μ)) / 4)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact s.abs_secondMoment_mul_mean_secondDerivative_shift_sub_le_fourth ν μ ξ hξ hδ
          hbound hcenter x a hr j k H hH
    _ = _ := by unfold fourthCoordinateMoment; simp only [Finset.mul_sum]

theorem abs_thirdCommonPointCorrection_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (hr : |a| * δ ≤ r)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.thirdCommonPointCorrection ν μ ξ x a| ≤ |a| * fourthCoordinateMoment μ ξ H := by
  unfold thirdCommonPointCorrection
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, |(∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
        ((∫ ω, s.convolutionThirdDerivative ν (x + a • ξ ω) j k l ∂μ) -
          s.convolutionThirdDerivative ν x j k l)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, ∑ l, |a| * (∑ m, H j k l m *
        (((∫ ω, ξ ω j ^ 4 ∂μ) + (∫ ω, ξ ω k ^ 4 ∂μ) +
          (∫ ω, ξ ω l ^ 4 ∂μ) + (∫ ω, ξ ω m ^ 4 ∂μ)) / 4)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact s.abs_thirdMoment_mul_mean_thirdDerivative_shift_sub_le_fourth ν μ ξ hξ hδ
          hbound x a hr j k l H hH
    _ = _ := by unfold fourthCoordinateMoment; simp only [Finset.mul_sum]

/-- Residual after replacing both principal moment contractions by the
one-observation retained operator at the common point. -/
noncomputable def correctedOneObservationResidual {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  s.oneObservationTaylorResidual ν μ ξ x t +
    thinningProbability t / 2 * s.secondCommonPointCorrection ν μ ξ x (thinningScale t) +
    t * thinningProbability t / 3 * s.thirdCommonPointCorrection ν μ ξ x (thinningScale t)

/-- The actual corrected one-observation residual is fourth order, with an
absolute coefficient six and individual-coordinate fourth moments. -/
theorem abs_correctedOneObservationResidual_le
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ 2 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.correctedOneObservationResidual ν μ ξ x t| ≤ 6 * fourthCoordinateMoment μ ξ H := by
  let S := fourthCoordinateMoment μ ξ H
  let a := thinningScale t
  have ha0 : 0 ≤ a := (thinningScale_pos ht).le
  have ha2 : a ≤ 2 := thinningScale_le_two ht1
  have haabs : |a| = a := abs_of_nonneg ha0
  have hscale : |a| * δ ≤ 2 * δ := by rw [haabs]; exact mul_le_mul_of_nonneg_right ha2 hδ
  have hH0 (j k l m : Fin p) : 0 ≤ H j k l m := by
    have hh := hH 0 (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  have hS : 0 ≤ S := fourthCoordinateMoment_nonneg μ ξ H hH0
  have hraw : |s.oneObservationTaylorResidual ν μ ξ x t| ≤ 4 * S :=
    (s.abs_oneObservationTaylorResidual_le ν μ ξ hξ hδ hbound hcenter x ht ht1 H hH).trans
      (mul_le_mul_of_nonneg_left
        (fourthTensorMoment_le_fourthCoordinateMoment μ ξ hξ hbound H hH0) (by norm_num))
  have hq0 := thinningProbability_nonneg ht1
  have hq1 := thinningProbability_le_one ht
  have hquad := s.abs_secondCommonPointCorrection_le ν μ ξ hξ hδ hbound hcenter x a hscale H hH
  have hcubic := s.abs_thirdCommonPointCorrection_le ν μ ξ hξ hδ hbound x a hscale H hH
  have haSq : a ^ 2 ≤ 4 := by nlinarith only [ha0, ha2]
  have hquad' : |s.secondCommonPointCorrection ν μ ξ x a| ≤ 2 * S :=
    hquad.trans (by dsimp [S]; nlinarith only [mul_le_mul_of_nonneg_right haSq hS])
  have hcubic' : |s.thirdCommonPointCorrection ν μ ξ x a| ≤ 2 * S := by
    rw [haabs] at hcubic
    exact hcubic.trans (mul_le_mul_of_nonneg_right ha2 hS)
  have hcoef2 : |thinningProbability t / 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg (div_nonneg hq0 (by norm_num))]
    exact div_le_div_of_nonneg_right hq1 (by norm_num)
  have htq : t * thinningProbability t ≤ 1 :=
    (mul_le_mul ht1 hq1 hq0 (by norm_num)).trans (by norm_num)
  have hcoef3 : |t * thinningProbability t / 3| ≤ 1 / 3 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg ht hq0) (by norm_num))]
    exact div_le_div_of_nonneg_right htq (by norm_num)
  unfold correctedOneObservationResidual
  change |s.oneObservationTaylorResidual ν μ ξ x t +
    thinningProbability t / 2 * s.secondCommonPointCorrection ν μ ξ x a +
    t * thinningProbability t / 3 * s.thirdCommonPointCorrection ν μ ξ x a| ≤ _
  calc
    _ ≤ |s.oneObservationTaylorResidual ν μ ξ x t| +
        |thinningProbability t / 2 * s.secondCommonPointCorrection ν μ ξ x a| +
        |t * thinningProbability t / 3 * s.thirdCommonPointCorrection ν μ ξ x a| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |s.oneObservationTaylorResidual ν μ ξ x t| +
        |thinningProbability t / 2| * |s.secondCommonPointCorrection ν μ ξ x a| +
        |t * thinningProbability t / 3| * |s.thirdCommonPointCorrection ν μ ξ x a| := by rw [abs_mul, abs_mul]
    _ ≤ 4 * S + (1 / 2 : ℝ) * (2 * S) + (1 / 3 : ℝ) * (2 * S) :=
      add_le_add (add_le_add hraw (mul_le_mul hcoef2 hquad' (abs_nonneg _) (by norm_num)))
        (mul_le_mul hcoef3 hcubic' (abs_nonneg _) (by norm_num))
    _ ≤ _ := by dsimp [S]; nlinarith only [hS]


/-- Summing the actual corrected one-observation residuals costs only the
maximum summed coordinate fourth moment and the mass of the common envelope. -/
theorem sum_abs_correctedOneObservationResidual_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ 2 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    (∑ i, |s.correctedOneObservationResidual ν μ (ξ i) x t|) ≤
      6 * gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m) := by
  have hH0 (j k l m : Fin p) : 0 ≤ H j k l m := by
    have hh := hH 0 (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  calc
    _ ≤ ∑ i, 6 * fourthCoordinateMoment μ (ξ i) H := Finset.sum_le_sum
      (fun i _ => s.abs_correctedOneObservationResidual_le ν μ (ξ i) (hξ i) hδ
        (hbound i) (hcenter i) x ht ht1 H hH)
    _ = 6 * ∑ i, fourthCoordinateMoment μ (ξ i) H := by rw [Finset.mul_sum]
    _ ≤ 6 * (gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H j k l m)) :=
      mul_le_mul_of_nonneg_left (sum_fourthCoordinateMoment_le_gamma4 μ ξ H hH0) (by norm_num)
    _ = _ := by ring


omit [IsProbabilityMeasure ν] in
theorem observationSecondTerm_eq_tensor
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) :
    s.observationSecondTerm ν μ ξ x =
      ∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) * s.convolutionSecondDerivative ν x j k := by
  have hi (j k : Fin p) : Integrable (fun ω => ξ ω j * ξ ω k) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k] : Fin 2 → Fin p)
  unfold observationSecondTerm convolutionTranslationD2
  have heq (ω : Ω) (j k : Fin p) :
      s.convolutionSecondDerivative ν x j k * ξ ω j * ξ ω k =
        s.convolutionSecondDerivative ν x j k * (ξ ω j * ξ ω k) := by ring
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => (hi j k).const_mul (s.convolutionSecondDerivative ν x j k)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ
    (fun k _ => (hi j k).const_mul (s.convolutionSecondDerivative ν x j k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  ring

noncomputable def bernoulliMeanSecondDerivative {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) (j k : Fin p) : ℝ :=
  (1 - thinningProbability t) * s.convolutionSecondDerivative ν x j k +
    thinningProbability t *
      (∫ ω, s.convolutionSecondDerivative ν (x + thinningScale t • ξ ω) j k ∂μ)

noncomputable def bernoulliMeanThirdDerivative {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) (j k l : Fin p) : ℝ :=
  (1 - thinningProbability t) * s.convolutionThirdDerivative ν x j k l +
    thinningProbability t *
      (∫ ω, s.convolutionThirdDerivative ν (x + thinningScale t • ξ ω) j k l ∂μ)

omit [IsProbabilityMeasure ν] in
theorem sum_secondMoment_bernoulliMean_eq
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) (t : ℝ) :
    (∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
      s.bernoulliMeanSecondDerivative ν μ ξ x t j k) =
      s.observationSecondTerm ν μ ξ x + thinningProbability t *
        s.secondCommonPointCorrection ν μ ξ x (thinningScale t) := by
  rw [s.observationSecondTerm_eq_tensor ν μ ξ hξ hbound x]
  unfold bernoulliMeanSecondDerivative secondCommonPointCorrection
  calc
    _ = ∑ j, ∑ k, ((∫ ω, ξ ω j * ξ ω k ∂μ) * s.convolutionSecondDerivative ν x j k +
        thinningProbability t * ((∫ ω, ξ ω j * ξ ω k ∂μ) *
          ((∫ ω, s.convolutionSecondDerivative ν (x + thinningScale t • ξ ω) j k ∂μ) -
            s.convolutionSecondDerivative ν x j k))) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

omit [IsProbabilityMeasure ν] in
theorem sum_thirdMoment_bernoulliMean_eq
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) (t : ℝ) :
    (∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
      s.bernoulliMeanThirdDerivative ν μ ξ x t j k l) =
      s.observationThirdTerm ν μ ξ x + thinningProbability t *
        s.thirdCommonPointCorrection ν μ ξ x (thinningScale t) := by
  rw [s.observationThirdTerm_eq_tensor ν μ ξ hξ hbound x]
  unfold bernoulliMeanThirdDerivative thirdCommonPointCorrection
  calc
    _ = ∑ j, ∑ k, ∑ l,
        ((∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) * s.convolutionThirdDerivative ν x j k l +
          thinningProbability t * ((∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
            ((∫ ω, s.convolutionThirdDerivative ν (x + thinningScale t • ξ ω) j k l ∂μ) -
              s.convolutionThirdDerivative ν x j k l))) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

omit [IsProbabilityMeasure ν] in
/-- Exact common-point operator identity, prior to applying any remainder bound. -/
theorem oneObservation_operator_identity
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) (t : ℝ) :
    -(s.observationSecondTerm ν μ ξ x) / 2 -
      t / 3 * s.observationThirdTerm ν μ ξ x + s.oneObservationTaylorResidual ν μ ξ x t =
      -(∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
        s.bernoulliMeanSecondDerivative ν μ ξ x t j k) / 2 -
      t / 3 * (∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
        s.bernoulliMeanThirdDerivative ν μ ξ x t j k l) +
      s.correctedOneObservationResidual ν μ ξ x t := by
  rw [s.sum_secondMoment_bernoulliMean_eq ν μ ξ hξ hbound x t,
    s.sum_thirdMoment_bernoulliMean_eq ν μ ξ hξ hbound x t]
  unfold correctedOneObservationResidual
  ring

/-- The actual one-observation derivative in the retained common-point form. -/
theorem hasDerivAt_bernoulliTranslation_corrected
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (s.bernoulliTranslation ν μ ξ x)
      (-(∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
        s.bernoulliMeanSecondDerivative ν μ ξ x t j k) / 2 -
        t / 3 * (∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
          s.bernoulliMeanThirdDerivative ν μ ξ x t j k l) +
        s.correctedOneObservationResidual ν μ ξ x t) t := by
  have hd := s.hasDerivAt_bernoulliTranslation_taylor ν μ ξ hξ hbound x ht
  rw [s.oneObservation_operator_identity ν μ ξ hξ hbound x t] at hd
  exact hd

end FaceSmoother
end RectangleCLT
