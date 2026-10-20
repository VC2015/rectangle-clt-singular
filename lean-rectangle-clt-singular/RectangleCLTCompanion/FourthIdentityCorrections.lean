import RectangleCLTCompanion.FourthIdentityRows

/-! The second and third common-point corrections are exactly fourth order.
The coefficients are the actual signed row moments; independent fresh copies
are represented by their separate integrals. -/

open MeasureTheory
open scoped BigOperators Interval

set_option maxHeartbeats 800000

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

def fourthRowB {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  (1 - t) / 2 * ∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
    (∫ ω, (∫ r in (0 : ℝ)..1, (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω l * ξ ω m)) ∂μ)

def fourthRowC {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  t * (1 - t) / (3 * (1 + t)) * ∑ j, ∑ k, ∑ l,
    (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
    (∫ ω, (∫ r in (0 : ℝ)..1,
      (∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω m)) ∂μ)

theorem integral_secondDerivative_sub_eq_fourth_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) (a : ℝ) (j k : Fin p) :
    (∫ ω, s.convolutionSecondDerivative ν (x + a • ξ ω) j k ∂μ) -
      s.convolutionSecondDerivative ν x j k =
      a ^ 2 * ∫ ω, (∫ r in (0 : ℝ)..1, (1 - r) *
        (∑ l, ∑ m, s.convolutionFourthDerivative ν
          (line x (ξ ω) (a * r)) j k l m * ξ ω l * ξ ω m)) ∂μ := by
  have hline : Measurable (fun ω => x + a • ξ ω) :=
    measurable_const.add (measurable_const.smul hξ)
  have hiA : Integrable (fun ω => s.convolutionSecondDerivative ν (x + a • ξ ω) j k) μ :=
    integrable_bounded_test_comp μ _ hline _ (s.continuous_convolutionSecondDerivative ν j k)
      _ (fun z => s.norm_convolutionSecondDerivative_le ν z j k)
  have hiξ (l : Fin p) : Integrable (fun ω => ξ ω l) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => l)
  have hiL : Integrable (fun ω => a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l) μ :=
    (integrable_finset_sum _ (fun l _ => (hiξ l).const_mul _)).const_mul a
  have hzero : (∫ ω, a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l ∂μ) = 0 := by
    rw [integral_const_mul, integral_finset_sum _ (fun l _ => (hiξ l).const_mul _)]
    simp_rw [integral_const_mul, hcenter, mul_zero, Finset.sum_const_zero, mul_zero]
  have heq (ω : Ω) :
      s.convolutionSecondDerivative ν (x + a • ξ ω) j k -
        (s.convolutionSecondDerivative ν x j k +
          a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l) =
      a ^ 2 * (∫ r in (0 : ℝ)..1, (1 - r) *
        (∑ l, ∑ m, s.convolutionFourthDerivative ν
          (line x (ξ ω) (a * r)) j k l m * ξ ω l * ξ ω m)) := by
    rw [s.convolutionSecondDerivative_integral_remainder]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  have hh := integral_congr_ae (ae_of_all μ heq)
  rw [integral_sub (f := fun ω => s.convolutionSecondDerivative ν (x + a • ξ ω) j k)
      (g := fun ω => s.convolutionSecondDerivative ν x j k +
        a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l)
      hiA ((integrable_const _).add hiL),
    integral_add (f := fun _ => s.convolutionSecondDerivative ν x j k)
      (g := fun ω => a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l)
      (integrable_const _) hiL, integral_const, measureReal_univ_eq_one,
    one_smul, hzero, add_zero, integral_const_mul] at hh
  exact hh

theorem integral_thirdDerivative_sub_eq_fourth_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ)
    (x : Vector p) (a : ℝ) (j k l : Fin p) :
    (∫ ω, s.convolutionThirdDerivative ν (x + a • ξ ω) j k l ∂μ) -
      s.convolutionThirdDerivative ν x j k l =
      a * ∫ ω, (∫ r in (0 : ℝ)..1,
        (∑ m, s.convolutionFourthDerivative ν
          (line x (ξ ω) (a * r)) j k l m * ξ ω m)) ∂μ := by
  have hline : Measurable (fun ω => x + a • ξ ω) :=
    measurable_const.add (measurable_const.smul hξ)
  have hiA : Integrable (fun ω => s.convolutionThirdDerivative ν (x + a • ξ ω) j k l) μ :=
    integrable_bounded_test_comp μ _ hline _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l)
      _ (fun z => s.norm_convolutionThirdDerivative_le ν z j k l)
  have heq (ω : Ω) :
      s.convolutionThirdDerivative ν (x + a • ξ ω) j k l -
        s.convolutionThirdDerivative ν x j k l =
      a * (∫ r in (0 : ℝ)..1,
        (∑ m, s.convolutionFourthDerivative ν
          (line x (ξ ω) (a * r)) j k l m * ξ ω m)) := by
    rw [s.convolutionThirdDerivative_integral_increment,
      intervalIntegral.integral_const_mul]
  have hh := integral_congr_ae (ae_of_all μ heq)
  rw [integral_sub hiA (integrable_const _), integral_const, measureReal_univ_eq_one,
    one_smul, integral_const_mul] at hh
  exact hh

theorem secondCommonPointCorrection_eq_fourthRowB
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t / 2 * s.secondCommonPointCorrection ν μ ξ x (thinningScale t) =
      s.fourthRowB ν μ ξ x t := by
  unfold secondCommonPointCorrection fourthRowB
  simp_rw [s.integral_secondDerivative_sub_eq_fourth_integral ν μ ξ hξ hbound hcenter]
  have ha : thinningProbability t / 2 * thinningScale t ^ 2 = (1 - t) / 2 := by
    unfold thinningProbability thinningScale
    have hn : 1 + t ≠ 0 := by linarith
    field_simp [hn]
    ring
  calc
    _ = (thinningProbability t / 2 * thinningScale t ^ 2) *
        (∑ j, ∑ k, (∫ ω, ξ ω j * ξ ω k ∂μ) *
          (∫ ω, (∫ r in (0 : ℝ)..1, (1 - r) *
            (∑ l, ∑ m, s.convolutionFourthDerivative ν
              (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω l * ξ ω m)) ∂μ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [ha]

theorem thirdCommonPointCorrection_eq_fourthRowC
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    t * thinningProbability t / 3 * s.thirdCommonPointCorrection ν μ ξ x (thinningScale t) =
      s.fourthRowC ν μ ξ x t := by
  unfold thirdCommonPointCorrection fourthRowC
  simp_rw [s.integral_thirdDerivative_sub_eq_fourth_integral ν μ ξ hξ]
  have ha : t * thinningProbability t / 3 * thinningScale t = t * (1 - t) / (3 * (1 + t)) := by
    unfold thinningProbability thinningScale
    have hn : 1 + t ≠ 0 := by linarith
    field_simp [hn]
    ring
  calc
    _ = (t * thinningProbability t / 3 * thinningScale t) *
        (∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
          (∫ ω, (∫ r in (0 : ℝ)..1,
            (∑ m, s.convolutionFourthDerivative ν
              (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω m)) ∂μ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [ha]

/-- Exact equality: the three genuine fourth-order terms exhaust the
corrected one-row residual. No estimate is a premise. -/
theorem correctedOneObservationResidual_eq_fourthRows
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.correctedOneObservationResidual ν μ ξ x t =
      s.fourthRowA ν μ ξ x t + s.fourthRowB ν μ ξ x t + s.fourthRowC ν μ ξ x t := by
  unfold correctedOneObservationResidual
  rw [s.oneObservationTaylorResidual_eq_fourthRowA ν μ ξ hξ hbound hcenter x ht,
    s.secondCommonPointCorrection_eq_fourthRowB ν μ ξ hξ hbound hcenter x ht,
    s.thirdCommonPointCorrection_eq_fourthRowC ν μ ξ hξ x ht]

end
end RectangleCLT.FaceSmoother
