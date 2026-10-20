import RectangleCLTCompanion.FourthIdentityFresh

open MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 800000
namespace RectangleCLT.FaceSmoother
noncomputable section
variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

private theorem interval_sum2 (f : Fin p → Fin p → ℝ → ℝ)
    (c : Fin p → Fin p → ℝ)
    (hi : ∀ j k, IntervalIntegrable (f j k) volume 0 1) :
    (∑ j, ∑ k, c j k * (∫ r in (0 : ℝ)..1, f j k r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, ∑ k, c j k * f j k r := by
  have hinner (j : Fin p) : (∑ k, c j k * (∫ r in (0 : ℝ)..1, f j k r)) =
      ∫ r in (0 : ℝ)..1, ∑ k, c j k * f j k r := by
    rw [intervalIntegral.integral_finset_sum (fun k _ => (hi j k).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun j _ =>
    IntervalIntegrable.sum Finset.univ (fun k _ => (hi j k).const_mul (c j k)))
  simp only [Finset.sum_apply] at ho
  exact ho.symm

private theorem interval_sum3 (f : Fin p → Fin p → Fin p → ℝ → ℝ)
    (c : Fin p → Fin p → Fin p → ℝ)
    (hi : ∀ j k l, IntervalIntegrable (f j k l) volume 0 1) :
    (∑ j, ∑ k, ∑ l, c j k l * (∫ r in (0 : ℝ)..1, f j k l r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, ∑ k, ∑ l, c j k l * f j k l r := by
  have hinner (j : Fin p) := interval_sum2 (f j) (c j) (hi j)
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun j _ =>
    IntervalIntegrable.sum Finset.univ (fun k _ =>
      IntervalIntegrable.sum Finset.univ (fun l _ => (hi j k l).const_mul (c j k l))))
  simp only [Finset.sum_apply] at ho
  exact ho.symm

private theorem fourthTensor_pair_integral (x u v : Vector p) (a : ℝ) :
    (∑ j, ∑ k, (u j * u k) *
      (∫ r in (0 : ℝ)..1, (1 - r) *
        (∑ l, ∑ m, s.convolutionFourthDerivative ν
          (line x v (a * r)) j k l m * v l * v m))) =
      ∫ r in (0 : ℝ)..1, (1 - r) *
        s.convolutionFourthTensor ν (line x v (a * r)) u u v v := by
  have hc (j k l m : Fin p) :
      Continuous (fun r => s.convolutionFourthDerivative ν (line x v (a * r)) j k l m) :=
    (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp
      (continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const))
  have hi (j k : Fin p) : IntervalIntegrable (fun r => (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x v (a * r)) j k l m * v l * v m)) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul (continuous_finset_sum _ (fun l _ =>
      continuous_finset_sum _ (fun m _ => ((hc j k l m).mul continuous_const).mul continuous_const)))).intervalIntegrable 0 1
  rw [interval_sum2 (fun j k r => (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x v (a * r)) j k l m * v l * v m)) (fun j k => u j * u k) hi]
  apply intervalIntegral.integral_congr
  intro r _
  unfold convolutionFourthTensor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

private theorem fourthTensor_triple_integral (x u v : Vector p) (a : ℝ) :
    (∑ j, ∑ k, ∑ l, (u j * u k * u l) *
      (∫ r in (0 : ℝ)..1,
        (∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m))) =
      ∫ r in (0 : ℝ)..1,
        s.convolutionFourthTensor ν (line x v (a * r)) u u u v := by
  have hc (j k l m : Fin p) :
      Continuous (fun r => s.convolutionFourthDerivative ν (line x v (a * r)) j k l m) :=
    (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp
      (continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const))
  have hi (j k l : Fin p) : IntervalIntegrable (fun r =>
      ∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m) volume 0 1 :=
    (continuous_finset_sum _ (fun m _ => (hc j k l m).mul continuous_const)).intervalIntegrable 0 1
  rw [interval_sum3 (fun j k l r =>
      ∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m)
      (fun j k l => u j * u k * u l) hi]
  apply intervalIntegral.integral_congr
  intro r _
  unfold convolutionFourthTensor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The two row directions in B are sampled independently by the actual
product law. The repeated direction is the first coordinate of that law. -/
def fourthRowB_freshPair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  (1 - t) / 2 * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, (1 - r) *
    s.convolutionFourthTensor ν (line x (ξ z.2) (thinningScale t * r))
      (ξ z.1) (ξ z.1) (ξ z.2) (ξ z.2)) ∂μ.prod μ

/-- C has three copies of the first fresh row and one of the independent
second row, which also determines the translated base. -/
def fourthRowC_freshPair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  t * (1 - t) / (3 * (1 + t)) * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1,
    s.convolutionFourthTensor ν (line x (ξ z.2) (thinningScale t * r))
      (ξ z.1) (ξ z.1) (ξ z.1) (ξ z.2)) ∂μ.prod μ

theorem fourthRowB_eq_freshPair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.fourthRowB ν μ ξ x t = s.fourthRowB_freshPair ν μ ξ x t := by
  have ha : thinningScale t ≠ 0 := ne_of_gt (thinningScale_pos ht)
  have hi (j k : Fin p) : Integrable (fun ω => ξ ω j * ξ ω k) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j,k] : Fin 2 → Fin p)
  unfold fourthRowB fourthRowB_freshPair
  congr 1
  rw [Companion.integral_fresh_pair_tensor2 μ
    (fun ω j k => ξ ω j * ξ ω k)
    (fun ω j k => ∫ r in (0 : ℝ)..1, (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω l * ξ ω m))
    hi (fun j k => s.integrable_secondFourthKernel ν μ ξ hξ hbound x ha j k)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => s.fourthTensor_pair_integral ν x (ξ z.1) (ξ z.2) _)

theorem fourthRowC_eq_freshPair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.fourthRowC ν μ ξ x t = s.fourthRowC_freshPair ν μ ξ x t := by
  have ha : thinningScale t ≠ 0 := ne_of_gt (thinningScale_pos ht)
  have hi (j k l : Fin p) : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j,k,l] : Fin 3 → Fin p)
  unfold fourthRowC fourthRowC_freshPair
  congr 1
  rw [Companion.integral_fresh_pair_tensor3 μ
    (fun ω j k l => ξ ω j * ξ ω k * ξ ω l)
    (fun ω j k l => ∫ r in (0 : ℝ)..1,
      (∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (thinningScale t * r)) j k l m * ξ ω m))
    hi (fun j k l => s.integrable_thirdFourthKernel ν μ ξ hξ x ha j k l)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => s.fourthTensor_triple_integral ν x (ξ z.1) (ξ z.2) _)

end
end RectangleCLT.FaceSmoother
