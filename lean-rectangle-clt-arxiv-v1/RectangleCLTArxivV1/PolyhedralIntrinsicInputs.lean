import RectangleCLTArxivV1.TransfersProjection
import RectangleCLTArxivV1.TransfersMoments
import RectangleCLTCompanion.SplitV4.ZeroVarianceFaces

/-! Actual moment inputs for the intrinsic polyhedral transfer. The
polynomial envelope-only class is transferred at exactly `J B`; the class
with coordinate fourth moments is transferred at exactly `J² B`. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

namespace PolynomialEnvelopeHypotheses
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p m n : ℕ} {X : Fin n → Ω → Vector p} {q B : ℝ}

theorem projected_coordinate_memLp_two (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (M : Matrix (Fin m) (Fin p) ℝ) (i : Fin n) (α : Fin m) :
    MemLp (fun ω => M.mulVec (X i ω) α) 2 μ := by
  have he : (fun ω => M.mulVec (X i ω) α) = ∑ j, (fun ω => M α j*X i ω j) := by
    funext ω
    simp only [Matrix.mulVec,dotProduct,Finset.sum_apply]
  rw [he]
  exact memLp_finset_sum' Finset.univ
    (fun j _ => (h.coordinate_memLp_two hq i j).const_mul _)

theorem projected_centered (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (M : Matrix (Fin m) (Fin p) ℝ) (i : Fin n) (α : Fin m) :
    (∫ ω, M.mulVec (X i ω) α ∂μ)=0 := by
  unfold Matrix.mulVec dotProduct
  rw [integral_finset_sum Finset.univ (fun j _ =>
    ((h.coordinate_memLp_two hq i j).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul,h.centered,mul_zero,Finset.sum_const_zero]

theorem projected_covariance (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (M : Matrix (Fin m) (Fin p) ℝ) :
    covariance μ (normalizedObservationSum (fun i ω => M.mulVec (X i ω))) =
      M*covariance μ (normalizedObservationSum X)*M.transpose := by
  rw [normalizedObservationSum_mulVec]
  apply covariance_mulVec_of_centered_memLp
  · simpa only [sumVector_normalizedSummands] using
      memLp_sumVector_coordinate (normalizedSummands_coordinate_memLp_two (h.coordinate_memLp_two hq))
  · simpa only [sumVector_normalizedSummands] using
      integral_sumVector_coordinate_zero
        (fun i j => ((normalizedSummands_coordinate_memLp_two (h.coordinate_memLp_two hq) i j).integrable
          (by norm_num))) (normalizedSummands_centered h.centered)

theorem projected_average_second (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (M : Matrix (Fin m) (Fin p) ℝ)
    (hunit : ∀ α, (M*covariance μ (normalizedObservationSum X)*M.transpose) α α=1)
    (α : Fin m) :
    (1/(n:ℝ))*(∑ i, ∫ ω, M.mulVec (X i ω) α^2 ∂μ)=1 := by
  have hc := normalizedSummands_covariance_diagonal
    (h.independent.comp (fun _ => M.mulVec) (fun _ => measurable_rectangular_mulVec M))
    (h.projected_coordinate_memLp_two hq M) (h.projected_centered hq M) α
  change covariance μ (sumVector (normalizedSummands (fun i ω => M.mulVec (X i ω)))) α α = _ at hc
  rw [sumVector_normalizedSummands,h.projected_covariance hq M,hunit α] at hc
  exact hc.symm

omit [IsProbabilityMeasure μ] in
/-- The envelope-only branch uses `JB`, without inserting a fourth budget. -/
theorem projected_envelope_moment (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 0 ≤ q) (hB : 0 ≤ B) (M : Matrix (Fin m) (Fin p) ℝ)
    {J : ℝ} (hJ : 0 ≤ J) (hM : ∀ α, (∑ j, |M α j|)≤J) (i : Fin n) :
    Integrable (fun ω => ‖M.mulVec (X i ω)‖^q) μ ∧
      (∫ ω, ‖M.mulVec (X i ω)‖^q ∂μ)≤(J*B)^q := by
  have hp (ω : Ω) : ‖M.mulVec (X i ω)‖^q ≤ J^q*‖X i ω‖^q := by
    rw [←Real.mul_rpow hJ (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _)
      (norm_mulVec_le_of_row_l1 M J hJ hM _) hq
  have hi : Integrable (fun ω => ‖M.mulVec (X i ω)‖^q) μ :=
    ((h.envelope_integrable i).const_mul (J^q)).mono'
      ((((measurable_rectangular_mulVec M).comp (h.measurable i)).norm).pow_const q).aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hp ω))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, J^q*‖X i ω‖^q ∂μ := integral_mono hi ((h.envelope_integrable i).const_mul _) hp
    _ = J^q*(∫ ω, ‖X i ω‖^q ∂μ) := integral_const_mul _ _
    _ ≤ J^q*B^q := mul_le_mul_of_nonneg_left (h.envelope_moment i) (by positivity)
    _ = (J*B)^q := (Real.mul_rpow hJ hB).symm

theorem projected (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (hB : 0 ≤ B) (M : Matrix (Fin m) (Fin p) ℝ)
    {J : ℝ} (hJ : 0 ≤ J) (hM : ∀ α, (∑ j, |M α j|)≤J)
    (hunit : ∀ α, (M*covariance μ (normalizedObservationSum X)*M.transpose) α α=1) :
    PolynomialEnvelopeHypotheses μ (fun i ω => M.mulVec (X i ω)) q (J*B) :=
  ⟨fun i => (measurable_rectangular_mulVec M).comp (h.measurable i),
    h.independent.comp (fun _ => M.mulVec) (fun _ => measurable_rectangular_mulVec M),
    h.projected_centered hq M,
    fun i => (h.projected_envelope_moment (by linarith) hB M hJ hM i).1,
    h.projected_average_second hq M hunit,
    fun i => (h.projected_envelope_moment (by linarith) hB M hJ hM i).2⟩
end PolynomialEnvelopeHypotheses

namespace PolynomialFourthHypotheses
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p m n : ℕ} {X : Fin n → Ω → Vector p} {q B : ℝ}

omit [IsProbabilityMeasure μ] in
theorem toArchived (h : PolynomialFourthHypotheses μ X q B) :
    PolynomialIndependentHypotheses μ X q B :=
  ⟨h.measurable,h.independent,h.centered,h.envelope_integrable,h.fourth_integrable,
    h.average_second,h.envelope_moment,h.average_fourth⟩

/-- Averaging the fourth budget is done before summing face coefficients. -/
theorem projected (h : PolynomialFourthHypotheses μ X q B)
    (hq : 2 < q) (hB : 0 ≤ B) (M : Matrix (Fin m) (Fin p) ℝ)
    {J : ℝ} (hJ : 1 ≤ J) (hM : ∀ α, (∑ j, |M α j|)≤J)
    (hunit : ∀ α, (M*covariance μ (normalizedObservationSum X)*M.transpose) α α=1) :
    PolynomialFourthHypotheses μ (fun i ω => M.mulVec (X i ω)) q (J^2*B) := by
  have hh := polynomialIndependent_projected h.toArchived (by linarith) hB M hJ hM hunit
  exact ⟨⟨hh.measurable,hh.independent,hh.centered,hh.envelope_integrable,
    hh.average_second,hh.envelope_moment⟩,hh.fourth_integrable,hh.average_fourth⟩
end PolynomialFourthHypotheses

end
end RectangleCLTArxivV1
