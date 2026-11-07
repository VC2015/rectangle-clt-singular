import RectangleCLTCompanion.SplitV4.BennettTruncation
import RectangleCLT.TruncationBasic
import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Actual centered whole-vector truncation for the envelope-maximum bound in
Appendix E. The bounded summands use their actual removed means; the omitted
sum is controlled from genuine real q-moment integrals.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {p n : ℕ} {Y : Fin n → Ω → Vector p} {u q : ℝ}

/-- The centered whole-vector cutoff on the original probability space. -/
abbrev envelopeCenteredTruncation (μ : Measure Ω)
    (Y : Fin n → Ω → Vector p) (u : ℝ) : Fin n → Ω → Vector p :=
  fun i => centeredTruncateVector μ (Y i) u

theorem envelopeCenteredTruncation_boundedHypotheses [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) (hu : 0 ≤ u) :
    BoundedIndependentHypotheses μ (envelopeCenteredTruncation μ Y u) (2 * u) :=
  boundedIndependentHypotheses_centeredTruncateVector hY hind hu

theorem envelopeCenteredTruncation_second_moment_le [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i)) (_hu : 0 ≤ u)
    (hsecond : ∀ i j, Integrable (fun ω => Y i ω j ^ 2) μ) (i : Fin n) (j : Fin p) :
    (∫ ω, envelopeCenteredTruncation μ Y u i ω j ^ 2 ∂μ) ≤
      ∫ ω, Y i ω j ^ 2 ∂μ := by
  have hm : AEStronglyMeasurable (fun ω => truncateVector u (Y i ω) j) μ :=
    (measurable_bennettTruncate_coordinate (hY i) j).aestronglyMeasurable
  change (∫ ω, (truncateVector u (Y i ω) j -
    ∫ a, truncateVector u (Y i a) j ∂μ) ^ 2 ∂μ) ≤ _
  rw [← variance_eq_integral hm.aemeasurable]
  exact (variance_le_expectation_sq hm).trans
    (integral_bennettTruncate_coordinate_sq_le (hY i) j (hsecond i j))

theorem envelopeCenteredTruncation_second_moment_sum_le [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i)) (hu : 0 ≤ u)
    (hsecond : ∀ i j, Integrable (fun ω => Y i ω j ^ 2) μ) (j : Fin p) :
    (∑ i, ∫ ω, envelopeCenteredTruncation μ Y u i ω j ^ 2 ∂μ) ≤
      ∑ i, ∫ ω, Y i ω j ^ 2 ∂μ :=
  Finset.sum_le_sum (fun i _ => envelopeCenteredTruncation_second_moment_le hY hu hsecond i j)

/-- The coordinatewise removed mean equals the genuine vector integral. -/
theorem truncationMean_eq_integral [IsFiniteMeasure μ]
    {T : Ω → Vector p} (hT : Measurable T) (hu : 0 ≤ u) :
    truncationMean μ T u = ∫ ω, truncateVector u (T ω) ∂μ := by
  have hi : Integrable (fun ω => truncateVector u (T ω)) μ :=
    integrable_bennettTruncate hT hu
  ext j
  exact (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hi

theorem integral_vector_eq_zero_of_coordinate_centering
    {T : Ω → Vector p} (hT : Integrable T μ)
    (hcenter : ∀ j, (∫ ω, T ω j ∂μ) = 0) : (∫ ω, T ω ∂μ) = 0 := by
  ext j
  have hh := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hT
  change (∫ ω, T ω j ∂μ) = (∫ ω, T ω ∂μ) j at hh
  exact hh.symm.trans (hcenter j)

/-- Centering costs at most one additional omitted-tail expectation. -/
theorem norm_truncationMean_le_integral_remainder [IsProbabilityMeasure μ]
    {T : Ω → Vector p} (hT : Measurable T) (hu : 0 < u) (hq : 1 < q)
    (hmoment : Integrable (fun ω => ‖T ω‖ ^ q) μ)
    (hcenter : ∀ j, (∫ ω, T ω j ∂μ) = 0) :
    ‖truncationMean μ T u‖ ≤ ∫ ω, ‖T ω - truncateVector u (T ω)‖ ∂μ := by
  have hI := integrable_of_bennett_norm_moment hT hq hmoment
  have hC : Integrable (fun ω => truncateVector u (T ω)) μ :=
    integrable_bennettTruncate hT hu.le
  have hz := integral_vector_eq_zero_of_coordinate_centering hI hcenter
  have he : (∫ ω, T ω - truncateVector u (T ω) ∂μ) = -truncationMean μ T u := by
    rw [integral_sub hI hC, hz, zero_sub, truncationMean_eq_integral hT hu.le]
  have hh := norm_integral_le_integral_norm (μ := μ)
    (fun ω => T ω - truncateVector u (T ω))
  simpa only [he, norm_neg] using hh

/-- Full integrated comparison with the centered truncation, including both
the omitted summands and the actual deterministic centering correction. -/
theorem integral_norm_sum_le_centeredTruncation_add_tail [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i))
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    (hu : 0 < u) (hq : 1 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖ ^ q) μ)
    (A : ℝ) (hbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤
      (∫ ω, ‖sumVector (envelopeCenteredTruncation μ Y u) ω‖ ∂μ) +
        2 * A ^ q / u ^ (q - 1) := by
  let Z := envelopeCenteredTruncation μ Y u
  let R : Fin n → Ω → Vector p := fun i ω => Y i ω - truncateVector u (Y i ω)
  let m : Fin n → Vector p := fun i => truncationMean μ (Y i) u
  have hI (i : Fin n) : Integrable (Y i) μ :=
    integrable_of_bennett_norm_moment (hY i) hq (hmoment i)
  have hC (i : Fin n) : Integrable (fun ω => truncateVector u (Y i ω)) μ :=
    integrable_bennettTruncate (hY i) hu.le
  have hR (i : Fin n) : Integrable (R i) μ := (hI i).sub (hC i)
  have hZ (i : Fin n) : Integrable (Z i) μ := (hC i).sub (integrable_const _)
  have hmean (i : Fin n) : ‖m i‖ ≤ ∫ ω, ‖R i ω‖ ∂μ :=
    norm_truncationMean_le_integral_remainder (hY i) hu hq (hmoment i) (hcenter i)
  have htail : (∑ i, ∫ ω, ‖R i ω‖ ∂μ) ≤ A ^ q / u ^ (q - 1) := by
    calc
      _ ≤ ∑ i, (∫ ω, ‖Y i ω‖ ^ q ∂μ) / u ^ (q - 1) :=
        Finset.sum_le_sum (fun i _ =>
          integral_norm_bennettRemainder_le (hY i) hu hq (hmoment i))
      _ = (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) / u ^ (q - 1) := (Finset.sum_div ..).symm
      _ ≤ _ := div_le_div_of_nonneg_right hbudget (Real.rpow_nonneg hu.le _)
  have hpoint (ω : Ω) :
      ‖sumVector Y ω‖ ≤ ‖sumVector Z ω‖ + ∑ i, ‖R i ω‖ + ∑ i, ‖m i‖ := by
    have heq : sumVector Y ω = sumVector Z ω + (∑ i, R i ω) + ∑ i, m i := by
      simp only [sumVector, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [Z, envelopeCenteredTruncation, centeredTruncateVector, R, m]
      abel
    rw [heq]
    calc
      _ ≤ ‖sumVector Z ω‖ + ‖∑ i, R i ω‖ + ‖∑ i, m i‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ _ := by
        exact add_le_add (add_le_add_left (norm_sum_le _ _) _) (norm_sum_le _ _)
  have hbound : (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤
      (∫ ω, ‖sumVector Z ω‖ ∂μ) + (∑ i, ∫ ω, ‖R i ω‖ ∂μ) + ∑ i, ‖m i‖ := by
    calc
      _ ≤ ∫ ω, ‖sumVector Z ω‖ + (∑ i, ‖R i ω‖) + ∑ i, ‖m i‖ ∂μ :=
        integral_mono (integrable_finset_sum Finset.univ (fun i _ => hI i)).norm
          (((integrable_finset_sum Finset.univ (fun i _ => hZ i)).norm.add
            (integrable_finset_sum Finset.univ (fun i _ => (hR i).norm))).add
            (integrable_const _)) hpoint
      _ = _ := by
        rw [integral_add
          (f := fun ω => ‖sumVector Z ω‖ + ∑ i, ‖R i ω‖)
          (g := fun _ : Ω => ∑ i, ‖m i‖)
          ((integrable_finset_sum Finset.univ (fun i _ => hZ i)).norm.add
            (integrable_finset_sum Finset.univ (fun i _ => (hR i).norm))) (integrable_const _),
          integral_add (f := fun ω => ‖sumVector Z ω‖) (g := fun ω => ∑ i, ‖R i ω‖)
            (integrable_finset_sum Finset.univ (fun i _ => hZ i)).norm
            (integrable_finset_sum Finset.univ (fun i _ => (hR i).norm)),
          integral_finset_sum Finset.univ (fun i _ => (hR i).norm)]
        simp
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmean i)
  change (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤ (∫ ω, ‖sumVector Z ω‖ ∂μ) + _
  rw [mul_div_assoc]
  linarith

end

end RectangleCLT.Companion.SplitV4
