import RectangleCLTCompanion.Cancellation
import RectangleCLTCompanion.Examples

/-! A bounded centered independent observation realizes the singular
positive-gap covariance from `Examples`. Thus the distinction between the
two CLT scopes occurs within the actual probabilistic hypotheses. -/

open MeasureTheory

namespace RectangleCLT.Companion.Examples

noncomputable section

def gapObservation (_ : Fin 1) (ω : Bool × Bool) : Vector 3 :=
  ![signValue ω.1, signValue ω.2, (3 * signValue ω.1 + 4 * signValue ω.2) / 5]

theorem gapObservation_centered (i : Fin 1) (j : Fin 3) :
    (∫ ω, gapObservation i ω j ∂signPairLaw) = 0 := by
  fin_cases j <;> norm_num [integral_signPairLaw, gapObservation, signValue]

theorem gapObservation_bounded (i : Fin 1) (ω : Bool × Bool) :
    ‖gapObservation i ω‖ ≤ 7 / 5 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5)).mpr
  intro j
  rcases ω with ⟨x, y⟩
  fin_cases j <;> cases x <;> cases y <;>
    norm_num [gapObservation, signValue]

theorem gapObservation_data :
    BoundedIndependentHypotheses signPairLaw gapObservation (7 / 5) := by
  refine
    { measurable := fun _ => measurable_of_finite _
      independent := ProbabilityTheory.iIndepFun.of_subsingleton
      centered := gapObservation_centered
      bounded := fun i => ae_of_all _ (gapObservation_bounded i)
      delta_nonneg := by norm_num }

theorem gapObservation_covariance :
    covariance signPairLaw (sumVector gapObservation) = gapMatrix := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [covariance, sumVector, Fin.sum_univ_succ, gapObservation,
      integral_signPairLaw, signValue, gapMatrix]

/-- A real bounded independent probability model with normalized coordinate
variances and positive pair gap, outside the completed local theorem's scope. -/
theorem bounded_model_with_positive_gap_and_zero_local_minima :
    BoundedIndependentHypotheses signPairLaw gapObservation (7 / 5) ∧
      (∀ j, covariance signPairLaw (sumVector gapObservation) j j = 1) ∧
      pairGap (covariance signPairLaw (sumVector gapObservation)) = 1 / 5 ∧
      a3 (covariance signPairLaw (sumVector gapObservation)) = 0 ∧
      a4 (covariance signPairLaw (sumVector gapObservation)) = 0 := by
  rw [gapObservation_covariance]
  exact ⟨gapObservation_data, gapMatrix_unit_diagonal, gapMatrix_pairGap,
    gapMatrix_a3, gapMatrix_a4⟩

end

end RectangleCLT.Companion.Examples
