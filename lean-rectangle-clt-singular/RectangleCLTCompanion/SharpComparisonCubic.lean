import RectangleCLTCompanion.RestorationSmootherIBP
import RectangleCLTCompanion.RestorationMatrixBound
import RectangleCLTCompanion.RestorationIntegration
import RectangleCLTCompanion.FourthIdentityFresh

/-! Unshifted cubic restoration. Actual third derivatives are first converted
by two Gaussian integrations by parts, then the fresh-row covariance budget
is assembled into the actual selector score matrices. -/

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace RectangleCLT.Companion

noncomputable section

variable {p r : ℕ} (s : FaceSmoother p)

theorem firstDerivative_contraction_eq_faces (x u : Vector p) :
    (∑ j, u j * s.coordinateDerivativeF x j) =
      -(1 / s.bandwidth) * ∑ f : Face p, FaceSmoother.normalDot f u *
        selectorTupleWeight s (fun _ : Fin 1 => f) x := by
  have hm := (s.weights x).directionalMean_eq u
  change (∑ f : Face p, (s.weights x).pi f * FaceSmoother.normalDot f u) =
    ∑ j, (s.weights x).v j * u j at hm
  simp only [s.coordinateDerivativeF_eq, selectorTupleWeight, Fin.prod_univ_one]
  change (∑ j, u j * (-(s.F x / s.bandwidth) * (s.weights x).v j)) =
    -(1 / s.bandwidth) * ∑ f : Face p, FaceSmoother.normalDot f u *
      (s.F x * (s.weights x).pi f)
  calc
    _ = -(s.F x / s.bandwidth) * ∑ j, (s.weights x).v j * u j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -(s.F x / s.bandwidth) * ∑ f : Face p, (s.weights x).pi f *
        FaceSmoother.normalDot f u := by rw [hm]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring

private theorem measurable_affine (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) :
    Measurable (fun g => A.mulVec g + x) := by
  apply Measurable.add _ measurable_const
  apply measurable_pi_lambda
  intro j
  exact Finset.measurable_sum Finset.univ (fun k _ =>
    measurable_const.mul (measurable_pi_apply k))

private theorem integrable_score (z : Vector r) :
    Integrable (fun g => repeatedDirectionScore g z) (standardGaussian r) := by
  have hgg (j k : Fin r) : Integrable (fun g : Vector r => g j * g k * (1 : ℝ))
      (standardGaussian r) :=
    standardGaussian_integrable_weighted_product (fun _ : Vector r => (1 : ℝ))
      measurable_const (fun _ => by norm_num) j k
  have hh := integrable_repeatedDirectionScore_weight (standardGaussian r)
    (fun g : Vector r => g) (fun _ : Vector r => (1 : ℝ)) (integrable_const _) hgg z
  simpa only [mul_one] using hh

private theorem integrable_score_first (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (z : Vector r) (j : Fin p) :
    Integrable (fun g => repeatedDirectionScore g z *
      s.coordinateDerivativeF (A.mulVec g + x) j) (standardGaussian r) := by
  have hd : Measurable (fun g => s.coordinateDerivativeF (A.mulVec g + x) j) :=
    (s.continuous_firstDerivative j).measurable.comp
      (measurable_affine A x)
  convert (integrable_score z).bdd_mul' hd.aestronglyMeasurable
    (ae_of_all _ (fun g => s.norm_firstDerivative_le (A.mulVec g + x) j)) using 1
  ext g
  ring

private theorem integrable_score_selector (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (z : Vector r) (f : Face p) :
    Integrable (fun g => repeatedDirectionScore g z *
      selectorTupleWeight s (fun _ : Fin 1 => f) (A.mulVec g + x)) (standardGaussian r) := by
  have hm := measurable_selectorTupleWeight_comp s (fun _ : Fin 1 => f)
    (fun g => A.mulVec g + x) (measurable_affine A x)
  convert (integrable_score z).bdd_mul' hm.aestronglyMeasurable
    (ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]
      exact selectorTupleWeight_le_one s _ _)) using 1
  ext g
  ring

/-- Genuine repeated-direction third derivative identity, with arbitrary
observable direction and a rectangular, potentially singular factor. -/
theorem cubic_repeated_gaussian_eq_face_scores
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, s.translationD3 ((σ • A).mulVec g + x) (A.mulVec z) ∂standardGaussian r) =
      -(1 / (s.bandwidth * σ ^ 2)) *
        ∑ f : Face p, FaceSmoother.normalDot f (A.mulVec z) *
          (∫ g, repeatedDirectionScore g z *
            selectorTupleWeight s (fun _ : Fin 1 => f)
              ((σ • A).mulVec g + x) ∂standardGaussian r) := by
  let u := A.mulVec z
  let W := fun g => (σ • A).mulVec g + x
  have hW : Measurable W := measurable_affine (σ • A) x
  have hi (j k l : Fin p) : Integrable (fun g => s.mixedThirdDerivativeF (W g) j k l)
      (standardGaussian r) :=
    integrable_bounded_test_comp _ W hW _ (s.continuous_thirdDerivative j k l) _
      (fun y => s.norm_thirdDerivative_le y j k l)
  have hiQ (j : Fin p) : Integrable
      (fun g => matrixQuadratic (fun k l => s.mixedThirdDerivativeF (W g) j k l) u)
      (standardGaussian r) := by
    unfold matrixQuadratic
    exact integrable_finset_sum _ (fun k _ => integrable_finset_sum _
      (fun l _ => ((hi j k l).const_mul (u k)).mul_const (u l)))
  have heq (g : Vector r) : s.translationD3 (W g) u =
      ∑ j, u j * matrixQuadratic (fun k l => s.mixedThirdDerivativeF (W g) j k l) u := by
    unfold FaceSmoother.translationD3 matrixQuadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    _ = ∑ j, u j * (∫ g,
        matrixQuadratic (fun k l => s.mixedThirdDerivativeF (W g) j k l) u ∂standardGaussian r) := by
      change (∫ g, s.translationD3 (W g) u ∂standardGaussian r) = _
      simp_rw [heq]
      rw [integral_finset_sum _ (fun j _ => (hiQ j).const_mul _)]
      simp only [integral_const_mul]
    _ = (1 / σ ^ 2) * ∑ j, u j * (∫ g,
        repeatedDirectionScore g z * s.coordinateDerivativeF (W g) j ∂standardGaussian r) := by
      dsimp [u, W]
      simp_rw [smoother_third_repeated_score_scaled s A x z hσ]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u, W]
      ring
    _ = (1 / σ ^ 2) * (∫ g, repeatedDirectionScore g z *
        (∑ j, u j * s.coordinateDerivativeF (W g) j) ∂standardGaussian r) := by
      congr 1
      have hpoint : (fun g => repeatedDirectionScore g z *
          (∑ j, u j * s.coordinateDerivativeF (W g) j)) =
          (fun g => ∑ j, u j * (repeatedDirectionScore g z * s.coordinateDerivativeF (W g) j)) := by
        funext g
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hpoint, integral_finset_sum _ (fun j _ =>
        (integrable_score_first s (σ • A) x z j).const_mul (u j))]
      simp only [integral_const_mul]
      rfl
    _ = _ := by
      simp_rw [firstDerivative_contraction_eq_faces s]
      have hpoint (g : Vector r) : repeatedDirectionScore g z *
          (-(1 / s.bandwidth) * ∑ f : Face p, FaceSmoother.normalDot f u *
            selectorTupleWeight s (fun _ : Fin 1 => f) (W g)) =
          -(1 / s.bandwidth) * ∑ f : Face p, FaceSmoother.normalDot f u *
            (repeatedDirectionScore g z * selectorTupleWeight s (fun _ : Fin 1 => f) (W g)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        ring
      simp_rw [hpoint]
      rw [integral_const_mul, integral_finset_sum _ (fun f _ =>
        (integrable_score_selector s (σ • A) x z f).const_mul _)]
      simp only [integral_const_mul]
      dsimp [u, W]
      ring

end
end RectangleCLT.Companion
