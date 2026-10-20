import RectangleCLTCompanion.SharpGaussianConvolution
import RectangleCLTCompanion.SharpRepresentatives

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p n : ℕ} (s : FaceSmoother p)

/-- Exact full-mixture law bridge to the actual split-Gaussian base.
The fresh support rows remain independent of both retained rows and noises. -/
theorem signedCubicPathTerm_eq_integral_splitBase
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : Fin n → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ}
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (hrec : ∀ i, (fun a => A.mulVec (Z i a)) =ᵐ[μ] ξ i)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.signedCubicPathTerm μ ξ A x t =
      ∫ z, Companion.cubicGaussianSum s μ A Z (Companion.splitBaseValue A x t z)
        (Companion.splitGaussianScale t) ∂Companion.splitBaseLaw μ ξ t := by
  let B := bernoulliArrayLaw μ ξ t
  let H := Companion.splitBaseLaw μ ξ t
  let ν := gaussianLaw (Companion.splitGaussianScale t • A)
  let V := Companion.splitBaseValue (n := n) A x t
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  letI : IsProbabilityMeasure H := Companion.splitBaseLaw_isProbability μ ξ hξ ht ht1
  let M := fun j k l => ∑ i, ∫ a, ξ i a j * ξ i a k * ξ i a l ∂μ
  have hmoment (j k l : Fin p) :
      (∑ i, ∫ a, A.mulVec (Z i a) j * A.mulVec (Z i a) k * A.mulVec (Z i a) l ∂μ) = M j k l := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hrec i] with a ha
    rw [ha]
  have hiD (j k l : Fin p) : Integrable
      (fun z => s.convolutionThirdDerivative ν (V z) j k l) H :=
    integrable_bounded_test_comp H V (Companion.measurable_splitBaseValue A x t) _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  have hentry (j k l : Fin p) :
      s.selectorThirdDerivativeAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
        (thinningProbability t) (thinningScale t) j k l =
      ∫ z, s.convolutionThirdDerivative ν (V z) j k l ∂H := by
    rw [s.selectorThirdDerivativeAverage_eq_integral_arrayLaw μ ξ hξ _ x ht ht1]
    have hh := integral_prod (fun z => s.convolutionThirdDerivative ν (V z) j k l) (hiD j k l)
    change _ = ∫ z, s.convolutionThirdDerivative ν (V z) j k l ∂B.prod (standardGaussian p)
    rw [hh]
    apply integral_congr_ae
    apply ae_of_all
    intro b
    exact s.convolutionThirdDerivative_gaussian_split A t (x + arraySum b) j k l
  unfold signedCubicPathTerm
  simp_rw [hentry]
  change (∑ j, ∑ k, ∑ l, M j k l * (∫ z, s.convolutionThirdDerivative ν (V z) j k l ∂H)) = _
  simp_rw [← integral_const_mul]
  have hi (j k l : Fin p) := (hiD j k l).const_mul (M j k l)
  have hsum : (∫ z, ∑ j, ∑ k, ∑ l, M j k l * s.convolutionThirdDerivative ν (V z) j k l ∂H) =
      ∑ j, ∑ k, ∑ l, ∫ z, M j k l * s.convolutionThirdDerivative ν (V z) j k l ∂H := by
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ =>
      integrable_finset_sum _ (fun l _ => hi j k l)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hi j k l))]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finset_sum _ (fun l _ => hi j k l)
  rw [← hsum]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [Companion.cubicGaussianSum_eq_moment_tensor s μ A Z hZ hb]
  simp_rw [hmoment]
  rfl

/-- Canonical support rows and the actual split-Gaussian base give the cubic
cap from the genuine averaged selector matrix estimate, with factor two for
the half variance. -/
theorem abs_signedCubicPathTerm_le_of_split_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C T) :
    |s.signedCubicPathTerm μ ξ A x t| ≤ 2 * δ * C ^ 2 * T / (s.bandwidth * t) := by
  let Z := Companion.boundedSupportObservation A ξ δ
  have hZm := Companion.boundedSupportObservation_measurable h A
  have hZ := Companion.boundedSupportObservation_second_moments_integrable h A hA
  have hb (i : Fin n) : ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ :=
    ae_of_all _ (Companion.boundedSupportObservation_projected_le A ξ h.delta_nonneg i)
  rw [s.signedCubicPathTerm_eq_integral_splitBase μ ξ h.measurable A Z hZm hb
    (Companion.boundedSupportObservation_reconstruct h A hA) x ht.le ht1]
  have hh := Companion.abs_integral_cubicGaussianSum_le_of_matrix_estimate s
    (Companion.splitBaseLaw μ ξ t) μ A Z (Companion.splitBaseValue A x t)
    (Companion.measurable_splitBaseValue A x t) hZm hZ h.delta_nonneg
    (ne_of_gt (Companion.splitGaussianScale_pos ht)) hb
    (Companion.boundedSupportObservation_covariance_budget h A hA) hmatrix
  rw [Companion.splitGaussianScale_sq ht.le] at hh
  exact hh.trans_eq (by field_simp; ring)

end
end RectangleCLT.FaceSmoother
