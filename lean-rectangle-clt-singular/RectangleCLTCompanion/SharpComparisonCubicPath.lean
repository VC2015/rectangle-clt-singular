import RectangleCLTCompanion.SharpComparisonCubicBound
import RectangleCLTCompanion.SharpComparisonEarly
import RectangleCLTCompanion.SupportRows
import RectangleCLT.GaussianFourthSelectorBounds

/-! The signed cubic term on the actual Bernoulli path equals the genuine
independent support-row/Gaussian experiment. The full Bernoulli mixture is
retained when the averaged matrix estimate is applied. -/

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace RectangleCLT.Companion

noncomputable section

variable {p n : ℕ} (s : FaceSmoother p)

theorem integral_translationD3_gaussian_factor
    (A : Matrix (Fin p) (Fin p) ℝ) (x u : Vector p) (σ : ℝ) :
    (∫ g, s.translationD3 ((σ • A).mulVec g + x) u ∂standardGaussian p) =
      s.convolutionTranslationD3 (gaussianLaw (σ • A)) x u := by
  rw [← s.integral_translationD3_shift]
  rw [gaussianLaw, integral_map (f := fun z : Vector p => s.translationD3 (x + z) u)
    (measurable_mulVec (σ • A)).aemeasurable
    (((s.continuous_translationD3 u).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable)]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => congrArg (fun y => s.translationD3 y u) (add_comm _ _))

theorem cubicGaussianSum_eq_moment_tensor
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : Fin n → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ}
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (x : Vector p) (σ : ℝ) :
    cubicGaussianSum s μ A Z x σ =
      ∑ j, ∑ k, ∑ l, (∑ i, ∫ a,
        A.mulVec (Z i a) j * A.mulVec (Z i a) k * A.mulVec (Z i a) l ∂μ) *
        s.convolutionThirdDerivative (gaussianLaw (σ • A)) x j k l := by
  unfold cubicGaussianSum
  simp_rw [integral_translationD3_gaussian_factor s]
  change (∑ i, s.observationThirdTerm (gaussianLaw (σ • A)) μ
    (fun a => A.mulVec (Z i a)) x) = _
  have htensor (i : Fin n) := s.observationThirdTerm_eq_tensor (gaussianLaw (σ • A))
    μ (fun a => A.mulVec (Z i a)) ((measurable_mulVec A).comp (hZ i)) (hb i) x
  simp_rw [htensor]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

end
end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p n : ℕ} (s : FaceSmoother p)

theorem selectorThirdDerivativeAverage_eq_integral_arrayLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (j k l : Fin p) :
    s.selectorThirdDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k l =
      ∫ b, s.convolutionThirdDerivative ν (x + arraySum b) j k l ∂bernoulliArrayLaw μ ξ t := by
  exact (integral_bernoulliArrayLaw_comp_arraySum_eq_sum μ ξ hξ ht ht1
    (fun y => s.convolutionThirdDerivative ν (x + y) j k l)
    ((s.continuous_convolutionThirdDerivative_commonPoint ν j k l).measurable.comp
      (measurable_const.add measurable_id))
    (fun mask => integrable_bounded_test_comp _ (fun b => x + arraySum b)
      (measurable_const.add (measurable_arraySum p n)) _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l))).symm

/-- Exact signed-cubic law bridge; each fresh support row is independently
integrated against the same full retained-array law. -/
theorem signedCubicPathTerm_eq_integral_cubicGaussianSum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : Fin n → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ}
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (hrec : ∀ i, (fun a => A.mulVec (Z i a)) =ᵐ[μ] ξ i)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.signedCubicPathTerm μ ξ A x t =
      ∫ b, Companion.cubicGaussianSum s μ A Z (x + arraySum b) (Real.sqrt t)
        ∂bernoulliArrayLaw μ ξ t := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let B := bernoulliArrayLaw μ ξ t
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  let M := fun j k l => ∑ i, ∫ a, ξ i a j * ξ i a k * ξ i a l ∂μ
  have hmoment (j k l : Fin p) :
      (∑ i, ∫ a, A.mulVec (Z i a) j * A.mulVec (Z i a) k * A.mulVec (Z i a) l ∂μ) = M j k l := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hrec i] with a ha
    rw [ha]
  have hi (j k l : Fin p) : Integrable
      (fun b : Fin n → Vector p => M j k l * s.convolutionThirdDerivative ν (x + arraySum b) j k l) B :=
    (integrable_bounded_test_comp B (fun b => x + arraySum b)
      (measurable_const.add (measurable_arraySum p n)) _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)).const_mul _
  unfold signedCubicPathTerm
  simp_rw [s.selectorThirdDerivativeAverage_eq_integral_arrayLaw μ ξ hξ _ x ht ht1]
  change (∑ j, ∑ k, ∑ l, M j k l *
      (∫ b, s.convolutionThirdDerivative ν (x + arraySum b) j k l ∂B)) = _
  simp_rw [← integral_const_mul]
  have hsum : (∫ b, ∑ j, ∑ k, ∑ l, M j k l *
      s.convolutionThirdDerivative ν (x + arraySum b) j k l ∂B) =
      ∑ j, ∑ k, ∑ l, ∫ b, M j k l *
        s.convolutionThirdDerivative ν (x + arraySum b) j k l ∂B := by
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ
        (fun l _ => hi j k l)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hi j k l))]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finset_sum Finset.univ (fun l _ => hi j k l)
  rw [← hsum]
  apply integral_congr_ae
  apply ae_of_all
  intro b
  dsimp only
  rw [Companion.cubicGaussianSum_eq_moment_tensor s μ A Z hZ hb]
  simp_rw [hmoment]
  rfl

/-- The q=1 actual averaged matrix estimate supplies the cubic cap for the
full actual Bernoulli path, with its signed aggregate tensor unchanged. -/
theorem abs_signedCubicPathTerm_le_of_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : Fin n → Ω → Vector p)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (hrec : ∀ i, (fun a => A.mulVec (Z i a)) =ᵐ[μ] ξ i)
    (hbudget : ∀ u : Vector p, ∑ i, ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ ≤ vectorNormSq u)
    (x : Vector p) {t C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (bernoulliArrayLaw μ ξ t)
      (Real.sqrt t • A) (fun b => x + arraySum b) C T) :
    |s.signedCubicPathTerm μ ξ A x t| ≤ δ * C ^ 2 * T / (s.bandwidth * t) := by
  rw [s.signedCubicPathTerm_eq_integral_cubicGaussianSum μ ξ hξ A Z hZm hb hrec x ht.le ht1]
  have hh := Companion.abs_integral_cubicGaussianSum_le_of_matrix_estimate s
    (bernoulliArrayLaw μ ξ t) μ A Z (fun b => x + arraySum b)
    (measurable_const.add (measurable_arraySum p n)) hZm hZ hδ
    (ne_of_gt (Real.sqrt_pos.mpr ht)) hb hbudget hmatrix
  simpa only [Real.sq_sqrt ht.le] using hh

/-- The canonical singular-safe support rows discharge every row premise of
the actual cubic cap. The averaged matrix estimate is the only remaining
analytic input, and is taken under the full retained-array law. -/
theorem abs_signedCubicPathTerm_le_of_support_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (bernoulliArrayLaw μ ξ t)
      (Real.sqrt t • A) (fun b => x + arraySum b) C T) :
    |s.signedCubicPathTerm μ ξ A x t| ≤ δ * C ^ 2 * T / (s.bandwidth * t) := by
  let Z := Companion.whitenedObservation A ξ
  have hZ := Companion.whitenedObservation_hypotheses h A
  have hi (i : Fin n) (j k : Fin p) : Integrable (fun a => Z i a j * Z i a k) μ := by
    simpa [Fin.prod_univ_succ, Z] using
      integrable_bounded_coordinate_product μ _ (hZ.measurable i) (hZ.bounded i)
        (![j,k] : Fin 2 → Fin p)
  apply s.abs_signedCubicPathTerm_le_of_matrix_estimate μ ξ h.measurable A Z
    hZ.measurable hi h.delta_nonneg
    (Companion.whitenedObservation_projected_bounded h A hA)
    (Companion.whitenedObservation_reconstruct h A hA) ?_ x ht ht1 hmatrix
  intro u
  exact Companion.whitenedObservation_covariance_budget h A hA u

end
end RectangleCLT.FaceSmoother
