import RectangleCLTCompanion.SplitV4.SeededCubicLaw
import RectangleCLTCompanion.SplitV4.VariableAmplitudeFourthIdentity
import RectangleCLTCompanion.SharpComparisonCubicPath

/-! Exact signed cubic selector expectation at the actual seeded law.
The Gaussian factor may be singular and need not equal the array
covariance. Every coordinate derivative is genuinely integrable. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem selectorThirdDerivativeAverage_eq_seeded_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j k l : Fin p) :
    s.selectorThirdDerivativeAverage (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x
      (thinningProbability t) (1+t) j k l =
      ∫ y, s.mixedThirdDerivativeF (x+y) j k l ∂seededInterpolationLaw μ ξ A ε t := by
  let B := bernoulliArrayLaw μ ξ t
  let ν := gaussianLaw (Real.sqrt (t+ε) • A)
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  letI : IsProbabilityMeasure (B.map arraySum) := isProbabilityMeasure_map (measurable_arraySum p n).aemeasurable
  have hf : Measurable (fun y : Vector p => s.mixedThirdDerivativeF (x+y) j k l) :=
    (s.continuous_thirdDerivative j k l).measurable.comp (measurable_const.add measurable_id)
  have hprod : Integrable (fun z : Vector p × Vector p => s.mixedThirdDerivativeF (x+(z.1+z.2)) j k l)
      ((B.map arraySum).prod ν) :=
    integrable_bounded_test_comp _ _ (measurable_const.add (measurable_fst.add measurable_snd))
      _ (s.continuous_thirdDerivative j k l) _ (fun y => s.norm_thirdDerivative_le y j k l)
  have hLaw : (∫ y, s.mixedThirdDerivativeF (x+y) j k l ∂seededInterpolationLaw μ ξ A ε t) =
      ∫ b, s.convolutionThirdDerivative ν (x+arraySum b) j k l ∂B := by
    rw [seededInterpolationLaw_eq_shifted_heat μ ξ hξ A hε ht ht1,
      integral_map (measurable_fst.add measurable_snd).aemeasurable hf.aestronglyMeasurable,
      integral_prod _ hprod]
    simp only [← add_assoc]
    simp_rw [← s.convolutionThirdDerivative_eq_integral]
    rw [integral_map (f := fun y : Vector p => s.convolutionThirdDerivative ν (x+y) j k l) (measurable_arraySum p n).aemeasurable
      (((s.continuous_convolutionThirdDerivative_commonPoint ν j k l).measurable.comp
        (measurable_const.add measurable_id)).aestronglyMeasurable)]
  exact (s.selectorThirdDerivativeAverage_eq_integral_arrayLaw μ ξ hξ ν x ht ht1 j k l).trans hLaw.symm

theorem relativeThirdMatrix_eq_coordinate_third_moment
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j k l : Fin p) :
    relativeThirdMatrix μ ξ j k l = ∑ i, ∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ := by
  unfold relativeThirdMatrix restorationCoefficient
  apply Finset.sum_congr rfl
  intro i _
  exact integral_congr_ae (ae_of_all _ (fun ω => (mul_assoc _ _ _).symm))

/-- The calibrated selector cubic is the signed relative cubic contraction
under the genuine seeded interpolation law, including both time endpoints.
No covariance-factor identity is required for this law correspondence. -/
theorem variableSignedCubicPathTerm_eq_seeded_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (_hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.variableSignedCubicPathTerm (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x (thinningProbability t) (1+t) =
      ∫ y, relativeCubicContraction s μ ξ (x+y) ∂seededInterpolationLaw μ ξ A ε t := by
  let L := seededInterpolationLaw μ ξ A ε t
  letI : IsProbabilityMeasure L := seededInterpolationLaw_isProbability μ ξ h.measurable A ε ht ht1
  have hi (j k l : Fin p) : Integrable (fun y => s.mixedThirdDerivativeF (x+y) j k l) L :=
    integrable_bounded_test_comp L _ (measurable_const.add measurable_id) _
      (s.continuous_thirdDerivative j k l) _ (fun y => s.norm_thirdDerivative_le y j k l)
  unfold FaceSmoother.variableSignedCubicPathTerm
  simp_rw [selectorThirdDerivativeAverage_eq_seeded_integral s μ ξ h.measurable A x hε ht ht1,
    ← relativeThirdMatrix_eq_coordinate_third_moment μ ξ]
  unfold relativeCubicContraction
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => integrable_finset_sum Finset.univ (fun l _ => (hi j k l).const_mul _)))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ
    (fun l _ => (hi _ k l).const_mul _)),
    integral_finset_sum Finset.univ (fun l _ => (hi _ _ l).const_mul _), integral_const_mul]
  rfl

end
end RectangleCLT.Companion.SplitV4
