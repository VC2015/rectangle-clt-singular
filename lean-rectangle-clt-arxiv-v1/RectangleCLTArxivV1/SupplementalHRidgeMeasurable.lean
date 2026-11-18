import RectangleCLTArxivV1.SupplementalHRidgeGreen

/-! The actual hard ridge Gaussian integrals are jointly measurable in
thresholds, including at exceptional affine configurations. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

theorem measurable_hardPairSection_integral_threshold {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (e f : Vector r)
    (a c : Vector m → ℝ) (ha : Measurable a) (hc : Measurable c)
    (H : Vector r → ℝ) (hH : Measurable H) :
    Measurable (fun b : Vector m => ∫ g,
      (gaussianFiniteThresholdEvent s u b).indicator H
        (gaussianPairSectionPoint e f (a b) (c b) g) ∂standardGaussian r) := by
  let X := fun z : Vector m × Vector r => gaussianPairSectionPoint e f (a z.1) (c z.1) z.2
  have hX : Measurable X :=
    (measurable_gaussianPairSectionMap e f).comp
      (((ha.comp measurable_fst).prodMk (hc.comp measurable_fst)).prodMk measurable_snd)
  let E := {z : Vector m × Vector r | ∀ k∈s, faceDot (u k) (X z)≤z.1 k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left (u k)).measurable.comp hX)
      ((measurable_pi_apply k).comp measurable_fst)
  have hi := ((hH.comp hX).indicator hE).stronglyMeasurable.integral_prod_right' (ν := standardGaussian r)
  exact hi.measurable

theorem measurable_hardGaussianRidgeNormalWeight {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => hardGaussianRidgeNormalWeight u b j l) := by
  unfold hardGaussianRidgeNormalWeight
  have hpdf := measurable_gaussianPDFReal 0 1
  exact ((hpdf.comp (by unfold thresholdPairFirstLevel; fun_prop)).const_mul _).mul
    (hpdf.comp (by unfold thresholdPairSecondLevel; fun_prop))

theorem measurable_hardGaussianSignedRidgeTerm {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => hardGaussianSignedRidgeTerm u b j l) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · simp only [hardGaussianSignedRidgeTerm,hp,if_true]
    apply (measurable_hardGaussianRidgeNormalWeight u j l).mul
    exact measurable_hardPairSection_integral_threshold _ u _ _ _ _ (by unfold thresholdPairFirstLevel; fun_prop)
      (by unfold thresholdPairSecondLevel; fun_prop) _ (by unfold vectorNormSq; fun_prop)
  · simp only [hardGaussianSignedRidgeTerm,hp,if_false]
    exact measurable_const

theorem measurable_hardGaussianWeightedRidgeIntegral {m r : ℕ}
    (u : Fin m → Vector r) : Measurable (hardGaussianWeightedRidgeIntegral u) := by
  unfold hardGaussianWeightedRidgeIntegral
  exact (Finset.measurable_sum _ (fun q _ => measurable_hardGaussianSignedRidgeTerm u q.1 q.2)).const_mul _

theorem measurable_hardGaussianRidgeLeadingTerm {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => hardGaussianRidgeLeadingTerm u b j l) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · simp only [hardGaussianRidgeLeadingTerm,hp,if_true]
    apply Measurable.mul
    · unfold thresholdPairFirstLevel thresholdPairSecondLevel
      fun_prop
    · apply (measurable_hardGaussianRidgeNormalWeight u j l).mul
      exact measurable_hardPairSection_integral_threshold _ u _ _ _ _ (by unfold thresholdPairFirstLevel; fun_prop)
        (by unfold thresholdPairSecondLevel; fun_prop) _ measurable_const
  · simp only [hardGaussianRidgeLeadingTerm,hp,if_false]
    exact measurable_const

theorem measurable_hardGaussianRidgeLeadingIntegral {m r : ℕ}
    (u : Fin m → Vector r) : Measurable (hardGaussianRidgeLeadingIntegral u) := by
  unfold hardGaussianRidgeLeadingIntegral
  exact (Finset.measurable_sum _ (fun q _ => measurable_hardGaussianRidgeLeadingTerm u q.1 q.2)).const_mul _

end
end RectangleCLTArxivV1
