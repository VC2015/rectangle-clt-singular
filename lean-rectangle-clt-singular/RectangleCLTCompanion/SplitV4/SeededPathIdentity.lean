import RectangleCLTCompanion.SplitV4.CalibratedSeededExpectation
import RectangleCLTCompanion.SplitV4.SeededRemainderBound
import RectangleCLTCompanion.SplitV4.NormalizedSeededEndpoints

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem hasDerivAt_seeded_test_manuscript
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {ε : ℝ} (hε : 0 ≤ ε) (x : Vector p) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (s.seededSelectorHeatExpectation μ ξ A ε x)
      (-(t / 3) * s.variableSignedCubicPathTerm (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) + seededFourthRemainder s μ ξ A x ε t) t := by
  have hd := s.hasDerivAt_integral_variableSeededInterpolationLaw_manuscript μ ξ h A hA
    thinningScale (fun _ => 1) hε
    (fun r _ => by
      change HasDerivAt (fun x : ℝ => 1 + x) 1 r
      simpa only [id_eq, zero_add] using (hasDerivAt_const r (1 : ℝ)).add (hasDerivAt_id r))
    (fun r hr => by change 0 < 1 + r; linarith [hr.1])
    (fun r hr => calibrated_retention_mem_Icc ⟨hr.1.le, hr.2.le⟩) x ht.1 ht.2 continuousAt_const
  have hc : (-(thinningScale t) + (1 - t) * (1 : ℝ)) / 6 = -(t / 3) := by
    unfold thinningScale
    ring
  simp only [variableRetention_calibrated, variableEta_calibrated] at hd
  rw [hc, calibrated_cubic_kernel ht.1.le] at hd
  change HasDerivAt _ (-(t / 3) * s.variableSignedCubicPathTerm
    (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x (thinningProbability t) (1 + t) +
      seededFourthRemainder s μ ξ A x ε t) t at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact (seeded_selector_expectation_eq_variable_selector s μ ξ h.measurable A x hε hr.1.le hr.2.le).trans
    (s.integral_variableSeededInterpolationLaw_eq_variableSelectorHeatExpectation μ ξ h.measurable A
      thinningScale ε x r (calibrated_retention_mem_Icc ⟨hr.1.le, hr.2.le⟩)).symm

end

end RectangleCLT.Companion.SplitV4
