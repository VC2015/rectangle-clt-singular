import RectangleCLTCompanion.SplitV4.NormalizedSeededPath
import RectangleCLTCompanion.SplitV4.VariableAmplitudeFourthIdentity

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option maxHeartbeats 1000000

theorem variableRetention_calibrated (t : ℝ) :
    variableRetention thinningScale t = thinningProbability t := rfl

theorem variableEta_calibrated (t : ℝ) :
    variableEta thinningScale (fun _ => 1) t = calibratedEta t := by
  simp only [variableEta, calibratedEta, thinningScale, mul_one]

theorem seeded_test_expectation_eq_variable_selector
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ y, s.F (x + y) ∂seededInterpolationLaw μ ξ A ε t) =
      s.variableSelectorHeatExpectation μ ξ A thinningScale ε x t := by
  let B := bernoulliArrayLaw μ ξ t
  let G := gaussianLaw (Real.sqrt (t + ε) • A)
  let K : Vector p → ℝ := fun y => s.gaussianHeat A (x + y) (t + ε)
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have harg : Continuous (fun y : Vector p => (x + y, t + ε)) := by fun_prop
  have hK : Continuous K := by
    simpa only [K, Function.comp_def] using (s.continuous_gaussianHeat A).comp harg
  have hKb (y : Vector p) : ‖K y‖ ≤ 1 := by
    simpa only [K] using s.norm_gaussianHeat_le_one A (x + y) (t + ε)
  have hKK := integral_bernoulliArrayLaw_comp_arraySum_eq_sum μ ξ hξ ht ht1 K hK.measurable
    (fun mask => integrable_bounded_test_comp (μ.map (retainedArray ξ t mask)) arraySum
      (measurable_arraySum p n) K hK 1 hKb)
  have hmean : (∫ y, s.F (x + y) ∂seededInterpolationLaw μ ξ A ε t) =
      ∫ b, K (arraySum b) ∂B := by
    rw [seededInterpolationLaw_eq_shifted_heat μ ξ hξ A hε ht ht1]
    have hm : ((B.map arraySum).prod G) = (B.prod G).map (Prod.map arraySum id) := by
      simpa only [Measure.map_id] using Measure.map_prod_map B G (measurable_arraySum p n) measurable_id
    rw [hm, Measure.map_map (measurable_fst.add measurable_snd)
      ((measurable_arraySum p n).prodMap measurable_id)]
    let M : (Fin n → Vector p) × Vector p → Vector p := fun z => arraySum z.1 + z.2
    have hM : Measurable M := ((measurable_arraySum p n).comp measurable_fst).add measurable_snd
    have hTest : Measurable (fun y : Vector p => s.F (x + y)) := by
      simpa only [Function.comp_def] using s.continuous_F.measurable.comp
        (show Measurable (fun y : Vector p => x + y) from measurable_const.add measurable_id)
    change (∫ y, s.F (x + y) ∂(B.prod G).map M) = _
    rw [integral_map (f := fun y : Vector p => s.F (x + y)) hM.aemeasurable hTest.aestronglyMeasurable]
    have hi : Integrable (fun z : (Fin n → Vector p) × Vector p =>
        s.F (x + (arraySum z.1 + z.2))) (B.prod G) :=
      (integrable_const (1 : ℝ)).mono' (hTest.comp hM).aestronglyMeasurable
        (ae_of_all _ (fun z => s.norm_F_le_one _))
    change (∫ z : (Fin n → Vector p) × Vector p, s.F (x + (arraySum z.1 + z.2)) ∂B.prod G) = _
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact ae_of_all _ (fun b => by
      dsimp only [K]
      rw [s.gaussianHeat_eq_convolution]
      simp only [FaceSmoother.convolution, shiftIntegral, G, add_assoc])
  rw [hmean, hKK]
  unfold FaceSmoother.variableSelectorHeatExpectation
  rw [variableRetention_calibrated]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [s.variableHeatShiftExpectation_eq_convolution μ _ (measurable_maskObservationSum ξ hξ mask)]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => (s.gaussianHeat_eq_convolution A _ _))

theorem seeded_selector_expectation_eq_variable_selector
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.seededSelectorHeatExpectation μ ξ A ε x t =
      s.variableSelectorHeatExpectation μ ξ A thinningScale ε x t := by
  rw [← s.integral_seededInterpolationLaw_eq_seededSelectorHeatExpectation μ ξ hξ A ε x ht ht1]
  exact seeded_test_expectation_eq_variable_selector s μ ξ hξ A x hε ht ht1

end

end RectangleCLT.Companion.SplitV4
